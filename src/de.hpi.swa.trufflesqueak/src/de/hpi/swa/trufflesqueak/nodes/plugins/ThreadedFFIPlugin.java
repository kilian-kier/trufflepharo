/*
 * Copyright (c) 2017-2026 Software Architecture Group, Hasso Plattner Institute
 * Copyright (c) 2021-2026 Oracle and/or its affiliates
 *
 * Licensed under the MIT License.
 */
package de.hpi.swa.trufflesqueak.nodes.plugins;

import java.io.File;
import java.lang.foreign.Arena;
import java.lang.foreign.MemorySegment;
import java.lang.foreign.ValueLayout;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicLong;

import com.oracle.truffle.api.CompilerDirectives.TruffleBoundary;
import com.oracle.truffle.api.dsl.Bind;
import com.oracle.truffle.api.dsl.Cached;
import com.oracle.truffle.api.dsl.GenerateNodeFactory;
import com.oracle.truffle.api.dsl.NodeFactory;
import com.oracle.truffle.api.dsl.Specialization;
import com.oracle.truffle.api.interop.ArityException;
import com.oracle.truffle.api.interop.InteropLibrary;
import com.oracle.truffle.api.interop.UnknownIdentifierException;
import com.oracle.truffle.api.interop.UnsupportedMessageException;
import com.oracle.truffle.api.interop.UnsupportedTypeException;
import com.oracle.truffle.api.nodes.Node;
import com.oracle.truffle.api.source.Source;

import de.hpi.swa.trufflesqueak.exceptions.PrimitiveFailed;
import de.hpi.swa.trufflesqueak.image.SqueakImageContext;
import de.hpi.swa.trufflesqueak.interop.WrapToSqueakNode;
import de.hpi.swa.trufflesqueak.model.AbstractSqueakObject;
import de.hpi.swa.trufflesqueak.model.ArrayObject;
import de.hpi.swa.trufflesqueak.model.NativeObject;
import de.hpi.swa.trufflesqueak.model.NilObject;
import de.hpi.swa.trufflesqueak.model.PointersObject;
import de.hpi.swa.trufflesqueak.model.layout.ObjectLayouts;
import de.hpi.swa.trufflesqueak.nodes.accessing.AbstractPointersObjectNodes.AbstractPointersObjectReadNode;
import de.hpi.swa.trufflesqueak.nodes.accessing.AbstractPointersObjectNodes.AbstractPointersObjectWriteNode;
import de.hpi.swa.trufflesqueak.nodes.accessing.ArrayObjectNodes.ArrayObjectToObjectArrayCopyNode;
import de.hpi.swa.trufflesqueak.nodes.plugins.SqueakFFIPrims.ArgTypeConversionNode;
import de.hpi.swa.trufflesqueak.nodes.plugins.ffi.FFIConstants.FFI_TYPES;
import de.hpi.swa.trufflesqueak.nodes.primitives.AbstractPrimitiveFactoryHolder;
import de.hpi.swa.trufflesqueak.nodes.primitives.AbstractPrimitiveNode;
import de.hpi.swa.trufflesqueak.nodes.primitives.Primitive.Primitive0WithFallback;
import de.hpi.swa.trufflesqueak.nodes.primitives.Primitive.Primitive1WithFallback;
import de.hpi.swa.trufflesqueak.nodes.primitives.Primitive.Primitive2WithFallback;
import de.hpi.swa.trufflesqueak.nodes.primitives.SqueakPrimitive;
import de.hpi.swa.trufflesqueak.util.LogUtils;
import de.hpi.swa.trufflesqueak.util.OS;

/**
 * Implements Pharo's ThreadedFFI plugin primitives. Pharo's UFFI/TFFI framework uses this plugin
 * for native function calls. Without it, ffiCall: compilation and execution fails.
 */
public final class ThreadedFFIPlugin extends AbstractPrimitiveFactoryHolder {

    /**
     * Tracks objects whose "address" was requested via primitiveGetAddressOfOOP.
     * Since TruffleSqueak runs on the JVM and can't return real object addresses,
     * we assign fake IDs and resolve them back to byte[] in the callout primitives.
     */
    private static final AtomicLong NEXT_FAKE_ADDRESS = new AtomicLong(0x1000L);
    private static final ThreadLocal<Map<Long, NativeObject>> PINNED_OBJECTS = ThreadLocal.withInitial(HashMap::new);

    /**
     * Stores a NativeObject in the tracking map and returns a fake address ID.
     * Called by Pharo's PointerUtils>>primOopForObject: to get a "pointer" to an object.
     */
    static long trackObject(final NativeObject object) {
        final long fakeAddr = NEXT_FAKE_ADDRESS.getAndIncrement();
        PINNED_OBJECTS.get().put(fakeAddr, object);
        return fakeAddr;
    }

    /** Resolves a fake address back to the original NativeObject, or null if not tracked. */
    static NativeObject resolveTrackedObject(final long fakeAddr) {
        return PINNED_OBJECTS.get().get(fakeAddr);
    }

    /** Clears all tracked objects for the current thread. */
    static void clearTrackedObjects() {
        PINNED_OBJECTS.get().clear();
    }

    /** Reads an 8-byte NativeObject (ExternalAddress) as a little-endian long. */
    static long readAddressFromExternalAddress(final NativeObject externalAddress) {
        final byte[] bytes = externalAddress.getByteStorage();
        return ByteBuffer.wrap(bytes).order(ByteOrder.LITTLE_ENDIAN).getLong();
    }

    /**
     * Implements primitiveGetAddressOfOOP — returns a fake address for a Smalltalk object.
     * In the native Pharo VM, this returns the actual memory address. In TruffleSqueak,
     * we track the object and return a fake ID that our callout primitives can resolve.
     */
    @GenerateNodeFactory
    @SqueakPrimitive(names = "primitiveGetAddressOfOOP")
    protected abstract static class PrimGetAddressOfOOPNode extends AbstractPrimitiveNode implements Primitive1WithFallback {
        @Specialization(guards = "object.isByteType()")
        @TruffleBoundary
        protected static final long doGetAddress(@SuppressWarnings("unused") final Object receiver, final NativeObject object) {
            return trackObject(object);
        }

        @Specialization(guards = "object.isIntType()")
        @TruffleBoundary
        protected static final long doGetAddressInt(@SuppressWarnings("unused") final Object receiver, final NativeObject object) {
            return trackObject(object);
        }
    }

    /**
     * Fills the internal handle of a TFBasicType. In the native Pharo VM, this creates a libffi
     * ffi_type structure. In TruffleSqueak, this is a no-op since we use Truffle's NFI directly.
     */
    @GenerateNodeFactory
    @SqueakPrimitive(names = "primitiveFillBasicType")
    protected abstract static class PrimFillBasicTypeNode extends AbstractPrimitiveNode implements Primitive0WithFallback {
        @Specialization
        protected static final Object doFill(final PointersObject receiver) {
            return receiver;
        }
    }

    /**
     * Returns the byte size of a TFBasicType based on its typeCode (slot index 1).
     */
    @GenerateNodeFactory
    @SqueakPrimitive(names = "primitiveTypeByteSize")
    protected abstract static class PrimTypeByteSizeNode extends AbstractPrimitiveNode implements Primitive0WithFallback {
        @Specialization
        @TruffleBoundary
        protected static final long doByteSize(final PointersObject receiver) {
            final AbstractPointersObjectReadNode readNode = AbstractPointersObjectReadNode.getUncached();
            final Object typeCodeObj = readNode.execute(receiver, 1);
            final int typeCode;
            if (typeCodeObj instanceof Long l) {
                typeCode = l.intValue();
            } else if (typeCodeObj instanceof final NativeObject no) {
                /* Might be stored as a byte object (symbol). Try to interpret as string. */
                typeCode = guessTypeCodeFromClassName(receiver.getSqueakClass().getClassName());
            } else {
                typeCode = guessTypeCodeFromClassName(receiver.getSqueakClass().getClassName());
            }
            return byteSizeForTypeCode(typeCode);
        }

        private static int guessTypeCodeFromClassName(final String className) {
            return switch (className) {
                case "TFVoidType" -> 1;
                case "TFFloatType" -> 2;
                case "TFDoubleType" -> 3;
                case "TFUInt8Type" -> 4;
                case "TFUInt16Type" -> 5;
                case "TFUInt32Type" -> 6;
                case "TFUInt64Type" -> 7;
                case "TFSInt8Type" -> 8;
                case "TFSInt16Type" -> 9;
                case "TFSInt32Type" -> 10;
                case "TFSInt64Type" -> 11;
                case "TFPointerType", "TFStringType", "TFExternalAddressType" -> 12;
                case "TFCharType" -> 1;
                case "TFIntType" -> 10; // default to sint32
                default -> 12; // default to pointer
            };
        }

        private static long byteSizeForTypeCode(final int typeCode) {
            return switch (typeCode) {
                case 1 -> 0;  // void
                case 2 -> 4;  // float
                case 3 -> 8;  // double
                case 4 -> 1;  // uint8
                case 5 -> 2;  // uint16
                case 6 -> 4;  // uint32
                case 7 -> 8;  // uint64
                case 8 -> 1;  // sint8
                case 9 -> 2;  // sint16
                case 10 -> 4; // sint32
                case 11 -> 8; // sint64
                case 12 -> 8; // pointer (64-bit)
                case 13 -> 1; // uchar
                case 14 -> 1; // schar
                case 15 -> 2; // ushort
                case 16 -> 2; // sshort
                case 17 -> 4; // uint
                case 18 -> 4; // sint
                case 19 -> OS.isWindows() ? 4 : 8; // ulong (LLP64 vs LP64)
                case 20 -> OS.isWindows() ? 4 : 8; // slong (LLP64 vs LP64)
                default -> 8; // default to pointer size
            };
        }
    }

    /**
     * Called during FFI callout method compilation to set up the function definition.
     * Stores argument types (with return type prepended) into the ExternalLibraryFunction.
     */
    @GenerateNodeFactory
    @SqueakPrimitive(names = "primitiveDefineFunction")
    protected abstract static class PrimDefineFunctionNode extends AbstractPrimitiveNode implements Primitive2WithFallback {
        @Specialization
        @TruffleBoundary
        protected static final Object doDefine(final PointersObject receiver, final ArrayObject argTypes, final Object returnType,
                        @Bind final Node node,
                        @Bind final SqueakImageContext image,
                        @Cached final ArrayObjectToObjectArrayCopyNode getObjectArrayNode,
                        @Cached final AbstractPointersObjectWriteNode writeNode) {
            final String className = receiver.getSqueakClass().getClassName();
            if ("TFFunctionDefinition".equals(className)) {
                return receiver;
            }
            final Object[] args = getObjectArrayNode.execute(node, argTypes);
            final Object[] allTypes = new Object[args.length + 1];
            allTypes[0] = returnType;
            System.arraycopy(args, 0, allTypes, 1, args.length);
            writeNode.execute(receiver, ObjectLayouts.EXTERNAL_LIBRARY_FUNCTION.ARG_TYPES, image.asArrayOfObjects(allTypes));
            return receiver;
        }
    }

    /**
     * Executes an FFI callout with an array of arguments.
     * The receiver is an ExternalLibraryFunction with the standard layout.
     */
    @GenerateNodeFactory
    @SqueakPrimitive(names = "primitiveCalloutWithArgs")
    protected abstract static class PrimCalloutWithArgsNode extends AbstractPrimitiveNode implements Primitive1WithFallback {
        @Specialization
        @TruffleBoundary
        protected final Object doCalloutWithArgs(final PointersObject receiver, final ArrayObject argArray,
                        @Bind final Node node,
                        @Cached final ArrayObjectToObjectArrayCopyNode getObjectArrayNode) {
            return doFFICallout(getContext(), receiver, receiver, getObjectArrayNode.execute(node, argArray));
        }
    }

    /**
     * Executes an FFI callout on the same thread. Used by Pharo's UFFI (TFExternalFunction).
     * The receiver is the caller object, the function argument is a TFExternalFunction with
     * slots: 1=Definition, 2=Name, 3=Module.
     */
    @GenerateNodeFactory
    @SqueakPrimitive(names = "primitiveSameThreadCallout")
    protected abstract static class PrimSameThreadCalloutNode extends AbstractPrimitiveNode implements Primitive2WithFallback {
        @Specialization
        @TruffleBoundary
        protected final Object doSameThreadCallout(final PointersObject receiver, final PointersObject function, final Object args,
                        @Bind final Node node,
                        @Bind final SqueakImageContext image,
                        @Cached final ArrayObjectToObjectArrayCopyNode getObjectArrayNode) {
            final AbstractPointersObjectReadNode readNode = AbstractPointersObjectReadNode.getUncached();

            final Object definition = readNode.execute(function, 1);
            final NativeObject nameObj = readNode.executeNative(function, 2);
            final Object moduleObj = readNode.execute(function, 3);

            final String name = nameObj.asStringUnsafe();
            final String moduleName = (moduleObj instanceof final NativeObject mo) ? mo.asStringUnsafe() : null;

            Object[] currentArgs;
            if (args instanceof final ArrayObject ao) {
                currentArgs = getObjectArrayNode.execute(node, ao);
            } else if (args == NilObject.SINGLETON) {
                currentArgs = new Object[0];
            } else {
                currentArgs = new Object[]{args};
            }

            /* Extract type information from the TFFunctionDefinition. */
            final List<String> nfiTypes = new ArrayList<>();
            final List<Boolean> isPointerArg = new ArrayList<>();

            final String defClassName = (definition instanceof final PointersObject defPo) ? defPo.getSqueakClass().getClassName() : "";
            if ("TFFunctionDefinition".equals(defClassName)) {
                extractTFDefinitionNfiTypes(readNode, (PointersObject) definition, nfiTypes, isPointerArg);
            } else if (definition instanceof final PointersObject defPo) {
                extractExternalFunctionNfiTypes(readNode, defPo, nfiTypes, isPointerArg);
            }

            /* Convert POINTER types to SINT64 in NFI signature (we pass native addresses as longs). */
            final List<String> nfiSignatureTypes = new ArrayList<>(nfiTypes.size());
            for (final String t : nfiTypes) {
                nfiSignatureTypes.add("POINTER".equals(t) ? "SINT64" : t);
            }

            /* Build the NFI signature and code. */
            final String nfiSignature = buildNfiSignature(nfiSignatureTypes);
            final String libPath = resolveLibraryPath(image, moduleName);
            final String nfiCode = String.format("load \"%s\" {%s%s}", libPath, name, nfiSignature);

            /* Allocate native memory for pointer arguments. */
            final List<NativeBuffer> nativeBuffers = new ArrayList<>();
            try (Arena arena = Arena.ofConfined()) {
                final Object[] nfiArgs = resolveArgumentsForNfi(currentArgs, nfiTypes, isPointerArg, arena, nativeBuffers);

                final Object value = callNative(image, name, nfiArgs, nfiCode);
                assert value != null;

                /* Copy back modified native buffers to Smalltalk objects. */
                copyBackNativeBuffers(nativeBuffers);

                return WrapToSqueakNode.executeUncached(value);
            } catch (UnsupportedMessageException | ArityException | UnknownIdentifierException | UnsupportedTypeException e) {
                LogUtils.MAIN.warning("ThreadedFFI callout failed for " + name + ": " + e);
                throw PrimitiveFailed.GENERIC_ERROR;
            } finally {
                clearTrackedObjects();
            }
        }
    }

    /**
     * Extracts NFI type strings directly from TFFunctionDefinition type objects.
     * This avoids going through the old FFI header word system.
     */
    private static void extractTFDefinitionNfiTypes(final AbstractPointersObjectReadNode readNode,
                    final PointersObject definition, final List<String> nfiTypes, final List<Boolean> isPointerArg) {
        /* TFFunctionDefinition: Slot 1=parameterTypes, Slot 2=returnType. (Slot 0=handle from ExternalObject.) */
        final Object returnTypeObj = readNode.execute(definition, 2);
        addNfiTypeFromTFType(readNode, returnTypeObj, nfiTypes, isPointerArg);

        final Object paramTypes = readNode.execute(definition, 1);
        final Object[] paramElements = extractCollectionElements(readNode, paramTypes);
        for (final Object paramType : paramElements) {
            addNfiTypeFromTFType(readNode, paramType, nfiTypes, isPointerArg);
        }
    }

    /** Extract elements from an ArrayObject or OrderedCollection (PointersObject). */
    private static Object[] extractCollectionElements(final AbstractPointersObjectReadNode readNode, final Object collection) {
        if (collection instanceof final ArrayObject array) {
            return array.getObjectStorage();
        } else if (collection instanceof final PointersObject po) {
            /* OrderedCollection: slot 0=array, slot 1=firstIndex, slot 2=lastIndex. */
            final String className = po.getSqueakClass().getClassName();
            if ("OrderedCollection".equals(className)) {
                final Object innerArray = readNode.execute(po, 0);
                if (innerArray instanceof final ArrayObject inner) {
                    final Object firstObj = readNode.execute(po, 1);
                    final Object lastObj = readNode.execute(po, 2);
                    final int first = (firstObj instanceof Long l) ? l.intValue() : 1;
                    final int last = (lastObj instanceof Long l) ? l.intValue() : inner.getObjectLength();
                    /* Smalltalk indices are 1-based; Java array is 0-based. */
                    final int count = last - first + 1;
                    if (count <= 0) {
                        return new Object[0];
                    }
                    final Object[] result = new Object[count];
                    final Object[] storage = inner.getObjectStorage();
                    System.arraycopy(storage, first - 1, result, 0, count);
                    return result;
                }
            }
        }
        return new Object[0];
    }

    private static void addNfiTypeFromTFType(final AbstractPointersObjectReadNode readNode,
                    final Object typeObj, final List<String> nfiTypes, final List<Boolean> isPointerArg) {
        if (typeObj instanceof final PointersObject typePo) {
            final String typeClassName = typePo.getSqueakClass().getClassName();
            if (typeClassName.startsWith("TF")) {
                final String nfiType = tfClassNameToNfiType(typeClassName);
                nfiTypes.add(nfiType);
                isPointerArg.add("POINTER".equals(nfiType));
            } else {
                /* ExternalType with COMPILED_SPEC — use old conversion. */
                try {
                    final NativeObject compiledSpec = readNode.executeNative(typePo, ObjectLayouts.EXTERNAL_TYPE.COMPILED_SPEC);
                    final int headerWord = compiledSpec.getInt(0);
                    final boolean isPtr = FFI_TYPES.isPointerType(headerWord);
                    nfiTypes.add(isPtr ? "POINTER" : FFI_TYPES.getTruffleTypeFromInt(headerWord));
                    isPointerArg.add(isPtr);
                } catch (final Exception e) {
                    nfiTypes.add("VOID");
                    isPointerArg.add(false);
                }
            }
        } else {
            nfiTypes.add("VOID");
            isPointerArg.add(false);
        }
    }

    private static String tfClassNameToNfiType(final String className) {
        return switch (className) {
            case "TFVoidType", "TFBasicType" -> "VOID";
            case "TFBoolType", "TFBooleanType" -> "UINT8";
            case "TFUInt8Type" -> "UINT8";
            case "TFSInt8Type" -> "SINT8";
            case "TFUInt16Type" -> "UINT16";
            case "TFSInt16Type" -> "SINT16";
            case "TFUInt32Type" -> "UINT32";
            case "TFSInt32Type" -> "SINT32";
            case "TFUInt64Type" -> "UINT64";
            case "TFSInt64Type" -> "SINT64";
            case "TFFloatType" -> "FLOAT";
            case "TFDoubleType" -> "DOUBLE";
            case "TFPointerType", "TFStringType", "TFExternalAddressType", "TFOOPType" -> "POINTER";
            case "TFIntType" -> OS.isWindows() ? "SINT32" : "SINT64";
            case "TFCharType" -> "SINT8";
            default -> "POINTER";
        };
    }

    /** Tracks native memory allocations for copy-back after callout. */
    private record NativeBuffer(MemorySegment segment, NativeObject original) {
    }

    /**
     * Resolves arguments for NFI calling. For pointer-type arguments, allocates native memory,
     * copies data from the tracked byte arrays, and passes native addresses. After the call,
     * copyBackNativeBuffers() must be called to copy results back to the Smalltalk objects.
     */
    private static Object[] resolveArgumentsForNfi(final Object[] args, final List<String> nfiTypes,
                    final List<Boolean> isPointerArg, final Arena arena, final List<NativeBuffer> nativeBuffers) {
        final Object[] nfiArgs = new Object[args.length];
        for (int i = 0; i < args.length; i++) {
            final int typeIndex = i + 1; // +1 because index 0 is return type
            final String nfiType = typeIndex < nfiTypes.size() ? nfiTypes.get(typeIndex) : null;
            final boolean isPtr = typeIndex < isPointerArg.size() && isPointerArg.get(typeIndex);
            if (isPtr && args[i] instanceof final NativeObject no && no.isByteType()) {
                /* ExternalAddress — read the fake address and resolve to native memory. */
                final long fakeAddr = readAddressFromExternalAddress(no);
                final NativeObject tracked = resolveTrackedObject(fakeAddr);
                if (tracked != null) {
                    /* Allocate native memory, copy byte data, and pass the address. */
                    final byte[] data = tracked.getByteStorage();
                    final MemorySegment seg = arena.allocate(data.length);
                    MemorySegment.copy(data, 0, seg, ValueLayout.JAVA_BYTE, 0, data.length);
                    nativeBuffers.add(new NativeBuffer(seg, tracked));
                    nfiArgs[i] = seg.address();
                } else if (fakeAddr == 0L) {
                    nfiArgs[i] = 0L;
                } else {
                    /* Real external address (e.g., from malloc/loadSymbol). */
                    nfiArgs[i] = fakeAddr;
                }
            } else if (args[i] instanceof final Long l) {
                nfiArgs[i] = narrowForNfi(nfiType, l);
            } else if (args[i] instanceof final NativeObject no && no.isByteType()) {
                nfiArgs[i] = no.getByteStorage();
            } else {
                nfiArgs[i] = args[i];
            }
        }
        return nfiArgs;
    }

    /** After a native call, copies modified native buffers back to the original Smalltalk byte arrays. */
    private static void copyBackNativeBuffers(final List<NativeBuffer> nativeBuffers) {
        for (final NativeBuffer nb : nativeBuffers) {
            final byte[] dst = nb.original.getByteStorage();
            MemorySegment.copy(nb.segment, ValueLayout.JAVA_BYTE, 0, dst, 0, dst.length);
        }
    }

    /** Narrow a Long value to the correct Java type for the given NFI type. */
    private static Object narrowForNfi(final String nfiType, final long value) {
        if (nfiType == null) {
            return value;
        }
        return switch (nfiType) {
            case "SINT8" -> (byte) value;
            case "UINT8" -> (byte) value;
            case "SINT16" -> (short) value;
            case "UINT16" -> (short) value;
            case "SINT32", "UINT32" -> (int) value;
            case "FLOAT" -> (float) value;
            case "DOUBLE" -> (double) value;
            default -> value;
        };
    }

    /** Builds an NFI signature string from the type list (first = return type, rest = param types). */
    private static String buildNfiSignature(final List<String> nfiTypes) {
        if (nfiTypes.isEmpty()) {
            return "";
        }
        final String returnType = nfiTypes.getFirst();
        final StringBuilder sb = new StringBuilder(32);
        sb.append('(');
        for (int i = 1; i < nfiTypes.size(); i++) {
            if (i > 1) {
                sb.append(',');
            }
            sb.append(nfiTypes.get(i));
        }
        sb.append("):").append(returnType).append(';');
        return sb.toString();
    }

    /* Shared FFI callout implementation for primitiveCalloutWithArgs (old-style ExternalLibraryFunction). */
    @TruffleBoundary
    private static Object doFFICallout(final SqueakImageContext image, final PointersObject externalLibraryFunction,
                    final AbstractSqueakObject receiver, final Object... arguments) {
        final List<Integer> headerWordList = new ArrayList<>();
        final AbstractPointersObjectReadNode readNode = AbstractPointersObjectReadNode.getUncached();
        final ArgTypeConversionNode conversionNode = ArgTypeConversionNode.getUncached();

        final ArrayObject argTypes = readNode.executeArray(externalLibraryFunction, ObjectLayouts.EXTERNAL_LIBRARY_FUNCTION.ARG_TYPES);
        if (argTypes != null && argTypes.getObjectStorage().length == arguments.length + 1) {
            for (final Object argumentType : argTypes.getObjectStorage()) {
                if (argumentType instanceof final PointersObject o) {
                    final NativeObject compiledSpec = readNode.executeNative(o, ObjectLayouts.EXTERNAL_TYPE.COMPILED_SPEC);
                    headerWordList.add(compiledSpec.getInt(0));
                }
            }
        }

        final Object[] argumentsConverted = convertArguments(conversionNode, headerWordList, arguments);
        final List<String> nfiArgTypeList = getArgTypeListFromHeaderWords(headerWordList);

        final String name = readNode.executeNative(externalLibraryFunction, ObjectLayouts.EXTERNAL_LIBRARY_FUNCTION.NAME).asStringUnsafe();
        final String moduleName = getModuleName(readNode, receiver, externalLibraryFunction);
        final String nfiCodeParams = generateNfiCodeParamsString(nfiArgTypeList);
        final String libPath = resolveLibraryPath(image, moduleName);
        final String nfiCode = String.format("load \"%s\" {%s%s}", libPath, name, nfiCodeParams);

        try {
            final Object value = callNative(image, name, argumentsConverted, nfiCode);
            assert value != null;
            return WrapToSqueakNode.executeUncached(conversionNode.execute(headerWordList.getFirst(), value));
        } catch (UnsupportedMessageException | ArityException | UnknownIdentifierException | UnsupportedTypeException e) {
            LogUtils.MAIN.warning("ThreadedFFI callout failed: " + e);
            throw PrimitiveFailed.GENERIC_ERROR;
        } finally {
            clearTrackedObjects();
        }
    }

    private static void extractExternalFunctionNfiTypes(final AbstractPointersObjectReadNode readNode,
                    final PointersObject definition, final List<String> nfiTypes, final List<Boolean> isPointerArg) {
        final ArrayObject argTypes = readNode.executeArray(definition, ObjectLayouts.EXTERNAL_LIBRARY_FUNCTION.ARG_TYPES);
        if (argTypes != null) {
            for (final Object argumentType : argTypes.getObjectStorage()) {
                if (argumentType instanceof final PointersObject o) {
                    final NativeObject compiledSpec = readNode.executeNative(o, ObjectLayouts.EXTERNAL_TYPE.COMPILED_SPEC);
                    final int headerWord = compiledSpec.getInt(0);
                    final boolean isPtr = FFI_TYPES.isPointerType(headerWord);
                    nfiTypes.add(isPtr ? "POINTER" : FFI_TYPES.getTruffleTypeFromInt(headerWord));
                    isPointerArg.add(isPtr);
                }
            }
        }
    }

    private static Object[] convertArguments(final ArgTypeConversionNode conversionNode,
                    final List<Integer> headerWordList, final Object[] arguments) {
        final Object[] converted = new Object[arguments.length];
        for (int j = 1; j < headerWordList.size() && j - 1 < arguments.length; j++) {
            converted[j - 1] = conversionNode.execute(headerWordList.get(j), arguments[j - 1]);
        }
        for (int j = headerWordList.size(); j <= arguments.length; j++) {
            converted[j - 1] = arguments[j - 1];
        }
        return converted;
    }

    private static List<String> getArgTypeListFromHeaderWords(final List<Integer> headerWordList) {
        final List<String> nfiArgTypeList = new ArrayList<>();
        for (final int headerWord : headerWordList) {
            nfiArgTypeList.add(FFI_TYPES.getTruffleTypeFromInt(headerWord));
        }
        return nfiArgTypeList;
    }

    private static Object callNative(final SqueakImageContext image, final String name,
                    final Object[] arguments, final String nfiCode)
                    throws UnsupportedMessageException, ArityException, UnknownIdentifierException, UnsupportedTypeException {
        final Source source = Source.newBuilder("nfi", nfiCode, "native").build();
        final Object library = image.env.parseInternal(source).call();
        final InteropLibrary interopLib = InteropLibrary.getFactory().getUncached(library);
        return interopLib.invokeMember(library, name, arguments);
    }

    private static String getModuleName(final AbstractPointersObjectReadNode readNode,
                    final AbstractSqueakObject receiver, final PointersObject externalLibraryFunction) {
        final Object moduleObject = readNode.execute(externalLibraryFunction, ObjectLayouts.EXTERNAL_LIBRARY_FUNCTION.MODULE);
        if (moduleObject != NilObject.SINGLETON) {
            return ((NativeObject) moduleObject).asStringUnsafe();
        } else if (receiver instanceof final PointersObject po) {
            return ((NativeObject) po.instVarAt0Slow(1)).asStringUnsafe();
        }
        return null;
    }

    /**
     * Resolves a library name to a loadable path. Handles system libraries (e.g., kernel32.dll
     * on Windows) and falls back to the library name itself, letting the OS loader resolve it.
     */
    @TruffleBoundary
    static String resolveLibraryPath(final SqueakImageContext image, final String moduleName) {
        if (moduleName == null || moduleName.isEmpty()) {
            throw PrimitiveFailed.GENERIC_ERROR;
        }

        final File moduleFile = new File(moduleName);
        if (moduleFile.isAbsolute() && moduleFile.exists()) {
            return moduleName;
        }

        final String libName = System.mapLibraryName(moduleName);
        final var libPath = image.getHomePath().resolve("lib" + File.separatorChar + libName);
        if (libPath.exists()) {
            return libPath.getAbsoluteFile().getPath();
        }

        if (OS.isWindows()) {
            if (moduleName.toLowerCase().endsWith(".dll")) {
                return moduleName;
            }
            return libName;
        }

        final String[] searchDirs = {"/lib", "/lib64", "/usr/lib", "/usr/lib64",
                        "/lib/x86_64-linux-gnu", "/usr/lib/x86_64-linux-gnu"};
        final String[] candidates = {libName, moduleName};
        for (final String dir : searchDirs) {
            for (final String candidate : candidates) {
                final File file = new File(dir, candidate);
                if (file.exists()) {
                    return file.getAbsolutePath();
                }
            }
        }

        return libName;
    }

    private static String generateNfiCodeParamsString(final List<String> argumentList) {
        final StringBuilder nfiCodeParams = new StringBuilder(32);
        if (!argumentList.isEmpty()) {
            final String returnType = argumentList.getFirst();
            argumentList.removeFirst();
            if (!argumentList.isEmpty()) {
                nfiCodeParams.append('(').append(String.join(",", argumentList)).append(')');
            } else {
                nfiCodeParams.append("()");
            }
            nfiCodeParams.append(':').append(returnType).append(';');
        }
        return nfiCodeParams.toString();
    }

    @Override
    public List<? extends NodeFactory<? extends AbstractPrimitiveNode>> getFactories() {
        return ThreadedFFIPluginFactory.getFactories();
    }
}
