/*
 * Copyright (c) 2017-2026 Software Architecture Group, Hasso Plattner Institute
 * Copyright (c) 2021-2026 Oracle and/or its affiliates
 *
 * Licensed under the MIT License.
 */
package de.hpi.swa.trufflesqueak.nodes.plugins;

import java.util.List;

import com.oracle.truffle.api.CompilerDirectives.TruffleBoundary;
import com.oracle.truffle.api.dsl.Bind;
import com.oracle.truffle.api.dsl.GenerateNodeFactory;
import com.oracle.truffle.api.dsl.NodeFactory;
import com.oracle.truffle.api.dsl.Specialization;
import com.oracle.truffle.api.interop.InteropLibrary;
import com.oracle.truffle.api.interop.UnsupportedMessageException;
import com.oracle.truffle.api.source.Source;

import de.hpi.swa.trufflesqueak.exceptions.PrimitiveFailed;
import de.hpi.swa.trufflesqueak.image.SqueakImageContext;
import de.hpi.swa.trufflesqueak.model.ArrayObject;
import de.hpi.swa.trufflesqueak.model.ClassObject;
import de.hpi.swa.trufflesqueak.model.NativeObject;
import de.hpi.swa.trufflesqueak.model.NilObject;
import de.hpi.swa.trufflesqueak.model.PointersObject;
import de.hpi.swa.trufflesqueak.nodes.primitives.AbstractPrimitiveFactoryHolder;
import de.hpi.swa.trufflesqueak.nodes.primitives.AbstractPrimitiveNode;
import de.hpi.swa.trufflesqueak.nodes.primitives.Primitive.Primitive0WithFallback;
import de.hpi.swa.trufflesqueak.nodes.primitives.Primitive.Primitive2WithFallback;
import de.hpi.swa.trufflesqueak.nodes.primitives.SqueakPrimitive;
import de.hpi.swa.trufflesqueak.util.UnsafeUtils;
import de.hpi.swa.trufflesqueak.util.VarHandleUtils;

public final class ThreadedFFIPlugin extends AbstractPrimitiveFactoryHolder {

    private static final int[] BASIC_TYPE_SIZES = {
                    0, // 0: unused
                    0, // 1: void
                    4, // 2: float
                    8, // 3: double
                    1, // 4: uint8
                    2, // 5: uint16
                    4, // 6: uint32
                    8, // 7: uint64
                    1, // 8: sint8
                    2, // 9: sint16
                    4, // 10: sint32
                    8, // 11: sint64
                    8, // 12: pointer
                    1, // 13: uchar
                    1, // 14: schar
                    2, // 15: ushort
                    2, // 16: sshort
                    4, // 17: uint
                    4, // 18: sint
                    8, // 19: ulong (64-bit)
                    8, // 20: slong (64-bit)
    };

    @Override
    public List<? extends NodeFactory<? extends AbstractPrimitiveNode>> getFactories() {
        return ThreadedFFIPluginFactory.getFactories();
    }

    @GenerateNodeFactory
    @SqueakPrimitive(names = {"primitiveFillBasicType", "primFillType"})
    protected abstract static class PrimFillBasicTypeNode extends AbstractPrimitiveNode implements Primitive0WithFallback {
        @Specialization
        protected static final Object doFill(final PointersObject receiver,
                        @Bind final SqueakImageContext image) {
            final Object typeCodeObj = receiver.instVarAt0Slow(2);
            final long typeCode = typeCodeObj instanceof final Long l ? l : 0L;
            final ClassObject externalAddressClass = (ClassObject) image.getExternalAddressClass();
            receiver.instVarAtPut0Slow(0, newExternalAddress(externalAddressClass, 0xDEADEFF10000L + typeCode));
            return receiver;
        }

        private static NativeObject newExternalAddress(final ClassObject cls, final long pointer) {
            return NativeObject.newNativeBytes(cls,
                            new byte[]{(byte) pointer, (byte) (pointer >> 8), (byte) (pointer >> 16), (byte) (pointer >> 24), (byte) (pointer >> 32), (byte) (pointer >> 40),
                                            (byte) (pointer >> 48), (byte) (pointer >> 56)});
        }
    }

    @GenerateNodeFactory
    @SqueakPrimitive(names = "primitiveTypeByteSize")
    protected abstract static class PrimTypeByteSizeNode extends AbstractPrimitiveNode implements Primitive0WithFallback {
        @Specialization
        protected static final long doSize(final PointersObject receiver) {
            final Object handleObj = receiver.instVarAt0Slow(0);
            if (handleObj instanceof final NativeObject handle && handle.isByteType()) {
                final long magic = VarHandleUtils.getLongFromBytes(handle.getByteStorage(), 0);
                if ((magic & 0xFFFFFFFF0000L) == 0xDEADEFF10000L) {
                    final int typeCode = (int) (magic & 0xFFFF);
                    if (typeCode >= 1 && typeCode < BASIC_TYPE_SIZES.length) {
                        return BASIC_TYPE_SIZES[typeCode];
                    }
                }
            }
            throw PrimitiveFailed.andTransferToInterpreter();
        }
    }

    @GenerateNodeFactory
    @SqueakPrimitive(names = {"primitiveDefineFunction", "primDefineFunctionWith:returnType:"})
    protected abstract static class PrimDefineFunctionWithReturnTypeNode extends AbstractPrimitiveNode implements Primitive2WithFallback {
        @Specialization
        protected static final Object doDefine(final PointersObject receiver, @SuppressWarnings("unused") final Object parameterTypes,
                        @SuppressWarnings("unused") final Object returnType,
                        @Bind final SqueakImageContext image) {
            final ClassObject externalAddressClass = (ClassObject) image.getExternalAddressClass();
            receiver.instVarAtPut0Slow(0, NativeObject.newNativeBytes(externalAddressClass, new byte[]{1, 0, 0, 0, 0, 0, 0, 0}));
            return receiver;
        }
    }

    @GenerateNodeFactory
    @SqueakPrimitive(names = "primitiveSameThreadCallout")
    protected abstract static class PrimSameThreadCalloutNode extends AbstractPrimitiveNode implements Primitive2WithFallback {
        private static final String[] NFI_TYPE_NAMES = {
                        "VOID",     // 0: unused
                        "VOID",     // 1: void
                        "FLOAT",    // 2: float
                        "DOUBLE",   // 3: double
                        "UINT8",    // 4: uint8
                        "UINT16",   // 5: uint16
                        "UINT32",   // 6: uint32
                        "UINT64",   // 7: uint64
                        "SINT8",    // 8: sint8
                        "SINT16",   // 9: sint16
                        "SINT32",   // 10: sint32
                        "SINT64",   // 11: sint64
                        "POINTER",  // 12: pointer
                        "UINT8",    // 13: uchar
                        "SINT8",    // 14: schar
                        "UINT16",   // 15: ushort
                        "SINT16",   // 16: sshort
                        "UINT32",   // 17: uint
                        "SINT32",   // 18: sint
                        "UINT64",   // 19: ulong (64-bit)
                        "SINT64",   // 20: slong (64-bit)
        };

        @Specialization
        @TruffleBoundary
        protected static final Object doCallout(@SuppressWarnings("unused") final Object receiver, final PointersObject externalFunction,
                        final ArrayObject argumentsArray,
                        @Bind final SqueakImageContext image) {
            final PointersObject definition = (PointersObject) externalFunction.instVarAt0Slow(1);
            final Object handleObj = externalFunction.instVarAt0Slow(0);
            if (!(handleObj instanceof final NativeObject handle) || !handle.isByteType()) {
                throw PrimitiveFailed.andTransferToInterpreter();
            }
            final long functionPointer = VarHandleUtils.getLongFromBytes(handle.getByteStorage(), 0);
            if (functionPointer == 0) {
                throw PrimitiveFailed.andTransferToInterpreter();
            }

            final Object paramTypesObj = definition.instVarAt0Slow(1);
            final Object returnTypeObj = definition.instVarAt0Slow(2);

            final int returnTypeCode = getTypeCode(returnTypeObj);
            final String returnTypeNfi = getNfiTypeName(returnTypeCode);

            final StringBuilder sigBuilder = new StringBuilder();
            sigBuilder.append('(');

            final Object[] args;
            if (argumentsArray.isObjectType()) {
                args = argumentsArray.getObjectStorage();
            } else {
                args = new Object[0];
            }

            int[] paramTypeCodes = new int[args.length];
            final Object[] paramTypeObjs = extractOrderedCollectionItems(paramTypesObj);
            if (paramTypeObjs != null) {
                for (int i = 0; i < args.length && i < paramTypeObjs.length; i++) {
                    paramTypeCodes[i] = getTypeCode(paramTypeObjs[i]);
                }
            }

            for (int i = 0; i < args.length; i++) {
                if (i > 0) {
                    sigBuilder.append(',');
                }
                sigBuilder.append(getNfiTypeName(paramTypeCodes[i]));
            }
            sigBuilder.append("):").append(returnTypeNfi);

            final Object[] convertedArgs = new Object[args.length];
            for (int i = 0; i < args.length; i++) {
                convertedArgs[i] = convertArgument(args[i], paramTypeCodes[i]);
            }

            try {
                final InteropLibrary interop = InteropLibrary.getUncached();
                final String sig = sigBuilder.toString();
                final Object nfiSymbol = image.nfiSymbols.get(functionPointer);
                if (nfiSymbol == null) {
                    throw PrimitiveFailed.andTransferToInterpreter();
                }
                final Object signature = image.env.parseInternal(
                                Source.newBuilder("nfi", sig, "native").build()).call();
                final Object boundFunction = interop.invokeMember(signature, "bind", nfiSymbol);
                final Object result = interop.execute(boundFunction, convertedArgs);
                return convertResult(result, returnTypeCode);
            } catch (final PrimitiveFailed pf) {
                throw pf;
            } catch (final Exception e) {
                throw PrimitiveFailed.andTransferToInterpreter();
            }
        }

        private static Object[] extractOrderedCollectionItems(final Object obj) {
            if (obj instanceof final ArrayObject arr && arr.isObjectType()) {
                return arr.getObjectStorage();
            }
            if (obj instanceof final PointersObject oc) {
                final Object arrayObj = oc.instVarAt0Slow(0);
                if (arrayObj instanceof final ArrayObject arr && arr.isObjectType()) {
                    final Object firstObj = oc.instVarAt0Slow(1);
                    final Object lastObj = oc.instVarAt0Slow(2);
                    if (firstObj instanceof final Long first && lastObj instanceof final Long last) {
                        final Object[] storage = arr.getObjectStorage();
                        final int from = first.intValue() - 1;
                        final int to = last.intValue();
                        if (from >= 0 && to <= storage.length) {
                            final Object[] result = new Object[to - from];
                            System.arraycopy(storage, from, result, 0, result.length);
                            return result;
                        }
                    }
                }
            }
            return null;
        }

        private static int getTypeCode(final Object typeObj) {
            if (typeObj instanceof final PointersObject type) {
                final Object code = type.instVarAt0Slow(2);
                if (code instanceof final Long l) {
                    return l.intValue();
                }
            }
            return 1;
        }

        private static String getNfiTypeName(final int typeCode) {
            if (typeCode >= 0 && typeCode < NFI_TYPE_NAMES.length) {
                return NFI_TYPE_NAMES[typeCode];
            }
            return "SINT64";
        }

        private static Object convertArgument(final Object arg, final int typeCode) {
            if (arg instanceof final NativeObject nObj && nObj.isByteType()) {
                final long ptr = VarHandleUtils.getLongFromBytes(nObj.getByteStorage(), 0);
                return ptr;
            } else if (arg instanceof final Long l) {
                return l;
            } else if (arg == NilObject.SINGLETON) {
                return 0L;
            } else if (arg instanceof final Double d) {
                return d;
            }
            return 0L;
        }

        private static Object convertResult(final Object result, final int returnTypeCode) {
            if (result == null || returnTypeCode == 1) {
                return 0L;
            }
            final InteropLibrary interop = InteropLibrary.getUncached();
            try {
                if (interop.fitsInLong(result)) {
                    return interop.asLong(result);
                } else if (interop.fitsInDouble(result)) {
                    return interop.asDouble(result);
                } else if (interop.isPointer(result)) {
                    return interop.asPointer(result);
                }
            } catch (final UnsupportedMessageException e) {
                // fall through
            }
            return 0L;
        }
    }
}
