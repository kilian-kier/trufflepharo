/*
 * Copyright (c) 2026 Software Architecture Group, Hasso Plattner Institute
 * Copyright (c) 2026 Oracle and/or its affiliates
 *
 * Licensed under the MIT License.
 */
package de.hpi.swa.trufflesqueak.nodes.plugins;

import com.oracle.truffle.api.CompilerDirectives.CompilationFinal;
import com.oracle.truffle.api.dsl.Bind;
import com.oracle.truffle.api.dsl.Cached;
import com.oracle.truffle.api.dsl.GenerateNodeFactory;
import com.oracle.truffle.api.dsl.NodeFactory;
import com.oracle.truffle.api.dsl.Specialization;
import com.oracle.truffle.api.interop.ArityException;
import com.oracle.truffle.api.interop.UnknownIdentifierException;
import com.oracle.truffle.api.interop.UnsupportedMessageException;
import com.oracle.truffle.api.interop.UnsupportedTypeException;
import com.oracle.truffle.api.nodes.Node;
import de.hpi.swa.trufflesqueak.exceptions.PrimitiveFailed;
import de.hpi.swa.trufflesqueak.image.SqueakImageContext;
import de.hpi.swa.trufflesqueak.interop.WrapToSqueakNode;
import de.hpi.swa.trufflesqueak.model.ArrayObject;
import de.hpi.swa.trufflesqueak.model.NativeObject;
import de.hpi.swa.trufflesqueak.model.NilObject;
import de.hpi.swa.trufflesqueak.model.PointersObject;
import de.hpi.swa.trufflesqueak.model.layout.ObjectLayouts;
import de.hpi.swa.trufflesqueak.nodes.accessing.AbstractPointersObjectNodes.AbstractPointersObjectWriteNode;
import de.hpi.swa.trufflesqueak.nodes.accessing.AbstractPointersObjectNodes.AbstractPointersObjectReadNode;
import de.hpi.swa.trufflesqueak.nodes.accessing.ArrayObjectNodes.ArrayObjectToObjectArrayCopyNode;
import de.hpi.swa.trufflesqueak.nodes.accessing.NativeObjectNodes.NativeObjectWriteNode;
import de.hpi.swa.trufflesqueak.nodes.plugins.SqueakFFIPrims.AbstractFFIPrimitiveNode;
import de.hpi.swa.trufflesqueak.nodes.primitives.AbstractPrimitiveFactoryHolder;
import de.hpi.swa.trufflesqueak.nodes.primitives.AbstractPrimitiveNode;
import de.hpi.swa.trufflesqueak.nodes.primitives.Primitive.Primitive0WithFallback;
import de.hpi.swa.trufflesqueak.nodes.primitives.Primitive.Primitive1WithFallback;
import de.hpi.swa.trufflesqueak.nodes.primitives.Primitive.Primitive2WithFallback;
import de.hpi.swa.trufflesqueak.nodes.primitives.SqueakPrimitive;
import de.hpi.swa.trufflesqueak.util.ArrayUtils;
import de.hpi.swa.trufflesqueak.util.LogUtils;
import de.hpi.swa.trufflesqueak.util.OS;
import de.hpi.swa.trufflesqueak.util.UnsafeUtils;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicLong;

public final class ThreadedFFIPlugin extends AbstractPrimitiveFactoryHolder {
    // Since we don't have real stable pointer addresses on the JVM, we just fake the addresses
    private static final AtomicLong NEXT_FAKE_ADDRESS = new AtomicLong(0x1000L);
    private static final Map<Long, NativeObject> TRACKED_OBJECTS = new HashMap<>();
    private static final Map<Long, String> NFI_SIGNATURES = new HashMap<>();
    private static final int POINTER_SIZE = 8;

    static long trackObject(final NativeObject object) {
        final long fakeAddr = NEXT_FAKE_ADDRESS.getAndIncrement();
        TRACKED_OBJECTS.put(fakeAddr, object);
        return fakeAddr;
    }

    static long trackSignature(final String signature) {
        final long fakeAddr = NEXT_FAKE_ADDRESS.getAndIncrement();
        NFI_SIGNATURES.put(fakeAddr, signature);
        return fakeAddr;
    }

    private enum TF_FFIType {
        VOID(1, 0, "VOID"),
        FLOAT(2, 4, "FLOAT"),
        DOUBLE(3, 8, "DOUBLE"),
        UINT8(4, 1, "UINT8"),
        UINT16(5, 2, "UINT16"),
        UINT32(6, 4, "UINT32"),
        UINT64(7, 8, "UINT64"),
        SINT8(8, 1, "SINT8"),
        SINT16(9, 2, "SINT16"),
        SINT32(10, 4, "SINT32"),
        SINT64(11, 8, "SINT64"),
        POINTER(12, POINTER_SIZE, "POINTER"),
        UCHAR(13, 1, "UINT8"),
        SCHAR(14, 1, "SINT8"),
        USHORT(15, 2, "UINT16"),
        SSHORT(16, 2, "SINT16"),
        UINT(17, 4, "UINT32"),
        SINT(18, 4, "SINT32"),
        ULONG(19, OS.isWindows() ? 4 : POINTER_SIZE, OS.isWindows() ? "UINT32" : "UINT64"),
        SLONG(20, OS.isWindows() ? 4 : POINTER_SIZE, OS.isWindows() ? "SINT32" : "SINT64");

        public final int code;
        public final int size;
        public final String nfiString;

        TF_FFIType(final int code, final int size, final String nfiString) {
            this.code = code;
            this.size = size;
            this.nfiString = nfiString;
        }
    }

    @GenerateNodeFactory
    @SqueakPrimitive(names = "primitiveGetAddressOfOOP")
    protected abstract static class PrimGetAddressOfOOPNode extends AbstractPrimitiveNode implements Primitive1WithFallback {
        @Specialization(guards = "object.isByteType()")
        protected static final long getAddressByte(@SuppressWarnings("unused") final Object receiver, final NativeObject object) {
            return trackObject(object);
        }
    }

    @GenerateNodeFactory
    @SqueakPrimitive(names = "primitiveFillBasicType")
    protected abstract static class PrimFillBasicTypeNode extends AbstractPrimitiveNode implements Primitive0WithFallback {
        @Specialization
        protected static final Object fillBasicType(final PointersObject receiver,
                        @Cached final AbstractPointersObjectReadNode readNode,
                        @Cached final NativeObjectWriteNode writeNode,
                        @Bind final Node node) {
            final long typeCode = (long) readNode.execute(receiver, ObjectLayouts.TF_BASIC_TYPE.TYPE_CODE);
            final NativeObject handler = (NativeObject) readNode.execute(receiver, ObjectLayouts.TF_BASIC_TYPE.HANDLER);
            writeNode.execute(node, handler, 7, typeCode);
            return receiver;
        }
    }

    @GenerateNodeFactory
    @SqueakPrimitive(names = "primitiveTypeByteSize")
    protected abstract static class PrimTypeByteSizeNode extends AbstractPrimitiveNode implements Primitive0WithFallback {
        @CompilationFinal(dimensions = 1) private static final long[] SIZES_BY_CODE = new long[TF_FFIType.values().length + 1];

        // For better performance, we pre-fill a map between code to size.
        static {
            for (TF_FFIType type : TF_FFIType.values()) {
                SIZES_BY_CODE[type.code] = type.size;
            }
        }

        @Specialization
        protected static final long typeByteSize(final PointersObject receiver,
                        @Cached final AbstractPointersObjectReadNode readNode) {
            final long typeCode = (long) readNode.execute(receiver, ObjectLayouts.TF_BASIC_TYPE.TYPE_CODE);

            assert (typeCode >= 1 && typeCode < SIZES_BY_CODE.length);
            return SIZES_BY_CODE[Math.toIntExact(typeCode)];
        }
    }

    @GenerateNodeFactory
    @SqueakPrimitive(names = "primitiveDefineFunction")
    protected abstract static class PrimDefineFunctionNode extends AbstractPrimitiveNode implements Primitive2WithFallback {
        @Specialization
        protected static final Object defineFunction(final PointersObject receiver, final ArrayObject parameterHandlers, final Object returnType,
                        @Bind final Node node,
                        @Bind final SqueakImageContext image,
                        @Cached final ArrayObjectToObjectArrayCopyNode getObjectArrayNode,
                        @Cached final AbstractPointersObjectReadNode readNode,
                        @Cached final AbstractPointersObjectWriteNode writeNode) {
            final Object[] args = getObjectArrayNode.execute(node, parameterHandlers);
            final String nfiSignature = buildNFISignature(args, returnType, image);
            final long fakeAddress = trackSignature(nfiSignature);
            final NativeObject handler = (NativeObject) readNode.execute(receiver, 0);
            final byte[] fakeAddressByteArray = ArrayUtils.longToAddressByteArray(fakeAddress);
            writeNode.execute(receiver, 0, NativeObject.newNativeBytes(handler.getSqueakClass(), fakeAddressByteArray));
            return receiver;
        }

        private static String buildNFISignature(final Object[] params, final Object returnType, final SqueakImageContext image) {
            final StringBuilder builder = new StringBuilder();
            builder.append("(");

            for (int i = 0; i < params.length; i++) {
                builder.append(resolveType(params[i], image));
                if (i < params.length - 1) {
                    builder.append(",");
                }
            }

            builder.append("):").append(resolveType(returnType, image)).append(';');

            return builder.toString();
        }

        private static String resolveType(final Object typeObj, final SqueakImageContext image) {
            final long code = ((NativeObject) typeObj).getByte(7);
            return TF_FFIType.values()[(int) code - 1].nfiString;
        }
    }

    @GenerateNodeFactory
    @SqueakPrimitive(names = "primitiveSameThreadCallout")
    protected abstract static class PrimSameThreadCalloutNode extends AbstractFFIPrimitiveNode implements Primitive2WithFallback {
        @Specialization
        protected final Object sameThreadCallout(@SuppressWarnings("unused") final PointersObject receiver, final PointersObject function, final Object args,
                        @Bind final Node node,
                        @Bind final SqueakImageContext image,
                        @Cached final ArrayObjectToObjectArrayCopyNode getObjectArrayNode) {
            final AbstractPointersObjectReadNode readNode = AbstractPointersObjectReadNode.getUncached();

            final PointersObject definition = (PointersObject) readNode.execute(function, 1);
            final NativeObject nameObj = readNode.executeNative(function, 2);
            final Object moduleObj = readNode.execute(function, 3);

            final long fakeSignatureAddress = ArrayUtils.addressByteArrayToLong(((NativeObject) readNode.execute(definition, 0)).getByteStorage());
            final String functionSignature = NFI_SIGNATURES.get(fakeSignatureAddress);
            final String name = nameObj.asStringUnsafe();
            final String moduleName = (moduleObj instanceof final NativeObject module) ? module.asStringUnsafe() : null;
            final Object[] arguments = getObjectArrayNode.execute(node, (ArrayObject) args);
            final Object[] convertedArguments = new Object[arguments.length];
            final List<Long> nativeAddresses = new ArrayList<>();
            for (int i = 0; i < arguments.length; i++) {
                if (arguments[i] instanceof final NativeObject argument) {
                    assert argument.getSqueakClass().getClassName().equals("ExternalAddress");
                    final long fakeObjectAddress = ArrayUtils.addressByteArrayToLong(argument.getByteStorage());
                    if (fakeObjectAddress == 0) {
                        convertedArguments[i] = 0;
                    } else {
                        final byte[] data = argument.getByteStorage();
                        final long nativeAddress = UnsafeUtils.allocateNativeBytes(data);
                        nativeAddresses.add(nativeAddress);
                        convertedArguments[i] = nativeAddress;
                    }
                } else {
                    convertedArguments[i] = arguments[i];
                }
            }
            final String nfiCode = String.format("load \"%s\" {%s%s}", getPath(image, moduleName), name, functionSignature);
            try {
                // TODO: refactor and deduplicate with SqueakFFIPrims
                final Object value = calloutToLib(image, name, convertedArguments, nfiCode);
                assert value != null;
                return WrapToSqueakNode.executeUncached(value);
            } catch (UnsupportedMessageException | ArityException | UnknownIdentifierException |
                            UnsupportedTypeException e) {
                LogUtils.MAIN.warning(e.toString());
                // TODO: return correct error code.
                throw PrimitiveFailed.GENERIC_ERROR;
            } catch (final Exception e) {
                LogUtils.MAIN.warning(e.toString());
                // TODO: handle exception
                throw PrimitiveFailed.GENERIC_ERROR;
            } finally {
                for (long address : nativeAddresses) {
                    UnsafeUtils.copyNativeBytesBackAndFree(address, new byte[0]); // TODO: why copy?
                }
            }
        }
    }

    @Override
    public List<? extends NodeFactory<? extends AbstractPrimitiveNode>> getFactories() {
        return ThreadedFFIPluginFactory.getFactories();
    }
}
