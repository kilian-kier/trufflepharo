/*
 * Copyright (c) 2017-2025 Software Architecture Group, Hasso Plattner Institute
 * Copyright (c) 2021-2025 Oracle and/or its affiliates
 *
 * Licensed under the MIT License.
 */
package de.hpi.swa.trufflesqueak.image;

import com.oracle.truffle.api.CompilerDirectives;

import de.hpi.swa.trufflesqueak.exceptions.SqueakExceptions.SqueakException;
import de.hpi.swa.trufflesqueak.image.SqueakImageConstants.ObjectHeader;
import de.hpi.swa.trufflesqueak.model.ArrayObject;
import de.hpi.swa.trufflesqueak.model.BlockClosureObject;
import de.hpi.swa.trufflesqueak.model.CharacterObject;
import de.hpi.swa.trufflesqueak.model.ClassObject;
import de.hpi.swa.trufflesqueak.model.CompiledCodeObject;
import de.hpi.swa.trufflesqueak.model.ContextObject;
import de.hpi.swa.trufflesqueak.model.EmptyObject;
import de.hpi.swa.trufflesqueak.model.EphemeronObject;
import de.hpi.swa.trufflesqueak.model.FloatObject;
import de.hpi.swa.trufflesqueak.model.NativeObject;
import de.hpi.swa.trufflesqueak.model.NilObject;
import de.hpi.swa.trufflesqueak.model.PointersObject;
import de.hpi.swa.trufflesqueak.model.VariablePointersObject;
import de.hpi.swa.trufflesqueak.model.WeakVariablePointersObject;
import de.hpi.swa.trufflesqueak.nodes.plugins.LargeIntegers;
import de.hpi.swa.trufflesqueak.util.LogUtils;
import de.hpi.swa.trufflesqueak.util.MiscUtils;
import de.hpi.swa.trufflesqueak.util.VarHandleUtils;

public final class SqueakImageChunk {
    private final SqueakImageReader reader;
    private final long header;
    private final int position;
    private final byte[] bytes;

    private Object object;
    private ClassObject squeakClass;

    public SqueakImageChunk(final SqueakImageReader reader, final long header, final int position, final byte[] bytes) {
        this.reader = reader;
        this.header = header;
        this.position = position;
        this.bytes = bytes;
        if (bytes == null) { /* Ignored object (see SqueakImageReader#ignoreObjectData) */
            assert SqueakImageReader.isHiddenObject(getClassIndex());
            object = NilObject.SINGLETON;
        }
    }

    public ClassObject asClassObject() {
        if (object == null) {
            if (getFormat() != 1) {
                return null; /* Not a class-format object. */
            }
            return new ClassObject(this);
        } else if (object == NilObject.SINGLETON) {
            return null;
        } else if (object instanceof final ClassObject classObject) {
            return classObject;
        } else {
            return null; /* Already instantiated as another type. */
        }
    }

    public Object asObject() {
        if (object != null) {
            return object;
        }
        final ClassObject classObject = getSqueakClass();
        if (classObject == null) {
            // nil out unreachable object without class
            object = NilObject.SINGLETON;
            return object;
        }
        final SqueakImageContext image = getImage();
        final int format = getFormat();
        if (format == 0) { // no fields
            return new EmptyObject(this);
        } else if (format == 1) { // fixed pointers
            if (classObject.instancesAreClasses()) {
                /*
                 * In rare cases, there are still some classes that are not in the class table for
                 * some reason (e.g. not completely removed from the system yet).
                 */
                return new ClassObject(this);
            } else {
                return new PointersObject(this);
            }
        } else if (format == 2) { // indexable fields
            return new ArrayObject(this);
        } else if (format == 3) { // fixed and indexable fields
            if (classObject == image.methodContextClass) {
                return new ContextObject(this);
            } else if (image.isBlockClosureClass(classObject) || image.isFullBlockClosureClass(classObject)) {
                return new BlockClosureObject(this);
            } else {
                return new VariablePointersObject(this);
            }
        } else if (format == 4) { // indexable weak fields
            return new WeakVariablePointersObject(this);
        } else if (format == 5) { // fixed fields, special notification
            return new EphemeronObject(this);
        } else if (format <= 8) {
            throw CompilerDirectives.shouldNotReachHere("Should never happen (unused format)");
        } else if (format == 9) { // 64-bit integers
            return NativeObject.newNativeLongs(this);
        } else if (format <= 11) { // 32-bit integers
            if (classObject == image.floatClass) {
                return FloatObject.newFrom(this);
            } else {
                return NativeObject.newNativeInts(this);
            }
        } else if (format <= 15) { // 16-bit integers
            return NativeObject.newNativeShorts(this);
        } else if (format <= 23) { // bytes
            if (squeakClass == image.largePositiveIntegerClass) {
                return LargeIntegers.normalize(this, false);
            } else if (squeakClass == image.largeNegativeIntegerClass) {
                return LargeIntegers.normalize(this, true);
            } else {
                return NativeObject.newNativeBytes(this);
            }
        } else { // compiled methods
            assert format <= 31;
            return new CompiledCodeObject(this);
        }
    }

    public void setObject(final Object value) {
        assert object == null || object == value : "Cannot set object to " + de.hpi.swa.trufflesqueak.util.MiscUtils.toObjectString(value) + " as it is already set to " + de.hpi.swa.trufflesqueak.util.MiscUtils.toObjectString(object);
        object = value;
    }

    public Object getObject() {
        return object;
    }

    public boolean isNil() {
        return object == NilObject.SINGLETON;
    }

    public int getFormat() {
        final int format = ObjectHeader.getFormat(header);
        assert 0 <= format && format != 6 && format != 8 && format <= 31 : "Unexpected format";
        return format;
    }

    public int getHash() {
        return ObjectHeader.getHash(header);
    }

    public long getHeader() {
        return header;
    }

    public ClassObject getSqueakClass() {
        if (squeakClass == null) {
            final SqueakImageChunk classChunk = getClassChunk();
            if (classChunk == null) {
                 return null;
            }
            squeakClass = classChunk.asClassObject();
        }
        return squeakClass;
    }

    public SqueakImageContext getImage() {
        return reader.image;
    }

    public int getPosition() {
        return position;
    }

    public SqueakImageChunk getClassChunk() {
        final int classIndex = getClassIndex();
        final int majorIndex = de.hpi.swa.trufflesqueak.image.SqueakImageConstants.majorClassIndexOf(classIndex);
        final int minorIndex = de.hpi.swa.trufflesqueak.image.SqueakImageConstants.minorClassIndexOf(classIndex);
        final long pagePtr = reader.hiddenRootsChunk.getWord(majorIndex);
        if (pagePtr == reader.nilPointer || pagePtr == reader.baseAddress) {
            return null;
        }
        final SqueakImageChunk classTablePage = reader.chunkMap.get(pagePtr);
        if (classTablePage == null || classTablePage.isNil()) {
            return null; /* Class page does not exist (Pharo sparse class table). */
        }
        if (classTablePage.getBytes() == null || classTablePage.getBytes().length == 0) {
            return null; /* Empty class table page. */
        }
        final long classPtr = classTablePage.getWord(minorIndex);
        if (classPtr == reader.nilPointer || classPtr == reader.baseAddress) {
             return null;
        }
        return reader.chunkMap.get(classPtr);
    }

    public void setSqueakClass(final ClassObject baseSqueakObject) {
        squeakClass = baseSqueakObject;
    }

    public SqueakImageChunk getChunk(final int index) {
        final long pointer = getWord(index);
        assert (pointer & 7) == SqueakImageConstants.OBJECT_TAG;
        final SqueakImageChunk chunk = reader.chunkMap.get(pointer);
        assert chunk != null : "Unable to find chunk for index " + index;
        return chunk;
    }

    public Object getPointer(final int index) {
        return decodePointer(getWord(index));
    }

    public Object[] getPointers(final int start) {
        return getPointers(start, getWordSize());
    }

    public Object[] getPointers(final int start, final int end) {
        final int numObjects = end - start;
        final Object[] result = new Object[numObjects];
        for (int i = 0; i < numObjects; i++) {
            result[i] = getPointer(start + i);
        }
        return result;
    }

    private Object decodePointer(final long ptr) {
        if (ptr == reader.nilPointer || ptr == reader.baseAddress) {
            return NilObject.SINGLETON;
        }
        switch ((int) (ptr & 7)) {
            case SqueakImageConstants.OBJECT_TAG:
                final SqueakImageChunk chunk = reader.chunkMap.get(ptr);
                if (chunk == null) {
                    LogUtils.IMAGE.warning(() -> "Bogus pointer: " + ptr + ". Treating as smallint.");
                    return ptr >>> SqueakImageConstants.NUM_TAG_BITS;
                } else {
                    assert bytes != null : "Must not be an ignored object";
                    return chunk.asObject();
                }
            case SqueakImageConstants.SMALL_INTEGER_TAG: // SmallInteger
                return ptr >> SqueakImageConstants.NUM_TAG_BITS;
            case SqueakImageConstants.CHARACTER_TAG: // Character
                return CharacterObject.valueOf(ptr >> SqueakImageConstants.NUM_TAG_BITS);
            case SqueakImageConstants.SMALL_FLOAT_TAG:
                /* SmallFloat (see Spur64BitMemoryManager>>#smallFloatBitsOf:). */
                long valueWithoutTag = ptr >>> SqueakImageConstants.NUM_TAG_BITS;
                if (valueWithoutTag > 1) {
                    valueWithoutTag += SqueakImageConstants.SMALL_FLOAT_TAG_BITS_MASK;
                }
                final double value = Double.longBitsToDouble(Long.rotateRight(valueWithoutTag, 1));
                assert Double.isFinite(value) : "SmallFloats must be finite";
                return value;
            default:
                throw SqueakException.create("Unexpected pointer");
        }
    }

    public int getClassIndex() {
        return ObjectHeader.getClassIndex(header);
    }

    public byte[] getBytes() {
        return bytes;
    }

    public long getWord(final int index) {
        return VarHandleUtils.getLong(bytes, index);
    }

    public void setWord(final int index, final long value) {
        VarHandleUtils.putLong(bytes, index, value);
    }

    public int getWordSize() {
        return bytes.length / SqueakImageConstants.WORD_SIZE;
    }
}
