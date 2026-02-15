/*
 * Copyright (c) 2017-2026 Software Architecture Group, Hasso Plattner Institute
 * Copyright (c) 2021-2026 Oracle and/or its affiliates
 *
 * Licensed under the MIT License.
 */
package de.hpi.swa.trufflesqueak.image;

import java.io.IOException;
import java.nio.ByteOrder;
import java.nio.MappedByteBuffer;
import java.nio.channels.FileChannel;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.util.Arrays;
import java.util.HashSet;
import java.util.logging.Level;

import com.oracle.truffle.api.CompilerDirectives.TruffleBoundary;
import com.oracle.truffle.api.TruffleFile;

import de.hpi.swa.trufflesqueak.exceptions.SqueakExceptions.SqueakException;
import de.hpi.swa.trufflesqueak.model.AbstractSqueakObjectWithClassAndHash;
import de.hpi.swa.trufflesqueak.model.AbstractSqueakObjectWithHash;
import de.hpi.swa.trufflesqueak.model.ArrayObject;
import de.hpi.swa.trufflesqueak.model.BooleanObject;
import de.hpi.swa.trufflesqueak.model.ClassObject;
import de.hpi.swa.trufflesqueak.model.NativeObject;
import de.hpi.swa.trufflesqueak.model.NilObject;
import de.hpi.swa.trufflesqueak.model.layout.ObjectLayouts.CLASS;
import de.hpi.swa.trufflesqueak.model.layout.ObjectLayouts.METACLASS;
import de.hpi.swa.trufflesqueak.model.layout.ObjectLayouts.SPECIAL_OBJECT;
import de.hpi.swa.trufflesqueak.nodes.accessing.ArrayObjectNodes.ArrayObjectReadNode;
import de.hpi.swa.trufflesqueak.util.ArrayUtils;
import de.hpi.swa.trufflesqueak.util.LogUtils;
import de.hpi.swa.trufflesqueak.util.MiscUtils;
import de.hpi.swa.trufflesqueak.util.UnsafeUtils;

public final class SqueakImageReader {
    public SqueakImageChunk hiddenRootsChunk;

    public final AddressToChunkMap chunkMap = new AddressToChunkMap();
    public final SqueakImageContext image;
    long baseAddress;
    private int headerSize;
    private long specialObjectsPointer;
    long nilPointer;

    private SqueakImageChunk freePageList;

    public SqueakImageReader(final SqueakImageContext image) {
        this.image = image;
    }

    /*
     * Image reading happens only once per TruffleSqueak instance and should therefore be excluded
     * from Truffle compilation.
     */
    @TruffleBoundary
    public static void load(final SqueakImageContext image) {
        new SqueakImageReader(image).run();
        System.gc(); // Clean up after image loading
    }

    private void run() {
        SqueakImageContext.initializeBeforeLoadingImage();
        image.setPharo(image.getImagePath().contains("Pharo"));
        final long start = MiscUtils.currentTimeMillis();
        final TruffleFile truffleFile = image.env.getPublicTruffleFile(image.getImagePath());
        if (!truffleFile.isRegularFile()) {
            throw SqueakException.create(MiscUtils.format("Image at '%s' does not exist.", image.getImagePath()));
        }
        try (var channel = FileChannel.open(Path.of(image.getImagePath()), StandardOpenOption.READ)) {
            final MappedByteBuffer buffer = channel.map(FileChannel.MapMode.READ_ONLY, 0, channel.size());
            buffer.order(ByteOrder.LITTLE_ENDIAN);
            readImage(buffer);
            UnsafeUtils.invokeCleaner(buffer);
        } catch (final IOException e) {
            throw SqueakException.create("Failed to read Smalltalk image:", e.getMessage());
        }

        if (chunkMap.size() == 0) {
            LogUtils.IMAGE.warning("Empty chunk map after readImage");
            return;
        }

        initObjects();
        LogUtils.IMAGE.fine(() -> "Image loaded in " + (MiscUtils.currentTimeMillis() - start) + "ms.");
        image.setHiddenRoots((ArrayObject) hiddenRootsChunk.asObject());
        image.getSqueakImage();
    }

    private static void skip(final MappedByteBuffer buffer, final int numBytes) {
        buffer.position(buffer.position() + numBytes);
    }

    private void readImage(final MappedByteBuffer buffer) {
        // Read header
        image.imageFormat = buffer.getInt();
        if (!ArrayUtils.contains(SqueakImageConstants.SUPPORTED_IMAGE_FORMATS, image.imageFormat)) {
            throw SqueakException.create(MiscUtils.format("Image format %s not supported. Please supply a compatible 64bit Spur image (%s).", image.imageFormat,
                            Arrays.toString(SqueakImageConstants.SUPPORTED_IMAGE_FORMATS)));
        }

        // Base header start
        headerSize = buffer.getInt();
        final long dataSize = buffer.getLong();
        baseAddress = buffer.getLong();
        specialObjectsPointer = buffer.getLong();
        // 1 word last used hash
        buffer.getLong();
        final long snapshotScreenSize = buffer.getLong();
        final long headerFlags = buffer.getLong();
        // extraVMMemory
        buffer.getInt();

        // Spur header start
        // numStackPages
        buffer.getShort();
        // cogCodeSize
        buffer.getShort();
        assert buffer.position() == 64 : "Wrong position";
        // edenBytes
        buffer.getInt();
        final short maxExternalSemaphoreTableSize = buffer.getShort();
        // unused, realign to word boundary
        buffer.getShort();
        assert buffer.position() == 72 : "Wrong position";
        final long firstSegmentSize = buffer.getLong();
        // freeOldSpace
        buffer.getLong();

        image.flags.initialize(baseAddress, headerFlags, snapshotScreenSize, maxExternalSemaphoreTableSize);

        skip(buffer, headerSize - buffer.position());
        assert buffer.position() == headerSize;

        // Read body
        long segmentEnd = headerSize + firstSegmentSize;
        long currentAddressSwizzle = baseAddress;
        while (buffer.position() < segmentEnd) {
            while (buffer.position() < segmentEnd - SqueakImageConstants.IMAGE_BRIDGE_SIZE) {
                final SqueakImageChunk chunk = readObject(buffer);
                final long key = chunk.getPosition() + currentAddressSwizzle;
                chunkMap.put(key, chunk);
            }
            final long bridge = buffer.getLong();
            final long nextSegmentSize = buffer.getLong();
            long bridgeSpan = 0;
            final int numSlots = SqueakImageConstants.ObjectHeader.getNumSlots(bridge);
            if (numSlots != 0) {
                bridgeSpan = numSlots;
                if (numSlots == SqueakImageConstants.OVERFLOW_SLOTS) {
                    bridgeSpan = bridge & ~SqueakImageConstants.SLOTS_MASK;
                }
            }
            if (nextSegmentSize == 0) {
                break;
            }
            segmentEnd += nextSegmentSize;
            currentAddressSwizzle += bridgeSpan * SqueakImageConstants.WORD_SIZE;
        }
        assert buffer.position() == headerSize + dataSize;
    }

    private SqueakImageChunk readObject(final MappedByteBuffer buffer) {
        int pos = buffer.position() - headerSize;
        assert pos % SqueakImageConstants.WORD_SIZE == 0 : "every object must be 64-bit aligned: " + pos % SqueakImageConstants.WORD_SIZE;
        long headerWord = buffer.getLong();
        int numSlots = SqueakImageConstants.ObjectHeader.getNumSlots(headerWord);
        if (numSlots == SqueakImageConstants.OVERFLOW_SLOTS) {
            numSlots = (int) (headerWord & ~SqueakImageConstants.SLOTS_MASK);
            assert numSlots >= SqueakImageConstants.OVERFLOW_SLOTS;
            pos = buffer.position() - headerSize;
            headerWord = buffer.getLong();
            assert SqueakImageConstants.ObjectHeader.getNumSlots(headerWord) == SqueakImageConstants.OVERFLOW_SLOTS : "Objects with long header must have 255 in slot count";
        }
        final int size = numSlots;
        assert size >= 0 : "Negative object size";
        final int classIndex = SqueakImageConstants.ObjectHeader.getClassIndex(headerWord);
        final byte[] objectData;
        if (ignoreObjectData(headerWord, classIndex, size)) {
            /* Skip some hidden objects for performance reasons. */
            objectData = null;
            skip(buffer, size * SqueakImageConstants.WORD_SIZE);
        } else {
            final int format = SqueakImageConstants.ObjectHeader.getFormat(headerWord);
            objectData = nextObjectData(buffer, size, format);
        }
        final SqueakImageChunk chunk = new SqueakImageChunk(this, headerWord, pos, objectData);
        if (hiddenRootsChunk == null && isHiddenObject(classIndex)) {
            if (freePageList == null) {
                assert classIndex == SqueakImageConstants.WORD_SIZE_CLASS_INDEX_PUN && size == SqueakImageConstants.NUM_FREE_LISTS;
                freePageList = chunk; /* First hidden object. */
            } else {
                assert classIndex == SqueakImageConstants.ARRAY_CLASS_INDEX_PUN &&
                                size >= SqueakImageConstants.CLASS_TABLE_ROOT_SLOTS + SqueakImageConstants.HIDDEN_ROOT_SLOTS : "hiddenRootsObj has unexpected size: " + size;
                hiddenRootsChunk = chunk; /* Second hidden object. */
            }
        }
        return chunk;
    }

    private static byte[] nextObjectData(final MappedByteBuffer buffer, final int size, final int format) {
        if (size == 0) {
            skip(buffer, SqueakImageConstants.WORD_SIZE); // skip trailing alignment word
            return ArrayUtils.EMPTY_BYTE_ARRAY;
        }
        final int paddedObjectSize = size * SqueakImageConstants.WORD_SIZE;
        final int padding = calculateObjectPadding(format);
        final int objectDataSize = paddedObjectSize - padding;
        final byte[] bytes = new byte[objectDataSize];
        buffer.get(bytes);
        skip(buffer, padding);
        return bytes;
    }

    private static boolean ignoreObjectData(final long headerWord, final int classIndex, final int size) {
        if (isFreeObject(classIndex) || isObjectStack(classIndex, size)) {
            return true;
        }
        if (isHiddenObject(classIndex) && SqueakImageConstants.ObjectHeader.isPinned(headerWord)) {
            /*
             * Don't skip ARRAY_CLASS_INDEX_PUN hidden objects - these include class table pages
             * whose data is needed to traverse the class table during image loading (Pharo compat).
             */
            if (classIndex == SqueakImageConstants.ARRAY_CLASS_INDEX_PUN) {
                return false;
            }
            return true;
        }
        return false;
    }

    protected static boolean isHiddenObject(final int classIndex) {
        return classIndex <= SqueakImageConstants.LAST_CLASS_INDEX_PUN;
    }

    private static boolean isFreeObject(final int classIndex) {
        return classIndex == SqueakImageConstants.FREE_OBJECT_CLASS_INDEX_PUN;
    }

    private static boolean isObjectStack(final int classIndex, final int size) {
        return classIndex == SqueakImageConstants.WORD_SIZE_CLASS_INDEX_PUN && size == SqueakImageConstants.OBJ_STACK_PAGE_SLOTS;
    }

    private SqueakImageChunk specialObjectChunk(final SqueakImageChunk specialObjectsChunk, final int idx) {
        return chunkMap.get(specialObjectsChunk.getWord(idx));
    }

    private boolean isValidSpecialObjectChunk(final SqueakImageChunk specialObjectsChunk, final int idx) {
        final SqueakImageChunk chunk = specialObjectChunk(specialObjectsChunk, idx);
        return chunk != null && !chunk.isNil() && chunk.getWordSize() > 0;
    }

    private void initializeClass(final SqueakImageChunk specialChunk, final int index, final ClassObject targetClass) {
        final SqueakImageChunk chunk = specialObjectChunk(specialChunk, index).getClassChunk();
        chunk.setObject(targetClass);
        targetClass.setSqueakClass(chunk.getSqueakClass());
    }

    private void setPrebuiltObject(final SqueakImageChunk specialObjectsChunk, final int idx, final NativeObject object) {
        final SqueakImageChunk chunk = specialObjectChunk(specialObjectsChunk, idx);
        if (chunk == null || chunk.isNil()) {
            return;
        }
        if (chunk.getObject() != null) {
            return;
        }
        object.initializeFrom(chunk);
        assert 15 < chunk.getFormat() && chunk.getFormat() <= 23 : "non-byte NativeObject in special objects array";
        object.setStorage(chunk.getBytes());
    }

    private void setPrebuiltObject(final SqueakImageChunk specialObjectsChunk, final int idx, final AbstractSqueakObjectWithClassAndHash object) {
        final SqueakImageChunk chunk = specialObjectChunk(specialObjectsChunk, idx);
        if (chunk == null || chunk.isNil()) {
            return;
        }
        if (chunk.getObject() != null) {
            return;
        }
        object.initializeFrom(chunk);
    }

    private void setPrebuiltObject(final SqueakImageChunk specialObjectsChunk, final int idx, final Object object) {
        final SqueakImageChunk chunk = specialObjectChunk(specialObjectsChunk, idx);
        if (chunk == null) {
            return;
        }
        if (chunk.getObject() == null || chunk.getObject() == object) {
            chunk.setObject(object);
        }
    }

    private void initPrebuiltMetaClass() {
        final SqueakImageChunk specialChunk = chunkMap.get(specialObjectsPointer);
        if (specialChunk == null) {
            throw SqueakException.create("specialObjectsArray chunk not found in map! pointer: 0x" + Long.toHexString(specialObjectsPointer) + ", map size: " + chunkMap.size());
        }
        specialChunk.setObject(image.specialObjectsArray);

        // first we find the Metaclass, we need it to correctly instantiate
        // those classes that do not have any instances. Metaclass always
        // has instances, and all instances of Metaclass have their singleton
        // Behavior instance, so these are all correctly initialized already
        final SqueakImageChunk sqArray = specialChunk.getClassChunk();
        final SqueakImageChunk sqArrayClass = sqArray.getClassChunk();
        final SqueakImageChunk sqMetaclass = sqArrayClass.getClassChunk();
        sqMetaclass.setObject(image.metaClass);
        image.metaClass.setSqueakClass(sqMetaclass.getSqueakClass());
    }

    private void initPrebuiltConstant() {
        final SqueakImageChunk specialChunk = chunkMap.get(specialObjectsPointer);
        if (specialChunk == null) {
            LogUtils.IMAGE.warning(() -> "specialObjectsArray chunk not found at 0x" + Long.toHexString(specialObjectsPointer));
            return;
        }

        /*
         * Pin core singletons early to prevent accidental promotion if indices point to these chunks
         * (e.g. index 31 in Pharo 13 points to nil).
         */
        setPrebuiltObject(specialChunk, SPECIAL_OBJECT.NIL_OBJECT, NilObject.SINGLETON);
        setPrebuiltObject(specialChunk, SPECIAL_OBJECT.FALSE_OBJECT, BooleanObject.FALSE);
        setPrebuiltObject(specialChunk, SPECIAL_OBJECT.TRUE_OBJECT, BooleanObject.TRUE);

        // also cache nil, true, and false classes
        initializeClass(specialChunk, SPECIAL_OBJECT.NIL_OBJECT, image.nilClass);
        initializeClass(specialChunk, SPECIAL_OBJECT.FALSE_OBJECT, image.falseClass);
        initializeClass(specialChunk, SPECIAL_OBJECT.TRUE_OBJECT, image.trueClass);

        setPrebuiltObject(specialChunk, SPECIAL_OBJECT.CLASS_BITMAP, image.bitmapClass);
        setPrebuiltObject(specialChunk, SPECIAL_OBJECT.CLASS_SMALL_INTEGER, image.smallIntegerClass);
        setPrebuiltObject(specialChunk, SPECIAL_OBJECT.CLASS_STRING, image.byteStringClass);
        setPrebuiltObject(specialChunk, SPECIAL_OBJECT.CLASS_ARRAY, image.arrayClass);
        setPrebuiltObject(specialChunk, SPECIAL_OBJECT.CLASS_FLOAT, image.floatClass);
        setPrebuiltObject(specialChunk, SPECIAL_OBJECT.CLASS_METHOD_CONTEXT, image.methodContextClass);
        if (isValidSpecialObjectChunk(specialChunk, SPECIAL_OBJECT.CLASS_WIDE_STRING)) {
            setPrebuiltObject(specialChunk, SPECIAL_OBJECT.CLASS_WIDE_STRING, image.initializeWideStringClass());
        }
        setPrebuiltObject(specialChunk, SPECIAL_OBJECT.CLASS_POINT, image.pointClass);
        setPrebuiltObject(specialChunk, SPECIAL_OBJECT.CLASS_LARGE_POSITIVE_INTEGER, image.largePositiveIntegerClass);
        setPrebuiltObject(specialChunk, SPECIAL_OBJECT.CLASS_MESSAGE, image.messageClass);
        if (isValidSpecialObjectChunk(specialChunk, SPECIAL_OBJECT.CLASS_COMPILED_METHOD)) {
            setPrebuiltObject(specialChunk, SPECIAL_OBJECT.CLASS_COMPILED_METHOD, image.compiledMethodClass);
        }
        setPrebuiltObject(specialChunk, SPECIAL_OBJECT.CLASS_SEMAPHORE, image.semaphoreClass);
        setPrebuiltObject(specialChunk, SPECIAL_OBJECT.CLASS_CHARACTER, image.characterClass);

        setPrebuiltObject(specialChunk, SPECIAL_OBJECT.CLASS_BYTE_ARRAY, image.byteArrayClass);
        setPrebuiltObject(specialChunk, SPECIAL_OBJECT.CLASS_PROCESS, image.processClass);
        if (isValidSpecialObjectChunk(specialChunk, SPECIAL_OBJECT.CLASS_DOUBLE_BYTE_ARRAY)) {
            setPrebuiltObject(specialChunk, SPECIAL_OBJECT.CLASS_DOUBLE_BYTE_ARRAY, image.initializeDoubleByteArrayClass());
        }
        if (isValidSpecialObjectChunk(specialChunk, SPECIAL_OBJECT.CLASS_WORD_ARRAY)) {
            setPrebuiltObject(specialChunk, SPECIAL_OBJECT.CLASS_WORD_ARRAY, image.initializeWordArrayClass());
        }
        if (isValidSpecialObjectChunk(specialChunk, SPECIAL_OBJECT.CLASS_DOUBLE_WORD_ARRAY)) {
            setPrebuiltObject(specialChunk, SPECIAL_OBJECT.CLASS_DOUBLE_WORD_ARRAY, image.initializeDoubleWordArrayClass());
        }

        setPrebuiltObject(specialChunk, SPECIAL_OBJECT.CLASS_BLOCK_CLOSURE, image.blockClosureClass);
        if (isValidSpecialObjectChunk(specialChunk, SPECIAL_OBJECT.CLASS_FULL_BLOCK_CLOSURE)) {
            setPrebuiltObject(specialChunk, SPECIAL_OBJECT.CLASS_FULL_BLOCK_CLOSURE, image.initializeFullBlockClosureClass());
        }
        setPrebuiltObject(specialChunk, SPECIAL_OBJECT.CLASS_LARGE_NEGATIVE_INTEGER, image.largeNegativeIntegerClass);
        if (isValidSpecialObjectChunk(specialChunk, SPECIAL_OBJECT.CLASS_EXTERNAL_ADDRESS)) {
            setPrebuiltObject(specialChunk, SPECIAL_OBJECT.CLASS_EXTERNAL_ADDRESS, image.initializeExternalAddressClass());
        }
        if (isValidSpecialObjectChunk(specialChunk, SPECIAL_OBJECT.CLASS_EXTERNAL_STRUCTURE)) {
            setPrebuiltObject(specialChunk, SPECIAL_OBJECT.CLASS_EXTERNAL_STRUCTURE, image.initializeExternalStructureClass());
        }
        if (isValidSpecialObjectChunk(specialChunk, SPECIAL_OBJECT.CLASS_EXTERNAL_DATA)) {
            setPrebuiltObject(specialChunk, SPECIAL_OBJECT.CLASS_EXTERNAL_DATA, image.initializeExternalDataClass());
        }
        if (isValidSpecialObjectChunk(specialChunk, SPECIAL_OBJECT.CLASS_EXTERNAL_FUNCTION)) {
            setPrebuiltObject(specialChunk, SPECIAL_OBJECT.CLASS_EXTERNAL_FUNCTION, image.initializeExternalFunctionClass());
        }
        if (isValidSpecialObjectChunk(specialChunk, SPECIAL_OBJECT.CLASS_EXTERNAL_LIBRARY)) {
            setPrebuiltObject(specialChunk, SPECIAL_OBJECT.CLASS_EXTERNAL_LIBRARY, image.initializeExternalLibraryClass());
        }
        if (isValidSpecialObjectChunk(specialChunk, SPECIAL_OBJECT.CLASS_ALIEN)) {
            setPrebuiltObject(specialChunk, SPECIAL_OBJECT.CLASS_ALIEN, image.initializeAlienClass());
        }
        if (isValidSpecialObjectChunk(specialChunk, SPECIAL_OBJECT.CLASS_UNSAFE_ALIEN)) {
            setPrebuiltObject(specialChunk, SPECIAL_OBJECT.CLASS_UNSAFE_ALIEN, image.initializeUnsafeAlienClass());
        }

        setPrebuiltObject(specialChunk, SPECIAL_OBJECT.SCHEDULER_ASSOCIATION, image.schedulerAssociation);

        // Smalltalk dictionary is deferred until after fillInClassObjects

        setPrebuiltObject(specialChunk, SPECIAL_OBJECT.SELECTOR_DOES_NOT_UNDERSTAND, image.doesNotUnderstand);
        setPrebuiltObject(specialChunk, SPECIAL_OBJECT.SELECTOR_CANNOT_RETURN, image.cannotReturn);
        setPrebuiltObject(specialChunk, SPECIAL_OBJECT.SPECIAL_SELECTORS, image.specialSelectors);
        setPrebuiltObject(specialChunk, SPECIAL_OBJECT.SELECTOR_MUST_BE_BOOLEAN, image.mustBeBooleanSelector);

        setPrebuiltObject(specialChunk, SPECIAL_OBJECT.SELECTOR_CANNOT_INTERPRET, image.cannotInterpretSelector);
        setPrebuiltObject(specialChunk, SPECIAL_OBJECT.SELECTOR_ABOUT_TO_RETURN, image.aboutToReturnSelector);
        setPrebuiltObject(specialChunk, SPECIAL_OBJECT.SELECTOR_RUN_WITHIN, image.runWithInSelector);
        setPrebuiltObject(specialChunk, SPECIAL_OBJECT.PRIM_ERR_TABLE_INDEX, image.primitiveErrorTable);

        image.specialObjectsArray.setSqueakClass(specialChunk.getSqueakClass());
        image.specialObjectsArray.fillin(specialChunk);
        // Selector forcing for Pharo 13 moved to after fillInClassObjects
        final SqueakImageChunk specialSelectorsChunk = specialChunk.getChunk(SPECIAL_OBJECT.SPECIAL_SELECTORS);
        image.specialSelectors.fillin(specialSelectorsChunk);
    }

    private void ensureSpecialSelectors(final ArrayObject selectors) {
        final String[] standardSelectors = {
            "+", "-", "<", ">", "<=", ">=", "=", "~=",
            "*", "/", "\\", "@", "bitShift:", "//", "bitAnd:", "bitOr:",
            "at:", "at:put:", "size", "next", "nextPut:", "atEnd",
            "==", "class", "~~", "value", "value:", "do:",
            "new", "new:", "x", "y"
        };
        final int[] standardArities = {
            1, 1, 1, 1, 1, 1, 1, 1,
            1, 1, 1, 1, 1, 1, 1, 1,
            1, 2, 0, 0, 1, 0,
            1, 0, 1, 0, 1, 1,
            0, 1, 0, 0
        };
        final Object[] storage = selectors.getObjectStorage();
        final ClassObject byteSymbolClass = image.getByteSymbolClass();
        if (byteSymbolClass == null) {
             // If we don't have the class yet, we can't reliably inject them here.
             // They will likely be filled in by the image anyway, or discovered later.
             return;
        }
        for (int i = 0; i < standardSelectors.length; i++) {
            if (storage[i * 2] == NilObject.SINGLETON || storage[i * 2] == null) {
                final NativeObject selector = NativeObject.newNativeBytes(byteSymbolClass, MiscUtils.stringToBytes(standardSelectors[i]));
                // Set a hash so that method cache logic doesn't crash
                selector.setSqueakHash(standardSelectors[i].hashCode() & 0x3fffff);
                storage[i * 2] = selector;
                storage[i * 2 + 1] = (long) standardArities[i];
            }
        }
    }

    private void forceSelector(final NativeObject selector, final String name) {
        selector.setSqueakClass(image.byteSymbolClass);
        selector.setStorage(MiscUtils.stringToBytes(name));
        if (selector.getSqueakHash() == -1) {
            selector.setSqueakHash(name.hashCode() & 0x3fffff);
        }
    }

    private void initSmalltalk() {
        final SqueakImageChunk specialChunkReal = chunkMap.get(specialObjectsPointer);
        setPrebuiltObject(specialChunkReal, SPECIAL_OBJECT.SMALLTALK_DICTIONARY, image.smalltalk);
    }

    private void initObjects() {
        if (hiddenRootsChunk != null && hiddenRootsChunk.getWordSize() > 0) {
            final long specialObjectsArrayOop = hiddenRootsChunk.getWord(0);
            final SqueakImageChunk specialObjectsArrayChunk = chunkMap.get(specialObjectsArrayOop);
            if (specialObjectsArrayChunk != null && specialObjectsArrayChunk.getWordSize() > 0) {
                nilPointer = specialObjectsArrayChunk.getWord(0);
            }
        }
        if (nilPointer == 0) {
            nilPointer = baseAddress; // Fallback
        }
        initPrebuiltMetaClass();
        initPrebuiltConstant();
        fillInClassObjects();
        if (image.isPharo()) {
            forceSelector(image.cannotReturn, "cannotReturn:");
            forceSelector(image.mustBeBooleanSelector, "mustBeBoolean");
            forceSelector(image.doesNotUnderstand, "doesNotUnderstand:");
            ensureSpecialSelectors(image.specialSelectors);
            if (image.specialObjectsArray.getObject(SPECIAL_OBJECT.SELECTOR_CANNOT_RETURN) == NilObject.SINGLETON) {
                image.specialObjectsArray.setObject(SPECIAL_OBJECT.SELECTOR_CANNOT_RETURN, image.cannotReturn);
            }
            if (image.specialObjectsArray.getObject(SPECIAL_OBJECT.SELECTOR_MUST_BE_BOOLEAN) == NilObject.SINGLETON) {
                image.specialObjectsArray.setObject(SPECIAL_OBJECT.SELECTOR_MUST_BE_BOOLEAN, image.mustBeBooleanSelector);
            }
            if (image.specialObjectsArray.getObject(SPECIAL_OBJECT.SELECTOR_DOES_NOT_UNDERSTAND) == NilObject.SINGLETON) {
                image.specialObjectsArray.setObject(SPECIAL_OBJECT.SELECTOR_DOES_NOT_UNDERSTAND, image.doesNotUnderstand);
            }
        }
        initSmalltalk();
        fillInObjects();
        fillInClassesFromCompactClassList();
    }

    /**
     * Fill in classes and ensure instances of Behavior and its subclasses use {@link ClassObject}.
     * Uses a multi-pass approach for robustness with both Squeak and Pharo images.
     */
    private void fillInClassObjects() {
        /* Find all metaclasses and instantiate their singleton instances as class objects. */
        int highestKnownClassIndex = -1;
        if (hiddenRootsChunk.getBytes() == null) {
            throw SqueakException.create("hiddenRootsChunk has null bytes. header=" + hiddenRootsChunk.getHeader());
        }
        for (int pass = 0; pass < 3; pass++) {
            for (int p = 0; p < SqueakImageConstants.CLASS_TABLE_ROOT_SLOTS; p++) {
                final SqueakImageChunk classTablePage = chunkMap.get(hiddenRootsChunk.getWord(p));
                if (classTablePage == null || classTablePage.isNil()) {
                    break; /* End of classTable reached (pages are consecutive). */
                }
                if (classTablePage.getBytes() == null || classTablePage.getBytes().length == 0) {
                    continue; /* Skip zero-length pages (Pharo class table placeholders). */
                }
                for (int i = 0; i < SqueakImageConstants.CLASS_TABLE_PAGE_SIZE; i++) {
                    final long potentialClassPtr = classTablePage.getWord(i);
                    assert potentialClassPtr != 0;
                    final SqueakImageChunk classChunk = chunkMap.get(potentialClassPtr);
                    if (classChunk == null || classChunk.getFormat() != 1) {
                        continue;
                    }
                    final ClassObject classObject = classChunk.asClassObject();
                    if (classObject == null) {
                        continue;
                    }
                    /* Derive classIndex from current position in class table. */
                    highestKnownClassIndex = p << SqueakImageConstants.CLASS_TABLE_MAJOR_INDEX_SHIFT | i;
                    if (classChunk.getWordSize() >= METACLASS.INST_SIZE) {
                        final long thisClassPtr = classChunk.getWord(METACLASS.THIS_CLASS);
                        final SqueakImageChunk classInstance = chunkMap.get(thisClassPtr);
                        if (classInstance != null && classInstance.getFormat() == 1) {
                            classObject.setInstancesAreClasses();
                            classInstance.asClassObject();
                        }
                    }
                }
            }
        }
        assert highestKnownClassIndex > 0 : "Failed to find highestKnownClassIndex";
        image.classTableIndex = highestKnownClassIndex;

        /* Fill in metaClass. */
        final SqueakImageChunk specialObjectsChunk = chunkMap.get(specialObjectsPointer);
        final SqueakImageChunk sqArray = specialObjectsChunk.getClassChunk();
        final SqueakImageChunk sqArrayClass = sqArray.getClassChunk();
        final SqueakImageChunk sqMetaclass = sqArrayClass.getClassChunk();
        image.metaClass.fillin(sqMetaclass);

        /*
         * Walk over all classes again, fill them in, and ensure instances of all subclasses of
         * ClassDescriptions are {@link ClassObject}s.
         */
        final HashSet<ClassObject> inst = new HashSet<>();
        final ClassObject classDescriptionClass = image.metaClass.getSuperclassOrNull();
        classDescriptionClass.setInstancesAreClasses();
        inst.add(classDescriptionClass);

        for (int p = 0; p < SqueakImageConstants.CLASS_TABLE_ROOT_SLOTS; p++) {
            final SqueakImageChunk classTablePage = chunkMap.get(hiddenRootsChunk.getWord(p));
            if (classTablePage == null || classTablePage.isNil()) {
                break; /* End of classTable reached (pages are consecutive). */
            }
            if (classTablePage.getBytes() == null || classTablePage.getBytes().length == 0) {
                continue; /* Skip zero-length pages. */
            }
            for (int i = 0; i < SqueakImageConstants.CLASS_TABLE_PAGE_SIZE; i++) {
                final long potentialClassPtr = classTablePage.getWord(i);
                if (potentialClassPtr == 0) continue; // Pharo 13 might have zero entries in pages
                final SqueakImageChunk classChunk = chunkMap.get(potentialClassPtr);
                if (classChunk == null || classChunk.getFormat() != 1) {
                    continue;
                }
                final ClassObject classObject = classChunk.asClassObject();
                if (classObject == null) {
                    continue;
                }
                if (classChunk.getWordSize() >= METACLASS.INST_SIZE) {
                    final long thisClassPtr = classChunk.getWord(METACLASS.THIS_CLASS);
                    final SqueakImageChunk classInstance = chunkMap.get(thisClassPtr);
                    if (classInstance != null && classInstance.getFormat() == 1) {
                        final ClassObject instanceClassObject = classInstance.asClassObject();
                        classObject.fillin(classChunk);
                        if (instanceClassObject != null) {
                            instanceClassObject.fillin(classInstance);
                            /* Discover Pharo-specific closure and core classes by name. */
                            final String name = instanceClassObject.getClassName();
                            if ("FullBlockClosure".equals(name)) {
                                if (image.getFullBlockClosureClass() == null) {
                                    image.setFullBlockClosureClass(instanceClassObject);
                                }
                            } else if ("BlockClosure".equals(name)) {
                                if (image.blockClosureClass == null || image.blockClosureClass.isDummy()) {
                                    image.blockClosureClass = instanceClassObject;
                                }
                            } else if ("CompiledMethod".equals(name)) {
                                image.compiledMethodClass = instanceClassObject;
                            } else if ("Process".equals(name)) {
                                if (image.processClass == null || image.processClass.isDummy()) {
                                    image.processClass = instanceClassObject;
                                }
                            } else if ("Context".equals(name) || "MethodContext".equals(name)) {
                                if (image.methodContextClass == null || image.methodContextClass.isDummy()) {
                                    image.methodContextClass = instanceClassObject;
                                }
                            } else if ("ByteSymbol".equals(name)) {
                                if (image.byteSymbolClass == null || image.byteSymbolClass.isDummy()) {
                                    image.byteSymbolClass = instanceClassObject;
                                }
                            }
                            classObject.setOtherPointer(METACLASS.THIS_CLASS, instanceClassObject);
                            if (inst.contains(instanceClassObject.getSuperclassOrNull())) {
                                inst.add(instanceClassObject);
                                instanceClassObject.setInstancesAreClasses();
                            }
                        }
                    }
                } else {
                    classObject.fillin(classChunk);
                    if (inst.contains(classObject.getSuperclassOrNull())) {
                        inst.add(classObject);
                        classObject.setInstancesAreClasses();
                    }
                }
            }
        }
        assert image.metaClass.instancesAreClasses();
        if (image.byteSymbolClass == null || image.byteSymbolClass.isDummy()) {
            final Object[] metaClassPointers = image.metaClass.getOtherPointers();
            if (metaClassPointers.length > CLASS.NAME && metaClassPointers[CLASS.NAME] instanceof final NativeObject nameSymbol) {
                image.setByteSymbolClass(nameSymbol.getSqueakClass());
            }
        }

        /* Finally, ensure instances of Behavior are {@link ClassObject}s. */
        final ClassObject behaviorClass = classDescriptionClass.getSuperclassOrNull();
        behaviorClass.setInstancesAreClasses();

        /* Ensure any class-like chunk is upgraded to ClassObject before objects are filled in. */
        forceUpgradeClassLikeChunks(behaviorClass);
    }

    private boolean isSubclassOf(final ClassObject klass, final ClassObject superclass) {
        ClassObject current = klass;
        while (current != null) {
            if (current == superclass) {
                return true;
            }
            current = current.getSuperclassOrNull();
        }
        return false;
    }

    private void forceUpgradeClassLikeChunks(final ClassObject behaviorClass) {
        for (final SqueakImageChunk chunk : chunkMap.getChunks()) {
            if (chunk == null || chunk.getObject() != null) {
                continue;
            }
            final byte[] bytes = chunk.getBytes();
            if (bytes == null || bytes.length == 0) {
                continue;
            }
            if (chunk.getFormat() != 1) {
                continue;
            }
            final ClassObject chunkClass = chunk.getSqueakClass();
            if (chunkClass == null) {
                continue;
            }
            if (isSubclassOf(chunkClass, behaviorClass)) {
                chunk.asClassObject();
            }
        }
    }

    private void fillInObjects() {
        for (final SqueakImageChunk chunk : chunkMap.getChunks()) {
            if (chunk == null) {
                continue;
            }
            final Object chunkObject = chunk.asObject();
            if (chunkObject instanceof final AbstractSqueakObjectWithHash obj) {
                assert !(obj instanceof final AbstractSqueakObjectWithClassAndHash o) || !o.needsSqueakClass() : "object is missing class";
                assert obj.getSqueakHashInt() == chunk.getHash() : "object is missing hash";
                obj.fillin(chunk);
            }
        }

    }

    private void fillInClassesFromCompactClassList() {
        image.smallFloatClass = lookupClassInCompactClassList(SqueakImageConstants.SMALL_FLOAT_TAG);
    }

    private ClassObject lookupClassInCompactClassList(final int compactIndex) {
        final int majorIndex = SqueakImageConstants.majorClassIndexOf(compactIndex);
        final int minorIndex = SqueakImageConstants.minorClassIndexOf(compactIndex);
        final ArrayObject classTablePage = (ArrayObject) chunkMap.get(hiddenRootsChunk.getWord(majorIndex)).asObject();
        final Object result = ArrayObjectReadNode.executeUncached(classTablePage, minorIndex);
        return result instanceof final ClassObject c ? c : null;
    }

    /* Calculate odd bits (see Behavior>>instSpec). */
    public static int calculateObjectPadding(final int format) {
        if (16 <= format && format <= 31) {
            return format & 7; /* 8-bit indexable and compiled methods: three odd bits */
        } else if (format == 11) {
            return Integer.BYTES; /* 32-bit words with 1 word padding. */
        } else if (12 <= format && format <= 15) {
            // 16-bit words with 2, 4, or 6 bytes padding
            return (format & 3) * Short.BYTES; /* 16-bit indexable: two odd bits */
        } else if (10 <= format) {
            return format & 1; /* 1 word padding */
        } else {
            return 0;
        }
    }

    public static class AddressToChunkMap {
        private static final int INITIAL_CAPACITY = 1_000_000;
        private static final float THRESHOLD_PERCENTAGE = 0.75f;
        private static final float RESIZE_FACTOR = 1.5f;
        private static final int COLLISION_OFFSET = 31;

        private int capacity = INITIAL_CAPACITY;
        private int threshold = (int) (capacity * THRESHOLD_PERCENTAGE);
        private long[] addresses = new long[capacity];
        private SqueakImageChunk[] chunks = new SqueakImageChunk[capacity];
        private int size;

        public int size() {
            return size;
        }

        public void put(final long address, final SqueakImageChunk chunk) {
            if (size > threshold) {
                resize();
            }
            int slot = (int) (address % capacity);
            if (slot < 0) {
                slot += capacity;
            }
            while (true) {
                if (chunks[slot] == null) {
                    addresses[slot] = address;
                    chunks[slot] = chunk;
                    size++;
                    return;
                }
                slot = (slot + COLLISION_OFFSET) % capacity;
                if (slot < 0) {
                    slot += capacity;
                }
            }
        }

        public SqueakImageChunk get(final long address) {
            int slot = (int) (address % capacity);
            if (slot < 0) {
                slot += capacity;
            }
            while (true) {
                if (addresses[slot] == address) {
                    return chunks[slot];
                }
                if (chunks[slot] == null) {
                    return null;
                }
                slot = (slot + COLLISION_OFFSET) % capacity;
                if (slot < 0) {
                    slot += capacity;
                }
            }
        }

        private SqueakImageChunk[] getChunks() {
            return chunks;
        }

        private void resize() {
            capacity = (int) (capacity * RESIZE_FACTOR);
            threshold = (int) (capacity * THRESHOLD_PERCENTAGE);
            LogUtils.READER.log(Level.FINE, "Resizing chunk map to {0}", capacity);
            final long[] oldAddresses = addresses;
            final SqueakImageChunk[] oldChunks = chunks;
            addresses = new long[capacity];
            chunks = new SqueakImageChunk[capacity];
            size = 0;
            for (int i = 0; i < oldChunks.length; i++) {
                final SqueakImageChunk chunk = oldChunks[i];
                if (chunk != null) {
                    put(oldAddresses[i], chunk);
                }
            }
        }
    }
}
