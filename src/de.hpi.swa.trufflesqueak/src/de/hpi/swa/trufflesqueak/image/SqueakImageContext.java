/*
 * Copyright (c) 2017-2026 Software Architecture Group, Hasso Plattner Institute
 * Copyright (c) 2021-2026 Oracle and/or its affiliates
 *
 * Licensed under the MIT License.
 */
package de.hpi.swa.trufflesqueak.image;

import java.lang.ref.ReferenceQueue;
import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.Map;
import java.util.logging.Level;

import org.graalvm.collections.UnmodifiableEconomicMap;

import com.oracle.truffle.api.Assumption;
import com.oracle.truffle.api.CompilerAsserts;
import com.oracle.truffle.api.CompilerDirectives;
import com.oracle.truffle.api.CompilerDirectives.CompilationFinal;
import com.oracle.truffle.api.CompilerDirectives.TruffleBoundary;
import com.oracle.truffle.api.Truffle;
import com.oracle.truffle.api.TruffleFile;
import com.oracle.truffle.api.TruffleLanguage.ContextReference;
import com.oracle.truffle.api.TruffleLanguage.ParsingRequest;
import com.oracle.truffle.api.dsl.Bind.DefaultExpression;
import com.oracle.truffle.api.nodes.IndirectCallNode;
import com.oracle.truffle.api.nodes.RootNode;
import com.oracle.truffle.api.frame.FrameDescriptor;
import com.oracle.truffle.api.frame.MaterializedFrame;
import com.oracle.truffle.api.frame.VirtualFrame;
import com.oracle.truffle.api.interop.InteropLibrary;
import com.oracle.truffle.api.library.Message;
import com.oracle.truffle.api.nodes.ExplodeLoop;
import com.oracle.truffle.api.nodes.Node;
import com.oracle.truffle.api.profiles.InlinedConditionProfile;
import com.oracle.truffle.api.source.Source;
import com.oracle.truffle.api.utilities.CyclicAssumption;

import de.hpi.swa.trufflesqueak.SqueakImage;
import de.hpi.swa.trufflesqueak.SqueakLanguage;
import de.hpi.swa.trufflesqueak.SqueakOptions.SqueakContextOptions;
import de.hpi.swa.trufflesqueak.exceptions.PrimitiveFailed;
import de.hpi.swa.trufflesqueak.exceptions.ProcessSwitch;
import de.hpi.swa.trufflesqueak.exceptions.Returns;
import de.hpi.swa.trufflesqueak.exceptions.SqueakExceptions.SqueakException;
import de.hpi.swa.trufflesqueak.io.SqueakDisplay;
import de.hpi.swa.trufflesqueak.model.AbstractPointersObject;
import de.hpi.swa.trufflesqueak.model.AbstractSqueakObject;
import de.hpi.swa.trufflesqueak.model.AbstractSqueakObjectWithClassAndHash;
import de.hpi.swa.trufflesqueak.model.AbstractSqueakObjectWithHash;
import de.hpi.swa.trufflesqueak.model.ArrayObject;
import de.hpi.swa.trufflesqueak.model.BlockClosureObject;
import de.hpi.swa.trufflesqueak.model.BooleanObject;
import de.hpi.swa.trufflesqueak.model.ClassObject;
import de.hpi.swa.trufflesqueak.model.CompiledCodeObject;
import de.hpi.swa.trufflesqueak.model.CompiledCodeObject.CompiledCodeHeaderUtils;
import de.hpi.swa.trufflesqueak.model.ContextObject;
import de.hpi.swa.trufflesqueak.model.EphemeronObject;
import de.hpi.swa.trufflesqueak.model.NativeObject;
import de.hpi.swa.trufflesqueak.model.NilObject;
import de.hpi.swa.trufflesqueak.model.PointersObject;
import de.hpi.swa.trufflesqueak.model.layout.ObjectLayouts;
import de.hpi.swa.trufflesqueak.model.layout.ObjectLayouts.ASSOCIATION;
import de.hpi.swa.trufflesqueak.model.layout.ObjectLayouts.FRACTION;
import de.hpi.swa.trufflesqueak.model.layout.ObjectLayouts.MESSAGE;
import de.hpi.swa.trufflesqueak.model.layout.ObjectLayouts.POINT;
import de.hpi.swa.trufflesqueak.model.layout.ObjectLayouts.PROCESS;
import de.hpi.swa.trufflesqueak.model.layout.ObjectLayouts.PROCESS_SCHEDULER;
import de.hpi.swa.trufflesqueak.model.layout.ObjectLayouts.SPECIAL_OBJECT;
import de.hpi.swa.trufflesqueak.model.layout.SlotLocation;
import de.hpi.swa.trufflesqueak.nodes.DoItRootNode;
import de.hpi.swa.trufflesqueak.nodes.ExecuteTopLevelContextNode;
import de.hpi.swa.trufflesqueak.nodes.SqueakGuards;
import de.hpi.swa.trufflesqueak.nodes.accessing.AbstractPointersObjectNodes.AbstractPointersObjectReadNode;
import de.hpi.swa.trufflesqueak.nodes.accessing.AbstractPointersObjectNodes.AbstractPointersObjectWriteNode;
import de.hpi.swa.trufflesqueak.nodes.accessing.SqueakObjectClassNode;
import de.hpi.swa.trufflesqueak.nodes.interrupts.CheckForInterruptsState;
import de.hpi.swa.trufflesqueak.nodes.plugins.B2D;
import de.hpi.swa.trufflesqueak.nodes.plugins.BitBlt;
import de.hpi.swa.trufflesqueak.nodes.plugins.JPEGReader;
import de.hpi.swa.trufflesqueak.nodes.plugins.Zip;
import de.hpi.swa.trufflesqueak.nodes.plugins.ffi.InterpreterProxy;
import de.hpi.swa.trufflesqueak.nodes.process.SignalSemaphoreNodeGen;
import de.hpi.swa.trufflesqueak.shared.SqueakImageLocator;
import de.hpi.swa.trufflesqueak.tools.SqueakMessageInterceptor;
import de.hpi.swa.trufflesqueak.util.ArrayUtils;
import de.hpi.swa.trufflesqueak.util.FrameAccess;
import de.hpi.swa.trufflesqueak.util.LogUtils;
import de.hpi.swa.trufflesqueak.util.MethodCacheEntry;
import de.hpi.swa.trufflesqueak.util.MiscUtils;
import de.hpi.swa.trufflesqueak.util.ObjectGraphUtils;

@DefaultExpression("get($node)")
public final class SqueakImageContext {
    private static final ContextReference<SqueakImageContext> REFERENCE = ContextReference.create(SqueakLanguage.class);

    /* Special objects */
    public final ClassObject falseClass = new ClassObject(this);
    public final ClassObject trueClass = new ClassObject(this);
    public final PointersObject schedulerAssociation = new PointersObject();
    public final ClassObject bitmapClass = new ClassObject(this);
    public final ClassObject smallIntegerClass = new ClassObject(this);
    public final ClassObject byteStringClass = new ClassObject(this);
    public final ClassObject arrayClass = new ClassObject(this);
    public final PointersObject smalltalk = new PointersObject();
    public final ClassObject floatClass = new ClassObject(this);
    @CompilationFinal public ClassObject methodContextClass = new ClassObject(this);
    @CompilationFinal private ClassObject wideStringClass;
    @CompilationFinal public ClassObject pointClass = new ClassObject(this);
    @CompilationFinal public ClassObject largePositiveIntegerClass = new ClassObject(this);
    @CompilationFinal public ClassObject messageClass = new ClassObject(this);
    public ClassObject compiledMethodClass = new ClassObject(this);
    @CompilationFinal public ClassObject semaphoreClass = new ClassObject(this);
    @CompilationFinal public ClassObject characterClass = new ClassObject(this);
    public final NativeObject doesNotUnderstand = new NativeObject();
    public final NativeObject cannotReturn = new NativeObject();
    public final ArrayObject specialSelectors = new ArrayObject();
    public final NativeObject mustBeBooleanSelector = new NativeObject();
    @CompilationFinal public ClassObject byteArrayClass = new ClassObject(this);
    @CompilationFinal public ClassObject processClass = new ClassObject(this);
    @CompilationFinal private ClassObject doubleByteArrayClass;
    @CompilationFinal private ClassObject wordArrayClass;
    @CompilationFinal private ClassObject doubleWordArrayClass;
    public final NativeObject cannotInterpretSelector = new NativeObject(); // TODO: use selector
    @CompilationFinal public ClassObject blockClosureClass = new ClassObject(this);
    @CompilationFinal private ClassObject fullBlockClosureClass;
    @CompilationFinal public ClassObject largeNegativeIntegerClass = new ClassObject(this);
    @CompilationFinal private ClassObject externalAddressClass;
    @CompilationFinal private ClassObject externalStructureClass;
    @CompilationFinal private ClassObject externalDataClass;
    @CompilationFinal private ClassObject externalFunctionClass;
    @CompilationFinal private ClassObject externalLibraryClass;
    public final NativeObject aboutToReturnSelector = new NativeObject();
    public final NativeObject runWithInSelector = new NativeObject();
    public final ArrayObject primitiveErrorTable = new ArrayObject();
    @CompilationFinal private ClassObject alienClass;
    @CompilationFinal private ClassObject unsafeAlienClass;

    @CompilationFinal public ClassObject smallFloatClass;
    @CompilationFinal public ClassObject byteSymbolClass;
    @CompilationFinal private ClassObject foreignObjectClass;
    private final CyclicAssumption foreignObjectClassStable = new CyclicAssumption("ForeignObjectClassStable assumption");
    @CompilationFinal private ClassObject linkedListClass;

    public final ArrayObject specialObjectsArray = new ArrayObject();
    public final ClassObject metaClass = new ClassObject(this);
    public final ClassObject nilClass = new ClassObject(this);

    public final CompiledCodeObject dummyMethod = new CompiledCodeObject(
                    /* Object>>#yourself */
                    new byte[]{(byte) 112, (byte) 124, 0, 0, 0, 0, 0},
                    CompiledCodeHeaderUtils.makeHeaderWord(true, 0, 0, 0, true, true),
                    ArrayUtils.EMPTY_ARRAY, compiledMethodClass == null ? new ClassObject(this) : compiledMethodClass);
    public final VirtualFrame externalSenderFrame = Truffle.getRuntime().createVirtualFrame(FrameAccess.newWith(NilObject.SINGLETON, null, NilObject.SINGLETON), dummyMethod.getFrameDescriptor());

    /* Method Cache */
    private static final int METHOD_CACHE_SIZE = 2 << 12;
    private static final int METHOD_CACHE_MASK = METHOD_CACHE_SIZE - 1;
    private static final int METHOD_CACHE_REPROBES = 4;
    private int methodCacheRandomish;
    @CompilationFinal(dimensions = 1) private final MethodCacheEntry[] methodCache = new MethodCacheEntry[METHOD_CACHE_SIZE];

    /* Interpreter state */
    private int primFailCode = -1;

    /* System Information */
    public final SqueakImageFlags flags = new SqueakImageFlags();
    private String imagePath;
    @CompilationFinal public int imageFormat;
    private final TruffleFile homePath;
    @CompilationFinal(dimensions = 1) private byte[] resourcesDirectoryBytes;
    @CompilationFinal(dimensions = 1) private byte[] resourcesPathBytes;
    private final boolean isHeadless;
    public final SqueakContextOptions options;
    private final SqueakSystemAttributes systemAttributes = new SqueakSystemAttributes(this);

    /* System */
    public NativeObject clipboardTextHeadless = asByteString("");
    private boolean currentMarkingFlag;
    public final ObjectGraphUtils objectGraphUtils;
    private ArrayObject hiddenRoots;
    private int numClassTablePages = SqueakImageConstants.CLASS_TABLE_ROOT_SLOTS;
    // first page of classTable is special
    public int classTableIndex = SqueakImageConstants.CLASS_TABLE_PAGE_SIZE;
    @CompilationFinal private SqueakDisplay display;
    public final CheckForInterruptsState interrupt;
    public final long startUpMillis = System.currentTimeMillis();
    public final ReferenceQueue<AbstractSqueakObject> weakPointersQueue = new ReferenceQueue<>();

    /* Truffle */
    @CompilationFinal public SqueakLanguage.Env env;
    private final SqueakLanguage language;
    private final HashMap<Message, NativeObject> interopMessageToSelectorMap = new HashMap<>();

    @CompilationFinal private SqueakImage squeakImage;

    /* Low space handling */
    private static final int LOW_SPACE_NUM_SKIPPED_SENDS = 4;
    private int lowSpaceSkippedSendsCount;

    /* Ephemeron support */
    public boolean containsEphemerons;
    public final ArrayDeque<EphemeronObject> ephemeronsQueue = new ArrayDeque<>();

    /* Context stack depth */
    @CompilationFinal private final int maxContextStackDepth;
    private int currentContextStackDepth;

    @CompilationFinal private ClassObject fractionClass;
    private PointersObject parserSharedInstance;
    private AbstractSqueakObject requestorSharedInstanceOrNil;
    @CompilationFinal private PointersObject scheduler;
    @CompilationFinal private Object smalltalkScope;
    @CompilationFinal private boolean isPharo;

    /* Plugins */
    @CompilationFinal private InterpreterProxy interpreterProxy;
    public final Map<String, Object> loadedLibraries = new HashMap<>();
    public final B2D b2d = new B2D(this);
    public final BitBlt bitblt = new BitBlt(this);
    public String[] dropPluginFileList = ArrayUtils.EMPTY_STRINGS_ARRAY;
    public final JPEGReader jpegReader = new JPEGReader();
    public final Zip zip = new Zip();

    public SqueakImageContext(final SqueakLanguage squeakLanguage, final SqueakLanguage.Env environment) {
        language = squeakLanguage;
        options = SqueakContextOptions.create(environment.getOptions());
        isHeadless = options.isHeadless();
        maxContextStackDepth = options.maxContextStackDepth();
        patch(environment);
        interrupt = new CheckForInterruptsState(this);
        objectGraphUtils = new ObjectGraphUtils(this);
        SqueakMessageInterceptor.enableIfRequested(environment);
        final String truffleLanguageHome = language.getTruffleLanguageHome();
        if (truffleLanguageHome != null) {
            homePath = env.getInternalTruffleFile(truffleLanguageHome);
        } else { /* Fall back to image directory if language home is not set. */
            homePath = env.getInternalTruffleFile(options.imagePath()).getParent();
        }
        assert homePath != null && homePath.exists() : "Home directory does not exist: " + homePath;
        initializeMethodCache();
    }

    public static SqueakImageContext get(final Node node) {
        return REFERENCE.get(node);
    }

    public static SqueakImageContext getSlow() {
        CompilerAsserts.neverPartOfCompilation();
        return get(null);
    }

    public boolean isPharo() {
        return isPharo;
    }

    public void setPharo(final boolean value) {
        isPharo = value;
    }

    public void ensureLoaded() {
        if (squeakImage == null) {
            // Load image.
            SqueakImageReader.load(this);
            if (options.disableStartup()) {
                LogUtils.IMAGE.info("Skipping startup routine...");
                return;
            }

            if (isPharo()) {
                /* For Pharo, do not clear the active context. The snapshot context resumes
                 * naturally and handles SessionManager startup and CommandLineHandler. */
            } else {
                final String prepareHeadlessImageScript = """
                                "Remove active context."
                                Processor activeProcess instVarNamed: #suspendedContext put: nil.

                                "Avoid interactive windows and instead exit on errors."
                                %s ifFalse: [ ToolSet default: CommandLineToolSet ].

                                "Start up image (see SmalltalkImage>>#snapshot:andQuit:withExitCode:embedded:)."
                                Smalltalk
                                    clearExternalObjects;
                                    processStartUpList: true;
                                    setPlatformPreferences;
                                    recordStartupStamp.

                                "Set author information."
                                Utilities
                                    authorName: 'TruffleSqueak';
                                    setAuthorInitials: 'TS'.
                                """.formatted(Boolean.toString(options.isTesting()));
                try {
                    evaluate(prepareHeadlessImageScript);
                } catch (final Exception e) {
                    LogUtils.IMAGE.log(Level.WARNING, "startUpList failed", e);
                } finally {
                    interrupt.clear();
                }
            }
        }
    }

    public SqueakImage getSqueakImage() {
        if (squeakImage == null) {
            CompilerDirectives.transferToInterpreterAndInvalidate();
            squeakImage = new SqueakImage(this);
        }
        return squeakImage;
    }

    @TruffleBoundary
    public Object evaluate(final String sourceCode) {
        return getDoItContextNode(sourceCode).getCallTarget().call();
    }

    @TruffleBoundary
    public Object evaluateUninterruptably(final String sourceCode) {
        final boolean wasActive = interrupt.deactivate();
        try {
            final ExecuteTopLevelContextNode rootNode = getDoItContextNode(sourceCode);
            while (true) {
                try {
                    return rootNode.getCallTarget().call();
                } catch (final ProcessSwitch ps) {
                    interrupt.clear();
                } catch (final de.hpi.swa.trufflesqueak.exceptions.Returns.AbstractStandardSendReturn r) {
                    throw de.hpi.swa.trufflesqueak.exceptions.SqueakExceptions.SqueakException.create("Unexpected return exception during uninterruptable evaluation", r);
                }
            }
        } finally {
            interrupt.reactivate(wasActive);
        }
    }


    public boolean patch(final SqueakLanguage.Env newEnv) {
        CompilerDirectives.transferToInterpreterAndInvalidate();
        env = newEnv;
        return true;
    }

    @TruffleBoundary
    public ExecuteTopLevelContextNode getActiveContextNode() {
        final PointersObject activeProcess = getActiveProcessSlow();
        final ContextObject activeContext = (ContextObject) activeProcess.instVarAt0Slow(PROCESS.SUSPENDED_CONTEXT);
        LogUtils.IMAGE.info(() -> "Active context: " + activeContext + " method: " + activeContext.getCodeObject() +
                        " sender: " + activeContext.getSender());
        activeProcess.instVarAtPut0Slow(PROCESS.SUSPENDED_CONTEXT, NilObject.SINGLETON);
        return ExecuteTopLevelContextNode.create(this, getLanguage(), activeContext, true);
    }

    @TruffleBoundary
    public RootNode parseRequest(final ParsingRequest request) {
        if (isPharo()) {
            return getPharoDoItRootNode(request);
        }
        return getDoItContextNode(request);
    }

    /**
     * For Pharo images, compile the source as a DoIt method using OpalCompiler, execute it
     * directly, and convert the result to a Java String for display by the launcher.
     */
    @TruffleBoundary
    private RootNode getPharoDoItRootNode(final ParsingRequest request) {
        final String source = request.getSource().getCharacters().toString();
        final Object compilerClass = lookup("OpalCompiler");
        if (!(compilerClass instanceof final ClassObject opalCompiler)) {
            throw CompilerDirectives.shouldNotReachHere("OpalCompiler not found in Pharo image");
        }

        final SqueakImageContext image = this;
        return new RootNode(getLanguage(), new FrameDescriptor()) {
            @Override
            public Object execute(final VirtualFrame frame) {
                return pharoCompileAndExecute();
            }

            @TruffleBoundary
            private Object pharoCompileAndExecute() {
                /*
                 * Compile with error handler that captures error + Smalltalk stack, then
                 * returns the error object. We detect it on the Java side and throw a
                 * SqueakExceptionWrapper for proper Truffle error reporting.
                 */
                final AbstractSqueakObjectWithClassAndHash compiler = (AbstractSqueakObjectWithClassAndHash) opalCompiler.send(image, "new");
                compiler.send(image, "source:", image.asByteString(
                                "DoIt ^ [ " + source + " ] on: Error do: [ :e | e freeze. e ]"));
                compiler.send(image, "class:", image.nilClass);
                compiler.send(image, "requestor:", NilObject.SINGLETON);
                final Object compiled = compiler.send(image, "compile");

                if (!(compiled instanceof final CompiledCodeObject doItMethod)) {
                    return "Compilation error (got " + compiled.getClass().getSimpleName() + " instead of CompiledMethod)";
                }

                internLiterals(doItMethod);

                /* Execute the DoIt method with nil as receiver. */
                Object result;
                try {
                    result = IndirectCallNode.getUncached().call(
                                    doItMethod.getCallTarget(),
                                    FrameAccess.newWith(NilObject.SINGLETON, null, NilObject.SINGLETON, new Object[0]));
                } catch (final ProcessSwitch e) {
                    return "Execution error: unexpected process switch";
                } catch (final Returns.AbstractStandardSendReturn r) {
                    return "Execution error: " + r.getReturnValue();
                }

                return resultToString(result);
            }

            private String resultToString(final Object result) {
                if (result instanceof Long || result instanceof Double || result instanceof Boolean) {
                    return result.toString();
                } else if (result == NilObject.SINGLETON) {
                    return "nil";
                } else if (result instanceof final NativeObject no) {
                    if (no.isByteType() && image.isByteStringClass(no.getSqueakClass())) {
                        return "'" + no.asStringUnsafe() + "'";
                    }
                    if (no.isIntType() && image.isWideStringClass(no.getSqueakClass())) {
                        return "'" + no.asStringFromWideString() + "'";
                    }
                }
                if (result instanceof final PointersObject po && isSmalltalkError(po)) {
                    throwSmalltalkError(po);
                }
                if (result instanceof final AbstractSqueakObjectWithClassAndHash obj) {
                    /* Try printString for complex objects, include class name. */
                    try {
                        final Object ps = obj.send(image, "printString");
                        if (ps instanceof final NativeObject no && no.isByteType()) {
                            return no.asStringUnsafe() + " - " + obj.getSqueakClass().getClassName() + " @" + Integer.toHexString(obj.hashCode());
                        }
                    } catch (final Exception e) {
                        /* Fall through to default. */
                    }
                    return obj.getSqueakClass().getClassName() + " @" + Integer.toHexString(obj.hashCode());
                }
                return String.valueOf(result);
            }

            private static boolean isSmalltalkError(final PointersObject obj) {
                ClassObject cls = obj.getSqueakClass();
                while (cls != null) {
                    if ("Error".equals(cls.getClassName())) {
                        return true;
                    }
                    cls = cls.getSuperclassOrNull();
                }
                return false;
            }

            private void throwSmalltalkError(final PointersObject errorObj) {
                /* Get error description. */
                String description = errorObj.getSqueakClass().getClassName();
                try {
                    final Object desc = errorObj.send(image, "description");
                    if (desc instanceof final NativeObject no && no.isByteType()) {
                        description = no.asStringUnsafe();
                    }
                } catch (final Exception e) {
                    /* Ignore. */
                }

                /* Walk signalerContext to build Smalltalk stack trace. */
                final StringBuilder sb = new StringBuilder(description);
                try {
                    Object ctx = errorObj.send(image, "signalerContext");
                    int depth = 0;
                    while (ctx instanceof final AbstractSqueakObjectWithHash ctxObj && depth < 20) {
                        try {
                            final Object ps = ctxObj.send(image, "printString");
                            if (ps instanceof final NativeObject no && no.isByteType()) {
                                sb.append("\n\tat <smalltalk> ").append(no.asStringUnsafe()).append("(Unknown)");
                            }
                        } catch (final Exception e) {
                            break;
                        }
                        try {
                            ctx = ctxObj.send(image, "sender");
                        } catch (final Exception e) {
                            break;
                        }
                        depth++;
                    }
                } catch (final Exception e) {
                    /* No stack trace available. */
                }

                throw SqueakException.create(sb.toString());
            }
        };
    }

    @TruffleBoundary
    public DoItRootNode getDoItContextNode(final ParsingRequest request) {
        final Source source = request.getSource();
        final String blockBody;
        if (isFileInFormat(source)) {
            blockBody = "(FileStream readOnlyFileNamed: '" + source.getPath() + "') fileIn. true";
        } else {
            if (request.getArgumentNames().isEmpty()) {
                blockBody = source.getCharacters().toString();
            } else {
                blockBody = ":" + String.join(" :", request.getArgumentNames()) + " | " + source.getCharacters();
            }
        }
        final String sourceCode;
        if (isPharo()) {
            /* Pharo does not have the Interop class, so use a simpler wrapper. */
            sourceCode = "[ " + blockBody + " ]";
        } else {
            sourceCode = "[[ " + blockBody + " ] on: Error do: [ :e | Interop throwException: e ]]";
        }
        return DoItRootNode.create(this, language, (BlockClosureObject) evaluateUninterruptably(sourceCode));
    }

    private static boolean isFileInFormat(final Source source) {
        final CharSequence firstLine = source.getCharacters(1);
        /* First line must end with an `!`. */
        return firstLine.charAt(firstLine.length() - 1) == '!';
    }

    @TruffleBoundary
    private ExecuteTopLevelContextNode getDoItContextNode(final String source) {
        /*
         * Pharo images do not have the Parser class. Fall back to OpalCompiler-based evaluation.
         */
        if (parserSharedInstance == null) {
            final Object parserClass = lookup("Parser");
            if (parserClass instanceof final ClassObject parserClassObject) {
                parserSharedInstance = (PointersObject) parserClassObject.send(this, "new");
                final Object polyglotRequestorClassOrNil = lookup("PolyglotRequestor");
                if (polyglotRequestorClassOrNil instanceof final ClassObject polyglotRequestorClass) {
                    requestorSharedInstanceOrNil = (AbstractSqueakObject) polyglotRequestorClass.send(this, "default");
                } else {
                    requestorSharedInstanceOrNil = NilObject.SINGLETON;
                }
            } else {
                /* Parser not available (Pharo) — use OpalCompiler fallback. */
                return getCompilerDoItContextNode(source);
            }
        }

        final NativeObject smalltalkSource = asByteString(source);
        if (requestorSharedInstanceOrNil != NilObject.SINGLETON) {
            ((AbstractSqueakObjectWithClassAndHash) requestorSharedInstanceOrNil).send(this, "currentSource:", smalltalkSource);
        }
        final PointersObject methodNode;
        try {
            methodNode = (PointersObject) parserSharedInstance.send(this, "parse:class:noPattern:notifying:ifFail:",
                            smalltalkSource, nilClass, BooleanObject.TRUE, requestorSharedInstanceOrNil, new BlockClosureObject(true, 0));
        } catch (final ProcessSwitch e) {
            /*
             * A ProcessSwitch exception is thrown in case of a syntax error to open the
             * corresponding window. Fail with an appropriate exception here. This way, it is clear
             * why code execution failed (e.g. when requested through the Polyglot API).
             */
            throw CompilerDirectives.shouldNotReachHere("Unexpected process switch detected during parse request", e);
        }
        final CompiledCodeObject doItMethod = (CompiledCodeObject) methodNode.send(this, "generate");

        final ContextObject doItContext = new ContextObject(doItMethod.getSqueakContextSize());
        doItContext.setReceiver(NilObject.SINGLETON);
        doItContext.setCodeObject(doItMethod);
        doItContext.setInstructionPointer(0);
        doItContext.setStackPointer(doItMethod.getNumTemps());
        doItContext.setSenderUnsafe(NilObject.SINGLETON);
        return ExecuteTopLevelContextNode.create(this, getLanguage(), doItContext, false);
    }

    @TruffleBoundary
    private ExecuteTopLevelContextNode getCompilerDoItContextNode(final String source) {
        /*
         * Use OpalCompiler for Pharo images. Wrap the source in a DoIt method pattern so that
         * OpalCompiler parses it as a method definition (avoiding the need for isScripting:).
         * The method selector must be 'DoIt' so that ExecuteTopLevelContextNode can recognize
         * it as a top-level return target.
         */
        final Object compilerClass = lookup("OpalCompiler");
        if (!(compilerClass instanceof final ClassObject opalCompiler)) {
            throw CompilerDirectives.shouldNotReachHere("Neither Parser nor OpalCompiler found in image");
        }
        final String doItSource = "DoIt ^ " + source;
        final AbstractSqueakObjectWithClassAndHash compiler = (AbstractSqueakObjectWithClassAndHash) opalCompiler.send(this, "new");
        compiler.send(this, "source:", asByteString(doItSource));
        compiler.send(this, "class:", nilClass);
        compiler.send(this, "requestor:", NilObject.SINGLETON);
        final Object compileResult;
        try {
            compileResult = compiler.send(this, "compile");
        } catch (final ProcessSwitch e) {
            /*
             * A ProcessSwitch exception is thrown in case of a syntax error to open the
             * corresponding window. Fail with an appropriate exception here.
             */
            throw CompilerDirectives.shouldNotReachHere("Unexpected process switch detected during OpalCompiler compile request", e);
        }
        if (!(compileResult instanceof final CompiledCodeObject doItMethod)) {
            throw CompilerDirectives.shouldNotReachHere("OpalCompiler compile did not return a CompiledMethod, got: " + compileResult);
        }
        /* Fix up literal selectors to use the image's interned symbols. */
        internLiterals(doItMethod);

        final ContextObject doItContext = new ContextObject(doItMethod.getSqueakContextSize());
        doItContext.setReceiver(NilObject.SINGLETON);
        doItContext.setCodeObject(doItMethod);
        doItContext.setInstructionPointer(0);
        doItContext.setStackPointer(doItMethod.getNumTemps());
        doItContext.setSenderUnsafe(NilObject.SINGLETON);
        return ExecuteTopLevelContextNode.create(this, getLanguage(), doItContext, false);
    }

    /*
     * CONTEXT STACK DEPTH MANAGEMENT
     */

    public boolean enteringContextExceedsDepth() {
        return ++currentContextStackDepth > maxContextStackDepth;
    }

    public void exitingContext() {
        --currentContextStackDepth;
    }

    public void resetContextStackDepth() {
        currentContextStackDepth = 0;
    }

    /*
     * ACCESSING
     */

    public SqueakLanguage getLanguage() {
        return language;
    }

    public boolean toggleCurrentMarkingFlag() {
        return currentMarkingFlag = !currentMarkingFlag;
    }

    /* SpurMemoryManager>>#setHiddenRootsObj: */
    public void setHiddenRoots(final ArrayObject theHiddenRoots) {
        assert hiddenRoots == null && (theHiddenRoots.isObjectType() || isTesting());
        hiddenRoots = theHiddenRoots;
        // This assertion is checked with the initial value of numClassTablePages.
        assert validClassTableRootPages();

        if (!hiddenRoots.isObjectType()) {
            assert isTesting(); // Ignore dummy images for testing
            return;
        }

        // Set numClassTablePages to the number of used pages.
        // Set classTableIndex to the first unused slot in the class table after the first page.
        classTableIndex = 0;
        for (int i = 1; i < SqueakImageConstants.CLASS_TABLE_ROOT_SLOTS; i++) {
            if (hiddenRoots.getObject(i) instanceof final ArrayObject page) {
                // Search for the first unused slot if we have not yet found one.
                if (classTableIndex == 0) {
                    for (int j = 0; j < SqueakImageConstants.CLASS_TABLE_PAGE_SIZE; j++) {
                        final Object entry = page.getObject(j);
                        if (entry == NilObject.SINGLETON) {
                            classTableIndex = SqueakImageConstants.classTableIndexFor(i, j);
                            break;
                        }
                    }
                }
            } else {
                // Found nil page -- end of table.
                assert hiddenRoots.getObject(i) == NilObject.SINGLETON;
                if (classTableIndex == 0) {
                    // SpurMemoryManager>>#setHiddenRootsObj: sets this to first entry of previous
                    // page and then asserts that that entry must be nil, which is will always fail.
                    // Here, we set it to the first entry of the first unallocated page.
                    classTableIndex = SqueakImageConstants.classTableIndexFor(i, 0);
                }
                numClassTablePages = i;
                assert lookupClassIndex(classTableIndex) == NilObject.SINGLETON;
                return;
            }
        }

        // We get here when all pages of the class table are allocated.
        if (classTableIndex == 0) {
            // No unused slots; set it to the start of the second page.
            // Assertion below will always fail in this case.
            classTableIndex = SqueakImageConstants.classTableIndexFor(1, 0);
        }
        assert lookupClassIndex(classTableIndex) == NilObject.SINGLETON;
    }

    /* SpurMemoryManager>>#validClassTableRootPages */
    public boolean validClassTableRootPages() {
        if (!hiddenRoots.isObjectType()) {
            assert isTesting(); // Ignore dummy images for testing
            return true;
        }

        final Object[] hiddenRootsObjects = hiddenRoots.getObjectStorage();
        if (hiddenRootsObjects.length != SqueakImageConstants.CLASS_TABLE_ROOT_SLOTS + SqueakImageConstants.HIDDEN_ROOT_SLOTS) {
            LogUtils.DEBUG.warning(
                            "hiddenRootsObjects size out of bounds: " + hiddenRootsObjects.length + " != " + (SqueakImageConstants.CLASS_TABLE_ROOT_SLOTS + SqueakImageConstants.HIDDEN_ROOT_SLOTS));
            return false;
        }
        // "is it in range?"
        if (!(numClassTablePages > 1 && numClassTablePages <= SqueakImageConstants.CLASS_TABLE_ROOT_SLOTS)) {
            LogUtils.DEBUG.warning("numClassTablePages out of bounds: " + numClassTablePages + " not within 2 to " + SqueakImageConstants.CLASS_TABLE_ROOT_SLOTS);
            return false;
        }
        // "are all pages the right size?"
        for (int i = 0; i < numClassTablePages; i++) {
            final Object classPageOrNil = hiddenRootsObjects[i];
            if (classPageOrNil instanceof final ArrayObject classPage) {
                final int numSlots = classPage.isEmptyType() ? classPage.getEmptyLength() : classPage.getObjectLength();
                if (numSlots != SqueakImageConstants.CLASS_TABLE_PAGE_SIZE) {
                    LogUtils.DEBUG.warning("numSlots wrong size: " + numSlots + " != " + SqueakImageConstants.CLASS_TABLE_PAGE_SIZE);
                    return false;
                }
            } else if (classPageOrNil != NilObject.SINGLETON) {
                // We are expecting either an Array or nil as page entries.
                LogUtils.DEBUG.warning("internal classPageOrNil not nil: " + classPageOrNil);
                return false;
            }
        }
        // are all entries beyond numClassTablePages nil?
        for (int i = numClassTablePages; i < SqueakImageConstants.CLASS_TABLE_ROOT_SLOTS; i++) {
            final Object classPageOrNil = hiddenRootsObjects[i];
            if (classPageOrNil != NilObject.SINGLETON) {
                LogUtils.DEBUG.warning("trailing classPageOrNil not nil: " + classPageOrNil);
                return false;
            }
        }
        return true;
    }

    public ArrayObject getHiddenRoots() {
        return hiddenRoots;
    }

    /* SpurMemoryManager>>#enterIntoClassTable: */
    @TruffleBoundary
    public void enterIntoClassTable(final ClassObject clazz) {
        assert clazz.assertNotForwarded();
        int majorIndex = SqueakImageConstants.majorClassIndexOf(classTableIndex);
        final int initialMajorIndex = majorIndex;
        assert initialMajorIndex > 0 : "classTableIndex should never index the first page; it's reserved for known classes";
        int minorIndex = SqueakImageConstants.minorClassIndexOf(classTableIndex);
        while (true) {
            // Allocate new page if necessary.
            if (hiddenRoots.getObject(majorIndex) == NilObject.SINGLETON) {
                hiddenRoots.setObject(majorIndex, newClassTablePage());
                ++numClassTablePages;
                minorIndex = 0;
            }
            final ArrayObject page = (ArrayObject) hiddenRoots.getObject(majorIndex);
            for (int i = minorIndex; i < SqueakImageConstants.CLASS_TABLE_PAGE_SIZE; i++) {
                final Object entry = page.getObject(i);
                if (entry == NilObject.SINGLETON) {
                    classTableIndex = SqueakImageConstants.classTableIndexFor(majorIndex, i);
                    assert classTableIndex >= 1 << SqueakImageConstants.CLASS_TABLE_MAJOR_INDEX_SHIFT : "classTableIndex must never index the first page, which is reserved for classes known to the VM";
                    page.setObject(i, clazz);
                    clazz.setSqueakHash(classTableIndex);
                    assert lookupClassIndex(classTableIndex) == clazz;
                    return;
                }
            }
            // OSVM wraps majorIndex incorrectly and will allocate pages beyond the number allowed.
            if (++majorIndex >= SqueakImageConstants.CLASS_TABLE_ROOT_SLOTS) {
                majorIndex = 1;
            }
            // OSVM is missing the following line and will miss free slots on subsequent pages.
            minorIndex = 0;
            assert majorIndex != initialMajorIndex : "wrapped; table full";
        }
    }

    private ArrayObject newClassTablePage() {
        return asArrayOfObjects(ArrayUtils.withAll(SqueakImageConstants.CLASS_TABLE_PAGE_SIZE, NilObject.SINGLETON));
    }

    private Object lookupClassIndex(final int classIndex) {
        final long majorIndex = SqueakImageConstants.majorClassIndexOf(classIndex);
        final Object classTablePageOrNil = hiddenRoots.getObject(majorIndex);
        if (classTablePageOrNil instanceof final ArrayObject classTablePage) {
            final long minorIndex = SqueakImageConstants.minorClassIndexOf(classIndex);
            return classTablePage.getObject(minorIndex);
        } else {
            assert classTablePageOrNil == NilObject.SINGLETON;
            return NilObject.SINGLETON;
        }
    }

    /* SpurMemoryManager>>#purgeDuplicateClassTableEntriesFor: */
    public void purgeDuplicateAndUnreachableClassTableEntriesFor(final ClassObject clazz, final UnmodifiableEconomicMap<Object, Object> becomeMap) {
        final int expectedIndex = clazz != null ? clazz.getSqueakHashInt() : -1;
        // Must search all pages, but classTableIndex cannot be in page zero.
        for (int majorIndex = 0; majorIndex < numClassTablePages; majorIndex++) {
            // Guaranteed to be non-nil.
            final ArrayObject page = (ArrayObject) hiddenRoots.getObject(majorIndex);
            if (page.isObjectType()) {
                for (int minorIndex = 0; minorIndex < SqueakImageConstants.CLASS_TABLE_PAGE_SIZE; minorIndex++) {
                    Object entry = page.getObject(minorIndex);
                    if (entry instanceof final ClassObject classObject && !classObject.isNotForwarded()) {
                        entry = classObject.getForwardingPointer();
                        page.setObject(minorIndex, entry);
                    }
                    final int currentClassTableIndex = SqueakImageConstants.classTableIndexFor(majorIndex, minorIndex);
                    final boolean isDuplicate = entry == clazz && currentClassTableIndex != expectedIndex && currentClassTableIndex > SqueakImageConstants.LAST_CLASS_INDEX_PUN;
                    if (isDuplicate || isUnreachable(entry)) {
                        page.setObject(minorIndex, NilObject.SINGLETON);
                        if (currentClassTableIndex < classTableIndex) {
                            // Guaranteed not in page 0 since classes there can't be deleted.
                            classTableIndex = currentClassTableIndex;
                        }
                    } else if (entry instanceof final ClassObject classObject && !becomeMap.isEmpty()) {
                        classObject.pointersBecomeOneWay(becomeMap);
                    }
                }
            } else {
                assert page.isEmptyType() && page.getEmptyLength() == SqueakImageConstants.CLASS_TABLE_PAGE_SIZE;
            }
        }
        assert classTableIndex >= SqueakImageConstants.CLASS_TABLE_PAGE_SIZE : "classTableIndex must never index the first page, which is reserved for classes known to the VM";
    }

    private boolean isUnreachable(final Object object) {
        if (object instanceof final ClassObject classObject) {
            /*
             * Class is unreachable if it was not yet marked with the current marking flag by the
             * last object graph traversal.
             */
            return classObject.tryToMarkWith(currentMarkingFlag);
        } else {
            assert object == NilObject.SINGLETON;
            return false;
        }
    }

    private void flushCachesForSelectorInClassTable(final NativeObject selector) {
        for (final Object classTablePageOrNil : hiddenRoots.getObjectStorage()) {
            if (classTablePageOrNil instanceof final ArrayObject page) {
                if (page.isObjectType()) {
                    final Object[] entries = page.getObjectStorage();
                    for (int i = 0; i < SqueakImageConstants.CLASS_TABLE_PAGE_SIZE; i++) {
                        final Object entry = entries[i];
                        if (entry instanceof final ClassObject classObject) {
                            if (!classObject.isNotForwarded()) {
                                entries[i] = classObject.getForwardingPointer();
                            }
                            ((ClassObject) entries[i]).flushCachesForSelector(selector);
                        } else {
                            assert entry == NilObject.SINGLETON;
                        }
                    }
                } else {
                    assert page.isEmptyType() && page.getEmptyLength() == SqueakImageConstants.CLASS_TABLE_PAGE_SIZE;
                }
            } else {
                assert classTablePageOrNil == NilObject.SINGLETON;
                break;
            }
        }
    }

    public void flushCachesForSelector(final NativeObject selector) {
        flushCachesForSelectorInClassTable(selector);
        flushMethodCacheForSelector(selector);
    }

    public TruffleFile getHomePath() {
        return homePath;
    }

    public TruffleFile getLibraryPath() {
        final TruffleFile libraryPath = getHomePath().resolve("lib");
        assert libraryPath.exists() : "Library path not found";
        return libraryPath;
    }

    public NativeObject getResourcesDirectory() {
        ensureResourcesDirectoryAndPathInitialized();
        return NativeObject.newNativeBytes(byteStringClass, resourcesDirectoryBytes.clone());
    }

    public NativeObject getResourcesPath() {
        ensureResourcesDirectoryAndPathInitialized();
        return NativeObject.newNativeBytes(byteStringClass, resourcesPathBytes.clone());
    }

    private void ensureResourcesDirectoryAndPathInitialized() {
        if (resourcesDirectoryBytes == null) {
            CompilerDirectives.transferToInterpreterAndInvalidate();
            final String languageHome = getLanguage().getTruffleLanguageHome();
            final TruffleFile path;
            if (languageHome != null) {
                path = getHomePath().resolve("resources");
            } else { /* Fallback to image directory. */
                path = env.getInternalTruffleFile(getImagePath()).getParent();
                if (path == null) {
                    throw SqueakException.create("`parent` should not be `null`.");
                }
            }
            resourcesDirectoryBytes = MiscUtils.stringToBytes(path.getAbsoluteFile().getPath());
            resourcesPathBytes = MiscUtils.stringToBytes(path.getAbsoluteFile().getPath() + env.getFileNameSeparator());
        }
    }

    public ClassObject getByteSymbolClass() {
        return byteSymbolClass;
    }

    public void setByteSymbolClass(final ClassObject classObject) {
        CompilerDirectives.transferToInterpreterAndInvalidate();
        assert byteSymbolClass == null;
        byteSymbolClass = classObject;
    }

    public static void initializeBeforeLoadingImage() {
        SlotLocation.initialize();
    }

    public ClassObject getWideStringClass() {
        assert wideStringClass != null;
        return wideStringClass;
    }

    public ClassObject initializeWideStringClass() {
        assert wideStringClass == null;
        return wideStringClass = new ClassObject(this);
    }

    public ClassObject getDoubleByteArrayClass() {
        assert doubleByteArrayClass != null;
        return doubleByteArrayClass;
    }

    public ClassObject initializeDoubleByteArrayClass() {
        assert doubleByteArrayClass == null;
        return doubleByteArrayClass = new ClassObject(this);
    }

    public ClassObject getWordArrayClass() {
        assert wordArrayClass != null;
        return wordArrayClass;
    }

    public ClassObject initializeWordArrayClass() {
        assert wordArrayClass == null;
        return wordArrayClass = new ClassObject(this);
    }

    public ClassObject getDoubleWordArrayClass() {
        assert doubleWordArrayClass != null;
        return doubleWordArrayClass;
    }

    public ClassObject initializeDoubleWordArrayClass() {
        assert doubleWordArrayClass == null;
        return doubleWordArrayClass = new ClassObject(this);
    }

    public ClassObject getFullBlockClosureClass() {
        return fullBlockClosureClass; /* may be null during image loading */
    }

    public void setFullBlockClosureClass(final ClassObject classObject) {
        CompilerDirectives.transferToInterpreterAndInvalidate();
        fullBlockClosureClass = classObject;
    }

    public ClassObject initializeFullBlockClosureClass() {
        assert fullBlockClosureClass == null;
        return fullBlockClosureClass = new ClassObject(this);
    }

    public AbstractSqueakObject getExternalAddressClass() {
        return NilObject.nullToNil(externalAddressClass);
    }

    public ClassObject initializeExternalAddressClass() {
        assert externalAddressClass == null;
        return externalAddressClass = new ClassObject(this);
    }

    public AbstractSqueakObject getExternalStructureClass() {
        return NilObject.nullToNil(externalStructureClass);
    }

    public ClassObject initializeExternalStructureClass() {
        assert externalStructureClass == null;
        return externalStructureClass = new ClassObject(this);
    }

    public AbstractSqueakObject getExternalDataClass() {
        return NilObject.nullToNil(externalDataClass);
    }

    public ClassObject initializeExternalDataClass() {
        assert externalDataClass == null;
        return externalDataClass = new ClassObject(this);
    }

    public ClassObject getExternalFunctionClassOrNull() {
        return externalFunctionClass;
    }

    public AbstractSqueakObject getExternalFunctionClass() {
        return NilObject.nullToNil(getExternalFunctionClassOrNull());
    }

    public ClassObject initializeExternalFunctionClass() {
        assert externalFunctionClass == null;
        return externalFunctionClass = new ClassObject(this);
    }

    public AbstractSqueakObject getExternalLibraryClass() {
        return NilObject.nullToNil(externalLibraryClass);
    }

    public ClassObject initializeExternalLibraryClass() {
        assert externalLibraryClass == null;
        return externalLibraryClass = new ClassObject(this);
    }

    public AbstractSqueakObject getAlienClass() {
        return NilObject.nullToNil(alienClass);
    }

    public ClassObject initializeAlienClass() {
        assert alienClass == null;
        return alienClass = new ClassObject(this);
    }

    public AbstractSqueakObject getUnsafeAlienClass() {
        return NilObject.nullToNil(unsafeAlienClass);
    }

    public ClassObject initializeUnsafeAlienClass() {
        assert unsafeAlienClass == null;
        return unsafeAlienClass = new ClassObject(this);
    }

    public ClassObject getForeignObjectClass() {
        if (foreignObjectClass == null) {
            CompilerDirectives.transferToInterpreterAndInvalidate();
            return nilClass;
        }
        return foreignObjectClass;
    }

    public Assumption getForeignObjectClassStableAssumption() {
        return foreignObjectClassStable.getAssumption();
    }

    public boolean setForeignObjectClass(final ClassObject classObject) {
        foreignObjectClassStable.invalidate("New foreign object class");
        foreignObjectClass = classObject;
        return true;
    }

    public ClassObject getLinkedListClass() {
        if (linkedListClass == null) {
            CompilerDirectives.transferToInterpreterAndInvalidate();
            final Object lists = getScheduler().instVarAt0Slow(PROCESS_SCHEDULER.PROCESS_LISTS);
            linkedListClass = SqueakObjectClassNode.executeUncached(((ArrayObject) lists).getObject(0));
        }
        return linkedListClass;
    }

    public boolean supportsNFI() {
        CompilerAsserts.neverPartOfCompilation();
        return env.getInternalLanguages().containsKey("nfi");
    }

    public InterpreterProxy getInterpreterProxy(final MaterializedFrame frame, final int numReceiverAndArguments) {
        if (interpreterProxy == null) {
            CompilerDirectives.transferToInterpreterAndInvalidate();
            interpreterProxy = new InterpreterProxy(this);
        }
        return interpreterProxy.instanceFor(frame, numReceiverAndArguments);
    }

    public PointersObject getScheduler() {
        if (scheduler == null) {
            CompilerDirectives.transferToInterpreterAndInvalidate();
            scheduler = (PointersObject) schedulerAssociation.instVarAt0Slow(ASSOCIATION.VALUE);
        }
        return scheduler;
    }

    public PointersObject getActiveProcessSlow() {
        return AbstractPointersObjectReadNode.getUncached().executePointers(getScheduler(), PROCESS_SCHEDULER.ACTIVE_PROCESS);
    }

    public Object getSpecialObject(final int index) {
        if (!specialObjectsArray.isObjectType()) {
            return NilObject.SINGLETON;
        }
        return specialObjectsArray.getObjectStorage()[index];
    }

    public void setSpecialObject(final int index, final Object value) {
        specialObjectsArray.getObjectStorage()[index] = value;
    }

    private ArrayObject getSpecialSelectors() {
        final Object selectors = getSpecialObject(SPECIAL_OBJECT.SPECIAL_SELECTORS);
        return selectors instanceof ArrayObject ? (ArrayObject) selectors : specialObjectsArray;
    }

    public NativeObject getSpecialSelector(final int index) {
        final ArrayObject selectors = getSpecialSelectors();
        if (!selectors.isObjectType()) {
            return null;
        }
        return (NativeObject) selectors.getObjectStorage()[index * 2];
    }

    public int getSpecialSelectorNumArgs(final int index) {
        final ArrayObject selectors = getSpecialSelectors();
        if (!selectors.isObjectType()) {
            return 0;
        }
        return MiscUtils.toIntExact((long) selectors.getObjectStorage()[index * 2 + 1]);
    }

    public void setSemaphore(final int index, final AbstractSqueakObject semaphore) {
        assert semaphore == NilObject.SINGLETON || isSemaphoreClass(((AbstractSqueakObjectWithClassAndHash) semaphore).getSqueakClass());
        setSpecialObject(index, semaphore);
    }

    /**
     * Ensure the active process is saved and try to signal low space semaphore (see
     * #setSignalLowSpaceFlagAndSaveProcess). The JVM has just thrown a {@link StackOverflowError},
     * so thread stack space is limited. To avoid hitting the limit again, free up some space by
     * unwinding a couple of sends before actually signaling the low space semaphore.
     */
    public StackOverflowError tryToSignalLowSpace(final VirtualFrame frame, final StackOverflowError stackOverflowError) {
        CompilerAsserts.neverPartOfCompilation();
        final Object lastSavedProcess = getSpecialObject(SPECIAL_OBJECT.PROCESS_SIGNALING_LOW_SPACE);
        if (lastSavedProcess == NilObject.SINGLETON) {
            setSpecialObject(SPECIAL_OBJECT.PROCESS_SIGNALING_LOW_SPACE, getActiveProcessSlow());
        }
        if (lowSpaceSkippedSendsCount < LOW_SPACE_NUM_SKIPPED_SENDS) {
            lowSpaceSkippedSendsCount++;
            throw stackOverflowError; // continue further up the sender chain
        } else {
            final Object lowSpaceSemaphoreOrNil = getSpecialObject(SPECIAL_OBJECT.THE_LOW_SPACE_SEMAPHORE);
            if (SignalSemaphoreNodeGen.executeUncached(frame, this, lowSpaceSemaphoreOrNil)) {
                // success! reset counter and continue in new process
                lowSpaceSkippedSendsCount = 0;
                throw ProcessSwitch.SINGLETON;
            }
            throw CompilerDirectives.shouldNotReachHere("Failed to signal low space semaphore.", stackOverflowError);
        }
    }

    public SqueakDisplay getDisplay() {
        return display;
    }

    public String getImagePath() {
        if (imagePath == null) {
            CompilerDirectives.transferToInterpreterAndInvalidate();
            setImagePath(SqueakImageLocator.findImage(options.imagePath()));
        }
        return imagePath;
    }

    public void setImagePath(final String path) {
        imagePath = path;
    }

    public String[] getImageArguments() {
        if (options.imageArguments().length > 0) {
            return options.imageArguments();
        } else {
            return env.getApplicationArguments();
        }
    }

    public AbstractSqueakObject getSystemAttribute(final int index) {
        return systemAttributes.getSystemAttribute(index);
    }

    public boolean interruptHandlerDisabled() {
        return options.disableInterruptHandler();
    }

    public void attachDisplayIfNecessary() {
        if (!isHeadless) {
            CompilerDirectives.transferToInterpreterAndInvalidate();
            display = SqueakDisplay.create(this);
        }
    }

    public boolean isTesting() {
        return options.isTesting();
    }

    public void finalizeContext() {
        if (options.printResourceSummary()) {
            MiscUtils.printResourceSummary();
        }
    }

    public int getPrimFailCode() {
        assert primFailCode >= 0;
        final int result = primFailCode;
        primFailCode = 0;
        return result;
    }

    public void setPrimFailCode(final PrimitiveFailed primitiveFailed) {
        primFailCode = primitiveFailed.getPrimFailCode();
    }

    @TruffleBoundary
    public Object getScope() {
        ensureLoaded();
        if (smalltalkScope == null) {
            CompilerDirectives.transferToInterpreterAndInvalidate();
            smalltalkScope = smalltalk.send(this, "asInteropScope");
        }
        return smalltalkScope;
    }

    /*
     * METHOD CACHE
     */

    private void initializeMethodCache() {
        for (int i = 0; i < METHOD_CACHE_SIZE; i++) {
            methodCache[i] = new MethodCacheEntry();
        }
    }

    /*
     * Probe the cache, and return the matching entry if found. Otherwise, return one that can be
     * used (selector and class set) with method == null. Initial probe is class xor selector,
     * reprobe delta is selector. We do not try to optimize probe time -- all are equally 'fast'
     * compared to lookup. Instead, we randomize the reprobe so two or three very active conflicting
     * entries will not keep dislodging each other.
     */
    @ExplodeLoop
    public MethodCacheEntry findMethodCacheEntry(final ClassObject classObject, final NativeObject selector) {
        methodCacheRandomish = methodCacheRandomish + 1 & 3;
        final int selectorHash = System.identityHashCode(selector);
        int firstProbe = (System.identityHashCode(classObject) ^ selectorHash) & METHOD_CACHE_MASK;
        final int stride = (selectorHash << 1) | 1;

        int probe = firstProbe;
        for (int i = 0; i < METHOD_CACHE_REPROBES; i++) {
            final MethodCacheEntry entry = methodCache[probe];
            if (entry.getClassObject() == classObject && entry.getSelector() == selector) {
                return entry;
            }
            if (i == methodCacheRandomish) {
                firstProbe = probe;
            }
            probe = probe + stride & METHOD_CACHE_MASK;
        }
        return methodCache[firstProbe].reuseFor(classObject, selector);
    }

    public Object lookup(final ClassObject receiverClass, final NativeObject selector) {
        final MethodCacheEntry cachedEntry = findMethodCacheEntry(receiverClass, selector);
        if (cachedEntry.getResult() == null) {
            cachedEntry.setResult(receiverClass.lookupInMethodDictSlow(selector));
        }
        return cachedEntry.getResult();
    }

    /* Clear all cache entries (prim 89). */
    public void flushMethodCache() {
        for (int i = 0; i < METHOD_CACHE_SIZE; i++) {
            methodCache[i].freeAndRelease();
        }
    }

    /* Clear cache entries for selector (prim 119). */
    private void flushMethodCacheForSelector(final NativeObject selector) {
        for (int i = 0; i < METHOD_CACHE_SIZE; i++) {
            if (methodCache[i].getSelector() == selector) {
                methodCache[i].freeAndRelease();
            }
        }
    }

    /* Clear cache entries for method (prim 116). */
    public void flushMethodCacheForMethod(final CompiledCodeObject method) {
        for (int i = 0; i < METHOD_CACHE_SIZE; i++) {
            if (methodCache[i].getResult() == method) {
                methodCache[i].freeAndRelease();
            }
        }
    }

    public void flushMethodCacheAfterBecome() {
        /* TODO: Could be selective by checking class, selector, and method against mutations. */
        flushMethodCache();
    }

    /*
     * CLASS CHECKS
     */

    public boolean isBitmapClass(final ClassObject object) {
        return object == bitmapClass;
    }

    public boolean isBlockClosureClass(final ClassObject object) {
        return object == blockClosureClass;
    }

    public boolean isByteString(final NativeObject object) {
        return isByteStringClass(object.getSqueakClass());
    }

    public boolean isByteStringClass(final ClassObject object) {
        return object == byteStringClass;
    }

    public boolean isByteSymbol(final NativeObject object) {
        return isByteSymbolClass(object.getSqueakClass());
    }

    public boolean isByteSymbolClass(final ClassObject object) {
        return object == getByteSymbolClass();
    }

    public boolean isFloatClass(final ClassObject object) {
        return object == floatClass;
    }

    public boolean isFullBlockClosureClass(final ClassObject object) {
        return object == fullBlockClosureClass; /* may be null */
    }

    public boolean isLargeIntegerClass(final ClassObject object) {
        return object == largePositiveIntegerClass || object == largeNegativeIntegerClass;
    }

    public boolean isLargeInteger(final NativeObject object) {
        return isLargeIntegerClass(object.getSqueakClass());
    }

    public boolean isLargePositiveInteger(final NativeObject object) {
        return object.getSqueakClass() == largePositiveIntegerClass;
    }

    public boolean isLargeNegativeInteger(final NativeObject object) {
        return object.getSqueakClass() == largeNegativeIntegerClass;
    }

    public boolean isMetaClass(final ClassObject object) {
        return object == metaClass;
    }

    public boolean isMethodContextClass(final ClassObject object) {
        return object == methodContextClass;
    }

    public boolean isNilClass(final ClassObject object) {
        return object == nilClass;
    }

    public boolean isPoint(final AbstractPointersObject object) {
        return object.getSqueakClass() == pointClass;
    }

    public boolean isSemaphoreClass(final ClassObject object) {
        if (object == semaphoreClass) {
            return true;
        }
        // For Pharo: check if object is a subclass of Semaphore (e.g., SymbolTableSemaphore)
        if (isPharo()) {
            ClassObject current = object;
            while (current != null) {
                if (current == semaphoreClass) {
                    return true;
                }
                current = current.getSuperclassOrNull();
            }
        }
        return false;
    }

    public boolean isWideStringClass(final ClassObject object) {
        return object == getWideStringClass();
    }

    /*
     * INSTANCE CREATION
     */

    public ArrayObject asArrayOfLongs(final long... elements) {
        return ArrayObject.createWithStorage(arrayClass, elements);
    }

    public ArrayObject asArrayOfObjects(final Object... elements) {
        return ArrayObject.createWithStorage(arrayClass, elements);
    }

    public ClassObject getFractionClass() {
        if (fractionClass == null) {
            CompilerDirectives.transferToInterpreterAndInvalidate();
            final Object fractionLookup = lookup("Fraction");
            if (fractionLookup instanceof final ClassObject c) {
                fractionClass = c;
            } else {
                throw SqueakException.create("Unable to find Fraction class");
            }
        }
        return fractionClass;
    }

    public PointersObject asFraction(final long numerator, final long denominator, final AbstractPointersObjectWriteNode writeNode) {
        final long actualNumerator;
        final long actualDenominator;
        if (denominator < 0) { // "keep sign in numerator"
            actualNumerator = -numerator;
            actualDenominator = -denominator;
        } else {
            actualNumerator = numerator;
            actualDenominator = denominator;
        }
        // Calculate gcd
        long n = actualNumerator;
        long m = actualDenominator;
        while (n != 0) {
            n = m % (m = n);
        }
        final long gcd = Math.abs(m);
        // Instantiate reduced fraction
        final PointersObject fraction = new PointersObject(getFractionClass());
        writeNode.execute(fraction, FRACTION.NUMERATOR, actualNumerator / gcd);
        writeNode.execute(fraction, FRACTION.DENOMINATOR, actualDenominator / gcd);
        return fraction;
    }

    public static double fromFraction(final PointersObject fraction, final AbstractPointersObjectReadNode readNode, final Node inlineTarget) {
        assert SqueakGuards.isFraction(fraction, inlineTarget);
        final long numerator = readNode.executeLong(fraction, ObjectLayouts.FRACTION.NUMERATOR);
        final double denominator = readNode.executeLong(fraction, ObjectLayouts.FRACTION.DENOMINATOR);
        return numerator / denominator;
    }

    public NativeObject asByteArray(final byte[] bytes) {
        return NativeObject.newNativeBytes(byteArrayClass, bytes);
    }

    public NativeObject asByteString(final byte[] bytes) {
        return NativeObject.newNativeBytes(byteStringClass, bytes);
    }

    public NativeObject asByteString(final String value) {
        return asByteString(MiscUtils.stringToBytes(value));
    }

    public NativeObject asByteSymbol(final String value) {
        CompilerAsserts.neverPartOfCompilation();
        return (NativeObject) asByteString(value).send(this, "asSymbol");
    }

    private NativeObject asWideString(final String value) {
        return NativeObject.newNativeInts(getWideStringClass(), MiscUtils.stringToCodePointsArray(value));
    }

    public NativeObject asString(final String value, final InlinedConditionProfile wideStringProfile, final Node node) {
        return wideStringProfile.profile(node, NativeObject.needsWideString(value)) ? asWideString(value) : asByteString(value);
    }

    public PointersObject asPoint(final AbstractPointersObjectWriteNode writeNode, final Object xPos, final Object yPos) {
        final PointersObject point = new PointersObject(pointClass);
        writeNode.execute(point, POINT.X, xPos);
        writeNode.execute(point, POINT.Y, yPos);
        return point;
    }

    public ArrayObject newEmptyArray() {
        return ArrayObject.createWithStorage(arrayClass, ArrayUtils.EMPTY_ARRAY);
    }

    public PointersObject newMessage(final AbstractPointersObjectWriteNode writeNode, final NativeObject selector, final ClassObject lookupClass, final Object[] arguments) {
        final PointersObject message = new PointersObject(messageClass);
        writeNode.execute(message, MESSAGE.SELECTOR, selector);
        writeNode.execute(message, MESSAGE.ARGUMENTS, asArrayOfObjects(arguments));
        assert message.instsize() > MESSAGE.LOOKUP_CLASS : "Early versions do not have lookupClass";
        writeNode.execute(message, MESSAGE.LOOKUP_CLASS, lookupClass);
        return message;
    }

    /*
     * INTEROP
     */

    public Object lookup(final String className) {
        final Object specialObject = getSpecialObject(className);
        if (specialObject != NilObject.SINGLETON) {
            return specialObject;
        }
        if (isPharo()) {
            return lookupPharoClass(className);
        }
        return smalltalk.send(this, "at:ifAbsent:", asByteSymbol(className), NilObject.SINGLETON);
    }

    private Object lookupPharoClass(final String className) {
        // 1. Try Smalltalk globals dictionary (Pharo 13 layout)
        final PointersObject globals = smalltalk;
        if (globals == null || globals.getLayout() == null) {
            // globals not yet initialized
        } else if (globals.instsize() == 0) {
            // smalltalk has 0 slots
        } else {
            final Object bindings = globals.instVarAt0Slow(1); // Dictionary array
            if (bindings instanceof final ArrayObject array) {
                final NativeObject selector = asByteString(className);
                for (final Object binding : array.getObjectStorage()) {
                    if (binding instanceof final PointersObject assoc) {
                        if (assoc.instVarAt0Slow(ASSOCIATION.KEY) == selector) {
                            return assoc.instVarAt0Slow(ASSOCIATION.VALUE);
                        }
                    }
                }
            }
        }

        // 2. Fallback: Iterate ClassTable
        // Pharo 13 has a class table in hiddenRoots.
        if (hiddenRoots != null) {
            final Object[] pages = hiddenRoots.getObjectStorage();
            final int numPages = Math.min(pages.length, SqueakImageConstants.CLASS_TABLE_ROOT_SLOTS);
            for (int major = 0; major < numPages; major++) {
                final Object pageObj = pages[major];
                if (pageObj instanceof final ArrayObject page) {
                    for (final Object classObj : page.getObjectStorage()) {
                        if (classObj instanceof final ClassObject cl) {
                            if (className.equals(cl.getClassName())) {
                                return cl;
                            }
                        }
                    }
                }
            }
        }
        return NilObject.SINGLETON;
    }

    private Object getSpecialObject(final String className) {
        final Object result = switch (className) {
            case "Nil" -> nilClass;
            case "False" -> falseClass;
            case "True" -> trueClass;
            case "Scheduler" -> schedulerAssociation;
            case "Bitmap" -> bitmapClass;
            case "SmallInteger" -> smallIntegerClass;
            case "String" -> byteStringClass;
            case "Array" -> arrayClass;
            case "Float" -> floatClass;
            case "MethodContext", "Context" -> methodContextClass;
            case "BlockClosure" -> blockClosureClass;
            case "FullBlockClosure" -> fullBlockClosureClass;
            case "LargePositiveInteger" -> largePositiveIntegerClass;
            case "LargeNegativeInteger" -> largeNegativeIntegerClass;
            case "Character" -> characterClass;
            case "Semaphore" -> semaphoreClass;
            case "Fraction" -> fractionClass;
            default -> NilObject.SINGLETON;
        };
        return result == null ? NilObject.SINGLETON : result;
    }

    @TruffleBoundary
    public NativeObject toInteropSelector(final Message message) {
        assert message.getLibraryClass() == InteropLibrary.class;
        return interopMessageToSelectorMap.computeIfAbsent(message, ignored -> {
            final String libraryName = message.getLibraryClass().getSimpleName();
            final String libraryPrefix = libraryName.substring(0, 1).toLowerCase() + libraryName.substring(1, libraryName.length() - 7);
            final String messageName = message.getSimpleName();
            final String messageCapitalized = messageName.substring(0, 1).toUpperCase() + messageName.substring(1);
            final String suffix;
            switch (message.getParameterCount()) {
                case 1 -> suffix = "";
                case 2 -> suffix = ":";
                default -> suffix = ":" + "and:".repeat(Math.max(0, message.getParameterCount() - 2));
            }
            return asByteSymbol(libraryPrefix + messageCapitalized + suffix);
        });
    }

    /**
     * Replace selector literals in a compiled method with the interned symbol objects from
     * the image. This is necessary because OpalCompiler may create new symbol objects that
     * are not identical (==) to the symbols stored in method dictionaries. Since method
     * lookup uses object identity, non-interned symbols cause doesNotUnderstand errors.
     */
    @TruffleBoundary
    private void internLiterals(final CompiledCodeObject method) {
        for (int i = 0; i < method.getNumLiterals(); i++) {
            final Object literal = method.getLiteral(i);
            if (literal instanceof final NativeObject nativeLiteral && nativeLiteral.isByteType()) {
                final NativeObject interned = findInternedSymbol(nativeLiteral);
                if (interned != null && interned != nativeLiteral) {
                    method.setLiteral(i, interned);
                }
            }
        }
    }

    /**
     * Find the interned symbol that matches the given NativeObject's bytes.
     * Checks the special selectors and all class method dictionaries in the hierarchy.
     */
    @TruffleBoundary
    private NativeObject findInternedSymbol(final NativeObject symbol) {
        final byte[] bytes = symbol.getByteStorage();
        /* Check special selectors first (most common case for arithmetic). */
        final ArrayObject specialSelectors = getSpecialSelectors();
        if (specialSelectors.isObjectType()) {
            final Object[] selectorStorage = specialSelectors.getObjectStorage();
            for (int i = 0; i < selectorStorage.length; i += 2) {
                if (selectorStorage[i] instanceof final NativeObject sel && sel.isByteType()) {
                    if (java.util.Arrays.equals(bytes, sel.getByteStorage())) {
                        return sel;
                    }
                }
            }
        }
        /*
         * Search through well-known class hierarchies' method dictionaries.
         * This covers SmallInteger, Integer, Number, Magnitude, Object, ProtoObject
         * as well as UndefinedObject (nil class), and other common roots.
         */
        final ClassObject[] rootClasses = {smallIntegerClass, nilClass};
        for (final ClassObject rootClass : rootClasses) {
            ClassObject cls = rootClass;
            while (cls != null) {
                final NativeObject found = findSelectorInMethodDict(cls, bytes);
                if (found != null) {
                    return found;
                }
                cls = cls.getSuperclassOrNull();
            }
        }
        return null;
    }

    private static NativeObject findSelectorInMethodDict(final ClassObject classObject, final byte[] selectorBytes) {
        if (classObject.getMethodDict() == null) {
            return null;
        }
        final Object[] variablePart = classObject.getMethodDict().getVariablePart();
        for (final Object entry : variablePart) {
            if (entry instanceof final NativeObject sel && sel.isByteType()) {
                if (java.util.Arrays.equals(selectorBytes, sel.getByteStorage())) {
                    return sel;
                }
            }
        }
        return null;
    }

}
