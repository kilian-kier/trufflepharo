/*
 * Copyright (c) 2026 Software Architecture Group, Hasso Plattner Institute
 * Copyright (c) 2026 Oracle and/or its affiliates
 *
 * Licensed under the MIT License.
 */

package de.hpi.swa.trufflesqueak.nodes.plugins;

import com.oracle.truffle.api.CompilerDirectives.CompilationFinal;
import com.oracle.truffle.api.dsl.GenerateNodeFactory;
import com.oracle.truffle.api.dsl.NodeFactory;
import com.oracle.truffle.api.dsl.Specialization;
import de.hpi.swa.trufflesqueak.image.SqueakImageContext;
import de.hpi.swa.trufflesqueak.model.NilObject;
import de.hpi.swa.trufflesqueak.nodes.primitives.AbstractPrimitiveFactoryHolder;
import de.hpi.swa.trufflesqueak.nodes.primitives.AbstractPrimitiveNode;
import de.hpi.swa.trufflesqueak.nodes.primitives.Primitive;
import de.hpi.swa.trufflesqueak.nodes.primitives.SqueakPrimitive;
import de.hpi.swa.trufflesqueak.util.OS;

import java.util.Arrays;
import java.util.List;

public final class FileAttributesPlugin extends AbstractPrimitiveFactoryHolder {

    @GenerateNodeFactory
    @SqueakPrimitive(names = "primitiveFileMasks")
    protected abstract static class PrimFileMasksNode extends AbstractPrimitiveNode implements Primitive.Primitive0 {
        private static final long S_IFMT = 0170000L;
        private static final long S_IFSOCK = 0140000L;
        private static final long S_IFLNK = 0120000L;
        private static final long S_IFREG = 0100000L;
        private static final long S_IFBLK = 0060000L;
        private static final long S_IFDIR = 0040000L;
        private static final long S_IFCHR = 0020000L;
        private static final long S_IFIFO = 0010000L;

        @CompilationFinal(dimensions = 1) private static final Object[] MASK_TEMPLATE = computeMasks();

        private static Object[] computeMasks() {
            final Object[] masks = new Object[8];

            Arrays.fill(masks, NilObject.SINGLETON);

            masks[0] = S_IFMT;

            if (!OS.isWindows()) {
                masks[1] = S_IFSOCK;
                masks[2] = S_IFLNK;
            }

            masks[3] = S_IFREG;
            masks[4] = S_IFBLK;
            masks[5] = S_IFDIR;
            masks[6] = S_IFCHR;
            masks[7] = S_IFIFO;

            return masks;
        }

        @Specialization
        protected final Object doMasks(@SuppressWarnings("unused") final Object receiver) {
            final SqueakImageContext image = getContext();
            return image.asArrayOfObjects(MASK_TEMPLATE.clone());
        }
    }

    @Override
    public List<? extends NodeFactory<? extends AbstractPrimitiveNode>> getFactories() {
        return FileAttributesPluginFactory.getFactories();
    }
}
