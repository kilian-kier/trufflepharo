/*
 * Copyright (c) 2017-2026 Software Architecture Group, Hasso Plattner Institute
 * Copyright (c) 2021-2026 Oracle and/or its affiliates
 *
 * Licensed under the MIT License.
 */
package de.hpi.swa.trufflesqueak.nodes.plugins;

import com.oracle.truffle.api.dsl.GenerateNodeFactory;
import com.oracle.truffle.api.dsl.NodeFactory;
import com.oracle.truffle.api.dsl.Specialization;
import com.oracle.truffle.api.frame.VirtualFrame;
import de.hpi.swa.trufflesqueak.nodes.primitives.AbstractPrimitiveFactoryHolder;
import de.hpi.swa.trufflesqueak.nodes.primitives.AbstractPrimitiveNode;
import de.hpi.swa.trufflesqueak.nodes.primitives.AbstractSingletonPrimitiveNode;
import de.hpi.swa.trufflesqueak.nodes.primitives.Primitive.Primitive0;
import de.hpi.swa.trufflesqueak.nodes.primitives.SqueakPrimitive;

import java.util.List;
import java.util.TimeZone;

public final class LocalePlugin extends AbstractPrimitiveFactoryHolder {

    @GenerateNodeFactory
    @SqueakPrimitive(names = "primitiveTimezoneOffset")
    protected abstract static class PrimTimezoneOffset extends AbstractSingletonPrimitiveNode implements Primitive0 {
        @Specialization
        protected static final Object timezoneOffset(final VirtualFrame frame, final Object receiver) {
            final TimeZone defaultZone = TimeZone.getDefault();
            final int offsetMillis = defaultZone.getOffset(System.currentTimeMillis());
            return offsetMillis / 60_000L;
        }
    }

    @Override
    public List<? extends NodeFactory<? extends AbstractPrimitiveNode>> getFactories() {
        return LocalePluginFactory.getFactories();
    }
}
