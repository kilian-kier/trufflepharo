/*
 * Copyright (c) 2025-2025 Software Architecture Group, Hasso Plattner Institute
 * Copyright (c) 2025-2025 Oracle and/or its affiliates
 *
 * Licensed under the MIT License.
 */
package de.hpi.swa.trufflesqueak.nodes.interpreter;

import de.hpi.swa.trufflesqueak.exceptions.SqueakExceptions.SqueakException;
import de.hpi.swa.trufflesqueak.model.CompiledCodeObject;

public class BytecodeUtils {
    public static final int trailerPosition(final CompiledCodeObject code) {
        if (code.isCompiledBlock()) {
            return code.getBytes().length;
        } else {
            return Math.max(0, code.getBytes().length - 5);
        }
    }
}
