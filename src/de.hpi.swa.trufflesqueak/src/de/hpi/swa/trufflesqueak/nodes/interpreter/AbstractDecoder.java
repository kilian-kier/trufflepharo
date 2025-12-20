/*
 * Copyright (c) 2017-2025 Software Architecture Group, Hasso Plattner Institute
 * Copyright (c) 2021-2025 Oracle and/or its affiliates
 *
 * Licensed under the MIT License.
 */
package de.hpi.swa.trufflesqueak.nodes.interpreter;

import com.oracle.truffle.api.CompilerAsserts;

import de.hpi.swa.trufflesqueak.exceptions.SqueakExceptions.SqueakException;
import de.hpi.swa.trufflesqueak.model.CompiledCodeObject;

public abstract class AbstractDecoder {

    public abstract boolean hasStoreIntoTemp1AfterCallPrimitive(CompiledCodeObject code);

    public abstract int pcPreviousTo(CompiledCodeObject code, int pc);

    public abstract int determineMaxNumStackSlots(CompiledCodeObject code);

    protected abstract int decodeNumBytes(CompiledCodeObject code, int index);

    protected abstract String decodeBytecodeToString(CompiledCodeObject code, int currentByte, int bytecodeIndex);

    public final String decodeToString(final CompiledCodeObject code) {
        CompilerAsserts.neverPartOfCompilation();
        final StringBuilder sb = new StringBuilder();
        final int trailerPosition = trailerPosition(code);
        int bytecodeIndex = 0;
        int lineIndex = 1;
        int indent = 0;
        final byte[] bytes = code.getBytes();
        while (bytecodeIndex < trailerPosition) {
            final int currentByte = Byte.toUnsignedInt(bytes[bytecodeIndex]);
            sb.append(lineIndex);
            for (int j = 0; j < 1 + indent; j++) {
                sb.append(' ');
            }
            final int numBytecodes = decodeNumBytes(code, bytecodeIndex);
            sb.append('<');
            for (int j = bytecodeIndex; j < bytecodeIndex + numBytecodes; j++) {
                if (j > bytecodeIndex) {
                    sb.append(' ');
                }
                if (j < bytes.length) {
                    sb.append(String.format("%02X", bytes[j]));
                }
            }
            sb.append("> ");
            sb.append(decodeBytecodeToString(code, currentByte, bytecodeIndex));
            if (currentByte == 143) {
                indent++; // increment indent on push closure
            } else if (currentByte == 125) {
                indent--; // decrement indent on block return
            }
            lineIndex++;
            bytecodeIndex += numBytecodes;
            if (bytecodeIndex < trailerPosition) {
                sb.append('\n');
            }
        }
        return sb.toString();
    }

    public final int findLineNumber(final CompiledCodeObject code, final int successorIndex) {
        if (successorIndex == 0) { // handle backjumps to startPC
            return 1;
        }
        final int trailerPosition = trailerPosition(code);
        int index = 0;
        assert index < successorIndex && successorIndex <= trailerPosition : successorIndex + " not between 0 and " + trailerPosition;
        int lineNumber = 0;
        while (index != successorIndex && index < trailerPosition) {
            index += decodeNumBytes(code, index);
            lineNumber++;
        }
        assert index == successorIndex && lineNumber <= trailerPosition;
        return lineNumber;
    }

    public static final int trailerPosition(final CompiledCodeObject code) {
        if (code.isCompiledBlock()) {
            return code.getBytes().length;
        }
        return Math.max(0, code.getBytes().length - 5);
    }

}
