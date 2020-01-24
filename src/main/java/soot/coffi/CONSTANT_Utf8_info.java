package soot.coffi;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 1997 Clark Verbrugge
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as
 * published by the Free Software Foundation, either version 2.1 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Lesser Public License for more details.
 *
 * You should have received a copy of the GNU General Lesser Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/lgpl-2.1.html>.
 * #L%
 */

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.IOException;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.G;
import soot.Value;
import soot.jimple.ConstantFactory;

/**
 * A constant pool entry of type CONSTANT_Utf8; note this is <b>not</b> multithread safe. It is, however, immutable.
 *
 * @author Clark Verbrugge
 */
public class CONSTANT_Utf8_info  {
    private static final Logger logger = LoggerFactory.getLogger(CONSTANT_Utf8_info.class);
    // Some local private objects to help with efficient comparisons.


    /**
     * Utility method; converts the given String into a utf8 encoded array of bytes.
     *
     * @param s
     *          String to encode.
     * @return array of bytes, utf8 encoded version of s.
     */
    public static byte[] toUtf8(String s) {
        try {
            ByteArrayOutputStream bs = new ByteArrayOutputStream(s.length());
            DataOutputStream d = new DataOutputStream(bs);
            d.writeUTF(s);
            return bs.toByteArray();
        } catch (IOException e) {
            logger.debug("Some sort of IO exception in toUtf8 with " + s);
        }
        return null;
    }


    /**
     * Returns a String description of what kind of entry this is.
     *
     * @return the String "utf8".
     */
    public String typeName() {
        return "utf8";
    }

}
