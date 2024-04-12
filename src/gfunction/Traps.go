/*
 * Jacobin VM - A Java virtual machine
 * Copyright (c) 2023 by  the Jacobin authors. Consult jacobin.org.
 * Licensed under Mozilla Public License 2.0 (MPL 2.0) All rights reserved.
 */

package gfunction

import (
	"jacobin/exceptions"
)

func Load_Traps() map[string]GMeth {

	MethodSignatures["java/io/DefaultFileSystem.getFileSystem()Ljava/io/FileSystem;"] =
		GMeth{
			ParamSlots: 0,
			GFunction:  trapGetDefaultFileSystem,
		}

	MethodSignatures["java/io/FileDescriptor.<clinit>()"] =
		GMeth{
			ParamSlots: 0,
			GFunction:  trapFileDescriptor,
		}

	MethodSignatures["java/io/FileSystem.<clinit>()"] =
		GMeth{
			ParamSlots: 0,
			GFunction:  trapFileSystem,
		}

	MethodSignatures["java/nio/charset/Charset.<clinit>()"] =
		GMeth{
			ParamSlots: 0,
			GFunction:  trapCharset,
		}

	MethodSignatures["java/nio/channels/FileChannel.<clinit>()"] =
		GMeth{
			ParamSlots: 0,
			GFunction:  trapFileChannel,
		}

	// Unsupported readers

	MethodSignatures["java/io/BufferedReader.<clinit>()"] =
		GMeth{
			ParamSlots: 0,
			GFunction:  trapReader,
		}

	MethodSignatures["java/io/CharArrayReader.<clinit>()"] =
		GMeth{
			ParamSlots: 0,
			GFunction:  trapReader,
		}

	MethodSignatures["java/io/FilterReader.<clinit>()"] =
		GMeth{
			ParamSlots: 0,
			GFunction:  trapReader,
		}

	MethodSignatures["java/io/PipedReader.<clinit>()"] =
		GMeth{
			ParamSlots: 0,
			GFunction:  trapReader,
		}

	MethodSignatures["java/io/StringReader.<clinit>()"] =
		GMeth{
			ParamSlots: 0,
			GFunction:  trapReader,
		}

	// Unsupported writers

	MethodSignatures["java/io/BufferedWriter.<clinit>()"] =
		GMeth{
			ParamSlots: 0,
			GFunction:  trapWriter,
		}

	MethodSignatures["java/io/CharArrayWriter.<clinit>()"] =
		GMeth{
			ParamSlots: 0,
			GFunction:  trapWriter,
		}

	MethodSignatures["java/io/FileSystem.<clinit>()"] =
		GMeth{
			ParamSlots: 0,
			GFunction:  trapFileSystem,
		}

	MethodSignatures["java/io/FilterWriter.<clinit>()"] =
		GMeth{
			ParamSlots: 0,
			GFunction:  trapWriter,
		}

	MethodSignatures["java/io/PipedWriter.<clinit>()"] =
		GMeth{
			ParamSlots: 0,
			GFunction:  trapWriter,
		}

	MethodSignatures["java/io/PrintWriter.<clinit>()"] =
		GMeth{
			ParamSlots: 0,
			GFunction:  trapWriter,
		}

	MethodSignatures["java/io/StringWriter.<clinit>()"] =
		GMeth{
			ParamSlots: 0,
			GFunction:  trapWriter,
		}

	return MethodSignatures
}

// "java/io/DefaultFileSystem.getFileSystem()Ljava/io/FileSystem;"
func trapGetDefaultFileSystem([]interface{}) interface{} {
	errMsg := "DefaultFileSystem.getFileSystem() is not yet supported"
	return getGErrBlk(exceptions.UnsupportedOperationException, errMsg)
}

// Trap for Charset references
func trapCharset([]interface{}) interface{} {
	errMsg := "Class java/nio/charset/Charset is not yet supported"
	return getGErrBlk(exceptions.UnsupportedOperationException, errMsg)
}

// Trap for deprecated functions
func trapDeprecated([]interface{}) interface{} {
	errMsg := "The function requested is deprecated and will not be supported by jacobin"
	return getGErrBlk(exceptions.UnsupportedOperationException, errMsg)
}

// Trap for FileChannel references
func trapFileChannel([]interface{}) interface{} {
	errMsg := "Class java.nio.channels.FileChannel is not yet supported"
	return getGErrBlk(exceptions.UnsupportedOperationException, errMsg)
}

// Trap for FileDescriptor references
func trapFileDescriptor([]interface{}) interface{} {
	errMsg := "Class java/io/FileDescriptor is not yet supported"
	return getGErrBlk(exceptions.UnsupportedOperationException, errMsg)
}

// Trap for FileSystem references
func trapFileSystem([]interface{}) interface{} {
	errMsg := "Class java.io.FileSystem is not yet supported"
	return getGErrBlk(exceptions.UnsupportedOperationException, errMsg)
}

// Trap for unsupported readers
func trapReader([]interface{}) interface{} {
	errMsg := "The requested reader is not yet supported"
	return getGErrBlk(exceptions.UnsupportedOperationException, errMsg)
}

// Trap for unsupported writers
func trapWriter([]interface{}) interface{} {
	errMsg := "The requested writer is not yet supported"
	return getGErrBlk(exceptions.UnsupportedOperationException, errMsg)
}
