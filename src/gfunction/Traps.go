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

	MethodSignatures["java/nio/charset/Charset.<clinit>()"] =
		GMeth{
			ParamSlots: 0,
			GFunction:  trapCharset,
		}

	MethodSignatures["java/io/DefaultFileSystem.getFileSystem()Ljava/io/FileSystem;"] =
		GMeth{
			ParamSlots: 0,
			GFunction:  trapGetDefaultFileSystem,
		}

	MethodSignatures["java/nio/channels/FileChannel.<clinit>()"] =
		GMeth{
			ParamSlots: 0,
			GFunction:  trapFileChannel,
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

	return MethodSignatures
}

// "java/io/DefaultFileSystem.getFileSystem()Ljava/io/FileSystem;"
func trapGetDefaultFileSystem([]interface{}) interface{} {
	errMsg := "DefaultFileSystem.getFileSystem() is not yet supported"
	return getGErrBlk(exceptions.UnsupportedOperationException, errMsg)
}

// ----------- Traps that are global to G functions (only)

// Trap for Charset references
func trapCharset([]interface{}) interface{} {
	errMsg := "Class java/nio/charset/Charset is not yet supported"
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

// Trap for deprecated functions
func trapDeprecated([]interface{}) interface{} {
	errMsg := "The function requested is deprecated and will not be supported by jacobin"
	return getGErrBlk(exceptions.UnsupportedOperationException, errMsg)
}
