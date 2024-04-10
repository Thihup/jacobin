/*
 * Jacobin VM - A Java virtual machine
 * Copyright (c) 2023 by  the Jacobin authors. Consult jacobin.org.
 * Licensed under Mozilla Public License 2.0 (MPL 2.0) All rights reserved.
 */

package gfunction

func Load_Io_FileWriter() map[string]GMeth {

	MethodSignatures["java/io/FileWriter.<clinit>()V"] =
		GMeth{
			ParamSlots: 0,
			GFunction:  justReturn,
		}

	MethodSignatures["java/io/FileWriter.<init>(Ljava/io/File;)V"] =
		GMeth{
			ParamSlots: 1,
			GFunction:  initFileOutputStreamFile,
		}

	MethodSignatures["java/io/FileWriter.<init>(Ljava/io/File;Z)V"] =
		GMeth{
			ParamSlots: 1,
			GFunction:  initFileOutputStreamFileBoolean,
		}

	MethodSignatures["java/io/FileWriter.<init>(Ljava/lang/String;)V"] =
		GMeth{
			ParamSlots: 1,
			GFunction:  initFileOutputStreamString,
		}

	MethodSignatures["java/io/FileWriter.<init>(Ljava/lang/String;Z)V"] =
		GMeth{
			ParamSlots: 1,
			GFunction:  initFileOutputStreamStringBoolean,
		}

	MethodSignatures["java/io/FileWriter.close()V"] =
		GMeth{
			ParamSlots: 0,
			GFunction:  osrClose,
		}

	MethodSignatures["java/io/FileWriter.flush()V"] =
		GMeth{
			ParamSlots: 0,
			GFunction:  osrFlush,
		}

	MethodSignatures["java/io/FileWriter.write(I)V"] =
		GMeth{
			ParamSlots: 1,
			GFunction:  osrWriteOneChar,
		}

	MethodSignatures["java/io/FileWriter.write([CII)V"] =
		GMeth{
			ParamSlots: 3,
			GFunction:  WriteCharBuffer,
		}

	MethodSignatures["java/io/FileWriter.write(Ljava/lang/String;II)V"] =
		GMeth{
			ParamSlots: 3,
			GFunction:  WriteStringBuffer,
		}

	// -----------------------------------------
	// Traps that do nothing but return an error
	// -----------------------------------------

	MethodSignatures["java/io/FileWriter.<init>(Ljava/io/File;Ljava/lang.String;)V"] =
		GMeth{
			ParamSlots: 2,
			GFunction:  trapCharset,
		}

	MethodSignatures["java/io/FileWriter.<init>(Ljava/io/FileDescriptor;)V"] =
		GMeth{
			ParamSlots: 1,
			GFunction:  trapFileDescriptor,
		}

	MethodSignatures["java/io/FileWriter.<init>(Ljava/io/File;Ljava/nio/charset/Charset;)V"] =
		GMeth{
			ParamSlots: 2,
			GFunction:  trapCharset,
		}

	MethodSignatures["java/io/FileWriter.<init>(Ljava/io/File;Ljava/nio/charset/Charset;Z)V"] =
		GMeth{
			ParamSlots: 3,
			GFunction:  trapCharset,
		}

	MethodSignatures["java/io/FileWriter.<init>(Ljava/lang/String;Ljava/nio/charset/Charset;)V"] =
		GMeth{
			ParamSlots: 2,
			GFunction:  trapCharset,
		}

	MethodSignatures["java/io/FileWriter.<init>(Ljava/lang/String;Ljava/nio/charset/Charset;Z)V"] =
		GMeth{
			ParamSlots: 3,
			GFunction:  trapCharset,
		}

	return MethodSignatures
}
