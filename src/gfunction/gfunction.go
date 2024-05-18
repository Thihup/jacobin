/*
 * Jacobin VM - A Java virtual machine
 * Copyright (c) 2023 by  the Jacobin authors. Consult jacobin.org.
 * Licensed under Mozilla Public License 2.0 (MPL 2.0) All rights reserved.
 */

package gfunction

import (
	"fmt"
	"jacobin/classloader"
	"jacobin/excNames"
	"jacobin/exceptions"
	"jacobin/log"
	"jacobin/object"
	"jacobin/types"
	"os"
	"strings"
)

// Map repository of method signatures for all G functions:
var MethodSignatures = make(map[string]GMeth)

// File I/O and stream Field keys:
var FileStatus string = "status"     // using this value in case some member function is looking at it
var FilePath string = "FilePath"     // full absolute path of a file aka canonical path
var FileHandle string = "FileHandle" // *os.File
var FileMark string = "FileMark"     // file position relative to beginning (0)
var FileAtEOF string = "FileAtEOF"   // file at EOF

// File I/O constants:
var CreateFilePermissions os.FileMode = 0664 // When creating, read and write for user and group, others read-only

// Radix boundaries:
var MinRadix int64 = 2
var MaxRadix int64 = 36
var MaxIntValue int64 = 2147483647
var MinIntValue int64 = -2147483648

// GMeth is the entry in the MTable for Go functions. See MTable comments for details.
//   - ParamSlots - the number of user parameters in a G function. E.g. For atan2, this would be 2.
//   - GFunction - a go function. All go functions accept a possibly empty slice of interface{} and
//     return an interface{} which might be nil (E.g. Java void).
//   - NeedsContext - does this method need a pointer to the frame stack? Defaults to false.
type GMeth struct {
	ParamSlots   int
	GFunction    func([]interface{}) interface{}
	NeedsContext bool
}

// G function error block.
type GErrBlk struct {
	ExceptionType int
	ErrMsg        string
}

// Construct a G function error block. Return a ptr to it.
func getGErrBlk(exceptionType int, errMsg string) *GErrBlk {
	var gErrBlk GErrBlk
	gErrBlk.ExceptionType = exceptionType
	gErrBlk.ErrMsg = errMsg
	return &gErrBlk
}

// MTableLoadGFunctions loads the Go methods from files that contain them. It does this
// by calling the Load_* function in each of those files to load whatever Go functions
// they make available.
func MTableLoadGFunctions(MTable *classloader.MT) {

	Load_Io_Console() // load the java.io.Console golang functions

	Load_Io_BufferedReader()
	Load_Io_File()
	Load_Io_FileInputStream()
	Load_Io_FileOutputStream()
	Load_Io_FileReader()
	Load_Io_FileWriter()
	Load_Io_InputStreamReader()
	Load_Io_OutputStreamWriter()
	Load_Io_PrintStream()
	Load_Io_RandomAccessFile()

	Load_Lang_Boolean()
	Load_Lang_Byte()
	Load_Lang_Character()
	Load_Lang_Class() // load the java.lang.Class golang functions
	Load_Lang_Double()
	Load_Lang_Float()
	Load_Lang_Integer()
	Load_Lang_Long()
	Load_Lang_Math()   // load the java.lang.Math & StrictMath golang functions
	Load_Lang_Object() // load the java.lang.Class golang functions
	Load_Lang_Short()
	Load_Lang_String()            // load the java.lang.String golang functions
	Load_Lang_StringBuilder()     // load the java.lang.StringBuilder golang functions
	Load_Lang_System()            // load the java.lang.System golang functions
	Load_Lang_StackTraceELement() //  java.lang.StackTraceElement golang functions
	Load_Lang_Thread()            // load the java.lang.Thread golang functions
	Load_Lang_Throwable()         // load the java.lang.Throwable golang functions (errors & exceptions)
	Load_Lang_UTF16()             // load the java.lang.UTF16 golang functions

	Load_Nio_Charset_Charset() // Zero Charset support

	Load_Util_Concurrent_Atomic_AtomicInteger()
	Load_Util_Concurrent_Atomic_Atomic_Long()
	Load_Util_HashMap()
	Load_Util_HexFormat()
	Load_Util_Locale()
	Load_Util_Random()

	Load_Jdk_Internal_Misc_Unsafe()
	Load_Jdk_Internal_Misc_ScopedMemoryAccess()

	Load_Nil_Clinit() // Load <clinit> functions that invoke justReturn()
	Load_Traps()      // Load traps that lead to unconditional error returns

	/*
		With the accumulated MethodSignatures maps, load MTable.
	*/
	loadlib(MTable, MethodSignatures)

}

func checkKey(key string) bool {
	if strings.Index(key, ".") == -1 || strings.Index(key, "(") == -1 || strings.Index(key, ")") == -1 {
		return false
	}
	if strings.HasSuffix(key, ")") {
		return false
	}
	return true
}

func loadlib(tbl *classloader.MT, libMeths map[string]GMeth) {
	ok := true
	for key, val := range libMeths {
		if !checkKey(key) {
			errMsg := fmt.Sprintf("loadlib: Invalid key=%s", key)
			log.Log(errMsg, log.SEVERE)
			ok = false
		}
		gme := GMeth{}
		gme.ParamSlots = val.ParamSlots
		gme.GFunction = val.GFunction
		gme.NeedsContext = val.NeedsContext

		tableEntry := classloader.MTentry{
			MType: 'G',
			Meth:  gme,
		}

		classloader.AddEntry(tbl, key, tableEntry)
	}
	if !ok {
		exceptions.ThrowExNil(excNames.InternalException, "loadlib: at least one key was invalid")
	}
}

// do-nothing Go function shared by several source files
func justReturn([]interface{}) interface{} {
	return nil
}

// Populate an object for a primitive type (Byte, Character, Double, Float, Integer, Long, Short, String).
func populator(classname string, fldtype string, fldvalue interface{}) interface{} {
	var objPtr *object.Object
	if fldtype == types.StringIndex {
		objPtr = object.StringObjectFromGoString(fldvalue.(string))
	} else {
		objPtr = object.MakePrimitiveObject(classname, fldtype, fldvalue)
		(*objPtr).FieldTable["value"] = object.Field{fldtype, fldvalue}
	}
	return objPtr
}

// File set EOF condition.
func eofSet(obj *object.Object, value bool) {
	obj.FieldTable[FileAtEOF] = object.Field{Ftype: types.Bool, Fvalue: value}
}

// File get EOF boolean.
func eofGet(obj *object.Object) bool {
	value, ok := obj.FieldTable[FileAtEOF].Fvalue.(bool)
	if !ok {
		return false
	}
	return value
}
