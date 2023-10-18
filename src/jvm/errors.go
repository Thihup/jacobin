/*
 * Jacobin VM - A Java virtual machine
 * Copyright (c) 2023 by  the Jacobin authors. Consult jacobin.org.
 * Licensed under Mozilla Public License 2.0 (MPL 2.0) All rights reserved.
 */

package jvm

import (
	"container/list"
	"encoding/binary"
	"fmt"
	"jacobin/frames"
	"jacobin/globals"
	"jacobin/log"
	"jacobin/object"
	"jacobin/thread"
	"runtime/debug"
	"strings"
)

// routines for formatting error data when an error occurs inside the JVM

// Stack overflow error (e.g., pushing a value when the stack is full, etc.)
func formatStackOverflowError(f *frames.Frame) {
	// Change the bytecode to be IMPDEP2 and give info in four bytes:
	// IMDEP2 (0xFF), 0x01 code for stack underflow, bytes 2 and 3:
	// the present PC written as an int16 value. First check that there
	// are enough bytes in the method that we can overwrite the first four bytes.
	currPC := int16(f.PC)
	if len(f.Meth) < 5 { // the present bytecode + 4 bytes for error info
		f.Meth = make([]byte, 5)
	}

	f.Meth[0] = 0x00 // dummy for the current bytecode
	f.Meth[1] = IMPDEP2
	f.Meth[2] = 0x01

	// now convert the PC at time of error into a two-byte value
	bytes := make([]byte, 2)
	binary.BigEndian.PutUint16(bytes, uint16(currPC))
	f.Meth[3] = bytes[0]
	f.Meth[4] = bytes[1]
	f.PC = 0 // reset the current PC to point to the zeroth byte of our error data
}

// Stack underflow error (e.g., trying to pop when the stack is empty, etc.)
func formatStackUnderflowError(f *frames.Frame) {
	// Change the bytecode to be IMPDEP2 and give info in four bytes:
	// IMDEP2 (0xFF), 0x02 code for stack underflow, bytes 2 and 3:
	// the present PC written as an int16 value. First check that there
	// are enough bytes in the method that we can overwrite the first four bytes.
	currPC := int16(f.PC)
	if len(f.Meth) < 5 { // the present bytecode + 4 bytes for error info
		f.Meth = make([]byte, 5)
	}

	f.Meth[0] = 0x00 // dummy for the current bytecode
	f.Meth[1] = IMPDEP2
	f.Meth[2] = 0x02

	// now convert the PC at time of error into a two-byte value
	bytes := make([]byte, 2)
	binary.BigEndian.PutUint16(bytes, uint16(currPC))
	f.Meth[3] = bytes[0]
	f.Meth[4] = bytes[1]
	f.PC = 0 // reset the current PC to point to the zeroth byte of our error data
}

// Prints out the frame stack
func showFrameStack(t *thread.ExecThread) {
	if globals.GetGlobalRef().JvmFrameStackShown == false {
		entries := grabFrameStack(t.Stack)
		if len(entries) == 0 {
			_ = log.Log("no further data available", log.SEVERE)
			return
		}

		// step through the list-based stack of called methods and print contents
		for i := 0; i < len(entries); i++ {
			_ = log.Log(entries[i], log.SEVERE)
		}
		globals.GetGlobalRef().JvmFrameStackShown = true
	}
}

// gets the full JVM stack trace using java.lang.StackTraceElement slice to hold the data
// in case of error, nil is returned
func getStackTraces(fs *list.List) *object.Object {
	var stackListing []*object.Object

	frameStack := fs.Front()
	if frameStack == nil {
		// return an empty stack listing
		return nil
	}

	// ...will eventually go into java/lang/Throwable.stackTrace
	// ...Type will be: [Ljava/lang/StackTraceElement;
	// ...other fields to be sure to capture: cause, detailMessage,
	// ....not sure about backtrace

	// // step through the list-based stack of called methods and print contents
	for e := frameStack; e != nil; e = e.Next() {
		stackTrace, err := instantiateClass("java/lang/StackTraceElement", nil)
		if err != nil {
			return nil
		}

		frame := e.Value.(*frames.Frame)
		f := stackTrace.FieldTable["declaringClass"]
		f.Fvalue = frame.ClName

		f = stackTrace.FieldTable["methodName"]
		f.Fvalue = frame.MethName

		stackListing = append(stackListing, stackTrace)
	}

	obj := object.MakeEmptyObject()
	klassName := "java/lang/StackTraceElement"
	obj.Klass = &klassName

	// add array to the object we're returning
	fieldToAdd := new(object.Field)
	fieldToAdd.Ftype = "[Ljava/lang/StackTraceElement;"
	fieldToAdd.Fvalue = stackListing

	// add the field to the field table for this object
	obj.FieldTable["stackTrace"] = fieldToAdd
	//

	// 	methName := fmt.Sprintf("%s.%s", val.ClName, val.MethName)
	// 	stackTrace.FieldTable[]
	// 	entry := fmt.Sprintf("Method: %-40s PC: %03d", methName, val.PC)
	// 	stackListing = append(stackListing, entry)
	// }
	// return *stackListing

	return obj
}

// gets the JVM frame stack data and returns it as a slice of strings
func grabFrameStack(fs *list.List) []string {
	var stackListing []string

	frameStack := fs.Front()
	if frameStack == nil {
		// return an empty stack listing
		return stackListing
	}

	// step through the list-based stack of called methods and print contents
	for e := frameStack; e != nil; e = e.Next() {
		val := e.Value.(*frames.Frame)
		methName := fmt.Sprintf("%s.%s", val.ClName, val.MethName)
		entry := fmt.Sprintf("Method: %-40s PC: %03d", methName, val.PC)
		stackListing = append(stackListing, entry)
	}
	return stackListing
}

// takes the panic cause (as returned by the golang runtime) and prints the
// cause as determined by the runtime. Not sure it could ever be nil, but
// covering our bases nonetheless.
func showPanicCause(reason any) {
	// don't show the cause a second time
	if globals.GetGlobalRef().PanicCauseShown {
		return
	}

	// show the event that caused the panic
	if reason != nil {
		cause := fmt.Sprintf("%v", reason)
		_ = log.Log("\nerror: go panic because of "+cause+"\n", log.SEVERE)
	} else {
		_ = log.Log("\nerror: go panic -- cause unknown\n", log.SEVERE)
	}
	globals.GetGlobalRef().PanicCauseShown = true
}

// in the event of a panic, this routine explains that a panic occurred and
// (to a limited extent why) and then prints the golang stack trace.
// stackInfo is the error returned when the panic occurred
func showGoStackTrace(stackInfo any) {
	var stack string

	global := globals.GetGlobalRef()
	if global.GoStackShown {
		return
	}

	if stackInfo != nil && global.PanicCauseShown == false {
		showPanicCause(stackInfo)
	}

	// get the golang stack either b/c it was saved or fetch it new here
	if global.ErrorGoStack != "" {
		stack = global.ErrorGoStack
	} else {
		stack = string(debug.Stack())
	}
	entries := strings.Split(stack, "\n")

	_ = log.Log(" ", log.SEVERE) // print a blank line

	// print the remaining strings in the golang stack trace
	var i = 0
	for {
		if i < len(entries) {
			if strings.HasPrefix(entries[i], "runtime") {
				i += 2 // skip over runtime traces, we just want app data
			}
			_ = log.Log(entries[i], log.SEVERE)
			i += 1
		} else {
			break
		}
	}
	global.GoStackShown = true
}
