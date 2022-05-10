/*
 * Jacobin VM - A Java virtual machine
 * Copyright (c) 2022 by Andrew Binstock. All rights reserved.
 * Licensed under Mozilla Public License 2.0 (MPL 2.0)
 */

package jvm

import (
	"jacobin/classloader"
	"jacobin/globals"
	"jacobin/log"
	"jacobin/shutdown"
	"os"
)

var Global globals.Globals

// JVMrun is where everything begins
func JVMrun() {
	Global = globals.InitGlobals(os.Args[0])
	log.Init()

	// during development, let's use the most verbose logging level
	// log.Level = log.FINEST  // no longer needed
	_ = log.Log("running program: "+Global.JacobinName, log.FINE)

	// handle the command-line interface (cli) -- i.e., process the args
	LoadOptionsTable(Global)
	err := HandleCli(os.Args, &Global)
	if err != nil {
		shutdown.Exit(shutdown.APP_EXCEPTION)
	}
	// some CLI options, like -version, show data and immediately exit. This tests for that.
	if Global.ExitNow == true {
		shutdown.Exit(shutdown.OK)
	}

	if Global.StartingClass == "" {
		_ = log.Log("Error: No executable program specified. Exiting.", log.INFO)
		ShowUsage(os.Stdout)
		shutdown.Exit(shutdown.APP_EXCEPTION)
	}

	// load the starting class, classes it references, and some base classes
	_ = classloader.Init()
	classloader.LoadBaseClasses(&Global)
	mainClass, err := classloader.LoadClassFromFile(classloader.BootstrapCL, Global.StartingClass)
	if err != nil { // the exceptions message will already have been shown to user
		shutdown.Exit(shutdown.JVM_EXCEPTION)
	}
	classloader.LoadReferencedClasses(mainClass)

	// begin execution
	_ = log.Log("Starting execution with: "+Global.StartingClass, log.INFO)
	if StartExec(mainClass, &Global) != nil {
		shutdown.Exit(shutdown.APP_EXCEPTION)
	}

	shutdown.Exit(shutdown.OK)
}
