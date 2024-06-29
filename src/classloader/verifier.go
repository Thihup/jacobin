package classloader

import (
	"context"
	_ "embed"
	"github.com/ichiban/prolog"
	"github.com/ichiban/prolog/engine"
	"jacobin/stringPool"
	"os"
	"unsafe"
)

var PrologInterpreter = prolog.New(nil, os.Stdout)

//go:embed verifier.pl
var prologVerifier string

func init() {

	ctx := context.TODO()

	err := PrologInterpreter.Compile(ctx, prologVerifier)
	if err != nil {
		panic(err)
	}

}

type VerifierContext struct {
	classloader *Classloader
	class       *Klass
}

func VerifyClass(class *Klass, i *Classloader) error {

	verifierContext := VerifierContext{class: class, classloader: i}

	PrologInterpreter.Register2(engine.NewAtom("classClassName"), classClassName(&verifierContext))
	PrologInterpreter.Register1(engine.NewAtom("classIsInterface"), classIsInterface)
	PrologInterpreter.Register1(engine.NewAtom("classIsNotFinal"), classIsNotFinal)
	PrologInterpreter.Register2(engine.NewAtom("classSuperClassName"), classSuperClassName)
	PrologInterpreter.Register2(engine.NewAtom("classInterfaces"), classInterfaces)
	PrologInterpreter.Register2(engine.NewAtom("classMethods"), classMethods)
	PrologInterpreter.Register2(engine.NewAtom("classAttributes"), classAttributes)
	PrologInterpreter.Register2(engine.NewAtom("classDefiningLoader"), classDefiningLoader)
	PrologInterpreter.Register1(engine.NewAtom("isBootstrapLoader"), isBootstrapLoader)
	PrologInterpreter.Register3(engine.NewAtom("loadedClass"), loadedClass(&verifierContext))
	PrologInterpreter.Register2(engine.NewAtom("methodName"), methodName)
	PrologInterpreter.Register2(engine.NewAtom("methodAccessFlags"), methodAccessFlags)
	PrologInterpreter.Register3(engine.NewAtom("methodDescriptor"), methodDescriptorVerifier)
	PrologInterpreter.Register2(engine.NewAtom("methodAttributes"), methodAttributes)
	PrologInterpreter.Register1(engine.NewAtom("isInit"), isInit)
	PrologInterpreter.Register1(engine.NewAtom("isNotInit"), isNotInit)
	PrologInterpreter.Register2(engine.NewAtom("isNotFinal"), isNotFinal)
	PrologInterpreter.Register2(engine.NewAtom("isFinal"), isFinal)
	PrologInterpreter.Register2(engine.NewAtom("isStatic"), isStatic)
	PrologInterpreter.Register2(engine.NewAtom("isNotStatic"), isNotStatic)
	PrologInterpreter.Register2(engine.NewAtom("isPrivate"), isPrivate)
	PrologInterpreter.Register2(engine.NewAtom("isNotPrivate"), isNotPrivate)
	PrologInterpreter.Register3(engine.NewAtom("isProtected"), isProtected)
	PrologInterpreter.Register3(engine.NewAtom("isNotProtected"), isNotProtected)
	PrologInterpreter.Register2(engine.NewAtom("parseFieldDescriptor"), parseFieldDescriptor)
	PrologInterpreter.Register3(engine.NewAtom("parseMethodDescriptor"), parseMethodDescriptor)
	PrologInterpreter.Register7(engine.NewAtom("parseCodeAttribute"), parseCodeAttributeVerifier)
	PrologInterpreter.Register2(engine.NewAtom("samePackageName"), samePackageName)
	PrologInterpreter.Register2(engine.NewAtom("differentPackageName"), differentPackageName)

	sols := PrologInterpreter.QuerySolution(`classIsTypeSafe(?).`, klassToIntegerPointer(class))

	//if err != nil {
	//	print(err.Error())
	//	print("\n")
	//	return nil
	//}
	//defer sols.Close()

	if err := sols.Err(); err != nil {
		println(err.Error())
		return nil
	}

	return nil
}

func klassToIntegerPointer(class *Klass) engine.Integer {
	return engine.Integer(uintptr(unsafe.Pointer(class)))
}

func methodsArrayToIntegerPointer(class *[]Method) engine.Integer {
	return engine.Integer(uintptr(unsafe.Pointer(class)))
}

// Extracts the name, ClassName, of the class Class.
func classClassName(verifierContext *VerifierContext) engine.Predicate2 {
	return func(vm *engine.VM, Class engine.Term, ClassName engine.Term, cont engine.Cont, env *engine.Env) *engine.Promise {
		return engine.Unify(vm, ClassName, engine.NewAtom(verifierContext.class.Data.Name), cont, env)
	}
}

func getClass(vm *engine.VM, env *engine.Env, term engine.Term) *Klass {
	resolve := env.Resolve(term)

	switch resolve.(type) {
	case engine.Integer:
		integerPtr := resolve.(engine.Integer)
		classInfo := (*Klass)(unsafe.Pointer(uintptr(integerPtr)))
		return classInfo
	default:
		return nil
	}

}

// True iff the class, Class, is an interface.
func classIsInterface(vm *engine.VM, term engine.Term, cont engine.Cont, env *engine.Env) *engine.Promise {
	return engine.Bool(true)
}

// True iff the class, Class, is not a final class.
func classIsNotFinal(vm *engine.VM, Class engine.Term, cont engine.Cont, env *engine.Env) *engine.Promise {
	return engine.Unify(vm, Class, Class, cont, env)
}

// Extracts the name, SuperClassName, of the superclass of class Class.
func classSuperClassName(vm *engine.VM, Class engine.Term, SuperClassName engine.Term, cont engine.Cont, env *engine.Env) *engine.Promise {
	data := getClass(vm, env, Class)
	pointer := stringPool.GetStringPointer(data.Data.SuperclassIndex)
	if *pointer == "" {
		return engine.Bool(false)
	}
	atom := engine.NewAtom(*pointer)
	return engine.Unify(vm, SuperClassName, atom, cont, env)
}

// Extracts a list, Interfaces, of the direct superinterfaces of the class Class.
func classInterfaces(vm *engine.VM, term engine.Term, term2 engine.Term, cont engine.Cont, env *engine.Env) *engine.Promise {
	return engine.Bool(true)
}

// Extracts a list, Methods, of the methods declared in the class Class.
func classMethods(vm *engine.VM, Class engine.Term, Methods engine.Term, cont engine.Cont, env *engine.Env) *engine.Promise {
	class := getClass(vm, env, Class)
	return engine.Unify(vm, Methods, methodsArrayToIntegerPointer(&class.Data.Methods), cont, env)
}

// Extracts a list, Attributes, of the attributes of the class Class.
// Each attribute is represented as a functor application of the form attribute(AttributeName, AttributeContents),
// where AttributeName is the name of the attribute.
// The format of the attribute's contents is unspecified.
func classAttributes(vm *engine.VM, term engine.Term, term2 engine.Term, cont engine.Cont, env *engine.Env) *engine.Promise {
	return engine.Bool(true)
}

// Extracts the defining class loader, Loader, of the class Class.
func classDefiningLoader(vm *engine.VM, Class engine.Term, Loader engine.Term, cont engine.Cont, env *engine.Env) *engine.Promise {
	classData := getClass(vm, env, Class)
	return engine.Unify(vm, Loader, engine.NewAtom(classData.Loader), cont, env)
}

// True iff the class loader Loader is the bootstrap class loader.
func isBootstrapLoader(vm *engine.VM, term engine.Term, cont engine.Cont, env *engine.Env) *engine.Promise {
	return engine.Unify(vm, term, term, cont, env)
}

// True iff there exists a class named Name whose representation (in accordance with this specification) when loaded by the class loader InitiatingLoader is ClassDefinition.
// func loadedClass(vm *engine.VM, Name engine.Term, InitiatingLoader engine.Term, ClassDefinition engine.Term, cont engine.Cont, env *engine.Env) *engine.Promise {
//
//		return engine.Unify(vm, ClassDefinition, classAtom, cont, env)
//	}
func loadedClass(verifierContext *VerifierContext) engine.Predicate3 {
	return func(vm *engine.VM, Name engine.Term, InitiatingLoader engine.Term, ClassDefinition engine.Term, cont engine.Cont, env *engine.Env) *engine.Promise {
		term := printTerm(vm, env, Name)
		term = term[1 : len(term)-1]
		if term == "" {
			return cont(env)
		}
		fetch := MethAreaFetch(term)

		if fetch == nil {
			err := LoadClassFromNameOnlyToClassLoader(verifierContext.classloader, term)
			if err != nil {
				return engine.Unify(vm, ClassDefinition, ClassDefinition, cont, env)
			}
			fetch = MethAreaFetch(term)
			if fetch == nil {
				return cont(env)
			}

		}
		return engine.Unify(vm, ClassDefinition, klassToIntegerPointer(fetch), cont, env)
	}
}

// Extracts the name, Name, of the method Method.
func methodName(vm *engine.VM, term engine.Term, term2 engine.Term, cont engine.Cont, env *engine.Env) *engine.Promise {
	return engine.Bool(true)
}

// Extracts the access flags, AccessFlags, of the method Method.
func methodAccessFlags(vm *engine.VM, term engine.Term, term2 engine.Term, cont engine.Cont, env *engine.Env) *engine.Promise {
	return engine.Bool(true)
}

// Extracts the descriptor, Descriptor, of the method Method.
func methodDescriptorVerifier(vm *engine.VM, term engine.Term, term2 engine.Term, term3 engine.Term, cont engine.Cont, env *engine.Env) *engine.Promise {
	return engine.Bool(true)
}

// Extracts a list, Attributes, of the attributes of the method Method.
func methodAttributes(vm *engine.VM, term engine.Term, term2 engine.Term, cont engine.Cont, env *engine.Env) *engine.Promise {
	return engine.Bool(true)
}

// True iff Method (regardless of class) is <init>.
func isInit(vm *engine.VM, term engine.Term, cont engine.Cont, env *engine.Env) *engine.Promise {
	return engine.Bool(true)
}

// True iff Method (regardless of class) is not <init>.
func isNotInit(vm *engine.VM, term engine.Term, cont engine.Cont, env *engine.Env) *engine.Promise {
	return engine.Bool(true)
}

// True iff Method in class Class is final.
func isFinal(vm *engine.VM, term engine.Term, term2 engine.Term, cont engine.Cont, env *engine.Env) *engine.Promise {
	return engine.Bool(true)
}

// True iff Method in class Class is not final.
func isNotFinal(vm *engine.VM, term engine.Term, term2 engine.Term, cont engine.Cont, env *engine.Env) *engine.Promise {
	return engine.Bool(true)
}

// True iff Method in class Class is static.
func isStatic(vm *engine.VM, term engine.Term, term2 engine.Term, cont engine.Cont, env *engine.Env) *engine.Promise {

	return engine.Bool(true)
}

// True iff Method in class Class is not static.
func isNotStatic(vm *engine.VM, term engine.Term, term2 engine.Term, cont engine.Cont, env *engine.Env) *engine.Promise {

	return engine.Bool(true)
}

// True iff Method in class Class is private.
func isPrivate(vm *engine.VM, term engine.Term, term2 engine.Term, cont engine.Cont, env *engine.Env) *engine.Promise {
	return engine.Bool(true)
}

// True iff Method in class Class is not private.
func isNotPrivate(vm *engine.VM, term engine.Term, term2 engine.Term, cont engine.Cont, env *engine.Env) *engine.Promise {
	return engine.Bool(true)
}

// True iff there is a member named MemberName with descriptor MemberDescriptor in the class MemberClass and it is protected.
func isProtected(vm *engine.VM, term engine.Term, term2 engine.Term, term3 engine.Term, cont engine.Cont, env *engine.Env) *engine.Promise {
	return engine.Bool(true)
}

// True iff there is a member named MemberName with descriptor MemberDescriptor in the class MemberClass and it is not protected.
func isNotProtected(vm *engine.VM, term engine.Term, term2 engine.Term, term3 engine.Term, cont engine.Cont, env *engine.Env) *engine.Promise {
	return engine.Bool(true)
}

// Converts a field descriptor, Descriptor, into the corresponding verification type Type (§4.10.1.2).
func parseFieldDescriptor(vm *engine.VM, term engine.Term, term2 engine.Term, cont engine.Cont, env *engine.Env) *engine.Promise {
	return engine.Bool(true)
}

// Converts a method descriptor, Descriptor, into a list of verification types, ArgTypeList, corresponding to the method argument types, and a verification type, ReturnType, corresponding to the return type.
func parseMethodDescriptor(vm *engine.VM, term engine.Term, term2 engine.Term, term3 engine.Term, cont engine.Cont, env *engine.Env) *engine.Promise {
	return engine.Bool(true)
}

// Extracts the instruction stream, ParsedCode, of the method Method in Class,
// as well as the maximum operand stack size, MaxStack, the maximal number of local variables, FrameSize,
// the exception handlers, Handlers, and the stack map StackMap.
// The representation of the instruction stream and stack map attribute must be as specified in §4.10.1.3 and §4.10.1.4.
func parseCodeAttributeVerifier(vm *engine.VM, term engine.Term, term2 engine.Term, term3 engine.Term, term4 engine.Term, term5 engine.Term, term6 engine.Term, term7 engine.Term, cont engine.Cont, env *engine.Env) *engine.Promise {
	return engine.Bool(true)
}

// True iff the package names of Class1 and Class2 are the same.
func samePackageName(vm *engine.VM, term engine.Term, term2 engine.Term, cont engine.Cont, env *engine.Env) *engine.Promise {
	return engine.Bool(true)
}

// True iff the package names of Class1 and Class2 are different.
func differentPackageName(vm *engine.VM, term engine.Term, term2 engine.Term, cont engine.Cont, env *engine.Env) *engine.Promise {
	return engine.Bool(true)
}

func printTerm(vm *engine.VM, env *engine.Env, term engine.Term) string {
	termString := prolog.TermString("")
	err := termString.Scan(vm, term, env)
	if err != nil {
		return ""
	}
	return string(termString)

}
