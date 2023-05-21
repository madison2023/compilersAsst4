package visitor;

import syntaxtree.*;

import java.util.*;

import errorMsg.*;
// The purpose of this class is to do type-checking and related
// actions.  These include:
// - evaluate the type for each expression, filling in the 'type'
//   link for each
// - ensure that each expression follows MiniJava's type rules (e.g.,
//   that the arguments to '*' are both integer, the argument to
//   '.length' is an array, etc.)
// - ensure that each method-call follows Java's type rules:
//   - there exists a method for the given class (or a superclass)
//     for the receiver's object type
//   - the method has the correct number of parameters
//   - the types of each actual parameter is compatible with that
//     of its corresponding formal parameter
// - ensure that for each instance variable access (e.g., abc.foo),
//   there is an instance variable defined for the given class (or
//   in a superclass
//   - sets the 'varDec' link in the InstVarAccess to refer to the
//     method
// - ensure that the RHS expression in each assignment statement is
//   type-compatible with its corresponding LHS
//   - also checks that the LHS an lvalue
// - ensure that if a method with a given name is defined in both
//   a subclass and a superclass, that they have the same parameters
//   (with identical types) and the same return type
// - ensure that the declared return-type of a method is compatible
//   with its "return" expression
// - ensuring that the type of the control expression for an if- or
//   while-statement is boolean
public class Sem4Visitor extends ASTvisitor {

	ClassDecl currentClass;
	IdentifierType currentClassType;
	IdentifierType currentSuperclassType;
	ConstEvalVisitor constVisitor;
	ClassDecl objectClassDecl;
	ErrorMsg errorMsg;

	BooleanType theBoolType;
	IntegerType theIntType;
	NullType theNullType;
	VoidType theVoidType;
	IdentifierType theStringType;

	Hashtable<String,ClassDecl> globalSymTab;

	public Sem4Visitor(Hashtable<String,ClassDecl> globalSymTb, ErrorMsg e) {
		errorMsg = e;
		globalSymTab = globalSymTb;
		initInstanceVars();
		constVisitor = new ConstEvalVisitor();
	}

	private void initInstanceVars() {
		currentClass = null;

		objectClassDecl = globalSymTab.get("Object");
		theBoolType = new BooleanType(-1);
		theIntType = new IntegerType(-1);
		theNullType = new NullType(-1);
		theVoidType = new VoidType(-1);
		if (globalSymTab != null) {
			theStringType = new IdentifierType(-1, "String");
			theStringType.link = globalSymTab.get("String");
		}
	}
	
	
	/*
	Checks whether two type objects represent exactly the same type 
	(i.e., tests for strict equivalence). If either Type is null, return false. 
	Otherwise check them for equality (using .equals, which Type objects understand). 
	If they are equal, return true, otherwise print an "incompatible types" 
	error message (unless pos is negative) and return false.
	*/
	public boolean matchTypesExact(Type have, Type need, int pos) {
		if(have == null || need == null) {
			return false;
		}
		else if (have.equals(need)){
			return true;
		}
		else {
			if (pos >= 0) {
				errorMsg.error(pos, "Error: " + have.toString() + " should be " + need.toString());
			}
			return false;
		}
	}
	
	
	/*
	 * Checks whether src is assignment-compatible with target. If either Type is
	 * null, return false. Otherwise, if either is a VoidType object, print an
	 * "incompatible types" error message and return false. Otherwise, if the types
	 * are equal (using .equals) return true. If src is a NullType object, also
	 * return true if target is an IdentifierType or an ArrayType. If src is an
	 * ArrayType and the target is an IdentifierType with the name Object, return
	 * true. If src is an IdentifierType object, return true if target is a (direct
	 * or indirect) superclass. Otherwise print an "incompatible types" error
	 * message (unless pos is negative) and return false.
	 */	
	public boolean matchTypesAssign(Type src, Type target, int pos) {
		if(src == null || target == null) {
			return false;
		}
		else if (src instanceof VoidType || target instanceof VoidType) {
			//if either is a VoidType object, print an "incompatible types" error message and return false.
			if (pos >= 0) {
				errorMsg.error(pos, "Error: " + src.toString() + " does not conform to " + target.toString());
			}
			return false;
		}
		else if (src.equals(target)) {
			//if the types are equal (using .equals) return true
			return true;
		}
		else if (src instanceof NullType && (target instanceof IdentifierType || target instanceof ArrayType)) {
			//If src is a NullType object, also return true if target is an IdentifierType or an ArrayType
			return true;
		}
		else if (src instanceof ArrayType && target instanceof IdentifierType && ((IdentifierType) target).name.equals("Object")) { //double check this
			//If src is an ArrayType and the target is an IdentifierType with the name Object, return true
			return true;
		}
		else if (src instanceof IdentifierType && target instanceof IdentifierType) {
			//If src is an IdentifierType object, return true if target is a (direct or indirect) superclass.
			if (findSuperClassMatch(((IdentifierType) src).link, ((IdentifierType)target).link)) {
				return true;
			}
		}
		
		if (pos >= 0) {
			//Otherwise print an "incompatible types" error message (unless pos is negative) and return false.
			errorMsg.error(pos, "Error: " + src.toString() + " does not conform to " + target.toString());
		}
		return false;
	}
	
	public boolean findSuperClassMatch(ClassDecl srcDecl, ClassDecl targetDecl) {
		//If src is an IdentifierType object, return true if target is a (direct or indirect) superclass.
		if(srcDecl == null) {
			return false; //we did not find a match going all the way up the super links
		}
		else if(srcDecl == targetDecl) {
			return true;
		}
		else {
			return findSuperClassMatch(srcDecl.superLink, targetDecl);
		}
	}
	
	/*
	 * Checks whether t1 and t2 can be compared using == or !=. If either Type is
	 * null, return false. Otherwise, invoke matchTypesAssign twice—once with t1
	 * first; once with t2 first—but with a negative pos, so that the error message
	 * does not get flagged. If either returns true, return true. Otherwise print an
	 * "incompatible types" error message (unless pos is negative) and return false.
	 */	
	public boolean matchTypesEqCompare(Type t1, Type t2, int pos) {
		//null check
		if (t1 == null || t2 == null) {
			return false;
		}
		//check if can be compared using == or !=
		else if (matchTypesAssign(t1,t2,-1) || matchTypesAssign(t2,t1,-1)){
			return true;
			
		}
		else {
			if (pos >= 0){
			errorMsg.error(pos, "Error: " + t1.toString() + " and " + t2.toString() + " are incompatible types");
			}
			return false;

		}
	}
	
	/*
	 * this method returns the InstVarDecl object for the class denoted by classDecl, or
	 * null if such does not exist. Start by looking up name in the clas's
	 * instance-variable symbol table. If it's there, return it. If not, look in the
	 * instance variable symbol table of the superclass, then the super-super-class,
	 * etc. If it's in none of those, report an error using pos as the file position
	 * and msg as the error message.
	 */	
	public InstVarDecl instVarLookup(String name, ClassDecl classDecl, int pos, String msg) {
		if (classDecl == null) {
			if (pos >= 0) {
				errorMsg.error(pos, msg); 
			}
			return null;
		}
		else {
			InstVarDecl decl = classDecl.instVarTable.get(name);
			if (decl != null) {
				return decl;
			}
			else {
				return instVarLookup(name, classDecl.superLink, pos, msg);
			}
		}
		
	}
	
	/*
	 * this method returns the InstVarDecl object for the name in the class denoted
	 * by t, or null if such does not exist. In particular it returns null
	 * immediately if t is null. Otherwise, if t is not an IdentifierType, report an
	 * error using msg as the error message. Otherwise return the result of looking
	 * up the instance variable name in the class to which t refers (version of
	 * instVarLookup defined above).
	 */	
	public InstVarDecl instVarLookup(String name, Type t, int pos, String msg) {
		if (t == null) {
			return null;
		}
		else if (!(t instanceof IdentifierType)) {
			if (pos >= 0) {
				errorMsg.error(pos, msg);
			}
			return null;
		}
		else {
			return instVarLookup(name, globalSymTab.get(((IdentifierType) t).name), pos, msg); 
		}
	}
	
	public MethodDecl methodLookup(String name, ClassDecl classDecl, int pos, String msg) {
		if (classDecl == null) {
			if (pos >= 0) {
				errorMsg.error(pos, msg); 
			}
			return null;
		}
		else {
			MethodDecl decl = classDecl.methodTable.get(name);
			if (decl != null) {
				return decl;
			}
			else {
				return methodLookup(name, classDecl.superLink, pos, msg);
			}
		}
	}
	
	public MethodDecl methodLookup(String name, Type t, int pos, String msg) {
		if (t == null) {
			return null;
		}
		else if (!(t instanceof IdentifierType)) {
			if (pos >= 0) {
				errorMsg.error(pos, msg);
			}
			return null;
		}
		else {
			return methodLookup(name, globalSymTab.get(((IdentifierType)t).name), pos, msg); 
		}
	}
	
	
	@Override
	public Object visitIntegerLiteral(IntegerLiteral n) {
		super.visitIntegerLiteral(n);
		n.type = theIntType;
		return null;
	}

	@Override
	public Object visitStringLiteral(StringLiteral n) {
		super.visitStringLiteral(n);
		n.type = theStringType;
		return null;
	}
	
	@Override
	public Object visitIdentifierExp(IdentifierExp n) {
		super.visitIdentifierExp(n);
		n.type = n.link.type;
		return null;
	}
	
	@Override
  	public Object visitNull(Null n) {
  		super.visitNull(n);
  		n.type = theNullType;
  		return null;
  	}
	
	@Override
  	public Object visitTrue(True n) {
		super.visitTrue(n);
		n.type = theBoolType;
		return null;
	}
	
	@Override
	public Object visitFalse(False n) {
		super.visitFalse(n);
		n.type = theBoolType;
		return null;
	}
	
	@Override
  	public Object visitThis(This n) {
  		super.visitThis(n);
  		n.type = currentClassType;
  		return null;
  	}

	@Override
  	public Object visitSuper(Super n) {
  		super.visitSuper(n);
  		n.type = currentSuperclassType;
  		return null;
  	}
	
	@Override
  	public Object visitPlus(Plus n) {
		super.visitPlus(n);
		//check that both sides have ints
		matchTypesExact(n.left.type, theIntType,n.left.pos);
		matchTypesExact(n.right.type, theIntType,n.right.pos);
		//set type
		n.type = theIntType;
		return null;
	}

	@Override
  	public Object visitMinus(Minus n) {
		super.visitMinus(n);
		//check that both sides have ints
		matchTypesExact(n.left.type, theIntType,n.left.pos);
		matchTypesExact(n.right.type, theIntType,n.right.pos);
		//set type
		n.type = theIntType;
		return null;
	}
	
	@Override
  	public Object visitTimes(Times n) {
		super.visitTimes(n);
		//check that both sides have ints
		matchTypesExact(n.left.type, theIntType,n.left.pos);
		matchTypesExact(n.right.type, theIntType,n.right.pos);
		//set type
		n.type = theIntType;
		return null;
	}
	
	@Override
  	public Object visitDivide(Divide n) {
		super.visitDivide(n);
		//check that both sides have ints
		matchTypesExact(n.left.type, theIntType,n.left.pos);
		matchTypesExact(n.right.type, theIntType,n.right.pos);
		//set type
		n.type = theIntType;
		return null;
	}
	
	@Override
  	public Object visitRemainder(Remainder n) {
		super.visitRemainder(n);
		//check that both sides have ints
		matchTypesExact(n.left.type, theIntType,n.left.pos);
		matchTypesExact(n.right.type, theIntType,n.right.pos);
		//set type
		n.type = theIntType;
		return null;
	}
	
	@Override
	public Object visitGreaterThan(GreaterThan n) {
		super.visitGreaterThan(n);
		//check that both sides have ints
		matchTypesExact(n.left.type, theIntType,n.left.pos);
		matchTypesExact(n.right.type, theIntType,n.right.pos);
		//set type
		n.type = theBoolType;
		return null;
	}
	
	@Override
	public Object visitLessThan(LessThan n) {
		super.visitLessThan(n);
		//check that both sides have ints
		matchTypesExact(n.left.type, theIntType,n.left.pos);
		matchTypesExact(n.right.type, theIntType,n.right.pos);
		//set type
		n.type = theBoolType;
		return null;
	}
	
	@Override
	public Object visitEquals(Equals n) {
		super.visitEquals(n);
		//check that both sides have same types
		matchTypesEqCompare(n.left.type,n.right.type,n.pos);
		//set type
		n.type = theBoolType;
		return null;
	}
	
	@Override
	public Object visitNot(Not n) {
		super.visitNot(n);
		//check that operand is a bool
		matchTypesExact(n.exp.type, theBoolType, n.pos);
		//set type
		n.type = theBoolType;
		return null;
	}
	
	@Override
	public Object visitAnd(And n) {
		super.visitAnd(n);
		//check that operands are bools
		matchTypesExact(n.left.type, theBoolType, n.left.pos);
		matchTypesExact(n.right.type, theBoolType, n.right.pos);
		//set type
		n.type = theBoolType;
		return null;
	}
	
	@Override
	public Object visitOr(Or n) {
		super.visitOr(n);
		//check that operands are bools
		matchTypesExact(n.left.type, theBoolType, n.left.pos);
		matchTypesExact(n.right.type, theBoolType, n.right.pos);
		//set type
		n.type = theBoolType;
		return null;
	}
	
	@Override
	public Object visitArrayLength(ArrayLength n) {
		super.visitArrayLength(n);
		if (n.exp.type == null || !(n.exp.type instanceof ArrayType)) {
			if (n.pos >= 0) {
				errorMsg.error(n.pos, "Error: Array Length operation on expression with invalid type " + n.exp.type.toString());
			}
		}
		n.type = theIntType;
		return null;
	}

	
	
	@Override
	public Object visitArrayLookup(ArrayLookup n) {
		super.visitArrayLookup(n);
		//check that the idxExp field's type exactly matches theIntType
		boolean isMatch = matchTypesExact(n.idxExp.type, theIntType, n.pos);
		//check that the arrExp field's type is an ArrayType (and is not null)
		if(!(n.arrExp.type instanceof ArrayType) || n.arrExp.type == null) {
			if(n.pos >= 0) {
				errorMsg.error(n.pos, "Error: Indexing of non-array type");
			}
		}
		else if (isMatch){
		n.type = n.arrExp.type;
		}
		return null;
	}

	/*
	 * if the exp field's type is null, silently return 
	 * set varDec field to refer to the declaration of the named instance variable (hint: use instVarLookup) 
	 * report error and return if such an instance variable is not
	 * defined 
	 * assuming the varDec was set to a non-null value, set the type
	 * Again, traverse subnodes first. field to be type of the declared instance
	 * variable
	 */
	@Override
	public Object visitInstVarAccess(InstVarAccess n) {
		super.visitInstVarAccess(n);
		if (n.exp == null) {
			return null;
		}
		else {
			n.varDec = instVarLookup(n.varName, n.exp.type, n.pos, "Error: Instance Variable " + n.varName + " is not defined for " + n.exp.type);
			if (n.varDec != null) {
				n.type = n.varDec.type;
			}
			return null;
		}
		
	}
	
	@Override
	public Object visitCast(Cast n) {
		super.visitCast(n);
		if (n.castType.equals(theIntType) || n.castType.equals(theBoolType)) {
			if (n.pos >= 0) {
				errorMsg.error(n.pos, "Error: Cannot cast to " + n.castType.toString() + " type");
			}
		}

		if(n.exp.type == null || n.castType == null) {
			return null;
		}
		
		if(!(matchTypesAssign(n.exp.type, n.castType, -1) || matchTypesAssign(n.castType, n.exp.type, -1))) {
			if(n.pos >= 0) {
				errorMsg.error(n.pos, "Error: Incompatible types, cannot cast between " + n.exp.type + " and " + n.castType);
			}
		}
		
		n.type = n.castType;
		return null;
	}

	@Override
	public Object visitInstanceOf(InstanceOf n) {
		super.visitInstanceOf(n);
		if (n.checkType.equals(theBoolType) || n.checkType.equals(theIntType)) {
			if (n.pos >= 0) {
				errorMsg.error(n.pos, "Cannot check type " + n.checkType.toString());
			}
		}
		
		if(n.exp.type == null || n.checkType == null) {
			return null;
		}
	
		if (!(matchTypesAssign(n.exp.type,n.checkType,-1) || matchTypesAssign(n.checkType,n.exp.type,-1))) {
			if (n.pos >= 0) {
				errorMsg.error(n.pos, "Error: unrelated instanceof operands " + n.exp.type + " and " + n.checkType);
			}
		}
		n.type = theBoolType;
		return null;
	}

	@Override
	public Object visitNewObject(NewObject n) {
		super.visitNewObject(n);
		n.type = n.objType;
		return null;
	}

	@Override
  	public Object visitNewArray(NewArray n) {
  		super.visitNewArray(n);
  		
  		matchTypesExact(n.sizeExp.type, theIntType, n.pos);
  		n.type = new ArrayType(n.pos, n.objType);
  		return null;
  	}

  	@Override
  	public Object visitCall(Call n) {
  		super.visitCall(n);
  		if (n.obj == null) {
  			return null;
  		}
  		
  		n.methodLink = methodLookup(n.methName, n.obj.type, n.pos, "Error: Method " + n.methName.toString() + " is not defined for " + n.obj.type);
  		
  		if (n.methodLink == null) { //there was an error so we need to return
  			return null;
  		}
  		else if (n.methodLink.formals.size() != n.parms.size()) {
  			//if(n.pos >= 0) {
  			errorMsg.error(n.pos, "Error: Number of parameters in call to '"+n.methName + "' (" +n.parms.size() + ") doesn't match number declared (" + n.methodLink.formals.size() + ")");
  			//}
  		}
  		else {
  			//check that each parameter matches the type in the method decl
  			for (int i = 0; i < n.methodLink.formals.size(); i++) {
  				matchTypesAssign(n.parms.elementAt(i).type, n.methodLink.formals.elementAt(i).type, n.pos);
  			}
  			
  			//set type
  	  		if (n.methodLink instanceof MethodDeclVoid) {
  	  			n.type = theVoidType;
  	  		}
  	  		else {
  	  			n.type = ((MethodDeclNonVoid)n.methodLink).rtnType;
  	  		}
  	  		
  		}
  		return null;
  	}
	
  	@Override
	public Object visitAssign(Assign n) {
		super.visitAssign(n);
		//check that lhs is an l-value
		if (!(n.lhs instanceof IdentifierExp || n.lhs instanceof ArrayLookup || n.lhs instanceof InstVarAccess)) {
			if (n.pos >= 0) {
				errorMsg.error(n.pos, "Error: Assignment target not modifiable");
			}
		}
		matchTypesAssign(n.rhs.type, n.lhs.type, n.pos); //check that r-value can be assigned to l-value

		return null;
	}
	
	@Override
	public Object visitLocalVarDecl(LocalVarDecl n) {
		super.visitLocalVarDecl(n);
		
		matchTypesAssign(n.initExp.type,n.type, n.pos);
		
		return null;
	}
	
	@Override
	public Object visitIf(If n) {
		super.visitIf(n);
		
		if(n.exp.type == null) {
			return null;
		}
		
		if (!matchTypesExact(n.exp.type,theBoolType, -1)) {
			if (n.pos >= 0) {
				errorMsg.error(n.pos, "Error: Condition must be boolean");
			}
		}
		
		return null;
	}
	
	@Override
	public Object visitWhile(While n) {
		super.visitWhile(n);
		
		if(n.exp.type == null) {
			return null;
		}
		
		if(!matchTypesExact(n.exp.type,theBoolType, -1)) {
			if (n.pos >= 0) {
				errorMsg.error(n.pos, "Error: Condition must be boolean");
			}
		}
		
		return null;
	}
	
	@Override
	public Object visitCase(Case n) {
		super.visitCase(n);
		
		if(n.exp.type == null) {
			return null;
		}
		
		if(!matchTypesExact(n.exp.type,theIntType, -1)) {
			if (n.pos >= 0) {
				errorMsg.error(n.pos, "Error: Case needs an int");
			}
		}
		
		return null;
	}
	
	@Override
	public Object visitMethodDeclVoid(MethodDeclVoid n) {
		super.visitMethodDeclVoid(n);
		
		 //if there isn't a superclass defn of the method it's not an error so put negative pos
		MethodDecl methodDecl = methodLookup(n.name, n.classDecl.superLink, -1, "");
		
		//System.out.println("Super class name lookin in is " + n.classDecl.superName);
		
		if (methodDecl != null) {
			//System.out.println("Found super class for " + methodDecl.name);

			//check: the superclass method is also a MethodDeclVoid
			if(!(methodDecl instanceof MethodDeclVoid)) {
				if(n.pos >= 0) {
					errorMsg.error(n.pos, "Error: Method's return type void doesn't match " + ((MethodDeclNonVoid)methodDecl).rtnType.toString() + " in superclass method");
				}
			}
			//check: the number and types of parameters for the two methods match exactly
			if (n.formals.size() != methodDecl.formals.size()) {
				if(n.pos >= 0) {
					errorMsg.error(n.pos, "Error: Method's parameter count " + n.formals.size() + " doesn't match " + methodDecl.formals.size() + " in super class method");
				}
			}
			else {
				//check that the types of the parameters match
				for (int i = 0; i < methodDecl.formals.size(); i++) {
					if (methodDecl.formals.elementAt(i).type == null || n.formals.elementAt(i).type == null) {
						return null;
					}
					
	  				if (!matchTypesExact(methodDecl.formals.elementAt(i).type, n.formals.elementAt(i).type, -1)) {
	  					if (n.pos >= 0) {
	  						errorMsg.error(n.pos, "Parameter type mismatch with superclass for " + methodDecl.formals.elementAt(i).name);
	  					}
	  				}
	  			}
			}
			//set our superMethod field to that of the superclass method declaration
			n.superMethod = methodDecl;
			
		}
		
		
		return null;
	}
	
	@Override
	public Object visitMethodDeclNonVoid(MethodDeclNonVoid n) {
		super.visitMethodDeclNonVoid(n);
		
		if (n.rtnExp.type == null || n.rtnExp ==  null) {
			return null;
		}
		
		if(!matchTypesAssign(n.rtnExp.type,n.rtnType,-1)) {
			if(n.pos >= 0) {
				errorMsg.error(n.rtnExp.pos, "Error: return type expected was " + n.rtnType.toString() + " but found was " + n.rtnExp.type);
			}
		}
		
		 //if there isn't a superclass defn of the method it's not an error so put negative pos
		MethodDecl methodDecl = methodLookup(n.name, n.classDecl.superLink, -1, "");
		
		if (methodDecl != null) {
			//check: the superclass method is also a MethodDeclVoid
			if(!(methodDecl instanceof MethodDeclNonVoid)) {
				if(n.pos >= 0) {
					errorMsg.error(n.pos, "Error: Method's return type" + n.rtnType.toString() + " doesn't match void in superclass method");
				}
			}
			//check: the number and types of parameters for the two methods match exactly
			else if (n.formals.size() != methodDecl.formals.size()) {
				if(n.pos >= 0) {
					errorMsg.error(n.pos, "Error: Method's parameter count " + n.formals.size() + " doesn't match " + methodDecl.formals.size() + " in super class method");
				}
			}
			else {
				//check that the types of the parameters match
				for (int i = 0; i < methodDecl.formals.size(); i++) {
					if (methodDecl.formals.elementAt(i).type == null || n.formals.elementAt(i).type == null) {
						return null;
					}
					
	  				if (!matchTypesExact(methodDecl.formals.elementAt(i).type, n.formals.elementAt(i).type, -1)) {
	  					if(n.pos >= 0) {
	  						errorMsg.error(n.pos, "Parameter type mismatch with super class for " + methodDecl.formals.elementAt(i).name);
	  					}
	  				}
	  			}
			}
			//set our superMethod field to that of the superclass method declaration
			n.superMethod = methodDecl;
			
		}
		
		
		return null;
	}
	
	@Override
	public Object visitClassDecl(ClassDecl n) {
		currentClass = n;
		//set currentClassType to refer to a new IdentifierType object that refers to this class (and set its link field to refer
		//back to this ClassDecl object)
		currentClassType = new IdentifierType(n.pos, n.name);
		currentClassType.link = n;
		
		/*
		 * set currentSuperclassType to refer to a new IdentifierType object that refers
		 * to the ClassDecl that is this class' superclass (and set its link field to
		 * refer back to the superclass' ClassDecl object)
		 */
		if (n.superLink != null) { //don't need to do following statements if there is no super class
			currentSuperclassType = new IdentifierType(n.superLink.pos, n.superName);
			currentSuperclassType.link = n.superLink;
		}

		super.visitClassDecl(n);
		return null;
	}
	
}

