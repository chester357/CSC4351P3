package Semant;

import java.util.ArrayList;

import Translate.Exp;
import Types.ARRAY;
import Types.NAME;
import Types.RECORD;
import Types.Type;

public class Semant {

	static final Types.VOID VOID = new Types.VOID();
	static final Types.INT INT = new Types.INT();
	static final Types.STRING STRING = new Types.STRING();
	static final Types.NIL NIL = new Types.NIL();

	Env env;

	public Semant(ErrorMsg.ErrorMsg err) {
		this(new Env(err));
	}

	Semant(Env e) {
		env = e;
	}

	// Expression Type Check -------------------------------------------------------
	// TODO: FieldExpList, FieldList, RecordExp,  
	
	ExpTy transExp(Absyn.Exp e) {
		ExpTy result;

		if (e == null)
			return new ExpTy(null, VOID);
		else if (e instanceof Absyn.OpExp)
			result = transExp((Absyn.OpExp) e);
		else if (e instanceof Absyn.LetExp)
			result = transExp((Absyn.LetExp) e);
		else if (e instanceof Absyn.IntExp)
			result = transExp((Absyn.IntExp) e);
		else if (e instanceof Absyn.StringExp)
			result = transExp((Absyn.StringExp) e);
		else if (e instanceof Absyn.IfExp)
			result = transExp((Absyn.IfExp) e);
		else if (e instanceof Absyn.ForExp)
			result = transExp((Absyn.ForExp) e);
		else if (e instanceof Absyn.SeqExp)
			result = transExp((Absyn.SeqExp) e);
		else if (e instanceof Absyn.WhileExp)
			result = transExp((Absyn.WhileExp) e);
		else if (e instanceof Absyn.BreakExp)
			result = transExp((Absyn.BreakExp) e);
		else if (e instanceof Absyn.AssignExp)
			result = transExp((Absyn.AssignExp) e);
		else if (e instanceof Absyn.ArrayExp)
			result = transExp((Absyn.ArrayExp) e);
		else if (e instanceof Absyn.VarExp)
			result = transExp((Absyn.VarExp) e);
		else if (e instanceof Absyn.NilExp)
			result = transExp((Absyn.NilExp) e);
		else
			throw new Error("Semant.transExp");
		e.type = result.ty;
		return result;
	}
	
	ExpTy transExp(Absyn.ForExp e)
	{
//		■ xx may not be the target of an assignment expression (inside www)
//		The scope of id is restricted to exp3.

//		■ xx is implicity declared to have type int
		ExpTy exp3;
		env.venv.beginScope();
		transDec(e.var);
		if (e.body instanceof Absyn.BreakExp){
			exp3 = Break();
		}
		else
			exp3 = transExp(e.body);
		env.venv.endScope();
		
		ExpTy exp1 = transExp(e.var.init);
		ExpTy exp2 = transExp(e.hi);
		
//		■ www must have type void
		if (!isVoid(exp3)) error(e.body.pos, "FOR ERROR: do must be void");
				
//		■ yy and zz must both have type int
		if (!isInt(exp1)) error(e.var.init.pos, "FOR ERROR: assignmen must be int");
		if (!isInt(exp2)) error(e.hi.pos, "FOR ERROR: max must be int");
		
//		■ result-type is void
		return new ExpTy(null, INT);	
	}

	ExpTy transExp(Absyn.IfExp e){
		
		ExpTy test = transExp(e.test);
		ExpTy then = transExp(e.thenclause);
		
		if (e.elseclause == null)
		{
			checkInt(test, e.test.pos);
			if (!isVoid(then)) error(e.thenclause.pos, "IF ERROR: then then return void");
			return new ExpTy(null, VOID);
		}
		else
		{
			ExpTy els = transExp(e.elseclause);
			checkInt(test, e.test.pos);
			if (then.ty != els.ty)
			{
				error(e.thenclause.pos, "IF ERROR: type mismatch");
				return new ExpTy(null, VOID);
			}
			else
				return new ExpTy(null, then.ty);
		}
	}
	
	ExpTy transExp(Absyn.OpExp e) {
		ExpTy left = transExp(e.left);
		ExpTy right = transExp(e.right);
		
		switch (e.oper) {
		case Absyn.OpExp.PLUS:
			checkInt(left, e.left.pos);
			checkInt(right, e.right.pos);
			return new ExpTy(null, INT);
		case Absyn.OpExp.MINUS:
			checkInt(left, e.left.pos);
			checkInt(right, e.right.pos);
			return new ExpTy(null, INT);
		case Absyn.OpExp.MUL:
			checkInt(left, e.left.pos);
			checkInt(right, e.right.pos);
			return new ExpTy(null, INT);
		case Absyn.OpExp.DIV:
			checkInt(left, e.left.pos);
			checkInt(right, e.right.pos);
			return new ExpTy(null, INT);
		case Absyn.OpExp.EQ:
			checkIfCompat(left, e.left.pos);
			checkIfCompat(right, e.right.pos);
			return new ExpTy(null, INT);
		case Absyn.OpExp.LT:
			checkIfCompat(left, e.left.pos);
			checkIfCompat(right, e.right.pos);
			return new ExpTy(null, INT);
		case Absyn.OpExp.LE:
			checkIfCompat(left, e.left.pos);
			checkIfCompat(right, e.right.pos);
			return new ExpTy(null, INT);
		case Absyn.OpExp.GT:
			checkIfCompat(left, e.left.pos);
			checkIfCompat(right, e.right.pos);
			return new ExpTy(null, INT);
		case Absyn.OpExp.GE:
			checkIfCompat(left, e.left.pos);
			checkIfCompat(right, e.right.pos);
			return new ExpTy(null, INT);
		case Absyn.OpExp.NE:
			checkIfCompat(left, e.left.pos);
			checkIfCompat(right, e.right.pos);
			return new ExpTy(null, INT);
		
		default:
			throw new Error("unknown operator");
		}
	}

	ExpTy transExp(Absyn.LetExp e) {
		env.venv.beginScope();
		env.tenv.beginScope();
		for (Absyn.DecList d = e.decs; d != null; d = d.tail) {
			transDec(d.head);
		}
		ExpTy body = transExp(e.body);
		env.venv.endScope();
		env.tenv.endScope();

		return new ExpTy(null, body.ty);
	}

	ExpTy transExp(Absyn.IntExp e){
		// Type Check ?
		
		return new ExpTy(null, INT);
	}
	
	ExpTy transExp(Absyn.SeqExp e){
		for(Absyn.ExpList d = e.list; d != null; d = d.tail){
			transExp(d.head);
		}
		return new ExpTy(null, VOID);
	}
	
	ExpTy transExp(Absyn.NilExp e){
		return new ExpTy(null, NIL); 
	}
	
	ExpTy transExp(Absyn.StringExp e){
		// Type Check ?
		
		return new ExpTy(null, STRING);
	}
	
	ExpTy transExp(Absyn.WhileExp e){


		ExpTy body;
		ExpTy test = transExp(e.test);
		if (e.body instanceof Absyn.BreakExp)
			body = Break();
		else 
			body = transExp(e.body);
		
//		while xxx do yyy
//		■ xxx must have type int
		if (!isInt(test)) error(e.test.pos, "WHILE ERROR: test exp must be int");
		
//		■ yyy must have type void
		if (!isVoid(body)) error(e.test.pos, "WHILE ERROR: body exp must be void");
		
//		■ result-type is void
		return new ExpTy(null, VOID);
	}

	ExpTy Break(){
		return new ExpTy(null, VOID);
	}
	
	ExpTy transExp(Absyn.AssignExp e){
		ExpTy exp = transExp(e.exp);
		ExpTy var = transVar(e.var);
		if (var.ty != exp.ty)
			error(e.pos, "ASSIGN ERROR: assignment types do not match");
		return new ExpTy(null, VOID);
	}
	
	ExpTy transExp(Absyn.ArrayExp e){
		NAME t = (NAME)env.tenv.get(e.typ);
		if(t != null){
			ExpTy size = transExp(e.size);
			ExpTy init = transExp(e.init);
			// Parser doesn't let this actually happen?
			if(!INT.coerceTo(size.ty)){ 
				error(e.pos, "Size parameter must be integer");
				return new ExpTy(null, VOID);
			}
			if(t.actual() instanceof ARRAY){
				ARRAY a = (ARRAY)t.actual(); 
				if(a.element.coerceTo(init.ty))
				return new ExpTy(null, t);
			}
		}
		error(e.pos, "Type not defined");
		return new ExpTy(null,VOID); 
	}
	
	ExpTy transExp(Absyn.VarExp e){
		ExpTy var = transVar(e.var);
		if(var == null){
			error(e.pos, "Variable not declared");
			return new ExpTy(null, INT); 
		}
		return new ExpTy(null, var.ty); 
	}
	
	// Declarations Type Check  ---------------------------------------------------
	// TODO FunctionDec 
	
	Exp transDec(Absyn.Dec d) {
		if (d instanceof Absyn.VarDec)
			return transDec((Absyn.VarDec) d);
		if (d instanceof Absyn.TypeDec)
			return transDec((Absyn.TypeDec) d);
		throw new Error("Semant.transDec");
	}

	Exp transDec(Absyn.VarDec d) {
		// NOTE: THIS IMPLEMENTATION IS INCOMPLETE
		// It is here to show you the general form of the transDec methods
		ExpTy init = transExp(d.init);
		Type type;
		
		if (d.typ == null) {
			type = init.ty;
		} 
		else {
			if(env.tenv.get(d.typ.name) == null){
				d.entry = new VarEntry(VOID);
				return null;
			}
			type = transTy(d.typ); 
		}
		d.entry = new VarEntry(type);
		env.venv.put(d.name, d.entry);
		return null;
	}
	
	Exp transDec(Absyn.TypeDec d){
		if(env.tenv.get(d.name) == null){
			d.entry = new NAME(d.name); 
			env.tenv.put(d.name, d.entry);
			d.entry.bind(transTy(d.ty));
			
			if(d.next != null){
				transDec(d.next);
			}
		}
		else
			error(d.pos, "Redeclared Type: "+d.name); 
		return null;
	}
	
	Exp transDec(Absyn.FunctionDec d){
		
//		aType must “match” the type of expr; if “:aType” is missing, then
//		expr must have a void type
		Type returnType = null;
		ExpTy body = transExp(d.body);
		
		if (d.result != null)
		{
			returnType = transTy(d.result);
			if (returnType.actual() != body.ty)
				error(d.result.pos, "FUNCTION DEC ERROR: return type not equal to body type");
		}
		else if(body.ty != VOID)
			error(d.pos, "FUNCTION DEC ERROR: body exp type must be void");
		
//		■ the formal parameter names (a and b, in this example) must be
//		unique within the parameter list.
		if (repeatedFields(d.params))
			error(d.pos, "FUNCTION DEC ERROR: field name repeated");
		
		// Not finished
		RECORD formals = transTypeFields(d.params);
		
		if (returnType != null){
			// add the function entry to the variable env
			env.venv.put(d.name, new FunEntry(formals, returnType));
		}
		else{
			// add the function entry to the variable env
			env.venv.put(d.name, new FunEntry(formals, VOID));
		}
		
		env.venv.beginScope();
		for(Absyn.FieldList p = d.params; p != null; p = p.tail){
			env.venv.put(p.name, new VarEntry((Type) env.tenv.get(p.typ)));
		}
		transExp(d.body);
		env.venv.endScope();
		
		return null;
	}
	
	RECORD transTypeFields(Absyn.FieldList f){
		// find a way to get field type (VOID is incorrect)
		if (f == null)
			return null;
		if (f.tail == null) 
			return null;
		return new RECORD(f.name, VOID, transTypeFields(f.tail));
	}
	
	// Variables, Subscripts, Fields Type Check ------------------------------------ 
	// TODO: Fields, FieldList, FieldExpList, 
	
	ExpTy transVar(Absyn.Var v){
		ExpTy result;
		
		if (v == null)
			return new ExpTy(null, VOID);
		if (v instanceof Absyn.SimpleVar)
			result = transVar((Absyn.SimpleVar) v);
		else if (v instanceof Absyn.FieldVar)
			result = transVar((Absyn.FieldVar) v);
		else if (v instanceof Absyn.SubscriptVar)
			result = transVar((Absyn.SubscriptVar) v);
		else 
			throw new Error("Semant.transVar");
		
		return result; 
	}
	
	ExpTy transVar(Absyn.SimpleVar v)
	{
		Entry x = (Entry) env.venv.get(v.name);
		if (x instanceof VarEntry){
			VarEntry ent = (VarEntry) x;
			return new ExpTy(null, ent.ty);
		}
		else{
			error(v.pos, "SIMPLE VAR ERROR: variable is undifined");
			return new ExpTy(null, VOID);
		}
	}
	
	ExpTy transVar(Absyn.FieldVar v)
	{
		// v.field might not be correct
		Entry x = (Entry) env.venv.get(v.field);
		if (x instanceof VarEntry){
			VarEntry ent = (VarEntry) x;
			return new ExpTy(null, ent.ty);
		}
		else{
			error(v.pos, "FIELD VAR ERROR: variable is undifined");
			return new ExpTy(null, VOID);
		}
	}
	
	ExpTy transVar(Absyn.SubscriptVar v){
		ExpTy index = transExp(v.index); 
		ExpTy var = transVar(v.var);
		
		if(!INT.coerceTo(index.ty))
			error(v.pos, "Index must be int.");
		if(var.ty.actual() instanceof ARRAY){
			ARRAY arr = (ARRAY)var.ty.actual(); 
			return new ExpTy(null, arr.element); 
		}
		error(v.pos, v.var + " ");
		return new ExpTy(null, VOID); 
	}
	
	// Types Type Check --------------------------------------------------------------
	// TODO:RecordTy
	
	Type transTy(Absyn.Ty t){
		if (t instanceof Absyn.NameTy)
			return transTy((Absyn.NameTy) t);
		if (t instanceof Absyn.ArrayTy)
			return transTy((Absyn.ArrayTy) t);
		if (t instanceof Absyn.RecordTy)
			return transTy((Absyn.RecordTy) t);
		throw new Error("Semant.transTy");
	}
	
	Type transTy(Absyn.NameTy t){
		NAME n = (NAME)env.tenv.get(t.name); 
		if(n != null)
			return n; 
		error(t.pos, "Not defined"); 
		return VOID;
	}
	
	Type transTy(Absyn.ArrayTy t){
		NAME n = (NAME)env.tenv.get(t.typ);
		if(n != null)
			return new ARRAY(n);
		error(t.pos, "Type:"+t.typ+" is not defined!");
		return VOID;
	}
	
	
	// Helpers ----------------------------------------------------------------------
	
	public void transProg(Absyn.Exp exp) {
		transExp(exp);
	}
	
	private boolean repeatedFields(Absyn.FieldList fl){
		boolean repeatedField = false;
		ArrayList<String> fieldNames = new ArrayList<String>();
		
		for (Absyn.FieldList f = fl; f != null; f = f.tail){
			
			fieldNames.add(f.name.toString());
			
			for (int i = 0; i < fieldNames.size() - 1; i++){
				if (fieldNames.get(i) == f.name.toString())
					repeatedField = true;
			}
		}
		
		if (repeatedField)
			return true;
		else
			return false;
	}
	
	private void error(int pos, String msg) {
		env.errorMsg.error(pos, msg);
	}

	private Exp checkInt(ExpTy et, int pos) {
		if (!INT.coerceTo(et.ty))
			error(pos, "integer required");
		return et.exp;
	}
	
	private boolean isVoid(ExpTy et) {
		if (!VOID.coerceTo(et.ty))
			return false;
		return true;
	}
	
	private boolean isInt(ExpTy et) {
		if (!INT.coerceTo(et.ty))
			return false;
		return true;
	}
	
	private Exp checkIfCompat(ExpTy et, int pos){
		if (!INT.coerceTo(et.ty))
			error(pos, "incompatible types for comparison");
		return et.exp;
	}

}

