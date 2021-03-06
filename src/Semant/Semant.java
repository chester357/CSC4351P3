package Semant;

import com.sun.java_cup.internal.runtime.Symbol;

import Absyn.NameTy;
import Absyn.SimpleVar;
import Absyn.VarDec;
import Translate.Exp;
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
	// TODO: ArrayExp, CallExp, ExpList, FieldExpList, FieldList, RecordExp, VarExp
	// DONE: IntExp, StringExp, OpExp, ForExp, NilExp, WhileExp, SeqExp, BreakExp, AssignExp,
	// LetExp, 
	
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
		else if (e instanceof Absyn.NilExp)
			result = transExp((Absyn.NilExp) e);
		else if (e instanceof Absyn.VarExp)
			result = transExp((Absyn.VarExp) e);
		else if (e instanceof Absyn.WhileExp)
			result = transExp((Absyn.WhileExp) e);
		else if (e instanceof Absyn.SeqExp)
			result = transExp((Absyn.SeqExp) e);
		else if (e instanceof Absyn.BreakExp)
			result = transExp((Absyn.BreakExp) e);
		else if (e instanceof Absyn.AssignExp)
			result = transExp((Absyn.AssignExp) e);
		else
			throw new Error("Semant.transExp");
		e.type = result.ty;
		return result;
	}
	
	ExpTy transExp(Absyn.AssignExp e){
		ExpTy exp = transExp(e.exp);
		ExpTy var = transVar(e.var);
		if (var.ty != exp.ty)
			error(e.pos, "ASSIGN ERROR: assignment types do not match");
		return new ExpTy(null, VOID);
	}
	
	ExpTy transExp(Absyn.BreakExp e){
		error(e.pos, "BREAK ERROR: break called outside a loop");
		return new ExpTy(null, VOID);
	}
	
	ExpTy Break(){
		return new ExpTy(null, VOID);
	}
	
	ExpTy transExp(Absyn.SeqExp e){
		for(Absyn.ExpList d = e.list; d != null; d = d.tail){
			if (d.head instanceof Absyn.BreakExp)
				Break();
			else
				transExp(d.head);
		}
		return new ExpTy(null, VOID);
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
	
	ExpTy transExp(Absyn.VarExp e){
		
		ExpTy var = transVar(e.var);
		
		if (var == null)
			return new ExpTy(null, INT);
		else
			return new ExpTy(null, var.ty);
	}
	
	ExpTy transExp(Absyn.NilExp e){
		return new ExpTy(null, NIL);
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
	
	ExpTy transExp(Absyn.StringExp e){
		// Type Check ?
		
		return new ExpTy(null, STRING);
	}
	
	// Declarations Type Check  ---------------------------------------------------
	// TODO: Dec, DecList, FunctionDec, TypeDec, VarDec
	
	Exp transDec(Absyn.Dec d) {
		if (d instanceof Absyn.VarDec)
			return transDec((Absyn.VarDec) d);
		throw new Error("Semant.transDec");
	}

	Exp transDec(Absyn.VarDec d) {
		// NOTE: THIS IMPLEMENTATION IS INCOMPLETE
		// It is here to show you the general form of the transDec methods
		ExpTy init = transExp(d.init);
		Type type;
		if (d.typ == null) {
			type = init.ty;
		} else {
			type = VOID;
			throw new Error("unimplemented");
		}
		d.entry = new VarEntry(type);
		env.venv.put(d.name, d.entry);
		return null;
	}
	
	// Variables, Subscripts, Fields Type Check ------------------------------------ 
	// TODO: FieldVar, SimpleVar, SubstriptVar, Var
	
	ExpTy transVar(Absyn.Var v){
		ExpTy result;
		
		if (v == null)
			return new ExpTy(null, VOID);
		if (v instanceof Absyn.SimpleVar)
			result = transVar((Absyn.SimpleVar) v);
		else if (v instanceof Absyn.FieldVar)
			result = transVar((Absyn.FieldVar) v);
		// SubscriptVar
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
	
//	ExpTy transVar(Absyn.SubscriptVar v)
//	{
//		Entry x = (Entry) env.venv.get();
//		if (x instanceof VarEntry){
//			VarEntry ent = (VarEntry) x;
//			return new ExpTy(null, ent.ty);
//		}
//		else{
//			error(v.pos, "SIMPLE VAR ERROR: variable is undifined");
//			return new ExpTy(null, INT);
//		}
//	}
	
	// Types Type Check --------------------------------------------------------------
	// TODO: ArrayTy, NameTy, RecordTy, Ty, 
	
	
	// Helpers ----------------------------------------------------------------------
	
	public void transProg(Absyn.Exp exp) {
		transExp(exp);
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

