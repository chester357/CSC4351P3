package Semant;

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
	// TODO: ArrayExp, AssignExp, BreakExp, CallExp, ExpList, FieldExpList, FieldList, WhileExp, 
	// ForExp, IfExp, LetExp, NilExp, RecordExp, SeqExp, VarExp, Exp
	// DONE: IntExp, StringExp, OpExp,
	
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
		else
			throw new Error("Semant.transExp");
		e.type = result.ty;
		return result;
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
	
	private Exp checkIfCompat(ExpTy et, int pos){
		if (!INT.coerceTo(et.ty))
			error(pos, "incompatible types for comparison");
		
		return et.exp;
	}

}

