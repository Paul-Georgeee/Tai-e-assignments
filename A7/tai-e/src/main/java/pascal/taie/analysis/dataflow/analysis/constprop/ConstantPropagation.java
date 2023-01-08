/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact fact = new CPFact();
        var parameters = cfg.getIR().getParams();
        for(Var parameter: parameters)
            if(canHoldInt(parameter))
                fact.update(parameter, Value.getNAC());

        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for(Var var: fact.keySet())
            target.update(var, meetValue(target.get(var), fact.get(var)));
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if(v1.isNAC() || v2.isNAC())
            return Value.getNAC();
        else if (v1.isUndef())
            return v2;
        else if (v2.isUndef())
            return v1;
        else{
            if(v1.getConstant() == v2.getConstant())
                return v1;
            else
                return Value.getNAC();
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        var temp = in.copy();
        if(stmt instanceof DefinitionStmt<?,?>)
        {
            var leftval = ((DefinitionStmt<?, ?>) stmt).getLValue();
            if(leftval instanceof Var && canHoldInt((Var) leftval))
            {
                var exp = ((DefinitionStmt<?, ?>) stmt).getRValue();
                if(exp != null) {
                    var value = evaluate(((DefinitionStmt<?, ?>) stmt).getRValue(), in);
                    temp.update((Var) leftval, value);
                }
            }
        }
        return out.copyFrom(temp);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        if (exp instanceof Var) {
            return in.get((Var) exp);
        }
        else if (exp instanceof IntLiteral) {
            return Value.makeConstant(((IntLiteral) exp).getValue());
        }
        else if (exp instanceof BinaryExp){
            var operand1 = ((BinaryExp) exp).getOperand1();
            var operand2 = ((BinaryExp) exp).getOperand2();
            var value1 = in.get(operand1);
            var value2 = in.get(operand2);

            if(exp instanceof ArithmeticExp && value2.isConstant())
            {
                var op = ((ArithmeticExp) exp).getOperator();
                if((op == ArithmeticExp.Op.REM || op == ArithmeticExp.Op.DIV) && value2.getConstant() == 0)
                    return Value.getUndef();
            }

            if(value1.isNAC() || value2.isNAC())
                return Value.getNAC();
            else if(value1.isConstant() && value2.isConstant()) {
                var constant1 = value1.getConstant();
                var constant2 = value2.getConstant();
                if (exp instanceof ArithmeticExp) {
                    var op = ((ArithmeticExp) exp).getOperator();

                    return switch (op) {
                        case ADD -> Value.makeConstant(constant1 + constant2);
                        case MUL -> Value.makeConstant(constant1 * constant2);
                        case SUB -> Value.makeConstant(constant1 - constant2);
                        case DIV -> Value.makeConstant(constant1 / constant2);
                        case REM -> Value.makeConstant(constant1 % constant2);
                    };
                } else if(exp instanceof BitwiseExp){
                    var op = ((BitwiseExp) exp).getOperator();

                    return switch (op) {
                        case OR -> Value.makeConstant(constant1 | constant2);
                        case AND -> Value.makeConstant(constant1 & constant2);
                        case XOR -> Value.makeConstant(constant1 ^ constant2);
                    };
                } else if (exp instanceof ConditionExp) {
                    var op = ((ConditionExp) exp).getOperator();
                    int ret = switch (op) {
                        case EQ -> constant1 == constant2 ? 1 : 0;
                        case GE -> constant1 >= constant2 ? 1 : 0;
                        case GT -> constant1 > constant2 ? 1 : 0;
                        case LE -> constant1 <= constant2 ? 1 : 0;
                        case LT -> constant1 < constant2 ? 1 : 0;
                        case NE -> constant1 != constant2 ? 1 : 0;
                    };
                    return Value.makeConstant(ret);
                } else if (exp instanceof ShiftExp) {
                    var op = ((ShiftExp) exp).getOperator();
                    return switch (op) {
                        case SHL -> Value.makeConstant(constant1 << constant2);
                        case SHR -> Value.makeConstant(constant1 >> constant2);
                        case USHR -> Value.makeConstant(constant1 >>> constant2);
                    };
                }

            }
            else return Value.getUndef();
        }
        return Value.getNAC();
    }
}
