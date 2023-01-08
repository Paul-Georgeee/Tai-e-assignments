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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;

import java.util.HashMap;
import java.util.HashSet;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private HashMap<FieldAccess, HashSet<StoreField>> aliasFieldMap = new HashMap<>();
    public HashMap<FieldAccess, HashSet<LoadField>>  updateListField = new HashMap<>();
    private HashMap<ArrayAccess, HashSet<StoreArray>> aliasArrayMap = new HashMap<>();
    public HashMap<ArrayAccess, HashSet<LoadArray>>  updateListArray = new HashMap<>();

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    private HashSet<StoreField> findFieldAlias(Var base, JField field, PointerAnalysisResult pta, LoadField loadField)
    {
        HashSet<StoreField> set = new HashSet<>();
        for(var stmt: icfg)
        {
            if(stmt instanceof StoreField && !((StoreField) stmt).isStatic())
            {
                var fieldAccess = ((StoreField) stmt).getFieldAccess();
                var storeBase = ((InstanceFieldAccess)fieldAccess).getBase();
                var storeField = fieldAccess.getFieldRef().resolve();

                if(storeField == field) {
                    var loadSet = pta.getPointsToSet(base);
                    var storeSet = pta.getPointsToSet(storeBase);
                    for (var obj : loadSet)
                        if (storeSet.contains(obj)) {
                            set.add((StoreField) stmt);
                            var updateList = this.updateListField.get(fieldAccess);
                            if(updateList == null)
                            {
                                HashSet<LoadField> s = new HashSet<>();
                                s.add(loadField);
                                this.updateListField.put(fieldAccess, s);
                            }
                            else
                                updateList.add(loadField);
                            break;
                        }
                }
            }
        }
        return set;
    }

    private HashSet<StoreField> findFieldAliasStatic(JField field, PointerAnalysisResult pta, LoadField loadField)
    {
        HashSet<StoreField> set = new HashSet<>();
        for(var stmt: icfg)
        {
            if(stmt instanceof StoreField && ((StoreField) stmt).isStatic()) {
                var storeField = ((StoreField) stmt).getFieldRef().resolve();
                var fieldAccess = ((StoreField) stmt).getFieldAccess();
                if (storeField == field) {
                    set.add((StoreField) stmt);
                    var updateList = this.updateListField.get(fieldAccess);
                    if(updateList == null)
                    {
                        HashSet<LoadField> s = new HashSet<>();
                        s.add(loadField);
                        this.updateListField.put(fieldAccess, s);
                    }
                    else
                        updateList.add(loadField);
                }
            }
        }
        return set;
    }

    private HashSet<StoreArray> findArrayAlias(Var base, PointerAnalysisResult pta, LoadArray loadArray)
    {
        HashSet<StoreArray> set = new HashSet<>();
        for(var stmt: icfg)
        {
            if(stmt instanceof StoreArray)
            {
                var storeBase = ((StoreArray) stmt).getArrayAccess().getBase();
                var arrayAccess = ((StoreArray) stmt).getArrayAccess();
                var loadSet = pta.getPointsToSet(base);
                var storeSet = pta.getPointsToSet(storeBase);
                for(var obj:loadSet)
                    if(storeSet.contains(obj)){
                        set.add((StoreArray) stmt);
                        var updateList = this.updateListArray.get(arrayAccess);
                        if(updateList == null)
                        {
                            HashSet<LoadArray> s = new HashSet<>();
                            s.add(loadArray);
                            this.updateListArray.put(arrayAccess, s);
                        }
                        else
                            updateList.add(loadArray);
                        break;
                    }
            }
        }
        return set;
    }
    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);

        // You can do initialization work here
        for(var stmt: icfg)
        {
            if(stmt instanceof LoadField)
            {
                var fieldAccess = ((LoadField) stmt).getFieldAccess();
                var jField = fieldAccess.getFieldRef().resolve();
                if(!this.aliasFieldMap.containsKey(fieldAccess))
                {
                    if(((LoadField) stmt).isStatic())
                        this.aliasFieldMap.put(fieldAccess, this.findFieldAliasStatic(jField, pta, (LoadField) stmt));
                    else
                        this.aliasFieldMap.put(fieldAccess, this.findFieldAlias(((InstanceFieldAccess)fieldAccess).getBase(), jField, pta, (LoadField) stmt));

                }
            }
            else if(stmt instanceof LoadArray)
            {
                var arrayAccess = ((LoadArray) stmt).getArrayAccess();
                if(!this.aliasArrayMap.containsKey(arrayAccess))
                    this.aliasArrayMap.put(arrayAccess, this.findArrayAlias(arrayAccess.getBase(), pta, (LoadArray) stmt));
            }
        }
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        return out.copyFrom(in);
    }

    private boolean isAliasArray(Var index1, Var index2, CPFact in1, CPFact in2)
    {
        Value v1 = in1.get(index1), v2 = in2.get(index2);
        if(v1.isUndef() || v2.isUndef())
            return false;
        else if(v1.isNAC() || v2.isNAC())
            return true;
        else if(v1.getConstant() == v2.getConstant())
            return true;
        else
            return false;
    }

    private boolean transferLoadArray(LoadArray stmt, CPFact in, CPFact out)
    {
        var lValue =  stmt.getLValue();
        if(!ConstantPropagation.canHoldInt(lValue))
            return out.copyFrom(in);
        var tmp = in.copy();
        var arrayAccess = stmt.getArrayAccess();
        var storeArraySet = this.aliasArrayMap.get(arrayAccess);
        var value = Value.getUndef();
        for(var store: storeArraySet)
        {
            var storeIndex = store.getArrayAccess().getIndex();
            var rValue = store.getRValue();
            var storeIn = solver.result.getInFact(store);
            if(ConstantPropagation.canHoldInt(rValue) && this.isAliasArray(arrayAccess.getIndex(), storeIndex, in, storeIn))
                value = cp.meetValue(value, ConstantPropagation.evaluate(rValue, storeIn));
        }
        tmp.update(lValue, value);
        return out.copyFrom(tmp);
    }

    private boolean transferLoadField(LoadField stmt, CPFact in, CPFact out)
    {
        var lValue = stmt.getLValue();
        if(!ConstantPropagation.canHoldInt(lValue))
            return out.copyFrom(in);
        var tmp = in.copy();
        var fieldAccess = stmt.getFieldAccess();
        var storeFieldSet = this.aliasFieldMap.get(fieldAccess);
        var value = Value.getUndef();
        for(var store: storeFieldSet)
        {
            var rValue = store.getRValue();
            var storeIn = solver.result.getInFact(store);
            if(ConstantPropagation.canHoldInt(rValue))
                value = cp.meetValue(value, ConstantPropagation.evaluate(rValue, storeIn));
        }
        tmp.update(lValue, value);
        return out.copyFrom(tmp);
    }
    private boolean transferStoreField(StoreField stmt, CPFact in, CPFact out)
    {
        boolean update = out.copyFrom(in);
        if(update)
        {
            var updateList = this.updateListField.get(stmt.getFieldAccess());
            if(updateList != null)
                for(var loadField: updateList)
                    if(!solver.workList.contains(loadField))
                        solver.workList.add(loadField);

        }
        return update;
    }

    private boolean transferStoreArray(StoreArray stmt, CPFact in, CPFact out)
    {
        boolean update = out.copyFrom(in);
        if(update)
        {
            var updateList = this.updateListArray.get(stmt.getArrayAccess());
            if(updateList != null)
                for(var loadArray: updateList)
                    if(!solver.workList.contains(loadArray))
                        solver.workList.add(loadArray);
        }
        return update;
    }
    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        if(stmt instanceof LoadArray)
            return transferLoadArray((LoadArray) stmt, in, out);
        else if(stmt instanceof LoadField)
            return transferLoadField((LoadField) stmt, in, out);
        else if(stmt instanceof StoreField)
            return transferStoreField((StoreField) stmt, in, out);
        else if(stmt instanceof StoreArray)
            return transferStoreArray((StoreArray) stmt, in, out);
        else
            return cp.transferNode(stmt, in, out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        assert edge.getSource() instanceof Invoke;
        var ret = out.copy();
        Invoke invoke =(Invoke) edge.getSource();
        Var lhs = invoke.getResult();
        if(lhs != null)
            ret.update(lhs, Value.getUndef());
        return ret;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        assert edge.getSource() instanceof Invoke;
        CPFact ret = new CPFact();
        InvokeExp invokeExp = ((Invoke) edge.getSource()).getInvokeExp();
        var formalArgs = edge.getCallee().getIR().getParams();
        var practiceArgs = invokeExp.getArgs();
        for(int i = 0; i < formalArgs.size(); ++i){
            Var formalArg = formalArgs.get(i), practiceArg = practiceArgs.get(i);
            if(ConstantPropagation.canHoldInt(formalArg))
                ret.update(formalArg, callSiteOut.get(practiceArg));
        }
        return ret;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        var retFact = new CPFact();
        var returnVar = edge.getReturnVars();
        var callSite = edge.getCallSite();
        assert callSite instanceof Invoke;
        var lhs = ((Invoke) callSite).getResult();

        if(lhs != null)
        {
            for(var v: returnVar) {
                var oldValue = retFact.get(lhs);
                var newValue = returnOut.get(v);
                retFact.update(lhs, cp.meetValue(oldValue, newValue));
            }
        }
        return retFact;
    }
}
