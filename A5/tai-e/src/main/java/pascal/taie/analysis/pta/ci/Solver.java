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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if(!callGraph.contains(method))
        {
            callGraph.addReachableMethod(method);
            for(var stmt: method.getIR().getStmts())
                stmt.accept(stmtProcessor);
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(New stmt){
            workList.addEntry(pointerFlowGraph.getVarPtr(stmt.getLValue()), new PointsToSet(heapModel.getObj(stmt)));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()), pointerFlowGraph.getVarPtr(stmt.getLValue()));
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if(stmt.isStatic())
            {
                var jField = stmt.getFieldRef().resolve();
                var staticField = pointerFlowGraph.getStaticField(jField);
                var varPtr = pointerFlowGraph.getVarPtr(stmt.getLValue());
                addPFGEdge(staticField, varPtr);
            }
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(StoreField stmt) {
            if(stmt.isStatic())
            {
                var jField = stmt.getFieldRef().resolve();
                var staticField = pointerFlowGraph.getStaticField(jField);
                var varPtr = pointerFlowGraph.getVarPtr(stmt.getRValue());
                addPFGEdge(varPtr, staticField);
            }
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Invoke stmt) {
            if(stmt.isStatic())
            {
                var jMethod = resolveCallee(null, stmt);
                if(callGraph.addEdge(new Edge<>(getCallKind(stmt), stmt, jMethod)))
                    handleFuncArgsReturn(jMethod, stmt);
            }
            return StmtVisitor.super.visit(stmt);
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if(pointerFlowGraph.addEdge(source, target))
        {
            var pointSet = source.getPointsToSet();
            if(!pointSet.isEmpty())
                workList.addEntry(target, pointSet);
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty())
        {
            var entry = workList.pollEntry();
            var pointer = entry.pointer();
            var diffSet = propagate(pointer, entry.pointsToSet());
            if(pointer instanceof VarPtr)
            {
                for(var obj: diffSet)
                {
                    var variable = ((VarPtr) pointer).getVar();
                    for(var stmt: variable.getStoreFields())
                    {
                        var jFiled = stmt.getFieldRef().resolve();
                        var rValue = stmt.getRValue();
                        addPFGEdge(pointerFlowGraph.getVarPtr(rValue), pointerFlowGraph.getInstanceField(obj, jFiled));
                    }

                    for(var stmt: variable.getLoadFields())
                    {
                        var jFiled = stmt.getFieldRef().resolve();
                        var lValue = stmt.getLValue();
                        addPFGEdge(pointerFlowGraph.getInstanceField(obj, jFiled), pointerFlowGraph.getVarPtr(lValue));
                    }

                    for(var stmt: variable.getStoreArrays())
                    {
                        var rValue = stmt.getRValue();
                        addPFGEdge(pointerFlowGraph.getVarPtr(rValue), pointerFlowGraph.getArrayIndex(obj));
                    }

                    for(var stmt: variable.getLoadArrays())
                    {
                        var lValue = stmt.getLValue();
                        addPFGEdge(pointerFlowGraph.getArrayIndex(obj), pointerFlowGraph.getVarPtr(lValue));
                    }

                    processCall(variable, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        var diffSet = new PointsToSet();
        var pSet = pointer.getPointsToSet();
        for(var obj: pointsToSet) {
            if (!pSet.contains(obj)) {
                diffSet.addObject(obj);
                pSet.addObject(obj);
            }
        }
        if(!diffSet.isEmpty()) {
            for (var p : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(p, diffSet);
            }
        }
        return diffSet;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        for(var stmt: var.getInvokes())
        {
            var jMethod = resolveCallee(recv, stmt);
            var ir = jMethod.getIR();
            var thisVar = ir.getThis();
            if(thisVar != null)
            {
                workList.addEntry(pointerFlowGraph.getVarPtr(thisVar), new PointsToSet(recv));
                if(callGraph.addEdge(new Edge<>(getCallKind(stmt), stmt, jMethod)))
                    handleFuncArgsReturn(jMethod, stmt);
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }

    private CallKind getCallKind(Invoke callSite)
    {
        if(callSite.isStatic())
            return CallKind.STATIC;
        else if(callSite.isSpecial())
            return CallKind.SPECIAL;
        else if(callSite.isVirtual())
            return CallKind.VIRTUAL;
        else if(callSite.isInterface())
            return CallKind.INTERFACE;
        else
            assert false;
        return null;
    }

    private void handleFuncArgsReturn(JMethod jMethod, Invoke stmt)
    {
        addReachable(jMethod);
        var formalArgs =  jMethod.getIR().getParams();
        var invokeExp = stmt.getInvokeExp();
        var practicalArgs = invokeExp.getArgs();
        assert formalArgs.size() == practicalArgs.size();
        for(int i = 0; i < formalArgs.size(); ++i)
        {
            var formalArg = formalArgs.get(i);
            var practicalArg = practicalArgs.get(i);
            addPFGEdge(pointerFlowGraph.getVarPtr(practicalArg), pointerFlowGraph.getVarPtr(formalArg));
        }
        var lValue = stmt.getLValue();
        if(lValue != null)
            for(var returnVar: jMethod.getIR().getReturnVars())
                addPFGEdge(pointerFlowGraph.getVarPtr(returnVar), pointerFlowGraph.getVarPtr(lValue));
    }
}
