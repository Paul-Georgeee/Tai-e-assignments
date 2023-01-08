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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;


    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
        if(!callGraph.contains((csMethod)))
        {
            callGraph.addReachableMethod((csMethod));
            for(var stmt: csMethod.getMethod().getIR().getStmts())
                stmt.accept(stmtProcessor);
        }

    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me


        @Override
        public Void visit(New stmt) {
            var newObj = heapModel.getObj(stmt);
            var heapContext = contextSelector.selectHeapContext(csMethod, newObj);
            workList.addEntry(csManager.getCSVar(this.context, stmt.getLValue()), PointsToSetFactory.make(csManager.getCSObj(heapContext, newObj)));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            addPFGEdge(csManager.getCSVar(this.context, stmt.getRValue()), csManager.getCSVar(this.context, stmt.getLValue()));
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if(stmt.isStatic())
            {
                var jField = stmt.getFieldRef().resolve();
                var staticField = csManager.getStaticField(jField);
                var csVarPtr = csManager.getCSVar(this.context, stmt.getLValue());
                addPFGEdge(staticField, csVarPtr);
            }
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(StoreField stmt) {
            if(stmt.isStatic())
            {
                var jField = stmt.getFieldRef().resolve();
                var staticField = csManager.getStaticField(jField);
                var csVarPtr = csManager.getCSVar(this.context, stmt.getRValue());
                addPFGEdge(csVarPtr, staticField);
            }
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Invoke stmt) {
            if(stmt.isStatic())
            {
                var jMethod = resolveCallee(null, stmt);
                var csCallSite = csManager.getCSCallSite(this.context, stmt);
                var context = contextSelector.selectContext(csCallSite, jMethod);
                if(callGraph.addEdge(new Edge<>(getCallKind(stmt), csCallSite, csManager.getCSMethod(context, jMethod))))
                    handleFuncArgsReturn(this.context, stmt, context, jMethod);
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
            if(pointer instanceof CSVar)
            {
                for(var obj: diffSet)
                {
                    var variable = ((CSVar) pointer).getVar();
                    var context = ((CSVar) pointer).getContext();
                    for(var stmt: variable.getStoreFields())
                    {
                        var jField = stmt.getFieldRef().resolve();
                        var rValue = stmt.getRValue();
                        addPFGEdge(csManager.getCSVar(context, rValue), csManager.getInstanceField(obj, jField));
                    }

                    for(var stmt: variable.getLoadFields())
                    {
                        var jField = stmt.getFieldRef().resolve();
                        var lValue = stmt.getLValue();
                        addPFGEdge(csManager.getInstanceField(obj, jField), csManager.getCSVar(context, lValue));
                    }

                    for(var stmt: variable.getStoreArrays())
                    {
                        var rValue = stmt.getRValue();
                        addPFGEdge(csManager.getCSVar(context, rValue), csManager.getArrayIndex(obj));
                    }

                    for(var stmt: variable.getLoadArrays())
                    {
                        var lValue = stmt.getLValue();
                        addPFGEdge(csManager.getArrayIndex(obj), csManager.getCSVar(context, lValue));
                    }

                    processCall((CSVar) pointer, obj);
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
        var diffSet = PointsToSetFactory.make();
        var pSet = pointer.getPointsToSet();
        for(var obj: pointsToSet) {
            if(!pSet.contains(obj)) {
                diffSet.addObject(obj);
                pSet.addObject(obj);
            }
        }
        if(!diffSet.isEmpty()){
            for(var p: pointerFlowGraph.getSuccsOf(pointer)){
                workList.addEntry(p, diffSet);
            }
        }
        return diffSet;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        var variable = recv.getVar();
        var callerContext = recv.getContext();
        for(var stmt: variable.getInvokes())
        {
            var jMethod = resolveCallee(recvObj, stmt);
            var ir = jMethod.getIR();
            var thisVar = ir.getThis();
            var csCallSite = csManager.getCSCallSite(callerContext, stmt);
            var calleeContext = contextSelector.selectContext(csCallSite, recvObj, jMethod);
            if(thisVar != null)
            {
                workList.addEntry(csManager.getCSVar(calleeContext, thisVar), PointsToSetFactory.make(recvObj));
                if(callGraph.addEdge(new Edge<>(getCallKind(stmt), csCallSite, csManager.getCSMethod(calleeContext, jMethod))))
                    handleFuncArgsReturn(callerContext, stmt, calleeContext, jMethod);
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
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

    private void handleFuncArgsReturn(Context callerContext, Invoke stmt, Context calleeContext, JMethod jMethod)
    {
        addReachable(csManager.getCSMethod(calleeContext, jMethod));
        var formalArgs =  jMethod.getIR().getParams();
        var invokeExp = stmt.getInvokeExp();
        var practicalArgs = invokeExp.getArgs();
        assert formalArgs.size() == practicalArgs.size();
        for(int i = 0; i < formalArgs.size(); ++i)
        {
            var formalArg = formalArgs.get(i);
            var practicalArg = practicalArgs.get(i);
            addPFGEdge(csManager.getCSVar(callerContext, practicalArg), csManager.getCSVar(calleeContext, formalArg));
        }
        var lValue = stmt.getLValue();
        if(lValue != null)
            for(var returnVal: jMethod.getIR().getReturnVars())
                addPFGEdge(csManager.getCSVar(calleeContext, returnVal), csManager.getCSVar(callerContext, lValue));
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
