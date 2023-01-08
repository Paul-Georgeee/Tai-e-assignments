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

package pascal.taie.analysis.pta.plugin.taint;

import fj.test.Bool;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.heap.MockObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;

import pascal.taie.language.type.Type;

import java.util.*;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    public final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public HashSet<SinkSite> sinkSiteSet = new HashSet<>();


    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    // TODO - finish me

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.
        HashMap<CSVar, Set<CSObj>> taint = new HashMap<>();
        for(var csVar: result.getCSVars())
        {
            var s = new HashSet<CSObj>();
            for(var obj: result.getPointsToSet(csVar))
                if(manager.isTaint(obj.getObject()))
                    s.add(obj);
            if(!s.isEmpty())
            {
                var res = taint.get(csVar);
                if(res == null)
                    taint.put(csVar, s);
                else
                    res.addAll(s);
            }
        }

        for(var sinkSite: sinkSiteSet)
        {
            var arg = sinkSite.csCallSite().getCallSite().getRValue().getArg(sinkSite.index());
            var res = taint.get(csManager.getCSVar(sinkSite.csCallSite().getContext(), arg));
            if(res != null)
            {
                for(var obj: res)
                {
                    var sourceCall = obj.getObject().getAllocation();
                    taintFlows.add(new TaintFlow((Invoke) sourceCall, sinkSite.csCallSite().getCallSite(), sinkSite.index()));
                }
            }
        }


        return taintFlows;
    }

    public CSObj getTaintObj(JMethod method, Invoke invoke)
    {
        var sourceSet = config.getSources();
        if(sourceSet.contains(new Source(method, method.getReturnType())))
            return csManager.getCSObj(emptyContext, manager.makeTaint(invoke, method.getReturnType()));
        else
            return null;
    }

    public CSObj makeTaintTransferObj(Obj obj, Var toVar)
    {
        return csManager.getCSObj(emptyContext, manager.makeTaint(manager.getSourceCall(obj), toVar.getType()));
    }
    public Boolean isTaintObj(Obj obj)
    {
        return manager.isTaint(obj);
    }
    public Boolean detectBase2Result(JMethod method, Type type)
    {
        var transferSet = config.getTransfers();
        return transferSet.contains(new TaintTransfer(method, TaintTransfer.BASE, TaintTransfer.RESULT, type));
    }
    public Boolean detectArg2Base(JMethod method, Type type, int argIndex)
    {
        var transferSet = config.getTransfers();
        return transferSet.contains(new TaintTransfer(method, argIndex, TaintTransfer.BASE, type));
    }
    public Boolean detectArg2Result(JMethod method, Type type, int argIndex)
    {
        var transferSet = config.getTransfers();
        return transferSet.contains(new TaintTransfer(method, argIndex, TaintTransfer.RESULT, type));
    }

    public void detectSinkSite(JMethod method, int index, CSCallSite csCallSite)
    {
        var sinkSet = config.getSinks();
        if (sinkSet.contains(new Sink(method, index)))
            sinkSiteSet.add(new SinkSite(csCallSite, index));
    }


}

record SinkSite(CSCallSite csCallSite, int index){

}
