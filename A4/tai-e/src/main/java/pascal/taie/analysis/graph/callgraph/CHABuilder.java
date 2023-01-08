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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;
import soot.jimple.internal.JCastExpr;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
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
    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        LinkedList<JMethod> workList = new LinkedList<>();
        workList.add(entry);
        while (!workList.isEmpty())
        {
            var jMethod = workList.removeFirst();
            if(!callGraph.contains(jMethod))
            {
                callGraph.addReachableMethod(jMethod);
                callGraph.callSitesIn(jMethod).forEach((callSite)->{
                            for(var callee: resolve(callSite))
                            {
                                workList.add(callee);
                                callGraph.addEdge(new Edge<>(getCallKind(callSite), callSite, callee));
                            }
                        }
                );
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> set = new HashSet<>();
        var signature = callSite.getMethodRef();
        var declaredClass = signature.getDeclaringClass();
        var subSignature = signature.getSubsignature();
        var callKind = CallGraphs.getCallKind(callSite);
        if(callKind == CallKind.STATIC)
        {
            var staticMethod = declaredClass.getDeclaredMethod(subSignature);
            assert staticMethod != null;
            set.add(staticMethod);
        }
        else if(callKind == CallKind.SPECIAL)
        {
            var specialMethod = dispatch(declaredClass, subSignature);
            assert specialMethod != null;
            set.add(specialMethod);
        }
        else if(callKind == CallKind.VIRTUAL || callKind == CallKind.INTERFACE)
        {
            LinkedList<JClass> list = new LinkedList<>();
            list.add(declaredClass);
            while (!list.isEmpty()){
                var jClass = list.removeFirst();
                var res = dispatch(jClass, subSignature);
                if(res != null)
                    set.add(res);

                if(jClass.isInterface())
                {
                    list.addAll(hierarchy.getDirectSubinterfacesOf(jClass));
                    list.addAll(hierarchy.getDirectImplementorsOf(jClass));
                }
                else
                    list.addAll(hierarchy.getDirectSubclassesOf(jClass));

            }
        }
        else
            assert false;
        return set;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        var method = jclass.getDeclaredMethod(subsignature);
        if(method != null && !method.isAbstract())
            return method;
        else{
            if(jclass.getSuperClass() == null)
                return null;
            else
                return dispatch(jclass.getSuperClass(), subsignature);
        }

    }
}
