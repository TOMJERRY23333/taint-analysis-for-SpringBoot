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

package pascal.taie.analysis.pta.core.solver;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.graph.flowgraph.FlowKind;
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
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.Descriptor;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.MockObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.AssignLiteral;
import pascal.taie.ir.stmt.Cast;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.ArrayType;
import pascal.taie.language.type.ClassType;
import pascal.taie.language.type.Type;
import pascal.taie.language.type.TypeSystem;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.Sets;

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Predicate;

import static pascal.taie.language.classes.Signatures.FINALIZE;
import static pascal.taie.language.classes.Signatures.FINALIZER_REGISTER;

public class SpringBootSolver implements Solver {

    private static final Logger logger = LogManager.getLogger(SpringBootSolver.class);

    /**
     * Descriptor for array objects created implicitly by multiarray instruction.
     */
    private static final Descriptor MULTI_ARRAY_DESC = () -> "MultiArrayObj";

    /**
     * Number that represents unlimited elapsed time.
     */
    private static final long UNLIMITED = -1;

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private final CSManager csManager;

    private final ClassHierarchy hierarchy  =World.get().getClassHierarchy();

    private final TypeSystem typeSystem;

    private final PointsToSetFactory ptsFactory;

    private final PropagateTypes propTypes;

    /**
     * Whether only analyzes application code.
     */
    private final boolean onlyApp;

    /**
     * Time limit for pointer analysis (in seconds).
     */
    private final long timeLimit;

    private TimeLimiter timeLimiter;

    /**
     * Whether the analysis has reached time limit.
     */
    private volatile boolean isTimeout;

    private Plugin plugin;

    private WorkList workList;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private Set<JMethod> reachableMethods;

    /**
     * Set of classes that have been initialized.
     */
    private Set<JClass> initializedClasses;

    /**
     * Set of methods to be intercepted and ignored.
     */
    private Set<JMethod> ignoredMethods;

//    private StmtProcessor stmtProcessor;

    private PointerAnalysisResult result;

    /*
    visitor
    */
//    Information shared by all visitors.

//    private final Map<NewMultiArray, Obj[]> newArrays = Maps.newMap();
//
//    private final Map<New, Invoke> registerInvokes = Maps.newMap();
//
//    private final JMethod finalize = Objects.requireNonNull(
//            hierarchy.getJREMethod(FINALIZE));
//
//    private final MethodRef finalizeRef = finalize.getRef();
//
//    private final MethodRef registerRef = Objects.requireNonNull(
//            hierarchy.getJREMethod(FINALIZER_REGISTER)).getRef();



    @SuppressWarnings("unchecked")
    public SpringBootSolver(AnalysisOptions options, HeapModel heapModel,
                         ContextSelector contextSelector, CSManager csManager) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
        this.csManager = csManager;
//        hierarchy = World.get().getClassHierarchy();
        typeSystem = World.get().getTypeSystem();
        ptsFactory = new PointsToSetFactory(csManager.getObjectIndexer());
        propTypes = new PropagateTypes(
                (List<String>) options.get("propagate-types"),
                typeSystem);
        onlyApp = options.getBoolean("only-app");
        timeLimit = options.getInt("time-limit");
    }
        /*
    visitor
    */
//    Information shared by all visitors.

    private final Map<NewMultiArray, Obj[]> newArrays = Maps.newMap();

    private final Map<New, Invoke> registerInvokes = Maps.newMap();

    private final JMethod finalize = Objects.requireNonNull(
            hierarchy.getJREMethod(FINALIZE));

    private final MethodRef finalizeRef = finalize.getRef();

    private final MethodRef registerRef = Objects.requireNonNull(
            hierarchy.getJREMethod(FINALIZER_REGISTER)).getRef();

    @Override
    public AnalysisOptions getOptions() {
        return options;
    }

    @Override
    public HeapModel getHeapModel() {
        return heapModel;
    }

    @Override
    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    @Override
    public CSManager getCSManager() {
        return csManager;
    }

    @Override
    public ClassHierarchy getHierarchy() {
        return hierarchy;
    }

    @Override
    public TypeSystem getTypeSystem() {
        return typeSystem;
    }

    @Override
    public CSCallGraph getCallGraph() {
        return callGraph;
    }

    @Override
    public PointsToSet getPointsToSetOf(Pointer pointer) {
        PointsToSet pts = pointer.getPointsToSet();
        if (pts == null) {
            pts = ptsFactory.make();
            pointer.setPointsToSet(pts);
        }
        return pts;
    }

    @Override
    public PointsToSet makePointsToSet() {
        return ptsFactory.make();
    }

    @Override
    public void setPlugin(Plugin plugin) {
        this.plugin = plugin;
    }

    // ---------- solver logic starts ----------

    /**
     * Runs pointer analysis algorithm.
     */
    @Override
    public void solve() {
        initialize();
        analyze();
    }

    @Override
    public void propagateNew(Pointer pointer, Obj obj) {

    }


    @Override
    public PointsToSet propagate(Pointer pointer, Obj obj) {
        return null;
    }


    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph(csManager);
//        workList = new WorkList();
        reachableMethods = Sets.newSet();
        initializedClasses = Sets.newSet();
        ignoredMethods = Sets.newSet();
//        stmtProcessor = new StmtProcessor();
        isTimeout = false;
        if (timeLimit != UNLIMITED) {
            timeLimiter = new TimeLimiter(timeLimit);
            timeLimiter.countDown();
        }
        plugin.onStart();
    }

    private class TimeLimiter {

        private static final long MILLIS_FACTOR = 1000;

        private final Thread thread;

        /**
         * @param seconds the time limit.
         */
        private TimeLimiter(long seconds) {
            thread = new Thread(() -> {
                try {
                    Thread.sleep(seconds * MILLIS_FACTOR);
                } catch (InterruptedException ignored) {
                }
                isTimeout = true;
            });
        }

        /**
         * Starts count down.
         */
        private void countDown() {
            thread.start();
        }

        /**
         * Stops count down.
         */
        private void stop() {
            thread.interrupt();
        }
    }

    /**
     * Processes work list entries until the work list is empty.
     */
    private void analyze() {

        if (timeLimiter != null) { // finish normally but time limiter is still running
            timeLimiter.stop();
        }
        plugin.onFinish();
    }



    @Override
    public void propagateNew(Pointer pointer, PointsToSet pointsToSet){
        logger.trace("Propagate {} to {}", pointsToSet, pointer);
        Set<Predicate<CSObj>> filters = pointer.getFilters();
        if (!filters.isEmpty()) {
            // apply filters (of the pointer) on pointsToSet
            pointsToSet = pointsToSet.objects()
                    .filter(o -> filters.stream().allMatch(f -> f.test(o)))
                    .collect(ptsFactory::make, PointsToSet::addObject, PointsToSet::addAll);
        }
        PointsToSet diff = getPointsToSetOf(pointer).addAllDiff(pointsToSet);
        if (!diff.isEmpty()) {
            pointerFlowGraph.getOutEdgesOf(pointer).forEach(edge -> {
                Pointer target = edge.target();
                edge.getTransfers().forEach(transfer ->
                        addPointsTo(target, transfer.apply(edge, diff)));
            });
        }
    }

    /**
     * Processes instance stores when points-to set of the base variable changes.
     *
     * @param baseVar the base variable
     * @param pts     set of new discovered objects pointed by the variable.
     */
    private void processInstanceStore(CSVar baseVar, PointsToSet pts) {
        Context context = baseVar.getContext();
        Var var = baseVar.getVar();
        for (StoreField store : var.getStoreFields()) {
            Var fromVar = store.getRValue();
            if (propTypes.isAllowed(fromVar)) {
                CSVar from = csManager.getCSVar(context, fromVar);
                JField field = store.getFieldRef().resolve();
                pts.forEach(baseObj -> {
                    if (baseObj.getObject().isFunctional()) {
                        InstanceField instField = csManager.getInstanceField(baseObj, field);
                        addPFGEdge(from, instField, FlowKind.INSTANCE_STORE);
                    }
                });
            }
        }
    }

    /**
     * Processes instance loads when points-to set of the base variable changes.
     *
     * @param baseVar the base variable
     * @param pts     set of new discovered objects pointed by the variable.
     */
    private void processInstanceLoad(CSVar baseVar, PointsToSet pts) {
        Context context = baseVar.getContext();
        Var var = baseVar.getVar();
        for (LoadField load : var.getLoadFields()) {
            Var toVar = load.getLValue();
            if (propTypes.isAllowed(toVar)) {
                CSVar to = csManager.getCSVar(context, toVar);
                JField field = load.getFieldRef().resolve();
                pts.forEach(baseObj -> {
                    if (baseObj.getObject().isFunctional()) {
                        InstanceField instField = csManager.getInstanceField(baseObj, field);
                        addPFGEdge(instField, to, FlowKind.INSTANCE_LOAD);
                    }
                });
            }
        }
    }

    /**
     * Processes array stores when points-to set of the array variable changes.
     *
     * @param arrayVar the array variable
     * @param pts      set of new discovered arrays pointed by the variable.
     */
    private void processArrayStore(CSVar arrayVar, PointsToSet pts) {
        Context context = arrayVar.getContext();
        Var var = arrayVar.getVar();
        for (StoreArray store : var.getStoreArrays()) {
            Var rvalue = store.getRValue();
            if (propTypes.isAllowed(rvalue)) {
                CSVar from = csManager.getCSVar(context, rvalue);
                pts.forEach(array -> {
                    if (array.getObject().isFunctional()) {
                        ArrayIndex arrayIndex = csManager.getArrayIndex(array);
                        // we need type guard for array stores as Java arrays
                        // are covariant
                        addPFGEdge(new PointerFlowEdge(
                                        FlowKind.ARRAY_STORE, from, arrayIndex),
                                arrayIndex.getType());
                    }
                });
            }
        }
    }

    /**
     * Processes array loads when points-to set of the array variable changes.
     *
     * @param arrayVar the array variable
     * @param pts      set of new discovered arrays pointed by the variable.
     */
    private void processArrayLoad(CSVar arrayVar, PointsToSet pts) {
        Context context = arrayVar.getContext();
        Var var = arrayVar.getVar();
        for (LoadArray load : var.getLoadArrays()) {
            Var lvalue = load.getLValue();
            if (propTypes.isAllowed(lvalue)) {
                CSVar to = csManager.getCSVar(context, lvalue);
                pts.forEach(array -> {
                    if (array.getObject().isFunctional()) {
                        ArrayIndex arrayIndex = csManager.getArrayIndex(array);
                        addPFGEdge(arrayIndex, to, FlowKind.ARRAY_LOAD);
                    }
                });
            }
        }
    }

    private boolean isIgnored(JMethod method) {
        return ignoredMethods.contains(method) ||
                onlyApp && !method.isApplication();
    }

    /**
     * Processes new reachable methods.
     */
    private void processNewMethod(JMethod method) {
        if (reachableMethods.add(method)) {
            plugin.onNewMethod(method);
            method.getIR().forEach(stmt -> plugin.onNewStmt(stmt, method));
        }
    }



    // ---------- solver logic ends ----------

    @Override
    public void addPointsTo(Pointer pointer, PointsToSet pts) {
        workList.addEntry(pointer, pts);
    }

    @Override
    public void addPointsTo(Pointer pointer, CSObj csObj) {
        PointsToSet pts = makePointsToSet();
        pts.addObject(csObj);
        addPointsTo(pointer, pts);
    }

    @Override
    public void addPointsTo(Pointer pointer, Context heapContext, Obj obj) {
        addPointsTo(pointer, csManager.getCSObj(heapContext, obj));
    }

    @Override
    public void addVarPointsTo(Context context, Var var, PointsToSet pts) {
        addPointsTo(csManager.getCSVar(context, var), pts);
    }

    @Override
    public void addVarPointsTo(Context context, Var var, CSObj csObj) {
        addPointsTo(csManager.getCSVar(context, var), csObj);
    }

    @Override
    public void addVarPointsTo(Context context, Var var, Context heapContext, Obj obj) {
        addPointsTo(csManager.getCSVar(context, var), heapContext, obj);
    }

    @Override
    public void addPointerFilter(Pointer pointer, Predicate<CSObj> filter) {
        pointer.addFilter(filter);
    }

    @Override
    public void addPFGEdge(PointerFlowEdge edge, Transfer transfer) {
        edge = pointerFlowGraph.addEdge(edge);
        if (edge != null && edge.addTransfer(transfer)) {
            PointsToSet targetSet = transfer.apply(
                    edge, getPointsToSetOf(edge.source()));
            if (!targetSet.isEmpty()) {
                addPointsTo(edge.target(), targetSet);
            }
        }
    }

    public void visitor(JMethod container,Context context,Stmt stmt){
        CSMethod csMethod = csManager.getCSMethod(context, container);
        // =======处理new语句 生成抽象对象=======
        if(stmt instanceof New newStmt){
            // obtain context-sensitive heap object
            NewExp rvalue = newStmt.getRValue();
            Var var = newStmt.getLValue();
            Obj obj = heapModel.getObj(newStmt);
            Context heapContext = contextSelector.selectHeapContext(csMethod, obj);

                      /*  =====对于new语句直接给var赋予堆抽象对象，而不是原本的如WL=====
                         // addVarPointsTo(entryCtx, var, heapContext, obj);
                        */
            Pointer point = csManager.getCSVar(context,var);
            //创建PTS对象,并传播
            PointsToSet pts = makePointsToSet();
            pts.addObject(csManager.getCSObj(heapContext,obj));
            propagateNew(point,pts);
            //==========================

            if (rvalue instanceof NewMultiArray) {
                processNewMultiArray(newStmt, heapContext, obj,csMethod);
            }
            if (hasOverriddenFinalize(rvalue)) {
                processFinalizer(newStmt,csMethod,context);
            }
        }
        //=====================

        // =====处理x = o.f，x = T.f语句，并判断是否为fieldsources====
        if(stmt instanceof  LoadField loadFieldStmt) {
            if (loadFieldStmt.isStatic() && propTypes.isAllowed(loadFieldStmt.getRValue())) {
                JField field = loadFieldStmt.getFieldRef().resolve();
                StaticField sfield = csManager.getStaticField(field);
                // 左值
                Var var = loadFieldStmt.getLValue();
                CSVar to = csManager.getCSVar(context, var);
//              addPFGEdge(sfield, to, FlowKind.STATIC_LOAD);
                addPFGEdgeAndPropagate(sfield,to,FlowKind.STATIC_LOAD);
            }
        }

        //=====处理o.f = x，T.f = x语句====
        if(stmt instanceof  StoreField storeFieldStmt){
            if (storeFieldStmt.isStatic() && propTypes.isAllowed(storeFieldStmt.getRValue())) {
                JField field = storeFieldStmt.getFieldRef().resolve();
                StaticField sfield = csManager.getStaticField(field);
                CSVar from = csManager.getCSVar(context, storeFieldStmt.getRValue());
                addPFGEdgeAndPropagate(from,sfield,FlowKind.STATIC_STORE);
            }
        }

        // =====处理statement that assigns literals, e.g., a = 10.语句=====
        if(stmt instanceof AssignLiteral assignLiteralStmt){
            Literal literal = assignLiteralStmt.getRValue();
            Type type = literal.getType();
            if (type instanceof ClassType) {
                // here we only generate objects of ClassType
                Obj obj = heapModel.getConstantObj((ReferenceLiteral) literal);
                Context heapContext = contextSelector
                        .selectHeapContext(csMethod, obj);
//                addVarPointsTo(context, assignLiteralStmt.getLValue(), heapContext, obj);

                //创建PTS对象,并传播
                Var var = assignLiteralStmt.getLValue();
                CSObj  csObj = csManager.getCSObj(heapContext,obj);
                addPtsAndPropagate(context,var,csObj);
            }
        }

        // =======处理e.g., a = b.语句=====
        if(stmt instanceof Copy copyStmt){
            Var rvalue = copyStmt.getRValue();
            if (propTypes.isAllowed(rvalue)) {
                CSVar from = csManager.getCSVar(context, rvalue);
                CSVar to = csManager.getCSVar(context, copyStmt.getLValue());
                addPFGEdgeAndPropagate(from, to, FlowKind.LOCAL_ASSIGN);
            }
        }
        // ======处理a = (T) b语句========
        if(stmt instanceof Cast castStmt){
            CastExp cast = castStmt.getRValue();
            if (propTypes.isAllowed(cast.getValue())) {
                CSVar from = csManager.getCSVar(context, cast.getValue());
                CSVar to = csManager.getCSVar(context, castStmt.getLValue());
                addPFGEdgeAndPropagate(new PointerFlowEdge(
                                FlowKind.CAST, from, to),
                        cast.getType());
            }
        }
        // =============================================

        // ==========处理InstanceStore:  o.f = x,T.f = x============
        if(stmt instanceof StoreField storeFieldStmt){
            Var fromVar = storeFieldStmt.getRValue();
            if (propTypes.isAllowed(fromVar)) {
                CSVar from = csManager.getCSVar(context,fromVar);

                JField field = storeFieldStmt.getFieldRef().resolve();
                FieldAccess fieldAccess = storeFieldStmt.getFieldAccess();
                Var InstanceVar = ((InstanceFieldAccess) fieldAccess).getBase();
                CSVar csToInstanceVar = csManager.getCSVar(context,InstanceVar);
                PointsToSet pts = getPointsToSetOf(csToInstanceVar);

                pts.forEach(baseObj -> {
                    if (baseObj.getObject().isFunctional()) {
                        InstanceField instField = csManager.getInstanceField(baseObj, field);
                        addPFGEdgeAndPropagate(from, instField, FlowKind.INSTANCE_STORE);
                    }
                });
            }
        }

        //===================================


        // ==============处理InstanceLoad:x = o.f, x = T.f==============
        if(stmt instanceof LoadField loadFieldStmt){
            Var toVar = loadFieldStmt.getLValue();
            if (propTypes.isAllowed(toVar)) {
                CSVar to = csManager.getCSVar(context, toVar);
                JField field = loadFieldStmt.getFieldRef().resolve();
                FieldAccess fieldAccess = loadFieldStmt.getFieldAccess();
                Var InstanceVar = ((InstanceFieldAccess) fieldAccess).getBase();
                CSVar csFromInstanceVar = csManager.getCSVar(context,InstanceVar);
                PointsToSet pts = getPointsToSetOf(csFromInstanceVar);
                pts.forEach(baseObj -> {
                    if (baseObj.getObject().isFunctional()) {
                        InstanceField instField = csManager.getInstanceField(baseObj, field);
                        addPFGEdgeAndPropagate(instField, to, FlowKind.INSTANCE_LOAD);
                    }
                });
            }
        }
        //===================================

        //================处理ArrayStore:a[..] = x==============
        if(stmt instanceof StoreArray storeArrayStmt){
            Var rvalue = storeArrayStmt.getRValue();
            CSVar from = csManager.getCSVar(context,rvalue);
//            访问数组
            Var toArrayVar  = storeArrayStmt.getLValue().getBase();
            CSVar toCSArrayVar = csManager.getCSVar(context,toArrayVar);

            if (propTypes.isAllowed(rvalue)) {
//                addPFGEdgeAndPropagate(from,toCSArrayVar,FlowKind.INSTANCE_STORE);
                PointsToSet ptsArray = getPointsToSetOf(toCSArrayVar);
                for(CSObj csObj: ptsArray){
                    if(csObj.getObject().isFunctional()){
                        ArrayIndex arrayIndex = csManager.getArrayIndex(csObj);
                        addPFGEdgeAndPropagate(new PointerFlowEdge(
                                        FlowKind.ARRAY_STORE, from, arrayIndex),
                                arrayIndex.getType());
                    }

                }
            }
        }
        // =========================================

        // ====================处理ArrayLoad: x = a[..].=====================
        if(stmt instanceof  LoadArray loadArrayStmt){
            Var lvalue = loadArrayStmt.getLValue();
            CSVar to = csManager.getCSVar(context,lvalue);
            // 获得数组对象
            Var fromArrayVar= loadArrayStmt.getArrayAccess().getBase();
            CSVar from = csManager.getCSVar(context,fromArrayVar);
            PointsToSet ptsArray = getPointsToSetOf(from);
            if (propTypes.isAllowed(lvalue)) {
                ptsArray.forEach(array -> {
                    if (array.getObject().isFunctional()) {
                        ArrayIndex arrayIndex = csManager.getArrayIndex(array);
                        addPFGEdgeAndPropagate(arrayIndex, to, FlowKind.ARRAY_LOAD);
                    }
                });
            }
        }


        if(stmt instanceof  Invoke invokeStmt){
            if (invokeStmt.isStatic()) {
                processInvokeStatic(invokeStmt,context);
            }
            else {
                // 获得callee
                InvokeExp  invokeExp = invokeStmt.getInvokeExp();
                // 处理静态调用和虚拟调用
                Var var = ((InvokeInstanceExp) invokeExp).getBase();
                CSVar csVar = csManager.getCSVar(context,var);
                getPointsToSetOf(csVar).forEach(recvObj -> {
                    JMethod callee = CallGraphs.resolveCallee(var.getType(),invokeStmt);
                    if (callee != null) {
                        // select context
                        CSCallSite csCallSite = csManager.getCSCallSite(context, invokeStmt);
                        Context calleeContext = contextSelector.selectContext(
                                csCallSite, recvObj, callee);
                        // build call edge
                        CSMethod csCallee = csManager.getCSMethod(calleeContext, callee);
//                        JMethod callee = csCallee.getMethod();
                        Edge<CSCallSite,CSMethod> edge = new Edge<>(CallGraphs.getCallKind(invokeStmt),
                                csCallSite, csCallee);
//                        addCallEdge(edge);
                        // pass receiver object to *this* variable
                        if (edge.getKind()!=CallKind.OTHER && !isIgnored(callee)) {
                             // true说明需要探查,false不需要探查该invoke的具体方法
                            if(plugin.judgeCheck(edge,csVar)) {

                                // 1.传播<c:M_this,{c:recvObj}(相当于var-M_this,但不构建PFG边)
                                addPtsAndPropagate(calleeContext, callee.getIR().getThis(),recvObj);
                                // 2. 构建并传播ret-lhs,arg-param
                                processEdgeTransfer(edge);
                                visitor(callee, calleeContext, invokeStmt);
                            }
                        }

                    } else {
                        plugin.onUnresolvedCall(recvObj, context, invokeStmt);
                    }
                });

            }
        }


    }

    public void processEdgeTransfer(Edge<CSCallSite, CSMethod> edge){
        CSMethod csCallee = edge.getCallee();
        // 调用点所在的上下文
        Context callerCtx = edge.getCallSite().getContext();
        Invoke callSite = edge.getCallSite().getCallSite();
        //调用点所产生的上下文
        Context calleeCtx = csCallee.getContext();
        JMethod callee = csCallee.getMethod();
        InvokeExp invokeExp = callSite.getInvokeExp();
        // pass arguments to parameters
        // 参数传递arg-param
        for (int i = 0; i < invokeExp.getArgCount(); ++i) {
            Var arg = invokeExp.getArg(i);
            if (propTypes.isAllowed(arg)) {
                Var param = callee.getIR().getParam(i);
                CSVar argVar = csManager.getCSVar(callerCtx, arg);
                CSVar paramVar = csManager.getCSVar(calleeCtx, param);
                addPFGEdgeAndPropagate(argVar, paramVar, FlowKind.PARAMETER_PASSING);
            }
        }
        // pass results to LHS variable
        Var lhs = callSite.getResult();
        if (lhs != null && propTypes.isAllowed(lhs)) {
            CSVar csLHS = csManager.getCSVar(callerCtx, lhs);
            for (Var ret : callee.getIR().getReturnVars()) {
                if (propTypes.isAllowed(ret)) {
                    CSVar csRet = csManager.getCSVar(calleeCtx, ret);
                    addPFGEdgeAndPropagate(csRet, csLHS, FlowKind.RETURN);
                }
            }
        }
    }

//    public void propagate(Var var,Context currContext,Context heapContext,Obj obj){
//        //创建PTS对象,并传播
//        Var var = assignLiteralStmt.getLValue();
//        Pointer point = csManager.getCSVar(context,var);
//        PointsToSet pts = makePointsToSet();
//        pts.addObject(csManager.getCSObj(heapContext,obj));
//        propagate(point,pts);
//    }
//    public void addPFGEdgeAndPropagate(Context context, Var var,CSObj csObj){
//        addPFGEdgeAndPropagate(csManager.getCSVar(context,var),csObj);
//    }
    public void addPtsAndPropagate(Context context,Var var,Context heapContext,Obj obj){
          addPtsAndPropagate(context,var,csManager.getCSObj(heapContext,obj));
    }
    public void addPtsAndPropagate(Context context,Var var,CSObj csObj){
        Pointer pointer = csManager.getCSVar(context,var);
        addPtsAndPropagate(pointer,csObj);
    }
    public void addPtsAndPropagate(Pointer pointer,Context heapContext,Obj obj){
        CSObj csObj = csManager.getCSObj(heapContext,obj);
        addPtsAndPropagate(pointer,csObj);
    }
    public void addPtsAndPropagate(Pointer pointer,CSObj csObj){
        PointsToSet pts = makePointsToSet();
        pts.addObject(csObj);
        propagateNew(pointer,pts);
    }


    public void addPFGEdgeAndPropagate(Pointer source, Pointer target, FlowKind kind){
        // 创建PFG的边
        PointerFlowEdge edge = new PointerFlowEdge(kind,source,target);
        Transfer transfer = Identity.get();
        edge = pointerFlowGraph.addEdge(edge);
        if (edge != null && edge.addTransfer(transfer)) {
            PointsToSet targetSet = transfer.apply(
                    edge, getPointsToSetOf(edge.source()));
            if (!targetSet.isEmpty()) {
                //传播
                propagateNew(edge.target(), targetSet);
            }
        }
    }

    @Override
    public void addPFGEdgeAndPropagate(PointerFlowEdge edge, Transfer transfer){
        // 创建PFG的边
        edge = pointerFlowGraph.addEdge(edge);
        if (edge != null && edge.addTransfer(transfer)) {
            PointsToSet targetSet = transfer.apply(
                    edge, getPointsToSetOf(edge.source()));
            if (!targetSet.isEmpty()) {
                //传播
                propagateNew(edge.target(), targetSet);
            }
        }
    }



    @Override
    public void addEntryPoint(EntryPoint entryPoint) {
        Context entryCtx = contextSelector.getEmptyContext();
        JMethod entryMethod = entryPoint.method();
        CSMethod csEntryMethod = csManager.getCSMethod(entryCtx, entryMethod);
        callGraph.addEntryMethod(csEntryMethod);

        IR ir = entryMethod.getIR();
        ParamProvider paramProvider = entryPoint.paramProvider();
        // pass this objects
        if (!entryMethod.isStatic()) {
            for (Obj thisObj : paramProvider.getThisObjs()) {
                addPtsAndPropagate(entryCtx, ir.getThis(), entryCtx, thisObj);
            }
        }
        // pass parameter objects
        for (int i = 0; i < entryMethod.getParamCount(); ++i) {
            Var param = ir.getParam(i);
            if (propTypes.isAllowed(param)) {
                for (Obj paramObj : paramProvider.getParamObjs(i)) {
                    addPtsAndPropagate(entryCtx, param, entryCtx, paramObj);
                }
            }
        }
        // pass field objects
        paramProvider.getFieldObjs().forEach((base, field, obj) -> {
            CSObj csBase = csManager.getCSObj(entryCtx, base);
            InstanceField iField = csManager.getInstanceField(csBase, field);
            addPtsAndPropagate(iField, entryCtx, obj);
        });
        // pass array objects
        paramProvider.getArrayObjs().forEach((array, elem) -> {
            CSObj csArray = csManager.getCSObj(entryCtx, array);
            ArrayIndex arrayIndex = csManager.getArrayIndex(csArray);
            addPtsAndPropagate(arrayIndex, entryCtx, elem);
        });

        //处理方法的STMT
        // 1.先处理new语句——recv,pts
        // 处理调用
        if (callGraph.addReachableMethod(csEntryMethod)) {
            // process new reachable context-sensitive method
            if (isIgnored(entryMethod)) {
                return;
            }
            if (reachableMethods.add(entryMethod)) {
//                plugin.onNewMethod(method);
                // 污点分析：在SourceHandler插件中对其进行处理,并对main方法中所有new语句进行处理
                ir.forEach(stmt -> plugin.onNewStmt(stmt, entryMethod));
                for(Stmt stmt: ir){
                    visitor(entryMethod,entryCtx,stmt);
                }
            }

        }
    }

    private void processNewMultiArray(
            New allocSite, Context arrayContext, Obj array,CSMethod csMethod) {
        NewMultiArray newMultiArray = (NewMultiArray) allocSite.getRValue();
        Obj[] arrays = newArrays.computeIfAbsent(newMultiArray, nma -> {
            ArrayType type = nma.getType();
            Obj[] newArrays = new MockObj[nma.getLengthCount() - 1];
            for (int i = 1; i < nma.getLengthCount(); ++i) {
                type = (ArrayType) type.elementType();
                newArrays[i - 1] = heapModel.getMockObj(MULTI_ARRAY_DESC,
                        allocSite, type, allocSite.getContainer());
            }
            return newArrays;
        });
        for (Obj newArray : arrays) {
            Context elemContext = contextSelector
                    .selectHeapContext(csMethod, newArray);
            CSObj arrayObj = csManager.getCSObj(arrayContext, array);
            ArrayIndex arrayIndex = csManager.getArrayIndex(arrayObj);
            addPointsTo(arrayIndex, elemContext, newArray);
            array = newArray;
            arrayContext = elemContext;
        }
    }

    private boolean hasOverriddenFinalize(NewExp newExp) {
        return !finalize.equals(
                hierarchy.dispatch(newExp.getType(), finalizeRef));
    }

    private void processFinalizer(New stmt,CSMethod csMethod,Context context) {
        Invoke registerInvoke = registerInvokes.computeIfAbsent(stmt, s -> {
            InvokeStatic callSite = new InvokeStatic(registerRef,
                    Collections.singletonList(s.getLValue()));
            Invoke invoke = new Invoke(csMethod.getMethod(), callSite);
            invoke.setLineNumber(stmt.getLineNumber());
            return invoke;
        });
        processInvokeStatic(registerInvoke,context);
    }

    private void processInvokeStatic(Invoke callSite,Context context) {
        JMethod callee = CallGraphs.resolveCallee(null, callSite);
        if (callee != null) {
            CSCallSite csCallSite = csManager.getCSCallSite(context, callSite);
            Context calleeCtx = contextSelector.selectContext(csCallSite, callee);
            CSMethod csCallee = csManager.getCSMethod(calleeCtx, callee);
//            addCallEdge(new Edge<>(CallKind.STATIC, csCallSite, csCallee));
        }
    }
    @Override
    public void addCallEdge(Edge<CSCallSite, CSMethod> edge) {
        workList.addEntry(edge);
    }

    public void newProcessCall(Edge<CSCallSite, CSMethod> edge){

    }

    //处理新的上下文被调用的方法
    @Override
    public void addCSMethod(CSMethod csMethod) {
        if (callGraph.addReachableMethod(csMethod)) {
            // process new reachable context-sensitive method
            JMethod method = csMethod.getMethod();
            if (isIgnored(method)) {
                return;
            }
            processNewMethod(method);
            // 处理方法语句
            addStmts(csMethod, method.getIR().getStmts());
//            plugin.onNewCSMethod(csMethod);
        }
    }

    @Override
    public void addStmts(CSMethod csMethod, Collection<Stmt> stmts) {

    }

//    @Override
//    public void addStmts(CSMethod csMethod, Collection<Stmt> stmts) {
//        stmtProcessor.process(csMethod, stmts);
//    }
//
//    public void addInvokeStmts(CSMethod csMethod, Collection<Stmt> stmts) {
//        stmtProcessor.process(csMethod, stmts);
//    }

    @Override
    public void addIgnoredMethod(JMethod method) {
        ignoredMethods.add(method);
    }

    @Override
    public void initializeClass(JClass cls) {
        if (cls == null || initializedClasses.contains(cls)) {
            return;
        }
        // initialize super class
        JClass superclass = cls.getSuperClass();
        if (superclass != null) {
            initializeClass(superclass);
        }
        // TODO: initialize the superinterfaces which
        //  declare default methods
        JMethod clinit = cls.getClinit();
        if (clinit != null) {
            // addCSMethod() may trigger initialization of more
            // classes. So cls must be added before addCSMethod(),
            // otherwise, infinite recursion may occur.
            initializedClasses.add(cls);
            CSMethod csMethod = csManager.getCSMethod(
                    contextSelector.getEmptyContext(), clinit);
            addCSMethod(csMethod);
        }
    }

    @Override
    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(
                    propTypes, csManager, heapModel,
                    callGraph, pointerFlowGraph);
        }
        return result;
    }
}
