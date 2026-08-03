/*
 * Copyright (c) 1999-2014, Ecole des Mines de Nantes
 * All rights reserved.
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *     * Redistributions in binary form must reproduce the above copyright
 *       notice, this list of conditions and the following disclaimer in the
 *       documentation and/or other materials provided with the distribution.
 *     * Neither the name of the Ecole des Mines de Nantes nor the
 *       names of its contributors may be used to endorse or promote products
 *       derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND ANY
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE REGENTS AND CONTRIBUTORS BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package org.chocosolver.graphsolver.cstrs.cost.tsp.lagrangianRelaxation;

import org.chocosolver.graphsolver.variables.GraphEventType;
import org.chocosolver.graphsolver.variables.UndirectedGraphVar;
import org.chocosolver.graphsolver.variables.delta.GraphDeltaMonitor;
import org.chocosolver.memory.IStateDouble;
import org.chocosolver.memory.IStateIntVector;
import org.chocosolver.solver.constraints.Propagator;
import org.chocosolver.solver.constraints.PropagatorPriority;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.solver.variables.Variable;
import org.chocosolver.solver.variables.events.IntEventType;
import org.chocosolver.util.ESat;
import org.chocosolver.util.objects.graphs.UndirectedGraph;
import org.chocosolver.util.procedure.PairProcedure;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * TSP Lagrangian relaxation
 * Inspired from the work of Held & Karp
 * and Benchimol et. al. (Constraints 2012)
 *
 * @author Jean-Guillaume Fages
 */
public class PropFusionAsymUndirectedGraphVar extends Propagator<Variable> {

	//***********************************************************************************
	// VARIABLES
	//***********************************************************************************

	protected UndirectedGraph g;
	protected UndirectedGraphVar gV;
	private GraphDeltaMonitor deltaMonitor;
	private PairProcedure onArcRemoved;
	private PairProcedure onArcEnforced;

	protected IntVar costVar;
	protected int n;
	protected int[][] originalSmallCosts;
	protected double[][] costs;
	protected double[][] reducedCosts;

	//TODO je pourrais garder les variables dual au lieu de la matrice,
	// ce serait plus léger mais plus chiant à recalculer
	private IStateDouble[][] reducedCostsState;
	//private IStateBitSet[] cyclesState;
	//private IStateDouble[] penaltiesState;
	private IStateDouble lowerBoundState;
	private IStateIntVector arcsEnforcedFromState;
	BitSet remainingRows;
	BitSet remainingCols;
	int nRemaining;
	protected boolean waitFirstSol;
	protected int nbSprints;
	private static int bigValue = 99999999;
	public double firstLb = Double.NEGATIVE_INFINITY;
	public int[][] bestStarZeros;
	//private HashSet<Integer> remainingRows;
	//private HashSet<Integer> remainingCols;
	//private IStateBitSet remainingNodesState;

	// DataFirstIter
	private boolean getData = true;
	private long startTime;
	public List<Integer> dataTime;
	public List<Integer> dataBound;
	public List<Boolean> dataIsHungarian;
	private double lowerBound;
	public String graphData;
	private HungarianAlgorithm hung;
	//True : Hung
	//False: Edmond

	//***********************************************************************************
	// CONSTRUCTORS
	//***********************************************************************************

	public Result hungarianSSP(double[][] costs){
		Result result = hung.execute(costs, remainingRows, remainingCols);
		return result;
	}

	private int countStars(int[][] zeros) {
		int count = 0;
		for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1))
			for (int j = remainingCols.nextSetBit(0); j >= 0; j = remainingCols.nextSetBit(j + 1))
				if (zeros[i][j] == 1)
					count++;
		return count;
	}


	public static class Result {
		public final double lb;
		public final double[][] array;
		public final int[] matching;

		public Result(double lb, double[][] array, int[] matching) {
			this.lb = lb;
			this.array = array;
			this.matching = matching;
		}
	}

	public static List<Integer> dfsFindCycle(int[] matching, int node, Set<Integer> visited,
											 Map<Integer, Integer> parent, Set<Integer> recStack) {
		visited.add(node);
		recStack.add(node);
		int i = matching[node];
		if (recStack.contains(i)) {
			parent.put(i, node);
			List<Integer> cycle = new ArrayList<>();

			int x = node;
			cycle.add(x);
			while (x != i) {
				x = parent.get(x);
				cycle.add(0, x);
			}
			return cycle;
		}

		// If not visited → recurse
		if (!visited.contains(i)) {
			parent.put(i, node);
			List<Integer> cycle = dfsFindCycle(matching, i, visited, parent, recStack);
			if (cycle != null && !cycle.isEmpty()) {
				return cycle;
			}
		}

		recStack.remove(node);
		return null;  // no cycle found
	}

	int removed = 0;

	public void basicFiltering(double[][] reducedCostsArray, double lowerBound) throws ContradictionException {

		double delta = costVar.getUB() - lowerBound;
		if (delta < 0){
			this.fails();
		}
		for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)){
			for (int j = remainingCols.nextSetBit(0); j >= 0; j = remainingCols.nextSetBit(j + 1)){
				if (gV.getUB().isArcOrEdge(i+n,j) && i != j && reducedCostsArray[i][j] > delta) {
					//System.out.println("[FUSION][BASICFILTER] remove " + (i+n) + "->" + j
					//		+ " rc=" + reducedCostsArray[i][j] + " delta=" + delta + " lb=" + lowerBound);
					reducedCostsArray[i][j] = bigValue;
					remove(i+n, j);
				}
			}
		}
		//mandFiltering();
	}

	//TODO remove de la map apres l'avoir annulé
	private HashMap<BitSet, Double> cycleMap = new HashMap<>();

	public Result testtest(
			double[][] matrix,
			boolean ignoreStars,
			int[][] starZeros
	) throws ContradictionException {
		int a = 3;
		return null;
	}

	int count = 0;

	public Result edmondsIteration(
			double[][] matrix,
			boolean ignoreStars,
			int[] matching
	) throws ContradictionException {
		//TODO check je fais quoi avec ça, est-ce que j'exécute juste si countStars est n? ou >n/2? ou 3n/4 ?
		/*if(starZeros == null && !ignoreStars || countStars(starZeros) < n){
			return new Result(0, matrix, null);
		}*/
		//for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)){
		//	for (int j = remainingCols.nextSetBit(0); j >= 0; j = remainingCols.nextSetBit(j + 1)){

		count++;

		if(count == 2){
			int a =3;
		}
		int n = matrix.length;
		double lb = 0;
		if(!ignoreStars){
		} else {
			throw new RuntimeException("Error352");
		}

		for (int i = remainingRows.nextClearBit(0); i < n; i = remainingRows.nextClearBit(i + 1)){
			//Met les zéros des arcs obligatoires
			matching[i] = arcsEnforcedFromState.quickGet(i);
		}
		//Force 1-tree, maybe not necessary
			/*	new int[n - 1][n - 1];
		for (int i = 1; i < n; i++)
			System.arraycopy(starZeros[i], 1, edges[i - 1], 0, n - 1);*/

		Set<Integer> visited = new HashSet<>();
		 List<List<Integer>> cycles = new ArrayList<>();

		// Find cycle
		for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)){
			if (!visited.contains(i) /*&& cycle == null*/) {
				List<Integer> cycle = dfsFindCycle(matching, i, visited,
						new HashMap<>(), new HashSet<>());
				if (cycle != null && cycle.size() < n) {
					cycles.add(cycle);
				}
			}
		}

		//TODO peut-être refactor ici pour ne pas utiliser les masques, il doit y avoir plus efficace en java
		// Utiliser tuples pour cycleEdgesMask
		for(List<Integer> cycle : cycles){
			/*for (int i = 0; i < edges.length; i++)
				for (int j = 0; j < edges[0].length; j++)
					if (cycleEdgesMask[i][j])
						minimumCandidates.add(matrix[i][j]);*/
			BitSet cycleBs = createBitsetFromList(cycle);
			double minimum = bigValue;
			for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)){
				if(!cycleBs.get(i)){
					continue;
				}
				for (int j = remainingCols.nextSetBit(0); j >= 0; j = remainingCols.nextSetBit(j + 1)){
					if (cycleBs.get(j)){
						minimum = Math.min(minimum, matrix[i][j]);
					}
				}
			}

			if (minimum > bigValue*0.9){
				//Implique que la meilleure alternative est un infini, donc on est obligé de rester dans le cycle. Contradiction
				this.fails();
			}

			if (cycle.size() > 2 && minimum != 0){
				int a =3;
			}

			double minimumRows = bigValue;
			double minimumCols = bigValue;

			/*for (int i = 0; i < edges.length; i++) {
				for (int j = 0; j < edges[0].length; j++) {
					if (cycle.contains(i) && edges[i][j] != 1) {
						if (matrix[i][j] < minimumRows) {
							minimumRows = matrix[i][j];
						}
					}
					if (i != j && cycle.contains(j) && edges[i][j] != 1) {
						if (matrix[i][j] < minimumCols) {
							minimumCols = matrix[i][j];
						}
					}
				}
			}*/

			if(minimumCols != minimum){
				int a =3;
			}
			//double minimum = minimumCols;// Math.max(minimumRows, minimumCols);


			//Check if there's at least one non-zero

			/*if (minimum == 0) {
				for (int i = 0; i < n; i++)
					for (int j = 0; j < n; j++)
						if (i != j && matrix[i][j] != 0)
							minimum = 1;
			}*/

			/*for (int i = 0; i < cycle.size(); i++) {
				int from = cycle.get(i);
				int to = cycle.get((i + 1) % cycle.size());
				matrix[from][to] += minimum;
			}*/
			int updated = 0;
			BitSet notCycleBs = createBitsetFromList(cycle);
			notCycleBs.flip(0, n);
			for (int i = notCycleBs.nextSetBit(0); i >= 0; i = notCycleBs.nextSetBit(i + 1)){
				if(remainingRows.get(i)){
					for(int j : cycle){
						if (remainingCols.get(j) && i != j) {
							updated++;
							matrix[i][j] -= minimum;
							if(matrix[i][j] < 0){
								int a =3;
							}
						}
					}
				}
			}

			double boundChange = minimum * (cycle.size() - 1);
			lb += minimum;

			//System.out.println("[FUSION][EDMONDS] cycle=" + cycle + " minimum=" + minimum + " boundChange=" + boundChange);
			// For logging cycle changes
			boundDecreased += boundChange;
			if (minimum != 0){
				updateMap(createBitsetFromList(cycle), minimum);
			}

			//TODO ???

			/*for (int col = 0; col < n; col++) {
				double min = Double.POSITIVE_INFINITY;
				//TODO
				for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1))
					min = Math.min(min, matrix[i][col]);

				lb += min;

				for (int row = 0; row < n; row++)
					matrix[row][col] -= min;
			}*/
		}


		// Column reduction USELESS
		/*for (int col = remainingCols.nextSetBit(0); col >= 0; col = remainingCols.nextSetBit(col + 1)){
			double min = Double.POSITIVE_INFINITY;
			for (int row = remainingRows.nextSetBit(0); row >= 0; row = remainingRows.nextSetBit(row + 1))
				min = Math.min(min, matrix[row][col]);

			lb += min;

			for (int row = remainingRows.nextSetBit(0); row >= 0; row = remainingRows.nextSetBit(row + 1))
				matrix[row][col] -= min;
		}*/
		if(lb < 0){
			System.out.println("ErrorOutOfEdmondNeg");
			int a =3;
		}
		//System.out.println("ActualBoundChangeLB: " + lb);

		return new Result(lb, matrix, null);
	}

	private BitSet createBitsetFromList(List<Integer> list){
		BitSet bs = new BitSet(n);
		for (int i = 0; i < list.size(); i++) {
			bs.set(list.get(i));
		}
		return bs;
	}

	private void updateMap(BitSet bs, Double value){
		Double old = cycleMap.get(bs);
		//System.out.println("updateMap bs: " + bs.toString() + "penalty " + value + "lb " + lowerBound + "worldindex " + model.getEnvironment().getWorldIndex());
		model.getEnvironment().save(() -> {
			//System.out.println("undo updateMap bs: " + bs.toString() + "penalty " + value  + "worldindex" + model.getEnvironment().getWorldIndex());
			if (old == null) cycleMap.remove(bs);
			else cycleMap.put(bs, old);
		});
		cycleMap.merge(bs, value, Double::sum);
		//cycleMap.put(bs, value);
	}

	private void removeMap(BitSet bs){
		//System.out.println("removeMap bs: " + bs.toString() +  "lb " + lowerBound + "worldindex " + model.getEnvironment().getWorldIndex());
		Double old = cycleMap.get(bs);
		if (old == null) return;
		model.getEnvironment().save(() -> {
			/*int cost = 0;
			for (int i = 0; i < n; i++) {
				Iterator<Integer> it = gV.getMandNeighOf(i).iterator();
				while(it.hasNext()){
					int j = it.next();
					if(originalCostMatrix[i][j]>0){
						cost += originalCostMatrix[i][j];
					}
				}
			}
			//System.out.println("solution found : " + );//"[" + (totalCost.getLB() + M*n) +", " + (totalCost.getUB() + M*n) + "]");
			double reported = (lowerBound - M*n);
			if(reported != cost){
				int a =3;
			}
			System.out.println("[CHECK] reported=" + reported + " real=" + cost);*/
			//System.out.println("undo removeMap bs: " + bs.toString() + "worldindex " + model.getEnvironment().getWorldIndex());
			cycleMap.put(bs, old);
		});
		cycleMap.remove(bs);
	}

	int boundDecreased = 0;

	////////////////////////////////////////
	int M;
	int[][] originalCostMatrix;
	protected PropFusionAsymUndirectedGraphVar(Variable[] vars, int[][] costMatrix) {
		super(vars, PropagatorPriority.QUADRATIC, true);
		graphData = "";
		n = costMatrix.length / 2;
		nRemaining = n;
		originalSmallCosts = new int[n][n];
		originalCostMatrix = costMatrix;
		hung = new HungarianAlgorithm(n);
		M = costMatrix[n][0];
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				if (i == j){
					originalSmallCosts[i][j] = bigValue;
				} else {
					originalSmallCosts[i][j] = costMatrix[i+n][j];
				}
			}
		}


		reducedCostsState = new IStateDouble[n][n];
		for (int i = 0; i < n; i++) {
			//cyclesState[i] = model.getEnvironment().makeBitSet(n);
			//penaltiesState[i] = model.getEnvironment().makeFloat();
			for (int j = 0; j < n; j++) {
				reducedCostsState[i][j] = model.getEnvironment().makeFloat();
			}
		}

		arcsEnforcedFromState = model.getEnvironment().makeIntVector(n, -1);
		lowerBoundState = model.getEnvironment().makeFloat(0);

		costs = new double[n][n];
		reducedCosts = new double[n][n];
		this.onArcRemoved = this::arcRemovedPropagation;
		this.onArcEnforced = this::arcEnforcedPropagation;
	}
	boolean interleave;

	public PropFusionAsymUndirectedGraphVar(UndirectedGraphVar graph, IntVar cost, int[][] costMatrix, boolean interleave) {
		this(new Variable[]{graph, cost}, costMatrix);
		g = graph.getUB();
		gV = graph;
		costVar = cost;
		this.deltaMonitor = gV.monitorDelta(this);
		this.interleave = interleave;
	}

	private void undoEdmondsPenality(int from, int to){

	}

	//***********************************************************************************
	// HK Algorithm(s)
	//***********************************************************************************

	//////////////////////UTILS/////////////

	boolean firstProp = true;
	////////////////////////////////////////
	double baseLowerBound = 0;
	private void enforceInitial() throws ContradictionException {
		 for (int i = 0; i < n; i++) {
        //System.out.println("[FUSION][INIT-ENFORCE] " + (i+n) + " -> " + i);
        gV.enforceArc(i+n, i, this);
        baseLowerBound += M;
        for (int j = 0; j < n; j++) {
            //System.out.println("[FUSION][INIT-REMOVE] " + i + " -> " + j);
            gV.removeArc(i,j, this);
            //System.out.println("[FUSION][INIT-REMOVE] " + (i+n) + " -> " + (j+n));
            gV.removeArc(i+n,j+n, this);
        }
    }
	}

	private void arcRemovedPropagation(int from, int to) throws ContradictionException {
		// TODO
		/*if(gV.getPotNeighOf(from).size() == 2){
			if(g.getNeighOf(from).size() == 2){
				int neigh = g.getNeighOf(from).min();
				if (neigh == from - n)
					neigh = g.getNeighOf(from).max();
				arcEnforcedPropagation(from, neigh);
			}
		}*/

		if (from >= n && to < n) {
			from = from % n;
		}
		else if (from < n && to >= n) {
			int temp = to;
			to = from;
			from = temp % n;
		}
		else{
			return;
			//C'est ok, c'est un arc dans les zones infini
			//throw new RuntimeException();
		}
		if(from == to) return;
		if (arcsEnforcedFromState.quickGet(from) != -1){
			int a =3;
		}

		if(reducedCosts[from][to] >= bigValue*0.9){
			int a =3;
		}
		reducedCosts[from][to] = bigValue;
	}

	int wi = 7;
	private void arcEnforcedPropagation(int from, int to) throws ContradictionException {
		if(model.getEnvironment().getWorldIndex() == wi){
			wi++;
		}

		if (from >= n && to < n) {
			from = from % n;
		}
		else if (from < n && to >= n) {
			int temp = to;
			to = from;
			from = temp % n;
		}
		else{
			//TODO pas normal d'arriver ici
			System.out.println("Error42");
			throw new RuntimeException();
		}

		if(to == 4 || to == 5){
			int a =3;
		}
		if(from == to) return;
		if (arcsEnforcedFromState.quickGet(from) == to) return;
		if (!remainingRows.get(from) || !remainingCols.get(to)) return;

		for (int i = 0; i < n; i++) {
			if(arcsEnforcedFromState.quickGet(i) == to){
				int a =3;
			}
		}

		List<BitSet> bsToRemove = new ArrayList<>();
		for (BitSet bs : cycleMap.keySet()) {
			//Si fait partie du K(S)
			if(bs.get(to) && !bs.get(from)){
				double penalty = cycleMap.get(bs);
				BitSet notBs = (BitSet) bs.clone();
				notBs.flip(0, n);

				for (int i = notBs.nextSetBit(0); i >= 0; i = notBs.nextSetBit(i + 1)) {
					//Compensate for removed row/cols that would be augmented.
					if(arcsEnforcedFromState.quickGet(i) >= 0 && bs.get(arcsEnforcedFromState.quickGet(i))){ //||
						//	g.getNeighOf(i+n).size() == 2 && i != from && (bs.get(g.getNeighOf(i+n).min()) || bs.get(g.getNeighOf(i+n).max()))){
						lowerBound+=penalty;
					}
					/*if(g.getNeighOf(i+n).size() == 2 && i != from && (bs.get(g.getNeighOf(i+n).min()) || bs.get(g.getNeighOf(i+n).max()))){
						lowerBound+=penalty;
					}*/
					if(remainingRows.get(i)){
						for (int j = bs.nextSetBit(0); j >= 0; j = bs.nextSetBit(j + 1)) {
							if(remainingCols.get(j)){
								//System.out.println("i " + i + "j " + j + "before cost" + reducedCosts[i][j]);
								reducedCosts[i][j] += penalty;
								//System.out.println("i " + i + "j " + j + "after cost" + reducedCosts[i][j]);
							}
						}
					}
				}

				lowerBound -= penalty;
				bsToRemove.add(bs);
			}
			/*if(!(bs.get(to) && !bs.get(from))){
				double penalty = cycleMap.get(bs);
				lowerBound -= penalty;
			}*/
		}
		while(!bsToRemove.isEmpty()){
			BitSet bs = bsToRemove.get(0);
			removeMap(bs);
			bsToRemove.remove(bs);
		}

		arcsEnforcedFromState.set(from, to);
		if(remainingRows.get(from) && remainingCols.get(to)){
			remainingRows.clear(from);
			remainingCols.clear(to);
			nRemaining--;
			if(reducedCosts[from][to] > bigValue*0.9){
				int a =3;
			}
			lowerBound += reducedCosts[from][to];
		}
		else{
			int a =3;
		}

		//fusionRelaxationAsym();
	}

	int setRedCount = 0;
	private void setReducedCostsFromState(){
		setRedCount++;
		if(setRedCount == 13){
			int a =3;
		}
		remainingRows = new BitSet(n);
		remainingCols = new BitSet(n);
		remainingRows.flip(0,n);
		remainingCols.flip(0,n);

		for (int i = 0; i < n; i++) {
			if(arcsEnforcedFromState.quickGet(i) != -1){
				if(remainingCols.cardinality() != remainingRows.cardinality()){
					int a =3;
				}
				remainingRows.clear(i);
				remainingCols.clear(arcsEnforcedFromState.quickGet(i));
				if(remainingCols.cardinality() != remainingRows.cardinality()){
					int a =3;
				}
			}
		}
		nRemaining = remainingRows.cardinality();
		for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)) {
			for (int j = remainingCols.nextSetBit(0); j >= 0; j = remainingCols.nextSetBit(j + 1)) {
				reducedCosts[i][j] = reducedCostsState[i][j].get();
			}
		}
		lowerBound = lowerBoundState.get();
	}

	public void propagate(int idVar, int evtMask) throws ContradictionException {
		updateRemaining();
		//System.out.println("worldindex " + model.getEnvironment().getWorldIndex());
		//System.out.println("graph " + g.toString());
		deltaMonitor.freeze();
		try{
			setReducedCostsFromState();

			if(GraphEventType.isRemArc(evtMask)){
				deltaMonitor.forEachArc(onArcRemoved, GraphEventType.REMOVE_ARC);
			}

			if(GraphEventType.isAddArc(evtMask)){
				deltaMonitor.forEachArc(onArcEnforced, GraphEventType.ADD_ARC);
			}
		}
		finally {
			deltaMonitor.unfreeze();
		}

		logState();
		removed = 0;
		fusionRelaxationAsym();
		int a =3;


		//propagate(evtMask);
	}

	public void propagate(int evtmask) throws ContradictionException {
	//	deltaMonitor.unfreeze();
		setReducedCostsFromState();
		remainingRows = new BitSet(n);
		remainingCols = new BitSet(n);
		remainingRows.flip(0,n);
		remainingCols.flip(0,n);
		nRemaining = remainingRows.cardinality();

		//graphData += gV.graphVizExport() + "\n---\n";
		if (firstProp){
			enforceInitial();
			firstProp = false;
		}

		if (waitFirstSol && getModel().getSolver().getSolutionCount() == 0) {
			return;//the UB does not allow to prune
		}
		// initialisation
		setCosts();
		int lb;
		lb = costVar.getLB();
		reducedCosts = Arrays.stream(costs).map(double[]::clone).toArray(double[][]::new);
		lowerBound = M*n;
		fusionRelaxationAsym();
		if(getData){
			getData = false;
		}
		if(firstLb == Double.NEGATIVE_INFINITY){
			firstLb = costVar.getLB();
		}
	}

	private void updateStateVariables(){
		/*int i = 0;
		for (Map.Entry<BitSet, Double> entry : cycleMap.entrySet()) {
			cyclesState[i].set(entry.getKey());
			i++;
		}*/
	}

	int iter = 0;

	int fwRemoves = 0;
	private void filterFloydWarshallNew(double lowerBound, int[] matching) throws ContradictionException {
		// build base matrix restricted to remaining rows/cols
		double[][] W = new double[2*nRemaining][2*nRemaining];
		for (double[] row : W) Arrays.fill(row, bigValue);

		// map: row i -> position ki in [0, nRemaining)
		//      col j -> position kj+nRemaining in [nRemaining, 2*nRemaining)
		int ki = 0;
		for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)) {
			int kj = 0;
			for (int j = remainingCols.nextSetBit(0); j >= 0; j = remainingCols.nextSetBit(j + 1)) {
				// row i -> column j  (forward arc)
				W[ki][kj + nRemaining] = getCostFlow(i, j + n, matching);
				// column j -> row i  (reverse/matching arc)
				W[kj + nRemaining][ki] = getCostFlow(j + n, i, matching);
				kj++;
			}
			ki++;
		}

		for (int idx = 0; idx < 2*nRemaining; idx++) {
			W[idx][idx] = 0;
		}

		for (int k = 0; k < 2*nRemaining; k++) {
			for (int i = 0; i < 2*nRemaining; i++) {
				for (int j = 0; j < 2*nRemaining; j++) {
					W[i][j] = Math.min(W[i][j], W[i][k] + W[k][j]);
				}
			}
		}

		double[][] bigReducedCosts = new double[n][n];
		ki = 0;
		for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)) {
			int kj = 0;
			for (int j = remainingCols.nextSetBit(0); j >= 0; j = remainingCols.nextSetBit(j + 1)) {
				if (i == j) {
					bigReducedCosts[i][j] = bigValue;
				} else {
					// mirrors old: W[j+n][i] + reducedCosts[i][j], with j+n -> kj+nRemaining, i -> ki
					bigReducedCosts[i][j] = W[kj + nRemaining][ki] + reducedCosts[i][j];
				}
				kj++;
			}
			ki++;
		}
		int before = removed;
		basicFiltering(bigReducedCosts, lowerBound);
		fwRemoves += removed - before;
	}

	private double getCostFlow(int from, int to, int[] matching){
		if(from < n && to < n || from >= n && to >= n){
			return bigValue;
		}
		if (from >= n){
			// Should transpose
			if(matching[to] == from-n){
				return 0;
			}
			return bigValue;
		}else{
			if(matching[from] == to-n){
				return bigValue;
			}
			return reducedCosts[from][to-n];
		}
	}

	double lbBegin = 0;
	protected void fusionRelaxationAsym() throws ContradictionException {
		iter++;
		if(iter == 10){
			int a =3;
		}
		double maxLb;
		maxLb = Double.NEGATIVE_INFINITY;
		Result result = null;
		double[][] bestReducedCosts = null;
		int maxNonImprove = 1;
		nbSprints = n;
		//cycleMap = new HashMap<>();
		int nonImprove = 0;
		int i = 0;
		lbBegin = lowerBound;

		while (i < nbSprints && nonImprove < maxNonImprove){
			//updateRemainingArcs();

			if(interleave) {
				double prevLb = lowerBound;
				result = null;//hungarianIteration(reducedCosts);
				lowerBound += result.lb;
				reducedCosts = result.array;
			}
			else{
				result = hungarianSSP(reducedCosts);
				lowerBound += result.lb;
				reducedCosts = result.array;
				basicFiltering(reducedCosts, lowerBound);
			}

			basicFiltering(reducedCosts, lowerBound);
			if (lowerBound > maxLb) {
				maxLb = lowerBound;
				if (result.matching!= null){
					//bestStarZeros = result.zeros;
				}
				nonImprove = 0;
			}
			else {
				nonImprove++;
			}


			if(interleave){
				result = edmondsIteration(reducedCosts, false, result.matching);
				lowerBound += result.lb;
			} else {
				while(result.lb > 0) {
					result = edmondsIteration(reducedCosts, false, result.matching);
					lowerBound += result.lb;
					basicFiltering(reducedCosts, lowerBound);
				}
			}

			if (lowerBound - Math.floor(lowerBound) < 0.001) {
				lowerBound = Math.floor(lowerBound);
			}


			costVar.updateLowerBound((int) Math.ceil(maxLb), this);
			i++;
		}
        //System.out.println(i);

		if(costVar.getUB() - maxLb < maxLb/2){
			//filterBigReducedCosts(maxLb, bestReducedCosts);
		}

		result = hungarianSSP(reducedCosts);
		lowerBound += result.lb;
		reducedCosts = result.array;

		/*if(lowerBound > lbBegin){
			System.out.println("lbImproved at iter " + iter);
		}*/
		if(removed > 0){
		//	System.out.println("Before FW removed " + removed + " at iter " + iter);
		}
		//System.out.println("RealLowerBound : " + getRealLowerBound(result.zeros)+ " ReportedLowerBound : " + (lowerBound-M*n));
		if((removed > 0)){
			filterFloydWarshallNew(lowerBound, result.matching);
			costVar.updateLowerBound(getRealLowerBound(result.matching)+M*n, this);
		}

		logState();

		if(lbBegin > lowerBound){
		//System.out.println("After logState, lbBegin > lowerBound");
		}
		//filterBigReducedCosts(lowerBound, reducedCosts);

		if(removed > 0){
			if(lbBegin >= lowerBound){
				//System.out.println("FILTERNOCHANGE");
			}
			//System.out.println("After FW removed " + removed + " at iter " + iter);
		}
		removed = 0;
		boundDecreased = 0;
		//count = 0;
		if(maxLb > 5600) {
			int a = 3;
		}
	}
	private void logState() throws ContradictionException {
		updateRemaining();
		for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)) {
			for (int j = remainingCols.nextSetBit(0); j >= 0; j = remainingCols.nextSetBit(j + 1)) {
				reducedCostsState[i][j].set(reducedCosts[i][j]);
			}
		}
		//hungarianIteration(reducedCosts);
		if(lowerBound > lbBegin){
			int a =3;
		}
		lowerBoundState.set(lowerBound);
	}

	private void updateRemaining() throws ContradictionException {
        boolean justAssigned = false;
		for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)) {
			if(g.getNeighOf(i+n).size() == 2){
				int neigh = g.getNeighOf(i+n).min();
				if (neigh == i)
					neigh = g.getNeighOf(i+n).max();

                if(i == 20 && neigh == 18){
                    justAssigned = true;
                }
				for (int j = 0; j < n; j++) {
					if(arcsEnforcedFromState.quickGet(j) == neigh){
						//TODO optimize this, detect this case earlier?
						int a =3;
						System.out.println("Error12");
						this.fails();
					}
				}
				//System.out.println("[FUSION][UPDATEREMAINING-ENFORCE] " + (i+n) + " -> " + neigh);

				gV.enforceArc(i+n, neigh, this);
				arcEnforcedPropagation(i+n, neigh);
				if(reducedCosts[i][neigh] != 0){
					int a =3;
				}
			}
		}
	}

	public int getRealLowerBound(int[] matching){
		int lb = 0;
		for (int i = 0; i < n; i++) {
			if(arcsEnforcedFromState.quickGet(i) != -1){
				lb += originalSmallCosts[i][arcsEnforcedFromState.quickGet(i)];
			}
			else{
				lb += originalSmallCosts[i][matching[i]];
			}

		}
		return lb;
	}


	//OLD*********************


	//***********************************************************************************
	// DETAILS
	//***********************************************************************************

	protected void setCosts() {
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				//TODO à tester ci-dessous
				if(i != j && gV.getUB().isArcOrEdge(i+n,j) /*&& !gV.getLB().arcExists(j,i)*/){
					costs[i][j] = originalSmallCosts[i][j];
				}
				else {
					costs[i][j] = bigValue;
				}
			}
		}
	}

	//***********************************************************************************
	// INFERENCE
	//***********************************************************************************
	public void remove(int from, int to) throws ContradictionException {
		//System.out.println("[FUSION][REMOVE] " + from + " -> " + to);
		removed++;
		gV.removeArc(from, to, this);
	}

	public void enforce(int from, int to) throws ContradictionException {
		//System.out.println("[FUSION][ENFORCE] " + from + " -> " + to);
		gV.enforceArc(from, to, this);
	}

	public void contradiction() throws ContradictionException {
		fails();
	}

	//***********************************************************************************
	// PROP METHODS
	//***********************************************************************************

	@Override
	public int getPropagationConditions(int vIdx) {
		if (vIdx == 0) {
			return GraphEventType.REMOVE_ARC.getMask() + GraphEventType.ADD_ARC.getMask();
		} else {
			return IntEventType.boundAndInst();
		}
	}

	@Override
	public ESat isEntailed() {
		return ESat.TRUE;// it is just implied filtering
	}

	public boolean isMandatory(int i, int j) {
		return gV.getMandNeighOf(i).contains(j);
	}
}
