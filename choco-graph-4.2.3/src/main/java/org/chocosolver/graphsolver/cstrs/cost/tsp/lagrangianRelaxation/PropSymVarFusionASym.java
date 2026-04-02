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

import gnu.trove.list.array.TIntArrayList;
import org.chocosolver.graphsolver.cstrs.cost.GraphLagrangianRelaxation;
import org.chocosolver.graphsolver.cstrs.cost.trees.lagrangianRelaxation.AbstractTreeFinder;
import org.chocosolver.graphsolver.variables.GraphEventType;
import org.chocosolver.graphsolver.variables.UndirectedGraphVar;
import org.chocosolver.solver.constraints.Propagator;
import org.chocosolver.solver.constraints.PropagatorPriority;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.solver.variables.Variable;
import org.chocosolver.solver.variables.events.IntEventType;
import org.chocosolver.util.ESat;
import org.chocosolver.util.objects.graphs.UndirectedGraph;
import org.chocosolver.util.objects.setDataStructures.ISet;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * TSP Lagrangian relaxation
 * Inspired from the work of Held & Karp
 * and Benchimol et. al. (Constraints 2012)
 *
 * @author Jean-Guillaume Fages
 */
public class PropSymVarFusionASym extends Propagator<Variable> implements GraphLagrangianRelaxation {

	//***********************************************************************************
	// VARIABLES
	//***********************************************************************************

	protected UndirectedGraph g;
	protected UndirectedGraphVar gV;
	protected IntVar obj;
	protected int n;
	protected int[][] originalBigCosts;
	protected double[][] bigCosts;
	protected int[][] smallAsymCosts;
	protected int[][] originalSmallAsymCosts;
	protected int lowerBoundAB;
	protected double[] penalities;
	protected double totalPenalities;
	protected UndirectedGraph mst;
	protected TIntArrayList mandatoryArcsList;
	protected double step;
	protected AbstractTreeFinder HKfilter, HK;
	protected boolean waitFirstSol;
	protected int nbSprints;
	private int M = 1000000;
	private int bigValue = 999999999;

	public double firstLb = Integer.MIN_VALUE;
	//***********************************************************************************
	// CONSTRUCTORS
	//***********************************************************************************

	protected PropSymVarFusionASym(Variable[] vars, int[][] costMatrix) {
		super(vars, PropagatorPriority.CUBIC, false);
		originalSmallAsymCosts = costMatrix;
		n = originalSmallAsymCosts.length;
		smallAsymCosts = new int[n][n];
		bigCosts = new double[2*n][2*n];
		totalPenalities = 0;
		penalities = new double[2*n];
		mandatoryArcsList = new TIntArrayList();
		nbSprints = 30;
		HK = new PrimOneTreeFinder(2*n, this);
		HKfilter = new KruskalOneTree_GAC(2*n, this);
	}

	public PropSymVarFusionASym(UndirectedGraphVar graph, IntVar cost, int[][] costMatrix) {
		this(new Variable[]{graph, cost}, costMatrix);
		g = graph.getUB();
		gV = graph;
		obj = cost;
	}

	//***********************************************************************************
	// HK Algorithm(s)
	//***********************************************************************************
	private int[][] makeBenchMatrix(int[][] data){
		int[][] bench = new int[2*n][2*n];
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				//Bottom left
				bench[i+n][j] = data[i][j];
				//Top right
				bench[i][j+n] = data[j][i];

				bench[i][j] = bigValue;
				bench[i+n][j+n] = bigValue;
			}
			bench[i+n][i] = -M;
			bench[i][i+n] = -M;
		}
		return bench;
	}

	public void propagate(int evtmask) throws ContradictionException {
		if (waitFirstSol && getModel().getSolver().getSolutionCount() == 0) {
			return;//the UB does not allow to prune
		}
		// initialisation
		prepareSmallCosts();
		int[][] reducedCosts = solveAdditiveBounding();
		originalBigCosts = makeBenchMatrix(reducedCosts);

		rebuild();
		updateBigCosts();
		int lb;

		do {
			lb = obj.getLB();
			lagrangianRelaxation();
		} while (lb < obj.getLB());

		System.out.println(gV.removed);
		gV.removed = 0;

		if (firstLb == Integer.MIN_VALUE){
			firstLb = obj.getLB();
		}
		//System.out.println("removed " + gV.removed);
	}

	double hkb;
	protected void lagrangianRelaxation() throws ContradictionException {
		double alpha = 2;
		double beta = 0.5;
		double bestHKB;
		bestHKB = 0;
		HKfilter.computeMST(bigCosts, g);
		hkb = HKfilter.getBound() - totalPenalities;
		bestHKB = hkb;
		mst = HKfilter.getMST();
		if (hkb - Math.floor(hkb) < 0.001) {
			hkb = Math.floor(hkb);
		}
		obj.updateLowerBound((int) Math.ceil(hkb) + lowerBoundAB, this);
		HKfilter.performPruning((double) (obj.getUB()) + totalPenalities + 0.001 - lowerBoundAB);
		for (int iter = 5; iter > 0; iter--) {
			for (int i = nbSprints; i > 0; i--) {
				HK.computeMST(bigCosts, g);
				hkb = HK.getBound() - totalPenalities;
				if (hkb > bestHKB + 1) {
					bestHKB = hkb;
				}
				mst = HK.getMST();
				if (hkb - Math.floor(hkb) < 0.001) {
					hkb = Math.floor(hkb);
				}
				obj.updateLowerBound((int) Math.ceil(hkb) + lowerBoundAB, this);
				// HK.performPruning((double) (obj.getUB()) + totalPenalities + 0.001);
				//	DO NOT FILTER HERE TO SPEED UP CONVERGENCE (not always true)
				updateStep(hkb, alpha);
				HKPenalities();
				updateBigCosts();
			}
			HKfilter.computeMST(bigCosts, g);
			hkb = HKfilter.getBound() - totalPenalities;
			if (hkb > bestHKB + 1) {
				bestHKB = hkb;
			}
			mst = HKfilter.getMST();
			if (hkb - Math.floor(hkb) < 0.001) {
				hkb = Math.floor(hkb);
			}
			obj.updateLowerBound((int) Math.ceil(hkb) + lowerBoundAB, this);
			HKfilter.performPruning((double) (obj.getUB()) + totalPenalities + 0.001 - lowerBoundAB);
			updateStep(hkb, alpha);
			HKPenalities();
			updateBigCosts();
			alpha *= beta;
			beta /= 2;

		}
	}

	//***********************************************************************************
	// DETAILS
	//***********************************************************************************

	protected void rebuild() {
		mandatoryArcsList.clear();
		ISet nei;
		for (int i = 0; i < n*2; i++) {
			nei = gV.getMandNeighOf(i);
			for (int j : nei) {
				if (i < j) {
					mandatoryArcsList.add(i * n*2 + j);
				}
			}
		}
	}

	protected void updateBigCosts() {
		ISet nei;
		for (int i = 0; i < n*2; i++) {
			nei = g.getNeighOf(i);
			for (int j : nei) {
				if (i < j) {
					bigCosts[i][j] = Math.max(originalBigCosts[i][j] + penalities[i] + penalities[j], Integer.MIN_VALUE);
					bigCosts[j][i] = bigCosts[i][j];
				}
			}
		}
	}

	protected void prepareSmallCosts() {
		ISet nei;
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				if(i != j && g.edgeExists(n+i, j)){
					smallAsymCosts[i][j] = originalSmallAsymCosts[i][j];
				} else{
					smallAsymCosts[i][j] = bigValue;
				}
			}
		}
	}

	protected void updateStep(double hkb, double alpha) {
		double nb2viol = 0;
		double target = obj.getUB();
		if (target - hkb < 0) {
			target = hkb + 0.1;
		}
		int deg;
		for (int i = 0; i < n*2; i++) {
			deg = mst.getNeighOf(i).size();
			nb2viol += (2 - deg) * (2 - deg);
		}
		if (nb2viol == 0) {
			step = 0;
		} else {
			step = alpha * (target - hkb) / nb2viol;
		}
	}

	protected void HKPenalities() {
		if (step == 0) {
			return;
		}
		double sumPenalities = 0;
		int deg;
		for (int i = 0; i < n*2; i++) {
			deg = mst.getNeighOf(i).size();
			penalities[i] += (deg - 2) * step;
			assert !(penalities[i] > Double.MAX_VALUE / (n*2 - 1) || penalities[i] < -Double.MAX_VALUE / (n*2 - 1)) :
					"Extreme-value lagrangian multipliers. Numerical issue may happen";
			sumPenalities += penalities[i];
		}
		this.totalPenalities = 2 * sumPenalities;
	}



	//***********************************************************************************
	// INFERENCE
	//***********************************************************************************

	public void remove(int from, int to) throws ContradictionException {
		gV.removeArc(from, to, this);
	}

	public void enforce(int from, int to) throws ContradictionException {
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

	public double getMinArcVal() {
		return -(((double) obj.getUB()) + totalPenalities);
	}

	public TIntArrayList getMandatoryArcsList() {
		return mandatoryArcsList;
	}

	public boolean isMandatory(int i, int j) {
		return gV.getMandNeighOf(i).contains(j);
	}

	public void waitFirstSolution(boolean b) {
		waitFirstSol = b;
	}

	public boolean contains(int i, int j) {
		return mst == null || mst.edgeExists(i, j);
	}

	public UndirectedGraph getSupport() {
		return mst;
	}

	public double getReplacementCost(int from, int to) {
		return HKfilter.getRepCost(from, to);
	}

	public double getMarginalCost(int from, int to) {
		return HKfilter.getRepCost(from, to);
	}

	//********ADDITIVEBOUNDING PROCEDURE
	protected int[][] solveAdditiveBounding() throws ContradictionException {
		int lowerBound = 0;
		int maxLb;
		maxLb = -1;
		Result result;
		int[][] bestReducedCosts = null;
		int[][] reducedCosts = Arrays.stream(smallAsymCosts).map(int[]::clone).toArray(int[][]::new);
		int[][] bestStarZeros = null;
		int maxNonImprove = 30;
		nbSprints = 100;
		int nonImprove = 0;
		int i = 0;
		while (i < nbSprints && nonImprove < maxNonImprove){
			result = hungarianIteration(reducedCosts);
			lowerBound += result.lb;
			reducedCosts = result.array;

			if (lowerBound > maxLb) {
				maxLb = lowerBound;
				if (result.zeros != null){
					bestStarZeros = result.zeros;
				}
				bestReducedCosts = reducedCosts.clone();
				nonImprove = 0;
			}
			else {
				nonImprove++;
			}

			result = edmondsIteration(reducedCosts, true, result.zeros);
			lowerBound += result.lb;

			i++;
		}

		removed = 0;
		lowerBoundAB = maxLb;
		return bestReducedCosts;
	}



	//*****ADDITIVEBOUNDING STUFF*******//


	public static Result hungarianIteration(int[][] costs) {
		int n = costs.length;
		int m = costs[0].length;

		int lb = 0;

		// Subtract minimum value from each row
		for (int i = 0; i < n; i++) {
			double min = Double.POSITIVE_INFINITY;
			for (int j = 0; j < m; j++)
				min = Math.min(min, costs[i][j]);

			lb += min;
			for (int j = 0; j < m; j++) {
				costs[i][j] -= min;
			}
		}

		// Subtract minimum value from each column
		for (int j = 0; j < m; j++) {
			double min = Double.POSITIVE_INFINITY;
			for (int i = 0; i < n; i++)
				min = Math.min(min, costs[i][j]);

			lb += min;
			for (int i = 0; i < n; i++)
				costs[i][j] -= min;
		}

		int[][] zeros = new int[n][m]; // 0 = empty, 1 = star, 2 = prime
		boolean[] rowCovered = new boolean[n];
		boolean[] colCovered = new boolean[m];

		//Fais cette étape seulement si la précédente n'a pas modifié la borne
		if (true/*lb == 0*/) {

			// Star a zero in each row
			for (int i = 0; i < n; i++) {
				boolean zeroAssigned = false;
				for (int j = 0; j < m && !zeroAssigned; j++) {
					if (costs[i][j] == 0 && !columnHasStar(zeros, j)) {
						zeros[i][j] = 1;
						zeroAssigned = true;
					}
				}
			}

			boolean gotoCoverCols = true;

			while (gotoCoverCols) {
				gotoCoverCols = false;

				// Cover columns with starred zeros
				for (int i = 0; i < n; i++)
					for (int j = 0; j < m; j++)
						if (zeros[i][j] == 1)
							colCovered[j] = true;

				boolean gotoFindZero = true;

				while (gotoFindZero) {
					gotoFindZero = false;

					for (int i = 0; i < n; i++) {
						for (int j = 0; j < m; j++) {

							if (!gotoCoverCols &&
									costs[i][j] == 0 &&
									!rowCovered[i] &&
									!colCovered[j]) {

								zeros[i][j] = 2;
								int starCol = findStarInRow(zeros, i);
								if (starCol != -1) {
									rowCovered[i] = true;
									colCovered[starCol] = false;
									gotoFindZero = true;
								} else {
									gotoCoverCols = true;

									// Trouver chemin
									int currentRow = i;
									int currentCol = j;
									boolean done = false;

									while (!done) {
										int starRow = findStarInCol(zeros, currentCol, currentRow);
										if (starRow != -1) {
											zeros[starRow][currentCol] = 0;
											currentRow = starRow;

											int primeCol = findPrimeInRow(zeros, currentRow);
											zeros[currentRow][primeCol] = 1;
											currentCol = primeCol;
										} else {
											zeros[currentRow][currentCol] = 1;
											done = true;
										}
									}

									// Unprime all primed and uncover all lines
									for (int ii = 0; ii < n; ii++)
										for (int jj = 0; jj < m; jj++)
											if (zeros[ii][jj] == 2)
												zeros[ii][jj] = 0;

									Arrays.fill(rowCovered, false);
									Arrays.fill(colCovered, false);
								}
							}
						}
					}
				}
			}

			//TODO rendu la
			int starCount = countStars(zeros);
			if (starCount < n) {
				int missing = n - starCount;

				double minimum = Double.POSITIVE_INFINITY;
				for (int i = 0; i < n; i++)
					for (int j = 0; j < m; j++)
						if (!rowCovered[i] && !colCovered[j])
							minimum = Math.min(minimum, costs[i][j]);

				lb += minimum * missing;

				for (int i = 0; i < n; i++) {
					for (int j = 0; j < m; j++) {
						if (!rowCovered[i])
							costs[i][j] -= minimum;
						if (colCovered[j])
							costs[i][j] += minimum;
					}
				}
			}
			return new Result(lb, costs, zeros);
		}
		else{
			return new Result(lb, costs, null);
		}
	}

	private static boolean columnHasStar(int[][] zeros, int col) {
		for (int[] zero : zeros)
			if (zero[col] == 1)
				return true;
		return false;
	}

	private static int findStarInRow(int[][] zeros, int row) {
		for (int j = 0; j < zeros[0].length; j++)
			if (zeros[row][j] == 1)
				return j;
		return -1;
	}

	private static int findStarInCol(int[][] zeros, int col, int rowExcept) {
		for (int i = 0; i < zeros.length; i++)
			if (i != rowExcept && zeros[i][col] == 1)
				return i;
		return -1;
	}

	private static int findPrimeInRow(int[][] zeros, int row) {
		for (int j = 0; j < zeros[0].length; j++)
			if (zeros[row][j] == 2)
				return j;
		return -1;
	}

	private static int countStars(int[][] zeros) {
		int count = 0;
		for (int[] row : zeros)
			for (double v : row)
				if (v == 1)
					count++;
		return count;
	}

	public static class Result {
		public final int lb;
		public final int[][] array;
		public final int[][] zeros;

		public Result(int lb, int[][] array, int[][] zeros) {
			this.lb = lb;
			this.array = array;
			this.zeros = zeros;
		}
	}


	public static List<Integer> dfsFindCycle(int[][] matrix, int node, Set<Integer> visited,
											 Map<Integer, Integer> parent, Set<Integer> recStack) {
		visited.add(node);
		recStack.add(node);

		for (int i = 0; i < matrix.length; i++) {
			if (matrix[node][i] == 1) {

				// If node is in recursion stack → cycle found
				if (recStack.contains(i)) {
					parent.put(i, node);
					int x = i;
					List<Integer> cycle = new ArrayList<>();
					cycle.add(x);

					while (x != node) {
						x = parent.get(x);
						cycle.add(0, x);  // insert at beginning
					}
					return cycle;
				}

				// If not visited → recurse
				if (!visited.contains(i)) {
					parent.put(i, node);
					List<Integer> cycle = dfsFindCycle(matrix, i, visited, parent, recStack);
					if (cycle != null && !cycle.isEmpty()) {
						return cycle;
					}
				}
			}
		}

		recStack.remove(node);
		return null;  // no cycle found
	}

	int removed = 0;

	public static Result edmondsIteration(
			int[][] matrix,
			boolean incrementZeros,
			int[][] starZeros
	) {
		if(starZeros == null){
			return new Result(0, matrix, null);
		}

		int n = matrix.length;
		int lb = 0;

		// Column reduction
		for (int col = 0; col < n; col++) {
			double min = Double.POSITIVE_INFINITY;
			for (int row = 0; row < n; row++)
				min = Math.min(min, matrix[row][col]);

			lb += min;

			for (int row = 0; row < n; row++)
				matrix[row][col] -= min;
		}

		int[][] edges;

		edges = new int[n - 1][n - 1];
		for (int i = 1; i < n; i++)
			System.arraycopy(starZeros[i], 1, edges[i - 1], 0, n - 1);

		Set<Integer> visited = new HashSet<>();
		List<Integer> cycle = null;

		// Find cycle
		for (int i = 0; i < edges.length; i++) {
			if (!visited.contains(i) &&
					(cycle == null || cycle.size() == matrix.length)) {

				cycle = dfsFindCycle(edges, i, visited,
						new HashMap<>(), new HashSet<>());
			}
		}

		//TODO peut-être refactor ici pour ne pas utiliser les masques, il doit y avoir plus efficace en java
		// Utiliser tuples pour cycleEdgesMask

		if (cycle != null && cycle.size() < matrix.length) {

			boolean[][] cycleEdgesMask =
					new boolean[edges.length][edges[0].length];

			for (int col : cycle)
				for (int row = 0; row < edges.length; row++)
					cycleEdgesMask[row][col] = true;

			for (int i = 0; i < cycle.size(); i++) {
				int from = cycle.get(i);
				int to = cycle.get((i + 1) % cycle.size());
				cycleEdgesMask[from][to] = false;
			}

			List<Integer> minimumCandidates = new ArrayList<>();

			for (int i = 0; i < edges.length; i++)
				for (int j = 0; j < edges[0].length; j++)
					if (cycleEdgesMask[i][j])
						minimumCandidates.add(matrix[i+1][j+1]);

			double minimum = Collections.min(minimumCandidates);

			//Check if there's at least one non-zero
			if (incrementZeros && minimum == 0) {

				for (int i = 0; i < n; i++)
					for (int j = 0; j < n; j++)
						if (i != j && matrix[i][j] != 0)
							minimum = 1;
			}

			for (int i = 0; i < cycle.size(); i++) {
				int from = cycle.get(i);
				int to = cycle.get((i + 1) % cycle.size());
				matrix[from+1][to+1] += minimum;
			}

			double boundChange = minimum * (cycle.size() - 1);
			lb -= boundChange;
		}

		return new Result(lb, matrix, null);
	}

}
