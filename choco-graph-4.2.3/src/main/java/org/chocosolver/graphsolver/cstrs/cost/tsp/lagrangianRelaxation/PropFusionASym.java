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
import org.chocosolver.graphsolver.variables.DirectedGraphVar;
import org.chocosolver.graphsolver.variables.GraphEventType;
import org.chocosolver.solver.constraints.Propagator;
import org.chocosolver.solver.constraints.PropagatorPriority;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.solver.variables.Variable;
import org.chocosolver.solver.variables.events.IntEventType;
import org.chocosolver.util.ESat;
import org.chocosolver.util.objects.graphs.DirectedGraph;
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
import java.util.TreeMap;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * TSP Lagrangian relaxation
 * Inspired from the work of Held & Karp
 * and Benchimol et. al. (Constraints 2012)
 *
 * @author Jean-Guillaume Fages
 */
public class PropFusionASym extends Propagator<Variable> implements GraphLagrangianRelaxation {

	//***********************************************************************************
	// VARIABLES
	//***********************************************************************************

	protected DirectedGraph g;
	protected DirectedGraphVar gV;
	protected IntVar costVar;
	protected int n;
	protected int[][] originalCosts;
	protected double[][] costs;
	protected double[][] reducedCosts;
	protected double[] penalities;
	protected double totalPenalities;
	protected UndirectedGraph mst;
	protected TIntArrayList mandatoryArcsList;
	protected double step;
	protected AbstractTreeFinder HKfilter, HK;
	protected boolean waitFirstSol;
	protected int nbSprints;
	private static int bigValue = 99999999;
	public double firstLb = Double.NEGATIVE_INFINITY;
	public int[][] bestStarZeros;
	private HashSet<Integer> remainingRows;
	private HashSet<Integer> remainingCols;

	// DataFirstIter
	private boolean getData = true;
	private long startTime;
	public List<Integer> dataTime;
	public List<Integer> dataBound;
	public List<Boolean> dataIsHungarian;
	public String graphData;
	//True : Hung
	//False: Edmond

	//***********************************************************************************
	// CONSTRUCTORS
	//***********************************************************************************

	public Result hungarianIteration(double[][] costs) {
		int n = costs.length;
		int m = costs[0].length;

		double lb = 0.0;

		// Subtract minimum value from each row
		for (int i = 0; i < n; i++) {
			double min = Double.POSITIVE_INFINITY;
			for (int j = 0; j < n; j++)
				min = Math.min(min, costs[i][j]);

			lb += min;
			for (int j = 0; j < n; j++) {
				costs[i][j] -= min;
			}
		}

		// Subtract minimum value from each column
		for (int j = 0; j < n; j++) {
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
									zeros[i][j] = 1;

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
		public final double lb;
		public final double[][] array;
		public final int[][] zeros;

		public Result(double lb, double[][] array, int[][] zeros) {
			this.lb = lb;
			this.array = array;
			this.zeros = zeros;
		}

		public Result(int lb, int[][] array, int[][] zeros) {
			this.lb = lb;
			this.array = Arrays.stream(array)
				.map(row -> Arrays.stream(row)
					.asDoubleStream()
					.toArray())
				.toArray(double[][]::new);;
			this.zeros = zeros;
		}
	}

	public static List<Integer> dfsFindCycle(int[][] matrix, int node, Set<Integer> visited,
											 Map<Integer, Integer> parent, Set<Integer> recStack) {
		visited.add(node);
		recStack.add(node);

		for (int i = 0; i < matrix.length; i++) {
			if (matrix[node][i] == 1) {
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

	public void basicFiltering(double[][] reducedCostsArray, double lowerBound) throws ContradictionException {
		double delta = costVar.getUB() - lowerBound;
		if (delta < 0){
			throw new ContradictionException();
		}
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				if (gV.getUB().isArcOrEdge(i,j) && i != j && reducedCostsArray[i][j] > delta) {
					reducedCostsArray[i][j] = bigValue;
					removed++;
						remove(i, j);
				}
			}
		}
		//mandFiltering();
	}

	public void mandFiltering() throws ContradictionException {
		for (int i = 0; i < n; i++) {
			ISet succ = gV.getPotSuccOf(i);
			ISet pred = gV.getPotPredOf(i);
			if(succ.size() == 1){
				gV.enforceArc(i, succ.min(), this);
			}

			if(pred.size() == 1){
				gV.enforceArc(pred.min(), i, this);
			}
		}
	}

	private HashMap<List<Integer>, Double> cycleMap = new HashMap<>();

	public Result edmondsIteration(
			double[][] matrix,
			boolean ignoreStars,
			int[][] starZeros
	) throws ContradictionException {
		if(starZeros == null && !ignoreStars /*|| countStars(starZeros) < n*/){
			return new Result(0, matrix, null);
		}

		int n = matrix.length;
		double lb = 0;

		int[][] edges;
		if(!ignoreStars){
			edges = starZeros;
		} else {
			edges = new int[n][n];
			for (int j = 0; j <n; j++) {
				//Does not add to edges columns with multiple zeroes, they will not do anything
				int numOfZeros = 0;
				for (int i = 0; i <n; i++) {
					if(matrix[i][j] == 0){
						numOfZeros++;
					}
				}
				if (numOfZeros == 1){
					for (int i = 0; i <n; i++) {
						if(matrix[i][j] == 0){
							edges[i][j] = 1;
						}
					}
				}
			}
		}
		//Force 1-tree, maybe not necessary
			/*	new int[n - 1][n - 1];
		for (int i = 1; i < n; i++)
			System.arraycopy(starZeros[i], 1, edges[i - 1], 0, n - 1);*/

		Set<Integer> visited = new HashSet<>();
		 List<List<Integer>> cycles = new ArrayList<>();

		// Find cycle
		for (int i = 0; i < edges.length; i++) {
			if (!visited.contains(i) /*&& cycle == null*/) {
				List<Integer> cycle = dfsFindCycle(edges, i, visited,
						new HashMap<>(), new HashSet<>());
				if (cycle != null && cycle.size() < n) {
					cycles.add(cycle);
				}
			}
		}

		//TODO peut-être refactor ici pour ne pas utiliser les masques, il doit y avoir plus efficace en java
		// Utiliser tuples pour cycleEdgesMask

		for(List<Integer> cycle : cycles){
			if (cycle.size() > 2){
				int a =3;
			}
			boolean[][] cycleEdgesMask =
					new boolean[edges.length][edges[0].length];

			for (int col : cycle)
				for (int row = 0; row < edges.length; row++)
					cycleEdgesMask[row][col] = true;

			for (int i = 0; i < cycle.size(); i++) {
				int from = cycle.get(i);
				int to = cycle.get((i+1) % cycle.size());
				cycleEdgesMask[from][to] = false;
			}

			List<Double> minimumCandidates = new ArrayList<>();


			/*for (int i = 0; i < edges.length; i++)
				for (int j = 0; j < edges[0].length; j++)
					if (cycleEdgesMask[i][j])
						minimumCandidates.add(matrix[i][j]);*/

			for (int i = 0; i < edges.length; i++) {
				for (int j = 0; j < edges.length; j++) {
					if (!cycle.contains(i) && cycle.contains(j)){
						minimumCandidates.add(matrix[i][j]);
					}
				}
			}

			double minimum = Collections.min(minimumCandidates);
			if (minimum > bigValue*0.9){
				//Implique que la meilleure alternative est un infini, donc on est obligé de rester dans le cycle. Contradiction
				throw new ContradictionException();
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
			for (int i : cycle) {
				for(int j : cycle){
					if (i != j) {
						updated++;
						matrix[i][j] += minimum;
					}
				}
			}
			int a =3;

			double boundChange = minimum * (cycle.size() - 1);
			lb -= boundChange;

			// For logging cycle changes
			boundDecreased += boundChange;
			int minIndex = cycle.indexOf(Collections.min(cycle));
			for (int i = 0; i < minIndex; i++) {
				cycle.add(cycle.get(0));
				cycle.remove(0);
			}
			if (minimum != 0){
				cycleMap.merge(cycle, boundChange, Double::sum);
			}


			for (int col = 0; col < n; col++) {
				double min = Double.POSITIVE_INFINITY;
				for (int row = 0; row < n; row++)
					min = Math.min(min, matrix[row][col]);

				lb += min;

				for (int row = 0; row < n; row++)
					matrix[row][col] -= min;
			}
		}

		// Column reduction
		for (int col = 0; col < n; col++) {
			double min = Double.POSITIVE_INFINITY;
			for (int row = 0; row < n; row++)
				min = Math.min(min, matrix[row][col]);

			lb += min;

			for (int row = 0; row < n; row++)
				matrix[row][col] -= min;
		}

		return new Result(lb, matrix, null);
	}

	int boundDecreased = 0;

	////////////////////////////////////////
	protected PropFusionASym(Variable[] vars, int[][] costMatrix) {
		super(vars, PropagatorPriority.CUBIC, false);
		graphData = "";
		n = costMatrix.length;
		originalCosts = costMatrix;
		costs = new double[n][n];
		reducedCosts = new double[n][n];
		totalPenalities = 0;
		penalities = new double[n];
		mandatoryArcsList = new TIntArrayList();
		HK = new PrimOneTreeFinder(n, this);
		HKfilter = new KruskalOneTree_GAC(n, this);
	}
	boolean interleave;

	public PropFusionASym(DirectedGraphVar graph, IntVar cost, int[][] costMatrix, boolean interleave) {
		this(new Variable[]{graph, cost}, costMatrix);
		g = graph.getUB();
		gV = graph;
		costVar = cost;
		this.interleave = interleave;
	}

	//***********************************************************************************
	// HK Algorithm(s)
	//***********************************************************************************

	//////////////////////UTILS/////////////


	public static Result edmondsFull(double[][] matrix)  {
		int lb = 0;
		int root = 0;
		int n = matrix.length;
		double[][] reduced = new double[n][n];
		for (int i = 0; i < n; i++)
			reduced[i] = matrix[i].clone();

		// Step 1: Column reduction — subtract min incoming for each non-root node
		for (int v = 0; v < n; v++) {
			double minCost = Double.POSITIVE_INFINITY;
			for (int u = 0; u < n; u++)
				if (u != v) minCost = Math.min(minCost, reduced[u][v]);
			if (minCost == Double.POSITIVE_INFINITY) return null; // no arborescence
			for (int u = 0; u < n; u++)
				reduced[u][v] -= minCost;
			lb += minCost;
		}

		// Build adjacency matrix of zeros (min incoming edges) for dfsFindCycle
		int[][] edges = new int[n][n];
		int[] minParent = new int[n];
		for (int v = 0; v < n; v++) {
			if (v == root) continue;
			for (int u = 0; u < n; u++) {
				if (u != v && reduced[u][v] == 0) {
					edges[u][v] = 1;
					minParent[v] = u;
					break;
				}
			}
		}

		// Step 2: Find cycle using dfsFindCycle
		Set<Integer> visited = new HashSet<>();
		List<Integer> cycle = null;
		for (int i = 0; i < n; i++) {
			if (!visited.contains(i)) {
				List<Integer> c = dfsFindCycle(edges, i, visited, new HashMap<>(), new HashSet<>());
				if (c != null) { cycle = c; break; }
			}
		}

		// No cycle → reduced costs are already valid, return them
		if (cycle == null) return new Result(lb, reduced, null);

		// Step 3: Contract cycle — adjust entering edge costs
		boolean[] inCycle = new boolean[n];
		for (int v : cycle) inCycle[v] = true;

		// Build contracted graph (cycle → supernode n)
		double[][] newMatrix = new double[n + 1][n + 1];
		for (double[] row : newMatrix) Arrays.fill(row, bigValue);
		int[] cycleEnter = new int[n];
		int[] cycleOut = new int[n];
		for (int u = 0; u < n; u++) {
			for (int v = 0; v < n; v++) {
				if (reduced[u][v] == bigValue) continue;
				int newU = u;
				int newV = v;

				if(inCycle[u]){
					newU = n;
				}

				if(inCycle[v]){
					newV = n;
				}

				if (newU == newV) continue;
				if (reduced[u][v] < newMatrix[newU][newV]){
					//if(newU == n)
					//	cycleOut[u] = v;
					if(newV == n)
						cycleEnter[u] = v;
					newMatrix[newU][newV] = reduced[u][v];
				}

			}
		}

		Result result = edmondsFull(newMatrix);
		lb += result.lb;
		double[][] contractedReduced = result.array;
		if (contractedReduced == null) return null;

		// Step 4: Expand back — map contracted reduced costs back to original nodes
		for (int u = 0; u < n; u++) {
			for (int v = 0; v < n; v++) {
				if (cycle.contains(u) || cycle.contains(v)) continue;
				reduced[u][v] = contractedReduced[u][v];
			}
			// Edges enter cycle
			for (int v : cycle) {
				//TODO ICI soustraire le minimum, réfléchir à comment faire ça similaire à la méthode itération
				//reduced[u][v] -= (reduced[cycleEnter[v]][v] - contractedReducedt) ;
			}

			//Edges out cycle ??
		}
		result = new Result(lb, reduced, null);
		return result;
	}



	private void fillDiagonal(double[][] matrix, double value){
		for (int i = 0; i < matrix.length; i++) {
			matrix[i][i] = value;
		}
	}

	////////////////////////////////////////
	public void propagate(int evtmask) throws ContradictionException {
		//graphData += gV.graphVizExport() + "\n---\n";

		if (waitFirstSol && getModel().getSolver().getSolutionCount() == 0) {
			return;//the UB does not allow to prune
		}
		// initialisation
		rebuild();
		setCosts();
		//edmondsFull(costs);
		updateRemainingArcs();
		int lb;
		lb = costVar.getLB();

		fusionRelaxationAsym();
		if(getData){
			getData = false;
		}
		if(firstLb == Double.NEGATIVE_INFINITY){
			firstLb = costVar.getLB();
		}
		//System.out.println("removed " + gV.removed);
	}

	int iter = 0;

	private void filterBigReducedCosts(double lowerBound, double[][] rc) throws ContradictionException {
		double[][] reducedCostsClone = Arrays.stream(rc).map(double[]::clone).toArray(double[][]::new);
		double[][] bigReducedCosts = new double[n][n];

		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				bigReducedCosts[i][j] = getBigReducedCostValue(i, j, reducedCostsClone, rc);
			}
		}

		basicFiltering(bigReducedCosts, lowerBound);
	}

	private double getBigReducedCostValue(int i, int j, double[][] reducedCostsClone, double[][] originalRc){
		for (int ii = 0; ii < n; ii++) {
			if (ii != i){
				reducedCostsClone[ii][j] = bigValue;
			}
		}
		for (int jj = 0; jj < n; jj++) {
			if(jj != j){
				reducedCostsClone[i][jj] = bigValue;
			}
		}
		double lb = 0;
		int bigHungarianIterations = 10;
		double[][] rc = reducedCostsClone;
		for (int k = 0; k < bigHungarianIterations; k++) {
			Result result = hungarianIteration(rc);
			rc = result.array;
			lb += result.lb;
		}

		for (int ii = 0; ii < n; ii++) {
			for (int jj = 0; jj < n; jj++) {
				reducedCostsClone[ii][jj] = originalRc[ii][jj];
			}
		}

		return lb;
	}

	public static String get2DArrayPrint(double[][] matrix) {
		String output = new String();
		for (int i = 0; i < matrix.length; i++) {
			for (int j = 0; j < matrix[i].length; j++) {
				output = output + (matrix[i][j] + "\t");
			}
			output = output + "\n";
		}
		return output;
	}

	protected void fusionRelaxationAsym() throws ContradictionException {
		iter++;
		double lowerBound = 0;
		double alpha = 2;
		double beta = 0.5;
		double maxLb;
		maxLb = 0;
		Result result = null;
		double[][] bestReducedCosts = null;
		reducedCosts = Arrays.stream(costs).map(double[]::clone).toArray(double[][]::new);
		int maxNonImprove = 1;
		nbSprints = n;
		cycleMap = new HashMap<>();
		int nonImprove = 0;
		int i = 0;
		/*if(getData){
			dataBound = new ArrayList<>();
			dataTime = new ArrayList<>();
			dataIsHungarian = new ArrayList<>();
			startTime = System.currentTimeMillis();
		}*/

		while (i < nbSprints && nonImprove < maxNonImprove){
			updateRemainingArcs();
			if(interleave) {
				result = hungarianIteration(reducedCosts);
				lowerBound += result.lb;
				reducedCosts = result.array;
				/*if(getData){
					dataBound.add((int) lowerBound);
					dataTime.add((int) (System.currentTimeMillis() - startTime));
					dataIsHungarian.add(true);
				}*/
			}

			else{
				while(result == null || result.lb > 0) {
					result = hungarianIteration(reducedCosts);
					lowerBound += result.lb;
					reducedCosts = result.array;
					basicFiltering(reducedCosts, lowerBound);
					/*if(getData){
						dataBound.add((int) lowerBound);
						dataTime.add((int) (System.currentTimeMillis() - startTime));
						dataIsHungarian.add(true);
					}*/
				}
			}
			if(result.zeros != null && countStars(result.zeros) == n){
				// Ceci n'est pas inquiétant. À regarder les cas où realLb > lowerbound, probablement du à des augmentations de cycle qu'on peut enlever.
				int realLb = getRealLowerBound(result.zeros);
				if(realLb < lowerBound){
					if(lowerBound - realLb != boundDecreased){
						int d =3;
					}
					int a = 3;
				}
			}
			basicFiltering(reducedCosts, lowerBound);

			if (lowerBound > maxLb) {
				maxLb = lowerBound;
				if (result.zeros != null){
					bestStarZeros = result.zeros;
				}
				if(result.zeros != null && countStars(result.zeros) == n){
					int sum = 0;
					for (int ii = 0; ii < n; ii++) {
						for (int j = 0; j < n; j++) {
							if (result.zeros[ii][j] == 1){
								sum += originalCosts[ii][j];
							}

						}
					}

					if(sum < lowerBound){
						int a =3;
					}
				}
				bestReducedCosts = reducedCosts.clone();
				nonImprove = 0;
			}
			else {
				nonImprove++;
			}
			if(interleave){
				result = edmondsIteration(reducedCosts, false,result.zeros);
				lowerBound += result.lb;
				/*if(getData){
					dataBound.add((int) lowerBound);
					dataTime.add((int) (System.currentTimeMillis() - startTime));
					dataIsHungarian.add(false);
				}*/

			} else {
				result = null;
				while(result == null || result.lb > 0) {
					result = edmondsIteration(reducedCosts, true/*true*/, null/*result.zeros*/);
					lowerBound += result.lb;
					/*if(getData){
						dataBound.add((int) lowerBound);
						dataTime.add((int) (System.currentTimeMillis() - startTime));
						dataIsHungarian.add(false);
					}*/

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


		//System.out.println(removed);
		/*if(costVar.getUB() - maxLb < maxLb/2){
			filterBigReducedCosts(maxLb, bestReducedCosts);
		}*/



		filterBigReducedCosts(lowerBound, reducedCosts);
		removed = 0;
		boundDecreased = 0;
		if(maxLb > 5600) {
			int a = 3;
		}
	}


	public int getRealLowerBound(int[][] starZeros){
		int lb = 0;
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				if(starZeros[i][j] == 1){
					lb += originalCosts[i][j];
				}
			}
		}
		return lb;
	}


	//OLD*********************


	//***********************************************************************************
	// DETAILS
	//***********************************************************************************

	protected void rebuild() {
		mandatoryArcsList.clear();
		ISet nei;
		for (int i = 0; i < n; i++) {
			nei = gV.getMandSuccOf(i);
			for (int j : nei) {
				if (i < j) {
					mandatoryArcsList.add(i * n + j);
				}
			}
		}
	}

	protected void setCosts() {
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				//TODO à tester ci-dessous
				if(i != j && gV.getUB().arcExists(i,j) /*&& !gV.getLB().arcExists(j,i)*/){
					costs[i][j] = originalCosts[i][j];
				}
				else {
					costs[i][j] = bigValue;
				}
			}
		}
	}


	protected void updateRemainingArcs() {
		remainingRows = IntStream.rangeClosed(0, n-1)
                                .boxed()
                                .collect(Collectors.toCollection(HashSet::new));

		remainingCols = IntStream.rangeClosed(0, n-1)
				.boxed()
				.collect(Collectors.toCollection(HashSet::new));

		for (int i = 0; i < n; i++) {
			if(!gV.getMandSuccOf(i).isEmpty()){
				//un seul élément
				int j = gV.getMandSuccOf(i).min();
				remainingRows.remove(i);
				remainingCols.remove(j);
			}
		}
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
		return -(((double) costVar.getUB()) + totalPenalities);
	}

	public TIntArrayList getMandatoryArcsList() {
		return mandatoryArcsList;
	}

	public boolean isMandatory(int i, int j) {
		return gV.getMandSuccOf(i).contains(j);
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
}
