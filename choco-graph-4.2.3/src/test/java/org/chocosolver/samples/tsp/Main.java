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

package org.chocosolver.samples.tsp;

import org.chocosolver.graphsolver.GraphModel;
import org.chocosolver.graphsolver.cstrs.cost.tsp.lagrangianRelaxation.PropFusionASym;
import org.chocosolver.graphsolver.cstrs.cost.tsp.lagrangianRelaxation.PropLagr_OneTree;
import org.chocosolver.graphsolver.cstrs.cost.tsp.lagrangianRelaxation.PropSymVarFusionASym;
import org.chocosolver.graphsolver.search.strategy.GraphSearch;
import org.chocosolver.graphsolver.variables.DirectedGraphVar;
import org.chocosolver.graphsolver.variables.UndirectedGraphVar;
import org.chocosolver.solver.Model;
import org.chocosolver.solver.Solver;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.util.objects.graphs.DirectedGraph;
import org.chocosolver.util.objects.graphs.UndirectedGraph;
import org.chocosolver.util.objects.setDataStructures.SetType;
import org.moeaframework.problem.tsplib.TSPInstance;
import org.moeaframework.problem.tsplib.DistanceTable;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Arrays;
import java.util.Random;
import java.util.stream.Collectors;

/**
 * Solves the Traveling Salesman Problem
 * Parses TSP instances of the TSPLIB library
 * See <a href = "http://comopt.ifi.uni-heidelberg.de/software/TSPLIB95/">TSPLIB</a>
 * <p/>
 *
 * This is an exact approach dedicated to prove optimality of a solution.
 * It is assumed that a local search (e.g. LKH) algorithm has been performed
 * as a pre-processing step
 *
 * @author Jean-Guillaume Fages
 * @since Oct. 2012
 */
public class Main {

    //***********************************************************************************
    // MAIN
    //***********************************************************************************

	private static GraphModel model;
	private static IntVar totalCost;
	private static UndirectedGraphVar graph;
	private static DirectedGraphVar digraph;
	private static int LIMIT = 30; // in seconds
	private static int n;
	private static int M = 1000000;
	private static int bigValue = 999999999;
    public static void main(String[] args) throws IOException {
		//randomLoop();
		//results();

		int[][] data = getATSPInstance("test.atsp");
		n = data.length;

		int[][] bench_matrix = makeBenchMatrix(data);
		//	int presolve = TSP_Utils.getOptimum(INSTANCE,REPO+"/bestSols.csv");
		int presolve = 99999999;
		//benchimol(bench_matrix ,presolve);
		fusionAsym(data, presolve);
		//fusionBench(data, bench_matrix, presolve);
    }

	private static void results() throws IOException {
		String[] filenames = getATSPFilenames();
		double[] fusionResults = new double[filenames.length];
		double[] benchResults = new double[filenames.length];
		for (int i = 0; i < filenames.length; i++){
			int[][] data = getATSPInstance(filenames[i]);
			n = data.length;

			int[][] bench_matrix = makeBenchMatrix(data);
			//	int presolve = TSP_Utils.getOptimum(INSTANCE,REPO+"/bestSols.csv");
			int presolve = 9999999;
			benchResults[i] = benchimol(bench_matrix ,presolve);
			fusionResults[i] = fusionAsym(data, presolve);
		}

		try (BufferedWriter bw = new BufferedWriter(new FileWriter("src/results.csv"))) {
			bw.write("," + String.join(",", filenames)); bw.newLine();
			bw.write("benchimol," + Arrays.stream(benchResults)
					.mapToObj(String::valueOf).collect(Collectors.joining(","))); bw.newLine();
			bw.write("maMéthode," + Arrays.stream(fusionResults)
					.mapToObj(String::valueOf).collect(Collectors.joining(","))); bw.newLine();
		}



	}

	private static void randomLoop(){
		n = 4;
		while (true){
			int[][] data = randomMatrix();
			int[][] bench_matrix = makeBenchMatrix(data);
			int presolve = 9999999;
			int solBench = benchimol(bench_matrix ,presolve);
			int solFusion = fusionAsym(data, presolve);

			/*if(solBench != solFusion) {
				int a = 3;
			}*/
		}
	}

	private static int[][] makeBenchMatrix(int[][] data){
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

	private static int seed = 6778;
	public static int[][] randomMatrix() {
		Random rand = new Random(seed);
		seed++;
		int[][] matrix = new int[n][n];

		for (int i = 0; i < n; i++)
			for (int j = 0; j < n; j++)
				if (i == j) {
					matrix[i][i] = 99999;
				} else {
					matrix[i][j] = rand.nextInt(10);
				}

		return matrix;
	}

	private static int[][] getTSPInstance(String name) throws IOException {
		String REPO = "src/test/java/org/chocosolver/samples/tsp";
		org.moeaframework.problem.tsplib.TSPInstance problem = new TSPInstance(new File(REPO + "/" + name + ".tsp"));
		//int[][] data = TSP_Utils.parseInstance(REPO+"/"+INSTANCE+".atsp", 300);
		return getDataFromProblem(problem);
	}

	private static int[][] getATSPInstance(String name) throws IOException {
		String REPO = "src/test/java/org/chocosolver/samples/atsp";
		org.moeaframework.problem.tsplib.TSPInstance problem = new TSPInstance(new File(REPO + "/" + name));
		return getDataFromProblem(problem);
	}
	private static String[] getATSPFilenames() throws IOException {
		String REPO = "src/test/java/org/chocosolver/samples/atsp";
		File dir = new File(REPO);
		return dir.list();
	}

	private static int[][] getDataFromProblem(TSPInstance problem){
		DistanceTable temp = problem.getDistanceTable();
		int[][] data = new int[temp.listNodes().length][temp.listNodes().length];
		for (int i = 0; i < temp.listNodes().length; i++) {
			for (int j = 0; j < temp.listNodes().length; j++) {
				data[i][j] = (int) temp.getDistanceBetween(i+1,j+1);
			}
		}
		return data;
	}

    //***********************************************************************************
    // SOLVER
    //***********************************************************************************
	private static void createModel(int[][] costMatrix, int initialUB){
		final int doubleN = costMatrix.length;
		model = new GraphModel();
		// variables
		totalCost = model.intVar("obj", -M*doubleN, initialUB, true);
		// creates a graph containing n nodes
		UndirectedGraph GLB = new UndirectedGraph(model, doubleN, SetType.LINKED_LIST, true);
		UndirectedGraph GUB = new UndirectedGraph(model, doubleN, SetType.BIPARTITESET, true);
		// adds potential edges
		for (int i = 0; i < doubleN; i++) {
			for (int j = i + 1; j < doubleN; j++) {
				GUB.addEdge(i, j);
			}
		}
		graph = model.graphVar("G", GLB, GUB);
	}


	private static void createModelAsym(int[][] costMatrix, int initialUB){
		final int n = costMatrix.length;

		model = new GraphModel();
		// variables
		totalCost = model.intVar("obj", 0, initialUB, true);
		// creates a graph containing n nodes
		DirectedGraph GLB = new DirectedGraph(model, n, SetType.LINKED_LIST, true);
		DirectedGraph GUB = new DirectedGraph(model, n, SetType.BIPARTITESET, true);
		// adds potential edges
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				if(i != j){
					GUB.addArc(i, j);
				}
			}
		}
		digraph = model.digraphVar("G", GLB, GUB);
	}

	private static int search(int[][] costMatrix, boolean benchMatrix){
		Solver solver = model.getSolver();
		// Fail first principle (requires a very good initial upper bound)
		solver.setSearch(new GraphSearch(graph, costMatrix).configure(GraphSearch.MIN_COST).useLastConflict());
		solver.limitTime(LIMIT+"s");

		model.setObjective(Model.MINIMIZE,totalCost);
		while (solver.solve()){
			System.out.println("After " + solver.getNodeCount() + "nodes,");
			if (benchMatrix){
				System.out.println("solution found : " + (solver.getBestSolutionValue().intValue() + M*n));//"[" + (totalCost.getLB() + M*n) +", " + (totalCost.getUB() + M*n) + "]");
			}
			else{
				System.out.println("solution found : " + solver.getBestSolutionValue());
			}
		}
		if(solver.getTimeCount()<LIMIT){
			System.out.println("Optimality proved with exact CP approach");
		}else{
			if(solver.getSolutionCount()>0) {
				System.out.println("Best solution found : " + solver.getBestSolutionValue() + " (but no optimality proof");
			}else{
				System.out.println("no solution found");
			}
		}
		return solver.getBestSolutionValue().intValue() + M*n;
	}

	private static int searchAsym(int[][] costMatrix){
		Solver solver = model.getSolver();
		// Fail first principle (requires a very good initial upper bound)
		solver.setSearch(new GraphSearch(digraph, costMatrix, fusion).configure(GraphSearch.LEX).useLastConflict());
		solver.limitTime(LIMIT+"s");

		model.setObjective(Model.MINIMIZE,totalCost);
		while (solver.solve()){
			System.out.println("After " + solver.getNodeCount() + "nodes,");
			System.out.println("solution found : " + solver.getBestSolutionValue());
		}
		if(solver.getTimeCount()<LIMIT){
			System.out.println("Optimality proved with exact CP approach");
		}else{
			if(solver.getSolutionCount()>0) {
				System.out.println("Best solution found : " + solver.getBestSolutionValue() + " (but no optimality proof");
			}else{
				System.out.println("no solution found");
			}
		}

		return solver.getBestSolutionValue().intValue();
	}

	private static PropFusionASym fusion = null;
	private static PropLagr_OneTree bench = null;
	private static int benchimol(int[][] costMatrix, int initialUB){
		createModel(costMatrix, - (n-1)*M);
        // constraints (TSP basic model + lagrangian relaxation)
		bench = new PropLagr_OneTree(graph, totalCost, costMatrix);
		model.tsp(graph, totalCost, costMatrix, 1, bench).post();
		return search(costMatrix, true);
    }

	/*private static void fusion(int[][] costMatrix, int initialUB){
		createModel(costMatrix, initialUB);
		// constraints (TSP basic model + lagrangian relaxation)
		model.tsp_fusion(graph, totalCost, costMatrix).post();
		search(costMatrix, false);
	}*/

	private static int fusionAsym(int[][] costMatrix, int initialUB){
		createModelAsym(costMatrix, initialUB);
		fusion = new PropFusionASym(digraph, totalCost, costMatrix);
		// constraints (TSP basic model + lagrangian relaxation)
		model.tsp_fusion_asym(digraph, totalCost, costMatrix, fusion).post();
		return searchAsym(costMatrix);
	}

	private static int fusionBench(int[][] smallCostMatrix, int[][] bigCostMatrix, int initialUB){
		createModel(bigCostMatrix, initialUB);
		PropSymVarFusionASym prop = new PropSymVarFusionASym(graph, totalCost, smallCostMatrix);
		// constraints (TSP basic model + lagrangian relaxation)
		model.tsp_fusion(graph, totalCost, bigCostMatrix, prop).post();
		return search(bigCostMatrix, true);
	}
}
