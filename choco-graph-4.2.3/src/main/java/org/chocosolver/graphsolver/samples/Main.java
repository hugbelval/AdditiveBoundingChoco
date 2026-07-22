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

package org.chocosolver.graphsolver.samples;

import org.chocosolver.graphsolver.GraphModel;
import org.chocosolver.graphsolver.cstrs.cost.tsp.lagrangianRelaxation.PropFusionASym;
import org.chocosolver.graphsolver.cstrs.cost.tsp.lagrangianRelaxation.PropFusionAsymUndirectedGraphVar;
import org.chocosolver.graphsolver.cstrs.cost.tsp.lagrangianRelaxation.PropLagr_OneTree;
import org.chocosolver.graphsolver.cstrs.cost.tsp.lagrangianRelaxation.PropLagr_OneTree_APSTART;
import org.chocosolver.graphsolver.cstrs.cost.tsp.lagrangianRelaxation.PropSymVarFusionASym;
import org.chocosolver.graphsolver.search.strategy.GraphSearch;
import org.chocosolver.graphsolver.variables.DirectedGraphVar;
import org.chocosolver.graphsolver.variables.UndirectedGraphVar;
import org.chocosolver.solver.Model;
import org.chocosolver.solver.Solver;
import org.chocosolver.solver.constraints.Propagator;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.search.loop.monitors.IMonitorContradiction;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.util.objects.graphs.DirectedGraph;
import org.chocosolver.util.objects.graphs.UndirectedGraph;
import org.chocosolver.util.objects.setDataStructures.SetType;
import org.moeaframework.problem.tsplib.TSPInstance;
import org.moeaframework.problem.tsplib.DistanceTable;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Arrays;
import java.util.Iterator;
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
	private static int LIMIT = 3000; // in seconds
	private static int n;
	private static int M = 1000000;
	private static int bigValue = 999999999;
    public static void main(String[] args) throws IOException {
		//resultsFirstLB_vsHeldKarp();
		//resultsFirstLB_vsSequencing();

		//resultsTimeAndNodes_vsHeldKarp();
		//resultsTimeAndNodes_vsSequencing();

		//randomLoop();
		//resultsFirstLB();
		//resultsTimeAndNodes();
		//getData();
		String fileName = "rbg358.atsp";
		int[][] data = getATSPInstance(fileName);
		n = data.length;
		int[][] jonker_matrix = makeJonkerMatrix(data);
		int presolve = (int)getBestSol(fileName);
		fusionAsymUndirected(jonker_matrix, presolve, true);
		//heldKarp(jonker_matrix, presolve);
		//Solver solver = heldKarp(jonker_matrix, presolve);
		int a =3;
		//fusionAsymUndirected(jonker_matrix, presolve, true);
		//fusionAsym(data, presolve, true);
		//benchimol(jonker_matrix, presolve);
    }

	public static double getBestSol(String filename) {
		String filepath = "bestSols.csv";
		String cleanedFilename = filename.replace(".atsp", "").trim();
		try (BufferedReader br = new BufferedReader(new FileReader(filepath))) {
			String line;
			while ((line = br.readLine()) != null) {
				String[] parts = line.split(",");
				if (parts.length >= 2 && parts[0].trim().equalsIgnoreCase(cleanedFilename)) {
					return Double.parseDouble(parts[1].trim());
				}
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
		System.out.println("BestSol not found");
		return 99999999; // filename not found
	}


	private static void getData() throws IOException {
		int[][] data = getATSPInstance("ft70.atsp");
		n = data.length;
		int presolve = 99999;

		//fusionAsym(data, presolve, false);

		try (BufferedWriter bw = new BufferedWriter(new FileWriter("src/dataFirstIterNoInterleave.csv"))) {
			bw.write("time," + Arrays.stream(fusion.dataTime.toArray())
					.map(String::valueOf).collect(Collectors.joining(","))); bw.newLine();
			bw.write("bound," + Arrays.stream(fusion.dataBound.toArray())
					.map(String::valueOf).collect(Collectors.joining(","))); bw.newLine();
			bw.write("isHungarian," + Arrays.stream(fusion.dataIsHungarian.toArray())
					.map(String::valueOf).collect(Collectors.joining(","))); bw.newLine();
		}

		//fusionAsym(data, presolve, true);

		try (BufferedWriter bw = new BufferedWriter(new FileWriter("src/dataFirstIter.csv"))) {
			bw.write("time," + Arrays.stream(fusion.dataTime.toArray())
					.map(String::valueOf).collect(Collectors.joining(","))); bw.newLine();
			bw.write("bound," + Arrays.stream(fusion.dataBound.toArray())
					.map(String::valueOf).collect(Collectors.joining(","))); bw.newLine();
			bw.write("isHungarian," + Arrays.stream(fusion.dataIsHungarian.toArray())
					.map(String::valueOf).collect(Collectors.joining(","))); bw.newLine();
		}
	}

	private static void resultsTimeAndNodes_vsHeldKarp() throws IOException {
		String[] filenames = getATSPFilenames();
		double[] fusionTime = new double[filenames.length];
		double[] fusionNodeCount = new double[filenames.length];
		double[] benchTime = new double[filenames.length];
		double[] benchNodeCount = new double[filenames.length];
		double[] sequencingTime = new double[filenames.length];
		double[] sequencingNodeCount = new double[filenames.length];
		for (int i = 0; i < filenames.length; i++){
			int[][] data = getATSPInstance(filenames[i]);
			n = data.length;
			int[][] jonker_matrix = makeJonkerMatrix(data);
			//	int presolve = TSP_Utils.getOptimum(INSTANCE,REPO+"/bestSols.csv");
			int presolve = (int)getBestSol(filenames[i]); //9999999;
			Solver resultsBench = heldKarp(jonker_matrix,presolve);
			benchTime[i] = resultsBench.getTimeCount();
			Solver resultsFusion = fusionAsymUndirected(jonker_matrix, presolve, true);
			fusionTime[i] = resultsFusion.getTimeCount();
			Solver resultsSequencing = fusionAsymUndirected(jonker_matrix, presolve, false);
			sequencingTime[i] = resultsSequencing.getTimeCount();

			fusionNodeCount[i] = resultsFusion.getNodeCount();
			benchNodeCount[i] = resultsBench.getNodeCount();
			sequencingNodeCount[i] = resultsSequencing.getNodeCount();
		}

		try (BufferedWriter bw = new BufferedWriter(new FileWriter("src/HK+Me_Fixed_RedCostMethod.csv"))) {
			bw.write("," + String.join(",", filenames)); bw.newLine();
			bw.write("Held-Karp - temps," + Arrays.stream(benchTime)
					.mapToObj(String::valueOf).collect(Collectors.joining(","))); bw.newLine();
			bw.write("Held-Karp+Sequencer - temps," + Arrays.stream(sequencingTime)
					.mapToObj(String::valueOf).collect(Collectors.joining(","))); bw.newLine();
			bw.write("Held-Karp+Entrelacer - temps," + Arrays.stream(fusionTime)
					.mapToObj(String::valueOf).collect(Collectors.joining(","))); bw.newLine();
			bw.write("Held-Karp - noeuds," + Arrays.stream(benchNodeCount)
					.mapToObj(String::valueOf).collect(Collectors.joining(","))); bw.newLine();
			bw.write("Held-Karp+Sequencer - noeuds," + Arrays.stream(sequencingNodeCount)
					.mapToObj(String::valueOf).collect(Collectors.joining(","))); bw.newLine();
			bw.write("Held-Karp+Entrelacer - noeuds," + Arrays.stream(fusionNodeCount)
					.mapToObj(String::valueOf).collect(Collectors.joining(","))); bw.newLine();
		}
	}

	private static void resultsTimeAndNodes_vsSequencing() throws IOException {
		String[] filenames = getATSPFilenames();
		double[] fusionTime = new double[filenames.length];
		double[] fusionNodeCount = new double[filenames.length];
		double[] benchTime = new double[filenames.length];
		double[] benchNodeCount = new double[filenames.length];

		/*for (int i = 0; i < filenames.length; i++){
			int[][] data = getATSPInstance(filenames[i]);
			n = data.length;
			int[][] jonker_matrix = makeJonkerMatrix(data);
			//	int presolve = TSP_Utils.getOptimum(INSTANCE,REPO+"/bestSols.csv");
			int presolve = 999999;//(int)getBestSol(filenames[i]); //9999999;
			Solver resultsBench = fusionAsymUndirected(jonker_matrix,presolve, false);
			benchTime[i] = resultsBench.getTimeCount();
			Solver resultsFusion = fusionAsymUndirected(jonker_matrix, presolve, true);
			fusionTime[i] = resultsFusion.getTimeCount();
			fusionNodeCount[i] = resultsFusion.getNodeCount();
			benchNodeCount[i] = resultsBench.getNodeCount();
		}*/
		for (int i = 0; i < filenames.length; i++){
			int[][] data = getATSPInstance(filenames[i]);
			n = data.length;
			int[][] jonker_matrix = makeJonkerMatrix(data);
			//int presolve = 999999;
			int presolve = (int)getBestSol(filenames[i]);
			Solver resultsBench = fusionAsymUndirected(jonker_matrix,presolve, false);
			benchTime[i] = resultsBench.getTimeCount();
			Solver resultsFusion = fusionAsymUndirected(jonker_matrix, presolve, true);
			fusionTime[i] = resultsFusion.getTimeCount();
			fusionNodeCount[i] = resultsFusion.getNodeCount();
			benchNodeCount[i] = resultsBench.getNodeCount();
		}

		try (BufferedWriter bw = new BufferedWriter(new FileWriter("src/SequenceVSInterleave_LKH.csv"))) {
			bw.write("," + String.join(",", filenames)); bw.newLine();
			bw.write("benchimol temps," + Arrays.stream(benchTime)
					.mapToObj(String::valueOf).collect(Collectors.joining(","))); bw.newLine();
			bw.write("benchimol noeuds," + Arrays.stream(benchNodeCount)
					.mapToObj(String::valueOf).collect(Collectors.joining(","))); bw.newLine();
			bw.write("entrelacer temps," + Arrays.stream(fusionTime)
					.mapToObj(String::valueOf).collect(Collectors.joining(","))); bw.newLine();
			bw.write("entrelacer noeuds," + Arrays.stream(fusionNodeCount)
					.mapToObj(String::valueOf).collect(Collectors.joining(","))); bw.newLine();
		}
	}

	private static void resultsFirstLB_vsHeldKarp() throws IOException {
		String[] filenames = getATSPFilenames();
		double[] fusionResults = new double[filenames.length];
		double[] benchResults = new double[filenames.length];
		for (int i = 0; i < filenames.length; i++){
			int[][] data = getATSPInstance(filenames[i]);
			n = data.length;

			int[][] bench_matrix = makeJonkerMatrix(data);
			//	int presolve = TSP_Utils.getOptimum(INSTANCE,REPO+"/bestSols.csv");
			int presolve = 9999999;
			heldKarp(bench_matrix, presolve);
			benchResults[i] = hk.firstLb;
			//fusionAsym(data, presolve, true);
			fusionResults[i] = fusion.firstLb;
		}

		try (BufferedWriter bw = new BufferedWriter(new FileWriter("src/resultsFirstLBHeldKarp.csv"))) {
			bw.write("," + String.join(",", filenames)); bw.newLine();
			bw.write("sans entrelacer," + Arrays.stream(benchResults)
					.mapToObj(String::valueOf).collect(Collectors.joining(","))); bw.newLine();
			bw.write("maMéthode," + Arrays.stream(fusionResults)
					.mapToObj(String::valueOf).collect(Collectors.joining(","))); bw.newLine();
		}
	}


	private static void resultsFirstLB_vsSequencing() throws IOException {
		String[] filenames = getATSPFilenames();
		double[] fusionResults = new double[filenames.length];
		double[] benchResults = new double[filenames.length];
		for (int i = 0; i < filenames.length; i++){
			int[][] data = getATSPInstance(filenames[i]);
			n = data.length;

			int[][] bench_matrix = makeJonkerMatrix(data);
			//	int presolve = TSP_Utils.getOptimum(INSTANCE,REPO+"/bestSols.csv");
			int presolve = 9999999;
			//fusionAsym(data ,presolve, false);
			benchResults[i] = fusion.firstLb;
			//fusionAsym(data, presolve, true);
			fusionResults[i] =fusion.firstLb;
		}

		try (BufferedWriter bw = new BufferedWriter(new FileWriter("src/resultsFirstLBSequencing.csv"))) {
			bw.write("," + String.join(",", filenames)); bw.newLine();
			bw.write("sans entrelacer," + Arrays.stream(benchResults)
					.mapToObj(String::valueOf).collect(Collectors.joining(","))); bw.newLine();
			bw.write("maMéthode," + Arrays.stream(fusionResults)
					.mapToObj(String::valueOf).collect(Collectors.joining(","))); bw.newLine();
		}
	}

	private static void randomLoop(){
		n = 8;
	while (true){
			int[][] data = randomMatrix();
			int[][] jonker_matrix = makeJonkerMatrix(data);
			int presolve = 500000;
			Solver result1 = fusionAsymUndirected(jonker_matrix, 999999, true);
			//System.out.println("result " + graph.toString());
			/*Solver result2 = heldKarp(jonker_matrix, 999999);
		System.out.println("result " + graph.toString());
			if(result1.getBestSolutionValue().intValue() != result2.getBestSolutionValue().intValue()){
				int a = 3;
			}*/
		}
	}

	private static int[][] makeJonkerMatrix(int[][] data){
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

	private static int seed = 7056;
	public static int[][] randomMatrix() {
		Random rand = new Random(seed);
		seed++;
		int[][] matrix = new int[n][n];

		for (int i = 0; i < n; i++)
			for (int j = 0; j < n; j++)
				if (i == j) {
					matrix[i][i] = 99999;
				} else {
					matrix[i][j] = rand.nextInt(20);
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
		String REPO = "hard_atsp/";
		org.moeaframework.problem.tsplib.TSPInstance problem = new TSPInstance(new File(REPO + "/" + name));
		return getDataFromProblem(problem);
	}

	private static String[] getATSPFilenames() throws IOException {
		String REPO = "hard_atsp/";
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
		totalCost = model.intVar("obj", -M*n, initialUB, true);
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

	private static Solver search(int[][] costMatrix, boolean benchMatrix, int graphSearch){
		Solver solver = model.getSolver();
		// Fail first principle (requires a very good initial upper bound)
		GraphSearch heuristic;
		if(graphSearch == GraphSearch.REDUCED_COST_INTERLEAVE){
			heuristic = new GraphSearch(graph, costMatrix, interleaveProp);
		}
		else if(graphSearch == GraphSearch.REDUCED_COST_HK){
			heuristic = new GraphSearch(graph, costMatrix, hk);
		}
		else{
			heuristic = new GraphSearch(graph, costMatrix);
		}
		solver.setSearch(heuristic.configure(graphSearch).useLastConflict());
		solver.limitTime(LIMIT+"s");

		model.setObjective(Model.MINIMIZE,totalCost);

// Print every decision and backtrack

		while (solver.solve()){
			System.out.println("After " + solver.getNodeCount() + "nodes,");
			//System.out.println("result " + graph.toString());
			if (benchMatrix){
				int cost = 0;
				UndirectedGraphVar gv = (UndirectedGraphVar) model.retrieveGraphVars()[0];
				for (int i = 0; i < n; i++) {
					Iterator<Integer> it = gv.getMandNeighOf(i).iterator();
					while(it.hasNext()){
						int j = it.next();
						if(costMatrix[i][j]>0){
							cost += costMatrix[i][j];
						}
					}
				}
				//System.out.println("solution found : " + );//"[" + (totalCost.getLB() + M*n) +", " + (totalCost.getUB() + M*n) + "]");
				int reported = (solver.getBestSolutionValue().intValue() + M*n);
				if(reported != cost){
					int a =3;
				}
				System.out.println("Solution [CHECK] reported=" + reported + " real=" + cost);
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


		return solver;
		//return solver.getBestSolutionValue().intValue() + M*n;
	}

	/*private static Solver searchAsym(int[][] costMatrix){
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
		//return (int) solver.getNodeCount();
		return solver;
	}*/

	private static PropFusionASym fusion = null;
	private static PropFusionAsymUndirectedGraphVar interleaveProp = null;
	private static PropLagr_OneTree hk = null;


	/*private static void fusion(int[][] costMatrix, int initialUB){
		createModel(costMatrix, initialUB);
		// constraints (TSP basic model + lagrangian relaxation)
		model.tsp_fusion(graph, totalCost, costMatrix).post();
		search(costMatrix, false);
	}*/

	/*private static Solver fusionAsym(int[][] costMatrix, int initialUB, boolean interleave){
		createModelAsym(costMatrix, initialUB);
		fusion = new PropFusionASym(digraph, totalCost, costMatrix, interleave);
		// constraints (TSP basic model + lagrangian relaxation)
		model.tsp_fusion_asym(digraph, totalCost, costMatrix, fusion).post();
		return searchAsym(costMatrix);
	}*/

	private static Solver heldKarp(int[][] costMatrix, int initialUB){
		createModel(costMatrix, - (n)*M+initialUB);
		// constraints (TSP basic model + lagrangian relaxation)
		hk = new PropLagr_OneTree(graph, totalCost, costMatrix);
		model.tsp(graph, totalCost, costMatrix, 1, hk).post();
		return search(costMatrix, true, GraphSearch.REDUCED_COST_HK);
	}

	private static Solver fusionAsymUndirected(int[][] costMatrix, int initialUB, boolean interleave){
		createModel(costMatrix, - (n)*M+initialUB);
		interleaveProp = new PropFusionAsymUndirectedGraphVar(graph, totalCost, costMatrix, interleave);
		hk = new PropLagr_OneTree(graph, totalCost, costMatrix);
		Propagator[] props = new Propagator[]{
				interleaveProp,
				//hk
		};
		//props[0] = ;
		// constraints (TSP basic model + lagrangian relaxation)
		model.tsp_general(graph, totalCost, costMatrix, props).post();
		return search(costMatrix, true, GraphSearch.REDUCED_COST_HK);
	}

	private static Solver heldKarpAPStart(int[][] costMatrix, int initialUB){
		createModel(costMatrix, - (n)*M+initialUB);
		Propagator[] props = new Propagator[]{
				new PropLagr_OneTree_APSTART(graph, totalCost, costMatrix),
				//new PropLagr_OneTree(graph, totalCost, costMatrix)
		};
		//props[0] = ;
		// constraints (TSP basic model + lagrangian relaxation)
		model.tsp_general(graph, totalCost, costMatrix, props).post();
		return search(costMatrix, true, GraphSearch.MAX_COST);
	}

	private static Solver fusionBench(int[][] smallCostMatrix, int[][] bigCostMatrix, int initialUB){
		createModel(bigCostMatrix, initialUB);
		PropSymVarFusionASym prop = new PropSymVarFusionASym(graph, totalCost, smallCostMatrix);
		// constraints (TSP basic model + lagrangian relaxation)
		model.tsp_fusion(graph, totalCost, bigCostMatrix, prop).post();
		return search(bigCostMatrix, true, GraphSearch.MAX_COST);
	}
}
