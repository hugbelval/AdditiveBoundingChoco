package org.chocosolver.graphsolver;

import org.chocosolver.graphsolver.cstrs.cost.tsp.lagrangianRelaxation.PropFusionASym;
import org.chocosolver.graphsolver.cstrs.cost.tsp.lagrangianRelaxation.PropLagr_OneTree;
import org.chocosolver.graphsolver.cstrs.cost.tsp.lagrangianRelaxation.PropSymVarFusionASym;
import org.chocosolver.graphsolver.search.strategy.GraphSearch;
import org.chocosolver.graphsolver.variables.DirectedGraphVar;
import org.chocosolver.graphsolver.variables.GraphVar;
import org.chocosolver.graphsolver.variables.UndirectedGraphVar;
import org.chocosolver.solver.Model;
import org.chocosolver.solver.Solver;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.util.objects.graphs.DirectedGraph;
import org.chocosolver.util.objects.graphs.UndirectedGraph;
import org.chocosolver.util.objects.setDataStructures.SetType;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.stream.Collectors;

public class GraphGeneration {
    private static GraphModel model;
    private static IntVar totalCost;
    private static UndirectedGraphVar graph;
    private static DirectedGraphVar digraph;
    private static int LIMIT = 60; // in seconds
    private static int n;
    private static int M = 1000000;
    private static int bigValue = 999999999;
    public static void main(String[] args) throws IOException {
        List<String> graphData = new ArrayList<>();
        String[] filenames = getATSPFilenames();
        List<List<DirectedGraphVar>> graphVars;
        String REPO = "src/test/java/org/chocosolver/samples";

        for (int i = 0; i < filenames.length; i++){
            int[][] data = getATSPInstance(filenames[i]);
            n = data.length;
            int presolve = 9999999;
            //fusionAsym(data, presolve, true);
            try (FileWriter writer = new FileWriter(REPO + "/" + filenames[i] + ".txt")) {
                writer.write(fusion.graphData);
                System.out.println("Successfully wrote to file.");
            } catch (IOException e) {
                System.err.println("Error writing to file: " + e.getMessage());
            }
        }
    }


    private static int[][] getATSPInstance(String name) throws IOException {
        String REPO = "src/test/java/org/chocosolver/samples/atsp";
        org.moeaframework.problem.tsplib.TSPInstance problem = new org.moeaframework.problem.tsplib.TSPInstance(new File(REPO + "/" + name));
        return getDataFromProblem(problem);
    }

    private static String[] getATSPFilenames() throws IOException {
        String REPO = "src/test/java/org/chocosolver/samples/atsp";
        File dir = new File(REPO);
        return dir.list();
    }

    private static int[][] getDataFromProblem(org.moeaframework.problem.tsplib.TSPInstance problem){
        org.moeaframework.problem.tsplib.DistanceTable temp = problem.getDistanceTable();
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

    private static Solver search(int[][] costMatrix, boolean benchMatrix){
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
    private static PropLagr_OneTree bench = null;

	/*private static void fusion(int[][] costMatrix, int initialUB){
		createModel(costMatrix, initialUB);
		// constraints (TSP basic model + lagrangian relaxation)
		model.tsp_fusion(graph, totalCost, costMatrix).post();
		search(costMatrix, false);
	}*/

   /* private static Solver fusionAsym(int[][] costMatrix, int initialUB, boolean interleave){
        createModelAsym(costMatrix, initialUB);
        fusion = new PropFusionASym(digraph, totalCost, costMatrix, interleave);
        // constraints (TSP basic model + lagrangian relaxation)
        model.tsp_fusion_asym(digraph, totalCost, costMatrix, fusion).post();
        return searchAsym(costMatrix);
    }*/
}
