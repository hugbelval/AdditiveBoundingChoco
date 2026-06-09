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

import java.util.Arrays;

/**
 * TSP Lagrangian relaxation
 * Inspired from the work of Held & Karp
 * and Benchimol et. al. (Constraints 2012)
 *
 * @author Jean-Guillaume Fages
 */
public class PropLagr_OneTree_APSTART extends Propagator<Variable> implements GraphLagrangianRelaxation {

    //***********************************************************************************
    // VARIABLES
    //***********************************************************************************

    protected UndirectedGraph g;
    protected UndirectedGraphVar gV;
    protected IntVar obj;
    protected int N;
    protected int n;
    protected int[][] originalCosts;
    protected double[][] costs;
    private double[][] reducedCosts;
    protected double[] penalities;
    double[][] marginalCosts;
    protected double totalPenalities;
    protected UndirectedGraph mst;
    protected TIntArrayList mandatoryArcsList;
    protected double step;
    protected AbstractTreeFinder HKfilter, HK;
    protected boolean waitFirstSol;
    protected int nbSprints;
    private int M;
    public double firstLb = Integer.MIN_VALUE;
    private double[][] smallCostMatrix;
    private int bigValue = 99999999;
    //***********************************************************************************
    // CONSTRUCTORS
    //***********************************************************************************

    protected PropLagr_OneTree_APSTART(Variable[] vars, int[][] costMatrix) {
        super(vars, PropagatorPriority.CUBIC, false);


        originalCosts = costMatrix;
        N = originalCosts.length;
        n = N / 2;
        M = -1*originalCosts[n][0];
        costs = new double[N][N];
        reducedCosts = new double[N][N];
        marginalCosts = new double[N][N];
        totalPenalities = 0;
        penalities = new double[N];
        mandatoryArcsList = new TIntArrayList();
        nbSprints = 30;
        HK = new PrimOneTreeFinder(N, this);
        HKfilter = new KruskalOneTree_GAC(N, this);

        smallCostMatrix = new double[n][n];
    }

    public PropLagr_OneTree_APSTART(UndirectedGraphVar graph, IntVar cost, int[][] costMatrix) {
        this(new Variable[]{graph, cost}, costMatrix);
        g = graph.getUB();
        gV = graph;
        obj = cost;
    }

    //***********************************************************************************
    // HK Algorithm(s)
    //***********************************************************************************
    double lowerBound;
    public void propagate(int evtmask) throws ContradictionException {
        if (waitFirstSol && getModel().getSolver().getSolutionCount() == 0) {
            return;//the UB does not allow to prune
        }
        // initialisation
        rebuild();
        //setSmallCostMatrix();
        //lowerBound = solveAP();
        lowerBound = 0;
        // Is this a patch for something that goes wrong ?
        //obj.updateLowerBound((int) (Math.ceil(lowerBound) - M*n), this);
        setReducedCostsAsOriginalCosts();
        //reducedCosts = makeJonkerMatrix(smallCostMatrix);
        //Je ne dois pas reset les penalities, sinon ça donne des résultats bcp moins bons
        //penalities = new double[N];
        //totalPenalities = 0;
        setCosts();
        int lb;
        do {
            lb = obj.getLB();
            lagrangianRelaxation();
        } while (lb < obj.getLB());

        setMarginalCosts();
        lowerBound = hkb;
        filterAP();
        gV.removed = 0;


        if (firstLb == Integer.MIN_VALUE){
            firstLb = obj.getLB();
        }
        //System.out.println("removed " + gV.removed);
    }

    private void setMarginalCosts(){
        for (int i = 0; i < N; i++) {
            for (int j = 0; j < N; j++) {
                marginalCosts[i][j] = getMarginalCost(i,j);
            }
        }
    }

    private void setReducedCostsAsOriginalCosts(){
        for (int i = 0; i < N; i++) {
            for (int j = 0; j <N; j++) {
                reducedCosts[i][j] = originalCosts[i][j];
            }
        }
    }
    private double solveAP(){
        double lowerBound = 0;
        PropFusionAsymUndirectedGraphVar.Result result = null;
        int i = 0;
        while(i < 99999999 && (result == null || result.lb > 0)) {
            result = hungarianIteration(smallCostMatrix);
            lowerBound += result.lb;
            smallCostMatrix = result.array;
            i++;
        }
        return lowerBound;
    }

    private double[][] makeSmallCostMatrix(double[][] matrix){
        double[][] scm = new double[n][n];
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                scm[i][j] = matrix[i+n][j];
                if(i ==j /*|| !gV.getUB().edgeExists(i+n,j)*/){
                    scm[i][j] = bigValue;
                }
            }
        }
        return scm;
    }

    private void filterAP() throws ContradictionException {
        //bigBasicFiltering(marginalCosts, lowerBound);

        smallCostMatrix = makeSmallCostMatrix(marginalCosts);
        basicFiltering(smallCostMatrix, lowerBound/* - n*M*/);
        PropFusionAsymUndirectedGraphVar.Result result = null;
        int i = 0;
        while(i < 1 && (result == null || result.lb != 0)) {
            result = hungarianIteration(smallCostMatrix);
            lowerBound += result.lb;
            if(lowerBound > 0){
                int a = 3;
            }
            smallCostMatrix = result.array;
            basicFiltering(smallCostMatrix, lowerBound);
            i++;
        }
    }

    public void basicFiltering(double[][] smallCostsArray, double lowerBound) throws ContradictionException {
        double delta = obj.getUB() - lowerBound + 1;
        if (delta < 0){
            throw new ContradictionException();
        }
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                if (!gV.getLB().edgeExists(i+n, j) && gV.getUB().isArcOrEdge(i+n,j) && i != j && smallCostsArray[i][j] > delta) {
                    //smallCostsArray[i][j] = bigValue;
                    remove(i+n, j);
                }
            }
        }
        //mandFiltering();
    }


    public void bigBasicFiltering(double[][] bigCostsArray, double lowerBound) throws ContradictionException {
        double delta = obj.getUB() - lowerBound + 1;
        if (delta < 0){
            throw new ContradictionException();
        }
        for (int i = 0; i < N; i++) {
            for (int j = 0; j < N; j++) {
                if (!gV.getLB().edgeExists(i,j) && i != j+n && i+n != j && gV.getUB().isArcOrEdge(i,j) && i != j && bigCostsArray[i][j] > delta) {
                    //bigCostsArray[i][j] = bigValue;
                    remove(i, j);
                }
            }
        }
        //mandFiltering();
    }

    double hkb;

    public PropFusionAsymUndirectedGraphVar.Result hungarianIteration(double[][] costs) {
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
            if(min > 50){
                int a =3;
            }
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
            return new PropFusionAsymUndirectedGraphVar.Result(lb, costs, zeros);
        }
        else{
            return new PropFusionAsymUndirectedGraphVar.Result(lb, costs, null);
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

    protected void lagrangianRelaxation() throws ContradictionException {
        double alpha = 2;
        double beta = 0.5;
        double bestHKB;
        bestHKB = 0;
        HKfilter.computeMST(costs, g);
        hkb = HKfilter.getBound() - totalPenalities;
        if(HKfilter.getBound() != -M*n){
            int a =3;
        }
        bestHKB = hkb;
        mst = HKfilter.getMST();
        if (hkb - Math.floor(hkb) < 0.001) {
            hkb = Math.floor(hkb);
        }
        obj.updateLowerBound((int) (Math.ceil(hkb + lowerBound)), this);
        //TODO ici le lowerbound est important
        HKfilter.performPruning((double) (obj.getUB()) + totalPenalities - lowerBound + 0.001);
        for (int iter = 5; iter > 0; iter--) {
            for (int i = nbSprints; i > 0; i--) {
                HK.computeMST(costs, g);
                hkb = HK.getBound() - totalPenalities;
                if (hkb > bestHKB + 1) {
                    bestHKB = hkb;
                }
                mst = HK.getMST();
                if (hkb - Math.floor(hkb) < 0.001) {
                    hkb = Math.floor(hkb);
                }
                obj.updateLowerBound((int) (Math.ceil(hkb + lowerBound)), this);
                // HK.performPruning((double) (obj.getUB()) + totalPenalities + 0.001);
                //	DO NOT FILTER HERE TO SPEED UP CONVERGENCE (not always true)
                updateStep(hkb, alpha);
                HKPenalities();
                updateCostMatrix();
            }
            HKfilter.computeMST(costs, g);
            hkb = HKfilter.getBound() - totalPenalities;
            if (hkb > bestHKB + 1) {
                bestHKB = hkb;
            }
            mst = HKfilter.getMST();
            if (hkb - Math.floor(hkb) < 0.001) {
                hkb = Math.floor(hkb);
            }
            obj.updateLowerBound((int) (Math.ceil(hkb + lowerBound)), this);
            HKfilter.performPruning((double) (obj.getUB()) + totalPenalities - lowerBound + 0.001);
            updateStep(hkb, alpha);
            HKPenalities();
            updateCostMatrix();
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
        for (int i = 0; i < N; i++) {
            nei = gV.getMandNeighOf(i);
            for (int j : nei) {
                if (i < j) {
                    mandatoryArcsList.add(i * N + j);
                }
            }
        }
    }

    private void setSmallCostMatrix(){
        for (int i = n; i < N; i++) {
            for (int j = 0; j < n; j++) {
                if (i == j+n || !gV.getUB().edgeExists(i,j)){
                    smallCostMatrix[i-n][j] = bigValue;
                }
                else{
                    smallCostMatrix[i-n][j] = originalCosts[i][j];
                }
            }
        }
    }

    private double[][] makeJonkerMatrix(double[][] data){
        double[][] bench = new double[N][N];
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                //Bottom left
                bench[i+ n][j] = data[i][j];
                //Top right
                bench[i][j+ n] = data[j][i];

                bench[i][j] = bigValue;
                bench[i+ n][j+ n] = bigValue;
            }
            bench[i+ n][i] = -M;
            bench[i][i+ n] = -M;
        }
        return bench;
    }

    protected void setCosts() {
        ISet nei;
        for (int i = 0; i < N; i++) {
            nei = g.getNeighOf(i);
            for (int j : nei) {
                if (i < j) {
                    costs[i][j] = reducedCosts[i][j] + penalities[i] + penalities[j];
                    costs[j][i] = costs[i][j];
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
        for (int i = 0; i < N; i++) {
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
        for (int i = 0; i < N; i++) {
            deg = mst.getNeighOf(i).size();
            penalities[i] += (deg - 2) * step;
            assert !(penalities[i] > Double.MAX_VALUE / (N - 1) || penalities[i] < -Double.MAX_VALUE / (N - 1)) :
                    "Extreme-value lagrangian multipliers. Numerical issue may happen";
            sumPenalities += penalities[i];
        }
        this.totalPenalities = 2 * sumPenalities;
    }

    protected void updateCostMatrix() {
        ISet nei;
        for (int i = 0; i < N; i++) {
            nei = g.getNeighOf(i);
            for (int j : nei) {
                if (i < j) {
                    costs[i][j] = reducedCosts[i][j] + penalities[i] + penalities[j];
                    costs[j][i] = costs[i][j];
                }
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
}
