package dfta;

import java.util.LinkedHashSet;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.BitSet;
import net.sf.javabdd.*;
import java.util.LinkedHashMap;
import java.util.Iterator;
import javax.swing.JTextArea;

public class DeterminiserBDD implements Determiniser {

   Indices idx;
   String ftaId;

   boolean any = false;
   boolean includesCheck = false;

   LinkedHashSet<FTATransition> delta;
   LinkedHashSet<String> q;
   LinkedHashSet<FuncSymb> sigma;
   LinkedHashMap<Integer, String> qIdx = new LinkedHashMap<>();
   LinkedHashMap<String, Integer> qIdxInv = new LinkedHashMap<>();
   LinkedHashMap<Integer, FTATransition> deltaIdx = new LinkedHashMap<>();
   int k, m, n;
   int maxArity, maxVarCount, maxPredArity;

   Iterator iter;

   BDDFactory B;
   BDD qds, oldqds, one, zero;
   int[] clauseVarIdx, standardVarIdx;
   BDD[] clauseVars, standardVars;
   BDD nonEmpty, orStates, orTrans, andTrans;
   LinkedHashMap<Integer, BDD> rhs = new LinkedHashMap<>();
   LinkedHashMap<Integer, BDD> rhsMap = new LinkedHashMap<>();
   LinkedHashMap<FuncSymb, ArrayList<LinkedHashMap<Integer, BDD>>> lhsf = new LinkedHashMap<>();
   LinkedHashMap<FuncSymb, ArrayList<LinkedHashMap<Integer, BDD>>> lhs = new LinkedHashMap<>();
   LinkedHashMap<FuncSymb, LinkedHashMap<Integer, BDD>> lhsAnd = new LinkedHashMap<>();
   LinkedHashMap<FuncSymb, BDD> fInfer = new LinkedHashMap<>();

   int[] rhsVarOrder;

   public DeterminiserBDD(String ftaId, LinkedHashSet transitions, LinkedHashSet finalStates, boolean any) {
      this.ftaId = ftaId;
      idx = new Indices(transitions, finalStates);
      idx.genDelta(ftaId);
      idx.genFinalStates(ftaId);
      if (any) {
         idx.genDeltaAny();
      }
      idx.buildIndices();
      //idx.showIndices();
      this.any = any;
      includesCheck = false;

      delta = idx.delta;
      sigma = idx.sigma;
      q = idx.qs;
      k = delta.size();
      m = q.size();
      n = sigma.size();

      iter = q.iterator();
      int qn = 0;
      String q1;
      while (iter.hasNext()) {
         q1 = (String) iter.next();
         qIdx.put(qn, q1);
         qIdxInv.put(q1, qn);
         qn++;
      }
      iter = delta.iterator();
      int dn = 0;
      FTATransition t1;
      while (iter.hasNext()) {
         t1 = (FTATransition) iter.next();
         deltaIdx.put(dn, t1);
         dn++;
      }
      iter = sigma.iterator();
      maxArity = 0;
      FuncSymb f1;
      while (iter.hasNext()) {
         f1 = (FuncSymb) iter.next();
         if (f1.arity > maxArity) {
            maxArity = f1.arity;
         }
      }
      System.out.println("Max arity: " + maxArity);
      maxPredArity = maxPredArity();
      System.out.println("Max pred arity: " + maxPredArity);

      int numberOfNodes = 10000;
      int cacheSize = 1000000;
      B = BDDFactory.init(numberOfNodes, cacheSize);
      B.setVarNum(1000);
      one = B.one();
      zero = B.zero();
      // create sufficient variables 
      maxVarCount = maxVarCount();
      System.out.println("Max clause vars: " + maxVarCount);
      clauseVars = new BDD[maxVarCount];
      clauseVarIdx = new int[maxVarCount];
      // clause variables  
      for (int i = 0; i < maxVarCount; i++) {
         clauseVars[i] = B.ithVar(maxPredArity + i);
         clauseVarIdx[i] = maxPredArity + i;
      }

      // variables for storing answers
      standardVars = new BDD[maxPredArity];
      standardVarIdx = new int[maxPredArity];
      for (int i = 0; i < maxPredArity; i++) {
         standardVars[i] = B.ithVar(i);
         standardVarIdx[i] = i;
      }
      int r;
      FTATransition[] deltaArray = new FTATransition[k];
      iter = delta.iterator();
      r = 0;
      while (iter.hasNext()) {
         t1 = (FTATransition) iter.next();
         deltaArray[r] = t1;
         r++;
      }
      r = 0;
      LinkedHashSet<Integer> used = new LinkedHashSet<>();
      rhsVarOrder = new int[m + k];
      for (int i = k - 1; i >= 0; i--) {
         rhsVarOrder[r] = i+m;
         r++;
         int y = qIdxInv.get(deltaArray[i].q0);  // index of rhs state
         if (!used.contains(y)) {
            rhsVarOrder[r] = y;
            r++;
            used.add(y);
         }
      }
      for (int i = 0; i<m; i++) {  // add the remaining state vars, if any
         if (!used.contains(i)) {
            rhsVarOrder[r] = i;
            r++;
         }
      }
      
      /*
       r = 0;
       qn = 0;
       iter = q.iterator();
       String q0;
       while (iter.hasNext()) {
       q0 = (String) iter.next();
       rhsVarOrder[r] = qn;
       r++;
       qn++;
       ArrayList<Integer> vs = idx.rhsIdx.get(q0);
       for (Integer v : vs) {
       rhsVarOrder[r] = m + v;
       r++;
       }
       }
       */
      System.out.println("Rhs variable order: ");
      for (int i = 0; i < m + k; i++) {
         System.out.print(rhsVarOrder[i] + " ");
      }
      System.out.println();
   }

   @Override
   public void makeDfta() {
      System.out.println("Building DFTA states...");
      dftaStates();
      System.out.println("Building DFTA product transitions...");
      dftaTransitions();
   }

   public boolean dftaStates() {
      // compute predicates bottom up
      nonEmpty = nonEmpty();
      System.out.println("nonEmpty: " + nonEmpty.nodeCount() + " nodes");
      orStates = orStates();
      System.out.println("orStates: " + orStates.nodeCount() + " nodes");
      orTrans = orTrans();
      System.out.println("orTrans: " + orTrans.nodeCount() + " nodes");
      andTrans = andTrans();
      System.out.println("andTrans: " + andTrans.nodeCount() + " nodes");
      for (int i = 0; i < k; i++) {
         rhsMap.put(i, rhsMap(i));
         System.out.println("rhsMap: " + i + " " + rhsMap.get(i).nodeCount() + " nodes");
      }

      for (int i = k - 1; i >= 0; i--) {
         rhs.put(i, rhs(i));
         System.out.println("rhs: " + i + " " + rhs.get(i).nodeCount() + " nodes");
      }
      iter = sigma.iterator();
      while (iter.hasNext()) {
         FuncSymb g = (FuncSymb) iter.next();
         if (g.arity > 0) {
            lhsf.put(g, new ArrayList<>());
            for (int h = 0; h < g.arity; h++) {
               lhsf.get(g).add(h, new LinkedHashMap<>());
               for (int r = 0; r < k; r++) {
                  lhsf.get(g).get(h).put(r, lhsf(g, h, r));
               }
            }
         }
      }

      iter = sigma.iterator();
      while (iter.hasNext()) {
         FuncSymb g = (FuncSymb) iter.next();
         if (g.arity > 0) {
            lhs.put(g, new ArrayList<>());
            for (int h = 0; h < g.arity; h++) {
               lhs.get(g).add(h, new LinkedHashMap<>());
               for (int r = m - 1; r >= 0; r--) {
                  lhs.get(g).get(h).put(r, lhs(g, h, r));
               }
            }
         }
      }
      iter = sigma.iterator();
      while (iter.hasNext()) {
         FuncSymb g = (FuncSymb) iter.next();
         if (g.arity > 0) {
            lhsAnd.put(g, new LinkedHashMap<>());
            for (int h = g.arity - 1; h >= 0; h--) {
               lhsAnd.get(g).put(h, lhsAnd(g, h));
            }
         }
      }
      iter = sigma.iterator();
      while (iter.hasNext()) {
         FuncSymb g = (FuncSymb) iter.next();
         if (g.arity > 0) {
            fInfer.put(g, fInfer(g));
         }
      }

      applyConstantRules();
      System.out.println("After constant rules");
      showStats(true);

      if (!qds.isZero()) {
         iterateToFixpoint();
      }
      return false;
   }

   private void applyConstantRules() {
      qds = zero.id();
      for (FuncSymb c : sigma) {
         if (c.arity == 0) {
            qds.orWith(state0(c));
         }
      }
   }

   private void iterateToFixpoint() {
      int iterCount = 1;
      do {
         oldqds = qds.id();
         qds.orWith(state());
         System.out.println("Iteration " + iterCount + " done");
         showStats(true);
         iterCount++;
      } while (!qds.equals(oldqds));
   }

   private BDD state() {
      BDD b0 = zero.id();
      for (FuncSymb g : sigma) {
         if (g.arity > 0) {
            b0.orWith(state(g));
         }
      }
      return b0;
   }

   private BDD state0(FuncSymb c) {
      BDDPairing subst = B.makePair();

      ArrayList<BDD> b = new ArrayList<>();
      ArrayList<int[]> ys = new ArrayList<>();
      ArrayList<int[]> xs = new ArrayList<>();

      // Qs,Ts,QsTs,Qs,Ts
      int[] asize = {m, k, k + m, m, k};
      int[][] vpat = {{0, m}, {m, k}, {0, m, m, k}, {0, m}, {m, k}};
      int k1;
      int l = asize.length;
      for (int i = 0; i < l; i++) {
         ys.add(new int[asize[i]]);
         xs.add(new int[asize[i]]);
         k1 = 0;
         for (int j = 0; j < vpat[i].length; j = j + 2) {
            System.arraycopy(clauseVarIdx, vpat[i][j], ys.get(i), k1, vpat[i][j + 1]);
            k1 += vpat[i][j + 1];
         }
         System.arraycopy(standardVarIdx, 0, xs.get(i), 0, asize[i]);
      }

      int[] rhsVarOrder1 = new int[m + k];

      for (int i = 0; i < m + k; i++) {
         int x = rhsVarOrder[i];
         rhsVarOrder1[i] = x + maxPredArity;
      }
      ys.set(2, rhsVarOrder1);
      // solve clause body
      b.add(one.id());
      b.add(lhs0(c));
      b.add(rhs.get(0).id());
      b.add(nonEmpty.id());
      b.add(B.makeSet(ys.get(l - 1)));

      // rename solutions using clause variables
      for (int i = 1; i < b.size() - 1; i++) {
         subst.set(xs.get(i), ys.get(i));
         b.get(0).andWith(b.get(i).replaceWith(subst));
      }
      BDD b0 = b.get(0).exist(b.get(l - 1));
      subst.set(ys.get(0), xs.get(0));
      /*for (int i = 0; i < l; i++) {
       b.get(i).free();
       }*/
      return (b0.replaceWith(subst));
   }

   private BDD state(FuncSymb g) {
      BDDPairing subst = B.makePair();

      ArrayList<BDD> b = new ArrayList<>();
      ArrayList<int[]> ys = new ArrayList<>();
      ArrayList<int[]> xs = new ArrayList<>();
      int gn = g.arity;

      // Qs,Qs1,...,Qsn
      int[] asize = new int[gn + 3];
      int l = asize.length;
      for (int i = 0; i < l - 2; i++) {
         asize[i] = m;
      }
      asize[l - 2] = m * (gn + 1);
      asize[l - 1] = gn * m;

      // Qs, Qs1,...,Qsn, QsQs1...Qsn
      // vpat = {{0,m},{m,m},{2*m,m},....,{n*m,m},{0,(n+1)*m},{m,n*m}}
      int[][] vpat = new int[l][2];
      vpat[0][0] = 0;
      vpat[0][1] = m;
      for (int i = 1; i <= gn; i++) {
         vpat[i][0] = i * m;
         vpat[i][1] = m;
      }
      vpat[gn + 1][0] = 0;
      vpat[gn + 1][1] = (gn + 1) * m;
      vpat[gn + 2][0] = m;
      vpat[gn + 2][1] = gn * m;

      int k1;
      for (int i = 0; i < l; i++) {
         ys.add(new int[asize[i]]);
         xs.add(new int[asize[i]]);
         k1 = 0;
         for (int j = 0; j < vpat[i].length; j = j + 2) {
            System.arraycopy(clauseVarIdx, vpat[i][j], ys.get(i), k1, vpat[i][j + 1]);
            k1 += vpat[i][j + 1];
         }
         System.arraycopy(standardVarIdx, 0, xs.get(i), 0, asize[i]);
      }
      // solve clause body
      b.add(one.id());
      for (int i = 1; i <= gn; i++) {
         b.add(oldqds.id());
      }
      b.add(fInfer.get(g).id());
      b.add(B.makeSet(ys.get(l - 1)));

      // rename solutions using clause variables
      for (int i = 1; i < b.size() - 1; i++) {
         subst.set(xs.get(i), ys.get(i));
         b.get(0).andWith(b.get(i).replaceWith(subst));
      }
      BDD b0 = b.get(0).exist(b.get(l - 1));
      subst.set(ys.get(0), xs.get(0));
      /*for (int i = 0; i < l; i++) {
       b.get(i).free();
       }*/
      return (b0.replaceWith(subst));
   }

   private BDD fInfer(FuncSymb g) {
      BDDPairing subst = B.makePair();

      ArrayList<BDD> b = new ArrayList<>();
      ArrayList<int[]> ys = new ArrayList<>();
      ArrayList<int[]> xs = new ArrayList<>();
      int gn = g.arity;

      // Qs,Qs1,...,Qsn,Ts
      int[] asize = {(gn + 1) * m, gn * m + k, k + m, m, k};
      int l = asize.length;

      // QsQs1...Qsn, Qs1...QsnTs,QsTs,Qs
      int[][] vpat = {{0, (gn + 1) * m}, {m, gn * m + k}, {0, m, (gn + 1) * m, k}, {0, m}, {(gn + 1) * m, k}};

      int k1;
      for (int i = 0; i < l; i++) {
         ys.add(new int[asize[i]]);
         xs.add(new int[asize[i]]);
         k1 = 0;
         for (int j = 0; j < vpat[i].length; j = j + 2) {
            System.arraycopy(clauseVarIdx, vpat[i][j], ys.get(i), k1, vpat[i][j + 1]);
            k1 += vpat[i][j + 1];
         }
         System.arraycopy(standardVarIdx, 0, xs.get(i), 0, asize[i]);
      }

      int[] rhsVarOrder1 = new int[m + k];
      for (int i = 0; i < m + k; i++) {
         int x = rhsVarOrder[i];
         rhsVarOrder1[i] = (x < m) ? x + maxPredArity : x + maxPredArity + gn * m;
      }
      ys.set(2, rhsVarOrder1);
      // solve clause body
      b.add(one.id());
      b.add(lhsAnd.get(g).get(0).id());
      b.add(rhs.get(0).id());
      b.add(nonEmpty.id());
      b.add(B.makeSet(ys.get(l - 1)));

      // rename solutions using clause variables
      for (int i = 1; i < b.size() - 1; i++) {
         subst.set(xs.get(i), ys.get(i));
         b.get(0).andWith(b.get(i).replaceWith(subst));
      }
      BDD b0 = b.get(0).exist(b.get(l - 1));
      subst.set(ys.get(0), xs.get(0));
      /*for (int i = 0; i < l; i++) {
       b.get(i).free();
       }*/
      return (b0.replaceWith(subst));
   }

   private BDD lhsAnd(FuncSymb g, int h) {
      int gn = g.arity;
      if (h < gn - 1) {
         BDDPairing subst = B.makePair();

         ArrayList<BDD> b = new ArrayList<>();
         ArrayList<int[]> ys = new ArrayList<>();
         ArrayList<int[]> xs = new ArrayList<>();

         // Qs1,...,Qsn,Ts, Ts1, Ts2
         int[] asize = {gn * m + k, gn * m + k, m + k, 3 * k, 2 * k};
         int l = asize.length;

         // Qs1...QsnTs, Qs1...QsnTs1, QshTs2, Ts1Ts2Ts, Ts1Ts2
         int[][] vpat = {
            {0, gn * m + k},
            {0, gn * m, gn * m + k, k},
            {h * m, m, gn * m + 2 * k, k},
            {gn * m + k, 2 * k, gn * m, k},
            {gn * m + k, 2 * k}};

         int k1;
         for (int i = 0; i < l; i++) {
            ys.add(new int[asize[i]]);
            xs.add(new int[asize[i]]);
            k1 = 0;
            for (int j = 0; j < vpat[i].length; j = j + 2) {
               System.arraycopy(clauseVarIdx, vpat[i][j], ys.get(i), k1, vpat[i][j + 1]);
               k1 += vpat[i][j + 1];
            }
            System.arraycopy(standardVarIdx, 0, xs.get(i), 0, asize[i]);
         }

         interleave(ys.get(3), k);
         // solve clause body
         b.add(one.id());
         b.add(lhsAnd.get(g).get(h + 1));
         b.add(lhs.get(g).get(h).get(0));
         b.add(andTrans.id());
         b.add(B.makeSet(ys.get(l - 1)));

         // rename solutions using clause variables
         for (int i = 1; i < b.size() - 1; i++) {
            subst.set(xs.get(i), ys.get(i));
            b.get(0).andWith(b.get(i).replaceWith(subst));
         }
         BDD b0 = b.get(0).exist(b.get(l - 1));
         subst.set(ys.get(0), xs.get(0));
         /*for (int i = 0; i < l; i++) {
          b.get(i).free();
          }*/
         return (b0.replaceWith(subst));
      } else { // h=gn-1
         BDDPairing subst = B.makePair();

         ArrayList<BDD> b = new ArrayList<>();
         ArrayList<int[]> ys = new ArrayList<>();
         ArrayList<int[]> xs = new ArrayList<>();

         // Qs1,...,Qsn,Ts
         int[] asize = {gn * m + k, gn * m + k, 0};
         int l = asize.length;

         // Qs1...QsnTs, Qs1...QsnTs
         int[][] vpat = {
            {0, gn * m + k},
            {m * h, m + k},
            {0, 0}};

         int k1;
         for (int i = 0; i < l; i++) {
            ys.add(new int[asize[i]]);
            xs.add(new int[asize[i]]);
            k1 = 0;
            for (int j = 0; j < vpat[i].length; j = j + 2) {
               System.arraycopy(clauseVarIdx, vpat[i][j], ys.get(i), k1, vpat[i][j + 1]);
               k1 += vpat[i][j + 1];
            }
            System.arraycopy(standardVarIdx, 0, xs.get(i), 0, asize[i]);
         }
         // solve clause body
         b.add(one.id());
         b.add(lhs.get(g).get(h).get(0));
         b.add(B.makeSet(ys.get(l - 1)));

         // rename solutions using clause variables
         for (int i = 1; i < b.size() - 1; i++) {
            subst.set(xs.get(i), ys.get(i));
            b.get(0).andWith(b.get(i).replaceWith(subst));
         }
         BDD b0 = b.get(0).id();
         subst.set(ys.get(0), xs.get(0));
         /*for (int i = 0; i < l; i++) {
          b.get(i).free();
          }*/
         return (b0.replaceWith(subst));
      }

   }

   private BDD lhs(FuncSymb g, int h, int r) {
      if (r < m - 1) {
         BDDPairing subst = B.makePair();

         ArrayList<BDD> b = new ArrayList<>();
         ArrayList<int[]> ys = new ArrayList<>();
         ArrayList<int[]> xs = new ArrayList<>();
         int gn = g.arity;

         // Qs,Ts,Ts1,Ts2
         int[] asize = {m + k, m + k, k + 1, 3 * k, 2 * k};
         int l = asize.length;

         // QsTs, QsTs1, QrTs2, Ts1Ts2Ts, Ts1Ts2
         int[][] vpat = {
            {0, m + k},
            {0, m, m + k, k},
            {r, 1, m + 2 * k, k},
            {m + k, 2 * k, m, k},
            {m + k, 2 * k}};

         int k1;
         for (int i = 0; i < l; i++) {
            ys.add(new int[asize[i]]);
            xs.add(new int[asize[i]]);
            k1 = 0;
            for (int j = 0; j < vpat[i].length; j = j + 2) {
               System.arraycopy(clauseVarIdx, vpat[i][j], ys.get(i), k1, vpat[i][j + 1]);
               k1 += vpat[i][j + 1];
            }
            System.arraycopy(standardVarIdx, 0, xs.get(i), 0, asize[i]);
         }
         interleave(ys.get(3), k);

         // solve clause body
         b.add(one.id());
         b.add(lhs.get(g).get(h).get(r + 1));
         b.add(lhsf.get(g).get(h).get(r));
         b.add(orTrans.id());
         b.add(B.makeSet(ys.get(l - 1)));

         // rename solutions using clause variables
         for (int i = 1; i < b.size() - 1; i++) {
            subst.set(xs.get(i), ys.get(i));
            b.get(0).andWith(b.get(i).replaceWith(subst));
         }
         BDD b0 = b.get(0).exist(b.get(l - 1));
         subst.set(ys.get(0), xs.get(0));
         /*for (int i = 0; i < l; i++) {
          b.get(i).free();
          }*/
         return (b0.replaceWith(subst));
      } else { // r=m-1
         BDDPairing subst = B.makePair();

         ArrayList<BDD> b = new ArrayList<>();
         ArrayList<int[]> ys = new ArrayList<>();
         ArrayList<int[]> xs = new ArrayList<>();
         int gn = g.arity;

         // Qs1,...,Qsn,Ts
         int[] asize = {gn * m + k, gn * m + k, 0};
         int l = asize.length;

         // Qs1...QsnTs, Qs1...QsnTs
         int[][] vpat = {
            {0, gn * m + k},
            {r, m + k},
            {0, 0}};

         int k1;
         for (int i = 0; i < l; i++) {
            ys.add(new int[asize[i]]);
            xs.add(new int[asize[i]]);
            k1 = 0;
            for (int j = 0; j < vpat[i].length; j = j + 2) {
               System.arraycopy(clauseVarIdx, vpat[i][j], ys.get(i), k1, vpat[i][j + 1]);
               k1 += vpat[i][j + 1];
            }
            System.arraycopy(standardVarIdx, 0, xs.get(i), 0, asize[i]);
         }
         // solve clause body
         b.add(one.id());
         b.add(lhsf.get(g).get(h).get(r));
         b.add(B.makeSet(ys.get(l - 1)));

         // rename solutions using clause variables
         for (int i = 1; i < b.size() - 1; i++) {
            subst.set(xs.get(i), ys.get(i));
            b.get(0).andWith(b.get(i).replaceWith(subst));
         }
         BDD b0 = b.get(0).id();
         subst.set(ys.get(0), xs.get(0));
         /*for (int i = 0; i < l; i++) {
          b.get(i).free();
          }*/
         return (b0.replaceWith(subst));
      }
   }

   private BDD lhsf(FuncSymb g, int h, int r) {
      String q0 = qIdx.get(r);
      LinkedHashMap<String, BitSet> qmaph = idx.lhsf.get(g).get(h);
      BitSet bs;
      if (qmaph.containsKey(q0)) {
         bs = qmaph.get(q0); // set of transitions
      } else {
         bs = new BitSet(k);
      }

      BDD b0 = one.id();
      BDD b1 = one.id();
      BDD bi;
      for (int i = 0; i < k; i++) {
         bi = standardVars[i + 1];
         if (bs.get(i)) {
            b0.andWith(bi.id());
         } else {
            b0.andWith(bi.id().not());
         }
         b1.andWith(bi.id().not());
      }
      return standardVars[0].id().ite(b0, b1);

   }

   private BDD lhs0(FuncSymb c) {
      BitSet bs = idx.fIndex.get(c); // set of transitions
      BDD b0 = B.one();
      BDD bi;

      for (int i = 0; i < k; i++) {
         bi = standardVars[i];
         if (!bs.get(i)) {
            b0.andWith(bi.id().not());
         } else {
            b0.andWith(bi.id());
         }

      }
      return b0;
   }

   private BDD rhs(int h) {
      int[] rhsVarOrder1 = new int[m + k];
      int[] rhsVarOrder2 = new int[m + k];
      for (int i = 0; i < m + k; i++) {
         int x = rhsVarOrder[i];
         rhsVarOrder1[i] = x + maxPredArity;
         rhsVarOrder2[i] = (x < m) ? x + maxPredArity + m + k : x + maxPredArity;
      }
      System.out.println("Clause vars:");
      for (int i=0; i<maxVarCount; i++){
         System.out.print(clauseVarIdx[i]+" ");
      }
      System.out.println();
      System.out.println("rhs vars (1):");
      for (int i=0; i<m+k; i++){
         System.out.print(rhsVarOrder1[i]+" ");
      }
      System.out.println();
      System.out.println("rhs vars (2):");
      for (int i=0; i<m+k; i++){
         System.out.print(rhsVarOrder2[i]+" ");
      }
      System.out.println();
      if (h < k - 1) {
         BDDPairing subst = B.makePair();

         ArrayList<BDD> b = new ArrayList<>();
         ArrayList<int[]> ys = new ArrayList<>();
         ArrayList<int[]> xs = new ArrayList<>();

         // Qs,Ts,Qs1,Qs2
         int[] asize = {k + m, k + m, m + 1, 3 * m, 2 * m};
         int l = asize.length;

         // 
         int[][] vpat = {
            {0, m + k}, // QsTs
            {k + m, m, m, k}, //Qs1Ts
            {m + h, 1, k + 2 * m, m}, //ThQs2
            {k + m, 2 * m, 0, m}, //Qs1Qs2Qs
            {k + m, 2 * m}};  //Qs1Qs2

         int k1;
         for (int i = 0; i < l; i++) {
            ys.add(new int[asize[i]]);
            xs.add(new int[asize[i]]);
            k1 = 0;
            for (int j = 0; j < vpat[i].length; j = j + 2) {
               System.arraycopy(clauseVarIdx, vpat[i][j], ys.get(i), k1, vpat[i][j + 1]);
               k1 += vpat[i][j + 1];
            }
            System.arraycopy(standardVarIdx, 0, xs.get(i), 0, asize[i]);
         }

         ys.set(0, rhsVarOrder1);
         ys.set(1, rhsVarOrder2);
         interleave(ys.get(3), m);  // to get a better orStates variable ordering

         // solve clause body
         b.add(one.id());
         b.add(rhs.get(h + 1));
         b.add(rhsMap.get(h));
         b.add(orStates.id());
         b.add(B.makeSet(ys.get(l - 1)));

         // rename solutions using clause variables
         for (int i = 1; i < b.size() - 1; i++) {
            subst.set(xs.get(i), ys.get(i));
            b.get(0).andWith(b.get(i).replaceWith(subst));
         }
         BDD b0 = b.get(0).exist(b.get(l - 1));
         subst.set(ys.get(0), xs.get(0));
         //for (int i = 0; i < l; i++) {
         //   b.get(i).free();
         //}

         return (b0.replaceWith(subst));
      } else { // h=k-1
         BDDPairing subst = B.makePair();

         ArrayList<BDD> b = new ArrayList<>();
         ArrayList<int[]> ys = new ArrayList<>();
         ArrayList<int[]> xs = new ArrayList<>();

         // Ts,Qs,Qs1,Qs2
         int[] asize = {k + m, m + 1, 0};
         int l = asize.length;

         // 
         int[][] vpat = {
            {0, k + m}, // QsTs
            {m + h, 1, 0, m}, //ThQs
            {0, 0}};  //

         int k1;
         for (int i = 0; i < l; i++) {
            ys.add(new int[asize[i]]);
            xs.add(new int[asize[i]]);
            k1 = 0;
            for (int j = 0; j < vpat[i].length; j = j + 2) {
               System.arraycopy(clauseVarIdx, vpat[i][j], ys.get(i), k1, vpat[i][j + 1]);
               k1 += vpat[i][j + 1];
            }
            System.arraycopy(standardVarIdx, 0, xs.get(i), 0, asize[i]);
         }
         ys.set(0, rhsVarOrder1);
         // solve clause body
         b.add(one.id());
         b.add(rhsMap.get(h));
         b.add(B.makeSet(ys.get(l - 1)));

         // rename solutions using clause variables
         for (int i = 1; i < b.size() - 1; i++) {
            subst.set(xs.get(i), ys.get(i));
            b.get(0).andWith(b.get(i).replaceWith(subst));
         }
         BDD b0 = b.get(0).id();
         subst.set(ys.get(0), xs.get(0));
         //for (int i = 0; i < l; i++) {
         //  b.get(i).free();
         //}

         return (b0.replaceWith(subst));
      }
   }

   private BDD rhsMap(int h) {
      BDD b0 = one.id();
      BDD b1 = one.id();
      BDD bi;

      String q0 = idx.tindex.get(h + 1).q0;
      for (int i = 0; i < m; i++) {
         bi = standardVars[i + 1];
         if (q0.equals(qIdx.get(i))) {
            b0.andWith(bi.id());
         } else {
            b0.andWith(bi.id().not());
         }
         b1.andWith(bi.id().not());
      }
      return standardVars[0].id().ite(b0, b1);
   }

   private BDD andTrans() {
      BDD b0 = one.id();
      BDD b1, b2, b3;
      for (int i = 0; i < 3 * k; i = i + 3) {
         b1 = standardVars[i].id();
         b2 = standardVars[i + 1].id();
         b3 = standardVars[i + 2].id();
         b0.andWith(b3.biimp(b1.and(b2)));
      }
      return b0;
   }

   private BDD orTrans() {
      BDD b0 = one.id();
      BDD b1, b2, b3;
      for (int i = 0; i < 3 * k; i = i + 3) {
         b1 = standardVars[i].id();
         b2 = standardVars[i + 1].id();
         b3 = standardVars[i + 2].id();
         b0.andWith(b3.biimp(b1.or(b2)));
      }
      return b0;
   }

   private BDD orStates() {
      BDD b0 = one.id();
      BDD b1, b2, b3;
      for (int i = 0; i < 3 * m; i = i + 3) {
         b1 = standardVars[i].id();
         b2 = standardVars[i + 1].id();
         b3 = standardVars[i + 2].id();
         b0.andWith(b3.biimp(b1.or(b2)));
      }
      return b0;
   }

   private BDD nonEmpty() {
      BDD b0 = zero.id();
      BDD bi;
      for (int i = 0; i < m; i++) {
         bi = standardVars[i].id();
         b0.orWith(bi);
      }
      return b0;
   }

   void dftaTransitions() {

   }

   // check inclusion between states in the input FTA
   @Override
   public boolean includes(String q1, String q2) {
      return false;
   }

   /**
    *
    * @param output
    * @param output1
    */
   @Override
   public void printDfta(PrintStream output, PrintStream output1) {

   }

   /**
    *
    * @param output
    */
   @Override
   public void printDftaDatalog(PrintStream output) {

   }

   public long deltaDCount() {
      return 0;
   }

   public long deltaDCountComplete() {
      return 0;
   }

   public Indices getIdx() {
      return idx;
   }

   @Override
   public void showStats(boolean verbose) {
      System.out.println("DFTA states");
      qds.printSet();
      int[] qvs = new int[m];
      System.arraycopy(clauseVarIdx, 0, qvs, 0, m);
      System.out.println();
      System.out.println(qds.satCount(B.makeSet(qvs)));
      System.out.println();
   }
   
   public void showStatsApp(JTextArea ja) {
    }

   private int maxVarCount() {
      int x1 = (maxArity + 1) * m + k;
      int x2 = maxArity * m + 3 * k;
      int x3 = k + 3 * m;
      int r = x1;
      if (x2 > r) {
         r = x2;
      }
      if (x3 > r) {
         r = x3;
      }
      return r;
   }

   private int maxPredArity() {
      int x1 = (maxArity + 1) * m;
      int x2 = maxArity * m + k;
      int x3 = 3 * m;
      int x4 = 3 * k;
      int r = x1;
      if (x2 > r) {
         r = x2;
      }
      if (x3 > r) {
         r = x3;
      }
      if (x4 > r) {
         r = x4;
      }
      return r;
   }

   private void interleave(int[] a, int w) {
      int[] b = new int[3 * w];
      for (int i = 0; i < w; i++) {
         b[i * 3] = a[i];
         b[i * 3 + 1] = a[w + i];
         b[i * 3 + 2] = a[2 * w + i];
      }
      System.arraycopy(b, 0, a, 0, 3 * w);
   }

   void showArray(int[] a) {
      for (int i = 0; i < a.length; i++) {
         System.out.print(a[i] + ", ");
      }
      System.out.println();
   }
}
