package dfta;

import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedHashMap;
import java.util.ArrayList;
import java.util.BitSet;
import java.io.PrintStream;
import com.microsoft.z3.*;
import java.io.File;
import java.io.FileNotFoundException;
import java.util.logging.Level;
import java.util.logging.Logger;
import javax.swing.JTextArea;

public class DeterminiserSAT implements Determiniser {

   Indices idx;
   String ftaId;

   LinkedHashSet<LinkedHashSet<String>> qd = new LinkedHashSet<>();
   ArrayList<PTransition> deltad = new ArrayList<>();

   LinkedHashMap<FuncSymb, ArrayList<LinkedHashMap<BitSet, LinkedHashSet<LinkedHashSet<String>>>>> t_inverse_table;
   LinkedHashMap<FuncSymb, ArrayList<LinkedHashSet<BitSet>>> psi
           = new LinkedHashMap<>();
   LinkedHashMap<FuncSymb, ArrayList<BitSet>> psi_glb;

   boolean dontCare = true;
   boolean any = false;
   boolean includesCheck = false;
   boolean verbose;

   LinkedHashSet<String> q1;  //  final states of FTA 1
   LinkedHashSet<String> q2;  //  final states of FTA 2 

   LinkedHashMap<FuncSymb, LinkedHashMap<Integer, ArrayList<ArrayList<Integer>>>> exprMap = new LinkedHashMap<>();
   LinkedHashMap<FuncSymb, LinkedHashSet<Integer>> constMap = new LinkedHashMap<>();
   LinkedHashMap<Integer, String> qIdx = new LinkedHashMap<>();
   LinkedHashMap<String, Integer> qIdxInv = new LinkedHashMap<>();

   Context ctx;
   Solver solver;
   int maxArity;

   public DeterminiserSAT(String ftaId, LinkedHashSet transitions, LinkedHashSet finalStates, boolean any, boolean dontCare, boolean verbose) {
      this.verbose = verbose;
      this.psi_glb = new LinkedHashMap<>();
      this.t_inverse_table = new LinkedHashMap<>();
      this.ftaId = ftaId;
      idx = new Indices(transitions, finalStates);
      this.any = any;
      this.dontCare = dontCare;
      includesCheck = false;

      LinkedHashMap<String, String> cfg = new LinkedHashMap<>();
      cfg.put("model", "true");
      ctx = new Context(cfg);
      solver = ctx.mkSolver("QF_BV");

   }

   @Override
   public void makeDfta() {
      idx.genDelta(ftaId);
      idx.genFinalStates(ftaId);
      if (any) {
         idx.genDeltaAny();
      }
      idx.buildIndices();
      Iterator iter = idx.sigma.iterator();
      maxArity = 0;
      FuncSymb f1;
      while (iter.hasNext()) {
         f1 = (FuncSymb) iter.next();
         if (f1.arity > maxArity) {
            maxArity = f1.arity;
         }
      }
      //idx.showIndices();
      dftaStates();
      if (verbose) {
         System.out.println("Made states");
      }

   }

   public boolean dftaStates() {
      if (verbose) {
         System.out.println("Building DFTA states...");
      }
      Iterator iter;
      LinkedHashSet<String> q0;
      FuncSymb f;
      LinkedHashSet<LinkedHashSet<String>> qdnew, qdnew1;

      makeStateConstraints();
      LinkedHashMap<FuncSymb, BoolExpr> boolConstraints = makeBoolConstraint(ctx);
      ArrayList<BoolExpr> solutions = new ArrayList<>();

      // Initialise array of solutions
      int qsize = idx.qs.size();
      for (int j = 0; j < maxArity + 1; j++) {
         solutions.add(ctx.mkFalse());
      }

      iter = idx.sigma.iterator();
      while (iter.hasNext()) {
         f = (FuncSymb) iter.next();
         if (f.arity == 0) {
            q0 = rhsSet(idx.fIndex.get(f));
            if (!q0.isEmpty()) {
               if (qd.add(q0)) {
                  for (int j = 0; j < maxArity + 1; j++) {
                     solutions.set(j, ctx.mkOr(solutions.get(j), makeSoln(q0, qsize, j * qsize)));
                  }
                  //System.out.println("New solution set " + solutions.get(0));
               }
               if (includesCheck) {
                  if (!inclusionCheckState(q0, q1, q2)) {
                     return false;
                  }
               }
            }
         }
      }

      qdnew = (LinkedHashSet<LinkedHashSet<String>>) qd.clone();
      qdnew1 = new LinkedHashSet<>();
      // Compute DFTA States - main loop
      LinkedHashSet<LinkedHashSet<String>> newqs;
      do {
         qdnew1.clear();
         iter = idx.sigma.iterator();
         while (iter.hasNext() && qdnew1.isEmpty()) {
            f = (FuncSymb) iter.next();
            if (f.arity > 0) {
               for (int y = 0; y < f.arity && qdnew1.isEmpty(); y++) {
                  try {
                     newqs = findSatState(f, qdnew, y, boolConstraints, solutions);
                     if (!newqs.isEmpty()) {
                        qdnew1.addAll(newqs);
                        qd.addAll(newqs);
                        for (LinkedHashSet<String> qq : newqs) {
                           solutions.set(0, ctx.mkOr(solutions.get(0), makeSoln(qq, qsize, 0)));
                        }
                     }
                  } catch (FileNotFoundException ex) {
                     Logger.getLogger(DeterminiserSAT.class.getName()).log(Level.SEVERE, null, ex);
                  }
               }
            }
         }
         System.out.println(qd.size());
         for (LinkedHashSet<String> qq : qdnew1) {
            for (int i = 1; i < maxArity + 1; i++) {
               solutions.set(i, ctx.mkOr(solutions.get(i), makeSoln(qq, qsize, i * qsize)));
            }
         }
         qdnew.clear();
         qdnew.addAll(qdnew1);
      } while (!qdnew.isEmpty());
      return true;

   }

   void dftaTransitions() {

   }

   LinkedHashSet<String> rhsSet(BitSet tSet
   ) {
      FTATransition t;
      LinkedHashSet<String> result = new LinkedHashSet<>();
      for (int i = tSet.nextSetBit(0); i >= 0; i = tSet.nextSetBit(i + 1)) {
         t = idx.tindex.get(i + 1);
         result.add(t.q0);
      }
      return result;
   }

   BitSet intersect(ArrayList<BitSet> d
   ) {
      BitSet result = (BitSet) d.get(0).clone();
      for (int i = 1; i < d.size(); i++) {
         result.and(d.get(i));
      }
      return result;
   }

// check inclusion between states in the input FTA
   @Override
   public boolean includes(String q1, String q2
   ) {
      Iterator iter;
      LinkedHashSet<String> q;
      boolean includes = true;
      iter = qd.iterator();
      while (iter.hasNext() && includes) {
         q = (LinkedHashSet<String>) iter.next();
         includes = includes && (!q.contains(q1) || q.contains(q2));
      }
      return includes;
   }

   // check inclusion between states in the input FTA
   public boolean inclusionCheck(LinkedHashSet<String> q1, LinkedHashSet<String> q2) {
      Iterator iter, qiter1, qiter2;
      String x;
      LinkedHashSet<String> q;
      boolean includes = true;
      boolean b;
      iter = qd.iterator();
      while (iter.hasNext() && includes) {
         q = (LinkedHashSet<String>) iter.next();
         qiter1 = q1.iterator();
         while (qiter1.hasNext()) {
            x = (String) qiter1.next();
            if (q.contains(x)) {
               b = false;
               qiter2 = q2.iterator();
               while (qiter2.hasNext() && !b) {
                  if (q.contains((String) qiter2.next())) {
                     b = true;
                  }
               }
               includes = includes && b;
            }
         }
      }
      return includes;
   }

// check inclusion between states in the input FTA
   public boolean inclusionCheckState(LinkedHashSet<String> q0, LinkedHashSet<String> q1, LinkedHashSet<String> q2) {
      Iterator iter, qiter1, qiter2;
      String x;
      boolean includes = true;
      boolean b;

      qiter1 = q1.iterator();
      while (qiter1.hasNext()) {
         x = (String) qiter1.next();
         if (q0.contains(x)) {
            b = false;
            qiter2 = q2.iterator();
            while (qiter2.hasNext() && !b) {
               if (q0.contains((String) qiter2.next())) {
                  b = true;
               }
            }
            includes = includes && b;
         }
      }
      return includes;
   }

   @Override
   public void printDfta(PrintStream output, PrintStream output1) {
      output.println();
      deltad.stream().forEach((deltad1) -> {
         output.println(deltad1.toString() + ".");
      });
   }

   @Override
   public void printDftaDatalog(PrintStream output) {

   }

   public long deltaDCount() {
      double count = 0;
      double tcount;
      double argsize;
      double qdsize = qd.size();
      ArrayList<LinkedHashSet<LinkedHashSet<String>>> lhs;
      for (PTransition deltad1 : deltad) {
         lhs = deltad1.lhs;
         tcount = 1.0;
         for (LinkedHashSet<LinkedHashSet<String>> lh : lhs) {
            argsize = lh.size();
            if (argsize == 0) {
               argsize = qdsize;  // don't care argument
            }
            tcount = tcount * argsize;
         }
         count = count + tcount;
      }
      return Math.round(count);
   }

   public long deltaDCountComplete() {
      Iterator iter = idx.sigma.iterator();
      double count = 0;
      FuncSymb f;
      double qdsize = qd.size();
      while (iter.hasNext()) {
         f = (FuncSymb) iter.next();
         count = count + Math.pow(qdsize, (double) f.arity);
      }
      return Math.round(count);
   }

   /**
    *
    */
   @Override
   public void showStats(boolean verbose) {
      if (verbose) {
         System.out.println();
         System.out.print("Number of input FTA states = ");
      }
      System.out.print(idx.qs.size() + ", ");
      if (verbose) {
         System.out.println();
         System.out.print("Number of input FTA transitions = ");
      }
      System.out.print(idx.delta.size() + ", ");
      if (verbose) {
         System.out.println();
         System.out.print("Number of DFTA states = ");
      }
      System.out.print(qd.size() + ", ");
      if (any) {
         if (verbose) {
            System.out.println();
            System.out.print("Number of DFTA transitions = ");
         }
         System.out.print(deltaDCountComplete() + ", ");
      } else {
         if (verbose) {
            System.out.println();
            System.out.print("Number of DFTA transitions = ");
         }
         System.out.print(deltaDCount() + ", ");
      }
      if (verbose) {
         System.out.println();
         System.out.print("Number of DFTA product transitions = ");
      }
      System.out.print(deltad.size() + ", ");
   }

   public void showStatsApp(JTextArea ja) {

        ja.append("Number of input FTA states = " + idx.qs.size() + "\n");
        ja.append("Number of input FTA transitions = " + idx.delta.size() + "\n");
        ja.append("Number of DFTA states = " + qd.size() + "\n");
        ja.append("Number of DFTA transitions = " + deltad.size() + "\n");
    }
   
   public LinkedHashSet<LinkedHashSet<String>> getQd() {
      return qd;
   }

   public ArrayList<PTransition> getDeltad() {
      return deltad;
   }

   /**
    *
    * @return
    */
   @Override
   public Indices getIdx() {
      return idx;
   }

   void showQD() {
      Iterator i;
      i = qd.iterator();
      while (i.hasNext()) {
         System.out.println((LinkedHashSet<String>) i.next());
      }
   }

   private void makeStateConstraints() {
      int m = idx.qs.size();
      Iterator iter = idx.qs.iterator();
      int qn = 0;
      String q1;
      while (iter.hasNext()) {
         q1 = (String) iter.next();
         qIdxInv.put(q1, qn);
         qIdx.put(qn, q1);
         qn++;
      }
      for (FTATransition t : idx.delta) {
         if (t.f.arity > 0) {
            ArrayList<Integer> lhs = new ArrayList<>();
            for (int i = 0; i < t.f.arity; i++) {
               lhs.add((i + 1) * m + qIdxInv.get(t.lhs.get(i)));
            }
            if (!exprMap.containsKey(t.f)) {
               exprMap.put(t.f, new LinkedHashMap<>());
            }
            if (!exprMap.get(t.f).containsKey(qIdxInv.get(t.q0))) {
               exprMap.get(t.f).put(qIdxInv.get(t.q0), new ArrayList<>());
            }
            exprMap.get(t.f).get(qIdxInv.get(t.q0)).add(lhs);
         }
      }
      if (verbose) {
         System.out.println(exprMap);
      }
   }

   private LinkedHashMap<FuncSymb, BoolExpr> makeBoolConstraint(Context ctx) {
      LinkedHashMap<FuncSymb, BoolExpr> result = new LinkedHashMap<>();
      Sort bool_type = ctx.getBoolSort();
      BoolExpr[] expr = new BoolExpr[idx.qs.size()];
      for (FuncSymb f : idx.sigma) {
         if (f.arity > 0) {
            for (int i = 0; i < idx.qs.size(); i++) {
               BoolExpr xi = (BoolExpr) ctx.mkConst("x" + i, bool_type);
               if (exprMap.get(f).containsKey(i)) {
                  BoolExpr[] disj = new BoolExpr[exprMap.get(f).get(i).size()];
                  for (int j = 0; j < exprMap.get(f).get(i).size(); j++) {
                     BoolExpr[] conj = new BoolExpr[f.arity];
                     int v;
                     for (int k = 0; k < f.arity; k++) {
                        v = exprMap.get(f).get(i).get(j).get(k);
                        conj[k] = (BoolExpr) ctx.mkConst("x" + v, bool_type);
                     }
                     disj[j] = ctx.mkAnd(conj);
                  }
                  expr[i] = ctx.mkOr(disj);
                  if (result.containsKey(f)) {
                     result.put(f, ctx.mkAnd(result.get(f), ctx.mkIff(xi, expr[i])));
                  } else {
                     result.put(f, ctx.mkIff(xi, expr[i]));
                  }
               } else if (result.containsKey(f)) {
                  result.put(f, ctx.mkAnd(result.get(f), ctx.mkNot(xi)));
               } else {
                  result.put(f, ctx.mkNot(xi));
               }
            }
         }
      }
      return result;
   }

   private BoolExpr makeSoln(LinkedHashSet<String> qs, int m, int mIdx) {
      BoolExpr[] b = new BoolExpr[m];
      Sort bool_type = ctx.getBoolSort();
      int y;
      for (int i = 0; i < m; i++) {
         y = i + mIdx;
         BoolExpr xi = (BoolExpr) ctx.mkConst("x" + y, bool_type);
         if (qs.contains(qIdx.get(i))) {
            b[i] = xi;
         } else {
            b[i] = ctx.mkNot(xi);
         }
      }
      BoolExpr ret = ctx.mkAnd(b);
      //System.out.println(ret);
      return ret;
   }

   private LinkedHashSet<LinkedHashSet<String>> findSatState(FuncSymb f, LinkedHashSet<LinkedHashSet<String>> qdnew, int j, LinkedHashMap<FuncSymb, BoolExpr> boolConstraints, ArrayList<BoolExpr> solutions) throws FileNotFoundException {
      LinkedHashSet<String> newState;
      int m = idx.qs.size();
      Sort bool_type = ctx.getBoolSort();
      LinkedHashSet<LinkedHashSet<String>> result = new LinkedHashSet<>();
      for (LinkedHashSet<String> qdstate : qdnew) {
         solver.reset();
         solver.add(boolConstraints.get(f));
         solver.add(nonEmptyConstraint(m));
         solver.add(ctx.mkNot(solutions.get(0)));
         for (int i = 0; i < f.arity; i++) {
//            if (j == i) {
//               solver.add(makeSoln(qdstate, m, m * (j + 1)));
//            } else {
            solver.add(solutions.get(i + 1));
//            }
         }
         if (solver.check() == Status.SATISFIABLE) {
//            if (qd.size() == 50) {
//               PrintStream modelFile = new PrintStream(new File("/Users/jpg/Desktop/model.txt"));
//
//               modelFile.println(solver.toString());
//               modelFile.close();
//            }
            newState = new LinkedHashSet<>();
            Model model = solver.getModel();
            for (int i = 0; i < m; i++) {
               BoolExpr xi = (BoolExpr) ctx.mkConst("x" + i, bool_type);
               if (model.evaluate(xi, false).toString().equals("true")) {
                  newState.add(qIdx.get(i));
               }
            }
            result.add(newState);
         }
      }
      return result;  // empty set if no satisfiable solution found
   }

   private BoolExpr nonEmptyConstraint(int m) {
      BoolExpr[] b = new BoolExpr[m];
      Sort bool_type = ctx.getBoolSort();
      for (int i = 0; i < m; i++) {
         BoolExpr xi = (BoolExpr) ctx.mkConst("x" + i, bool_type);
         b[i] = xi;
      }
      return ctx.mkOr(b);
   }

   private BoolExpr[] makeBoolArray(ArrayList<BoolExpr> bs) {
      BoolExpr[] result = new BoolExpr[bs.size()];
      result = bs.toArray(result);
      return result;
   }
}
