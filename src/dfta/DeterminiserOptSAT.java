package dfta;

import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedHashMap;
import java.util.ArrayList;
import java.util.BitSet;
import java.io.PrintStream;
import com.microsoft.z3.*;
import javax.swing.JTextArea;

public class DeterminiserOptSAT implements Determiniser {

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

   public DeterminiserOptSAT(String ftaId, LinkedHashSet transitions, LinkedHashSet finalStates, boolean any, boolean dontCare, boolean verbose) {
      this.verbose = verbose;
      this.psi_glb = new LinkedHashMap<>();
      this.t_inverse_table = new LinkedHashMap<>();
      this.ftaId = ftaId;
      idx = new Indices(transitions, finalStates);
      this.any = any;
      this.dontCare = dontCare;
      includesCheck = false;
      ctx = new Context(); // for Z3 solver
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
      Iterator iter = idx.qs.iterator();
      int qn = 0;
      String qj;
      while (iter.hasNext()) {
         qj = (String) iter.next();
         qIdxInv.put(qj, qn);
         qIdx.put(qn, qj);
         qn++;
      }
      //System.out.println("qIdx: " + qIdx);
      iter = idx.sigma.iterator();
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
      dftaTransitions();
   }

   public boolean dftaStates() {
      if (verbose) {
         System.out.println("Building DFTA states...");
      }
      Iterator iter;
      int temp, z;
      LinkedHashSet<String> q0;
      FuncSymb f;
      ArrayList<LinkedHashSet<BitSet>> phi_f, psi_f;
      LinkedHashSet<BitSet> phi_f_j;
      ArrayList<ArrayList<BitSet>> psi_phi_tuple;
      ArrayList<BitSet> deltatuple;

      LinkedHashMap<FuncSymb, ArrayList<LinkedHashSet<BitSet>>> phi
              = new LinkedHashMap<>();

      LinkedHashSet<LinkedHashSet<String>> qdnew, qdold, qdnew1;

      //makeStateConstraints();
      //LinkedHashMap<FuncSymb, BoolExpr> boolConstraints = makeBoolConstraint();
      LinkedHashMap<FuncSymb, BoolExpr> transConstraints = makeTransConstraint();
      ArrayList<BoolExpr> solutions = new ArrayList<>();
      LinkedHashMap<FuncSymb, ArrayList<BoolExpr>> phi_solutions = new LinkedHashMap<>();

      // Initialise array of solutions
      int qsize = idx.qs.size();
      for (int j = 0; j < maxArity + 1; j++) {
         solutions.add(ctx.mkFalse());
      }
      for (FuncSymb g : idx.sigma) {
         if (g.arity > 0) {
            phi_solutions.put(g, new ArrayList<>());
            for (int i = 0; i < g.arity; i++) {
               phi_solutions.get(g).add(ctx.mkFalse());
            }
         }
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
               }
               if (includesCheck) {
                  if (!inclusionCheckState(q0, q1, q2)) {
                     return false;
                  }
               }
            }
         }
      }
      // Initialise Psi_1 ... Psi_n and Phi_1 ... Phi_n for each f/n
      // Initialise the t_inverse_table
      iter = idx.sigma.iterator();
      while (iter.hasNext()) {
         f = (FuncSymb) iter.next();
         if (f.arity > 0) {
            psi_glb.put(f, new ArrayList<>());
            psi_f = new ArrayList<>(f.arity);
            phi_f = new ArrayList<>(f.arity);
            t_inverse_table.put(f, new ArrayList<>());
            for (int j = 0; j < f.arity; j++) {
               psi_f.add(j, new LinkedHashSet<>());
               phi_f.add(j, new LinkedHashSet<>());
               t_inverse_table.get(f).add(j, new LinkedHashMap<>());
               psi_glb.get(f).add(j, new BitSet(idx.delta.size()));
            }
            psi.put(f, psi_f);
            phi.put(f, phi_f);
         }
      }

      qdnew = (LinkedHashSet<LinkedHashSet<String>>) qd.clone();
      deltatuple = new ArrayList<>();
      psi_phi_tuple = new ArrayList<>();

      qdnew1 = new LinkedHashSet<>();

      // Compute DFTA States - main loop
      do {
         qdnew1.clear();
         iter = idx.sigma.iterator();
         while (iter.hasNext()) {
            f = (FuncSymb) iter.next();
            psi_f = psi.get(f);
            phi_f = phi.get(f);

            if (f.arity > 0) {  // initialise the Phi and Psi tuples 
               LinkedHashSet<LinkedHashSet<String>> qdpruned = new LinkedHashSet<>();

               for (int j = 0; j < f.arity; j++) {
                  //qdpruned = pruneStates1(f, qdnew, j, boolConstraints, solutions);
                  phi_f_j = t(j, f, qdnew);
                  phi_f_j.removeAll(psi_f.get(j));  // remove sets already computed for jth argument
                  phi_f.set(j, phi_f_j);

                  //l = phi_f_j.iterator();
               }
               for (int j = 0; j < f.arity; j++) {
                  if (phi_f.get(j).size() > 0) { // if size of phi_f[j] = 0 then prod will be 0
                     psi_phi_tuple.clear();
                     for (int k = 0; k < f.arity; k++) {
                        if (k < j) {
                           psi_phi_tuple.add(k, new ArrayList<>(psi_f.get(k)));
                        } else if (k == j) {
                           psi_phi_tuple.add(k, new ArrayList<>(phi_f.get(j)));
                        } else {
                           psi_phi_tuple.add(k, new ArrayList<>(phi_f.get(k)));
                           psi_phi_tuple.get(k).addAll(psi_f.get(k));
                        }
                     }
                     //System.out.println("Before pruning " + f + " :" + psi_phi_tuple);
                     psi_phi_tuple = pruneTrans(j, f, psi_phi_tuple, transConstraints, solutions);
                     //System.out.println("After pruning " + f + " :" + psi_phi_tuple);
                     int prod = 1;
                     for (int k = 0; k < f.arity; k++) {
                        prod = prod * psi_phi_tuple.get(k).size();
                     }
                     for (int k = 0; k < prod; k++) { // enumerate the delta-tuples (cartesian product)
                        temp = k;
                        // Re-initialise delta-tuple
                        deltatuple.clear();
                        for (int m = 0; m < f.arity; m++) {
                           z = psi_phi_tuple.get(m).size();
                           deltatuple.add(m, psi_phi_tuple.get(m).get(temp % z));
                           temp = temp / z;
                        }
                        q0 = rhsSet(intersect(deltatuple));
                        if (!q0.isEmpty()) {
                           if (qd.add(q0)) {
                              qdnew1.add(q0);

                              //System.out.print("*("+q0.size()+")");  // new element
                              if (includesCheck) {
                                 if (!inclusionCheckState(q0, q1, q2)) {
                                    return false;
                                 }
                              }
                           }
                        }
                        //else System.out.print("-("+q0.size()+")");  // duplicate
                        //else
                        //System.out.print(".");  // empty set
                     }

                  }
               }
               for (int j = 0; j < f.arity; j++) {
                  psi_f.get(j).addAll(phi_f.get(j));
               }
            }
         }
         qdnew.clear();
         qdnew.addAll(qdnew1);
         for (LinkedHashSet<String> newq : qdnew1) {
            for (int i = 0; i < maxArity + 1; i++) {
               solutions.set(i, ctx.mkOr(solutions.get(i), makeSoln(newq, qsize, i * qsize)));
            }
         }
         if (verbose) {
            System.out.println("Qdnew: " + qdnew.size());
         }
      } while (!qdnew.isEmpty());
      return true;
   }

   void dftaTransitions() {
      if (verbose) {
         System.out.println("Building DFTA product transitions...");
      }
      Iterator i = idx.sigma.iterator();
      FuncSymb f;
      LinkedHashSet<String> q0;
      ArrayList<ArrayList<BitSet>> psi_tuple;
      ArrayList<BitSet> deltatuple;
      ArrayList<LinkedHashSet<LinkedHashSet<String>>> lhs;
      int temp, z;

      // make a hashmap yielding canonical names for the elements of qd
      // E.g. {q1,q2} and {q2,q1} 
      LinkedHashMap<LinkedHashSet<String>, LinkedHashSet<String>> qdnames = new LinkedHashMap<>();
      Iterator qdi = qd.iterator();
      while (qdi.hasNext()) {
         q0 = (LinkedHashSet<String>) qdi.next();
         qdnames.put(q0, q0);
      }

      while (i.hasNext()) {
         f = (FuncSymb) i.next();
         if (f.arity == 0) {
            q0 = rhsSet(idx.fIndex.get(f));
            if (!q0.isEmpty()) {
               deltad.add(new PTransition(f, qdnames.get(q0)));
            }
         } else {
            psi_reinit(f);
            psi_tuple = new ArrayList<>();
            // Initialise delta-tuple and psi-tuple
            deltatuple = new ArrayList<>();
            for (int j = 0; j < f.arity; j++) {
               psi_tuple.add(j, new ArrayList<>(psi.get(f).get(j)));
               deltatuple.add(j, new BitSet(idx.delta.size()));
            }
            // check for don't care arguments for functions of arity > 1
            // remove such arguments from the psi-tuple
            if (f.arity > 1 && dontCare) {
               dontCareArgs(psi_tuple, f);
            }
            int prod = 1;
            for (int j = 0; j < f.arity; j++) {
               prod = prod * psi_tuple.get(j).size();
            }
            if (verbose) {
               System.out.println("Computing transitions for " + f);
            }
            for (int j = 0; j < prod; j++) { // enumerate the delta-tuples
               temp = j;
               for (int k = 0; k < f.arity; k++) {
                  z = psi_tuple.get(k).size();
                  deltatuple.set(k, psi_tuple.get(k).get(temp % z));
                  temp = temp / z;
               }

               q0 = rhsSet(intersect(deltatuple));

               if (!q0.isEmpty()) {
                  lhs = new ArrayList<>();
                  for (int m = 0; m < f.arity; m++) {
                     lhs.add(m, t_inverse_table.get(f).get(m).get(deltatuple.get(m)));
                  }
                  deltad.add(new PTransition(f, qdnames.get(q0), lhs));
               }
            }
         }
      }
   }

   LinkedHashSet<String> rhsSet(BitSet tSet) {
      FTATransition t;
      LinkedHashSet<String> result = new LinkedHashSet<>();
      for (int i = tSet.nextSetBit(0); i >= 0; i = tSet.nextSetBit(i + 1)) {
         t = idx.tindex.get(i + 1);
         result.add(t.q0);
      }
      return result;
   }

   BitSet intersect(ArrayList<BitSet> d) {
      BitSet result = (BitSet) d.get(0).clone();
      for (int i = 1; i < d.size(); i++) {
         result.and(d.get(i));
      }
      return result;
   }

   LinkedHashSet<BitSet> t(int i, FuncSymb f, LinkedHashSet<LinkedHashSet<String>> qss) {
      Iterator k = qss.iterator();
      LinkedHashSet<BitSet> result = new LinkedHashSet<>();
      LinkedHashSet<String> qs;
      BitSet h;
      while (k.hasNext()) {
         qs = (LinkedHashSet<String>) k.next();
         h = lhsSet(i, f, qs);
         if (!h.isEmpty()) {
            result.add(h);
         }
      }
      return result;
   }

   BitSet lhsSet(int i, FuncSymb f, LinkedHashSet<String> qs) {
      Iterator k = qs.iterator();
      BitSet result = new BitSet(idx.delta.size());
      LinkedHashMap<String, BitSet> lhsmap = idx.lhsf.get(f).get(i);
      String q;
      while (k.hasNext()) {
         q = (String) k.next();
         if (lhsmap.containsKey(q)) {
            result.or(lhsmap.get(q));
         }
      }
      // Tabulate result for the t_inverse function
      if (!result.isEmpty()) {
         LinkedHashMap<BitSet, LinkedHashSet<LinkedHashSet<String>>> hm = t_inverse_table.get(f).get(i);
         if (!hm.containsKey(result)) {
            hm.put(result, new LinkedHashSet<>());
         }
         hm.get(result).add(qs);
      }
      return result;
   }

   void dontCareArgs(ArrayList<ArrayList<BitSet>> psi_tuple, FuncSymb f) {
      LinkedHashSet<LinkedHashSet<String>> qs;
      ArrayList<BitSet> psiIntersectTuple = new ArrayList<>();
      BitSet ts;
      ArrayList<LinkedHashSet<LinkedHashSet<String>>> lhs;
      LinkedHashSet<String> rhs;
      BitSet temp;
      BitSet deltaj;
      ArrayList<LinkedHashSet<BitSet>> dontCares = new ArrayList<>();

      // Intersect elements of psi-tuple and initialise don't-care array
      for (int i = 0; i < f.arity; i++) {
         if (!psi_tuple.get(i).isEmpty()) {
            psiIntersectTuple.add(i, intersect(psi_tuple.get(i)));
         } else {
            psiIntersectTuple.add(i, new BitSet(idx.delta.size()));
         }
         dontCares.add(i, new LinkedHashSet<>());
      }

      for (int i = 0; i < f.arity; i++) {
         temp = psiIntersectTuple.get(i);
         for (int j = 0; j < psi_tuple.get(i).size(); j++) {
            deltaj = psi_tuple.get(i).get(j);
            psiIntersectTuple.set(i, deltaj);
            rhs = rhsSet(deltaj);
            if (rhs.equals(rhsSet(intersect(psiIntersectTuple)))) {
               // generate a don't care transition
               lhs = new ArrayList<>();
               for (int k = 0; k < f.arity; k++) {
                  lhs.add(k, new LinkedHashSet<>());
                  if (k == i) {
                     lhs.set(k, t_inverse_table.get(f).get(i).get(deltaj));
                  }
               }
               deltad.add(new PTransition(f, rhs, lhs));
               dontCares.get(i).add(deltaj);
            } else if (f.arity == 2 && isSingleton(rhs) && intersectsAll(deltaj, i, f, psi_tuple)) {
               lhs = new ArrayList<>();
               for (int k = 0; k < f.arity; k++) {
                  lhs.add(k, new LinkedHashSet<>());
                  if (k == i) {
                     lhs.set(k, t_inverse_table.get(f).get(i).get(deltaj));
                  }
               }
               deltad.add(new PTransition(f, rhs, lhs));
               dontCares.get(i).add(deltaj);
            }
         }
         psiIntersectTuple.set(i, temp);
      }
      for (int i = 0; i < f.arity; i++) {
         psi_tuple.get(i).removeAll(dontCares.get(i));
      }
   }

   boolean isSingleton(LinkedHashSet<String> s) {
      return s.size() == 1;
   }

   boolean intersectsAll(BitSet deltaj, int j, FuncSymb f, ArrayList<ArrayList<BitSet>> psi_tuple) {
      // check whether deltaj intersects with all members of all non-j elements of psi_tuple
      BitSet ts;
      for (int k = 0; k < f.arity; k++) {
         if (k != j) {
            if (psi_tuple.get(k).isEmpty()) {
               return false;
            }
            for (int l = 0; l < psi_tuple.get(k).size(); l++) {
               ts = (BitSet) deltaj.clone();
               ts.and(psi_tuple.get(k).get(l));
               if (ts.isEmpty()) {
                  return false;
               }
            }
         }
      }
      return true;
   }

// check inclusion between states in the input FTA
   @Override
   public boolean includes(String q1, String q2) {
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
      PTransition t;
      FuncSymb f;
      LinkedHashSet<String> q0;
      int n;

      ArrayList<LinkedHashSet<LinkedHashSet<String>>> lhs;
      ArrayList<String> args;
      LinkedHashMap<LinkedHashSet<LinkedHashSet<String>>, String> productNames = new LinkedHashMap<>();
      LinkedHashMap<LinkedHashSet<String>, String> stateNames = new LinkedHashMap<>();
      String head, body;

      // make state names q0, q1,... from elements of qd
      // print dictionary of state names as comments
      Iterator iter = qd.iterator();
      Iterator iter1;
      LinkedHashSet<String> q;
      int j = 0;
      output.println();
      while (iter.hasNext()) {
         q = (LinkedHashSet<String>) iter.next();
         stateNames.put(q, "qq" + j);
         j++;
         output.println("### " + q + " --> " + stateNames.get(q));
      }
      output.println();

      // print transitions as datalog clauses
      j = 0;
      for (PTransition deltad1 : deltad) {
         t = deltad1;
         f = t.f;
         lhs = t.lhs;
         q0 = t.q0;
         args = new ArrayList<>();
         for (int m = 0; m < lhs.size(); m++) {
            if (lhs.get(m).size() > 1) {
               if (!productNames.containsKey(lhs.get(m))) {
                  productNames.put(lhs.get(m), "product" + j);
                  j++;
               }
               args.add(m, "X" + m);
            } else if (lhs.get(m).size() < 1) { // empty set
               if (!productNames.containsKey(lhs.get(m))) {
                  productNames.put(lhs.get(m), "dontCare");
               }
               args.add(m, "X" + m);
            } else {
               iter1 = lhs.get(m).iterator();
               args.add(m, stateNames.get((LinkedHashSet<String>) iter1.next())); // singleton product state
            }
         }
         head = f.datalogName() + "(";
         for (String arg : args) {
            head += arg + ",";
         }
         head += stateNames.get(q0) + ")";
         // construct body
         body = "";
         int k = 0;
         for (int m = 0; m < args.size(); m++) {
            if (lhs.get(m).size() != 1) {
               if (k > 0) {
                  body += ",";
               }
               body += productNames.get(lhs.get(m)) + "(" + args.get(m) + ")";
               k++;
            }
         }
         if (k == 0) {
            output.println(head + ".");
         } else {
            output.println(head + " :- " + body + ".");
         }
      }

      // print product state clauses
      output.println();
      output.println("### Product states");
      iter = productNames.keySet().iterator();
      LinkedHashSet<LinkedHashSet<String>> product;
      String pName;
      while (iter.hasNext()) {
         product = (LinkedHashSet<LinkedHashSet<String>>) iter.next();
         pName = productNames.get(product);
         head = pName + "(";
         if (product.isEmpty()) {
            product = qd;
         }
         iter1 = product.iterator();
         while (iter1.hasNext()) {
            output.println(head + stateNames.get((LinkedHashSet<String>) iter1.next()) + ").");
         }
      }
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

   void psi_reinit(FuncSymb f) {
      psi.get(f).clear();
      for (int j = 0; j < f.arity; j++) {
         psi.get(f).add(j, t(j, f, qd));
      }
   }

   LinkedHashSet<BitSet> intersectCartProd(ArrayList<ArrayList<BitSet>> psi_phi_tuple, int k) {
      LinkedHashSet<BitSet> result = new LinkedHashSet<>();
      BitSet t;
      if (k == psi_phi_tuple.size() - 1) {
         for (int i = 0; i < psi_phi_tuple.get(k).size(); i++) {
            result.add((BitSet) (psi_phi_tuple.get(k).get(i)).clone());
         }
         return result;
      } else {
         LinkedHashSet<BitSet> r = intersectCartProd(psi_phi_tuple, k + 1);
         Iterator i = r.iterator();
         while (i.hasNext()) {
            t = (BitSet) i.next();
            for (int j = 0; j < psi_phi_tuple.get(k).size(); j++) {
               BitSet u = (BitSet) t.clone();
               u.and(psi_phi_tuple.get(k).get(j));
               if (!u.isEmpty()) {
                  result.add(u);
               }
            }
         }
      }
      return result;
   }

   private void makeStateConstraints() {
      int m = idx.qs.size();

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

   private LinkedHashMap<FuncSymb, BoolExpr> makeTransConstraint() {
      FTATransition t;
      int m = idx.qs.size();
      int k = idx.delta.size();
      Sort bool_type = ctx.getBoolSort();
      LinkedHashMap<FuncSymb, BoolExpr> result = new LinkedHashMap<>();

      int y;
      LinkedHashSet<Integer> qts;
      BoolExpr[] bfs = new BoolExpr[m];
      for (FuncSymb f : idx.sigma) {
         if (f.arity > 0) {
            for (int i = 0; i < m; i++) {
               BoolExpr xi = (BoolExpr) ctx.mkConst("x" + i, bool_type);
               //System.out.println(qIdx.get(i));
               if (idx.rhsIdx.get(qIdx.get(i)).containsKey(f)) {
                  qts = idx.rhsIdx.get(qIdx.get(i)).get(f);
                  BoolExpr[] bs = new BoolExpr[qts.size()];
                  y = 0;
                  int w;
                  for (Integer z : qts) {
                     BoolExpr[] cs = new BoolExpr[f.arity];
                     for (int j = 0; j < f.arity; j++) {
                        w = z + m + j * k;
                        Expr tz = ctx.mkConst("x" + w, bool_type);
                        cs[j] = (BoolExpr) tz;
                     }
                     bs[y] = (BoolExpr) ctx.mkAnd(cs);
                     y++;
                  }
                  bfs[i] = ctx.mkIff(xi, ctx.mkOr(bs));
               } else {
                  bfs[i] = ctx.mkIff(xi,ctx.mkFalse());
               }
            }
            result.put(f, ctx.mkAnd(bfs));
         }
      }
      return result;
   }

   private LinkedHashMap<FuncSymb, BoolExpr> makeBoolConstraint() {
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
      return ctx.mkAnd(b);
   }

   private LinkedHashSet<LinkedHashSet<String>> pruneStates(FuncSymb f, LinkedHashSet<LinkedHashSet<String>> qdnew, int j, LinkedHashMap<FuncSymb, BoolExpr> boolConstraints, ArrayList<BoolExpr> solutions) {
      LinkedHashSet<LinkedHashSet<String>> result = new LinkedHashSet<>();
      int m = idx.qs.size();
      for (LinkedHashSet<String> qs : qdnew) {
         solver.reset();
         solver.add(boolConstraints.get(f));
         solver.add(ctx.mkNot(solutions.get(0)));
         solver.add(nonEmptyConstraint(m));
         for (int i = 0; i < f.arity; i++) {
            if (j == i) {
               solver.add(makeSoln(qs, m, m * (j + 1)));
            } else {
               solver.add(solutions.get(i + 1));
            }
         }
         //if (verbose) System.out.println(solver.toString());
         if (solver.check() == Status.SATISFIABLE) {
            result.add(qs);
         } else {
//            if (verbose) {
//               System.out.println("Eliminated state " + qs + " from position " + j);
//            }
         }
      }
      return result;
   }

   private LinkedHashSet<LinkedHashSet<String>> pruneStates1(FuncSymb f, LinkedHashSet<LinkedHashSet<String>> qdnew, int j, LinkedHashMap<FuncSymb, BoolExpr> boolConstraints, ArrayList<BoolExpr> solutions) {
      int m = idx.qs.size();
      solver.reset();
      solver.add(boolConstraints.get(f));
      solver.add(ctx.mkNot(solutions.get(0)));
      solver.add(nonEmptyConstraint(m));
      for (int i = 0; i < f.arity; i++) {
         if (j == i) {
            BoolExpr[] bs = new BoolExpr[qdnew.size()];
            int y = 0;
            for (LinkedHashSet<String> qs : qdnew) {
               bs[y] = makeSoln(qs, m, m * (j + 1));
               y++;
            }
            solver.add(ctx.mkOr(bs));
         } else {
            solver.add(solutions.get(i + 1));
         }
      }
      //if (verbose) System.out.println(solver.toString());
      if (solver.check() == Status.SATISFIABLE) {
         return qdnew;
      } else {
         return new LinkedHashSet<>();
      }
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

   private ArrayList<ArrayList<BitSet>> pruneTrans(int j, FuncSymb f, ArrayList<ArrayList<BitSet>> psi_phi_tuple, LinkedHashMap<FuncSymb, BoolExpr> transConstraints, ArrayList<BoolExpr> solutions) {
      ArrayList<BitSet> resultj = new ArrayList<>();
      int m = idx.qs.size();
      int k = idx.delta.size();
      //System.out.println("Pruning :" + psi_phi_tuple);
      for (int i = 0; i < psi_phi_tuple.get(j).size(); i++) {
         solver.reset();
         solver.add(transConstraints.get(f));
         solver.add(ctx.mkNot(solutions.get(0)));
         solver.add(nonEmptyConstraint(m));

         int y = 0;
         for (ArrayList<BitSet> bj : psi_phi_tuple) {
            if (j != y) {
               solver.add(makeTransSolnSet(bj, m + y * k));
            }
            y++;
         }

         solver.add(makeTransSoln(psi_phi_tuple.get(j).get(i), m + j * k));
         //System.out.println(solver.toString());
         if (solver.check() == Status.SATISFIABLE) {
            resultj.add(psi_phi_tuple.get(j).get(i));
         } else {
            if (verbose) {
               //System.out.println("Eliminated set " + psi_phi_tuple.get(j).get(i) + " from position " + j);
               System.out.print("E");
            }
         }
      }
      psi_phi_tuple.set(j, resultj);
      return psi_phi_tuple;
   }

   private BoolExpr makeTransSoln(BitSet bset, int m) {
      BoolExpr[] bs = new BoolExpr[idx.delta.size()];
      int y;
      Sort bool_type = ctx.getBoolSort();
      for (int i = 0; i < idx.delta.size(); i++) {
         y = i + m;
         BoolExpr xi = (BoolExpr) ctx.mkConst("x" + y, bool_type);
         if (bset.get(i) == true) {
            bs[i] = xi;
         } else {
            bs[i] = ctx.mkNot(xi);
         }
      }
      return ctx.mkAnd(bs);
   }

   private BoolExpr makeTransSolnSet(ArrayList<BitSet> bset, int m) {
      BoolExpr[] bs = new BoolExpr[bset.size()];
      for (int i = 0; i < bset.size(); i++) {
         bs[i] = makeTransSoln(bset.get(i), m);
      }
      return ctx.mkOr(bs);
   }
}
