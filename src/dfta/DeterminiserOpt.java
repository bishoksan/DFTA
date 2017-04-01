package dfta;

import java.util.Iterator;
import java.util.HashSet;
import java.util.HashMap;
import java.util.ArrayList;
import java.util.BitSet;
import java.io.PrintStream;
import javax.swing.JTextArea;

public class DeterminiserOpt implements Determiniser {

   Indices idx;
   String ftaId;

   HashSet<HashSet<String>> qd = new HashSet<>();
   ArrayList<PTransition> deltad = new ArrayList<>();

   HashMap<FuncSymb, ArrayList<HashMap<BitSet, HashSet<HashSet<String>>>>> t_inverse_table;
   HashMap<FuncSymb, ArrayList<HashSet<BitSet>>> psi
           = new HashMap<>();
   HashMap<FuncSymb, ArrayList<BitSet>> psi_glb;

   boolean dontCare = true;
   boolean any = false;
   boolean includesCheck = false;
   boolean verbose;

   HashSet<String> q1;  //  final states of FTA 1
   HashSet<String> q2;  //  final states of FTA 2 

   HashMap<FuncSymb, HashMap<Integer, ArrayList<ArrayList<Integer>>>> exprMap = new HashMap<>();
   HashMap<FuncSymb, HashSet<Integer>> constMap = new HashMap<>();
   HashMap<String, Integer> qIdxInv = new HashMap<>();

   public DeterminiserOpt(String ftaId, HashSet transitions, HashSet finalStates, boolean any, boolean dontCare, boolean verbose) {
      this.verbose = verbose;
      this.psi_glb = new HashMap<>();
      this.t_inverse_table = new HashMap<>();
      this.ftaId = ftaId;
      idx = new Indices(transitions, finalStates);
      this.any = any;
      this.dontCare = dontCare;
      includesCheck = false;

   }

   @Override
   public void makeDfta() {
      idx.genDelta(ftaId);
      idx.genFinalStates(ftaId);
      if (any) {
         idx.genDeltaAny();
      }
      idx.buildIndices();
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
      HashSet<String> q0;
      FuncSymb f;
      ArrayList<HashSet<BitSet>> phi_f, psi_f;
      HashSet<BitSet> phi_f_j;
      ArrayList<ArrayList<BitSet>> psi_phi_tuple;
      ArrayList<BitSet> deltatuple;
      ArrayList<BitSet> newtrs = new ArrayList<>();

      HashMap<FuncSymb, ArrayList<HashSet<BitSet>>> phi
              = new HashMap<>();

      HashSet<HashSet<String>> qdnew, qdold, qdnew1;

      iter = idx.sigma.iterator();
      while (iter.hasNext()) {
         f = (FuncSymb) iter.next();
         if (f.arity == 0) {
            q0 = rhsSet(idx.fIndex.get(f));
            if (!q0.isEmpty()) {
               qd.add(q0);
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
               psi_f.add(j, new HashSet<>());
               phi_f.add(j, new HashSet<>());
               t_inverse_table.get(f).add(j, new HashMap<>());
               psi_glb.get(f).add(j, new BitSet(idx.delta.size()));
            }
            psi.put(f, psi_f);
            phi.put(f, phi_f);
         }
      }

      qdnew = (HashSet<HashSet<String>>) qd.clone();
      deltatuple = new ArrayList<>();
      psi_phi_tuple = new ArrayList<>();

      qdnew1 = new HashSet<>();

      // Compute DFTA States - main loop
      do {
         qdnew1.clear();
         iter = idx.sigma.iterator();
         while (iter.hasNext()) {
            f = (FuncSymb) iter.next();
            //System.out.println(f);
            psi_f = psi.get(f);
            phi_f = phi.get(f);

            if (f.arity > 0) {  // initialise the Phi and Psi tuples
               Iterator l;
               for (int j = 0; j < f.arity; j++) {
                  phi_f_j = t(j, f, qdnew);
                  phi_f_j.removeAll(psi_f.get(j));  // remove sets already computed for jth argument
                  phi_f.set(j, phi_f_j);

                  l = phi_f_j.iterator();
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

                     int prod = 1;
                     for (int k = 0; k < f.arity; k++) {
                        prod = prod * psi_phi_tuple.get(k).size();
                     }
                     //System.out.println(prod);
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
                  //System.out.print(psi_f.get(j).size()+", ");
               }
               //System.out.println();
            }
         }
         qdnew.clear();
         qdnew.addAll(qdnew1);
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
      HashSet<String> q0;
      ArrayList<ArrayList<BitSet>> psi_tuple;
      ArrayList<BitSet> deltatuple;
      ArrayList<HashSet<HashSet<String>>> lhs;
      int temp, z;

      // make a hashmap yielding canonical names for the elements of qd
      HashMap<HashSet<String>, HashSet<String>> qdnames = new HashMap<>();
      Iterator qdi = qd.iterator();
      while (qdi.hasNext()) {
         q0 = (HashSet<String>) qdi.next();
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
            //psi_reinit(f);
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

   HashSet<String> rhsSet(BitSet tSet) {
      FTATransition t;
      HashSet<String> result = new HashSet<>();
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

   HashSet<BitSet> t(int i, FuncSymb f, HashSet<HashSet<String>> qss) {
      Iterator k = qss.iterator();
      HashSet<BitSet> result = new HashSet<>();
      HashSet<String> qs;
      BitSet h;
      while (k.hasNext()) {
         qs = (HashSet<String>) k.next();
         h = lhsSet(i, f, qs);
         if (!h.isEmpty()) {
            result.add(h);
         }
      }
      return result;
   }

   BitSet lhsSet(int i, FuncSymb f, HashSet<String> qs) {
      Iterator k = qs.iterator();
      BitSet result = new BitSet(idx.delta.size());
      HashMap<String, BitSet> lhsmap = idx.lhsf.get(f).get(i);
      String q;
      while (k.hasNext()) {
         q = (String) k.next();
         if (lhsmap.containsKey(q)) {
            result.or(lhsmap.get(q));
         }
      }
      // Tabulate result for the t_inverse function
      if (!result.isEmpty()) {
         HashMap<BitSet, HashSet<HashSet<String>>> hm = t_inverse_table.get(f).get(i);
         if (!hm.containsKey(result)) {
            hm.put(result, new HashSet<>());
         }
         hm.get(result).add(qs);
      }
      return result;
   }

   void dontCareArgs(ArrayList<ArrayList<BitSet>> psi_tuple, FuncSymb f) {
      HashSet<HashSet<String>> qs;
      ArrayList<BitSet> psiIntersectTuple = new ArrayList<>();
      BitSet ts;
      ArrayList<HashSet<HashSet<String>>> lhs;
      HashSet<String> rhs;
      BitSet temp;
      BitSet deltaj;
      ArrayList<HashSet<BitSet>> dontCares = new ArrayList<>();

      // Intersect elements of psi-tuple and initialise don't-care array
      for (int i = 0; i < f.arity; i++) {
         if (!psi_tuple.get(i).isEmpty()) {
            psiIntersectTuple.add(i, intersect(psi_tuple.get(i)));
         } else {
            psiIntersectTuple.add(i, new BitSet(idx.delta.size()));
         }
         dontCares.add(i, new HashSet<>());
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
                  lhs.add(k, new HashSet<>());
                  if (k == i) {
                     lhs.set(k, t_inverse_table.get(f).get(i).get(deltaj));
                  }
               }
               deltad.add(new PTransition(f, rhs, lhs));
               dontCares.get(i).add(deltaj);
            } else if (f.arity == 2 && isSingleton(rhs) && intersectsAll(deltaj, i, f, psi_tuple)) {
               lhs = new ArrayList<>();
               for (int k = 0; k < f.arity; k++) {
                  lhs.add(k, new HashSet<>());
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

   boolean isSingleton(HashSet<String> s) {
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
      HashSet<String> q;
      boolean includes = true;
      iter = qd.iterator();
      while (iter.hasNext() && includes) {
         q = (HashSet<String>) iter.next();
         includes = includes && (!q.contains(q1) || q.contains(q2));
      }
      return includes;
   }

// check inclusion between states in the input FTA
   public boolean inclusionCheck(HashSet<String> q1, HashSet<String> q2) {
      Iterator iter, qiter1, qiter2;
      String x;
      HashSet<String> q;
      boolean includes = true;
      boolean b;
      iter = qd.iterator();
      while (iter.hasNext() && includes) {
         q = (HashSet<String>) iter.next();
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
   public boolean inclusionCheckState(HashSet<String> q0, HashSet<String> q1, HashSet<String> q2) {
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
      HashSet<String> q0;
      int n;

      ArrayList<HashSet<HashSet<String>>> lhs;
      ArrayList<String> args;
      HashMap<HashSet<HashSet<String>>, String> productNames = new HashMap<>();
      HashMap<HashSet<String>, String> stateNames = new HashMap<>();
      String head, body;

      // make state names q0, q1,... from elements of qd
      // print dictionary of state names as comments
      Iterator iter = qd.iterator();
      Iterator iter1;
      HashSet<String> q;
      int j = 0;
      output.println();
      while (iter.hasNext()) {
         q = (HashSet<String>) iter.next();
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
               args.add(m, stateNames.get((HashSet<String>) iter1.next())); // singleton product state
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
      HashSet<HashSet<String>> product;
      String pName;
      while (iter.hasNext()) {
         product = (HashSet<HashSet<String>>) iter.next();
         pName = productNames.get(product);
         head = pName + "(";
         if (product.isEmpty()) {
            product = qd;
         }
         iter1 = product.iterator();
         while (iter1.hasNext()) {
            output.println(head + stateNames.get((HashSet<String>) iter1.next()) + ").");
         }
      }
   }

   public long deltaDCount() {
      double count = 0;
      double tcount;
      double argsize;
      double qdsize = qd.size();
      ArrayList<HashSet<HashSet<String>>> lhs;
      for (PTransition deltad1 : deltad) {
         lhs = deltad1.lhs;
         tcount = 1.0;
         for (HashSet<HashSet<String>> lh : lhs) {
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


   
   public HashSet<HashSet<String>> getQd() {
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
         System.out.println((HashSet<String>) i.next());
      }
   }

   void psi_reinit(FuncSymb f) {
      psi.get(f).clear();
      for (int j = 0; j < f.arity; j++) {
         psi.get(f).add(j, t(j, f, qd));
      }
   }

   HashSet<BitSet> intersectCartProd(ArrayList<ArrayList<BitSet>> psi_phi_tuple, int k) {
      HashSet<BitSet> result = new HashSet<>();
      BitSet t;
      if (k == psi_phi_tuple.size() - 1) {
         for (int i = 0; i < psi_phi_tuple.get(k).size(); i++) {
            result.add((BitSet) (psi_phi_tuple.get(k).get(i)).clone());
         }
         return result;
      } else {
         HashSet<BitSet> r = intersectCartProd(psi_phi_tuple, k + 1);
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

}
