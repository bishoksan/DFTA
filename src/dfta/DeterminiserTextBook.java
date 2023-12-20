package dfta;

import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedHashMap;
import java.util.ArrayList;
import java.util.BitSet;
import java.io.PrintStream;
import javax.swing.JTextArea;

public class DeterminiserTextBook implements Determiniser {

   Indices idx;
   boolean verbose;

   LinkedHashSet<LinkedHashSet<String>> qd = new LinkedHashSet<>();
   final LinkedHashSet<DTransition> deltad = new LinkedHashSet<>();

   public DeterminiserTextBook(LinkedHashSet transitions, LinkedHashSet finalStates, boolean any, boolean verbose) {
      idx = new Indices(transitions, finalStates);
      idx.genDelta("");
      idx.genFinalStates("");
      if (any) {
         idx.genDeltaAny();
      }
      idx.buildIndices();
      this.verbose = verbose;
   }

   @Override
   public void makeDfta() {
      dftaStates();
   }

   void dftaStates() {
      if (verbose) {
         System.out.println("Building DFTA ...");
      }
      Iterator iter;
      int temp;
      LinkedHashSet<String> q0;
      FuncSymb f;
      ArrayList<LinkedHashSet<String>> qtuple;
      ArrayList<BitSet> deltatuple;

      LinkedHashSet<LinkedHashSet<String>> qdold;
      ArrayList<ArrayList<LinkedHashSet<String>>> qdoldarray;
      boolean newTransition;

      // Compute DFTA States - main loop
      do {
         newTransition = false;
         qdold = (LinkedHashSet<LinkedHashSet<String>>) qd.clone();

         iter = idx.sigma.iterator();
         while (iter.hasNext()) {
            f = (FuncSymb) iter.next();
            if (f.arity == 0) {
               q0 = rhsSet(idx.fIndex.get(f));
               if (!q0.isEmpty()) {
                  qd.add(q0);
                  newTransition |= addTransition(f, q0, new ArrayList<>());
               }
            } else {
               qdoldarray = new ArrayList<>();
               for (int i = 0; i < f.arity; i++) {
                  qdoldarray.add(i, new ArrayList<>(qdold));
               }
               int prod = 1;
               for (int k = 0; k < f.arity; k++) {
                  prod = prod * qdold.size();
               }
               for (int k = 0; k < prod; k++) { // enumerate the delta-tuples
                  temp = k;
                  // Initialise new q-tuple and delta-tuple
                  qtuple = new ArrayList<>();
                  deltatuple = new ArrayList<>();

                  for (int m = 0; m < f.arity; m++) {
                     qtuple.add(m, qdoldarray.get(m).get(temp % qdoldarray.get(m).size()));
                     deltatuple.add(m, lhsSet(m, f, qtuple.get(m)));
                     temp = temp / qdoldarray.get(m).size();
                  }
                  q0 = rhsSet(intersect(deltatuple));
                  if (!q0.isEmpty()) {
                     qd.add(q0);
                     newTransition |= addTransition(f, q0, qtuple);
                  }
               }
            }
         }
      } while (newTransition);
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

   BitSet lhsSet(int i, FuncSymb f, LinkedHashSet<String> qs) {
      Iterator k = qs.iterator();
      BitSet result = new BitSet();
      LinkedHashMap<String, BitSet> lhsmap = idx.lhsf.get(f).get(i);
      String q;
      while (k.hasNext()) {
         q = (String) k.next();
         if (lhsmap.containsKey(q)) {
            result.or(lhsmap.get(q));
         }
      }
      return result;
   }
   
   boolean addTransition(FuncSymb f, LinkedHashSet<String> q0, ArrayList<LinkedHashSet<String>> lhs) {
        return deltad.add(new DTransition(f, q0, lhs));
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

   /**
    *
    * @param output
    * @param output1
    */
   @Override
   public void printDfta(PrintStream output,PrintStream output1) {
      output.println();
      deltad.stream().forEach((deltad1) -> {
         output.println(deltad1.toString() + ".");
      });
   }

   @Override
   public void printDftaDatalog(PrintStream output) {
      DTransition t;
      FuncSymb f;
      LinkedHashSet<String> q0;
      int n;

      ArrayList<LinkedHashSet<String>> lhs;
      ArrayList<String> args;
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
      for (DTransition deltad1 : deltad) {
         t = deltad1;
         f = t.f;
         lhs = t.lhs;
         q0 = t.q0;
         args = new ArrayList<>();
         for (int m = 0; m < lhs.size(); m++) {
            args.add(m, stateNames.get(lhs.get(m)));
         }
         head = f.datalogName() + "(";
         for (String arg : args) {
            head += arg + ",";
         }
         head += stateNames.get(q0) + ")";
         output.println(head + ".");
      }
   }

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
      if (verbose) {
         System.out.println();
         System.out.print("Number of DFTA transitions = ");
      }
      System.out.println(deltad.size() + ", ");
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

   public LinkedHashSet<DTransition> getDeltad() {
      return deltad;
   }

   @Override
   public Indices getIdx() {
      return idx;
   }

}
