package dfta;

import dfta.parser.*;
import dfta.parser.syntaxtree.*;
import java.util.Iterator;
import java.util.HashSet;
import java.util.HashSet;
import java.util.HashMap;
import java.util.ArrayList;
import java.io.PrintStream;
import javax.swing.JTextArea;

public class DeterminiserTextBook implements Determiniser {

    Indices idx;

    HashSet<HashSet<String>> qd = new HashSet<HashSet<String>>();
    ArrayList<DTransition> deltad = new ArrayList<DTransition>();

    public DeterminiserTextBook(HashSet transitions, HashSet finalStates, boolean any) {
        idx = new Indices(transitions, finalStates);
        idx.genDelta("");
        idx.genFinalStates("");
        if (any) {
            idx.genDeltaAny();
        }
        idx.buildIndices();
    }

    public void makeDfta() {
        dftaStates();
    }

    void dftaStates() {
        System.out.println("Building DFTA ...");
        Iterator iter;
        int temp;
        HashSet<String> q0 = new HashSet<String>();
        FuncSymb f;
        ArrayList<HashSet<String>> qtuple;
        ArrayList<HashSet<FTATransition>> deltatuple;

        HashSet<HashSet<String>> qdold;
        ArrayList<ArrayList<HashSet<String>>> qdoldarray;
        boolean newTransition;

        // Compute DFTA States - main loop
        do {
            newTransition = false;
            qdold = (HashSet<HashSet<String>>) qd.clone();

            iter = idx.sigma.iterator();
            while (iter.hasNext()) {
                f = (FuncSymb) iter.next();
                //System.out.println(f.toString());
                if (f.arity == 0) {
                    q0 = rhsSet(idx.fIndex.get(f));
                    if (!q0.isEmpty()) {
                        qd.add(q0);
                        newTransition |= addTransition(f, q0, new ArrayList<HashSet<String>>());
                    }
                } else {
                    qdoldarray = new ArrayList<ArrayList<HashSet<String>>>();
                    for (int i = 0; i < f.arity; i++) {
                        qdoldarray.add(i, new ArrayList<HashSet<String>>(qdold));
                    }
                    int prod = 1;
                    for (int k = 0; k < f.arity; k++) {
                        prod = prod * qdold.size();
                    }
                    for (int k = 0; k < prod; k++) { // enumerate the delta-tuples
                        temp = k;
                        // Initialise new q-tuple and delta-tuple
                        qtuple = new ArrayList<HashSet<String>>();
                        deltatuple = new ArrayList<HashSet<FTATransition>>();

                        for (int m = 0; m < f.arity; m++) {
                            qtuple.add(m, qdoldarray.get(m).get(temp % qdoldarray.get(m).size()));
                            deltatuple.add(m, lhsSet(m, f, qtuple.get(m)));
                            temp = temp / qdoldarray.get(m).size();
                        }
                        q0 = rhsSet(intersect(deltatuple));
                        if (!q0.isEmpty()) {
                            qd.add(q0);
                            newTransition |= addTransition(f, q0, qtuple);
                            DTransition d = new DTransition(f, q0, qtuple);
                        }
                    }
                }
            }
        } while (newTransition);
    }

    HashSet<String> rhsSet(HashSet<FTATransition> tSet) {
        Iterator i = tSet.iterator();
        FTATransition t;
        HashSet<String> result = new HashSet<String>();
        while (i.hasNext()) {
            t = (FTATransition) i.next();
            result.add(t.q0);
        }
        return result;
    }

    HashSet<FTATransition> intersect(ArrayList<HashSet<FTATransition>> d) {
        HashSet<FTATransition> result = (HashSet<FTATransition>) d.get(0).clone();
        for (int i = 1; i < d.size(); i++) {
            result.retainAll(d.get(i));
        }
        return result;
    }

    HashSet<FTATransition> lhsSet(int i, FuncSymb f, HashSet<String> qs) {
        Iterator k = qs.iterator();
        HashSet<FTATransition> result = new HashSet<FTATransition>();
        HashMap<String, HashSet<FTATransition>> lhsmap = idx.lhsf.get(f).get(i);
        String q;
        while (k.hasNext()) {
            q = (String) k.next();
            if (lhsmap.containsKey(q)) {
                result.addAll(lhsmap.get(q));
            }
        }
        return result;
    }

    boolean addTransition(FuncSymb f, HashSet<String> q0, ArrayList<HashSet<String>> lhs) {
        DTransition d1;
        for (int i = 0; i < deltad.size(); i++) {
            d1 = deltad.get(i);
            if (d1.f.equals(f)
                    && d1.lhs.equals(lhs)
                    && d1.q0.equals(q0)) {
                return false;
            }
        }
        deltad.add(new DTransition(f, q0, lhs));
        return true;
    }

// check inclusion between states in the input FTA
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

    public void printDfta(PrintStream output) {
        for (int i = 0; i < deltad.size(); i++) {
            output.println(deltad.get(i).toString() + ".");
        }
    }

    public void showStats(JTextArea ja) {

        ja.append("Number of input FTA states = " + idx.qs.size() + "\n");
        ja.append("Number of input FTA transitions = " + idx.delta.size() + "\n");
        ja.append("Number of DFTA states = " + qd.size() + "\n");
        ja.append("Number of DFTA transitions = " + deltad.size() + "\n");
    }

    public HashSet<HashSet<String>> getQd() {
        return qd;
    }

    public ArrayList<DTransition> getDeltad() {
        return deltad;
    }

    public Indices getIdx() {
        return idx;
    }

}
