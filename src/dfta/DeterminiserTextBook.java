package dfta;

import dfta.parser.*;
import dfta.parser.syntaxtree.*;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedHashSet;
import java.util.LinkedHashMap;
import java.util.ArrayList;
import java.io.PrintStream;
import javax.swing.JTextArea;

public class DeterminiserTextBook implements Determiniser {

    Indices idx;

    LinkedHashSet<LinkedHashSet<String>> qd = new LinkedHashSet<LinkedHashSet<String>>();
    ArrayList<DTransition> deltad = new ArrayList<DTransition>();

    public DeterminiserTextBook(LinkedHashSet transitions, LinkedHashSet finalStates, boolean any) {
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
        LinkedHashSet<String> q0 = new LinkedHashSet<String>();
        FuncSymb f;
        ArrayList<LinkedHashSet<String>> qtuple;
        ArrayList<LinkedHashSet<FTATransition>> deltatuple;

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
                //System.out.println(f.toString());
                if (f.arity == 0) {
                    q0 = rhsSet(idx.fIndex.get(f));
                    if (!q0.isEmpty()) {
                        qd.add(q0);
                        newTransition |= addTransition(f, q0, new ArrayList<LinkedHashSet<String>>());
                    }
                } else {
                    qdoldarray = new ArrayList<ArrayList<LinkedHashSet<String>>>();
                    for (int i = 0; i < f.arity; i++) {
                        qdoldarray.add(i, new ArrayList<LinkedHashSet<String>>(qdold));
                    }
                    int prod = 1;
                    for (int k = 0; k < f.arity; k++) {
                        prod = prod * qdold.size();
                    }
                    for (int k = 0; k < prod; k++) { // enumerate the delta-tuples
                        temp = k;
                        // Initialise new q-tuple and delta-tuple
                        qtuple = new ArrayList<LinkedHashSet<String>>();
                        deltatuple = new ArrayList<LinkedHashSet<FTATransition>>();

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

    LinkedHashSet<String> rhsSet(LinkedHashSet<FTATransition> tSet) {
        Iterator i = tSet.iterator();
        FTATransition t;
        LinkedHashSet<String> result = new LinkedHashSet<String>();
        while (i.hasNext()) {
            t = (FTATransition) i.next();
            result.add(t.q0);
        }
        return result;
    }

    LinkedHashSet<FTATransition> intersect(ArrayList<LinkedHashSet<FTATransition>> d) {
        LinkedHashSet<FTATransition> result = (LinkedHashSet<FTATransition>) d.get(0).clone();
        for (int i = 1; i < d.size(); i++) {
            result.retainAll(d.get(i));
        }
        return result;
    }

    LinkedHashSet<FTATransition> lhsSet(int i, FuncSymb f, LinkedHashSet<String> qs) {
        Iterator k = qs.iterator();
        LinkedHashSet<FTATransition> result = new LinkedHashSet<FTATransition>();
        LinkedHashMap<String, LinkedHashSet<FTATransition>> lhsmap = idx.lhsf.get(f).get(i);
        String q;
        while (k.hasNext()) {
            q = (String) k.next();
            if (lhsmap.containsKey(q)) {
                result.addAll(lhsmap.get(q));
            }
        }
        return result;
    }

    boolean addTransition(FuncSymb f, LinkedHashSet<String> q0, ArrayList<LinkedHashSet<String>> lhs) {
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
        LinkedHashSet<String> q;
        boolean includes = true;
        iter = qd.iterator();
        while (iter.hasNext() && includes) {
            q = (LinkedHashSet<String>) iter.next();
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

    public LinkedHashSet<LinkedHashSet<String>> getQd() {
        return qd;
    }

    public ArrayList<DTransition> getDeltad() {
        return deltad;
    }

    public Indices getIdx() {
        return idx;
    }

}
