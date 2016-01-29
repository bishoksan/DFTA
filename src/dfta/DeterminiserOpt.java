package dfta;

import dfta.parser.*;
import dfta.parser.syntaxtree.*;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedHashSet;
import java.util.LinkedHashMap;
import java.util.ArrayList;
import java.io.PrintStream;
import java.lang.Math.*;
import javax.swing.JTextArea;

public class DeterminiserOpt implements Determiniser {

    Indices idx;
    String ftaId;

    LinkedHashSet<LinkedHashSet<String>> qd = new LinkedHashSet<LinkedHashSet<String>>();
    ArrayList<PTransition> deltad = new ArrayList<PTransition>();

    LinkedHashMap<FuncSymb, ArrayList<LinkedHashMap<LinkedHashSet<FTATransition>, LinkedHashSet<LinkedHashSet<String>>>>> t_inverse_table
            = new LinkedHashMap<FuncSymb, ArrayList<LinkedHashMap<LinkedHashSet<FTATransition>, LinkedHashSet<LinkedHashSet<String>>>>>();
    LinkedHashMap<FuncSymb, ArrayList<LinkedHashSet<LinkedHashSet<FTATransition>>>> psi
            = new LinkedHashMap<FuncSymb, ArrayList<LinkedHashSet<LinkedHashSet<FTATransition>>>>();
    LinkedHashMap<FuncSymb, ArrayList<LinkedHashSet<FTATransition>>> psi_glb
            = new LinkedHashMap<FuncSymb, ArrayList<LinkedHashSet<FTATransition>>>();

    boolean dontCare = true;
    boolean any = false;
    boolean includesCheck = false;

    LinkedHashSet<String> q1;
    LinkedHashSet<String> q2;

    public DeterminiserOpt(String ftaId, LinkedHashSet transitions, LinkedHashSet finalStates, boolean any, boolean dontCare) {
        this.ftaId = ftaId;
        idx = new Indices(transitions, finalStates);
        this.any = any;
        this.dontCare = dontCare;
        includesCheck = false;
    }

    public void makeDfta() {
        idx.genDelta(ftaId);
        idx.genFinalStates(ftaId);
        if (any) {
            idx.genDeltaAny();
        }
        idx.buildIndices();
        //idx.showIndices();
        dftaStates();
        System.out.println("Made states");
        dftaTransitions();
    }

    public boolean dftaStates() {
        System.out.println("Building DFTA states...");
        Iterator iter;
        int temp;
        LinkedHashSet<String> q0 = new LinkedHashSet<String>();
        FuncSymb f;
        ArrayList<LinkedHashSet<LinkedHashSet<FTATransition>>> phi_f, psi_f;
        LinkedHashSet<LinkedHashSet<FTATransition>> phi_f_j = new LinkedHashSet<LinkedHashSet<FTATransition>>();
        ArrayList<ArrayList<LinkedHashSet<FTATransition>>> psi_phi_tuple;
        ArrayList<LinkedHashSet<FTATransition>> deltatuple;
        ArrayList<LinkedHashSet<FTATransition>> newtrs = new ArrayList<LinkedHashSet<FTATransition>>();

        LinkedHashMap<FuncSymb, ArrayList<LinkedHashSet<LinkedHashSet<FTATransition>>>> phi
                = new LinkedHashMap<FuncSymb, ArrayList<LinkedHashSet<LinkedHashSet<FTATransition>>>>();

        LinkedHashSet<LinkedHashSet<String>> qdnew, qdold, qdnew1;

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
                psi_glb.put(f, new ArrayList<LinkedHashSet<FTATransition>>());
                psi_f = new ArrayList<LinkedHashSet<LinkedHashSet<FTATransition>>>(f.arity);
                phi_f = new ArrayList<LinkedHashSet<LinkedHashSet<FTATransition>>>(f.arity);
                t_inverse_table.put(f, new ArrayList<LinkedHashMap<LinkedHashSet<FTATransition>, LinkedHashSet<LinkedHashSet<String>>>>());
                for (int j = 0; j < f.arity; j++) {
                    psi_f.add(j, new LinkedHashSet<LinkedHashSet<FTATransition>>());
                    phi_f.add(j, new LinkedHashSet<LinkedHashSet<FTATransition>>());
                    t_inverse_table.get(f).add(j, new LinkedHashMap<LinkedHashSet<FTATransition>, LinkedHashSet<LinkedHashSet<String>>>());
                    psi_glb.get(f).add(j, new LinkedHashSet<FTATransition>());
                }
                psi.put(f, psi_f);
                phi.put(f, phi_f);
            }
        }

        qdnew = (LinkedHashSet<LinkedHashSet<String>>) qd.clone();
        deltatuple = new ArrayList<LinkedHashSet<FTATransition>>();
        psi_phi_tuple = new ArrayList<ArrayList<LinkedHashSet<FTATransition>>>();

        qdnew1 = new LinkedHashSet<LinkedHashSet<String>>();

        // Compute DFTA States - main loop
        do {
            qdnew1.clear();
            iter = idx.sigma.iterator();
            while (iter.hasNext()) {
                f = (FuncSymb) iter.next();
                psi_f = psi.get(f);
                phi_f = phi.get(f);

                if (f.arity > 0) {  // initialise the Phi and Psi tuples
                    newtrs.clear();
                    Iterator l;
                    for (int j = 0; j < f.arity; j++) {
                        phi_f_j = t(j, f, qdnew);
                        phi_f_j.removeAll(psi_f.get(j));  // remove sets already computed for jth argument
                        //prune(phi_f_j);
                        phi_f.set(j, phi_f_j);

                        //psi_f.get(j).addAll(phi_f_j);
                        l = phi_f_j.iterator();
					//newtrs.add(j,new LinkedHashSet<FTATransition>());
                        //while(l.hasNext()) {
                        //	if (psi_glb.get(f).get(j).isEmpty())
                        //		psi_glb.get(f).set(j,new LinkedHashSet<FTATransition>((LinkedHashSet<FTATransition>) l.next()));
                        //	else	
                        //		psi_glb.get(f).get(j).retainAll((LinkedHashSet<FTATransition>) l.next());
                        //	newtrs.get(j).addAll((LinkedHashSet<FTATransition>) l.next());
                        //}
                        //System.out.println(f+", "+j+": "+psi_glb.get(f).get(j));
                    }
                    for (int j = 0; j < f.arity; j++) {
                        if (phi_f.get(j).size() > 0) { // if size of phi_f[j] = 0 then prod will be 0
                            psi_phi_tuple.clear();
                            for (int k = 0; k < f.arity; k++) {
                                if (k < j) {
                                    psi_phi_tuple.add(k, new ArrayList<LinkedHashSet<FTATransition>>(psi_f.get(k)));
                                } else if (k == j) {
                                    psi_phi_tuple.add(k, new ArrayList<LinkedHashSet<FTATransition>>(phi_f.get(j)));
                                } //else psi_phi_tuple.add(k,pruneSets(psi_f.get(k),newtrs.get(j)));
                                else {
                                    psi_phi_tuple.add(k, new ArrayList<LinkedHashSet<FTATransition>>(phi_f.get(k)));
                                    psi_phi_tuple.get(k).addAll(psi_f.get(k));
                                }
                            }

                            int prod = 1;
                            for (int k = 0; k < f.arity; k++) {
                                prod = prod * psi_phi_tuple.get(k).size();
                            }
						//System.out.print("Cartesian product size: " + prod + " ");
						/*
                             LinkedHashSet<LinkedHashSet<FTATransition>> intersects = intersectCartProd(psi_phi_tuple,0);
                             Iterator i = intersects.iterator();
                             while (i.hasNext()) {
                             q0 = rhsSet((LinkedHashSet<FTATransition>) i.next());
                             if (qd.add(q0)) {
                             qdnew1.add(q0);
                             if (includesCheck) if (!inclusionCheckState(q0,q1,q2)) return false;
                             }
                             }
                             */
                            for (int k = 0; k < prod; k++) { // enumerate the delta-tuples (cartesian product)
                                temp = k;
                                // Re-initialise delta-tuple
                                deltatuple.clear();
                                for (int m = 0; m < f.arity; m++) {
                                    deltatuple.add(m, psi_phi_tuple.get(m).get(temp % psi_phi_tuple.get(m).size()));
                                    temp = temp / psi_phi_tuple.get(m).size();
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
            System.out.println("Qdnew: " + qdnew.size());
        } while (!qdnew.isEmpty());
        return true;
    }

    void dftaTransitions() {
        System.out.println("Building DFTA product transitions...");
        Iterator i = idx.sigma.iterator();
        FuncSymb f;
        LinkedHashSet<String> q0;
        ArrayList<ArrayList<LinkedHashSet<FTATransition>>> psi_tuple;
        ArrayList<LinkedHashSet<FTATransition>> deltatuple;
        ArrayList<LinkedHashSet<LinkedHashSet<String>>> lhs;
        int temp;

        while (i.hasNext()) {
            f = (FuncSymb) i.next();
            if (f.arity == 0) {
                q0 = rhsSet(idx.fIndex.get(f));
                if (!q0.isEmpty()) {
                    deltad.add(new PTransition(f, q0));
                }
            } else {
                //psi_reinit(f);
                psi_tuple = new ArrayList<ArrayList<LinkedHashSet<FTATransition>>>();
                // Initialise delta-tuple and psi-tuple
                deltatuple = new ArrayList<LinkedHashSet<FTATransition>>();
                for (int j = 0; j < f.arity; j++) {
                    psi_tuple.add(j, new ArrayList<LinkedHashSet<FTATransition>>(psi.get(f).get(j)));
                    deltatuple.add(j, new LinkedHashSet<FTATransition>());
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
                System.out.println("Computing transitions for " + f);
                //System.out.println("Product size "+f.toString()+" = "+prod);
                for (int j = 0; j < prod; j++) { // enumerate the delta-tuples
                    temp = j;
                    for (int k = 0; k < f.arity; k++) {
                        deltatuple.set(k, psi_tuple.get(k).get(temp % psi_tuple.get(k).size()));
                        temp = temp / psi_tuple.get(k).size();
                    }

                    q0 = rhsSet(intersect(deltatuple));

                    if (!q0.isEmpty()) {
                        lhs = new ArrayList<LinkedHashSet<LinkedHashSet<String>>>();
                        for (int m = 0; m < f.arity; m++) {
                            lhs.add(m, t_inverse_table.get(f).get(m).get(deltatuple.get(m)));
                        }
                        deltad.add(new PTransition(f, q0, lhs));
                    }
                }
            }
        }
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
        int smallest = 0;
        int smallestSize = d.get(0).size();
        for (int i = 1; i < d.size(); i++) {
            if (d.get(i).size() < smallestSize) {
                smallest = i;
                smallestSize = d.get(i).size();
            }
        }
        LinkedHashSet<FTATransition> result = (LinkedHashSet<FTATransition>) d.get(smallest).clone();
        for (int i = 0; i < d.size(); i++) {
            if (i != smallest) {
                result.retainAll(d.get(i));
            }
        }

        return result;
    }

    LinkedHashSet<LinkedHashSet<FTATransition>> t(int i, FuncSymb f, LinkedHashSet<LinkedHashSet<String>> qss) {
        Iterator k = qss.iterator();
        LinkedHashSet<LinkedHashSet<FTATransition>> result = new LinkedHashSet<LinkedHashSet<FTATransition>>();
        LinkedHashSet<String> qs;
        LinkedHashSet<FTATransition> h;
        while (k.hasNext()) {
            qs = (LinkedHashSet<String>) k.next();
            h = lhsSet(i, f, qs);
            if (!h.isEmpty()) {
                result.add(h);
            }
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
        // Tabulate result for the t_inverse function
        if (!result.isEmpty()) {
            LinkedHashMap<LinkedHashSet<FTATransition>, LinkedHashSet<LinkedHashSet<String>>> hm = t_inverse_table.get(f).get(i);
            if (!hm.containsKey(result)) {
                hm.put(result, new LinkedHashSet<LinkedHashSet<String>>());
            }
            hm.get(result).add(qs);
        }
        return result;
    }

    void dontCareArgs(ArrayList<ArrayList<LinkedHashSet<FTATransition>>> psi_tuple, FuncSymb f) {
        LinkedHashSet<LinkedHashSet<String>> qs;
        ArrayList<LinkedHashSet<FTATransition>> psiIntersectTuple = new ArrayList<LinkedHashSet<FTATransition>>();
        LinkedHashSet<FTATransition> ts;
        ArrayList<LinkedHashSet<LinkedHashSet<String>>> lhs = new ArrayList<LinkedHashSet<LinkedHashSet<String>>>();
        LinkedHashSet<String> rhs;
        LinkedHashSet<FTATransition> temp;
        LinkedHashSet<FTATransition> deltaj;
        ArrayList<LinkedHashSet<LinkedHashSet<FTATransition>>> dontCares = new ArrayList<LinkedHashSet<LinkedHashSet<FTATransition>>>();

        // Intersect elements of psi-tuple and initialise don't-care array
        for (int i = 0; i < f.arity; i++) {
            if (!psi_tuple.get(i).isEmpty()) {
                psiIntersectTuple.add(i, intersect(psi_tuple.get(i)));
            } else {
                psiIntersectTuple.add(i, new LinkedHashSet<FTATransition>());
            }
            dontCares.add(i, new LinkedHashSet<LinkedHashSet<FTATransition>>());
        }

        for (int i = 0; i < f.arity; i++) {
            temp = psiIntersectTuple.get(i);
            for (int j = 0; j < psi_tuple.get(i).size(); j++) {
                deltaj = psi_tuple.get(i).get(j);
                psiIntersectTuple.set(i, deltaj);
                rhs = rhsSet(deltaj);
                if (rhs.equals(rhsSet(intersect(psiIntersectTuple)))) {
                    // generate a don't care transition
                    lhs = new ArrayList<LinkedHashSet<LinkedHashSet<String>>>();
                    for (int k = 0; k < f.arity; k++) {
                        lhs.add(k, new LinkedHashSet<LinkedHashSet<String>>());
                        if (k == i) {
                            lhs.set(k, t_inverse_table.get(f).get(i).get(deltaj));
                        }
                    }
                    deltad.add(new PTransition(f, rhs, lhs));
                    dontCares.get(i).add(deltaj);
                } else if (f.arity == 2 && isSingleton(rhs) && intersectsAll(deltaj, i, f, psi_tuple)) {
                    lhs = new ArrayList<LinkedHashSet<LinkedHashSet<String>>>();
                    for (int k = 0; k < f.arity; k++) {
                        lhs.add(k, new LinkedHashSet<LinkedHashSet<String>>());
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

    boolean intersectsAll(LinkedHashSet<FTATransition> deltaj, int j, FuncSymb f, ArrayList<ArrayList<LinkedHashSet<FTATransition>>> psi_tuple) {
        // check whether deltaj intersects with all members of all non-j elements of psi_tuple
        LinkedHashSet<FTATransition> ts;
        for (int k = 0; k < f.arity; k++) {
            if (k != j) {
                if (psi_tuple.get(k).isEmpty()) {
                    return false;
                }
                for (int l = 0; l < psi_tuple.get(k).size(); l++) {
                    ts = (LinkedHashSet<FTATransition>) deltaj.clone();
                    ts.retainAll(psi_tuple.get(k).get(l));
                    if (ts.isEmpty()) {
                        return false;
                    }
                }
            }
        }
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

    public void printDfta(PrintStream output) {
        for (int i = 0; i < deltad.size(); i++) {
            output.println(deltad.get(i).toString() + ".");
        }
    }

    public long deltaDCount() {
        double count = 0;
        double tcount;
        double argsize;
        double qdsize = qd.size();
        ArrayList<LinkedHashSet<LinkedHashSet<String>>> lhs;
        for (int i = 0; i < deltad.size(); i++) {
            lhs = deltad.get(i).lhs;
            tcount = 1.0;
            for (int j = 0; j < lhs.size(); j++) {
                argsize = lhs.get(j).size();
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

    public void showStats(JTextArea ja) {
        ja.append("Number of input FTA states = " + idx.qs.size() + "\n");
        ja.append("Number of input FTA transitions = " + idx.delta.size() + "\n");
        ja.append("Number of DFTA states = " + qd.size() + "\n");
        if (any) {
            ja.append("Number of DFTA transitions = " + deltaDCountComplete() + "\n");
        } else {
            ja.append("Number of DFTA transitions = " + deltaDCount() + "\n");
        }
        ja.append("Number of DFTA product transitions = " + deltad.size() + "\n");
        System.out.println("=============================================");
    }

    public LinkedHashSet<LinkedHashSet<String>> getQd() {
        return qd;
    }

    public ArrayList<PTransition> getDeltad() {
        return deltad;
    }

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

    ArrayList<LinkedHashSet<FTATransition>> pruneSets(LinkedHashSet<LinkedHashSet<FTATransition>> psi_f_k, LinkedHashSet<FTATransition> newtrs) {
        ArrayList<LinkedHashSet<FTATransition>> result = new ArrayList<LinkedHashSet<FTATransition>>();
        LinkedHashSet<FTATransition> set1, set2;
        Iterator i = psi_f_k.iterator();
        int y = newtrs.size();
        System.out.print("Before " + psi_f_k.size() + " --- ");
        while (i.hasNext()) {
            set1 = (LinkedHashSet<FTATransition>) i.next();
            set2 = new LinkedHashSet<FTATransition>(newtrs);
            set2.retainAll(set1);
            //System.out.print(set1.size()+"."+set2.size()+": ");
            if (!set2.isEmpty()) {
                result.add(set2);
            }
        }
        System.out.println("After " + result.size());
        return result;
    }

    void prune(LinkedHashSet<LinkedHashSet<FTATransition>> psi_f_k) {
        Iterator i = psi_f_k.iterator();
        LinkedHashSet<FTATransition> set1;
        LinkedHashSet<String> r;
        while (i.hasNext()) {
            set1 = (LinkedHashSet<FTATransition>) i.next();
            r = rhsSet(set1);
            if (r.size() == 1) {
                if (qd.contains(r)) {
                    i.remove();
                }
            }
        }
    }

    void psi_reinit(FuncSymb f) {
        psi.get(f).clear();
        //System.out.println("re-initialize psi values for "+f);
        for (int j = 0; j < f.arity; j++) {
            psi.get(f).add(j, t(j, f, qd));
        }
	//System.out.println("finished re-initializing psi values for "+f);
    }

    LinkedHashSet<LinkedHashSet<FTATransition>> intersectCartProd(ArrayList<ArrayList<LinkedHashSet<FTATransition>>> psi_phi_tuple, int k) {
        LinkedHashSet<LinkedHashSet<FTATransition>> result = new LinkedHashSet<LinkedHashSet<FTATransition>>();
        LinkedHashSet<FTATransition> t;
        if (k == psi_phi_tuple.size() - 1) {
            for (int i = 0; i < psi_phi_tuple.get(k).size(); i++) {
                result.add((LinkedHashSet<FTATransition>) (psi_phi_tuple.get(k).get(i)).clone());
            }
            return result;
        } else {
            LinkedHashSet<LinkedHashSet<FTATransition>> r = intersectCartProd(psi_phi_tuple, k + 1);
            Iterator i = r.iterator();
            while (i.hasNext()) {
                t = (LinkedHashSet<FTATransition>) i.next();
                for (int j = 0; j < psi_phi_tuple.get(k).size(); j++) {
                    LinkedHashSet<FTATransition> u = (LinkedHashSet<FTATransition>) t.clone();
                    u.retainAll(psi_phi_tuple.get(k).get(j));
                    if (!u.isEmpty()) {
                        result.add(u);
                    }
                }
            }
        }
        return result;
    }
}
