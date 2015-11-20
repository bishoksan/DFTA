package dfta;

import dfta.parser.*;
import dfta.parser.syntaxtree.*;
import java.util.Iterator;
import java.util.HashSet;
import java.util.HashSet;
import java.util.HashMap;
import java.util.ArrayList;
import java.util.Vector;

public class Indices {

HashSet transitions;
HashSet finalStates;
HashSet<FTATransition> delta = new HashSet<FTATransition>();
HashSet<String> qs = new HashSet<String>();
HashSet<String> qfs = new HashSet<String>();

Iterator iter;
int transCount = 0;

HashSet<FuncSymb> sigma = new HashSet<FuncSymb>();
HashMap<FuncSymb, HashSet<FTATransition>> fIndex = new HashMap<FuncSymb, HashSet<FTATransition>>();
HashMap<FTATransition,String> rhs = new HashMap<FTATransition,String>();
HashMap<FuncSymb,ArrayList<HashMap<String,HashSet<FTATransition>>>> lhsf =
	new HashMap<FuncSymb,ArrayList<HashMap<String,HashSet<FTATransition>>>>();

public Indices(HashSet inputTransitions, HashSet finalStates) {
	 transitions = inputTransitions;
	 this.finalStates = finalStates;
}

void genDelta(String ftaId) {
	Transition t;
	String f;
	ArrayList<String> args;
	int arity;
	int i;
	String q;
	
	
	iter = transitions.iterator();
	while (iter.hasNext()) {
		t = (Transition)iter.next();
		transCount++;
		f = getFunc(t);
		args = getArgs(t,ftaId);
		arity = args.size();
		FuncSymb fn = new FuncSymb(f,arity);
		sigma.add(fn);
		q = getRhs(t,ftaId);
		qs.add(q);
		for (i=0; i<arity; i++) {
			qs.add(args.get(i));
		}
		FTATransition tr = new FTATransition(fn,q,args,transCount);
		//System.out.println("IInsertingg "+tr.f + tr.lhs.toString() + "->" + tr.q0);
		delta.add(tr);
		//showDelta();
		//System.out.println("***********************");
	}
}

void genFinalStates(String ftaId) {
	iter = finalStates.iterator();
	while(iter.hasNext()) {
		qfs.add(ftaId+iter.next());
	}
}

void buildIndices() {
	ArrayList<HashMap<String,HashSet<FTATransition>>> qmap;
	FTATransition t1;
	FuncSymb fn;
	String q;
	int i,arity;
	ArrayList<String> args;

	iter = delta.iterator();
	while (iter.hasNext()) {
		t1 = (FTATransition) iter.next();
		fn = t1.f;
		q = t1.q0;
		args = t1.lhs;
		arity = fn.arity;
		if (!fIndex.containsKey(fn)) {
			fIndex.put(fn,new HashSet<FTATransition>());
		}
		fIndex.get(fn).add(t1);
		rhs.put(t1,q);
		if (!lhsf.containsKey(fn)) {
			lhsf.put(fn,new ArrayList<HashMap<String,HashSet<FTATransition>>>());
			for (i=0; i<arity; i++) {
				lhsf.get(fn).add(i, new HashMap<String,HashSet<FTATransition>>());
			}
		}
		qmap = lhsf.get(fn);
		for (i=0; i<arity; i++) {
			q = args.get(i);
			if (!qmap.get(i).containsKey(q)) {
				qmap.get(i).put(q, new HashSet<FTATransition>());
			}
			qmap.get(i).get(q).add(t1);	
		}
	}
}

String getRhs(Transition t, String ftaId) {
	return (ftaId+(NodeToken) t.f1.f0.f0.choice).toString();
}

int getArity(FuncSymb f) {
	return f.arity;			
}

String getFunc(Transition t) {
	int k1;
	String f = "";
	NodeSequence ns1;
	Node n;
	int lhsKind = t.f0.f0.which;
	NodeSequence ns = (NodeSequence) t.f0.f0.choice;
	switch (lhsKind) {
		case 0: k1 = ((NodeChoice) ns.elementAt(1)).which;
		        n = ((NodeChoice) ns.elementAt(1)).choice;
		        f = ((NodeToken)((Ident)ns.elementAt(0)).f0.choice).toString();
		        switch (k1) {
		        	case 0: break;
		        	case 1: break;
		        	case 2: f = ((NodeToken)((NodeSequence)n).elementAt(0)).toString();
		        			break;
		        	case 3: f = ((NodeToken)((NodeSequence)n).elementAt(0)).toString();
		        			break;
		        	case 4: f = ((NodeToken)((NodeSequence)n).elementAt(0)).toString();
		        			break;
		        }
		        break;
		case 1: f = ((NodeToken)ns.elementAt(0)).toString();
				break;
		case 2: String f1 = ((NodeToken)ns.elementAt(0)).toString();
				n = ((NodeChoice) ns.elementAt(1)).choice;
				int k2 = ((NodeChoice) ns.elementAt(1)).which;
				String f2="";
				switch (k2) {
					case 0: f2 = ((NodeToken)n).toString();
							f = f1+f2;
							break;
					case 1: f = f1;
							break;
				}
				break;
		case 3:	k1 = ((NodeChoice) ns.elementAt(1)).which;
				switch (k1) {
		        	case 0: f = "cons";
		        			break;
		        	case 1: f = "[]";
		        			break;
		        }
		        break;
		case 4: k1 = ((NodeChoice) ns.elementAt(2)).which;
				switch (k1) {
		        	case 0: f = ((NodeToken)((NodeChoice) ns.elementAt(2)).choice).toString();
		        			break;
		        	case 1: f = ((NodeToken)((NodeChoice) ns.elementAt(2)).choice).toString();
		        			break;
		        }
		        break;
	}
	return f;			
}

ArrayList<String> getArgs(Transition t, String ftaId) {
	int k1;
	ArrayList<String> args = new ArrayList<String>();
	NodeSequence ns1;
	String arg;
	Node n;
	int lhsKind = t.f0.f0.which;
	NodeSequence ns = (NodeSequence) t.f0.f0.choice;
	switch (lhsKind) {
		case 0: k1 = ((NodeChoice) ns.elementAt(1)).which;
		        n = ((NodeChoice) ns.elementAt(1)).choice;
		        switch (k1) {
		        	case 0: Vector<Node> l = ((NodeListOptional)((NodeSequence)n).elementAt(2)).nodes;
		        			arg = ((NodeToken)((Ident)((NodeSequence)n).elementAt(1)).f0.choice).toString();
		        			args.add(0,ftaId+arg);
		        			for (int i=0; i<l.size(); i++) {
		        				arg = ((NodeToken)((Ident)((NodeSequence)l.elementAt(i)).elementAt(1)).f0.choice).toString();
		        				args.add(i+1,ftaId+arg);
		        			}
		        		 	break;
		        	case 1: break;
		        	case 2: arg = ((NodeToken)((Ident)ns.elementAt(0)).f0.choice).toString();
		        			args.add(0,ftaId+arg);
		        			arg = ((NodeToken)((Ident)((NodeSequence)n).elementAt(1)).f0.choice).toString();
		        			args.add(1,ftaId+arg);
		        			break;
		        	case 3: arg = ((NodeToken)((Ident)ns.elementAt(0)).f0.choice).toString();
		        			args.add(0,ftaId+arg);
		        			arg = ((NodeToken)((Ident)((NodeSequence)n).elementAt(1)).f0.choice).toString();
		        			args.add(1,ftaId+arg);
		        			break;
		        	case 4: arg = ((NodeToken)((Ident)ns.elementAt(0)).f0.choice).toString();
		        			args.add(0,ftaId+arg);
		        			arg = ((NodeToken)((Ident)((NodeSequence)n).elementAt(1)).f0.choice).toString();
		        			args.add(1,ftaId+arg);
		        			break;
		        }
		        break;
		case 1: break;
		case 2: n = ((NodeChoice) ns.elementAt(1)).choice;
				int k2 = ((NodeChoice) ns.elementAt(1)).which;
				switch (k2) {
					case 0: arg = ((NodeToken)n).toString();
							args.add(0,ftaId+arg);
							break;
					case 1: arg = ((NodeToken)((Ident)n).f0.choice).toString();
							args.add(0,ftaId+arg);
							break;
				}
				break;
		case 3:	k1 = ((NodeChoice) ns.elementAt(1)).which;
				n = ((NodeChoice) ns.elementAt(1)).choice;
				switch (k1) {
		        	case 0: arg=((NodeToken)((Ident)((NodeSequence)n).elementAt(0)).f0.choice).toString();
		        			args.add(0,ftaId+arg);
		        			arg=((NodeToken)((Ident)((NodeSequence)n).elementAt(2)).f0.choice).toString();
		        			args.add(1,ftaId+arg);
		        			break;
		        	case 1: break;
		        }
		        break;
		case 4: arg = ((NodeToken)((Ident)ns.elementAt(1)).f0.choice).toString();
				args.add(0,ftaId+arg);
				arg = ((NodeToken)((Ident)ns.elementAt(3)).f0.choice).toString();
				args.add(1,ftaId+arg);
				break;
	}
	return args;			
}

void genDeltaAny() {
	Iterator i = sigma.iterator();
	FuncSymb f;
	ArrayList<String> args;
	int j;
	while (i.hasNext()) {
		transCount++;
		f = (FuncSymb) i.next();
		args = new ArrayList<String>();
		for (j=0; j<f.arity; j++) {
			args.add(j,"'$any'");
		} 
		delta.add(new FTATransition(f,"'$any'",args,transCount));
	}
}


void showIndices() {
	Iterator i;
	i = sigma.iterator();
	System.out.println("Sigma");
	FuncSymb f;
	while (i.hasNext()) {
		f = (FuncSymb) i.next();
		System.out.println(f.fname+":"+f.arity);
	}
	i = fIndex.keySet().iterator();
	System.out.println("Func");
	while (i.hasNext()) {
		f = (FuncSymb) i.next();
		System.out.println(f.fname+":"+f.arity+"---"+fIndex.get(f).toString());
	}
	i = rhs.keySet().iterator();
	System.out.println("Rhs");
	FTATransition t;
	while (i.hasNext()) {
		t = (FTATransition) i.next();
		System.out.println(t+"---"+rhs.get(t).toString());
	}
	i = lhsf.keySet().iterator();
	System.out.println("Lhsf");
	while (i.hasNext()) {
		f = (FuncSymb) i.next();
		System.out.println(f.fname+":"+f.arity);
		for (int j=0; j<f.arity; j++) {
			System.out.println("  "+j);
			Iterator i1 = lhsf.get(f).get(j).keySet().iterator();
			String q;
			HashMap<String,HashSet<FTATransition>> fq = lhsf.get(f).get(j);
			while (i1.hasNext()) {
				q = (String) i1.next();
				System.out.println("    "+q+"---"+fq.get(q).toString());
			}
		}
	}
 }
 
void showQ() {
	Iterator i;
	i = qs.iterator();
	while (i.hasNext()) {
		System.out.println((String) i.next());
	}
 }
 
void showQF() {
	Iterator i;
	i = qfs.iterator();
	while (i.hasNext()) {
		System.out.println((String) i.next());
	}
 }
 
void showDelta() {
	Iterator i;
	FTATransition t;
	i = delta.iterator();
	while (i.hasNext()) {
		t = (FTATransition) i.next();
		System.out.println(t.f + t.lhs.toString() + "->" + t.q0);
	}
 }
}