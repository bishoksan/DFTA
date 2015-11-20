package dfta;

public class FuncSymb {

String fname;
int arity;

public FuncSymb(String fname, int arity) {
	this.fname=fname;
	this.arity=arity;
}

public int hashCode() 
    {
       return arity*31+fname.hashCode();
    }

public boolean equals(Object g) 
    {
       if (g == null) return false;
       if (getClass() != g.getClass()) return false;
       FuncSymb g1 = (FuncSymb) g;
       return (fname.equals(g1.fname) && arity==g1.arity);
    }
    
public String toString() {
	return fname+"/"+arity;
}
}