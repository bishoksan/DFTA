package dfta;

public class FuncSymb {

   String fname;
   int arity;

   public FuncSymb(String fname, int arity) {
      this.fname = fname;
      this.arity = arity;
   }
   
   public FuncSymb(Atom a) {
      this.fname = a.pred;
      this.arity = a.ys.length;
   }

   @Override
   public int hashCode() {
      return arity * 31 + fname.hashCode();
   }

   @Override
   public boolean equals(Object g) {
      if (g == null) {
         return false;
      }
      if (getClass() != g.getClass()) {
         return false;
      }
      FuncSymb g1 = (FuncSymb) g;
      return (fname.equals(g1.fname) && arity == g1.arity);
   }

   public String toString() {
      return fname + "_" + arity;
   }

   public String datalogName() {
      if (fname.equals("[]")) {
         return "nil";
      } else {
         try {
            int n = Integer.parseInt(fname);
            return "num_" + fname;
         } catch (NumberFormatException e) {
            return fname + "_" + arity;
         }
      }
   }
}
