package dfta;

import java.util.LinkedHashSet;
import java.util.ArrayList;

public class DTransition {

   FuncSymb f;
   LinkedHashSet<String> q0;
   ArrayList<LinkedHashSet<String>> lhs;

   public DTransition(FuncSymb f, LinkedHashSet<String> q0, ArrayList<LinkedHashSet<String>> lhs) {
      this.f = f;
      this.q0 = q0;
      this.lhs = lhs;
   }

   public DTransition(FuncSymb f, LinkedHashSet<String> q0) {
      this.f = f;
      this.q0 = q0;
      this.lhs = new ArrayList<>();
   }

   @Override
   public String toString() {
      String result;

      // To do - separate cases for lists and infix operators
      result = f.fname;
      if (f.arity > 0) {
         if (lhs.get(0).isEmpty()) {
            result += "(_";
         } else {
            result += "(" + lhs.get(0).toString();
         }
         for (int i = 1; i < f.arity; i++) {
            if (lhs.get(i).isEmpty()) {
               result += ",_";
            } else {
               result += "," + lhs.get(i).toString();
            }
         }
         result += ")";
      }
      result += " -> " + q0.toString();
      return result;
   }

   @Override
   public int hashCode() {
      return f.hashCode() * 31 + lhs.hashCode() * 17 + q0.hashCode();
   }

   @Override
   public boolean equals(Object g) {
      if (g == null) {
         return false;
      }
      if (getClass() != g.getClass()) {
         return false;
      }
      DTransition g1 = (DTransition) g;
      return (f.equals(g1.f) && lhs.equals(g1.lhs) && q0.equals(g1.q0));
   }

}
