package dfta;

import java.util.HashSet;
import java.util.ArrayList;

public class PTransition {

   FuncSymb f;
   HashSet<String> q0;
   ArrayList<HashSet<HashSet<String>>> lhs;

   public PTransition(FuncSymb f, HashSet<String> q0, ArrayList<HashSet<HashSet<String>>> lhs) {
      this.f = f;
      this.q0 = q0;
      this.lhs = lhs;
   }

   public PTransition(FuncSymb f, HashSet<String> q0) {
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
}
