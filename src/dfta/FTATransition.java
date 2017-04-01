package dfta;

import java.util.ArrayList;

public class FTATransition implements Comparable<FTATransition> {

   FuncSymb f;
   String q0;
   ArrayList<String> lhs;
   int m;

   public FTATransition(FuncSymb f, String q0, ArrayList<String> lhs, int m) {
      this.f = f;
      this.q0 = q0;
      this.lhs = lhs;
      this.m = m;
   }

   public FTATransition(FuncSymb f, String q0) {
      this.f = f;
      this.q0 = q0;
      this.lhs = new ArrayList<String>();
   }

   @Override
   public String toString() {
      return Integer.toString(m);
   }

   @Override
   public int hashCode() {
      return m;
   }

   @Override
   public boolean equals(Object g) {
      return (m == ((FTATransition) g).m);
   }

   @Override
   public int compareTo(FTATransition g) {
      int c = 0;
      if (m == g.m) {
         c = 0;
      }
      if (m > g.m) {
         c = 1;
      }
      if (m < g.m) {
         c = -1;
      }

      return c;
   }

}
