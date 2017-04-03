/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package dfta;

/**
 *
 * @author jpg
 */
public class Atom {

   String pred;
   int[] ys;

   Atom(String p, int[] xs) {
      pred = p;
      ys = xs;
   }

   @Override
   public String toString() {

      if (pred.substring(0, 4).equals("lhsf")) {
         return "lhsf(" + pred + ", [" + vars(ys) + "])";
      } else if (pred.substring(0, 4).equals("lhs0")) {
         return "lhs0(" + pred + ", [" + vars(ys) + "])";
      } else if (pred.substring(0, 3).equals("rhs")) {
         return "rhs(" + pred + ", [" + vars(ys) + "])";
      } else {
         return pred + "(" + vars(ys) + ")";
      }
   }

   public String toz3() {

      return "(" + pred + " " + varsz3(ys) + ")";
   }

   String vars(int[] xs) {
      String s = "";
      for (int i = 0; i < xs.length; i++) {
         if (xs[i] == -1 | xs[i] == -2) {
            s += xs[i] + 2;
         } else {
            s += "x" + xs[i];
         }
         if (i < xs.length - 1) {
            s += ",";
         }
      }
      return s;
   }

   String varsz3(int[] xs) {
      String s = "";
      for (int i = 0; i < xs.length; i++) {
         if (xs[i] == -1) {
            s += "true";
         } else if (xs[i] == -2) {
            s += "false";
         } else {
            s += "x" + xs[i];
            //s += xs[i];
         }
         if (i < xs.length - 1) {
            s += " ";
         }
      }
      return s;
   }

}
