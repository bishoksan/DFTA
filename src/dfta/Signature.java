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
class Signature {
   FuncSymb f;
   int i;
   
   Signature(FuncSymb f, int i){
      this.f = f;
      this.i = i;
   }
   
   

   @Override
   public boolean equals(Object g) {
      Signature g1 = (Signature) g;
      return (i == g1.i && f.equals(g1.f));
   }

   @Override
   public int hashCode() {
      return i * 127 + f.hashCode();
   }
   
   public String toString() {
      return "("+f + ","+i+")";
   }
}
