/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package dfta;

import java.util.ArrayList;

/**
 *
 * @author jpg
 */
public class Clause {
   
   Atom head;
   ArrayList<Atom> body;
   
   Clause(Atom h, ArrayList<Atom> b) {
      head = h;
      body = b;
   }
   
   public String toString() {
      String s = "";
      for (int i=0; i<body.size(); i++) {
         s += body.get(i).toString();
         if (i<body.size()-1) s+= ", ";
      }
      if (body.isEmpty()) return head.toString()+".";
      else return head.toString()+ " :- " + s + ".";
   }
}
