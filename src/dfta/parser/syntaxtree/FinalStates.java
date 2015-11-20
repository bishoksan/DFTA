//
// Generated by JTB 1.3.2
//

package dfta.parser.syntaxtree;

/**
 * Grammar production:
 * f0 -> <FINAL>
 * f1 -> <STATES>
 * f2 -> Ident()
 * f3 -> ( Ident() )*
 * f4 -> <FULLSTOP>
 */
public class FinalStates implements Node {
   public NodeToken f0;
   public NodeToken f1;
   public Ident f2;
   public NodeListOptional f3;
   public NodeToken f4;

   public FinalStates(NodeToken n0, NodeToken n1, Ident n2, NodeListOptional n3, NodeToken n4) {
      f0 = n0;
      f1 = n1;
      f2 = n2;
      f3 = n3;
      f4 = n4;
   }

   public FinalStates(Ident n0, NodeListOptional n1) {
      f0 = new NodeToken("Final");
      f1 = new NodeToken("States");
      f2 = n0;
      f3 = n1;
      f4 = new NodeToken(".");
   }

   public void accept(dfta.parser.visitor.Visitor v) {
      v.visit(this);
   }
   public <R,A> R accept(dfta.parser.visitor.GJVisitor<R,A> v, A argu) {
      return v.visit(this,argu);
   }
   public <R> R accept(dfta.parser.visitor.GJNoArguVisitor<R> v) {
      return v.visit(this);
   }
   public <A> void accept(dfta.parser.visitor.GJVoidVisitor<A> v, A argu) {
      v.visit(this,argu);
   }
}

