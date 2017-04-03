//
// Generated by JTB 1.3.2
//

package dfta.parser.syntaxtree;

/**
 * Grammar production:
 * f0 -> <TRANSITIONS>
 * f1 -> TimbukTransitionList()
 */
public class TimbukTransitions implements Node {
   public NodeToken f0;
   public TimbukTransitionList f1;

   public TimbukTransitions(NodeToken n0, TimbukTransitionList n1) {
      f0 = n0;
      f1 = n1;
   }

   public TimbukTransitions(TimbukTransitionList n0) {
      f0 = new NodeToken("Transitions");
      f1 = n0;
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

