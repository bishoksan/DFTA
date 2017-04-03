//
// Generated by JTB 1.3.2
//

package dfta.parser.syntaxtree;

/**
 * Grammar production:
 * f0 -> <IDENTIFIER>
 * f1 -> <COLON>
 * f2 -> <NUMBER>
 */
public class LabelDecl implements Node {
   public NodeToken f0;
   public NodeToken f1;
   public NodeToken f2;

   public LabelDecl(NodeToken n0, NodeToken n1, NodeToken n2) {
      f0 = n0;
      f1 = n1;
      f2 = n2;
   }

   public LabelDecl(NodeToken n0, NodeToken n1) {
      f0 = n0;
      f1 = new NodeToken(":");
      f2 = n1;
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

