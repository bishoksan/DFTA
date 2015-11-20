//
// Generated by JTB 1.3.2
//

package dfta.parser.syntaxtree;

/**
 * Grammar production:
 * f0 -> Ident() ( <LBRACE> Ident() ( <COMMA> Ident() )* <RBRACE> <ARROW> | <ARROW> | <BINOP> Ident() <ARROW> | <ANYOP> Ident() <ARROW> | <COMMA> Ident() <ARROW> )
 *       | <NUMBER> <ARROW>
 *       | <ANYOP> ( <NUMBER> | Ident() ) <ARROW>
 *       | <LSQBRACE> ( Ident() <VERTBAR> Ident() <RSQBRACE> <ARROW> | <RSQBRACE> <ARROW> )
 *       | <LBRACE> Ident() ( <COMMA> | <BINOP> ) Ident() <RBRACE> <ARROW>
 */
public class LHS implements Node {
   public NodeChoice f0;

   public LHS(NodeChoice n0) {
      f0 = n0;
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

