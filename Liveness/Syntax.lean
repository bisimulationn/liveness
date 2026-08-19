namespace Liveness

inductive Expr where
  | const : Int → Expr
  | var : String → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | lt : Expr → Expr → Expr
  | eq : Expr → Expr → Expr
  deriving Repr, DecidableEq

inductive Stmt where
  | skip : Stmt
  | assign : String → Expr → Stmt
  | seq : Stmt → Stmt → Stmt
  | ite : Expr → Stmt → Stmt → Stmt
  | while : Expr → Stmt → Stmt
  deriving Repr, DecidableEq

namespace Stmt

def size : Stmt → Nat
  | skip => 0
  | assign _ _ => 1
  | seq s₁ s₂ => s₁.size + s₂.size + 1
  | ite _ s₁ s₂ => s₁.size + s₂.size + 1
  | .while _ s => s.size + 1

end Stmt

end Liveness
