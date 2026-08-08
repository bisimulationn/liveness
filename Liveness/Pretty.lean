import Liveness.Syntax

namespace Liveness

namespace Expr

def pretty : Expr → String
  | const n => toString n
  | var x => x
  | add e₁ e₂ => "(" ++ e₁.pretty ++ " + " ++ e₂.pretty ++ ")"
  | sub e₁ e₂ => "(" ++ e₁.pretty ++ " - " ++ e₂.pretty ++ ")"

end Expr

namespace Stmt

def prettyLines (indent : String) : Stmt → List String
  | skip => [indent ++ "skip"]
  | assign x e => [indent ++ x ++ " := " ++ e.pretty]
  | seq s₁ s₂ => s₁.prettyLines indent ++ s₂.prettyLines indent
  | ite e s₁ s₂ =>
    [indent ++ "if " ++ e.pretty ++ " then"] ++ s₁.prettyLines (indent ++ "  ") ++
      [indent ++ "else"] ++ s₂.prettyLines (indent ++ "  ")
  | .while e s =>
    [indent ++ "while " ++ e.pretty ++ " do"] ++ s.prettyLines (indent ++ "  ")

def pretty (s : Stmt) : String := String.intercalate "\n" (s.prettyLines "")

end Stmt

end Liveness
