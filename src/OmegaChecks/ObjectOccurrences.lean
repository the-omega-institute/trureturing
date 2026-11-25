import Lean

open Lean

namespace OmegaChecks.ObjectOrigins

/-- Positions in the elaborated type survive aliases, notation and field resolution. -/
def occurrences (e : Expr) (includeBinderNames := true) : Array (Name × Name) :=
  collect e `type #[]
where
  binderPosition (pos binder : Name) := if includeBinderNames then pos ++ binder.eraseMacroScopes else pos
  collect (term : Expr) (pos : Name) (acc : Array (Name × Name)) : Array (Name × Name) :=
    match term with
    | .const n _ => acc.push (pos, n)
    | .proj s i target => collect target (.str pos "target") (acc.push (.num (.str pos "field") i, s))
    | .app fn arg => collect arg (.str pos "arg") (collect fn (.str pos "fn") acc)
    | .forallE binder dom body _ | .lam binder dom body _ =>
      collect body (.str pos "body") (collect dom (binderPosition (.str pos "binder") binder) acc)
    | .letE binder type value body _ =>
      let acc := collect type (binderPosition (.str pos "letType") binder) acc
      collect body (.str pos "body") (collect value (.str pos "value") acc)
    | .mdata _ body => collect body pos acc
    | _ => acc

end OmegaChecks.ObjectOrigins
