module
prelude
public import OmegaInit.Prelude

/-- Exercise both ways of appending a scoped name and consecutive scopes from two contexts. -/
@[export omega_test_scoped_name]
public def scopedName (left right : Omega.Lean.Name) (scope : Nat) (onLeft : Bool) : Omega.Lean.Name :=
  let scopedName' := Omega.Lean.addMacroScope right (Omega.Lean.addMacroScope left left scope) scope.succ
  let joined := match onLeft with
    | .true => Omega.Lean.Name.append scopedName' right
    | .false => Omega.Lean.Name.append right scopedName'
  (Omega.Lean.extractMacroScopes joined).review
