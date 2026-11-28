module
prelude
public import OmegaInit.Control.Basic
public import OmegaInit.Control.Id

@[export omega_mixed_or]
public def orResult (a b : Omega.Bool) : Omega.Bool :=
  @Omega.orM Omega.Id Omega.Bool Omega.Id.instMonad (Omega.ToBool.mk (fun x => x)) a b

@[export omega_mixed_and]
public def andResult (a b : Omega.Bool) : Omega.Bool :=
  @Omega.andM Omega.Id Omega.Bool Omega.Id.instMonad (Omega.ToBool.mk (fun x => x)) a b

@[export omega_mixed_quotation, instance_reducible] public def quotationDefault (_ : Omega.Bool) := Omega.Lean.Macro.instMonadQuotationMacroM

@[export omega_mixed_depth]
public def depthPositive (_ : Omega.Bool) : Omega.Bool :=
  Omega.Nat.casesOn (motive := fun _ => Omega.Bool) Omega.Lean.defaultMaxRecDepth .false (fun _ => .true)

@[noinline] private def noChildren (stx : Omega.Lean.Syntax) : Omega.Bool :=
  Omega.Nat.casesOn (motive := fun _ => Omega.Bool) (Omega.Lean.Syntax.getNumArgs stx) .true (fun _ => .false)

@[export omega_mixed_empty_syntax]
public def missingHasNoChildren (_ : Omega.Bool) : Omega.Bool := noChildren .missing
