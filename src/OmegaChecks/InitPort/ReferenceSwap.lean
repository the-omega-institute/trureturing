module
public import Lean
public import OmegaChecks.InitPort.Alternatives.ReferenceSwap
import all Init.System.ST

open Lean

namespace OmegaChecks.InitPort.ReferenceSwap

private noncomputable def officialDefault {σ α : Type} (r : ST.Ref σ α) (_ : α) : ST σ α :=
  ST.pure (Classical.choice r.h)

/-- Both fallback terms only inhabit a sealed constant. Its execution is supplied by the
same borrowed reference swap, which returns the previous payload. -/
public def check (strict publicStrict reference : Environment) (native : OpaqueVal) (candidate : Expr) : IO Unit := do
  let strictName := `Omega.ST.Prim.Ref.swap
  let some (.opaqueInfo full) := strict.find? strictName | throw <| IO.userError "missing opaque swap"
  let some exported := publicStrict.find? strictName | throw <| IO.userError "missing public swap"
  unless (exported.isAxiom || exported matches .opaqueInfo _) && !full.isUnsafe &&
      native.name == `ST.Prim.Ref.swap && !native.isUnsafe &&
      reference.getModuleIdxFor? native.name == reference.getModuleIdx? `Init.System.ST &&
      strict.getModuleIdxFor? strictName == strict.getModuleIdx? `OmegaInit.System.ST &&
      getExternNameFor reference `c native.name == some "lean_st_ref_swap" &&
      Kernel.isDefEqGuarded reference {} native.value (mkConst ``officialDefault) &&
      Kernel.isDefEqGuarded reference {} candidate (mkConst ``Alternatives.ST.Prim.Ref.swap) do
    throw <| IO.userError "mismatched sealed reference swap or native implementation"

end OmegaChecks.InitPort.ReferenceSwap
