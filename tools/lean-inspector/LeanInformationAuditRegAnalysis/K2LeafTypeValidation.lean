import LeanInformationAuditRegAnalysis.K2FactsGeneratorCore

open Lean Meta

namespace K2LeafTypeValidation

private def checkRaw (label : String) (node : Expr) : MetaM Unit := do
  let fast ← K2FactsGenerator.inferNodeType node
  let pinned ← inferType node
  unless fast.equal pinned do
    throwError "leaf type mismatch ({label}): fast {fast}, pinned {pinned}"

private def rejected (action : MetaM Expr) : MetaM Bool := do
  try
    let _ ← action
    return false
  catch _ =>
    return true

private def checkRejected (label : String) (node : Expr) : MetaM Unit := do
  unless (← rejected (K2FactsGenerator.inferNodeType node)) do
    throwError "fast path accepted invalid expression ({label})"
  unless (← rejected (inferType node)) do
    throwError "pinned compiler accepted invalid expression ({label})"

private def validate : MetaM Unit := do
  checkRaw "natural literal" (mkNatLit 42)
  checkRaw "string literal" (mkStrLit "leaf type")
  checkRaw "sort zero" (mkSort .zero)
  checkRaw "sort universe parameter" (mkSort (.param `u))
  checkRaw "sort unsimplified imax" (mkSort (.imax (.param `u) (.succ .zero)))
  checkRaw "constant Nat" (mkConst ``Nat)
  checkRaw "constant Eq parameter" (mkConst ``Eq [.param `u])
  checkRaw "constant Eq concrete" (mkConst ``Eq [.succ .zero])
  withLocalDeclD `ordinary (mkConst ``Nat) fun leaf =>
    checkRaw "ordinary fvar" leaf
  withLetDecl `assigned (mkConst ``Nat) (mkNatLit 7) (nondep := false) fun leaf =>
    checkRaw "assigned dependent let fvar" leaf
  withLetDecl `assignedNondep (mkConst ``Nat) (mkNatLit 9) (nondep := true) fun leaf =>
    checkRaw "assigned nondependent let fvar" leaf
  let typeVariable ← mkFreshExprMVar (some (mkSort (.succ .zero)))
  withLocalDeclD `pendingType typeVariable fun leaf => do
    checkRaw "fvar type with unassigned metavariable" leaf
    unless (← K2FactsGenerator.inferNodeType leaf).equal typeVariable do
      throwError "unassigned fvar type was changed"
    typeVariable.mvarId!.assign (mkConst ``Nat)
    checkRaw "fvar type with assigned metavariable" leaf
    unless (← K2FactsGenerator.inferNodeType leaf).equal typeVariable do
      throwError "assigned fvar type was instantiated"
  checkRaw "application fallback" (mkApp (mkConst ``Nat.succ) (mkNatLit 1))
  checkRaw "forall fallback" (.forallE `n (mkConst ``Nat) (mkConst ``Nat) .default)
  checkRaw "lambda fallback" (.lam `n (mkConst ``Nat) (mkBVar 0) .default)
  checkRaw "dependent let fallback" (.letE `n (mkConst ``Nat) (mkNatLit 3) (mkBVar 0) false)
  checkRaw "nondependent let fallback" (.letE `n (mkConst ``Nat) (mkNatLit 3) (mkNatLit 4) true)
  let pair := mkApp4 (mkConst ``Prod.mk [.zero, .zero])
    (mkConst ``Nat) (mkConst ``Nat) (mkNatLit 1) (mkNatLit 2)
  checkRaw "projection fallback" (.proj ``Prod 0 pair)
  checkRaw "metadata fallback" (.mdata {} (mkNatLit 5))
  let valueVariable ← mkFreshExprMVar (some (mkConst ``Nat))
  checkRaw "metavariable fallback" valueVariable
  checkRejected "Nat excessive universe arguments" (mkConst ``Nat [.zero])
  checkRejected "Eq missing universe argument" (mkConst ``Eq)
  checkRejected "unknown constant" (mkConst `K2UnknownLeafConstant)
  IO.eprintln "K2LeafTypeValidation passed: 21 raw type comparisons, 2 raw metavariable-preservation checks, 3 paired rejection checks"

run_meta validate

end K2LeafTypeValidation
