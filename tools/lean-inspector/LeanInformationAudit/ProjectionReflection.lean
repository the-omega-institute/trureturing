import LeanInformationAudit.ProjectionCertificates

namespace LeanInformationAudit

open Lean Lean.Meta
open D5.S3.ConceptDynamics.CIRPT
open D5.S3.ConceptDynamics.InformationEscape

universe u v w

namespace ProjectionProof

structure ReflectedRefinementSnapshot where
  cells : Array (Array Bool)

private def refinementSnapshotRequest {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    {n : Nat} (nodes : Fin n → catalog.GeneratedKernel) : ReflectedRefinementTable n :=
  fun a b => projectionRefinesB (nodes a) (nodes b)

private instance : ReduceEval ReflectedRefinementSnapshot where
  reduceEval request := do
    unless request.isAppOfArity ``refinementSnapshotRequest 4 do
      throwError "reduceEval: expected a reflected refinement request"
    let size : Nat ← reduceEval (request.getArg! 2)
    let mut cells := #[]
    for i in [:size] do
      let mut row := #[]
      for j in [:size] do
        let cell : Bool ← reduceEval (mkApp2 request (← fin i size) (← fin j size))
        row := row.push cell
      cells := cells.push row
    pure { cells }

structure CheckedRefinement where
  nodes : Expr
  table : Expr
  checked : Expr
  snapshot : ReflectedRefinementSnapshot
  certificate : Name

private partial def finiteProof (motive : Expr) (proofs : Array Expr)
    (offset remaining : Nat) : MetaM Expr := do
  let domain := mkApp (mkConst ``Fin) (mkNatLit remaining)
  if remaining == 0 then
    return ← withLocalDeclD `index domain fun index => do
      mkLambdaFVars #[index] (← mkAppOptM ``Fin.elim0 #[some (mkApp motive index), some index])
  let tailDomain := mkApp (mkConst ``Fin) (mkNatLit (remaining - 1))
  let tailMotive ← withLocalDeclD `index tailDomain fun index => do
    mkLambdaFVars #[index] (mkApp motive (← mkAppM ``Fin.succ #[index]))
  let tail ← finiteProof tailMotive proofs (offset + 1) (remaining - 1)
  withLocalDeclD `index domain fun index => do
    mkLambdaFVars #[index] (← mkAppOptM ``Fin.cases
      #[some (mkNatLit (remaining - 1)), some motive, some proofs[offset]!, some tail, some index])

private def checkRefinementCells (nodes table : Expr) (size : Nat) : MetaM Expr := do
  let domain := mkApp (mkConst ``Fin) (mkNatLit size)
  let proposition (a b : Expr) := do
    mkEq (mkApp2 table a b) (← mkAppM ``projectionRefinesB #[mkApp nodes a, mkApp nodes b])
  let mut rows := #[]
  for i in [:size] do
    let a ← fin i size
    let mut cells := #[]
    for j in [:size] do
      let b ← fin j size
      cells := cells.push (← mkDecideProof (← proposition a b))
    let motive ← withLocalDeclD `b domain fun b => do
      mkLambdaFVars #[b] (← proposition a b)
    rows := rows.push (← finiteProof motive cells 0 size)
  let motive ← withLocalDeclD `a domain fun a => do
    let row ← withLocalDeclD `b domain fun b => do
      mkForallFVars #[b] (← proposition a b)
    mkLambdaFVars #[a] row
  let pointwise ← finiteProof motive rows 0 size
  mkAppM ``decide_eq_true #[pointwise]

def reflectRefinement (nodes : Expr) (certPrefix : Name) : ProjectionM CheckedRefinement := do
  let request ← mkAppM ``refinementSnapshotRequest #[nodes]
  let snapshot : ReflectedRefinementSnapshot ← reduceEval request
  let rows ← snapshot.cells.mapM fun row =>
    vector (row.map fun cell => mkConst (if cell then ``Bool.true else ``Bool.false))
  let table ← vector rows
  let _ ← value (certPrefix.str "table") table
  let checked ← checkRefinementCells nodes table snapshot.cells.size
  let sound ← mkAppM ``reflectedRefines_sound #[nodes, table, checked]
  let certificate ← proof (certPrefix.str "sound") sound
  pure { nodes, table, checked, snapshot, certificate }

private partial def readoutEquality (type : Expr) : MetaM Expr := do
  let type ← whnf type
  if type.isAppOfArity ``Sum 2 then
    return ← mkAppOptM ``projectionSumDecision #[some (type.getArg! 0),
      some (type.getArg! 1), some (← readoutEquality (type.getArg! 0)),
      some (← readoutEquality (type.getArg! 1))]
  if type.isForall then
    return ← forallBoundedTelescope type (some 1) fun arguments target => do
      let decision ← readoutEquality target
      let instances ← mkLambdaFVars arguments decision
      let domain := (← inferType arguments[0]!)
      let family ← mkLambdaFVars arguments target
      mkAppOptM ``Fintype.decidablePiFintype
        #[some domain, some family, some instances, none]
  synthInstance (← mkAppM ``DecidableEq #[type])

private def reflectUnit (unit : Expr) : MetaM (Expr × Expr) := do
  let bundle ← mkAppM ``TheoremUnit.primitives #[unit]
  let indexType ← mkAppM ``PrimitiveBundle.Index #[bundle]
  let readouts ← withLocalDeclD `primitive indexType fun index => do
    let atom ← mkAppM ``PrimitiveBundle.atom #[bundle, index]
    let kernel ← mkAppM ``PrimitiveAtom.kernel #[atom]
    let relation ← mkAppM ``DecidableKernel.relation #[kernel]
    let decision ← forallTelescope (← inferType relation) fun states _ => do
      let proposition ← whnf (mkAppN relation states)
      let some (type, left, right) := proposition.eq?
        | throwError "readout reflection requires an equality kernel"
      let equality ← readoutEquality type
      mkLambdaFVars states (mkApp2 equality left right)
    let reflected ← mkAppM ``ProjectionReadout.ofDecision #[kernel, decision]
    mkLambdaFVars #[index] reflected
  pure (← mkAppM ``projectionReadoutUnit #[unit, readouts],
    ← mkAppM ``projectionReadoutUnit_eq #[unit, readouts])

/-- Reflect readout decisions, retaining a kernel proof of equality to the input catalog. -/
def reflectCatalog (catalog : Expr) (size : Nat) : MetaM (Expr × Expr) := do
  let mut reflected := #[]
  let mut equalities := #[]
  for i in [:size] do
    let unit ← mkAppM ``Catalog.theoremAt #[catalog, ← fin i size]
    let (replacement, equality) ← try reflectUnit unit catch _ =>
      pure (unit, ← mkEqRefl unit)
    reflected := reflected.push replacement
    equalities := equalities.push equality
  let reflectedVector ← vector reflected
  let originalFunction ← mkAppM ``Catalog.theoremAt #[catalog]
  let reconstructed ← mkAppM ``Catalog.ofVector #[originalFunction]
  unless ← isDefEq reconstructed catalog do
    throwError "readout reflection requires a materialized Fin catalog"
  let motive ← withLocalDeclD `index (mkApp (mkConst ``Fin) (mkNatLit size)) fun index => do
    mkLambdaFVars #[index] (← mkEq (mkApp reflectedVector index) (mkApp originalFunction index))
  let pointwise ← finiteProof motive equalities 0 size
  let vectorEquality ← mkAppM ``funext #[pointwise]
  let constructor ← withLocalDeclD `units (← inferType originalFunction) fun units => do
    mkLambdaFVars #[units] (← mkAppM ``Catalog.ofVector #[units])
  let equality ← mkCongrArg constructor vectorEquality
  checkWithKernel equality
  pure (← mkAppM ``Catalog.ofVector #[reflectedVector], equality)

end ProjectionProof
end LeanInformationAudit
