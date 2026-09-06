import LeanInformationAudit.Projection.ProjectionCounts
import LeanInformationAudit.Projection.ProjectionSchema
import LeanInformationAudit.CatalogBuilder

namespace LeanInformationAudit

open Lean Lean.Meta
open D5.S3.ConceptDynamics.InformationEscape

abbrev ProjectionM := StateT (Array Declaration) Lean.Elab.Term.TermElabM

namespace ProjectionProof

def fin (index size : Nat) : MetaM Expr := do
  mkAppM ``Fin.mk #[mkNatLit index, ← mkDecideProof (← mkLT (mkNatLit index) (mkNatLit size))]

def vector (values : Array Expr) : MetaM Expr := do
  let first := values[0]!
  let mut result ← withLocalDeclD `impossible (mkApp (mkConst ``Fin) (mkNatLit 0)) fun index => do
    let target ← inferType first
    let body ← mkAppOptM ``Fin.elim0 #[some target, some index]
    mkLambdaFVars #[index] body
  for value in values.reverse do
    result ← mkAppM ``Matrix.vecCons #[value, result]
  pure result

def selection (size : Nat) (indices : Array Nat) : MetaM Expr := do
  let type := mkApp (mkConst ``Fin) (mkNatLit size)
  let mut selected ← mkAppOptM ``Finset.empty #[some type]
  for index in indices.reverse do
    selected ← mkAppM ``Insert.insert #[← fin index size, selected]
  pure selected

def truth (proposition : Expr) : MetaM Bool := do
  withTransparency .all <| reduceEval (← mkDecide proposition)

def proof (name : Name) (value : Expr) : ProjectionM Name := do
  let type ← inferType value
  unless ← isProp type do throwError "projection certificate is not a proposition: {name}"
  checkWithKernel value
  modify (·.push (.thmDecl { name, levelParams := [], type, value }))
  pure name

def value (name : Name) (value : Expr) : ProjectionM Name := do
  checkWithKernel value
  let type ← inferType value
  modify (·.push (.defnDecl {
    name, levelParams := [], type, value, hints := .abbrev, safety := .safe }))
  pure name

def decide (name : Name) (proposition : Expr) : ProjectionM Name := do
  proof name (← mkDecideProof proposition)

def count (name : Name) (expression : Expr) : ProjectionM (Nat × Name) := do
  let args := expression.getAppArgs
  let reduction ← if expression.isAppOf ``Catalog.pairwiseCaptureOverlapCount then
      some <$> mkAppM ``projectionOverlapCount_eq (args.extract (args.size - 3) args.size)
    else if expression.isAppOf ``Catalog.captureSpectrum then
      some <$> mkAppM ``projectionSpectrum_eq (args.extract (args.size - 2) args.size)
    else if expression.isAppOf ``GeneratorSchedule.incrementCount then do
      let equality ← mkAppM ``projectionIncrementCount_eq
        (args.extract (args.size - 2) args.size)
      some <$> mkAppM ``Eq.symm #[equality]
    else pure none
  let computed ← match reduction with
    | some equality => pure (← inferType equality).eq?.get!.2.1
    | none => pure expression
  let number : Nat ← withTransparency .all <| reduceEval computed
  let numeric ← mkDecideProof (← mkEq computed (mkNatLit number))
  let evidence ← match reduction with
    | some equality => mkAppM ``Eq.trans #[← mkAppM ``Eq.symm #[equality], numeric]
    | none => pure numeric
  let certificate ← proof name evidence
  pure (number, certificate)

def conjunction (proofs : Array Expr) : MetaM Expr := do
  let mut result := mkConst ``True.intro
  for proof in proofs.reverse do
    result ← mkAppM ``And.intro #[proof, result]
  pure result

def arenaDecideProof (arena proposition : Expr) : MetaM Expr := do
  let decEq ← mkAppM ``Arena.stateDecidableEq #[arena]
  withLetDecl `stateDecidableEq (← inferType decEq) decEq fun instanceValue => do
    withNewLocalInstance ``DecidableEq instanceValue do
      mkLetFVars #[instanceValue] (← mkDecideProof proposition)

/-- Extract a concrete enumerator and certify it; no unsafe evaluator supplies evidence. -/
def enumeration (arena : Expr) (arenaName : Name) : MetaM Expr := do
  let name := arenaName.str "__state_enumeration"
  if (← getEnv).contains name then
    let candidate ← mkConstWithFreshMVarLevels name
    let expected ← mkAppM ``Arena.StateEnumeration #[arena]
    if ← isDefEq (← inferType candidate) expected then return candidate
  let fintype ← mkAppM ``Arena.stateFintype #[arena]
  let stateType ← mkAppM ``Arena.State #[arena]
  let elems ← mkAppOptM ``Fintype.elems #[some stateType, some fintype]
  let multiset ← whnf (← mkAppM ``Finset.val #[elems])
  unless multiset.isAppOfArity ``Quot.mk 3 do
    throwError "cannot reflect the arena state enumeration: {arenaName}"
  let states := multiset.getArg! 2
  let nodupProof ← mkAppM ``Finset.nodup #[elems]
  let decEq ← mkAppM ``Arena.stateDecidableEq #[arena]
  let stateSet ← mkAppOptM ``List.toFinset #[some stateType, some decEq, some states]
  let complete ← mkEq stateSet elems
  let completeProof ← arenaDecideProof arena complete
  mkAppOptM ``Arena.StateEnumeration.mk
    #[some arena, some states, some nodupProof, some completeProof]

end ProjectionProof

end LeanInformationAudit
