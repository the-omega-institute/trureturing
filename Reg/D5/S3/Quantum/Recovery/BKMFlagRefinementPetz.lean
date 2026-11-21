import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Recovery.BKMFlagRefinementPetz

/-! Source-bound readouts for classical flag refinement of testing and recovery. -/

noncomputable section

open LeanInformationAudit Matrix
open scoped BigOperators ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open _root_.D5.S3.Quantum.Recovery.BKMFlagRefinement

namespace Reg.D5.S3.Quantum.Recovery.BKMFlagRefinementPetz

universe u v z

private def unitWeight : ∀ _ : ULift.{v} Unit, ULift.{z} Unit → ℝ :=
  fun _ _ => 1

private theorem unitWeight_sum : ∀ i, ∑ j, unitWeight.{v, z} i j = 1 := by
  intro i
  simp [unitWeight]

private abbrev scalarSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def scalarActual : Realization scalarSignature :=
  realize scalarSignature (fun _ _ x y => x = y) (fun e => nomatch e)

private def scalarRejected : Realization scalarSignature :=
  realize scalarSignature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem scalarDependence : ObservationalDependence scalarSignature scalarActual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he : (1 : ℝ) = 0 := Eq.mp (congrFun h 0) rfl
  exact one_ne_zero he

namespace BinaryTesting

abbrev arena : Arena where
  signature := scalarSignature
  Law R := ∀ {n : Type u} {ι : Type v}
    [Fintype n] [Fintype ι] [DecidableEq ι]
    {J : ι → Type z} [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]
    (w : ∀ i, J i → ℝ) (hw : ∀ i j, 0 ≤ w i j) (hs : ∀ i, ∑ j, w i j = 1)
    (S T : ι → Matrix n n ℂ) (prior : ℝ),
    R.readout () ()
      (traceNorm (prior • joint (refinedBlocks w S) - (1 - prior) • joint (refinedBlocks w T)))
      (traceNorm (prior • joint S - (1 - prior) • joint T))

private theorem rejected_law : ¬ arena.{u, v, z}.Law scalarRejected := by
  intro h
  let S : ULift.{v} Unit → Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ := fun _ => 0
  exact h (J := fun _ => ULift.{z} Unit) unitWeight.{v, z} (fun _ _ => zero_le_one)
    unitWeight_sum S S 0

def family : Registration arena.{u, v, z} (type_of% @refine_binary_testing.{u, v, z}) where
  actual := scalarActual
  bridge := Iff.rfl
  variation := ⟨@refine_binary_testing.{u, v, z}, scalarRejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law scalarActual scalarRejected rejected_law
  dependence := scalarDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@refine_binary_testing.{u, v, z}) (Realization scalarSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.BKMFlagRefinement.refine_binary_testing.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.BKMFlagRefinementPetz.BinaryTesting.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v, z}⟩
  objectArena := .source ⟨arena.{u, v, z}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u, v, z} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.BKMFlagRefinementPetz
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end BinaryTesting

namespace OrdinaryPetz

private abbrev RefinedMatrix : (Σ _ : Type u, Σ ι : Type v, ι → Type z) → Type _
  | ⟨n, ι, J⟩ => Matrix (n × (Σ i, J i)) (n × (Σ i, J i)) ℂ

abbrev signature : Signature where
  Params := Σ _ : Type u, Σ ι : Type v, ι → Type z
  State := RefinedMatrix.{u, v, z}
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := RefinedMatrix.{u, v, z} p → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature.{u, v, z} :=
  realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e)

private def rejected : Realization signature.{u, v, z} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private def law (R : Realization signature.{u, v, z}) : Prop :=
  ∀ {n : Type u} {ι : Type v}
    [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
    {J : ι → Type z} [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]
    (T : ι → Matrix n n ℂ) (hT : ∀ i, (T i).PosDef)
    (w : ∀ i, J i → ℝ) (hw : ∀ i j, 0 < w i j) (hs : ∀ i, ∑ j, w i j = 1)
    (X : Matrix n n ℂ),
    R.readout () ⟨n, ι, J⟩
      (partialTracePetz (joint (refinedBlocks w T)) X)
      (joint (refinedBlocks w (petzBlocks T X)))

abbrev arena : Arena where
  signature := signature.{u, v, z}
  Law := law

private theorem rejected_law : ¬ arena.{u, v, z}.Law rejected.{u, v, z} := by
  intro h
  let T : ULift.{v} Unit → Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ := fun _ => 1
  exact h (J := fun _ => ULift.{z} Unit) T (fun _ => Matrix.PosDef.one)
    unitWeight.{v, z} (fun _ _ => zero_lt_one) unitWeight_sum 0

private theorem dependence : ObservationalDependence signature.{u, v, z} actual := by
  intro role
  let n := ULift.{u} Unit
  let ι := ULift.{v} Unit
  let J : ι → Type z := fun _ => ULift.{z} Unit
  let q : n × (Σ i, J i) := ⟨⟨()⟩, ⟨⟨()⟩, ⟨()⟩⟩⟩
  let A : Matrix (n × (Σ i, J i)) (n × (Σ i, J i)) ℂ := fun _ _ => 1
  refine ⟨⟨n, ι, J⟩, 0, A, ?_⟩
  intro h
  have he : A = 0 := Eq.mp (congrFun h 0) rfl
  exact one_ne_zero (show (1 : ℂ) = 0 from congrArg (fun M => M q q) he)

private def sourceStatement : Prop := type_of% @refine_ordinaryPetz.{u, v, z}

private theorem sourceBridge : sourceStatement.{u, v, z} ↔ arena.{u, v, z}.Law actual :=
  Iff.rfl

private theorem variation : Variation arena.{u, v, z} actual :=
  ⟨@refine_ordinaryPetz.{u, v, z}, rejected, rejected_law⟩

private theorem sensitivity : Sensitivity arena.{u, v, z} actual := by
  constructor
  · intro role
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro other different
    exact (different (Subsingleton.elim other role)).elim
  · intro e
    exact nomatch e

def family : Registration arena.{u, v, z} sourceStatement.{u, v, z} where
  actual := actual
  bridge := sourceBridge
  variation := variation
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (P := sourceStatement.{u, v, z}) (@refine_ordinaryPetz.{u, v, z})
    (Realization signature.{u, v, z}) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.BKMFlagRefinement.refine_ordinaryPetz.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.BKMFlagRefinementPetz.OrdinaryPetz.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v, z}⟩
  objectArena := .source ⟨arena.{u, v, z}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u, v, z} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u, v, z} (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.BKMFlagRefinementPetz
    definition := none
    coordinates := #[0, 1, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end OrdinaryPetz

namespace TraceError

abbrev arena : Arena where
  signature := scalarSignature
  Law R := ∀ {n : Type u} {ι : Type v}
    [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
    {J : ι → Type z} [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]
    (S T : ι → Matrix n n ℂ) (hT : ∀ i, (T i).PosDef)
    (w : ∀ i, J i → ℝ) (hw : ∀ i j, 0 < w i j) (hs : ∀ i, ∑ j, w i j = 1),
    R.readout () ()
      (traceNorm (joint (refinedBlocks w S) -
        partialTracePetz (joint (refinedBlocks w T)) (marginal (refinedBlocks w S))))
      (traceNorm (joint S - partialTracePetz (joint T) (marginal S)))

private theorem rejected_law : ¬ arena.{u, v, z}.Law scalarRejected := by
  intro h
  let S : ULift.{v} Unit → Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ := fun _ => 0
  let T : ULift.{v} Unit → Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ := fun _ => 1
  exact h (J := fun _ => ULift.{z} Unit) S T (fun _ => Matrix.PosDef.one)
    unitWeight.{v, z} (fun _ _ => zero_lt_one) unitWeight_sum

def family : Registration arena.{u, v, z} (type_of% @refine_petz_error.{u, v, z}) where
  actual := scalarActual
  bridge := Iff.rfl
  variation := ⟨@refine_petz_error.{u, v, z}, scalarRejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law scalarActual scalarRejected rejected_law
  dependence := scalarDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@refine_petz_error.{u, v, z}) (Realization scalarSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.BKMFlagRefinement.refine_petz_error.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.BKMFlagRefinementPetz.TraceError.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v, z}⟩
  objectArena := .source ⟨arena.{u, v, z}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u, v, z} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.BKMFlagRefinementPetz
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end TraceError

namespace EntropyLoss

private abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected (role : Bool) : Realization signature :=
  realize signature (fun j _ x y => if j = role then False else x = y) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} {ι : Type v}
    [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
    {J : ι → Type z} [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]
    (S T : ι → Matrix n n ℂ) (hS : ∀ i, (S i).PosSemidef) (hT : ∀ i, (T i).PosDef)
    (w : ∀ i, J i → ℝ) (hw : ∀ i j, 0 < w i j) (hs : ∀ i, ∑ j, w i j = 1),
    R.readout false ()
      (relativeEntropyOfMatrices (joint (refinedBlocks w S)) (joint (refinedBlocks w T)))
      (relativeEntropyOfMatrices (joint S) (joint T)) ∧
    R.readout true ()
      (partialTraceEntropyLoss (refinedBlocks w S) (refinedBlocks w T))
      (partialTraceEntropyLoss S T)

private theorem rejected_law (role : Bool) : ¬ arena.{u, v, z}.Law (rejected role) := by
  intro h
  let S : ULift.{v} Unit → Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ := fun _ => 0
  let T : ULift.{v} Unit → Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ := fun _ => 1
  have result := h (J := fun _ => ULift.{z} Unit) S T
    (fun _ => Matrix.PosSemidef.zero) (fun _ => Matrix.PosDef.one)
    unitWeight.{v, z} (fun _ _ => zero_lt_one) unitWeight_sum
  cases role
  · simpa [rejected, realize] using result.1
  · simpa [rejected, realize] using result.2

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he : (1 : ℝ) = 0 := Eq.mp (congrFun h 0) rfl
  exact one_ne_zero he

def family : Registration arena.{u, v, z} (type_of% @refine_entropy_loss.{u, v, z}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@refine_entropy_loss.{u, v, z}, rejected false, rejected_law false⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected role, ?_, rfl, rejected_law role⟩
      intro j hj
      funext parameter x y
      simp [rejected, actual, realize, hj]
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@refine_entropy_loss.{u, v, z}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.BKMFlagRefinement.refine_entropy_loss.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.BKMFlagRefinementPetz.EntropyLoss.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v, z}⟩
  objectArena := .source ⟨arena.{u, v, z}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u, v, z} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.BKMFlagRefinementPetz
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "fn", "arg",
        "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "arg", "fn",
        "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end EntropyLoss

end Reg.D5.S3.Quantum.Recovery.BKMFlagRefinementPetz
