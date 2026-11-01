import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath

/-! Source-owner families for branch characteristic and variation observations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath
open _root_.D5.S3.ConceptDynamics.InformationEscape
open Polynomial

attribute [local simp] Polynomial.coeff_one

/-- Parameters retain the whole edge sequence and every branch length. -/
abbrev signature : DependentFamily.Signature where
  Params := (ℕ → ℝ) × ℕ
  State := fun _ => ℕ → ℝ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ[X]
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature
    (fun role p dq => variation p.1 dq (p.2 + if role then 1 else 0))
    (fun e => nomatch e)

abbrev arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ (q dq : ℕ → ℝ) (n : ℕ),
    (∀ k < n, q k ≠ 0) →
    R.readout false (q, n) dq = 0 → R.readout true (q, n) dq = 0 →
    ∀ k < n, dq k = 0

abbrev sourceScope := type_of% (@branch_variation_injective)

lemma source_bridge : sourceScope ↔ arena.Law actual := by
  rfl

lemma actual_positive : arena.Law actual :=
  source_bridge.mp branch_variation_injective

def rejected (role : Bool) : DependentFamily.Realization signature :=
  DependentFamily.realize signature
    (fun index p dq => if index = role then 0 else actual.readout index p dq)
    (fun e => nomatch e)

lemma rejected_law (role : Bool) : ¬ arena.Law (rejected role) := by
  cases role with
  | false =>
      intro h
      let dq : ℕ → ℝ := fun k => if k = 0 then 1 else -1
      have hz : variation (fun _ => 1) dq 3 = 0 := by
        simp [variation, continuant, dq]
      have hc := h (fun _ => 1) dq 2 (by intro k hk; norm_num)
        (by simp [rejected, DependentFamily.realize])
        (by simpa [rejected, actual, DependentFamily.realize] using hz)
        0 (by omega)
      norm_num [dq] at hc
  | true =>
      intro h
      have hc := h (fun _ => 1) (fun _ => 1) 1 (by intro k hk; norm_num)
        (by simp [rejected, actual, DependentFamily.realize, variation])
        (by simp [rejected, DependentFamily.realize]) 0 (by omega)
      norm_num at hc

lemma dependence : DependentFamily.ObservationalDependence signature actual := by
  intro role
  cases role with
  | false =>
      refine ⟨((fun _ => 1), 2), (fun _ => 1), (fun _ => 0), ?_⟩
      norm_num [actual, DependentFamily.realize, variation, continuant]
  | true =>
      refine ⟨((fun _ => 1), 1), (fun _ => 1), (fun _ => 0), ?_⟩
      norm_num [actual, DependentFamily.realize, variation, continuant]

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected false, rejected_law false⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected role, ?_, rfl, rejected_law role⟩
      intro index hne
      funext p dq
      simp [rejected, DependentFamily.realize, hne]
    · intro e; exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@branch_variation_injective) (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath.branch_variation_injective.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature
    (fun role p dq => variation p.1 dq (p.2 + if role then 1 else 0))
    (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := some (ℕ → ℝ)
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev matrixSignature : DependentFamily.Signature where
  Params := ℕ
  State := fun _ => ℕ → ℝ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ[X]
  Anchor := Empty
  finiteAnchor := inferInstance

def matrixActual : DependentFamily.Realization matrixSignature :=
  DependentFamily.realize matrixSignature
    (fun role n b => if role then continuant b n else (weightedPath b n).charpoly)
    (fun e => nomatch e)

abbrev matrixArena : DependentFamily.Arena where
  signature := matrixSignature
  Law := fun R => ∀ (b : ℕ → ℝ) (n : ℕ),
    R.readout false n b = R.readout true n (fun k => b k ^ 2)

abbrev matrixSourceScope := type_of% (@weighted_path_charpoly)

lemma matrix_source_bridge : matrixSourceScope ↔ matrixArena.Law matrixActual := Iff.rfl

lemma matrix_actual_positive : matrixArena.Law matrixActual :=
  matrix_source_bridge.mp weighted_path_charpoly

def matrixRejected (role : Bool) : DependentFamily.Realization matrixSignature :=
  DependentFamily.realize matrixSignature
    (fun index n b => matrixActual.readout index n b + if index = role then 1 else 0)
    (fun e => nomatch e)

lemma matrix_rejected_law (role : Bool) : ¬ matrixArena.Law (matrixRejected role) := by
  intro h
  have he := h (fun _ => 0) 0
  cases role <;>
    norm_num [matrixRejected, matrixActual, DependentFamily.realize, continuant,
      Matrix.charpoly_isEmpty] at he

lemma matrix_dependence :
    DependentFamily.ObservationalDependence matrixSignature matrixActual := by
  intro role
  refine ⟨2, (fun _ => 1), (fun _ => 0), ?_⟩
  cases role <;>
    simp [matrixActual, DependentFamily.realize, weighted_path_charpoly, continuant]

def matrixFamilyRegistration : DependentFamily.Registration matrixArena matrixSourceScope where
  actual := matrixActual
  bridge := matrix_source_bridge
  variation := ⟨matrix_actual_positive, matrixRejected false, matrix_rejected_law false⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨matrixRejected role, ?_, rfl, matrix_rejected_law role⟩
      intro index hne
      funext n b
      simp [matrixRejected, DependentFamily.realize, hne]
    · intro e; exact nomatch e
  dependence := matrix_dependence

def matrixRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@weighted_path_charpoly) (DependentFamily.Realization matrixSignature) Type Unit where
  unitName := `D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath.weighted_path_charpoly.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath.matrixFamilyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨matrixArena⟩
  objectArena := .source ⟨matrixArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source matrixArena ⟨matrixFamilyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize matrixSignature
    (fun role n b => if role then continuant b n else (weightedPath b n).charpoly)
    (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := some (ℕ → ℝ)
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "fn", "arg"]
      booleanPredicate := false }, {
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev linearizationSignature : DependentFamily.Signature where
  Params := (ℕ → ℝ) × (ℕ → ℝ)
  State := fun _ => ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ[X]
  Anchor := Empty
  finiteAnchor := inferInstance

def linearizationActual : DependentFamily.Realization linearizationSignature :=
  DependentFamily.realize linearizationSignature
    (fun role p n => (deformedContinuant p.1 p.2 n).coeff (if role then 1 else 0))
    (fun e => nomatch e)

abbrev linearizationArena : DependentFamily.Arena where
  signature := linearizationSignature
  Law := fun R => ∀ (q dq : ℕ → ℝ) (n : ℕ),
    R.readout false (q, dq) n = continuant q n ∧
    R.readout true (q, dq) n = variation q dq n

abbrev linearizationSourceScope := type_of% (@continuant_linearization)

lemma linearization_source_bridge :
    linearizationSourceScope ↔ linearizationArena.Law linearizationActual := Iff.rfl

lemma linearization_actual_positive : linearizationArena.Law linearizationActual :=
  linearization_source_bridge.mp continuant_linearization

def linearizationRejected (role : Bool) : DependentFamily.Realization linearizationSignature :=
  DependentFamily.realize linearizationSignature
    (fun index p n => linearizationActual.readout index p n + if index = role then 1 else 0)
    (fun e => nomatch e)

lemma linearization_rejected_law (role : Bool) :
    ¬ linearizationArena.Law (linearizationRejected role) := by
  intro h
  have he := h (fun _ => 0) (fun _ => 0) 0
  cases role <;>
    norm_num [linearizationRejected, linearizationActual, DependentFamily.realize,
      deformedContinuant, continuant, variation] at he

lemma linearization_dependence :
    DependentFamily.ObservationalDependence linearizationSignature linearizationActual := by
  intro role
  cases role with
  | false =>
      refine ⟨((fun _ => 1), (fun _ => 1)), 0, 1, ?_⟩
      intro he
      have hc := congrArg (fun p : ℝ[X] => p.coeff 0) he
      norm_num [linearizationActual, DependentFamily.realize, deformedContinuant] at hc
  | true =>
      refine ⟨((fun _ => 1), (fun _ => 1)), 0, 2, ?_⟩
      norm_num [linearizationActual, DependentFamily.realize, deformedContinuant,
        mul_coeff_one]

def linearizationFamilyRegistration :
    DependentFamily.Registration linearizationArena linearizationSourceScope where
  actual := linearizationActual
  bridge := linearization_source_bridge
  variation := ⟨linearization_actual_positive, linearizationRejected false,
    linearization_rejected_law false⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨linearizationRejected role, ?_, rfl, linearization_rejected_law role⟩
      intro index hne
      funext p n
      simp [linearizationRejected, DependentFamily.realize, hne]
    · intro e; exact nomatch e
  dependence := linearization_dependence

def linearizationRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@continuant_linearization) (DependentFamily.Realization linearizationSignature) Type Unit where
  unitName := `D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath.continuant_linearization.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath.linearizationFamilyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨linearizationArena⟩
  objectArena := .source ⟨linearizationArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source linearizationArena ⟨linearizationFamilyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize linearizationSignature
    (fun role p n => (deformedContinuant p.1 p.2 n).coeff (if role then 1 else 0))
    (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "arg"]
      booleanPredicate := false }, {
      path := #["body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath
