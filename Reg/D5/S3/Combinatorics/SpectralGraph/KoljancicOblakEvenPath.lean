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

/-- Both entire branch sequences, the central loop, and both lengths remain parameters. -/
abbrev joinedSignature : DependentFamily.Signature where
  Params := ((ℕ → ℝ) × (ℕ → ℝ)) × (ℝ × ℕ × ℕ)
  State := fun _ => ℝ × (ℕ → ℝ) × (ℕ → ℝ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ[X]
  Anchor := Empty
  finiteAnchor := inferInstance

def joinedActual : DependentFamily.Realization joinedSignature :=
  DependentFamily.realize joinedSignature
    (fun _ p d => (deformedJoinedContinuant p.1.1 p.1.2 d.2.1 d.2.2 p.2.1 d.1 p.2.2.1 p.2.2.2).coeff 1)
    (fun e => nomatch e)

abbrev joinedArena : DependentFamily.Arena where
  signature := joinedSignature
  Law := fun R => ∀ (qL qR dqL dqR : ℕ → ℝ) (a da : ℝ) (r s : ℕ),
    a ≠ 0 → Odd (r + s) → (∀ k < r, qL k ≠ 0) → (∀ k < s, qR k ≠ 0) →
    IsCoprime (continuant qL r) (continuant qR s) →
    R.readout () ((qL, qR), (a, r, s)) (da, dqL, dqR) = 0 →
    da = 0 ∧ (∀ k < r, dqL k = 0) ∧ (∀ k < s, dqR k = 0)

abbrev joinedSourceScope := type_of% (@joined_variation_injective)

lemma joined_source_bridge : joinedSourceScope ↔ joinedArena.Law joinedActual := Iff.rfl

lemma joined_actual_positive : joinedArena.Law joinedActual :=
  joined_source_bridge.mp joined_variation_injective

def joinedRejected : DependentFamily.Realization joinedSignature :=
  DependentFamily.realize joinedSignature (fun _ _ _ => 0) (fun e => nomatch e)

lemma joined_rejected_law : ¬ joinedArena.Law joinedRejected := by
  intro h
  have hc := h (fun _ => 1) (fun _ => 1) (fun _ => 0) (fun _ => 0) 1 1 0 1
    (by norm_num) (by decide) (by intro k hk; omega)
    (by intro k hk; norm_num) (by simp [continuant, isCoprime_one_left]) rfl
  norm_num at hc

lemma joined_dependence :
    DependentFamily.ObservationalDependence joinedSignature joinedActual := by
  intro role
  cases role
  refine ⟨(((fun _ => 1), (fun _ => 1)), (1, 0, 1)),
    (1, (fun _ => 0), (fun _ => 0)), (0, (fun _ => 0), (fun _ => 0)), ?_⟩
  simp [joinedActual, DependentFamily.realize, deformedJoinedContinuant,
    deformedContinuant, mul_coeff_one]

def joinedFamilyRegistration : DependentFamily.Registration joinedArena joinedSourceScope where
  actual := joinedActual
  bridge := joined_source_bridge
  variation := ⟨joined_actual_positive, joinedRejected, joined_rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨joinedRejected, ?_, rfl, joined_rejected_law⟩
      intro index hne
      exact (hne (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := joined_dependence

def joinedRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@joined_variation_injective) (DependentFamily.Realization joinedSignature) Type Unit where
  unitName := `D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath.joined_variation_injective.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath.joinedFamilyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨joinedArena⟩
  objectArena := .source ⟨joinedArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source joinedArena ⟨joinedFamilyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize joinedSignature
    (fun _ p d => (deformedJoinedContinuant p.1.1 p.1.2 d.2.1 d.2.2 p.2.1 d.1 p.2.2.1 p.2.2.2).coeff 1)
    (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := some (ℝ × (ℕ → ℝ) × (ℕ → ℝ))
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev coprimeSignature : DependentFamily.Signature where
  Params := ℕ × ℕ
  State := fun _ => (ℕ → ℝ) × (ℕ → ℝ)
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ[X]
  Anchor := Empty
  finiteAnchor := inferInstance

def coprimeActual : DependentFamily.Realization coprimeSignature :=
  DependentFamily.realize coprimeSignature
    (fun role p q => if role then continuant q.2 p.2 else continuant q.1 p.1)
    (fun e => nomatch e)

abbrev coprimeArena : DependentFamily.Arena where
  signature := coprimeSignature
  Law := fun R => ∀ r s : ℕ, Odd (r + s) →
    ∃ qL qR : ℕ → ℝ, (∀ k, 0 < qL k) ∧ (∀ k, 0 < qR k) ∧
      IsCoprime (R.readout false (r, s) (qL, qR)) (R.readout true (r, s) (qL, qR))

abbrev coprimeSourceScope := type_of% (@coprime_positive_branches)

lemma coprime_source_bridge : coprimeSourceScope ↔ coprimeArena.Law coprimeActual := Iff.rfl

lemma coprime_actual_positive : coprimeArena.Law coprimeActual :=
  coprime_source_bridge.mp coprime_positive_branches

def coprimeRejected (role : Bool) : DependentFamily.Realization coprimeSignature :=
  DependentFamily.realize coprimeSignature
    (fun index p q => if index = role then 0 else coprimeActual.readout index p q)
    (fun e => nomatch e)

lemma coprime_rejected_law (role : Bool) : ¬ coprimeArena.Law (coprimeRejected role) := by
  intro h
  obtain ⟨qL, qR, _, _, hc⟩ := h 2 1 (by decide)
  cases role with
  | false =>
      change IsCoprime (0 : ℝ[X]) (continuant qR 1) at hc
      have hu := isCoprime_zero_left.mp hc
      have hc1 := coeff_eq_zero_of_natDegree_lt (p := continuant qR 1)
        (show (continuant qR 1).natDegree < 1 by rw [natDegree_eq_zero_of_isUnit hu]; omega)
      norm_num [continuant] at hc1
  | true =>
      change IsCoprime (continuant qL 2) (0 : ℝ[X]) at hc
      have hu := isCoprime_zero_right.mp hc
      have hc2 := coeff_eq_zero_of_natDegree_lt (p := continuant qL 2)
        (show (continuant qL 2).natDegree < 2 by rw [natDegree_eq_zero_of_isUnit hu]; omega)
      norm_num [continuant] at hc2

lemma coprime_dependence :
    DependentFamily.ObservationalDependence coprimeSignature coprimeActual := by
  intro role
  refine ⟨(2, 2), ((fun _ => 1), (fun _ => 1)), ((fun _ => 0), (fun _ => 0)), ?_⟩
  cases role <;> simp [coprimeActual, DependentFamily.realize, continuant]

def coprimeFamilyRegistration : DependentFamily.Registration coprimeArena coprimeSourceScope where
  actual := coprimeActual
  bridge := coprime_source_bridge
  variation := ⟨coprime_actual_positive, coprimeRejected false, coprime_rejected_law false⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨coprimeRejected role, ?_, rfl, coprime_rejected_law role⟩
      intro index hne
      funext p q
      simp [coprimeRejected, DependentFamily.realize, hne]
    · intro e; exact nomatch e
  dependence := coprime_dependence

def coprimeRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@coprime_positive_branches) (DependentFamily.Realization coprimeSignature) Type Unit where
  unitName := `D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath.coprime_positive_branches.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath.coprimeFamilyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨coprimeArena⟩
  objectArena := .source ⟨coprimeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source coprimeArena ⟨coprimeFamilyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize coprimeSignature
    (fun role p q => if role then continuant q.2 p.2 else continuant q.1 p.1)
    (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := some ((ℕ → ℝ) × (ℕ → ℝ))
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev joinedMatrixSignature : DependentFamily.Signature where
  Params := ℕ × ℕ
  State := fun _ => (ℕ → ℝ) × (ℕ → ℝ) × ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ[X]
  Anchor := Empty
  finiteAnchor := inferInstance

def joinedMatrixActual : DependentFamily.Realization joinedMatrixSignature :=
  DependentFamily.realize joinedMatrixSignature
    (fun _ p b => (joinedPath b.1 b.2.1 b.2.2 p.1 p.2).charpoly)
    (fun e => nomatch e)

abbrev joinedMatrixArena : DependentFamily.Arena where
  signature := joinedMatrixSignature
  Law := fun R => ∀ (bL bR : ℕ → ℝ) (a : ℝ) (r s : ℕ),
    R.readout () (r, s) (bL, bR, a) =
      continuant (fun k => bL k ^ 2) (r + 1) * continuant (fun k => bR k ^ 2) s +
      continuant (fun k => bL k ^ 2) r * continuant (fun k => bR k ^ 2) (s + 1) -
      (X + C a) * continuant (fun k => bL k ^ 2) r * continuant (fun k => bR k ^ 2) s

abbrev joinedMatrixSourceScope := type_of% (@joined_path_charpoly)

lemma joinedMatrix_source_bridge :
    joinedMatrixSourceScope ↔ joinedMatrixArena.Law joinedMatrixActual := Iff.rfl

lemma joinedMatrix_actual_positive : joinedMatrixArena.Law joinedMatrixActual :=
  joinedMatrix_source_bridge.mp joined_path_charpoly

def joinedMatrixRejected : DependentFamily.Realization joinedMatrixSignature :=
  DependentFamily.realize joinedMatrixSignature
    (fun role p b => joinedMatrixActual.readout role p b + 1) (fun e => nomatch e)

lemma joinedMatrix_rejected_law : ¬ joinedMatrixArena.Law joinedMatrixRejected := by
  intro h
  have he := h (fun _ => 0) (fun _ => 0) 0 0 0
  have hp := joinedMatrix_actual_positive (fun _ => 0) (fun _ => 0) 0 0 0
  change joinedMatrixActual.readout () (0, 0)
    ((fun _ => 0), (fun _ => 0), (0 : ℝ)) + 1 = _ at he
  rw [hp] at he
  have hz : (1 : ℝ[X]) = 0 := by
    linear_combination he
  exact one_ne_zero hz

lemma joinedMatrix_dependence :
    DependentFamily.ObservationalDependence joinedMatrixSignature joinedMatrixActual := by
  intro role
  refine ⟨(0, 0), ((fun _ => 0), (fun _ => 0), 0),
    ((fun _ => 0), (fun _ => 0), 1), ?_⟩
  intro he
  have hc := congrArg (fun p : ℝ[X] => p.coeff 0) he
  norm_num [joinedMatrixActual, DependentFamily.realize, joined_path_charpoly, continuant, coeff_add] at hc

def joinedMatrixFamilyRegistration :
    DependentFamily.Registration joinedMatrixArena joinedMatrixSourceScope where
  actual := joinedMatrixActual
  bridge := joinedMatrix_source_bridge
  variation := ⟨joinedMatrix_actual_positive, joinedMatrixRejected, joinedMatrix_rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨joinedMatrixRejected, ?_, rfl, joinedMatrix_rejected_law⟩
      intro index hne
      exact False.elim (hne (Subsingleton.elim _ _))
    · intro e; exact nomatch e
  dependence := joinedMatrix_dependence

def joinedMatrixRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@joined_path_charpoly) (DependentFamily.Realization joinedMatrixSignature) Type Unit where
  unitName := `D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath.joined_path_charpoly.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath.joinedMatrixFamilyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨joinedMatrixArena⟩
  objectArena := .source ⟨joinedMatrixArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source joinedMatrixArena ⟨joinedMatrixFamilyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize joinedMatrixSignature
    (fun _ p b => (joinedPath b.1 b.2.1 b.2.2 p.1 p.2).charpoly) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := some ((ℕ → ℝ) × (ℕ → ℝ) × ℝ)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

structure TangentParams where
  bL : ℕ → ℝ
  bR : ℕ → ℝ
  dbL : ℕ → ℝ
  dbR : ℕ → ℝ
  a : ℝ
  da : ℝ
  r : ℕ
  s : ℕ
  x : ℝ

abbrev tangentSignature : DependentFamily.Signature where
  Params := TangentParams
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def tangentActual : DependentFamily.Realization tangentSignature :=
  DependentFamily.realize tangentSignature
    (fun _ p t => ((joinedPath (fun k => p.bL k + t * p.dbL k)
      (fun k => p.bR k + t * p.dbR k) (p.a + t * p.da) p.r p.s).charpoly).eval p.x)
    (fun e => nomatch e)

abbrev tangentArena : DependentFamily.Arena where
  signature := tangentSignature
  Law := fun R => ∀ (bL bR dbL dbR : ℕ → ℝ) (a da : ℝ) (r s : ℕ) (x : ℝ),
    HasDerivAt (fun t : ℝ => R.readout () ⟨bL, bR, dbL, dbR, a, da, r, s, x⟩ t)
      ((joinedVariation (fun k => bL k ^ 2) (fun k => bR k ^ 2)
        (fun k => 2 * bL k * dbL k) (fun k => 2 * bR k * dbR k) a da r s).eval x) 0

abbrev tangentSourceScope := type_of% (@joined_path_charpoly_derivative)

lemma tangent_source_bridge : tangentSourceScope ↔ tangentArena.Law tangentActual := Iff.rfl

lemma tangent_actual_positive : tangentArena.Law tangentActual :=
  tangent_source_bridge.mp joined_path_charpoly_derivative

def tangentRejected : DependentFamily.Realization tangentSignature :=
  DependentFamily.realize tangentSignature (fun _ _ _ => 0) (fun e => nomatch e)

lemma tangent_rejected_law : ¬ tangentArena.Law tangentRejected := by
  intro h
  have he := h (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) 0 1 0 0 0
  change HasDerivAt (fun _ : ℝ => 0) _ 0 at he
  have hc := he.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  norm_num [joinedVariation, continuant, variation] at hc

lemma tangent_dependence :
    DependentFamily.ObservationalDependence tangentSignature tangentActual := by
  intro role
  refine ⟨⟨(fun _ => 0), (fun _ => 0), (fun _ => 0), (fun _ => 0), 0, 1, 0, 0, 0⟩,
    0, 1, ?_⟩
  norm_num [tangentActual, DependentFamily.realize, joined_path_charpoly, continuant]

def tangentFamilyRegistration : DependentFamily.Registration tangentArena tangentSourceScope where
  actual := tangentActual
  bridge := tangent_source_bridge
  variation := ⟨tangent_actual_positive, tangentRejected, tangent_rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨tangentRejected, ?_, rfl, tangent_rejected_law⟩
      intro index hne
      exact False.elim (hne (Subsingleton.elim _ _))
    · intro e; exact nomatch e
  dependence := tangent_dependence

def tangentRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@joined_path_charpoly_derivative) (DependentFamily.Realization tangentSignature) Type Unit where
  unitName := `D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath.joined_path_charpoly_derivative.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath.tangentFamilyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨tangentArena⟩
  objectArena := .source ⟨tangentArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source tangentArena ⟨tangentFamilyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize tangentSignature
    (fun _ p t => ((joinedPath (fun k => p.bL k + t * p.dbL k)
      (fun k => p.bR k + t * p.dbR k) (p.a + t * p.da) p.r p.s).charpoly).eval p.x)
    (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath
