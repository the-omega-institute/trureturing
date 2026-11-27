import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.CompleteHockeyStickChoiConverse

/-! Source-bound readouts for the replacement weight and the strict contraction criterion. -/

set_option autoImplicit false

noncomputable section

open Matrix LeanInformationAudit
open scoped CStarAlgebra ComplexOrder MatrixOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState QuantumChannel)
open _root_.D5.S3.Quantum.Foundation.FiniteDiamondDistance (IsPure)
open _root_.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (act)
open _root_.D5.S3.Quantum.Divergence.CompleteHockeyStickRefutation (completeCoefficient)
open _root_.D5.S3.Quantum.Divergence.CompleteHockeyStickChoiConverse
open UnitaryReconstruction.LiuWildChoiObstruction
  (normalizedChoi normalizedChoi_entry pairMatrix)

namespace Reg.D5.S3.Quantum.Divergence.CompleteHockeyStickChoiConverse

universe u

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h := congrFun he 1
  change ((0 : ℝ) < 1) = ((1 : ℝ) < 1) at h
  exact (lt_irrefl (1 : ℝ)) (h.mp zero_lt_one)

private def singletonIdentity (α : Type u) [Fintype α] [DecidableEq α] : QuantumChannel α α where
  toCompletelyPositiveMap :=
    { toLinearMap := LinearMap.id
      map_cstarMatrix_nonneg' := fun _ _ h => h }
  trace_preserving _ := rfl

private theorem singleton_support (α : Type u)
    [Fintype α] [DecidableEq α] [Unique α] (i : α) :
    (fun z : α × α => if z.1 = i then (1 : ℂ) else 0) ∈
      (pairMatrix (normalizedChoi (singletonIdentity α))).mulVecLin.range := by
  have hJ : pairMatrix (normalizedChoi (singletonIdentity α)) = 1 := by
    ext ⟨a, b⟩ ⟨c, d⟩
    rw [normalizedChoi_entry]
    have ha : a = c := Subsingleton.elim _ _
    have hb : b = a := Subsingleton.elim _ _
    have hd : d = a := Subsingleton.elim _ _
    subst c
    subst b
    subst d
    change (Fintype.card α : ℂ)⁻¹ * Matrix.single a a (1 : ℂ) a a = (1 : Matrix _ _ ℂ) _ _
    simp
  rw [hJ]
  refine ⟨1, ?_⟩
  change (1 : Matrix (α × α) (α × α) ℂ) *ᵥ 1 = _
  rw [Matrix.one_mulVec]
  funext z
  simp [Subsingleton.elim z.1 i]

private theorem singleton_vector_ne_zero (α : Type u) [Inhabited α] :
    (fun _ : α => (1 : ℂ)) ≠ 0 := by
  intro h
  exact one_ne_zero (congrFun h default)

namespace Replacement

private def rejected : Realization signature :=
  realize signature (fun _ _ _ p => 1 < p) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] (N : QuantumChannel A B)
      (v : B → ℂ) (_hv : v ≠ 0)
      (_hSupport : ∀ i : A, (fun z : A × B => if z.1 = i then v z.2 else 0) ∈
        (pairMatrix (normalizedChoi N)).mulVecLin.range),
    ∃ (p : ℝ) (τ : DensityState B) (M : QuantumChannel A B),
      R.readout () () 0 p ∧ p < 1 ∧ IsPure τ ∧
        ∀ Z : Matrix A A ℂ, act N Z = (1 - p) • act M Z + p • (Z.trace • pairMatrix τ)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨p, _, _, hlower, hupper, _⟩ :=
    h (singletonIdentity (ULift.{u} Unit)) (fun _ => 1)
      (singleton_vector_ne_zero _) (singleton_support _)
  exact (lt_irrefl p) (hupper.trans hlower)

def family : Registration arena.{u} (type_of% @exists_replacement_of_choi_support.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_replacement_of_choi_support.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_replacement_of_choi_support.{u}) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Divergence.CompleteHockeyStickChoiConverse.exists_replacement_of_choi_support.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.CompleteHockeyStickChoiConverse.Replacement.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.CompleteHockeyStickChoiConverse
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "body", "arg", "body", "arg", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Replacement

private def saturating : Realization signature :=
  realize signature (fun _ _ x y => y ≤ x) (fun e => nomatch e)

namespace SupportBound

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {A B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] (N : QuantumChannel A B) (γ : ℝ) (_hγ : 1 ≤ γ)
      (v : B → ℂ) (_hv : v ≠ 0)
      (_hSupport : ∀ i : A, (fun z : A × B => if z.1 = i then v z.2 else 0) ∈
        (pairMatrix (normalizedChoi N)).mulVecLin.range),
    R.readout () () (completeCoefficient N γ false) 1

private theorem rejected_law : ¬ arena.Law saturating := by
  intro h
  let N := singletonIdentity Unit
  have hlt := coefficient_lt_one_of_choi_support N 1 le_rfl (fun _ => 1)
    (singleton_vector_ne_zero _) (singleton_support _)
  exact (not_le.mpr hlt) (h N 1 le_rfl (fun _ => 1)
    (singleton_vector_ne_zero _) (singleton_support _))

def family : Registration arena (type_of% @coefficient_lt_one_of_choi_support) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@coefficient_lt_one_of_choi_support, saturating, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual saturating rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@coefficient_lt_one_of_choi_support) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Divergence.CompleteHockeyStickChoiConverse.coefficient_lt_one_of_choi_support.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.CompleteHockeyStickChoiConverse.SupportBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.CompleteHockeyStickChoiConverse
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SupportBound

namespace Criterion

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {A B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] (N : QuantumChannel A B) (γ : ℝ) (_hγ : 1 < γ),
    R.readout () () (completeCoefficient N γ false) 1 ↔
      ∃ v : B → ℂ, v ≠ 0 ∧ ∀ i : A, (fun z : A × B => if z.1 = i then v z.2 else 0) ∈
        (pairMatrix (normalizedChoi N)).mulVecLin.range

private theorem rejected_law : ¬ arena.Law saturating := by
  intro h
  let N := singletonIdentity Unit
  have hlt := coefficient_lt_one_of_choi_support N 2 (by norm_num) (fun _ => 1)
    (singleton_vector_ne_zero _) (singleton_support _)
  exact (not_le.mpr hlt) ((h N 2 (by norm_num)).mpr
    ⟨fun _ => 1, singleton_vector_ne_zero _, singleton_support _⟩)

def family : Registration arena (type_of% @coefficient_lt_one_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@coefficient_lt_one_iff, saturating, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual saturating rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@coefficient_lt_one_iff) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Divergence.CompleteHockeyStickChoiConverse.coefficient_lt_one_iff.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.CompleteHockeyStickChoiConverse.Criterion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.CompleteHockeyStickChoiConverse
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Criterion

#print axioms exists_replacement_of_choi_support
#print axioms coefficient_lt_one_of_choi_support
#print axioms coefficient_lt_one_iff
#print axioms Replacement.audit
#print axioms SupportBound.audit
#print axioms Criterion.audit

end Reg.D5.S3.Quantum.Divergence.CompleteHockeyStickChoiConverse
