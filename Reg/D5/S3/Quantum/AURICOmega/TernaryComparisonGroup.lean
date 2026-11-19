import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
import Reg.Support.DependentFamily

/-! Source-bound audits of the transfer and reading theorems for ternary comparison structures. -/

namespace Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonGroup

open _root_.D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section
universe u

/-- First coordinate of the two-point indicator feature map. -/
def featureTrue (b : ULift.{u} Bool) : ℝ := if b.down then 1 else 0

/-- Second coordinate of the two-point indicator feature map. -/
def featureFalse (b : ULift.{u} Bool) : ℝ := if b.down then 0 else 1

/-- The two-point structure: transfer by exclusive or, reading by orthonormal indicators. -/
def twoPoint : TernaryComparison (ULift.{u} Bool) where
  tri x y z := ⟨xor (xor x.down y.down) z.down⟩
  kappa a b := featureTrue a * featureTrue b + featureFalse a * featureFalse b
  tri_self_left x z := by
    cases x with | up x => cases z with | up z => cases x <;> cases z <;> rfl
  tri_self_right x z := by
    cases x with | up x => cases z with | up z => cases x <;> cases z <;> rfl
  tri_assoc x y z u v := by
    cases x with | up x => cases y with | up y => cases z with | up z =>
    cases u with | up u => cases v with | up v =>
    cases x <;> cases y <;> cases z <;> cases u <;> cases v <;> rfl
  kappa_symm x y := by ring
  kappa_eq_one_iff x y := by
    cases x with | up x => cases y with | up y =>
    cases x <;> cases y <;> norm_num [featureTrue, featureFalse]
  kappa_nonneg x y := by
    cases x with | up x => cases y with | up y =>
    cases x <;> cases y <;> norm_num [featureTrue, featureFalse]
  kappa_tri_right x y u v := by
    cases x with | up x => cases y with | up y => cases u with | up u =>
    cases v with | up v =>
    cases x <;> cases y <;> cases u <;> cases v <;> norm_num [featureTrue, featureFalse]
  kappa_tri_left u v x y := by
    cases x with | up x => cases y with | up y => cases u with | up u =>
    cases v with | up v =>
    cases x <;> cases y <;> cases u <;> cases v <;> norm_num [featureTrue, featureFalse]
  kappa_gram_nonneg n x c := by
    have key : ∑ i, ∑ j, c i * c j *
        (featureTrue (x i) * featureTrue (x j) + featureFalse (x i) * featureFalse (x j)) =
        (∑ i, c i * featureTrue (x i)) * (∑ j, c j * featureTrue (x j)) +
          (∑ i, c i * featureFalse (x i)) * (∑ j, c j * featureFalse (x j)) := by
      rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [key]
    exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

theorem twoPoint_commutes : ¬ twoPoint.{u}.Noncommutative := by
  rintro ⟨x, y, z, h⟩
  apply h
  cases x with | up x => cases y with | up y => cases z with | up z =>
  cases x <;> cases y <;> cases z <;> rfl

/-! The reading against a fixed first argument, for `kappa_self`. -/
namespace Reading

abbrev signature : Signature where
  Params := Σ M : Type u, Σ _ : TernaryComparison M, M
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p s => p.2.1.kappa p.2.2 s) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} Bool, twoPoint, ⟨true⟩⟩, ⟨true⟩, ⟨false⟩, ?_⟩
  change twoPoint.kappa ⟨true⟩ ⟨true⟩ ≠ twoPoint.kappa ⟨true⟩ ⟨false⟩
  norm_num [twoPoint, featureTrue, featureFalse]

/-- Retain the complete carrier, structure and argument telescope of `kappa_self`. -/
abbrev diagonalArena : Arena where
  signature := signature.{u}
  Law r := ∀ {M : Type u} (C : TernaryComparison M) (x : M), r.readout () ⟨M, C, x⟩ x = 1

theorem diagonal_rejected : ¬ diagonalArena.{u}.Law rejected := by
  intro h
  have hh := h twoPoint.{u} ⟨true⟩
  norm_num [rejected, realize] at hh

def diagonal_registration :
    Registration diagonalArena.{u} (type_of% @TernaryComparison.kappa_self.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@TernaryComparison.kappa_self.{u}, rejected, diagonal_rejected⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, diagonal_rejected⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Reading

/-! The transfer against two fixed arguments, for `tri_eq_mul_inv_mul`. -/
namespace Transfer

abbrev signature : Signature where
  Params := Σ M : Type u, Σ _ : TernaryComparison M, Σ _ : M, M
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p s => p.2.1.tri p.2.2.1 p.2.2.2 s) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ s => s) (fun e => nomatch e)

/-- Retain the complete carrier, structure and argument telescope of `tri_eq_mul_inv_mul`. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {M : Type u} (C : TernaryComparison M) (o x y z : M),
    r.readout () ⟨M, C, x, y⟩ z = (letI := C.groupAt o; x * y⁻¹ * z)

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h twoPoint.{u} ⟨true⟩ ⟨true⟩ ⟨false⟩ ⟨true⟩
  revert hh
  decide

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  refine ⟨⟨ULift.{u} Bool, twoPoint, ⟨true⟩, ⟨true⟩⟩, ⟨true⟩, ⟨false⟩, ?_⟩
  decide

def source_registration :
    Registration arena.{u} (type_of% @TernaryComparison.tri_eq_mul_inv_mul.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@TernaryComparison.tri_eq_mul_inv_mul.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Transfer

/-! The base change from `o` to `o'`, for `baseChange_bijective`. -/
namespace BaseChange

abbrev signature : Signature where
  Params := Σ M : Type u, Σ _ : TernaryComparison M, Σ _ : M, M
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p s => p.2.1.tri s p.2.2.1 p.2.2.2) (fun e => nomatch e)

def constant : Realization signature.{u} :=
  realize signature (fun _ p _ => p.2.2.1) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  refine ⟨⟨ULift.{u} Bool, twoPoint, ⟨true⟩, ⟨true⟩⟩, ⟨true⟩, ⟨false⟩, ?_⟩
  decide

/-- Retain the complete carrier, structure and base-point telescope of `baseChange_bijective`. -/
abbrev bijectiveArena : Arena where
  signature := signature.{u}
  Law r := ∀ {M : Type u} (C : TernaryComparison M) (o o' : M),
    Function.Bijective (fun x : M => r.readout () ⟨M, C, o, o'⟩ x)

theorem bijective_rejected : ¬ bijectiveArena.{u}.Law constant := by
  intro h
  have hh := (h twoPoint.{u} ⟨true⟩ ⟨true⟩).1 (a₁ := ⟨true⟩) (a₂ := ⟨false⟩) rfl
  exact absurd hh (by decide)

def bijective_registration :
    Registration bijectiveArena.{u} (type_of% @TernaryComparison.baseChange_bijective.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@TernaryComparison.baseChange_bijective.{u}, constant, bijective_rejected⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨constant, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, bijective_rejected⟩
    · intro e
      exact nomatch e
  dependence := dependence

end BaseChange

/-! The product through a fixed base point, for `noncommutative_iff`. -/
namespace Order

abbrev signature : Signature where
  Params := Σ M : Type u, Σ _ : TernaryComparison M, Σ _ : M, M
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p s => p.2.1.tri p.2.2.2 p.2.2.1 s) (fun e => nomatch e)

def constant : Realization signature.{u} :=
  realize signature (fun _ p _ => p.2.2.1) (fun e => nomatch e)

/-- Retain the complete carrier, structure and base-point telescope of `noncommutative_iff`. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {M : Type u} (C : TernaryComparison M) (o : M),
    C.Noncommutative ↔ ∃ x y : M, r.readout () ⟨M, C, o, x⟩ y ≠ C.tri y o x

theorem rejected_law : ¬ arena.{u}.Law constant := by
  intro h
  apply twoPoint_commutes.{u}
  refine (h twoPoint.{u} ⟨true⟩).2 ⟨⟨true⟩, ⟨false⟩, ?_⟩
  decide

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  refine ⟨⟨ULift.{u} Bool, twoPoint, ⟨true⟩, ⟨true⟩⟩, ⟨true⟩, ⟨false⟩, ?_⟩
  decide

def source_registration :
    Registration arena.{u} (type_of% @TernaryComparison.noncommutative_iff.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@TernaryComparison.noncommutative_iff.{u}, constant, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨constant, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Order

def kappa_self_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@TernaryComparison.kappa_self.{u}) (Realization Reading.signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonGroup.kappa_self_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonGroup.Reading.diagonal_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Reading.diagonalArena.{u}⟩
  objectArena := .source ⟨Reading.diagonalArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Reading.diagonalArena.{u} ⟨Reading.diagonal_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize Reading.signature.{u} (fun _ p s => p.2.1.kappa p.2.2 s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def tri_eq_mul_inv_mul_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@TernaryComparison.tri_eq_mul_inv_mul.{u}) (Realization Transfer.signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonGroup.tri_eq_mul_inv_mul_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonGroup.Transfer.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Transfer.arena.{u}⟩
  objectArena := .source ⟨Transfer.arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Transfer.arena.{u} ⟨Transfer.source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize Transfer.signature.{u} (fun _ p s => p.2.1.tri p.2.2.1 p.2.2.2 s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
    definition := none
    coordinates := #[0, 1, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def baseChange_bijective_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@TernaryComparison.baseChange_bijective.{u}) (Realization BaseChange.signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonGroup.baseChange_bijective_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonGroup.BaseChange.bijective_registration
  realizationSource := none
  generated := false
  arena := .source ⟨BaseChange.bijectiveArena.{u}⟩
  objectArena := .source ⟨BaseChange.bijectiveArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source BaseChange.bijectiveArena.{u} ⟨BaseChange.bijective_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize BaseChange.signature.{u} (fun _ p s => p.2.1.tri s p.2.2.1 p.2.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def noncommutative_iff_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@TernaryComparison.noncommutative_iff.{u}) (Realization Order.signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonGroup.noncommutative_iff_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonGroup.Order.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Order.arena.{u}⟩
  objectArena := .source ⟨Order.arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Order.arena.{u} ⟨Order.source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize Order.signature.{u} (fun _ p s => p.2.1.tri p.2.2.2 p.2.2.1 s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "body", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
