import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.NumericalSemigroup.SignedResidueRelation

/-! Source-bound audits of the nonzero exponents and reduced polynomial. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.NumericalSemigroup.SignedResidueRelation
open scoped BigOperators

namespace Reg.D5.S3.Combinatorics.NumericalSemigroup.SignedResidueRelation

private theorem two_vectors : 1 < (signedVectors 1 1).card := by
  classical
  apply Finset.one_lt_card.mpr
  refine ⟨(fun _ => 0), ?_, (fun _ => 1), ?_, ?_⟩
  · norm_num [signedVectors, Fintype.mem_piFinset, positiveMass, negativeMass]
  · norm_num [signedVectors, Fintype.mem_piFinset, positiveMass, negativeMass]
  · intro h
    have := congrFun h 0
    norm_num at this

namespace Exponents

abbrev signature : Signature where
  Params := ℕ
  State e := Fin e → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ e := (Fin e → ℕ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ a b => a ≠ b) (fun x => nomatch x)
def rejected : Realization signature := realize signature
  (fun _ _ _ _ => False) (fun x => nomatch x)

def arena : Arena where
  signature := signature
  Law R := ∀ (e q m : ℕ) (_ : 0 < m) (g : Fin e → ℕ)
    (_ : m < (signedVectors e q).card),
    ∃ a b : Fin e → ℕ, R.readout () e a b ∧ (∀ i, a i = 0 ∨ b i = 0) ∧
      (∑ i, a i) ≤ 2 * q ∧ (∑ i, b i) ≤ 2 * q ∧
      (∑ i, a i * g i) ≡ (∑ i, b i * g i) [MOD m]

private theorem bad : ¬ arena.Law rejected := by
  intro h
  obtain ⟨a, b, hn, _⟩ := h 1 1 1 (by omega) (fun _ => 1) two_vectors
  exact hn

def family : Registration arena (type_of% @bounded_residue_relation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨bounded_residue_relation, rejected, bad⟩
  sensitivity := by
    constructor
    · intro i
      change Unit at i
      refine ⟨rejected, ?_, rfl, bad⟩
      intro j hj
      change Unit at j
      exact (hj (by cases j; cases i; rfl)).elim
    · intro i
      exact nomatch i
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
    intro h
    change (fun b : Fin 1 → ℕ => (fun _ => 0) ≠ b) =
      (fun b : Fin 1 → ℕ => (fun _ => 1) ≠ b) at h
    have hn : (fun _ : Fin 1 => 1) ≠ (fun _ => 0) := by
      intro hh
      have := congrFun hh 0
      norm_num at this
    exact (Eq.mpr (congrFun h (fun _ => 0)) hn) rfl

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bounded_residue_relation) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.NumericalSemigroup.SignedResidueRelation.Exponents.unit
  realizationName := `Reg.D5.S3.Combinatorics.NumericalSemigroup.SignedResidueRelation.Exponents.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.NumericalSemigroup.SignedResidueRelation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","body",
        "arg","body","arg","body","fn","arg","fn","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Exponents

namespace Polynomial

abbrev signature : Signature where
  Params := ℕ
  State e := MvPolynomial (Fin e) ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ e := MvPolynomial (Fin e) ℚ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ f h => f ≠ h) (fun x => nomatch x)
def rejected : Realization signature := realize signature
  (fun _ _ _ _ => False) (fun x => nomatch x)

def arena : Arena where
  signature := signature
  Law R := ∀ (e q m : ℕ) (_ : 0 < m) (g : Fin e → ℕ)
    (_ : m < (signedVectors e q).card),
    ∃ f : MvPolynomial (Fin e) ℚ,
      f ∈ reducedToricIdeal m g ∧ R.readout () e f 0 ∧ f.totalDegree ≤ 2 * q

private theorem bad : ¬ arena.Law rejected := by
  intro h
  obtain ⟨f, _, hn, _⟩ := h 1 1 1 (by omega) (fun _ => 1) two_vectors
  exact hn

def family : Registration arena (type_of% @exists_bounded_reduced_relation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exists_bounded_reduced_relation, rejected, bad⟩
  sensitivity := by
    constructor
    · intro i
      change Unit at i
      refine ⟨rejected, ?_, rfl, bad⟩
      intro j hj
      change Unit at j
      exact (hj (by cases j; cases i; rfl)).elim
    · intro i
      exact nomatch i
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨1, 0, 1, ?_⟩
    intro h
    change (fun f : MvPolynomial (Fin 1) ℚ => 0 ≠ f) =
      (fun f : MvPolynomial (Fin 1) ℚ => 1 ≠ f) at h
    exact (Eq.mpr (congrFun h 0) one_ne_zero) rfl

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_bounded_reduced_relation) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.NumericalSemigroup.SignedResidueRelation.Polynomial.unit
  realizationName := `Reg.D5.S3.Combinatorics.NumericalSemigroup.SignedResidueRelation.Polynomial.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.NumericalSemigroup.SignedResidueRelation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","body",
        "arg","body","arg","fn","arg","fn","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Polynomial
end Reg.D5.S3.Combinatorics.NumericalSemigroup.SignedResidueRelation
