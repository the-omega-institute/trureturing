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

private theorem zero_mass_card_le_one (e : ℕ) : (signedVectors e 0).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro v hv w hw
  have hvb := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hv).1
  have hwb := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hw).1
  funext i
  have hvi := Finset.mem_Icc.mp (hvb i)
  have hwi := Finset.mem_Icc.mp (hwb i)
  norm_num at hvi hwi
  omega

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

namespace Counting

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ e q => (signedVectors e q).card) (fun x => nomatch x)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun x => nomatch x)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  intro h
  change (signedVectors 1 0).card = (signedVectors 1 1).card at h
  have hz := zero_mass_card_le_one 1
  have hp := two_vectors
  omega

def arena : Arena where
  signature := signature
  Law R := ∀ e q : ℕ,
    (∑ i ∈ Finset.range (e + 1), e.choose i * q.choose i * q.choose (e - i)) ≤
      R.readout () e q

private theorem bad : ¬ arena.Law rejected := by
  intro h
  have hn := h 0 0
  norm_num [rejected, realize] at hn

def family : Registration arena (type_of% @signed_count_lower_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨signed_count_lower_bound, rejected, bad⟩
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
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@signed_count_lower_bound) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.NumericalSemigroup.SignedResidueRelation.Counting.unit
  realizationName := `Reg.D5.S3.Combinatorics.NumericalSemigroup.SignedResidueRelation.Counting.family
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
      path := #["body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Counting

namespace Dominance

abbrev signature := Counting.signature
def actual : Realization signature := realize signature
  (fun _ e r => (signedVectors e (3 * r / 8)).card) (fun x => nomatch x)
def rejected : Realization signature := Counting.rejected

def arena : Arena where
  signature := signature
  Law R := ∀ (e : ℕ) (_ : 3 ≤ e),
    ∃ N : ℕ, ∀ r ≥ N, (e + r).choose e < R.readout () e r

private theorem bad : ¬ arena.Law rejected := by
  intro h
  obtain ⟨N, hN⟩ := h 3 (by omega)
  exact Nat.not_lt_zero _ (hN N le_rfl)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨3, 0, 3, ?_⟩
  intro h
  change (signedVectors 3 0).card = (signedVectors 3 1).card at h
  have hz := zero_mass_card_le_one 3
  have hp : 1 < (signedVectors 3 1).card := by
    classical
    apply Finset.one_lt_card.mpr
    refine ⟨(fun _ => 0), ?_, (fun j => if j = 0 then 1 else 0), ?_, ?_⟩
    · norm_num [signedVectors, Fintype.mem_piFinset, positiveMass, negativeMass]
    · norm_num [signedVectors, Fintype.mem_piFinset, positiveMass, negativeMass,
        Fin.sum_univ_succ, Fin.forall_fin_succ]
    · intro hh
      have := congrFun hh 0
      norm_num at this
  omega

def family : Registration arena (type_of% @eventual_signed_count_dominance) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨eventual_signed_count_dominance, rejected, bad⟩
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
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@eventual_signed_count_dominance) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.NumericalSemigroup.SignedResidueRelation.Dominance.unit
  realizationName := `Reg.D5.S3.Combinatorics.NumericalSemigroup.SignedResidueRelation.Dominance.family
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
      path := #["body", "body", "arg", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Dominance

namespace BlockRelation

abbrev signature := Polynomial.signature
abbrev actual := Polynomial.actual
abbrev rejected := Polynomial.rejected

def arena : Arena where
  signature := signature
  Law R := ∀ (e : ℕ) (_ : 3 ≤ e),
    ∃ N : ℕ, ∀ r ≥ N, ∀ m : ℕ,
      (e + r - 1).choose (r - 1) ≤ m → m < (e + r).choose r → ∀ g : Fin e → ℕ,
      ∃ f : MvPolynomial (Fin e) ℚ,
        f ∈ reducedToricIdeal m g ∧ R.readout () e f 0 ∧
          f.totalDegree ≤ 2 * (3 * r / 8)

private theorem bad : ¬ arena.Law rejected := by
  intro h
  obtain ⟨N, hN⟩ := h 3 (by omega)
  let r := N + 1
  have hp : 0 < (3 + r - 1).choose 2 := Nat.choose_pos (by dsimp [r]; omega)
  have hb : (3 + r - 1).choose 3 < (3 + r).choose 3 := by
    have hpas := Nat.choose_succ_succ (3 + r - 1) 2
    change (3 + r - 1 + 1).choose 3 =
      (3 + r - 1).choose 2 + (3 + r - 1).choose 3 at hpas
    rw [show 3 + r - 1 + 1 = 3 + r by dsimp [r]; omega] at hpas
    omega
  have lower : (3 + r - 1).choose (r - 1) = (3 + r - 1).choose 3 := by
    rw [← Nat.choose_symm (by dsimp [r]; omega : r - 1 ≤ 3 + r - 1)]
    congr 1
    dsimp [r]
    omega
  have upper : (3 + r).choose r = (3 + r).choose 3 := by
    rw [← Nat.choose_symm (by omega : r ≤ 3 + r), Nat.add_sub_cancel]
  obtain ⟨f, _, hn, _⟩ := hN r (by dsimp [r]; omega)
    ((3 + r - 1).choose 3) (by rw [lower]) (by rw [upper]; exact hb) (fun _ => 1)
  exact hn

def family : Registration arena (type_of% @eventual_block_reduced_relation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨eventual_block_reduced_relation, rejected, bad⟩
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
    refine ⟨3, 0, 1, ?_⟩
    intro h
    change (fun f : MvPolynomial (Fin 3) ℚ => 0 ≠ f) =
      (fun f : MvPolynomial (Fin 3) ℚ => 1 ≠ f) at h
    exact (Eq.mpr (congrFun h 0) one_ne_zero) rfl

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@eventual_block_reduced_relation) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.NumericalSemigroup.SignedResidueRelation.BlockRelation.unit
  realizationName := `Reg.D5.S3.Combinatorics.NumericalSemigroup.SignedResidueRelation.BlockRelation.family
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
      path := #["body", "body", "arg", "body", "body", "body", "body", "body",
        "body", "body", "arg", "body", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end BlockRelation
end Reg.D5.S3.Combinatorics.NumericalSemigroup.SignedResidueRelation
