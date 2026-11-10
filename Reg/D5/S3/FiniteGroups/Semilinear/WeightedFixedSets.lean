import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.Semilinear.WeightedFixedSets
import Reg.Support.DependentFamily

set_option autoImplicit false
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open WeightedSemilinear
open scoped Classical
namespace Reg.D5.S3.FiniteGroups.Semilinear.WeightedFixedSets
noncomputable section
universe u
private theorem ecard (q : ℕ) [Fact q.Prime] :
    Nat.card (IntermediateField.fixedField (Subgroup.zpowers (1 : Gal(ZMod q / ZMod q)))) = q := by
  rw [Subgroup.zpowers_one_eq_bot, IntermediateField.fixedField_bot,
    Nat.card_congr IntermediateField.topEquiv.toEquiv, Nat.card_eq_fintype_card, ZMod.card]
namespace coordinate_card
structure Scope where
  F : Type
  K : Type
  [fieldF : Field F]
  [fieldK : Field K]
  [finiteF : Fintype F]
  [finiteK : Fintype K]
  [algebraFK : Algebra F K]
  σ : Gal(K/F)
attribute [instance] Scope.fieldF Scope.fieldK Scope.finiteF Scope.finiteK Scope.algebraFK

abbrev signature : Signature where
  Params := Scope
  State p := p.K
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p x => Nat.card {y : p.K // p.σ y = x * y}) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun i p x => actual.readout i p x + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {F K : Type} [fF : Field F] [fK : Field K] [nF : Fintype F] [nK : Fintype K]
    [alg : Algebra F K] (σ : Gal(K/F)) (a : K),
    r.readout () ⟨F,K,σ⟩ a =
      if Algebra.norm (IntermediateField.fixedField (Subgroup.zpowers σ)) a = 1
      then Nat.card (IntermediateField.fixedField (Subgroup.zpowers σ)) else 1
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hb := h (F := ZMod 2) (K := ZMod 2) 1 0
  have hp := WeightedSemilinear.coordinate_card (F := ZMod 2) (K := ZMod 2) 1 0
  simp only [rejected, realize, actual] at hb
  omega
def family : Registration arena (type_of% (@WeightedSemilinear.coordinate_card)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@WeightedSemilinear.coordinate_card, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    letI : Fact (Nat.Prime 2) := ⟨by decide⟩
    refine ⟨⟨ZMod 2, ZMod 2, 1⟩, 0, 1, ?_⟩
    change Nat.card {y : ZMod 2 // (1 : Gal(ZMod 2 / ZMod 2)) y = 0 * y} ≠
      Nat.card {y : ZMod 2 // (1 : Gal(ZMod 2 / ZMod 2)) y = 1 * y}
    rw [WeightedSemilinear.coordinate_card, WeightedSemilinear.coordinate_card]
    norm_num [ecard]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@WeightedSemilinear.coordinate_card) (Realization signature) Unit Unit where
  unitName := `WeightedSemilinear.coordinate_card.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.Semilinear.WeightedFixedSets.coordinate_card.family
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
    owner := `D5.S3.FiniteGroups.Semilinear.WeightedFixedSets
    definition := none
    coordinates := #[0,1,2,3,4,5,6,7]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end coordinate_card
namespace vector_card
structure Scope where
  F : Type
  K : Type
  [fieldF : Field F]
  [fieldK : Field K]
  [finiteF : Fintype F]
  [finiteK : Fintype K]
  [algebraFK : Algebra F K]
  I : Type u
  [finiteI : Fintype I]
  σ : Gal(K/F)
  c : Kˣ
attribute [instance] Scope.fieldF Scope.fieldK Scope.finiteF Scope.finiteK Scope.algebraFK
attribute [instance] Scope.finiteI

abbrev signature : Signature where
  Params := Scope.{u}
  State p := p.I → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature.{u}
  (fun _ p x => Nat.card {A : p.I → p.K // ∀ i, p.σ (A i) = (p.c : p.K) ^ x i * A i}) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature.{u}
  (fun i p x => actual.readout i p x + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {F K : Type} [fF : Field F] [fK : Field K] [nF : Fintype F] [nK : Fintype K]
    [alg : Algebra F K] {I : Type u} [fi : Fintype I] (w : I → ℕ)
    (σ : Gal(K/F)) (c : Kˣ),
    r.readout () ⟨F,K,I,σ,c⟩ w =
      Nat.card (IntermediateField.fixedField (Subgroup.zpowers σ)) ^
        (Finset.univ.filter (fun i => orderOf
          (Units.map (Algebra.norm (IntermediateField.fixedField (Subgroup.zpowers σ)) (S := K)) c) ∣ w i)).card
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hb := h (F := ZMod 2) (K := ZMod 2) (I := PUnit.{u+1}) (fun _ => 0) 1 1
  have hp := WeightedSemilinear.vector_card (F := ZMod 2) (K := ZMod 2) (I := PUnit.{u+1}) (fun _ => 0) 1 1
  simp only [rejected, realize, actual] at hb
  omega
def family : Registration arena.{u} (type_of% (@WeightedSemilinear.vector_card.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@WeightedSemilinear.vector_card, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    letI : Fact (Nat.Prime 3) := ⟨by decide⟩
    refine ⟨⟨ZMod 3,ZMod 3,PUnit.{u+1},1,-1⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    simp only [actual, realize]
    simp
    intro a
    have hs : ∀ A : PUnit.{u+1} → ZMod 3, (∀ j, A j = -A j) ↔ A = 0 := by
      intro A
      constructor
      · intro h
        funext j
        have he := h j
        have hz : A j + A j = 0 := eq_neg_iff_add_eq_zero.mp he
        have hi : (2 : ZMod 3) * A j = 0 := by simpa [two_mul] using hz
        exact (mul_eq_zero.mp hi).resolve_left (by decide)
      · rintro rfl j
        simp
    simp_rw [hs] at a
    norm_num at a

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@WeightedSemilinear.vector_card.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `WeightedSemilinear.vector_card.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.Semilinear.WeightedFixedSets.vector_card.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.Semilinear.WeightedFixedSets
    definition := none
    coordinates := #[0,1,2,3,4,5,6,7,8,10,11]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end vector_card
end
end Reg.D5.S3.FiniteGroups.Semilinear.WeightedFixedSets
