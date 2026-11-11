import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.Semilinear.WeightedArithmetic
import Reg.Support.DependentFamily

set_option autoImplicit false
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open WeightedSemilinear
open scoped Classical
namespace Reg.D5.S3.FiniteGroups.Semilinear.WeightedArithmetic
noncomputable section
universe u
private theorem ecard (q : ℕ) [Fact q.Prime] :
    Nat.card (IntermediateField.fixedField (Subgroup.zpowers (1 : Gal(ZMod q / ZMod q)))) = q := by
  rw [Subgroup.zpowers_one_eq_bot, IntermediateField.fixedField_bot,
    Nat.card_congr IntermediateField.topEquiv.toEquiv, Nat.card_eq_fintype_card, ZMod.card]
namespace norm_average
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
attribute [instance] Scope.fieldF Scope.fieldK Scope.finiteF Scope.finiteK Scope.algebraFK
attribute [instance] Scope.finiteI

abbrev signature : Signature where
  Params := Scope.{u}
  State p := p.I → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature.{u}
  (fun _ p x => (∑ c : p.Kˣ,
      (Nat.card {A : p.I → p.K // ∀ i, p.σ (A i) = (c : p.K) ^ x i * A i} : ℚ)) /
      (Fintype.card p.K - 1 : ℕ)) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature.{u}
  (fun i p x => actual.readout i p x + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {F K : Type} [fF : Field F] [fK : Field K] [nF : Fintype F] [nK : Fintype K]
    [alg : Algebra F K] {I : Type u} [fi : Fintype I] (w : I → ℕ) (σ : Gal(K/F)),
    r.readout () ⟨F,K,I,σ⟩ w =
    (∑ m ∈ (Nat.card (IntermediateField.fixedField (Subgroup.zpowers σ)) - 1).divisors, (Nat.totient m : ℚ) *
      (Nat.card (IntermediateField.fixedField (Subgroup.zpowers σ)) : ℚ) ^ (Finset.univ.filter (fun i => m ∣ w i)).card) /
      (Nat.card (IntermediateField.fixedField (Subgroup.zpowers σ)) - 1 : ℕ)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hb := h (F := ZMod 2) (K := ZMod 2) (I := PUnit.{u+1}) (fun _ => 0) 1
  have hp := WeightedSemilinear.norm_average (F := ZMod 2) (K := ZMod 2) (I := PUnit.{u+1}) (fun _ => 0) 1
  simp only [rejected, realize, actual] at hb
  linarith
def family : Registration arena.{u} (type_of% (@WeightedSemilinear.norm_average.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@WeightedSemilinear.norm_average, rejected, rejected_law⟩
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
    refine ⟨⟨ZMod 3,ZMod 3,PUnit.{u+1},1⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    have hzero := WeightedSemilinear.norm_average (F := ZMod 3) (K := ZMod 3) (I := PUnit.{u+1}) (fun _ => 0) 1
    have hone := WeightedSemilinear.norm_average (F := ZMod 3) (K := ZMod 3) (I := PUnit.{u+1}) (fun _ => 1) 1
    have hd : Nat.divisors 2 = {1,2} := by decide
    conv_rhs at hzero => norm_num [ecard, ZMod.card, Module.finrank_self, hd]
    conv_rhs at hone => norm_num [ecard, ZMod.card, Module.finrank_self, hd]
    change _ ≠ _
    dsimp only [actual, realize]
    linarith

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@WeightedSemilinear.norm_average.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `WeightedSemilinear.norm_average.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.Semilinear.WeightedArithmetic.norm_average.family
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
    owner := `D5.S3.FiniteGroups.Semilinear.WeightedArithmetic
    definition := none
    coordinates := #[0,1,2,3,4,5,6,7,8,10]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end norm_average
namespace fixed_average
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
attribute [instance] Scope.fieldF Scope.fieldK Scope.finiteF Scope.finiteK Scope.algebraFK
attribute [instance] Scope.finiteI

abbrev signature : Signature where
  Params := Scope.{u}
  State p := p.I → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature.{u}
  (fun _ p x => (∑ σ : Gal(p.K/p.F),
      (∑ c : p.Kˣ,
        (Nat.card {A : p.I → p.K // ∀ i, σ (A i) = (c : p.K) ^ x i * A i} : ℚ)) /
          (Fintype.card p.K - 1 : ℕ))) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature.{u}
  (fun i p x => actual.readout i p x + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {F K : Type} [fF : Field F] [fK : Field K] [nF : Fintype F] [nK : Fintype K]
    [alg : Algebra F K] {I : Type u} [fi : Fintype I] (w : I → ℕ),
    r.readout () ⟨F,K,I⟩ w =
    ∑ d ∈ (Module.finrank F K).divisors,
      (Nat.totient (Module.finrank F K / d) : ℚ) /
        (Fintype.card F ^ d - 1 : ℕ) *
      ∑ m ∈ (Fintype.card F ^ d - 1).divisors, (Nat.totient m : ℚ) *
        (Fintype.card F : ℚ) ^
          (d * (Finset.univ.filter (fun i => m ∣ w i)).card)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hb := h (F := ZMod 2) (K := ZMod 2) (I := PUnit.{u+1}) (fun _ => 0)
  have hp := WeightedSemilinear.fixed_average (F := ZMod 2) (K := ZMod 2) (I := PUnit.{u+1}) (fun _ => 0)
  simp only [rejected, realize, actual] at hb
  linarith
def family : Registration arena.{u} (type_of% (@WeightedSemilinear.fixed_average.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@WeightedSemilinear.fixed_average, rejected, rejected_law⟩
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
    refine ⟨⟨ZMod 3,ZMod 3,PUnit.{u+1}⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    have hzero := WeightedSemilinear.fixed_average (F := ZMod 3) (K := ZMod 3) (I := PUnit.{u+1}) (fun _ => 0)
    have hone := WeightedSemilinear.fixed_average (F := ZMod 3) (K := ZMod 3) (I := PUnit.{u+1}) (fun _ => 1)
    have hd : Nat.divisors 2 = {1,2} := by decide
    conv_rhs at hzero => norm_num [ecard, ZMod.card, Module.finrank_self, hd]
    conv_rhs at hone => norm_num [ecard, ZMod.card, Module.finrank_self, hd]
    change _ ≠ _
    dsimp only [actual, realize]
    linarith

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@WeightedSemilinear.fixed_average.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `WeightedSemilinear.fixed_average.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.Semilinear.WeightedArithmetic.fixed_average.family
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
    owner := `D5.S3.FiniteGroups.Semilinear.WeightedArithmetic
    definition := none
    coordinates := #[0,1,2,3,4,5,6,7,8]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end fixed_average
end
end Reg.D5.S3.FiniteGroups.Semilinear.WeightedArithmetic
