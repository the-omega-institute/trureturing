import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.OmegaTail.Lower
import Reg.Support.SingleDependentReadout

/-! Typed source family for the injective prime-product lower bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Real Finset LeanInformationAudit
open scoped Topology BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTailUpper
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTail.Lower

namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Lower
universe u

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {J : Type u} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (k : J → ℕ) (B : J → ℝ) (lambda x : ℝ)
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hprime : ∀ j, ∀ p ∈ P j, Nat.Prime p)
    (hB : ∀ j, 0 < B j) (hcap : ∀ j, ∀ p ∈ P j, (p : ℝ) ≤ B j)
    (hsize : threshold lambda x < ((∑ j, k j : ℕ) : ℝ))
    (hcost : ∑ j, (k j : ℝ) * log (B j) ≤ log x) (hx : 0 < x),
    R.readout () () (∏ j, (P j).card.choose (k j)) (tailCount lambda x)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (J := PUnit) (fun _ => ∅) (fun _ => 1) (fun _ => 1) 0 1
    (by intro i j hij; simp) (by simp) (by simp) (by simp)
    (by simp [threshold, scale]) (by simp) (by norm_num)

def family : Registration arena (type_of% @multibox_bound.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@multibox_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), 1, ?_⟩
    intro he
    have hh : (1 : ℕ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@multibox_bound.{u}) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.Lower.multibox_bound.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Lower.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.Lower
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


namespace PrimeProduct

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Finset ℕ) (fun _ => Finset ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {S T : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hT : ∀ p ∈ T, Nat.Prime p)
    (h : ∏ p ∈ S, p = ∏ p ∈ T, p), R.readout () () S T

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (S := ∅) (T := ∅) (by simp) (by simp) (by simp)

def family : Registration arena (type_of% @prime_product_injective) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@prime_product_injective, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (∅ : Finset ℕ), {1}, ?_⟩
    intro he
    have hh : ({1} : Finset ℕ) = ∅ := Eq.mp (congrFun he (∅ : Finset ℕ)) rfl
    simp at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@prime_product_injective) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.Lower.prime_product_injective.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Lower.PrimeProduct.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.Lower
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PrimeProduct

namespace OmegaPrimeProduct

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p),
    R.readout () () (ArithmeticFunction.cardDistinctFactors (∏ p ∈ S, p)) S.card

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (S := ∅) (by simp)

def family : Registration arena (type_of% @omega_prime_product) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@omega_prime_product, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), 1, ?_⟩
    intro he
    have hh : (1 : ℕ) = 0 := Eq.mp (congrFun he 0) rfl
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@omega_prime_product) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.Lower.omega_prime_product.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Lower.OmegaPrimeProduct.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.Lower
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end OmegaPrimeProduct

namespace PrimeFamily

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (lambda x : ℝ) (C : Finset (Finset ℕ))
    (hprime : ∀ S ∈ C, ∀ p ∈ S, Nat.Prime p)
    (hsize : ∀ S ∈ C, threshold lambda x < (S.card : ℝ))
    (hcost : ∀ S ∈ C, ∑ p ∈ S, log (p : ℝ) ≤ log x)
    (hx : 0 < x), R.readout () () C.card (tailCount lambda x)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 1 ∅ (by simp) (by simp) (by simp) (by norm_num)

def family : Registration arena (type_of% @prime_family_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@prime_family_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), 1, ?_⟩
    intro he
    have hh : (1 : ℕ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@prime_family_bound) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.Lower.prime_family_bound.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Lower.PrimeFamily.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.Lower
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PrimeFamily

namespace BinUnion

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Finset ℕ) (fun _ => Finset ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {J : Type u} [Fintype J] [DecidableEq J]
    (P f : J → Finset ℕ) (hP : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hf : ∀ j, f j ⊆ P j) (j : J),
    R.readout () () ((univ.biUnion f) ∩ P j) (f j)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (J := PUnit) (fun _ => ∅) (fun _ => ∅)
    (by intro i j hij; exact (hij (Subsingleton.elim _ _)).elim)
    (by simp) PUnit.unit

def family : Registration arena (type_of% @bin_union_inter.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bin_union_inter.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (∅ : Finset ℕ), {1}, ?_⟩
    intro he
    have hh : ({1} : Finset ℕ) = ∅ := Eq.mp (congrFun he (∅ : Finset ℕ)) rfl
    simp at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bin_union_inter.{u}) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.Lower.bin_union_inter.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Lower.BinUnion.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.Lower
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end BinUnion

end Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Lower
