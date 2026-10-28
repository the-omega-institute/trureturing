import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySuffixEnergy
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Original increment energy as the readout of the disjoint suffix estimates. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySuffixEnergy

open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySuffixEnergy
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryPathSplit (S)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCentering (C)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceHardy (Edge H)
open _root_.D5.S0.Computability.Coding.PrefixFreeCode (IsPrefixFree)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators ENNReal

abbrev signature : Signature where
  Params := Unit
  State _ := H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖ ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

private def edge : Edge := ⟨[false], by simp⟩

private theorem dependence (i : Unit) : ∃ p s t, actual.readout i p s ≠ actual.readout i p t := by
  refine ⟨(), (0 : H), lp.single 2 edge (1 : ℝ), ?_⟩
  change ‖(0 : H)‖ ^ 2 ≠ ‖(lp.single 2 edge (1 : ℝ) : H)‖ ^ 2
  rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  norm_num

namespace Disjoint

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (A : Finset Address), IsPrefixFree (A : Set Address) → ∀ z : H,
    ∑ p ∈ A, ‖S p z‖ ^ 2 ≤ R.readout () () z

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h ∅ (by simp [IsPrefixFree]) 0
  change (∑ p ∈ (∅ : Finset Address), ‖S p (0 : H)‖ ^ 2) ≤ (-1 : ℝ) at he
  norm_num at he

def familyRegistration : Registration arena (type_of% prefix_free_suffix_energy) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨prefix_free_suffix_energy, rejected, rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@prefix_free_suffix_energy)
    (type_of% (realize signature (fun _ _ z => ‖z‖ ^ 2) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySuffixEnergy.Disjoint.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySuffixEnergy.Disjoint.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ z => ‖z‖ ^ 2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySuffixEnergy,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "arg"],
      stateBinder := 2, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Disjoint

namespace Weighted

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (A : Finset Address), IsPrefixFree (A : Set Address) →
    ∀ (w : Address → ℝ) (t : ℝ), 0 ≤ t →
    (∀ p ∈ A, 0 ≤ w p ∧ w p ≤ t) → ∀ z : H,
      ∑ p ∈ A, w p * ‖C (S p z)‖ ^ 2 ≤ Real.goldenRatio * t * R.readout () () z

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h ∅ (by simp [IsPrefixFree]) (fun _ => 0) 1 (by norm_num)
    (by simp) 0
  change (∑ p ∈ (∅ : Finset Address), (0 : ℝ) * ‖C (S p (0 : H))‖ ^ 2) ≤
    Real.goldenRatio * 1 * (-1 : ℝ) at he
  simp only [Finset.sum_empty, mul_one, mul_neg, mul_one] at he
  linarith [Real.goldenRatio_pos]

def familyRegistration : Registration arena (type_of% weighted_centered_suffix_energy) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨weighted_centered_suffix_energy, rejected, rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weighted_centered_suffix_energy)
    (type_of% (realize signature (fun _ _ z => ‖z‖ ^ 2) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySuffixEnergy.Weighted.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySuffixEnergy.Weighted.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ z => ‖z‖ ^ 2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySuffixEnergy,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg"],
      stateBinder := 6, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Weighted

end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySuffixEnergy
