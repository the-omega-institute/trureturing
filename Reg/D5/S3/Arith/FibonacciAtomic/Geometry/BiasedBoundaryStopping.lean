import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryStopping
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Full stopping families with actual mass and increment-energy readouts. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryStopping

open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryStopping
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrace
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCentering (Pi C)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryPathSplit (constG S)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryConditionalLaw (pullback)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderProjection (atomMean)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceHardy (H Edge)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceMass (a)
open _root_.D5.S0.Computability.Coding.PrefixFreeCode (IsPrefixFree)
open _root_.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality (wordMass)
open _root_.D5.S0.Computability.Coding.BiasedMassFrontier (letterMass)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory
open scoped BigOperators ENNReal

private def threshold : Threshold := ⟨1/2, by norm_num, by norm_num⟩
private def edge : Edge := ⟨[false], by simp⟩

namespace Partition
abbrev signature : Signature where
  Params := Unit
  State _ := Address
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => M.real (cylinder p)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ t : Threshold,
    (∀ p : Address, R.readout () () p = wordMass (letterMass a b) p) ∧
    (∀ p : Edge, p ∈ A t ↔ mass p.val ≤ t.val ∧ t.val < mass p.val.dropLast) ∧
    (∃ N : ℕ, ∀ p ∈ A t, p.val.length ≤ N) ∧
    IsPrefixFree (Subtype.val '' (A t : Set Edge)) ∧
    (∀ ω : Omega, ∃! p : Edge, p ∈ A t ∧ ω ∈ cylinder p.val) ∧
    (∑ p ∈ A t, M.real (cylinder p.val)) = 1 ∧
    (∀ p ∈ A t, b * t.val < M.real (cylinder p.val) ∧
      M.real (cylinder p.val) ≤ t.val) ∧
    1 / t.val ≤ ((A t).card : ℝ) ∧
      ((A t).card : ℝ) < 1 / (b * t.val)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h threshold).1 []
  change (0 : ℝ) = 1 at he
  norm_num at he

def familyRegistration : Registration arena (type_of% actual_stopping_partition) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_stopping_partition, rejected, rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), [], [false], ?_⟩
    change M.real (cylinder []) ≠ M.real (cylinder [false])
    simp only [measureReal_def, cylinder_mass, mass, List.map_nil, List.prod_nil,
      List.map_cons, Bool.false_eq_true, ↓reduceIte, List.prod_cons, mul_one]
    exact ne_of_gt a_lt_one

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_stopping_partition)
    (type_of% (realize signature (fun _ _ p => M.real (cylinder p)) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryStopping.Partition.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryStopping.Partition.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ p => M.real (cylinder p)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryStopping,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "fn", "arg", "body", "fn", "arg"],
      stateBinder := 1, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Partition

namespace Residual
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

abbrev arena : Arena where
  signature := signature
  Law R := ∀ t : Threshold,
    (∀ (p : Edge) (F : G), atomMean p F =
      (M.real (cylinder p.val))⁻¹ * ∫ ω in cylinder p.val, F ω ∂M) ∧
    (∀ F : G, Qt t F = (Vt t).starProjection F) ∧
    (∀ p ∈ A t, ∀ F : G, pullback p.val (Qt t F) = constG (atomMean p F)) ∧
    (∀ p ∈ A t, ∀ z : H, pullback p.val (C z-Qt t (C z)) = C (S p.val z)) ∧
    (∀ F : G, ‖F‖ ^ 2 =
      ∑ p ∈ A t, M.real (cylinder p.val) * ‖pullback p.val F‖ ^ 2) ∧
    (∀ z : H, ‖C z-Qt t (C z)‖ ^ 2 =
      ∑ p ∈ A t, M.real (cylinder p.val) * ‖C (S p.val z)‖ ^ 2) ∧
    (∀ z : H, ‖C z-Qt t (C z)‖ ^ 2 ≤ Real.goldenRatio * t.val * R.readout () () z) ∧
    (∀ c : ℝ, Qt t (constG c) = constG c) ∧
    (∀ F : G, Qt t (Pi F) = Pi (Qt t F)) ∧
    Module.finrank ℝ (Vt t) = (A t).card ∧
    Module.finrank ℝ (Vt0 t) = (A t).card - 1 ∧
    LinearMap.range ((Qt t).toLinearMap.comp G0.subtype) = Vt t ⊓ G0

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h threshold).2.2.2.2.2.2.1 0
  change ‖C (0 : H)-Qt threshold (C 0)‖ ^ 2 ≤
    Real.goldenRatio * (1/2) * (-1 : ℝ) at he
  simp only [map_zero, sub_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)] at he
  nlinarith [Real.goldenRatio_pos]

def familyRegistration : Registration arena (type_of% actual_stopping_residual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_stopping_residual, rejected, rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), (0 : H), lp.single 2 edge (1 : ℝ), ?_⟩
    change ‖(0 : H)‖ ^ 2 ≠ ‖(lp.single 2 edge (1 : ℝ) : H)‖ ^ 2
    rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
    norm_num

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_stopping_residual)
    (type_of% (realize signature (fun _ _ z => ‖z‖ ^ 2) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryStopping.Residual.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryStopping.Residual.familyRegistration,
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
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryStopping,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "body", "arg", "arg"],
      stateBinder := 1, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Residual
end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryStopping
