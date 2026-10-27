import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderProjection
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Actual normalized cylinder means in the full projection family. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderProjection

open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderProjection
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrace (Omega M G cylinder indicator)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryPathSplit (constG S boundary_path_split)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCentering (mean Pi C centered_suffix_residual)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryConditionalLaw (pullback conditional_pullback_law)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceHardy (Edge H)
open _root_.D5.S0.Computability.Coding.PrefixFreeCode (IsPrefixFree)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory
open scoped BigOperators ENNReal

abbrev signature : Signature where
  Params := Edge
  State _ := G
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p F => atomMean p F) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (A : Finset Edge), IsPrefixFree (Subtype.val '' (A : Set Edge)) →
    (∀ (p : Edge) (F : G), R.readout () p F =
      (M.real (cylinder p.val))⁻¹ * ∫ ω in cylinder p.val, F ω ∂M) ∧
    (∀ (p : Edge) (F : G), R.readout () p F = mean (pullback p.val F)) ∧
    (∀ F : G, Q A F = (V A).starProjection F) ∧
    (∀ p ∈ A, Q A (indicator p) = indicator p)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

private def edge : Edge := ⟨[false], by simp⟩

private theorem normalized_one (p : Edge) :
    (M.real (cylinder p.val))⁻¹ * ∫ ω in cylinder p.val, constG 1 ω ∂M = 1 := by
  rw [integral_congr_ae (ae_restrict_of_ae (boundary_path_split.2.2.2.1 (1 : ℝ)))]
  rw [integral_const]
  simp only [measureReal_def, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, smul_eq_mul, mul_one]
  exact inv_mul_cancel₀
    (ENNReal.toReal_pos (conditional_pullback_law.1 p.val) (measure_ne_top _ _)).ne'

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h ∅ (by simp [IsPrefixFree])).1 edge (constG 1)
  change (0 : ℝ) = _ at he
  rw [normalized_one] at he
  norm_num at he

def familyRegistration : Registration arena (type_of% cylinder_average_projection) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cylinder_average_projection, rejected, rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨edge, (0 : G), constG 1, ?_⟩
    change atomMean edge 0 ≠ atomMean edge (constG 1)
    rw [map_zero, (cylinder_average_projection ∅ (by simp [IsPrefixFree])).1,
      normalized_one]
    norm_num

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@cylinder_average_projection)
    (type_of% (realize signature (fun _ p F => atomMean p F) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderProjection.unit,
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderProjection.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p F => atomMean p F) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderProjection,
    definition := none, coordinates := #[2],
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "body", "fn", "arg"],
      stateBinder := 3, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

namespace FirstLevel

private def left : Edge := ⟨[false], by simp⟩
private def right : Edge := ⟨[true], by simp⟩

def base : Finset Edge := {left, right}

theorem prefix_free : IsPrefixFree (Subtype.val '' (base : Set Edge)) := by
  rintro u ⟨p, hp, rfl⟩ v ⟨q, hq, rfl⟩ huv
  have length_one (r : Edge) (hr : r ∈ base) : r.val.length = 1 := by
    simp only [base, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl <;> rfl
  exact huv.eq_of_length (by rw [length_one p hp, length_one q hq])

theorem cover : ∀ ω : Omega, ∃ p ∈ base, ω ∈ cylinder p.val := by
  intro ω
  let p : Edge := ⟨[ω 0], by simp⟩
  refine ⟨p, ?_, ?_⟩
  · cases h : ω 0 <;> simp [base, left, right, p, h]
  · simp [_root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrace.cylinder,
      p, Finset.range_one]

end FirstLevel

private theorem const_one_ne_zero : constG 1 ≠ 0 := by
  intro he
  have hm := congrArg mean he
  rw [centered_suffix_residual.2.1, map_zero] at hm
  norm_num at hm

namespace Partition

abbrev signature : Signature where
  Params := Finset Edge
  State _ := G
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := G
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ A F => Q A F) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (A : Finset Edge), IsPrefixFree (Subtype.val '' (A : Set Edge)) →
    (∀ ω : Omega, ∃ p ∈ A, ω ∈ cylinder p.val) →
    (∀ p ∈ A, ∀ F : G, pullback p.val (R.readout () A F) = constG (atomMean p F)) ∧
    (∀ p ∈ A, ∀ z : H, pullback p.val (C z-R.readout () A (C z)) = C (S p.val z)) ∧
    (∀ F : G, ‖F‖ ^ 2 =
      ∑ p ∈ A, M.real (cylinder p.val) * ‖pullback p.val F‖ ^ 2) ∧
    (∀ z : H, ‖C z-R.readout () A (C z)‖ ^ 2 =
      ∑ p ∈ A, M.real (cylinder p.val) * ‖C (S p.val z)‖ ^ 2) ∧
    (∀ c : ℝ, R.readout () A (constG c) = constG c) ∧
    (∀ F : G, R.readout () A (Pi F) = Pi (R.readout () A F))

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : G)) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h FirstLevel.base FirstLevel.prefix_free FirstLevel.cover).2.2.2.2.1 1
  change (0 : G) = constG 1 at he
  exact const_one_ne_zero he.symm

def familyRegistration : Registration arena (type_of% partition_centered_residual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨partition_centered_residual, rejected, rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨FirstLevel.base, (0 : G), constG 1, ?_⟩
    change Q FirstLevel.base 0 ≠ Q FirstLevel.base (constG 1)
    rw [map_zero, (partition_centered_residual FirstLevel.base
      FirstLevel.prefix_free FirstLevel.cover).2.2.2.2.1]
    exact const_one_ne_zero.symm

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@partition_centered_residual)
    (type_of% (realize signature (fun _ A F => Q A F) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderProjection.Partition.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderProjection.Partition.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ A F => Q A F) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderProjection,
    definition := none, coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "body", "body", "body", "fn", "arg", "arg"],
      stateBinder := 5, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Partition

namespace Bounded

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
  Law R := ∀ (A : Finset Edge), IsPrefixFree (Subtype.val '' (A : Set Edge)) →
    (∀ ω : Omega, ∃ p ∈ A, ω ∈ cylinder p.val) →
    ∀ (t : ℝ), 0 ≤ t → (∀ p ∈ A, M.real (cylinder p.val) ≤ t) → ∀ z : H,
      ‖C z-Q A (C z)‖ ^ 2 ≤ Real.goldenRatio * t * R.readout () () z

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h FirstLevel.base FirstLevel.prefix_free FirstLevel.cover 1
    (by norm_num) (fun _ _ => measureReal_le_one) 0
  change ‖C (0 : H)-Q FirstLevel.base (C 0)‖ ^ 2 ≤
    Real.goldenRatio * 1 * (-1 : ℝ) at he
  simp only [map_zero, sub_zero, norm_zero, zero_pow (by decide : 2 ≠ 0),
    mul_one, mul_neg] at he
  linarith [Real.goldenRatio_pos]

def familyRegistration : Registration arena (type_of% bounded_partition_residual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨bounded_partition_residual, rejected, rejected_law⟩
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
    (@bounded_partition_residual)
    (type_of% (realize signature (fun _ _ z => ‖z‖ ^ 2) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderProjection.Bounded.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderProjection.Bounded.familyRegistration,
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
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderProjection,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg"],
      stateBinder := 6, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Bounded

end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderProjection
