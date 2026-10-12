import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.OriginalMovingWindowMoment
import Reg.Support.DependentFamily

noncomputable section
set_option autoImplicit false
open _root_.D5.S3.Arith.Robin.OriginalMovingWindowMoment
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open MeasureTheory Set
open scoped BigOperators

namespace Reg.D5.S3.Arith.Robin.OriginalMovingWindowMoment

abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ t β => moment t β) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {t β : ℝ}, 4 ≤ t → 0 ≤ β →
    |R.readout () t β - t ^ (1 / 2 - β) / 2| ≤
      (4 + β + 2 * β * 2 ^ (β + 1)) * t ^ (-1 / 5 : ℝ) *
        (t ^ (1 / 2 - β) / 2)

private lemma test_scale : (32768 : ℝ) ^ (-1 / 5 : ℝ) = 1 / 8 := by
  calc
    _ = ((8 : ℝ) ^ 5) ^ (-1 / 5 : ℝ) := by norm_num
    _ = (8 : ℝ) ^ ((5 : ℝ) * (-1 / 5 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 8)]
      norm_num
    _ = _ := by norm_num [Real.rpow_neg_one]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ht := h (t := 32768) (β := 0) (by norm_num) (by norm_num)
  change |0 - (32768 : ℝ) ^ (1 / 2 - 0) / 2| ≤ _ at ht
  simp only [sub_zero, zero_sub, abs_neg, zero_mul, add_zero,
    test_scale, abs_of_pos (by positivity : 0 < (32768 : ℝ) ^ (1 / 2 : ℝ) / 2)] at ht
  have hp : 0 < (32768 : ℝ) ^ (1 / 2 : ℝ) := by positivity
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨32768, 0, 1, ?_⟩
  change moment 32768 0 ≠ moment 32768 1
  have h0 := original_window_moment_estimate (t := 32768) (β := 0)
    (by norm_num) (by norm_num)
  have h1 := original_window_moment_estimate (t := 32768) (β := 1)
    (by norm_num) (by norm_num)
  rw [test_scale] at h0 h1
  norm_num only [sub_zero, zero_mul, add_zero, one_mul,
    show (1 / 2 : ℝ) - 1 = -1 / 2 by norm_num] at h0 h1
  have hs : (32768 : ℝ) ^ (-(1 / 2 : ℝ)) = (32768 : ℝ) ^ (1 / 2 : ℝ) / 32768 := by
    calc
      _ = (32768 : ℝ) ^ ((1 / 2 : ℝ) - 1) := by norm_num
      _ = _ := by
        rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 32768), Real.rpow_one]
  rw [hs] at h1
  have hp : 0 < (32768 : ℝ) ^ (1 / 2 : ℝ) := by positivity
  have hlow := (abs_le.mp h0).1
  have hhigh := (abs_le.mp h1).2
  intro heq
  rw [heq] at hlow
  norm_num at hlow hhigh
  linarith

def family : Registration arena (type_of% (@original_window_moment_estimate)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@original_window_moment_estimate, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_window_moment_estimate)
    (type_of% (realize signature (fun _ t β => moment t β) (fun e => nomatch e)))
    Type Unit where
  unitName := `D5.S3.Arith.Robin.OriginalMovingWindowMoment.original_window_moment_estimate.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalMovingWindowMoment.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ t β => moment t β) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalMovingWindowMoment
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

namespace CutRowAudit

abbrev rowSignature : Signature where
  Params := ℝ × ℝ × ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def rowActual : Realization rowSignature :=
  realize rowSignature (fun _ p d => latticeRowRemainder p.1 p.2.1 p.2.2 d)
    (fun e => nomatch e)

def rowRejected : Realization rowSignature :=
  realize rowSignature
    (fun _ p _ => 3 * lowerHeight p.2.2 * Real.log (2 * p.2.2) + 1)
    (fun e => nomatch e)

abbrev rowArena : Arena where
  signature := rowSignature
  Law V := ∀ {ell R t : ℝ}, 256 ≤ ell → ell < R → t ∈ Set.Icc ell R →
    ∀ {d : ℕ}, 1 ≤ d →
      |V.readout () (ell, R, t) d| ≤ 3 * lowerHeight t * Real.log (2 * t)

private theorem rowActual_law : rowArena.Law rowActual := @original_cut_row_lattice_estimate

private theorem rowRejected_law : ¬ rowArena.Law rowRejected := by
  intro h
  have hh := h (ell := 256) (R := 257) (t := 256) (by norm_num) (by norm_num)
    (by norm_num) (d := 1) (by norm_num)
  change |3 * lowerHeight 256 * Real.log (2 * 256) + 1| ≤ _ at hh
  linarith [le_abs_self (3 * lowerHeight 256 * Real.log (2 * 256) + 1)]

private theorem rowVariation : Variation rowArena rowActual :=
  ⟨rowActual_law, rowRejected, rowRejected_law⟩

private theorem rowSensitivity : Sensitivity rowArena rowActual := by
  constructor
  · intro i
    refine ⟨rowRejected, ?_, rfl, rowRejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim
  · intro e
    exact nomatch e

private theorem rowBridge :
    (type_of% (@original_cut_row_lattice_estimate)) ↔ rowArena.Law rowActual := Iff.rfl

abbrev pointArena : Arena where
  signature := rowSignature
  Law V := ∀ {ell R t : ℝ}, 256 ≤ ell → ell < R → t ∈ Set.Icc ell R →
    ∑ d ∈ Finset.Icc 1 ⌊endpoint t ^ (151 / 500 : ℝ)⌋₊,
      |((ArithmeticFunction.moebius d : ℤ) : ℝ)| * |V.readout () (ell, R, t) d| ≤
        6 * t ^ (-99 / 500 : ℝ) * Real.log (2 * t)

def pointRejected : Realization rowSignature :=
  realize rowSignature
    (fun _ p _ => 6 * p.2.2 ^ (-99 / 500 : ℝ) * Real.log (2 * p.2.2) + 1)
    (fun e => nomatch e)

private theorem pointActual_law : pointArena.Law rowActual := @original_cut_row_pointwise_budget

private theorem pointRejected_law : ¬ pointArena.Law pointRejected := by
  intro h
  have hh := h (ell := 256) (R := 257) (t := 256) (by norm_num) (by norm_num)
    (by norm_num)
  let C : ℝ := 6 * (256 : ℝ) ^ (-99 / 500 : ℝ) * Real.log (2 * 256)
  change (∑ d ∈ Finset.Icc 1 ⌊endpoint 256 ^ (151 / 500 : ℝ)⌋₊,
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| * |C + 1|) ≤ C at hh
  have hB : 1 ≤ endpoint (256 : ℝ) := by
    have hp := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 256) (4 / 5 : ℝ)
    dsimp [endpoint, width]
    linarith
  have hfloor : 1 ≤ ⌊endpoint 256 ^ (151 / 500 : ℝ)⌋₊ := by
    apply Nat.le_floor
    simpa using Real.one_le_rpow hB (by norm_num : (0 : ℝ) ≤ 151 / 500)
  have hs := Finset.single_le_sum
    (f := fun d : ℕ => |((ArithmeticFunction.moebius d : ℤ) : ℝ)| * |C + 1|)
    (s := Finset.Icc 1 ⌊endpoint 256 ^ (151 / 500 : ℝ)⌋₊)
    (fun d _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    (Finset.mem_Icc.mpr ⟨le_rfl, hfloor⟩)
  simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, abs_one, one_mul] at hs
  linarith [le_abs_self (C + 1)]

private theorem pointVariation : Variation pointArena rowActual :=
  ⟨pointActual_law, pointRejected, pointRejected_law⟩

private theorem pointSensitivity : Sensitivity pointArena rowActual := by
  constructor
  · intro i
    refine ⟨pointRejected, ?_, rfl, pointRejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim
  · intro e
    exact nomatch e

private theorem pointBridge :
    (type_of% (@original_cut_row_pointwise_budget)) ↔ pointArena.Law rowActual := Iff.rfl

abbrev aggregateSignature : Signature where
  Params := ℝ × ℝ
  State _ := Set ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def aggregateActual : Realization aggregateSignature :=
  realize aggregateSignature
    (fun _ p S => cutLattice p.1 p.2 S + cutPosterior p.1 p.2 S)
    (fun e => nomatch e)

def aggregateRejected : Realization aggregateSignature :=
  realize aggregateSignature (fun _ p S =>
    (∫ t in S, ∑ d ∈ Finset.Icc 1 ⌊2 * p.2⌋₊,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * latticeRowRemainder p.1 p.2 t d) + 1)
    (fun e => nomatch e)

abbrev aggregateArena : Arena where
  signature := aggregateSignature
  Law V := ∀ {ell R : ℝ}, 256 ≤ ell → ell < R →
    ∀ {S : Set ℝ}, MeasurableSet S → S ⊆ Set.Icc ell R →
    0 < (MeasureTheory.volume S).toReal →
    V.readout () (ell, R) S =
        (∫ t in S, ∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) * latticeRowRemainder ell R t d) ∧
    |V.readout () (ell, R) S| ≤
        6 * (∫ t in S, t ^ (-99 / 500 : ℝ) * Real.log (2 * t)) ∧
    6 * (∫ t in S, t ^ (-99 / 500 : ℝ) * Real.log (2 * t)) ≤
        6 * (MeasureTheory.volume S).toReal * ell ^ (-99 / 500 : ℝ) * Real.log (2 * ell)

private theorem aggregateActual_law : aggregateArena.Law aggregateActual :=
  @original_cut_aggregate_estimate

private theorem aggregateRejected_law : ¬ aggregateArena.Law aggregateRejected := by
  intro h
  have hh := h (ell := 256) (R := 257) (by norm_num) (by norm_num)
    (S := Set.Icc 256 257) measurableSet_Icc Subset.rfl (by norm_num)
  have he := hh.1
  change _ + 1 = _ at he
  linarith

private theorem aggregateVariation : Variation aggregateArena aggregateActual :=
  ⟨aggregateActual_law, aggregateRejected, aggregateRejected_law⟩

private theorem aggregateSensitivity : Sensitivity aggregateArena aggregateActual := by
  constructor
  · intro i
    refine ⟨aggregateRejected, ?_, rfl, aggregateRejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim
  · intro e
    exact nomatch e

private theorem aggregateBridge :
    (type_of% (@original_cut_aggregate_estimate)) ↔ aggregateArena.Law aggregateActual := Iff.rfl

#print axioms rowBridge
#print axioms rowVariation
#print axioms rowSensitivity
#print axioms pointBridge
#print axioms pointVariation
#print axioms pointSensitivity
#print axioms aggregateBridge
#print axioms aggregateVariation
#print axioms aggregateSensitivity

end CutRowAudit

end Reg.D5.S3.Arith.Robin.OriginalMovingWindowMoment
