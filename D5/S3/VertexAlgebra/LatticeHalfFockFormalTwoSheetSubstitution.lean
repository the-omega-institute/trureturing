/- GID: D5/S3/VertexAlgebra/LatticeHalfFockFormalTwoSheetSubstitution
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockFormalTwoSheetSubstitution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact formal two-sheet substitution of the original half-integer binomial labels. -/

import D5.S3.VertexAlgebra.LatticeHalfFockActualChargedTwoSheetFullNormalJets
import Mathlib.RingTheory.PowerSeries.Inverse

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockFormalTwoSheetSubstitution

open scoped BigOperators

noncomputable section

def twoSheetSeries : PowerSeries ℂ :=
  4 * PowerSeries.X * ((1 - PowerSeries.X : PowerSeries ℂ)⁻¹) ^ 2

def halfRoot : PowerSeries ℂ := PowerSeries.binomialSeries ℂ (-1 / 2 : ℂ)

def halfLabel (label : ℤ) : PowerSeries ℂ :=
  PowerSeries.binomialSeries ℂ ((label : ℂ) / 2)

def twoSheetLabel (label : ℤ) : PowerSeries ℂ :=
  PowerSeries.binomialSeries (R := ℤ) ℂ label *
    PowerSeries.rescale (-1 : ℂ) (PowerSeries.binomialSeries (R := ℤ) ℂ (-label))

private theorem minus_constant :
    PowerSeries.constantCoeff (1 - PowerSeries.X : PowerSeries ℂ) ≠ 0 := by simp

private theorem plus_constant :
    PowerSeries.constantCoeff (1 + PowerSeries.X : PowerSeries ℂ) ≠ 0 := by simp

private theorem sheet_constant : PowerSeries.constantCoeff twoSheetSeries = 0 := by
  simp [twoSheetSeries]

def sheetSubstitution : PowerSeries ℂ →ₐ[ℂ] PowerSeries ℂ :=
  PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero sheet_constant)

private theorem sheet_substitution_apply (series : PowerSeries ℂ) :
    sheetSubstitution series = series.subst twoSheetSeries := by
  exact congrFun (PowerSeries.coe_substAlgHom
    (PowerSeries.HasSubst.of_constantCoeff_zero sheet_constant)) series

private theorem sheet_substitution_X : sheetSubstitution PowerSeries.X = twoSheetSeries := by
  exact PowerSeries.substAlgHom_X _

theorem formal_two_sheet_relation :
    twoSheetSeries * (1 - PowerSeries.X) ^ 2 = 4 * PowerSeries.X := by
  calc
    twoSheetSeries * (1 - PowerSeries.X) ^ 2 =
        4 * PowerSeries.X *
          ((1 - PowerSeries.X : PowerSeries ℂ)⁻¹ * (1 - PowerSeries.X)) ^ 2 := by
      unfold twoSheetSeries
      ring
    _ = 4 * PowerSeries.X := by
      rw [PowerSeries.inv_mul_cancel _ minus_constant]
      ring

private theorem one_add_sheet :
    1 + twoSheetSeries = (1 + PowerSeries.X) ^ 2 *
      ((1 - PowerSeries.X : PowerSeries ℂ)⁻¹) ^ 2 := by
  have inverse := PowerSeries.inv_mul_cancel (1 - PowerSeries.X : PowerSeries ℂ) minus_constant
  calc
    1 + twoSheetSeries =
        ((1 - PowerSeries.X : PowerSeries ℂ)⁻¹ * (1 - PowerSeries.X)) ^ 2 +
          twoSheetSeries *
            ((1 - PowerSeries.X : PowerSeries ℂ)⁻¹ * (1 - PowerSeries.X)) ^ 2 := by
      rw [inverse]
      ring
    _ = ((1 - PowerSeries.X) ^ 2 + twoSheetSeries * (1 - PowerSeries.X) ^ 2) *
        ((1 - PowerSeries.X : PowerSeries ℂ)⁻¹) ^ 2 := by ring
    _ = (1 + PowerSeries.X) ^ 2 *
        ((1 - PowerSeries.X : PowerSeries ℂ)⁻¹) ^ 2 := by
      rw [formal_two_sheet_relation]
      ring

private theorem root_square : halfRoot ^ 2 * (1 + PowerSeries.X) = 1 := by
  have one : PowerSeries.binomialSeries ℂ (1 : ℂ) =
      (1 + PowerSeries.X : PowerSeries ℂ) := by
    simpa using PowerSeries.binomialSeries_nat (A := ℂ) (R := ℂ) 1
  unfold halfRoot
  rw [pow_two, ← PowerSeries.binomialSeries_add,
    show (-1 / 2 : ℂ) + -1 / 2 = -1 by norm_num, ← one,
    ← PowerSeries.binomialSeries_add]
  norm_num

private theorem root_substitution_constant :
    PowerSeries.constantCoeff (sheetSubstitution halfRoot) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, sheet_substitution_apply,
    PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero sheet_constant),
    finsum_eq_single _ 0]
  · simp [halfRoot]
  · intro degree nonzero
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, sheet_constant]
    simp [nonzero]

theorem original_half_root_two_sheet :
    sheetSubstitution halfRoot =
      (1 - PowerSeries.X) * (1 + PowerSeries.X : PowerSeries ℂ)⁻¹ := by
  have square := congrArg sheetSubstitution root_square
  simp only [map_mul, map_pow, map_add, map_one, sheet_substitution_X] at square
  rw [one_add_sheet] at square
  let transformed := sheetSubstitution halfRoot
  let candidate := (1 - PowerSeries.X) * (1 + PowerSeries.X : PowerSeries ℂ)⁻¹
  have scaled : (transformed * (1 + PowerSeries.X) *
      (1 - PowerSeries.X : PowerSeries ℂ)⁻¹) ^ 2 = 1 := by
    change _ at square
    convert square using 1 <;> ring
  have factor :
      (transformed * (1 + PowerSeries.X) * (1 - PowerSeries.X : PowerSeries ℂ)⁻¹ - 1) *
        (transformed * (1 + PowerSeries.X) * (1 - PowerSeries.X : PowerSeries ℂ)⁻¹ + 1) = 0 := by
    linear_combination scaled
  have nonzero :
      transformed * (1 + PowerSeries.X) * (1 - PowerSeries.X : PowerSeries ℂ)⁻¹ + 1 ≠ 0 := by
    intro zero
    have constant := congrArg PowerSeries.constantCoeff zero
    simp [transformed, root_substitution_constant] at constant
  have normalized := sub_eq_zero.mp ((mul_eq_zero.mp factor).resolve_right nonzero)
  have output : transformed = candidate := by
    calc
      transformed = (transformed * (1 + PowerSeries.X) *
          (1 - PowerSeries.X : PowerSeries ℂ)⁻¹) * candidate := by
        dsimp [candidate]
        have minus := PowerSeries.inv_mul_cancel (1 - PowerSeries.X : PowerSeries ℂ) minus_constant
        have plus := PowerSeries.mul_inv_cancel (1 + PowerSeries.X : PowerSeries ℂ) plus_constant
        calc
          transformed = transformed * ((1 + PowerSeries.X) *
              (1 + PowerSeries.X : PowerSeries ℂ)⁻¹) *
              ((1 - PowerSeries.X : PowerSeries ℂ)⁻¹ * (1 - PowerSeries.X)) := by
            rw [plus, minus]
            ring
          _ = _ := by ring
      _ = candidate := by rw [normalized, one_mul]
  exact output

private theorem half_label_add (first second : ℤ) :
    halfLabel (first + second) = halfLabel first * halfLabel second := by
  unfold halfLabel
  rw [← PowerSeries.binomialSeries_add]
  congr 1
  push_cast
  ring

private theorem sheet_label_add (first second : ℤ) :
    twoSheetLabel (first + second) = twoSheetLabel first * twoSheetLabel second := by
  unfold twoSheetLabel
  rw [neg_add, PowerSeries.binomialSeries_add, PowerSeries.binomialSeries_add, map_mul]
  ring

private theorem integer_plus_one : PowerSeries.binomialSeries (R := ℤ) ℂ (1 : ℤ) =
    (1 + PowerSeries.X : PowerSeries ℂ) := by
  simpa using PowerSeries.binomialSeries_nat (A := ℂ) (R := ℤ) 1

private theorem integer_minus_one : PowerSeries.binomialSeries (R := ℤ) ℂ (-1 : ℤ) =
    (1 + PowerSeries.X : PowerSeries ℂ)⁻¹ := by
  apply (PowerSeries.eq_inv_iff_mul_eq_one plus_constant).2
  rw [← integer_plus_one, ← PowerSeries.binomialSeries_add]
  norm_num

private theorem rescaled_minus_one :
    PowerSeries.rescale (-1 : ℂ) (PowerSeries.binomialSeries (R := ℤ) ℂ (-1 : ℤ)) =
      (1 - PowerSeries.X : PowerSeries ℂ)⁻¹ := by
  apply (PowerSeries.eq_inv_iff_mul_eq_one minus_constant).2
  have one : PowerSeries.rescale (-1 : ℂ)
      (PowerSeries.binomialSeries (R := ℤ) ℂ (1 : ℤ)) =
        (1 - PowerSeries.X : PowerSeries ℂ) := by
    rw [integer_plus_one, map_add, map_one, PowerSeries.rescale_X]
    simp [sub_eq_add_neg]
  rw [← one, ← map_mul, ← PowerSeries.binomialSeries_add]
  norm_num

private theorem sheet_label_one : twoSheetLabel 1 =
    (1 + PowerSeries.X) * (1 - PowerSeries.X : PowerSeries ℂ)⁻¹ := by
  rw [twoSheetLabel, integer_plus_one, rescaled_minus_one]

private theorem sheet_label_neg_one : twoSheetLabel (-1) =
    (1 - PowerSeries.X) * (1 + PowerSeries.X : PowerSeries ℂ)⁻¹ := by
  rw [twoSheetLabel, neg_neg, integer_minus_one, integer_plus_one,
    map_add, map_one, PowerSeries.rescale_X]
  simp only [map_neg, map_one, neg_one_mul]
  ring

private theorem half_label_one_on_sheet :
    sheetSubstitution (halfLabel 1) = twoSheetLabel 1 := by
  have minus : halfLabel (-1) = halfRoot := by simp [halfLabel, halfRoot]
  have product := congrArg sheetSubstitution (half_label_add 1 (-1))
  have sheetProduct := sheet_label_add 1 (-1)
  simp only [Int.reduceAdd, halfLabel, Int.cast_zero, zero_div,
    PowerSeries.binomialSeries_zero, map_one, map_mul] at product
  change 1 = sheetSubstitution (halfLabel 1) * sheetSubstitution (halfLabel (-1)) at product
  rw [minus, original_half_root_two_sheet, ← sheet_label_neg_one] at product
  have nonzero : twoSheetLabel (-1) ≠ 0 := by
    intro zero
    have constant := congrArg PowerSeries.constantCoeff zero
    simp [sheet_label_neg_one] at constant
  apply mul_right_cancel₀ nonzero
  rw [← product, ← sheetProduct]
  simp [twoSheetLabel]

theorem original_half_integer_all_label_two_sheet (label : ℤ) :
    sheetSubstitution (halfLabel label) = twoSheetLabel label := by
  induction label using Int.induction_on with
  | zero => simp [halfLabel, twoSheetLabel]
  | succ label previous =>
    rw [half_label_add, map_mul, previous, half_label_one_on_sheet, ← sheet_label_add]
  | pred label previous =>
    have nonzero : twoSheetLabel 1 ≠ 0 := by
      intro zero
      have constant := congrArg PowerSeries.constantCoeff zero
      simp [sheet_label_one] at constant
    apply mul_right_cancel₀ nonzero
    calc
      sheetSubstitution (halfLabel (-(label : ℤ) - 1)) * twoSheetLabel 1 =
          sheetSubstitution (halfLabel (-(label : ℤ))) := by
        rw [← half_label_one_on_sheet, ← map_mul, ← half_label_add]
        congr 2
        omega
      _ = twoSheetLabel (-(label : ℤ)) := previous
      _ = twoSheetLabel (-(label : ℤ) - 1) * twoSheetLabel 1 := by
        rw [← sheet_label_add]
        congr 1
        omega

#print axioms formal_two_sheet_relation
#print axioms original_half_root_two_sheet
#print axioms original_half_integer_all_label_two_sheet

end

end D5.S3.VertexAlgebra.LatticeHalfFockFormalTwoSheetSubstitution
