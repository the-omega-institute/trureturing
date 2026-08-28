/- GID: D5/S3/Observer/ArithmeticTomography/GoldenSlopeSeparation
   generality: G
   mirror-B: D5/B/S3/Observer/ArithmeticTomography/GoldenSlopeSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden-slope readings of a finite integer window have a reciprocal linear gap. -/

import D5.S3.Observer.ArithmeticTomography.IrrationalSlopeFaithfulness
import Mathlib.NumberTheory.Real.GoldenRatio

/- Library-search audit trail (2026-08-28):
   * D5 body-shape searches for a finite `Icc` product gap set, an infimum of
     golden-slope distances, and the quadratic golden norm found no owner.
   * The exact D5 prerequisite `irrational_slope_observer_injective` is
     imported and applied to both golden conjugates.
   * Pinned Mathlib supplies the golden product, sum, sign, and irrationality
     identities, together with `Int.one_le_abs` and `le_csInf`; all are used.
   * No pinned-Mathlib theorem packages this finite-window separation bound. -/

noncomputable section

namespace D5.S3.Observer.ArithmeticTomography.GoldenSlopeSeparation

open D5.S3.Observer.ArithmeticTomography.IrrationalSlopeFaithfulness

/-- Distances between readings of distinct points of the positive `H` by `H` window. -/
def goldenWindowGapSet (H : Nat) : Set Real :=
  {d | ∃ x ∈ (Finset.Icc 1 H).product (Finset.Icc 1 H),
      ∃ y ∈ (Finset.Icc 1 H).product (Finset.Icc 1 H),
        x ≠ y ∧
          d = |Real.goldenRatio * (x.1 : Real) + (x.2 : Real) -
            (Real.goldenRatio * (y.1 : Real) + (y.2 : Real))|}

/-- The canonical minimum spectral spacing of the positive `H` by `H` window. -/
def goldenSeparation (H : Nat) : Real :=
  sInf (goldenWindowGapSet H)

private theorem coordinate_difference_abs_le {H m n : Nat}
    (hm : m ∈ Finset.Icc 1 H) (hn : n ∈ Finset.Icc 1 H) :
    |(((m : Int) - (n : Int) : Int) : Real)| ≤ (H : Real) - 1 := by
  simp only [Finset.mem_Icc] at hm hn
  have hm_lower : (1 : Real) ≤ (m : Real) := by exact_mod_cast hm.1
  have hm_upper : (m : Real) ≤ (H : Real) := by exact_mod_cast hm.2
  have hn_lower : (1 : Real) ≤ (n : Real) := by exact_mod_cast hn.1
  have hn_upper : (n : Real) ≤ (H : Real) := by exact_mod_cast hn.2
  rw [abs_le]
  constructor <;> push_cast <;> linarith

private theorem golden_difference_lower_bound {H : Nat} (hH : 2 ≤ H)
    {x y : Nat × Nat}
    (hx : x ∈ (Finset.Icc 1 H).product (Finset.Icc 1 H))
    (hy : y ∈ (Finset.Icc 1 H).product (Finset.Icc 1 H))
    (different : x ≠ y) :
    1 / (Real.goldenRatio * ((H : Real) - 1)) ≤
      |Real.goldenRatio * (x.1 : Real) + (x.2 : Real) -
        (Real.goldenRatio * (y.1 : Real) + (y.2 : Real))| := by
  let a : Int := (x.1 : Int) - (y.1 : Int)
  let b : Int := (x.2 : Int) - (y.2 : Int)
  have pair_nonzero : (a, b) ≠ (0, 0) := by
    intro zero_pair
    have ha : a = 0 := congrArg Prod.fst zero_pair
    have hb : b = 0 := congrArg Prod.snd zero_pair
    apply different
    apply Prod.ext <;> simp only [a, b] at ha hb <;> omega
  have first_nonzero :
      Real.goldenRatio * (a : Real) + (b : Real) ≠ 0 := by
    intro zero_reading
    have encoded_equal :
        Real.goldenRatio * (a : Real) + (b : Real) =
          Real.goldenRatio * ((0 : Int) : Real) + ((0 : Int) : Real) := by
      simpa using zero_reading
    exact pair_nonzero
      (irrational_slope_observer_injective Real.goldenRatio
        Real.goldenRatio_irrational encoded_equal)
  have conjugate_nonzero :
      Real.goldenConj * (a : Real) + (b : Real) ≠ 0 := by
    intro zero_reading
    have encoded_equal :
        Real.goldenConj * (a : Real) + (b : Real) =
          Real.goldenConj * ((0 : Int) : Real) + ((0 : Int) : Real) := by
      simpa using zero_reading
    exact pair_nonzero
      (irrational_slope_observer_injective Real.goldenConj
        Real.goldenConj_irrational encoded_equal)
  let normInteger : Int := b ^ 2 + a * b - a ^ 2
  have norm_identity :
      (Real.goldenRatio * (a : Real) + (b : Real)) *
          (Real.goldenConj * (a : Real) + (b : Real)) =
        (normInteger : Real) := by
    simp only [normInteger]
    push_cast
    calc
      _ = (a : Real) ^ 2 * (Real.goldenRatio * Real.goldenConj) +
          (a : Real) * (b : Real) *
            (Real.goldenRatio + Real.goldenConj) + (b : Real) ^ 2 := by ring
      _ = (b : Real) ^ 2 + (a : Real) * (b : Real) - (a : Real) ^ 2 := by
        rw [Real.goldenRatio_mul_goldenConj,
          Real.goldenRatio_add_goldenConj]
        ring
  have norm_integer_nonzero : normInteger ≠ 0 := by
    intro norm_zero
    have product_zero :
        (Real.goldenRatio * (a : Real) + (b : Real)) *
            (Real.goldenConj * (a : Real) + (b : Real)) = 0 := by
      rw [norm_identity, norm_zero]
      norm_num
    rcases mul_eq_zero.mp product_zero with first_zero | conjugate_zero
    · exact first_nonzero first_zero
    · exact conjugate_nonzero conjugate_zero
  have norm_at_least_one : (1 : Real) ≤ |(normInteger : Real)| := by
    exact_mod_cast Int.one_le_abs norm_integer_nonzero
  have absolute_product :
      |Real.goldenRatio * (a : Real) + (b : Real)| *
          |Real.goldenConj * (a : Real) + (b : Real)| =
        |(normInteger : Real)| := by
    rw [<- abs_mul, norm_identity]
  have product_at_least_one :
      (1 : Real) ≤
        |Real.goldenRatio * (a : Real) + (b : Real)| *
          |Real.goldenConj * (a : Real) + (b : Real)| := by
    rw [absolute_product]
    exact norm_at_least_one
  have hx_parts := Finset.mem_product.mp hx
  have hy_parts := Finset.mem_product.mp hy
  have a_bound : |(a : Real)| ≤ (H : Real) - 1 := by
    exact coordinate_difference_abs_le hx_parts.1 hy_parts.1
  have b_bound : |(b : Real)| ≤ (H : Real) - 1 := by
    exact coordinate_difference_abs_le hx_parts.2 hy_parts.2
  have conjugate_abs : |Real.goldenConj| = Real.goldenRatio ^ (-1 : Int) := by
    rw [abs_of_neg Real.goldenConj_neg, zpow_neg_one,
      Real.inv_goldenRatio]
  have inverse_plus_one : Real.goldenRatio ^ (-1 : Int) + 1 =
      Real.goldenRatio := by
    rw [zpow_neg_one, Real.inv_goldenRatio]
    linarith [Real.goldenRatio_add_goldenConj]
  have conjugate_bound :
      |Real.goldenConj * (a : Real) + (b : Real)| ≤
        Real.goldenRatio * ((H : Real) - 1) := by
    calc
      _ ≤ |Real.goldenConj * (a : Real)| + |(b : Real)| := abs_add_le _ _
      _ = |Real.goldenConj| * |(a : Real)| + |(b : Real)| := by rw [abs_mul]
      _ ≤ Real.goldenRatio ^ (-1 : Int) * ((H : Real) - 1) +
          ((H : Real) - 1) := by
        rw [conjugate_abs]
        exact add_le_add
          (mul_le_mul_of_nonneg_left a_bound (zpow_nonneg Real.goldenRatio_pos.le _))
          b_bound
      _ = Real.goldenRatio * ((H : Real) - 1) := by
        calc
          _ = (Real.goldenRatio ^ (-1 : Int) + 1) * ((H : Real) - 1) := by ring
          _ = _ := by rw [inverse_plus_one]
  have denominator_pos : 0 < Real.goldenRatio * ((H : Real) - 1) := by
    have hcast : (1 : Real) < (H : Real) := by
      exact_mod_cast (show 1 < H by omega)
    exact mul_pos Real.goldenRatio_pos (by linarith)
  have first_abs_nonneg :
      0 ≤ |Real.goldenRatio * (a : Real) + (b : Real)| := abs_nonneg _
  have product_upper :
      |Real.goldenRatio * (a : Real) + (b : Real)| *
          |Real.goldenConj * (a : Real) + (b : Real)| ≤
        |Real.goldenRatio * (a : Real) + (b : Real)| *
          (Real.goldenRatio * ((H : Real) - 1)) :=
    mul_le_mul_of_nonneg_left conjugate_bound first_abs_nonneg
  have reciprocal_bound :
      1 / (Real.goldenRatio * ((H : Real) - 1)) ≤
        |Real.goldenRatio * (a : Real) + (b : Real)| := by
    rw [div_le_iff₀ denominator_pos]
    exact product_at_least_one.trans product_upper
  have reading_difference :
      Real.goldenRatio * (a : Real) + (b : Real) =
        Real.goldenRatio * (x.1 : Real) + (x.2 : Real) -
          (Real.goldenRatio * (y.1 : Real) + (y.2 : Real)) := by
    simp only [a, b]
    push_cast
    ring
  rw [reading_difference] at reciprocal_bound
  exact reciprocal_bound

private theorem golden_window_gap_set_nonempty (H : Nat) (hH : 2 ≤ H) :
    (goldenWindowGapSet H).Nonempty := by
  refine ⟨|Real.goldenRatio * (1 : Real) + (1 : Real) -
      (Real.goldenRatio * (2 : Real) + (1 : Real))|, ?_⟩
  refine ⟨(1, 1), ?_, (2, 1), ?_, by decide, by norm_num⟩
  · simp
    omega
  · simp
    omega

/-- The minimum golden-slope gap in the positive `H` by `H` window is at
least the reciprocal of `goldenRatio * (H - 1)`. -/
theorem golden_separation_bound (H : Nat) (hH : 2 ≤ H) :
    1 / (Real.goldenRatio * ((H : Real) - 1)) ≤ goldenSeparation H := by
  apply le_csInf (golden_window_gap_set_nonempty H hH)
  intro d hd
  rcases hd with ⟨x, hx, y, hy, different, rfl⟩
  exact golden_difference_lower_bound hH hx hy different

#print axioms golden_separation_bound

end D5.S3.Observer.ArithmeticTomography.GoldenSlopeSeparation
