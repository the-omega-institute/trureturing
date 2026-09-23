/- GID: D5/S3/Combinatorics/LeastSquaresBinaryFit
   generality: G
   mirror-B: D5/B/S3/Combinatorics/LeastSquaresBinaryFit
   mirror-E: none(waiver:elementary-counting-argument)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Ring.Finset]
   utility: none
   digest: Zero slope fits a sample best exactly when its weighted index sum is balanced. -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace D5.S3.Combinatorics.LeastSquaresBinaryFit

/-- The total squared error of an affine fit to a finite rational sample. -/
def sqError (c : ℕ) (b : ℕ → ℚ) (α β : ℚ) : ℚ :=
  ∑ i ∈ Finset.range c, (b i - α - β * (i + 1)) ^ 2

/-- A finite sample admits an optimal affine fit whose slope is zero. -/
def ZeroSlopeOptimal (c : ℕ) (b : ℕ → ℚ) : Prop :=
  ∃ α₀ : ℚ, ∀ α β : ℚ, sqError c b α₀ 0 ≤ sqError c b α β

/-- The value sum and the position-weighted value sum obey the balance identity. -/
def BalancedPositions (c : ℕ) (b : ℕ → ℚ) : Prop :=
  2 * ∑ i ∈ Finset.range c, ((i : ℚ) + 1) * b i =
    ((c : ℚ) + 1) * ∑ i ∈ Finset.range c, b i

/-- Every nonempty finite rational sample has the stated optimality characterization. -/
def claim : Prop :=
  ∀ (c : ℕ) (b : ℕ → ℚ), 0 < c →
    (ZeroSlopeOptimal c b ↔ BalancedPositions c b)

/-- Zero slope is optimal exactly when the position-weighted sample sum is balanced. -/
theorem result : claim := by
  intro c b hc
  let w : ℚ := ∑ i ∈ Finset.range c, b i
  let S : ℚ := ∑ i ∈ Finset.range c, ((i : ℚ) + 1) * b i
  let ib : ℚ := ((c : ℚ) + 1) / 2
  let bb : ℚ := w / c
  let d : ℕ → ℚ := fun i => b i - bb
  let u : ℕ → ℚ := fun i => (i : ℚ) + 1 - ib
  let U : ℚ := ∑ i ∈ Finset.range c, (u i) ^ 2
  let C : ℚ := ∑ i ∈ Finset.range c, d i * u i
  have hcq_pos : (0 : ℚ) < (c : ℚ) := (Nat.cast_pos).2 hc
  have hcq : (c : ℚ) ≠ 0 := ne_of_gt hcq_pos
  have f1 : ∑ i ∈ Finset.range c, d i = 0 := by
    dsimp [d, bb]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp [hcq]
    show (∑ i ∈ Finset.range c, b i) - w = 0
    dsimp only [w]
    ring
  have position_sum :
      ∀ n : ℕ, ∑ i ∈ Finset.range n, ((i : ℚ) + 1) =
        (n : ℚ) * ((n : ℚ) + 1) / 2 := by
    intro n
    induction n with
    | zero =>
        simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero]
        ring
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        ring
  have f2 : ∑ i ∈ Finset.range c, u i = 0 := by
    dsimp [u, ib]
    rw [Finset.sum_sub_distrib, position_sum]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have weighted_center :
      ∑ i ∈ Finset.range c, b i * u i = S - ib * w := by
    dsimp [u, S, w]
    calc
      ∑ i ∈ Finset.range c, b i * ((i : ℚ) + 1 - ib) =
          ∑ i ∈ Finset.range c, (((i : ℚ) + 1) * b i - b i * ib) := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      _ = (∑ i ∈ Finset.range c, ((i : ℚ) + 1) * b i) -
          ∑ i ∈ Finset.range c, b i * ib := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ i ∈ Finset.range c, ((i : ℚ) + 1) * b i) -
          ib * ∑ i ∈ Finset.range c, b i := by
            rw [← Finset.sum_mul]
            ring
  have f3 : C = S - ib * w := by
    dsimp [C, d]
    calc
      ∑ i ∈ Finset.range c, (b i - bb) * u i =
          ∑ i ∈ Finset.range c, (b i * u i - bb * u i) := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      _ = (∑ i ∈ Finset.range c, b i * u i) -
          ∑ i ∈ Finset.range c, bb * u i := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ i ∈ Finset.range c, b i * u i) -
          bb * ∑ i ∈ Finset.range c, u i := by
            rw [Finset.mul_sum]
      _ = S - ib * w := by
            rw [f2, weighted_center]
            ring
  have key : ∀ α β : ℚ,
      sqError c b α β - ∑ i ∈ Finset.range c, (d i) ^ 2 =
        β ^ 2 * U + (c : ℚ) * (bb - α - β * ib) ^ 2 - 2 * β * C := by
    intro α β
    let γ : ℚ := bb - α - β * ib
    change sqError c b α β - ∑ i ∈ Finset.range c, (d i) ^ 2 =
      β ^ 2 * U + (c : ℚ) * γ ^ 2 - 2 * β * C
    have residual (i : ℕ) :
        b i - α - β * ((i : ℚ) + 1) = d i - β * u i + γ := by
      dsimp [d, u, γ]
      ring
    have beta_sum :
        ∑ i ∈ Finset.range c, β ^ 2 * (u i) ^ 2 = β ^ 2 * U := by
      dsimp [U]
      rw [Finset.mul_sum]
    have gamma_sum :
        ∑ _i ∈ Finset.range c, γ ^ 2 = (c : ℚ) * γ ^ 2 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have cross_sum :
        ∑ i ∈ Finset.range c, 2 * β * d i * u i = 2 * β * C := by
      calc
        ∑ i ∈ Finset.range c, 2 * β * d i * u i =
            ∑ i ∈ Finset.range c, (2 * β) * (d i * u i) := by
              apply Finset.sum_congr rfl
              intro i _hi
              ring
        _ = 2 * β * C := by
              dsimp [C]
              rw [Finset.mul_sum]
    have d_sum :
        ∑ i ∈ Finset.range c, 2 * γ * d i = 2 * γ * 0 := by
      calc
        ∑ i ∈ Finset.range c, 2 * γ * d i =
            (2 * γ) * ∑ i ∈ Finset.range c, d i := by
              rw [Finset.mul_sum]
        _ = 2 * γ * 0 := by rw [f1]
    have u_sum :
        ∑ i ∈ Finset.range c, 2 * β * γ * u i = 2 * β * γ * 0 := by
      calc
        ∑ i ∈ Finset.range c, 2 * β * γ * u i =
            (2 * β * γ) * ∑ i ∈ Finset.range c, u i := by
              rw [Finset.mul_sum]
        _ = 2 * β * γ * 0 := by rw [f2]
    have expanded :
        sqError c b α β =
          (∑ i ∈ Finset.range c, (d i) ^ 2) + β ^ 2 * U +
            (c : ℚ) * γ ^ 2 - 2 * β * C := by
      calc
        sqError c b α β =
            ∑ i ∈ Finset.range c,
              ((d i) ^ 2 + β ^ 2 * (u i) ^ 2 + γ ^ 2 -
                2 * β * d i * u i + 2 * γ * d i - 2 * β * γ * u i) := by
                  dsimp [sqError]
                  apply Finset.sum_congr rfl
                  intro i _hi
                  rw [residual]
                  ring
        _ = (∑ i ∈ Finset.range c, (d i) ^ 2) +
            (∑ i ∈ Finset.range c, β ^ 2 * (u i) ^ 2) +
            (∑ _i ∈ Finset.range c, γ ^ 2) -
            (∑ i ∈ Finset.range c, 2 * β * d i * u i) +
            (∑ i ∈ Finset.range c, 2 * γ * d i) -
            ∑ i ∈ Finset.range c, 2 * β * γ * u i := by
              simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        _ = (∑ i ∈ Finset.range c, (d i) ^ 2) + β ^ 2 * U +
            (c : ℚ) * γ ^ 2 - 2 * β * C := by
              rw [beta_sum, gamma_sum, cross_sum, d_sum, u_sum]
              ring
    rw [expanded]
    ring
  have base_value :
      sqError c b bb 0 = ∑ i ∈ Finset.range c, (d i) ^ 2 := by
    dsimp [sqError, d]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have U_nonneg : 0 ≤ U := by
    dsimp [U]
    apply Finset.sum_nonneg
    intro i _hi
    exact sq_nonneg (u i)
  have optimal_of_C : C = 0 → ZeroSlopeOptimal c b := by
    intro hC
    refine ⟨bb, ?_⟩
    intro α β
    have hkey := key α β
    rw [hC] at hkey
    have hβ : 0 ≤ β ^ 2 * U := mul_nonneg (sq_nonneg β) U_nonneg
    have hγ : 0 ≤ (c : ℚ) * (bb - α - β * ib) ^ 2 :=
      mul_nonneg (le_of_lt hcq_pos) (sq_nonneg (bb - α - β * ib))
    rw [base_value]
    nlinarith
  have C_of_optimal : ZeroSlopeOptimal c b → C = 0 := by
    rintro ⟨α₀, hopt⟩
    by_cases hc_one : c = 1
    · subst c
      dsimp [C, u, ib]
      norm_num [Finset.sum_range_succ]
    · have hc_two : 2 ≤ c := by
        exact (Nat.succ_le_iff).2 (lt_of_le_of_ne hc (Ne.symm hc_one))
      have hc_two_q : (2 : ℚ) ≤ (c : ℚ) := (Nat.cast_le).2 hc_two
      have hu_zero_neg : u 0 < 0 := by
        dsimp [u, ib]
        linarith
      have hu_zero_sq : 0 < (u 0) ^ 2 := by
        nlinarith [hu_zero_neg]
      have hsingle : (u 0) ^ 2 ≤ U := by
        dsimp [U]
        exact Finset.single_le_sum (fun i _hi => sq_nonneg (u i))
          (Finset.mem_range.2 hc)
      have hU_pos : 0 < U := lt_of_lt_of_le hu_zero_sq hsingle
      by_contra hC
      let β : ℚ := C / U
      let α : ℚ := bb - β * ib
      have hgamma : bb - α - β * ib = 0 := by
        dsimp [α]
        ring
      have hfit_diff :
          sqError c b α β - ∑ i ∈ Finset.range c, (d i) ^ 2 =
            -(C ^ 2 / U) := by
        calc
          sqError c b α β - ∑ i ∈ Finset.range c, (d i) ^ 2 =
              β ^ 2 * U + (c : ℚ) * (bb - α - β * ib) ^ 2 -
                2 * β * C := key α β
          _ = -(C ^ 2 / U) := by
                rw [hgamma]
                dsimp [β]
                field_simp [ne_of_gt hU_pos]
                ring
      have hC_sq : 0 < C ^ 2 := by
        positivity
      have hfit_lt :
          sqError c b α β < ∑ i ∈ Finset.range c, (d i) ^ 2 := by
        have hquot : 0 < C ^ 2 / U := div_pos hC_sq hU_pos
        linarith
      have hzero_diff := key α₀ 0
      norm_num at hzero_diff
      have hzero_ge :
          ∑ i ∈ Finset.range c, (d i) ^ 2 ≤ sqError c b α₀ 0 := by
        have hnonneg : 0 ≤ (c : ℚ) * (bb - α₀) ^ 2 :=
          mul_nonneg (le_of_lt hcq_pos) (sq_nonneg (bb - α₀))
        nlinarith
      have hopt_fit := hopt α β
      linarith
  constructor
  · intro hopt
    have hC : C = 0 := C_of_optimal hopt
    change 2 * S = ((c : ℚ) + 1) * w
    have hcenter : S - ib * w = 0 := by
      nlinarith [f3]
    dsimp [ib] at hcenter
    field_simp at hcenter
    linarith
  · intro hbalanced
    apply optimal_of_C
    change 2 * S = ((c : ℚ) + 1) * w at hbalanced
    have hcenter : S - ib * w = 0 := by
      dsimp [ib]
      field_simp
      linarith
    nlinarith [f3]

end D5.S3.Combinatorics.LeastSquaresBinaryFit
