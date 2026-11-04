/- GID: D5/S3/Combinatorics/Circle/OriginalRowBounds
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/OriginalRowBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort]
   utility: none
   digest: Attained source minima bound every computed physical own-row factor. -/
module
public import D5.S3.Combinatorics.Circle.M5SourceRows
import all D5.S3.Combinatorics.Circle.M5SourceRows

/-! # OriginalRowBounds
Uniform own-row bounds on the original centered source, independent of the
number of LARGE pairs and of any upper bound on the actual seed at row eight.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

namespace D5.S3.Combinatorics.Circle.OriginalRowBounds

open SourceWidth M5FullWordConsumer

/-- The source assumptions needed for the uniform row estimate. The maximum
is an actual physical label, and its prescribed row is an actual OwnRow. -/
structure RowCore (k t L : ℕ) (a b : ℤ) (p : Fin k) : Prop where
  dimension : 2 ≤ k
  nonzero : ∀ i : Fin k, actualSource k t i ≠ 0
  a_positive : 0 < a
  a_le_b : a ≤ b
  negative_minimum : ∀ i, actualSource k t i < 0 → a ≤ -actualSource k t i
  positive_minimum : ∀ i, 0 < actualSource k t i → b ≤ actualSource k t i
  negative_attained : ∃ i, actualSource k t i = -a
  p_maximum : ∀ i, actualSource k t i ≤ actualSource k t p
  p_row : OwnRow k t p L

private theorem own_row_length_le {k t L : ℕ} {a b : ℤ} {p y : Fin k}
    (h : RowCore k t L a b p) {len : ℕ} (hr : OwnRow k t y len) : len ≤ L := by
  obtain ⟨v, hv, hva⟩ := negative_minimum_parent k t h.dimension a
    h.a_positive h.negative_minimum h.negative_attained
  have hmax := h.p_maximum v
  have hp : quarter k ≤ actualSource k t p := hv.trans hmax
  obtain ⟨hstep, hneg⟩ := source_positive_step k t h.dimension p hp
  have hmin := h.negative_minimum (advance p 1) hneg
  have hseed : actualSource k t (advance p 1) = -a := by omega
  have hthreshold : quarter k ≤ (2 : ℤ) ^ L * a := by
    have ht := h.p_row.terminal_large
    rw [row_terminal h.dimension h.p_row, hseed, abs_mul,
      abs_of_nonneg (pow_nonneg (by norm_num) _), abs_neg,
      abs_of_pos h.a_positive] at ht
    exact ht
  have hseedmin : a ≤ |actualSource k t (advance y 1)| := by
    by_cases hn : actualSource k t (advance y 1) < 0
    · simpa only [abs_of_neg hn] using h.negative_minimum (advance y 1) hn
    · have hp' : 0 < actualSource k t (advance y 1) := by
        have hz := h.nonzero (advance y 1)
        omega
      rw [abs_of_pos hp']
      exact h.a_le_b.trans (h.positive_minimum (advance y 1) hp')
  by_contra hlong
  have hsmall := hr.small L (by omega)
  rw [row_value h.dimension hr L (by omega), abs_mul,
    abs_of_nonneg (pow_nonneg (by norm_num) _)] at hsmall
  have hh := mul_le_mul_of_nonneg_left hseedmin
    (pow_nonneg (by norm_num : (0 : ℤ) ≤ 2) L)
  omega

/-- Every row computed by the increasing actual LARGE cuts has length at
most L, dyadic factor at most 2^L, and its true terminal magnitude lies in
[Q,C]. No sign, nonemptiness or last-row assumption is imposed on the row. -/
theorem computed_row_bounds {k t L : ℕ} {a b : ℤ} {p : Fin k}
    (h : RowCore k t L a b p) (x : Fin k)
    (hx : quarter k ≤ |actualSource k t x|) (i : ℕ)
    (hi : i < (largeOffsets t x).card) :
    let s := actualSource k t
    let c := |s (advance (sourceParent t x i) 1)|
    let f := (2 : ℤ) ^ sourceLength t x i
    sourceLength t x i ≤ L ∧ 1 ≤ f ∧ f ≤ (2 : ℤ) ^ L ∧
      quarter k ≤ f * c ∧ f * c ≤ halfCapacity k := by
  dsimp only
  have hr : OwnRow k t (sourceParent t x i) (sourceLength t x i) :=
    cut_own_row x rfl hx i hi
  have hlen := own_row_length_le h hr
  have hterminal := row_terminal h.dimension hr
  have habs : |actualSource k t
      (advance (sourceParent t x i) (sourceLength t x i + 1))| =
      (2 : ℤ) ^ sourceLength t x i *
        |actualSource k t (advance (sourceParent t x i) 1)| := by
    rw [hterminal, abs_mul, abs_of_nonneg (pow_nonneg (by norm_num) _)]
  have hb := source_bounds k t h.dimension
    (advance (sourceParent t x i) (sourceLength t x i + 1))
  refine ⟨hlen, one_le_pow₀ (by norm_num),
    pow_le_pow_right₀ (by norm_num) hlen, ?_, ?_⟩
  · rw [← habs]
    exact hr.terminal_large
  · rw [← habs]
    exact abs_le.mpr hb

end D5.S3.Combinatorics.Circle.OriginalRowBounds
