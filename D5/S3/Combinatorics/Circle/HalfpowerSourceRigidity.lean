/- GID: D5/S3/Combinatorics/Circle/HalfpowerSourceRigidity
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/HalfpowerSourceRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort]
   utility: none
   digest: Restricted actual-source factor rigidity excludes low 4/1 successors. -/
module
public import D5.S3.Combinatorics.Circle.OriginalRowBounds
import all D5.S3.Combinatorics.Circle.M5SourceRows

/-! # Restricted halfpower source rigidity

Lengths six and seven equal to one, and the original seed-eight lower bound,
are hypotheses. They are not consequences of arbitrary initial source tests.
All cuts, seeds and labels are the original physical ones, including the
closing cut at k. No five-pair source or bound of seed eight by seed zero is
used. The retained executed hardSH/LOW history has a separate, still unproved
population problem; no continuation or existence assertion is made here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

namespace D5.S3.Combinatorics.Circle.HalfpowerSourceRigidity

open SourceWidth M5FullWordConsumer OriginalRowBounds

/- These are the cardinality-generic parts of the physical recurrence in
M5SourceRows / OriginalSourceRows. Their five-pair/source wrappers are not
instantiated. Each helper below is consumed by the source theorem. -/

private theorem actual_parent_next {k t : ℕ} (x : Fin k) (i : ℕ)
    (hi : i < (largeOffsets t x).card) :
    advance (sourceParent t x i) (sourceLength t x i + 1) =
      sourceParent t x (i + 1) := by
  have hlt := cut_strict x
    (rfl : (largeOffsets t x).card = (largeOffsets t x).card)
    (show i < i + 1 by omega) (show i + 1 ≤ (largeOffsets t x).card by omega)
  have he : sourceOffset t x i + (sourceLength t x i + 1) =
      sourceOffset t x (i + 1) := by
    dsimp only [sourceOffset, sourceLength] at *
    omega
  simp only [sourceParent, advance_add, he]

private theorem large_successor_magnitude {k t : ℕ} (hk : 2 ≤ k)
    (y : Fin k) (hy : quarter k ≤ |actualSource k t y|) :
    |actualSource k t (advance y 1)| =
      modulus k - 2 * |actualSource k t y| := by
  by_cases hn : actualSource k t y < 0
  · have hy' : actualSource k t y ≤ -quarter k := by
      rw [abs_of_neg hn] at hy
      omega
    obtain ⟨hs, hp⟩ := source_negative_step k t hk y hy'
    rw [abs_of_pos hp, hs, abs_of_neg hn]
    ring
  · have hq := (modulus_quarter k hk).2.2.2
    have hyn : 0 ≤ actualSource k t y := by omega
    have hp : 0 < actualSource k t y := by
      rw [abs_of_nonneg hyn] at hy
      omega
    have hy' : quarter k ≤ actualSource k t y := by
      simpa only [abs_of_pos hp] using hy
    obtain ⟨hs, hsneg⟩ := source_positive_step k t hk y hy'
    rw [abs_of_neg hsneg, hs, abs_of_pos hp]
    ring

/-- Literal recurrence of any real physical row. Its successor may be the
closing seed: i+1 is allowed to equal the full actual LARGE cardinality. -/
private theorem actual_seed_recurrence {k t : ℕ} (hk : 2 ≤ k) (x : Fin k)
    (hx : quarter k ≤ |actualSource k t x|) (i : ℕ)
    (hi : i < (largeOffsets t x).card) :
    sourceSeed t x (i + 1) = modulus k -
      (2 : ℤ) ^ (sourceLength t x i + 1) * sourceSeed t x i := by
  have hr : OwnRow k t (sourceParent t x i) (sourceLength t x i) :=
    cut_own_row x rfl hx i hi
  have hn := actual_parent_next x i hi
  have hlarge : quarter k ≤ |actualSource k t (sourceParent t x (i + 1))| := by
    rw [← hn]
    exact hr.terminal_large
  have hmag : |actualSource k t (sourceParent t x (i + 1))| =
      (2 : ℤ) ^ sourceLength t x i * sourceSeed t x i := by
    rw [← hn, row_terminal hk hr, abs_mul,
      abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℤ) ≤ 2) _)]
    rfl
  change |actualSource k t (advance (sourceParent t x (i + 1)) 1)| = _
  rw [large_successor_magnitude hk _ hlarge, hmag, pow_succ]
  ring

private theorem actual_seed_minimum {k t L : ℕ} {a b : ℤ} {p : Fin k}
    (core : RowCore k t L a b p) (x : Fin k) (i : ℕ) :
    a ≤ sourceSeed t x i := by
  let y := advance (sourceParent t x i) 1
  change a ≤ |actualSource k t y|
  by_cases hn : actualSource k t y < 0
  · simpa only [abs_of_neg hn] using core.negative_minimum y hn
  · have hp : 0 < actualSource k t y := by
      have hz := core.nonzero y
      omega
    rw [abs_of_pos hp]
    exact core.a_le_b.trans (core.positive_minimum y hp)

set_option maxHeartbeats 800000 in
/-- Remote initial-row data force two actual factors and exclude low
successors of every actual negative-4/positive-1 pair. All displayed bounds
are cross-multiplied integer inequalities. The quantified pair includes the
case i+2 equals the actual LARGE cardinality, hence the real closing seed.

This is a restriction on sources satisfying F=4, g_src=2 and the ORIGINAL
seed-eight guard. It asserts neither population of a retained execution
history nor existence/viability of any 4/2 supplier. -/
theorem restricted_source_rigidity {k t : ℕ} {a b : ℤ} {p d x : Fin k}
    (core : RowCore k t 2 a b p)
    (b_attained : ∃ v : Fin k, actualSource k t v = b)
    (d_minimum : ∀ v : Fin k, actualSource k t d ≤ actualSource k t v)
    (x_large : quarter k ≤ actualSource k t x)
    (real_rows : 8 ≤ (largeOffsets t x).card)
    (incoming_d : sourceParent t x 1 = d)
    (len0 : sourceLength t x 0 = 2)
    (len1 : sourceLength t x 1 = 2)
    (len2 : sourceLength t x 2 = 2)
    (len4 : sourceLength t x 4 = 1)
    (hard : 10 * a < modulus k)
    (delta_positive : 0 < b - sourceSeed t x 0)
    (w_upper : sourceSeed t x 4 ≤ 2 * a - 3)
    (len6 : sourceLength t x 6 = 1)
    (len7 : sourceLength t x 7 = 1)
    (original_seed8_guard : 2 * b + 1 ≤ sourceSeed t x 8) :
    let N := modulus k
    let z := sourceSeed t x 0
    let delta := b - z
    sourceLength t x 5 = 0 ∧ sourceLength t x 3 = 1 ∧
      19 * N + 2 * b + 384 ≤ 256 * a ∧
      16 * N + 135 < 10240 * delta ∧
      262160 * delta ≤ 467 * N - 9 ∧
      29077 * N + 1 ≤ 262160 * z ∧ 640 * z < 71 * N ∧
      (∀ i : ℕ, i + 1 < (largeOffsets t x).card →
        0 < actualSource k t (sourceParent t x i) →
        sourceLength t x i = 2 → sourceLength t x (i + 1) = 0 →
        3 * N + 2 * b + 384 ≤ 16 * sourceSeed t x (i + 2) ∧
          N < 5 * sourceSeed t x (i + 2) ∧
          2 * N + z + 1 < 14 * sourceSeed t x (i + 2)) := by
  let N := modulus k
  let T : ℕ → ℤ := sourceSeed t x
  let delta := b - T 0
  change sourceLength t x 5 = 0 ∧ sourceLength t x 3 = 1 ∧
    19 * N + 2 * b + 384 ≤ 256 * a ∧
    16 * N + 135 < 10240 * delta ∧ 262160 * delta ≤ 467 * N - 9 ∧
    29077 * N + 1 ≤ 262160 * T 0 ∧ 640 * T 0 < 71 * N ∧
    (∀ i : ℕ, i + 1 < (largeOffsets t x).card →
      0 < actualSource k t (sourceParent t x i) →
      sourceLength t x i = 2 → sourceLength t x (i + 1) = 0 →
      3 * N + 2 * b + 384 ≤ 16 * T (i + 2) ∧
        N < 5 * T (i + 2) ∧ 2 * N + T 0 + 1 < 14 * T (i + 2))
  change 10 * a < N at hard
  change 0 < delta at delta_positive
  change T 4 ≤ 2 * a - 3 at w_upper
  change 2 * b + 1 ≤ T 8 at original_seed8_guard
  have hdelta : delta = b - T 0 := rfl
  have hk := core.dimension
  have hQ := (modulus_quarter k hk).2.2.2
  have hN : 3 ≤ N := by
    have hmod := (modulus_quarter k hk).1
    change 3 ≤ modulus k
    omega
  have ha := core.a_positive
  have hb : 0 < b := lt_of_lt_of_le ha core.a_le_b
  have hx : quarter k ≤ |actualSource k t x| :=
    x_large.trans (le_abs_self _)
  have hrec (i : ℕ) (hi : i < (largeOffsets t x).card) :
      T (i + 1) = N - (2 : ℤ) ^ (sourceLength t x i + 1) * T i :=
    actual_seed_recurrence hk x hx i hi
  -- The attained positive minimum identifies the actual incoming seed.
  obtain ⟨_, hd, _, hdvalue⟩ := source_extrema k t hk a b ha hb
    core.negative_minimum core.positive_minimum core.negative_attained
    b_attained p d core.p_maximum d_minimum
  obtain ⟨hdstep, hdpos⟩ := source_negative_step k t hk d hd
  have seed1 : T 1 = b := by
    change |actualSource k t (advance (sourceParent t x 1) 1)| = b
    rw [incoming_d, abs_of_pos hdpos, hdstep]
    omega
  have e0 := hrec 0 (by omega)
  have e1 := hrec 1 (by omega)
  have e2 := hrec 2 (by omega)
  have e4 := hrec 4 (by omega)
  have e6 := hrec 6 (by omega)
  have e7 := hrec 7 (by omega)
  norm_num [len0] at e0
  norm_num [len1] at e1
  norm_num [len2] at e2
  norm_num [len4] at e4
  norm_num [len6] at e6
  norm_num [len7] at e7
  have hz : 9 * T 0 = N - delta := by linarith only [hdelta, e0, seed1]
  have hbN : 9 * b = N + 8 * delta := by linarith only [hdelta, e0, seed1]
  have hn : 9 * T 2 = N - 64 * delta := by linarith only [e1, seed1, hbN]
  have hnmin : a ≤ T 2 := actual_seed_minimum core x 2
  have hu_lower : 3 * N + 2 * b + 1 ≤ 16 * T 6 := by
    linarith only [e6, e7, original_seed8_guard]
  have hu_fifth : N < 5 * T 6 := by
    linarith only [hu_lower, hbN, delta_positive, hN]
  have hw_fifth : 5 * T 4 + 15 < N := by linarith only [hard, w_upper]
  have len5_le : sourceLength t x 5 ≤ 2 :=
    (computed_row_bounds core x hx 5 (by omega)).1
  have len5_zero : sourceLength t x 5 = 0 := by
    have hc : sourceLength t x 5 = 0 ∨ sourceLength t x 5 = 1 ∨
        sourceLength t x 5 = 2 := by omega
    rcases hc with h0 | h1 | h2
    · exact h0
    · have e5 := hrec 5 (by omega)
      norm_num [h1] at e5
      linarith only [e4, e5, hu_fifth, hw_fifth, hN]
    · have e5 := hrec 5 (by omega)
      norm_num [h2] at e5
      linarith only [e4, e5, hu_fifth, hw_fifth, hN]
  have e5 := hrec 5 (by omega)
  norm_num [len5_zero] at e5
  have hw_lower : 19 * N + 2 * b + 1 ≤ 128 * T 4 := by
    linarith only [e4, e5, hu_lower]
  have ha_strong : 19 * N + 2 * b + 385 ≤ 256 * a := by
    linarith only [hw_lower, w_upper]
  have len3_le : sourceLength t x 3 ≤ 2 :=
    (computed_row_bounds core x hx 3 (by omega)).1
  have len3_one : sourceLength t x 3 = 1 := by
    have hc : sourceLength t x 3 = 0 ∨ sourceLength t x 3 = 1 ∨
        sourceLength t x 3 = 2 := by omega
    rcases hc with h0 | h1 | h2
    · have e3 := hrec 3 (by omega)
      norm_num [h0] at e3
      have h14 : 14 * a ≤ N - 3 := by linarith only [e2, e3, hnmin, w_upper]
      linarith only [ha_strong, h14, hb, hN]
    · exact h1
    · have e3 := hrec 3 (by omega)
      norm_num [h2] at e3
      have hw_small : 9 * T 4 < N := by linarith only [e2, e3, hn, delta_positive]
      linarith only [hw_small, hw_lower, hb, hN]
  have e3 := hrec 3 (by omega)
  norm_num [len3_one] at e3
  have hw_eq : 9 * T 4 = 5 * N - 2048 * delta := by linarith only [e2, e3, hn]
  have hu_eq : 9 * T 6 = 31 * N - 16384 * delta := by linarith only [e4, e5, hw_eq]
  have ha0_eq : 9 * T 8 = 469 * N - 262144 * delta := by linarith only [e6, e7, hu_eq]
  have hdl : 16 * N + 135 < 10240 * delta := by linarith only [hw_eq, hw_fifth]
  have hdu : 262160 * delta ≤ 467 * N - 9 := by
    linarith only [ha0_eq, hbN, original_seed8_guard]
  have hzl : 29077 * N + 1 ≤ 262160 * T 0 := by linarith only [hz, hdu]
  have hzu : 640 * T 0 < 71 * N := by linarith only [hz, hdl]
  refine ⟨len5_zero, len3_one, by linarith only [ha_strong], hdl, hdu, hzl, hzu, ?_⟩
  intro i hi hpositive hnegative4 hpositive1
  have hi0 : i < (largeOffsets t x).card := by omega
  have hr : OwnRow k t (sourceParent t x i) (sourceLength t x i) :=
    cut_own_row x rfl hx i hi0
  have hp_large : quarter k ≤ actualSource k t (sourceParent t x i) := by
    simpa only [abs_of_pos hpositive] using hr.parent_large
  have hsneg := (source_positive_step k t hk _ hp_large).2
  have hS : a ≤ T i := by
    change a ≤ |actualSource k t (advance (sourceParent t x i) 1)|
    simpa only [abs_of_neg hsneg] using core.negative_minimum _ hsneg
  have ei := hrec i hi0
  have ej := hrec (i + 1) hi
  norm_num [hnegative4] at ei
  norm_num [hpositive1, Nat.add_assoc] at ej
  have hR : T (i + 2) = 16 * T i - N := by linarith only [ei, ej]
  have hRlower : 3 * N + 2 * b + 384 ≤ 16 * T (i + 2) := by
    linarith only [hR, hS, ha_strong]
  have hRfifth : N < 5 * T (i + 2) := by
    linarith only [hRlower, hbN, delta_positive, hN]
  refine ⟨hRlower, hRfifth, ?_⟩
  linarith only [hRfifth, hz, delta_positive, hN]

end D5.S3.Combinatorics.Circle.HalfpowerSourceRigidity
