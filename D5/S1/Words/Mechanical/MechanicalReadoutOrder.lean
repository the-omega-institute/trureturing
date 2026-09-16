/- GID: D5/S1/Words/Mechanical/MechanicalReadoutOrder
   generality: G
   mirror-B: D5/B/S1/Words/Mechanical/MechanicalReadoutOrder
   mirror-E: none(waiver:actual-dynamics-weight-cone-classification)
   anchors: []
   utility: none
   digest: Realized mechanical-bit exchanges characterize exactly which additive readouts preserve local slope order. -/

import D5.S1.Words.Mechanical.MechanicalSlopeSensitivity

/-!
# The order cone of numerical mechanical-bit readouts

For a fixed irrational slope and a finite nonempty observation horizon,
local monotonicity for every phase forces every successive weight drop and
the terminal weight to be nonnegative. The necessity proof realizes each
constraint on an actual swept interval of the rotation, rather than on an
arbitrary binary vector. The converse derives summation by parts from the
actual cumulative floors. Summation by parts itself is classical background.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S1.Words.Mechanical.MechanicalReadoutOrder

open Set Finset
open scoped BigOperators
open D5.S1.Words.Mechanical
open D5.S1.Words.Mechanical.MechanicalSlopeSensitivity

/-- Finite additive numerical readout of the actual integer-valued letters.
For slopes in [0,1), these letters are the actual binary observations. -/
def weightedPrefix (weights : ℕ → ℝ) (alpha x : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ range n, weights j * (lowerMechanicalLetter alpha x j : ℝ)

/-- A finite additive readout preserves all sufficiently small upward slope
changes at every phase exactly when its weights decrease to a nonnegative
last weight. Arbitrary real weights are allowed in the statement. -/
theorem local_order_iff_decreasing_weights
    (alpha : ℝ) (halpha : Irrational alpha) (h0 : 0 < alpha) (h1 : alpha < 1)
    (weights : ℕ → ℝ) (m : ℕ) :
    (∃ radius : ℝ, 0 < radius ∧ alpha + radius < 1 ∧
      ∀ delta : ℝ, 0 ≤ delta → delta ≤ radius → ∀ x ∈ Ico (0 : ℝ) 1,
        weightedPrefix weights alpha x (m + 1) ≤
          weightedPrefix weights (alpha + delta) x (m + 1)) ↔
      0 ≤ weights m ∧ ∀ k < m, weights (k + 1) ≤ weights k := by
  classical
  constructor
  · rintro ⟨r, hr, _, hmono⟩
    obtain ⟨s, hs, _, hlaw⟩ := local_slope_disagreement_law alpha halpha h0 h1 (m + 1)
    let delta := min r s / 2
    have hd : 0 < delta := div_pos (lt_min hr hs) (by norm_num)
    have hdr : delta ≤ r := by dsimp [delta]; linarith [min_le_left r s, lt_min hr hs]
    have hds : delta ≤ s := by dsimp [delta]; linarith [min_le_right r s, lt_min hr hs]
    obtain ⟨hset, _, _, hpattern⟩ := hlaw delta hd.le hds
    have hdrop (k : ℕ) (hk : k < m + 1) :
        0 ≤ weights k - if k + 1 < m + 1 then weights (k + 1) else 0 := by
      let i : Fin (m + 1) := ⟨k, hk⟩
      let c : ℝ := 1 - Int.fract (((k + 1 : ℕ) : ℝ) * alpha)
      let x := c - ((k + 1 : ℕ) : ℝ) * delta / 2
      have hlen : 0 < ((k + 1 : ℕ) : ℝ) * delta := mul_pos (by positivity) hd
      have hx : x ∈ Ico (c - ((k + 1 : ℕ) : ℝ) * delta) c := by
        dsimp [x]
        constructor <;> linarith
      have hxdis : x ∈ slopeDisagreement alpha (alpha + delta) (m + 1) := by
        rw [hset]
        exact Set.mem_iUnion.mpr ⟨i, hx⟩
      have hx01 : x ∈ Ico (0 : ℝ) 1 := hxdis.1
      have heq : weightedPrefix weights (alpha + delta) x (m + 1) -
          weightedPrefix weights alpha x (m + 1) =
          weights k - if k + 1 < m + 1 then weights (k + 1) else 0 := by
        unfold weightedPrefix
        rw [← sum_sub_distrib]
        calc
          (∑ j ∈ range (m + 1),
              (weights j * (lowerMechanicalLetter (alpha + delta) x j : ℝ) -
                weights j * (lowerMechanicalLetter alpha x j : ℝ))) =
              ∑ j ∈ range (m + 1), weights j *
                ((if j = k then (1 : ℝ) else 0) -
                  (if j = k + 1 then (1 : ℝ) else 0)) := by
            apply sum_congr rfl
            intro j hj
            have hp := hpattern i x hx ⟨j, mem_range.mp hj⟩
            have hpR := congrArg (fun z : ℤ => (z : ℝ)) hp
            simp only [Int.cast_sub, apply_ite, Int.cast_one, Int.cast_zero] at hpR
            rw [← mul_sub]
            exact congrArg (weights j * ·) hpR
          _ = weights k - if k + 1 < m + 1 then weights (k + 1) else 0 := by
            simp [mul_sub, mul_ite, sum_sub_distrib, hk]
      rw [← heq]
      exact sub_nonneg.mpr (hmono delta hd.le hdr x hx01)
    constructor
    · simpa using hdrop m (Nat.lt_succ_self m)
    · intro k hk
      have h := hdrop k (Nat.lt_succ_of_lt hk)
      rw [if_pos (by omega)] at h
      exact sub_nonneg.mp h
  · rintro ⟨hlast, hweights⟩
    refine ⟨(1 - alpha) / 2, by linarith, by linarith, ?_⟩
    intro delta hd _ x _
    let D : ℕ → ℝ := fun k =>
      (⌊x + (k : ℝ) * (alpha + delta)⌋ : ℝ) - (⌊x + (k : ℝ) * alpha⌋ : ℝ)
    have hD0 : D 0 = 0 := by simp [D]
    have hD (k : ℕ) : 0 ≤ D k := by
      apply sub_nonneg.mpr
      exact_mod_cast (Int.floor_mono
        (show x + (k : ℝ) * alpha ≤ x + (k : ℝ) * (alpha + delta) by
          nlinarith [mul_nonneg (Nat.cast_nonneg (R := ℝ) k) hd]))
    have hparts : ∀ N : ℕ,
        (∑ j ∈ range N, weights j * (D (j + 1) - D j)) =
          weights N * D N + ∑ j ∈ range N, (weights j - weights (j + 1)) * D (j + 1) := by
      intro N
      induction N with
      | zero => simp [hD0]
      | succ N ih =>
          rw [sum_range_succ, ih, sum_range_succ]
          ring
    have heq : weightedPrefix weights (alpha + delta) x (m + 1) -
        weightedPrefix weights alpha x (m + 1) =
        weights m * D (m + 1) +
          ∑ j ∈ range m, (weights j - weights (j + 1)) * D (j + 1) := by
      unfold weightedPrefix
      rw [← sum_sub_distrib]
      calc
        (∑ j ∈ range (m + 1),
            (weights j * (lowerMechanicalLetter (alpha + delta) x j : ℝ) -
              weights j * (lowerMechanicalLetter alpha x j : ℝ))) =
            ∑ j ∈ range (m + 1), weights j * (D (j + 1) - D j) := by
          apply sum_congr rfl
          intro j hj
          dsimp [D, lowerMechanicalLetter]
          push_cast
          ring
        _ = _ := by rw [sum_range_succ, hparts m]; ring
    apply sub_nonneg.mp
    rw [heq]
    exact add_nonneg (mul_nonneg hlast (hD (m + 1)))
      (sum_nonneg fun j hj => mul_nonneg
        (sub_nonneg.mpr (hweights j (mem_range.mp hj))) (hD (j + 1)))

#print axioms weightedPrefix
#print axioms local_order_iff_decreasing_weights

end D5.S1.Words.Mechanical.MechanicalReadoutOrder
