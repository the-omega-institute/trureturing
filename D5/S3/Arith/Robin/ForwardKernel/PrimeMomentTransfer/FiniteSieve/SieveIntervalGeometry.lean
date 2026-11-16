/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveIntervalGeometry
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveIntervalGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sieve interval sums have exact translation laws and finite endpoint grids. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.FiniteSieveDefs

/-! Integer interval geometry and translation invariance for uniform finite sieve sums. -/

open scoped BigOperators

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

/-- The integer points in a nonnegative scaled interval satisfy the unit endpoint error bound. -/
theorem sieve_interval_card_le (H a b : ℝ) (hH : 0 < H) (ha : 0 ≤ a) (hab : a ≤ b) :
    ((points H a b).card : ℝ) ≤ H * (b - a) + 1 := by
  have hf := Nat.floor_mono (mul_le_mul_of_nonneg_right hab hH.le)
  rw [points, Nat.card_Ioc, Nat.cast_sub hf]
  have hb := Nat.floor_le (mul_nonneg (ha.trans hab) hH.le)
  have ha' := Nat.lt_floor_add_one (a * H)
  rw [show H * (b - a) = b * H - a * H by ring]
  linarith only [hb, ha']

/-- Translating a block of shifts preserves every moment under the uniform residue average. -/
private theorem sieve_interval_moment_translate (Q : ℕ+) (t n r : ℕ) :
    sieveExpectation Q (fun x => (∑ d ∈ Finset.Ioc t (t + n), sieveVariable Q d x) ^ r) =
      sieveExpectation Q (fun x => sieveIntervalSum Q 1 0 n x ^ r) := by
  have hshift (x : ZMod (Q : ℕ)) :
      (∑ d ∈ Finset.Ioc t (t + n), sieveVariable Q d x) =
        ∑ d ∈ points 1 0 n, sieveVariable Q d (x + (t : ZMod (Q : ℕ))) := by
    rw [show Finset.Ioc t (t + n) = (Finset.Ioc 0 n).map (addLeftEmbedding t) by
      rw [Finset.map_add_left_Ioc, add_zero], Finset.sum_map]
    simp only [points, Nat.floor_zero, mul_one, Nat.floor_natCast]
    apply Finset.sum_congr rfl
    intro d _
    simp only [addLeftEmbedding_apply, sieveVariable, Nat.cast_add, add_assoc, add_comm]
  simp_rw [hshift]
  unfold sieveExpectation
  congr 1
  exact Equiv.sum_comp (Equiv.addRight (t : ZMod (Q : ℕ)))
    (fun x => (∑ d ∈ points 1 0 n, sieveVariable Q d x) ^ r)

/-- An interval has the same moment law as the prefix containing its number of integer points. -/
theorem sieve_interval_moment_prefix (Q : ℕ+) (H a b : ℝ) (r : ℕ) :
    sieveExpectation Q (fun x => sieveIntervalSum Q H a b x ^ r) =
      sieveExpectation Q (fun x => sieveIntervalSum Q 1 0 (points H a b).card x ^ r) := by
  by_cases hab : ⌊a * H⌋₊ ≤ ⌊b * H⌋₊
  · have hs := sieve_interval_moment_translate Q ⌊a * H⌋₊ (⌊b * H⌋₊ - ⌊a * H⌋₊) r
    simpa only [sieveIntervalSum, points, Nat.card_Ioc, Nat.add_sub_of_le hab] using hs
  · have he : points H a b = ∅ := Finset.Ioc_eq_empty_of_le (by omega)
    simp only [sieveIntervalSum, he, Finset.card_empty, Nat.cast_zero, Finset.sum_empty]
    simp [points]

/-- The finite mesh in the nonnegative endpoint window. -/
def sieveEndpointGrid (M δ : ℝ) : Finset ℝ :=
  (Finset.range (⌊M / δ⌋₊ + 1)).image (fun n : ℕ => δ * n)

/-- An endpoint rounded down to the mesh. -/
def sieveRoundDown (δ x : ℝ) : ℝ := δ * ⌊x / δ⌋₊

/-- Rounding endpoints down preserves their order and window, with error at most one mesh step. -/
theorem sieve_grid_rounding (M δ : ℝ) (_hM : 0 ≤ M) (hδ : 0 < δ)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M) :
    sieveRoundDown δ a ∈ sieveEndpointGrid M δ ∧ sieveRoundDown δ b ∈ sieveEndpointGrid M δ ∧
      0 ≤ sieveRoundDown δ a ∧ sieveRoundDown δ a ≤ sieveRoundDown δ b ∧ sieveRoundDown δ b ≤ M ∧
      |a - sieveRoundDown δ a| ≤ δ ∧ |b - sieveRoundDown δ b| ≤ δ := by
  have hround (x : ℝ) (hx : 0 ≤ x) :
      0 ≤ sieveRoundDown δ x ∧ sieveRoundDown δ x ≤ x ∧ |x - sieveRoundDown δ x| ≤ δ := by
    have hlo := (le_div_iff₀ hδ).mp (Nat.floor_le (div_nonneg hx hδ.le))
    have hhi := (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one (x / δ))
    have hle : sieveRoundDown δ x ≤ x := by simpa only [sieveRoundDown, mul_comm] using hlo
    refine ⟨mul_nonneg hδ.le (Nat.cast_nonneg _), hle, ?_⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    rw [show ((⌊x / δ⌋₊ : ℝ) + 1) * δ = sieveRoundDown δ x + δ by
      dsimp [sieveRoundDown]
      ring] at hhi
    linarith only [hhi]
  have hmem (x : ℝ) (hx : x ≤ M) : sieveRoundDown δ x ∈ sieveEndpointGrid M δ := by
    apply Finset.mem_image.mpr
    refine ⟨⌊x / δ⌋₊, Finset.mem_range.mpr ?_, rfl⟩
    exact Nat.lt_succ_of_le (Nat.floor_mono (div_le_div_of_nonneg_right hx hδ.le))
  have hmono : sieveRoundDown δ a ≤ sieveRoundDown δ b :=
    mul_le_mul_of_nonneg_left (Nat.cast_le.mpr
      (Nat.floor_mono (div_le_div_of_nonneg_right hab hδ.le))) hδ.le
  exact ⟨hmem a (hab.trans hb), hmem b hb, (hround a ha).1, hmono,
    (hround b (ha.trans hab)).2.1.trans hb, (hround a ha).2.2,
    (hround b (ha.trans hab)).2.2⟩

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
