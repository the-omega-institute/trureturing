/- GID: D5/S3/TotalVariation/HellingerDataProcessing
   generality: G
   mirror-B: D5/B/S3/TotalVariation/HellingerDataProcessing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove affinity growth and squared-Hellinger contraction under a stochastic channel. -/

/- Library-search audit trail (2026-08-10):
   * Local pinned-mathlib grep terms: `inner_mul_le_norm_mul_norm`,
     `sum_sqrt_mul_sqrt_le`, `sum_mul_sq_le_sq_mul_sq`, `Hellinger`, `Bhattacharyya`,
     `affinity`, `data processing`, and `DataProcessing`.
   * No statistical Hellinger/Bhattacharyya data-processing theorem was found. The Hellinger
     hits are for Hellinger--Toeplitz, while the data-processing hits concern Bayes risk.
     The finite real Cauchy--Schwarz lemma `Real.sum_sqrt_mul_sqrt_le` is reused below.
   * Repository grep over all 649 Lean declaration starts below `D5/S3` found neither target
     inequality and no public lemma saying that `channelOutput` preserves normalization.
     Output nonnegativity and normalization are therefore proved locally where needed.
-/

import D5.S3.TotalVariation.Hellinger

namespace D5.S3.TotalVariation.HellingerDataProcessing

open D5.S3.Divergence.ClassicalDPI
open D5.S3.TotalVariation.Bhattacharyya
open D5.S3.TotalVariation.Hellinger

/-- A nonnegative row-stochastic finite channel cannot decrease Bhattacharyya affinity.
The input mass functions need not be normalized. -/
theorem bhattacharyya_channel_le
    {X Y : Type*} [Fintype X] [Fintype Y]
    (p q : X → ℝ) (W : X → Y → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hW : (∀ x y, 0 ≤ W x y) ∧ ∀ x, ∑ y, W x y = 1) :
    bhattacharyya p q ≤
      bhattacharyya (channelOutput W p) (channelOutput W q) := by
  classical
  have hOutputPNonneg (y : Y) : 0 ≤ channelOutput W p y := by
    rw [channelOutput]
    exact Finset.sum_nonneg fun x _ ↦ mul_nonneg (hp x) (hW.1 x y)
  have hOutputQNonneg (y : Y) : 0 ≤ channelOutput W q y := by
    rw [channelOutput]
    exact Finset.sum_nonneg fun x _ ↦ mul_nonneg (hq x) (hW.1 x y)
  have hpointwise (y : Y) :
      (∑ x, Real.sqrt (p x * q x) * W x y) ≤
        Real.sqrt (channelOutput W p y * channelOutput W q y) := by
    calc
      (∑ x, Real.sqrt (p x * q x) * W x y) =
          ∑ x, Real.sqrt (p x * W x y) * Real.sqrt (q x * W x y) := by
        apply Finset.sum_congr rfl
        intro x _
        calc
          Real.sqrt (p x * q x) * W x y =
              Real.sqrt (p x) * Real.sqrt (q x) * W x y := by
            rw [Real.sqrt_mul (hp x)]
          _ = Real.sqrt (p x) * Real.sqrt (q x) * Real.sqrt (W x y) ^ 2 := by
            rw [Real.sq_sqrt (hW.1 x y)]
          _ = (Real.sqrt (p x) * Real.sqrt (W x y)) *
              (Real.sqrt (q x) * Real.sqrt (W x y)) := by ring
          _ = Real.sqrt (p x * W x y) * Real.sqrt (q x * W x y) := by
            rw [Real.sqrt_mul (hp x), Real.sqrt_mul (hq x)]
      _ ≤ Real.sqrt (∑ x, p x * W x y) *
          Real.sqrt (∑ x, q x * W x y) := by
        simpa using Real.sum_sqrt_mul_sqrt_le Finset.univ
          (fun x ↦ mul_nonneg (hp x) (hW.1 x y))
          (fun x ↦ mul_nonneg (hq x) (hW.1 x y))
      _ = Real.sqrt (channelOutput W p y) * Real.sqrt (channelOutput W q y) := by
        rfl
      _ = Real.sqrt (channelOutput W p y * channelOutput W q y) := by
        rw [Real.sqrt_mul (hOutputPNonneg y)]
  rw [bhattacharyya, bhattacharyya]
  calc
    (∑ x, Real.sqrt (p x * q x)) =
        ∑ x, ∑ y, Real.sqrt (p x * q x) * W x y := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.mul_sum, hW.2 x, mul_one]
    _ = ∑ y, ∑ x, Real.sqrt (p x * q x) * W x y := Finset.sum_comm
    _ ≤ ∑ y, Real.sqrt (channelOutput W p y * channelOutput W q y) := by
      apply Finset.sum_le_sum
      intro y _
      exact hpointwise y

/-- A nonnegative row-stochastic finite channel contracts squared Hellinger distance on
probability mass functions. -/
theorem hellinger_sq_channel_le
    {X Y : Type*} [Fintype X] [Fintype Y]
    (p q : X → ℝ) (W : X → Y → ℝ)
    (hp : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1)
    (hq : (∀ x, 0 ≤ q x) ∧ ∑ x, q x = 1)
    (hW : (∀ x y, 0 ≤ W x y) ∧ ∀ x, ∑ y, W x y = 1) :
    hellingerSq (channelOutput W p) (channelOutput W q) ≤ hellingerSq p q := by
  classical
  have hOutputP :
      (∀ y, 0 ≤ channelOutput W p y) ∧ ∑ y, channelOutput W p y = 1 := by
    constructor
    · intro y
      rw [channelOutput]
      exact Finset.sum_nonneg fun x _ ↦ mul_nonneg (hp.1 x) (hW.1 x y)
    · change (∑ y, ∑ x, p x * W x y) = 1
      calc
        (∑ y, ∑ x, p x * W x y) = ∑ x, ∑ y, p x * W x y := Finset.sum_comm
        _ = ∑ x, p x := by
          apply Finset.sum_congr rfl
          intro x _
          rw [← Finset.mul_sum, hW.2 x, mul_one]
        _ = 1 := hp.2
  have hOutputQ :
      (∀ y, 0 ≤ channelOutput W q y) ∧ ∑ y, channelOutput W q y = 1 := by
    constructor
    · intro y
      rw [channelOutput]
      exact Finset.sum_nonneg fun x _ ↦ mul_nonneg (hq.1 x) (hW.1 x y)
    · change (∑ y, ∑ x, q x * W x y) = 1
      calc
        (∑ y, ∑ x, q x * W x y) = ∑ x, ∑ y, q x * W x y := Finset.sum_comm
        _ = ∑ x, q x := by
          apply Finset.sum_congr rfl
          intro x _
          rw [← Finset.mul_sum, hW.2 x, mul_one]
        _ = 1 := hq.2
  have hAffinity := bhattacharyya_channel_le p q W hp.1 hq.1 hW
  rw [hellinger_sq_eq_two_sub (channelOutput W p) (channelOutput W q)
      hOutputP hOutputQ,
    hellinger_sq_eq_two_sub p q hp hq]
  linarith

end D5.S3.TotalVariation.HellingerDataProcessing
