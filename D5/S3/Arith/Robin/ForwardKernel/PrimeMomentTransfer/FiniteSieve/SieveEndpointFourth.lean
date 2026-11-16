/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveEndpointFourth
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveEndpointFourth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Scalar fourth norms control perturbations of both endpoints of sieve intervals. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.SieveScalarFourth

/-! Two-endpoint perturbations of finite sieve interval sums in the fourth norm. -/

open scoped BigOperators Topology
open Set Filter MeasureTheory

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

/-- The difference of two interval sums is the signed difference of their endpoint intervals. -/
private theorem sieve_interval_endpoint_difference (Q : ℕ+) (H a b c d : ℝ)
    (hH : 0 < H) (_ha : 0 ≤ a) (hab : a ≤ b) (_hc : 0 ≤ c) (hcd : c ≤ d)
    (x : ZMod (Q : ℕ)) :
    sieveIntervalSum Q H a b x - sieveIntervalSum Q H c d x =
      (if b ≤ d then -sieveIntervalSum Q H b d x else sieveIntervalSum Q H d b x) -
      (if a ≤ c then -sieveIntervalSum Q H a c x else sieveIntervalSum Q H c a x) := by
  have hf {u v : ℝ} (huv : u ≤ v) : ⌊u * H⌋₊ + 1 ≤ ⌊v * H⌋₊ + 1 :=
    Nat.succ_le_succ (Nat.floor_mono (mul_le_mul_of_nonneg_right huv hH.le))
  unfold sieveIntervalSum points
  simp only [← Finset.Ico_add_one_add_one_eq_Ioc]
  rw [Finset.sum_Ico_eq_sub _ (hf hab), Finset.sum_Ico_eq_sub _ (hf hcd)]
  split_ifs with hbd hac hac
  · rw [Finset.sum_Ico_eq_sub _ (hf hbd), Finset.sum_Ico_eq_sub _ (hf hac)]
    ring
  · rw [Finset.sum_Ico_eq_sub _ (hf hbd), Finset.sum_Ico_eq_sub _ (hf (le_of_not_ge hac))]
    ring
  · rw [Finset.sum_Ico_eq_sub _ (hf (le_of_not_ge hbd)), Finset.sum_Ico_eq_sub _ (hf hac)]
    ring
  · rw [Finset.sum_Ico_eq_sub _ (hf (le_of_not_ge hbd)),
      Finset.sum_Ico_eq_sub _ (hf (le_of_not_ge hac))]
    ring

private theorem sieve_threshold_scale_identity (H : ℝ) (hH : 0 < H) :
    H ^ (1 / 4 : ℝ) * Real.sqrt (Real.log H) = sieveScale H * H ^ (-1 / 4 : ℝ) := by
  have hp : Real.sqrt H * H ^ (-1 / 4 : ℝ) = H ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hH]
    norm_num
  rw [sieveScale, Real.sqrt_mul hH.le]
  calc
    _ = (Real.sqrt H * H ^ (-1 / 4 : ℝ)) * Real.sqrt (Real.log H) := by rw [hp]
    _ = _ := by ring

private theorem sieve_interval_norm4_normalize (Q : ℕ+) (H a b C : ℝ) (hH : 2 ≤ H)
    (hbound : sieveNorm4 Q (sieveIntervalSum Q H a b) ≤ C *
      (sieveScale H * Real.sqrt (b - a) + H ^ (1 / 4 : ℝ) * Real.sqrt (Real.log H))) :
    sieveNorm4 Q (normalizedIntervalSum Q H a b) ≤ C * (Real.sqrt (b - a) + H ^ (-1 / 4 : ℝ)) := by
  have hA : 0 < sieveScale H := (sieve_scale_power H hH 1).1
  have hH0 : 0 < H := by linarith
  have heq : normalizedIntervalSum Q H a b = fun x => (sieveScale H)⁻¹ * sieveIntervalSum Q H a b x := by
    funext x
    simp only [normalizedIntervalSum, div_eq_mul_inv, mul_comm]
  rw [heq, sieve_norm4_smul, abs_of_pos (inv_pos.mpr hA)]
  calc
    _ ≤ (sieveScale H)⁻¹ * (C *
        (sieveScale H * Real.sqrt (b - a) + H ^ (1 / 4 : ℝ) * Real.sqrt (Real.log H))) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hA.le)
    _ = _ := by
      rw [sieve_threshold_scale_identity H hH0]
      field_simp

private theorem sieve_endpoint_piece_norm4 (Q : ℕ+) (H C δ : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ u v : ℝ, 0 ≤ u → u ≤ v →
      sieveNorm4 Q (normalizedIntervalSum Q H u v) ≤ C * (Real.sqrt (v - u) + H ^ (-1 / 4 : ℝ)))
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hdist : |u - v| ≤ δ) :
    sieveNorm4 Q (fun x => if u ≤ v then -normalizedIntervalSum Q H u v x else normalizedIntervalSum Q H v u x) ≤
      C * (Real.sqrt δ + H ^ (-1 / 4 : ℝ)) := by
  by_cases huv : u ≤ v
  · simp only [ite_eq_left huv]
    have hneg : sieveNorm4 Q (fun x => -normalizedIntervalSum Q H u v x) = sieveNorm4 Q (normalizedIntervalSum Q H u v) := by
      simp only [sieve_norm4_eq_lpNorm, lpNorm_fun_neg]
    rw [hneg]
    have hlen : v - u ≤ δ := by
      rw [abs_of_nonpos (sub_nonpos.mpr huv)] at hdist
      linarith only [hdist]
    exact (hbound u v hu huv).trans (mul_le_mul_of_nonneg_left
      (add_le_add (Real.sqrt_le_sqrt hlen) le_rfl) hC)
  · simp only [ite_eq_right huv]
    have hvu : v ≤ u := le_of_not_ge huv
    have hlen : u - v ≤ δ := by
      rwa [abs_of_nonneg (sub_nonneg.mpr hvu)] at hdist
    exact (hbound v u hv hvu).trans (mul_le_mul_of_nonneg_left
      (add_le_add (Real.sqrt_le_sqrt hlen) le_rfl) hC)

/-- Nearby endpoints give a uniform normalized fourth-norm perturbation estimate. -/
theorem sieve_interval_endpoint_norm4_bound (hMS : MSFinite) (B : ℝ) (hB : 1 ≤ B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ H : ℝ in atTop,
      ∀ (Q : ℕ+), sieveDensity Q ≤ B * Real.log H → ∀ a b c d δ : ℝ,
      0 ≤ a → a ≤ b → 0 ≤ c → c ≤ d → 0 ≤ δ → |a - c| ≤ δ → |b - d| ≤ δ →
      sieveNorm4 Q (fun x => normalizedIntervalSum Q H a b x - normalizedIntervalSum Q H c d x) ≤
        C * (Real.sqrt δ + H ^ (-1 / 4 : ℝ)) := by
  obtain ⟨C, hC, hscalar⟩ := sieve_interval_norm4_bound hMS B hB
  refine ⟨2 * C, by linarith, ?_⟩
  filter_upwards [hscalar, eventually_ge_atTop (2 : ℝ)]
    with H hscalarH hH Q hP a b c d δ ha hab hc hcd _hδ hac hbd
  have hH0 : 0 < H := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hbound (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) :
      sieveNorm4 Q (normalizedIntervalSum Q H u v) ≤ C * (Real.sqrt (v - u) + H ^ (-1 / 4 : ℝ)) :=
    sieve_interval_norm4_normalize Q H u v C hH (hscalarH Q hP u v hu huv)
  let R : ZMod (Q : ℕ) → ℝ := fun x =>
    if b ≤ d then -normalizedIntervalSum Q H b d x else normalizedIntervalSum Q H d b x
  let L : ZMod (Q : ℕ) → ℝ := fun x =>
    if a ≤ c then -normalizedIntervalSum Q H a c x else normalizedIntervalSum Q H c a x
  have heq (x : ZMod (Q : ℕ)) : normalizedIntervalSum Q H a b x - normalizedIntervalSum Q H c d x = R x - L x := by
    dsimp only [normalizedIntervalSum, R, L]
    rw [← sub_div, sieve_interval_endpoint_difference Q H a b c d hH0 ha hab hc hcd x]
    split_ifs <;> simp only [sub_div, neg_div]
  have hR : sieveNorm4 Q R ≤ C * (Real.sqrt δ + H ^ (-1 / 4 : ℝ)) :=
    sieve_endpoint_piece_norm4 Q H C δ hC0 hbound b d (ha.trans hab) (hc.trans hcd) hbd
  have hL : sieveNorm4 Q L ≤ C * (Real.sqrt δ + H ^ (-1 / 4 : ℝ)) :=
    sieve_endpoint_piece_norm4 Q H C δ hC0 hbound a c ha hc hac
  calc
    _ = sieveNorm4 Q (fun x => R x - L x) := congrArg (sieveNorm4 Q) (funext heq)
    _ ≤ sieveNorm4 Q R + sieveNorm4 Q L := by
      simp only [sieve_norm4_eq_lpNorm]
      exact lpNorm_sub_le (sieve_memLp_four Q R) (by norm_num)
    _ ≤ C * (Real.sqrt δ + H ^ (-1 / 4 : ℝ)) +
        C * (Real.sqrt δ + H ^ (-1 / 4 : ℝ)) := add_le_add hR hL
    _ = (2 * C) * (Real.sqrt δ + H ^ (-1 / 4 : ℝ)) := by ring

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
