/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalNormal
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalNormal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Polynomial-geometric joint normal bounds for the actual signed external columns. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadial

/-! Finite binomial antidiagonals control every polynomial external and internal frequency weight. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Topology ENNReal
namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalNormal
open OriginalGaussianDifferentiation OriginalGaussianExternalResolvent
open OriginalGaussianSourceEvaluation

private def normalMajorant (d : ℕ) (δ ρ : ℝ) (ps : ℕ × ℕ) : ℝ :=
  (ps.1 + ps.2 + 1 : ℝ) ^ d * ((ps.1 + ps.2).choose ps.2 : ℝ) *
    δ ^ ps.1 * ρ ^ ps.2

private lemma normal_antidiagonal (d n : ℕ) (δ ρ : ℝ) :
    (∑ ps ∈ Finset.HasAntidiagonal.antidiagonal n, normalMajorant d δ ρ ps) =
      (n + 1 : ℝ) ^ d * (δ + ρ) ^ n := by
  rw [(Commute.all δ ρ).add_pow', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ps hps
  have hn : ps.1 + ps.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hps
  simp only [normalMajorant, ← Nat.cast_add, hn, nsmul_eq_mul]
  have hc : n.choose ps.2 = n.choose ps.1 := by
    rw [← hn]
    exact Nat.choose_symm_add.symm
  rw [hc]
  ring

private lemma normal_summable (d : ℕ) {δ ρ : ℝ}
    (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ) (hsmall : δ + ρ < 1) :
    Summable (normalMajorant d δ ρ) := by
  have hp (ps : ℕ × ℕ) : 0 ≤ normalMajorant d δ ρ ps := by
    unfold normalMajorant
    positivity
  have hs : Summable (fun n : ℕ => (n + 1 : ℝ) ^ d * (δ + ρ) ^ n) := by
    obtain ⟨R, hR, hR1⟩ := exists_between hsmall
    have hR0 : 0 < R := lt_of_le_of_lt (add_nonneg hδ hρ) hR
    apply Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_)
      (derivative_shifted_geometric hR0 hR1 d)
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (add_nonneg hδ hρ) hR.le n) (by positivity)
  let e : (Σ n : ℕ, ↥(Finset.HasAntidiagonal.antidiagonal n)) ≃ ℕ × ℕ :=
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd
  have hsig : Summable (fun ps : (Σ n : ℕ,
      ↥(Finset.HasAntidiagonal.antidiagonal n)) => normalMajorant d δ ρ ps.2) := by
    apply (summable_sigma_of_nonneg (f := fun ps : (Σ n : ℕ,
      ↥(Finset.HasAntidiagonal.antidiagonal n)) => normalMajorant d δ ρ ps.2)
      (fun ps => hp ps.2)).mpr
    constructor
    · intro n
      exact (hasSum_fintype _).summable
    · apply hs.congr
      intro n
      rw [tsum_fintype, ← normal_antidiagonal d n δ ρ]
      exact (Finset.sum_coe_sort _ _).symm
  exact e.summable_iff.mp hsig

/-- Joint normal summability includes arbitrary polynomial derivative weights and both signs. -/
theorem external_binomial_joint_summable (out : Bool) (d : ℕ) {δ ρ : ℝ}
    (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ) (hsmall : δ + ρ < 1) :
    Summable (fun ps : ℕ × ℕ => (ps.1 + ps.2 + 1 : ℝ) ^ d *
      δ ^ ps.1 * ρ ^ ps.2 * ‖externalBinomial out ps.1 ps.2‖) := by
  apply Summable.of_nonneg_of_le (fun _ => by positivity) (fun ps => ?_)
    (normal_summable d hδ hρ hsmall)
  have hb := choose_bound ps.1 (external_parameter_bound out ps.1) ps.2
  change _ ≤ normalMajorant d δ ρ ps
  unfold normalMajorant
  calc
    _ ≤ (ps.1 + ps.2 + 1 : ℝ) ^ d * δ ^ ps.1 * ρ ^ ps.2 *
        ((ps.1 + ps.2).choose ps.2 : ℝ) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

/-- Joint absolute summability of the original external columns, with their actual sign. -/
theorem externalColumn_joint_summable (out : Bool) {u z : ℂ}
    (hsmall : ‖u‖ + ‖z‖ < 1) :
    Summable (fun pn : ℕ × ℕ => ‖u‖ ^ pn.1 * ‖externalColumn out pn.1 z pn.2‖) := by
  have hs := external_binomial_joint_summable out 1 (norm_nonneg u) (norm_nonneg z) hsmall
  have hi : Function.Injective (fun pn : ℕ × ℕ => (pn.1, pn.2 + 1)) := by
    intro a b h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    exact Prod.ext h₁ (Nat.add_right_cancel h₂)
  have ht := hs.comp_injective hi
  apply Summable.of_nonneg_of_le (fun _ => by positivity) (fun pn => ?_) ht
  simp only [Function.comp_apply, pow_one, externalColumn, norm_mul, norm_neg,
    norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hh : Real.sqrt (pn.2 + 1 : ℝ) ≤ (pn.1 + (pn.2 + 1) + 1 : ℝ) := by
    have hsq := Real.sq_sqrt (by positivity : 0 ≤ (pn.2 + 1 : ℝ))
    have hn := Real.sqrt_nonneg (pn.2 + 1 : ℝ)
    have hp := Nat.cast_nonneg (α := ℝ) pn.1
    have hq := Nat.cast_nonneg (α := ℝ) pn.2
    nlinarith
  calc
    _ ≤ ‖u‖ ^ pn.1 * ((pn.1 + (pn.2 + 1) + 1 : ℝ) * ‖z‖ ^ (pn.2 + 1) *
        ‖externalBinomial out pn.1 (pn.2 + 1)‖) := by gcongr
    _ = _ := by push_cast; ring

/-- The original Hilbert-space external vectors form a normally convergent mode series. -/
theorem externalVector_mode_summable (out : Bool) {u z : ℂ}
    (hsmall : ‖u‖ + ‖z‖ < 1) :
    Summable (fun p : ℕ => ‖u ^ p • externalVector out p z‖) := by
  have hz : ‖z‖ < 1 := by linarith [norm_nonneg u]
  have hs := externalColumn_joint_summable out hsmall
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) hs.prod
  have hc : Summable (fun n : ℕ => ‖(lp.single 2 n (externalColumn out p z n) :
      OriginalGaussianResolvent.H)‖) := by
    simpa only [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)] using
      (externalColumn_l1 out p (norm_nonneg z) hz le_rfl).2
  rw [norm_smul, norm_pow, externalVector]
  calc
    _ ≤ ‖u‖ ^ p * ∑' n : ℕ, ‖(lp.single 2 n (externalColumn out p z n) :
        OriginalGaussianResolvent.H)‖ :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hc) (by positivity)
    _ = _ := by
      simp only [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), tsum_mul_left]

set_option maxHeartbeats 800000 in
-- Bilinear norm bounds elaborate two Hilbert carrier instances and the joint product sum.
/-- Both full literal kernels have absolutely convergent joint external mode sums. -/
theorem external_kernel_mode_summable (out out' : Bool) {u v z : ℂ}
    (hu : ‖u‖ + ‖z‖ < 1) (hv : ‖v‖ + ‖z‖ < 1) :
    Summable (fun pq : ℕ × ℕ => ‖u ^ pq.1 * v ^ pq.2 *
      externalJ out pq.1 out' pq.2 z‖) ∧
    Summable (fun pq : ℕ × ℕ => ‖u ^ pq.1 * v ^ pq.2 *
      externalT out pq.1 out' pq.2 z‖) := by
  have hz : ‖z‖ < 1 := by linarith [norm_nonneg u]
  have hp := externalVector_mode_summable out hu
  have hq := externalVector_mode_summable out' hv
  have hs : Summable (fun pq : ℕ × ℕ => ‖u ^ pq.1 • externalVector out pq.1 z‖ *
      ‖v ^ pq.2 • externalVector out' pq.2 z‖) :=
    hp.mul_of_nonneg hq (fun p => norm_nonneg _) (fun q => norm_nonneg _)
  have hbound (A : OriginalGaussianResolvent.H →L[ℂ] OriginalGaussianResolvent.H)
      (X Y : OriginalGaussianResolvent.H) :
      ‖OriginalGaussianDifferentiation.sourceBilinearFunctional X (A Y)‖ ≤
        ‖A‖ * (‖X‖ * ‖Y‖) := by
    change ‖inner ℂ (star X) (A Y)‖ ≤ _
    calc
      _ ≤ ‖star X‖ * ‖A Y‖ := norm_inner_le_norm (𝕜 := ℂ) (star X) (A Y)
      _ ≤ ‖X‖ * (‖A‖ * ‖Y‖) := by
        rw [norm_star]
        exact mul_le_mul_of_nonneg_left (A.le_opNorm Y) (norm_nonneg X)
      _ = _ := by ring
  have hb (A : OriginalGaussianResolvent.H →L[ℂ] OriginalGaussianResolvent.H)
      (f : ℕ → ℕ → ℂ)
      (he : ∀ p q, OriginalGaussianDifferentiation.sourceBilinearFunctional
        (externalVector out p z) (A (externalVector out' q z)) = f p q) :
      Summable (fun pq : ℕ × ℕ => ‖u ^ pq.1 * v ^ pq.2 * f pq.1 pq.2‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun pq => ?_)
      (hs.mul_left ‖A‖)
    rw [← he]
    simp only [norm_mul, norm_smul, norm_pow]
    calc
      _ ≤ (‖u‖ ^ pq.1 * ‖v‖ ^ pq.2) *
        (‖A‖ * (‖externalVector out pq.1 z‖ * ‖externalVector out' pq.2 z‖)) := by
          gcongr
          exact hbound A _ _
      _ = _ := by ring
  exact ⟨hb (OriginalGaussianAllIndexResolvent.oddResolvent z)
      (fun p q => externalJ out p out' q z)
      (fun p q => (external_contractions_explicit out p out' q hz).2.2.1),
    hb (OriginalGaussianAllIndexResolvent.squareResolvent z)
      (fun p q => externalT out p out' q z)
      (fun p q => (external_contractions_explicit out p out' q hz).2.2.2.1)⟩

/-- The evaluated amplitudes have a normally convergent joint external/radial series. -/
theorem sourceAmplitude_joint_summable (out : Bool) {u x : ℂ} (hsmall : ‖u‖ + ‖x‖ < 1) :
    Summable (fun pn : ℕ × ℕ => ‖(OriginalGaussianMatrix.centralWeight pn.2 : ℂ) *
      (-1 : ℂ) ^ pn.2 *
      Ring.choose ((if out then (pn.1 : ℂ) + 1 / 2 else -(pn.1 : ℂ) - 1 / 2) -
        1 / 2) pn.2 * x ^ pn.2 * u ^ pn.1‖) := by
  have hs := normal_summable 0 (norm_nonneg u) (norm_nonneg x) hsmall
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun pn => ?_) hs
  have hc : ‖(OriginalGaussianMatrix.centralWeight pn.2 : ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (OriginalGaussianMatrix.centralWeight_nonneg pn.2)] using
      OriginalGaussianResolvent.weight_le_one pn.2
  have hp : ‖((if out then (pn.1 : ℂ) + 1 / 2 else
      -(pn.1 : ℂ) - 1 / 2) - 1 / 2)‖ ≤ (pn.1 + 1 : ℝ) := by
    cases out
    · simp only [Bool.false_eq_true, ite_false]
      rw [show -(pn.1 : ℂ) - 1 / 2 - 1 / 2 = -(pn.1 + 1 : ℂ) by ring,
        norm_neg, show (pn.1 + 1 : ℂ) = ((pn.1 + 1 : ℕ) : ℂ) by push_cast; rfl,
        Complex.norm_natCast]
      simp only [Nat.cast_add, Nat.cast_one, le_refl]
    · simp only [ite_true, add_sub_cancel_right, Complex.norm_natCast]
      linarith
  have hb := choose_bound pn.1 hp pn.2
  simp only [norm_mul, norm_pow, norm_neg, norm_one,
    one_pow, mul_one, normalMajorant, pow_zero, one_mul]
  calc
    _ ≤ 1 * ((pn.1 + pn.2).choose pn.2 : ℝ) * ‖x‖ ^ pn.2 * ‖u‖ ^ pn.1 := by
      gcongr
    _ = _ := by ring

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalNormal
