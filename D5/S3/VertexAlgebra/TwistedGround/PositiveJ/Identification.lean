/- GID: D5/S3/VertexAlgebra/TwistedGround/PositiveJ/Identification
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/PositiveJ/Identification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Joint differentiability of the literal Gaussian kernel and positive J identification. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalAnalyticCandidate
import Mathlib.Analysis.Calculus.MeanValue

/-! The original Hilbert-space mode sums give joint differentiability of the
literal kernel. Characteristic uniqueness identifies its positive J sector
with the analytic candidate on the original bidisk. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators ENNReal Topology
open Filter Set

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalAnalyticCandidate

open OriginalGaussianExternalGeneratedSource OriginalGaussianExternalResolvent
open OriginalGaussianResolvent OriginalGaussianDifferentiation OriginalGaussianAllIndexResolvent
open OriginalGaussianExternalNormal OriginalGaussianExternalEquations

section

open private pairing from
  D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadialSums

private def modeVector (out : Bool) (u z : ℂ) : H :=
  ∑' p : ℕ, u ^ p • externalVector out p z

-- Banach-valued holomorphy follows from local normal convergence.
private lemma modeVector_differentiable (out : Bool) {u z : ℂ}
    (hu : ‖u‖ + ‖z‖ < 1) : DifferentiableAt ℂ (fun w => modeVector out w z) u := by
  obtain ⟨R, huR, hR⟩ := exists_between (show ‖u‖ < 1 - ‖z‖ by linarith)
  have hR0 : 0 < R := lt_of_le_of_lt (norm_nonneg u) huR
  have hs := externalVector_mode_summable out (u := (R : ℂ)) (z := z)
    (by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0] using
      (show R + ‖z‖ < 1 by linarith))
  have hd (p : ℕ) : DifferentiableOn ℂ
      (fun w : ℂ => w ^ p • externalVector out p z) (Metric.ball 0 R) := by
    intro w _
    exact ((hasDerivAt_pow p w).smul_const _).differentiableAt.differentiableWithinAt
  have hb (p : ℕ) (w : ℂ) (hw : w ∈ Metric.ball 0 R) :
      ‖w ^ p • externalVector out p z‖ ≤ ‖(R : ℂ) ^ p • externalVector out p z‖ := by
    simp only [norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0]
    gcongr
    exact (show ‖w‖ < R by simpa using hw).le
  exact (Complex.differentiableOn_tsum_of_summable_norm hs hd Metric.isOpen_ball hb)
    |>.differentiableAt (Metric.isOpen_ball.mem_nhds (by simpa using huR))

-- Two map_tsum applications factor the actual original kernel.
private lemma kernelMode_pairing (square out out' : Bool) {u v z : ℂ}
    (hu : ‖u‖ + ‖z‖ < 1) (hv : ‖v‖ + ‖z‖ < 1) :
    kernelMode square out out' u v z =
      pairing (modeVector out u z)
        ((if square then squareResolvent z else oddResolvent z) (modeVector out' v z)) := by
  let A : H →L[ℂ] H := if square then squareResolvent z else oddResolvent z
  let c : ℕ × ℕ → ℂ := fun pq =>
    if square then externalT out pq.1 out' pq.2 z else externalJ out pq.1 out' pq.2 z
  have hz : ‖z‖ < 1 := by linarith [norm_nonneg u]
  have hp := (externalVector_mode_summable out hu).of_norm
  have hq := (externalVector_mode_summable out' hv).of_norm
  have hc : Summable (fun pq : ℕ × ℕ => c pq * u ^ pq.1 * v ^ pq.2) := by
    have h := external_kernel_mode_summable out out' hu hv
    cases square
    · simpa only [c, Bool.false_eq_true, ite_false, norm_mul, mul_comm,
        mul_left_comm, mul_assoc] using h.1.of_norm
    · simpa only [c, ite_true, norm_mul, mul_comm, mul_left_comm, mul_assoc] using h.2.of_norm
  have he (p q : ℕ) :
      pairing (externalVector out p z) (A (externalVector out' q z)) = c (p, q) := by
    change sourceBilinearFunctional (externalVector out p z) (A (externalVector out' q z)) = _
    cases square
    · exact (external_contractions_explicit out p out' q hz).2.2.1
    · exact (external_contractions_explicit out p out' q hz).2.2.2.1
  symm
  calc
    _ = ∑' p : ℕ, pairing (u ^ p • externalVector out p z) (A (modeVector out' v z)) :=
      (pairing.flip (A (modeVector out' v z))).map_tsum hp
    _ = ∑' p : ℕ, ∑' q : ℕ,
        pairing (u ^ p • externalVector out p z) (A (v ^ q • externalVector out' q z)) := by
      apply tsum_congr
      intro p
      exact ((pairing (u ^ p • externalVector out p z)).comp A).map_tsum hq
    _ = ∑' p : ℕ, ∑' q : ℕ, c (p, q) * u ^ p * v ^ q := by
      apply tsum_congr
      intro p
      apply tsum_congr
      intro q
      simp only [map_smul, smul_apply, smul_eq_mul]
      rw [he]
      ring
    _ = _ := hc.tsum_prod.symm

-- The original kernel regularity follows from its actual vector mode sums.
theorem kernelMode_joint_differentiable (square out out' : Bool) {u v z : ℂ}
    (hu : ‖u‖ + ‖z‖ < 1) (hv : ‖v‖ + ‖z‖ < 1) :
    DifferentiableAt ℂ (fun p : ℂ × ℂ => kernelMode square out out' p.1 p.2 z) (u, v) := by
  let A : H →L[ℂ] H := if square then squareResolvent z else oddResolvent z
  have hfst : DifferentiableAt ℂ (fun p : ℂ × ℂ => p.1) (u, v) :=
    differentiableAt_fst
  have hsnd : DifferentiableAt ℂ (fun p : ℂ × ℂ => p.2) (u, v) :=
    differentiableAt_snd
  have hX := (modeVector_differentiable out hu).comp (u, v) hfst
  have hY := A.differentiableAt.comp (u, v)
    ((modeVector_differentiable out' hv).comp (u, v) hsnd)
  have h := (pairing.hasFDerivAt_of_bilinear hX.hasFDerivAt hY.hasFDerivAt).differentiableAt
  apply h.congr_of_eventuallyEq
  have hnu : ∀ᶠ p : ℂ × ℂ in 𝓝 (u, v), ‖p.1‖ + ‖z‖ < 1 :=
    (continuous_fst.norm.add continuous_const).continuousAt.eventually (gt_mem_nhds hu)
  have hnv : ∀ᶠ p : ℂ × ℂ in 𝓝 (u, v), ‖p.2‖ + ‖z‖ < 1 :=
    (continuous_snd.norm.add continuous_const).continuousAt.eventually (gt_mem_nhds hv)
  filter_upwards [hnu, hnv] with p hp hq
  exact kernelMode_pairing square out out' hp hq

end

private lemma joint_partials {F : ℂ × ℂ → ℂ} {u v : ℂ}
    (hf : DifferentiableAt ℂ F (u, v)) :
    deriv (fun w => F (w, v)) u = fderiv ℂ F (u, v) (1, 0) ∧
    deriv (fun w => F (u, w)) v = fderiv ℂ F (u, v) (0, 1) := by
  constructor
  · exact (hf.hasFDerivAt.comp_hasDerivAt u
      ((hasDerivAt_id u).prodMk (hasDerivAt_const u v))).deriv
  · exact (hf.hasFDerivAt.comp_hasDerivAt v
      ((hasDerivAt_const v u).prodMk (hasDerivAt_id v))).deriv

private def characteristicDenominator (u t : ℂ) : ℂ := 1 - u + t * u
private def characteristicPath (u t : ℂ) : ℂ := t * u / characteristicDenominator u t

private lemma path_control {u : ℂ} (hu : ‖u‖ < 1) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    characteristicDenominator u (t : ℂ) ≠ 0 ∧ ‖characteristicPath u (t : ℂ)‖ ≤ ‖u‖ := by
  have hb : 1 - (1 - t) * ‖u‖ ≤ ‖characteristicDenominator u (t : ℂ)‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (((1 - t : ℝ) : ℂ) * u)
    have he : (1 : ℂ) - (((1 - t : ℝ) : ℂ) * u) = characteristicDenominator u (t : ℂ) := by
      push_cast
      unfold characteristicDenominator
      ring
    rw [he] at h
    simpa only [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ht.2)] using h
  have hpos : 0 < ‖characteristicDenominator u (t : ℂ)‖ := by
    nlinarith [norm_nonneg u, mul_nonneg ht.1 (norm_nonneg u)]
  refine ⟨norm_ne_zero_iff.mp hpos.ne', ?_⟩
  rw [characteristicPath, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
  apply (div_le_iff₀ hpos).mpr
  have htD : t ≤ ‖characteristicDenominator u (t : ℂ)‖ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hu.le)]
  nlinarith [mul_nonneg (norm_nonneg u) (sub_nonneg.mpr htD)]

private lemma phi_hasDerivAt (u t : ℂ) (hd : characteristicDenominator u t ≠ 0) :
    HasDerivAt (characteristicPath u) (u * (1 - u) / characteristicDenominator u t ^ 2) t := by
  have hD : HasDerivAt (characteristicDenominator u) u t := by
    convert ((hasDerivAt_id t).mul_const u).const_add (1 - u) using 1 <;>
      (try funext w) <;> (try simp only [characteristicDenominator, id_eq]) <;> ring
  apply (((hasDerivAt_id t).mul_const u).div hD hd).congr_deriv
  dsimp only [characteristicDenominator, id_eq]
  ring

-- The squared characteristic invariant is consumed by the actual J identification.
private theorem positive_spatial_zero {R : ℝ} (hR : R ≤ 1) (F : ℂ × ℂ → ℂ)
    (hreg : ∀ a b : ℂ, ‖a‖ < R → ‖b‖ < R → DifferentiableAt ℂ F (a, b))
    (hpde : ∀ a b : ℂ, ‖a‖ < R → ‖b‖ < R →
      a * (1 - a) * deriv (fun w => F (w, b)) a +
      b * (1 - b) * deriv (fun w => F (a, w)) b +
      (1 - 3 * (a + b) / 2) * F (a, b) = 0)
    {u v : ℂ} (hu : ‖u‖ < R) (hv : ‖v‖ < R) : F (u, v) = 0 := by
  let g : ℂ → ℂ := fun t =>
    t ^ 2 * F (characteristicPath u t, characteristicPath v t) ^ 2 /
      (characteristicDenominator u t ^ 3 * characteristicDenominator v t ^ 3)
  have hder (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s : ℝ => g (s : ℂ)) 0 t := by
    have hcu := path_control (hu.trans_le hR) ht
    have hcv := path_control (hv.trans_le hR) ht
    have hpu : ‖characteristicPath u (t : ℂ)‖ < R := hcu.2.trans_lt hu
    have hpv : ‖characteristicPath v (t : ℂ)‖ < R := hcv.2.trans_lt hv
    have hf := hreg _ _ hpu hpv
    let d := fderiv ℂ F (characteristicPath u (t : ℂ), characteristicPath v (t : ℂ))
    have hpart := joint_partials hf
    have hlin (a b : ℂ) : d (a, b) = a * d (1, 0) + b * d (0, 1) := by
      have he : (a, b) = a • ((1, 0) : ℂ × ℂ) + b • ((0, 1) : ℂ × ℂ) := by
        ext <;> simp
      rw [he, map_add, map_smul, map_smul]
      rfl
    have hpath : HasDerivAt (fun s : ℂ => F (characteristicPath u s, characteristicPath v s))
        (u * (1 - u) / characteristicDenominator u (t : ℂ) ^ 2 * d (1, 0) +
          v * (1 - v) / characteristicDenominator v (t : ℂ) ^ 2 * d (0, 1)) (t : ℂ) := by
      exact (hf.hasFDerivAt.comp_hasDerivAt (t : ℂ)
        ((phi_hasDerivAt u (t : ℂ) hcu.1).prodMk
          (phi_hasDerivAt v (t : ℂ) hcv.1))).congr_deriv (hlin _ _)
    have hDu : HasDerivAt (characteristicDenominator u) u (t : ℂ) := by
      convert ((hasDerivAt_id (t : ℂ)).mul_const u).const_add (1 - u) using 1 <;>
        (try funext s) <;> (try simp only [characteristicDenominator, id_eq]) <;> ring
    have hDv : HasDerivAt (characteristicDenominator v) v (t : ℂ) := by
      convert ((hasDerivAt_id (t : ℂ)).mul_const v).const_add (1 - v) using 1 <;>
        (try funext s) <;> (try simp only [characteristicDenominator, id_eq]) <;> ring
    have he := hpde _ _ hpu hpv
    rw [hpart.1, hpart.2] at he
    have hg : HasDerivAt g 0 (t : ℂ) := by
      apply (((hasDerivAt_pow 2 (t : ℂ)).mul (hpath.pow 2)).div
        ((hDu.pow 3).mul (hDv.pow 3))
        (mul_ne_zero (pow_ne_zero _ hcu.1) (pow_ne_zero _ hcv.1))).congr_deriv
      dsimp only [Pi.mul_apply, Pi.pow_apply, id_eq]
      norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
      calc
        _ = (2 * (t : ℂ) * F (characteristicPath u (t : ℂ), characteristicPath v (t : ℂ)) /
            (characteristicDenominator u (t : ℂ) ^ 3 * characteristicDenominator v (t : ℂ) ^ 3)) *
            (characteristicPath u (t : ℂ) * (1 - characteristicPath u (t : ℂ)) * d (1, 0) +
             characteristicPath v (t : ℂ) * (1 - characteristicPath v (t : ℂ)) * d (0, 1) +
             (1 - 3 * (characteristicPath u (t : ℂ) + characteristicPath v (t : ℂ)) / 2) *
               F (characteristicPath u (t : ℂ), characteristicPath v (t : ℂ))) := by
          have hdu := hcu.1
          have hdv := hcv.1
          dsimp only [characteristicPath, characteristicDenominator] at hdu hdv ⊢
          field_simp [hdu, hdv]
          ring
        _ = 0 := by change _ * _ = 0; rw [he]; ring
    exact hg.comp_ofReal
  have hc : ContinuousOn (fun t : ℝ => g (t : ℂ)) (Icc (0 : ℝ) 1) :=
    fun t ht => (hder t ht).continuousAt.continuousWithinAt
  have hz := constant_of_has_deriv_right_zero hc
    (fun t ht => (hder t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    1 (by constructor <;> norm_num)
  have hs : F (u, v) ^ 2 = 0 := by simpa [g, characteristicPath, characteristicDenominator] using hz
  exact eq_zero_of_pow_eq_zero hs

section

open private W_sum_ne_zero candidateJ_joint_analytic from
  D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalAnalyticCandidate

/-- The actual positive J generator equals its analytic candidate on the full source bidisk. -/
theorem positiveJ_eq_candidateJ {u v : ℂ} {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hu : ‖u‖ + Real.sqrt r < 1) (hv : ‖v‖ + Real.sqrt r < 1) :
    kernelMode false true true u v (Real.sqrt r : ℂ) = candidateJ u v (r : ℂ) := by
  let R := 1 - Real.sqrt r
  let K : ℂ × ℂ → ℂ := fun p => kernelMode false true true p.1 p.2 (Real.sqrt r : ℂ)
  let C : ℂ × ℂ → ℂ := fun p => candidateJ p.1 p.2 (r : ℂ)
  let F : ℂ × ℂ → ℂ := K - C
  have hk (a b : ℂ) (ha : ‖a‖ < R) (hb : ‖b‖ < R) : DifferentiableAt ℂ K (a, b) := by
    apply kernelMode_joint_differentiable false true true
    · simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg r)] using
          (show ‖a‖ + Real.sqrt r < 1 by dsimp [R] at ha; linarith)
    · simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg r)] using
          (show ‖b‖ + Real.sqrt r < 1 by dsimp [R] at hb; linarith)
  have hrS : r ≤ Real.sqrt r := Real.le_sqrt_self_iff.mpr hr1.le
  have hc (a b : ℂ) (ha : ‖a‖ < R) (hb : ‖b‖ < R) : DifferentiableAt ℂ C (a, b) := by
    have har : ‖a‖ + ‖(r : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      dsimp [R] at ha
      linarith
    have hbr : ‖b‖ + ‖(r : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      dsimp [R] at hb
      linarith
    exact (candidateJ_joint_analytic har hbr (W_sum_ne_zero har hbr)).differentiableAt
  have hreg (a b : ℂ) (ha : ‖a‖ < R) (hb : ‖b‖ < R) : DifferentiableAt ℂ F (a, b) :=
    (hk a b ha hb).sub (hc a b ha hb)
  have hpde (a b : ℂ) (ha : ‖a‖ < R) (hb : ‖b‖ < R) :
      a * (1 - a) * deriv (fun w => F (w, b)) a +
      b * (1 - b) * deriv (fun w => F (a, w)) b +
      (1 - 3 * (a + b) / 2) * F (a, b) = 0 := by
    have haS : ‖a‖ + Real.sqrt r < 1 := by dsimp [R] at ha; linarith
    have hbS : ‖b‖ + Real.sqrt r < 1 := by dsimp [R] at hb; linarith
    have har : ‖a‖ + ‖(r : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]; linarith
    have hbr : ‖b‖ + ‖(r : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]; linarith
    have hK := (displacement_differential true true hr hr1 haS hbS).1
    have hC := candidateJ_differential har hbr
    have hKu := ((hk a b ha hb).hasFDerivAt.comp_hasDerivAt a
      ((hasDerivAt_id a).prodMk (hasDerivAt_const a b))).differentiableAt
    have hKv := ((hk a b ha hb).hasFDerivAt.comp_hasDerivAt b
      ((hasDerivAt_const b a).prodMk (hasDerivAt_id b))).differentiableAt
    have hCu := ((hc a b ha hb).hasFDerivAt.comp_hasDerivAt a
      ((hasDerivAt_id a).prodMk (hasDerivAt_const a b))).differentiableAt
    have hCv := ((hc a b ha hb).hasFDerivAt.comp_hasDerivAt b
      ((hasDerivAt_const b a).prodMk (hasDerivAt_id b))).differentiableAt
    change a * (1 - a) * deriv ((fun w => K (w, b)) - (fun w => C (w, b))) a +
      b * (1 - b) * deriv ((fun w => K (a, w)) - (fun w => C (a, w))) b +
      (1 - 3 * (a + b) / 2) * (K (a, b) - C (a, b)) = 0
    change DifferentiableAt ℂ (fun w => K (w, b)) a at hKu
    change DifferentiableAt ℂ (fun w => K (a, w)) b at hKv
    change DifferentiableAt ℂ (fun w => C (w, b)) a at hCu
    change DifferentiableAt ℂ (fun w => C (a, w)) b at hCv
    rw [deriv_sub hKu hCu, deriv_sub hKv hCv]
    dsimp only at hK hC
    simp only [modeScale, modeB, firstModeDerivative, secondModeDerivative,
      L, OriginalGaussianExternalAnalyticCandidate.b, ite_true, one_mul] at hK hC
    dsimp only [K, C]
    linear_combination hK - hC
  have hz := positive_spatial_zero (R := R)
    (by dsimp [R]; linarith [Real.sqrt_nonneg r]) F hreg hpde
    (u := u) (v := v) (by dsimp [R]; linarith) (by dsimp [R]; linarith)
  exact sub_eq_zero.mp hz

end

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalAnalyticCandidate
