/- GID: D5/S3/Weil/Analytic/NymanShellScale
   generality: I
   mirror-B: D5/B/S3/Weil/Analytic/NymanShellScale
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform control between adjacent reciprocal integer scales. -/

import D5.S3.Weil.Analytic.NymanShellMellin

/-! Uniform control between adjacent reciprocal integer scales. -/

set_option autoImplicit false
noncomputable section
open Finset Filter ArithmeticFunction Complex
open scoped Topology ArithmeticFunction.Moebius
open NymanShellMellin

namespace NymanShellScale

private theorem scaled_finite {W : ℝ→ℂ} (hW : ∀ x∉Set.Ioo (1:ℝ) 2,W x=0)
    {R : ℕ} {t : ℝ} (ht : 0<t) (hR : 2≤(R:ℝ)*t) :
    scaled W t=∑ n∈range (R+1),(μ n:ℂ)*W ((n:ℝ)*t) := by
  unfold scaled
  apply tsum_eq_sum
  intro n hn
  have hRn : (R:ℝ)≤n := by exact_mod_cast (show R≤n by rw [mem_range,not_lt] at hn; omega)
  have hnt : 2≤(n:ℝ)*t := hR.trans (mul_le_mul_of_nonneg_right hRn ht.le)
  rw [hW _ (by intro h; exact hnt.not_gt h.2),mul_zero]

private theorem mobius_norm_le_one (n : ℕ) : ‖(μ n:ℂ)‖≤1 := by
  rw [Complex.norm_intCast]
  exact_mod_cast abs_moebius_le_one (n:=n)

/-- Moving from an integer scale to the entire adjacent real-scale interval costs
a uniformly bounded error, given a globally Lipschitz compact kernel. -/
theorem scale_difference {W : ℝ→ℂ} (hW : ∀ x∉Set.Ioo (1:ℝ) 2,W x=0)
    {K : ℝ} (hK : 0≤K) (hlip : ∀ x y : ℝ, ‖W x-W y‖≤K*|x-y|)
    {N : ℕ} (hN : 0<N) {t : ℝ} (ht₁ : ((N:ℝ)+1)⁻¹≤t) (ht₂ : t≤(N:ℝ)⁻¹) :
    ‖scaled W t-scaled W ((N:ℝ)⁻¹)‖≤10*K := by
  let R := 2*(N+1)
  have hNr : (0:ℝ)<N := by positivity
  have ht : 0<t := (by positivity : (0:ℝ)<((N:ℝ)+1)⁻¹).trans_le ht₁
  have hR : 2≤(R:ℝ)*t := by
    have he : (R:ℝ)=2*((N:ℝ)+1) := by dsimp [R]; push_cast; ring
    rw [he]
    calc
      _ = (2*((N:ℝ)+1))*((N:ℝ)+1)⁻¹ := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left ht₁ (by positivity)
  have hR' : 2≤(R:ℝ)*(N:ℝ)⁻¹ := hR.trans (mul_le_mul_of_nonneg_left ht₂ (by positivity))
  rw [scaled_finite hW ht hR,scaled_finite hW (inv_pos.mpr hNr) hR',←sum_sub_distrib]
  have hdelta : |t-(N:ℝ)⁻¹|≤((N:ℝ)*((N:ℝ)+1))⁻¹ := by
    rw [abs_of_nonpos (sub_nonpos.mpr ht₂)]
    have he : (N:ℝ)⁻¹-((N:ℝ)+1)⁻¹=((N:ℝ)*((N:ℝ)+1))⁻¹ := by field_simp; ring
    linarith
  have hpoint (n : ℕ) (hn : n∈range (R+1)) :
      ‖(μ n:ℂ)*W ((n:ℝ)*t)-(μ n:ℂ)*W ((n:ℝ)*(N:ℝ)⁻¹)‖≤2*K/(N:ℝ) := by
    have hnR : (n:ℝ)≤2*((N:ℝ)+1) := by
      have hn' : n≤R := by have hm := mem_range.mp hn; omega
      dsimp [R] at hn'
      exact_mod_cast hn'
    rw [←mul_sub,norm_mul]
    calc
      _ ≤ 1*‖W ((n:ℝ)*t)-W ((n:ℝ)*(N:ℝ)⁻¹)‖ :=
        mul_le_mul_of_nonneg_right (mobius_norm_le_one n) (norm_nonneg _)
      _ ≤ K*|(n:ℝ)*t-(n:ℝ)*(N:ℝ)⁻¹| := by simpa using hlip ((n:ℝ)*t) ((n:ℝ)*(N:ℝ)⁻¹)
      _ = K*((n:ℝ)*|t-(N:ℝ)⁻¹|) := by rw [←mul_sub,abs_mul,abs_of_nonneg (by positivity)]
      _ ≤ K*(2*((N:ℝ)+1)*((N:ℝ)*((N:ℝ)+1))⁻¹) := by gcongr
      _ = 2*K/(N:ℝ) := by field_simp
  calc
    _ ≤ ∑ n∈range (R+1),‖(μ n:ℂ)*W ((n:ℝ)*t)-(μ n:ℂ)*W ((n:ℝ)*(N:ℝ)⁻¹)‖ := norm_sum_le _ _
    _ ≤ ∑ _n∈range (R+1),2*K/(N:ℝ) := sum_le_sum hpoint
    _ = ((R+1:ℕ):ℝ)*(2*K/(N:ℝ)) := by simp
    _ ≤ 10*K := by
      have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
      have hle : ((R+1:ℕ):ℝ)≤5*(N:ℝ) := by dsimp [R]; push_cast; linarith
      calc
        _ ≤ 5*(N:ℝ)*(2*K/(N:ℝ)) := mul_le_mul_of_nonneg_right hle (by positivity)
        _ = _ := by field_simp; ring

end NymanShellScale
