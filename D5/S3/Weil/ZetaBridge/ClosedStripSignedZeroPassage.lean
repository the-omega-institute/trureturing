/- GID: D5/S3/Weil/ZetaBridge/ClosedStripSignedZeroPassage
   generality: G
   mirror-B: none(waiver:actual-zeta-signed-zero-domain)
   mirror-E: none(waiver:infinite-zero-sum-passage)
   anchors: []
   utility: none
   digest: A common inverse-square strip envelope pays the actual signed zero sum. -/

import D5.S3.Weil.ZetaExplicit.ZeroSummability
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic

/-! Absolute summability and dominated passage for the actual signed zeta-zero series. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaBridge.ClosedStripSignedZeroPassage

open Zeta23 Zeta23.WeilEF Filter
open scoped Topology ComplexConjugate

/-- The inverse-square envelope is integrable against the EXISTING actual
zero-count weight. No nonzero-ordinate premise or new zero count is needed. -/
private theorem signed_sample_bound {D : ℝ} (hD : 0 ≤ D)
    {F : ℂ → ℂ}
    (hF : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖F z‖ ≤ D / (1 + z.re ^ (2 : ℕ)))
    (m : ℕ) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖(m : ℂ) * F z * conj (F (conj z))‖ ≤
      ((5 / 4 : ℝ) * D ^ (2 : ℕ)) *
        ((m : ℝ) / (1 + Complex.normSq z)) := by
  have hcz : |(conj z).im| ≤ 1 / 2 := by
    simpa only [Complex.conj_im, abs_neg] using hz
  have hFc : ‖F (conj z)‖ ≤ D / (1 + z.re ^ (2 : ℕ)) := by
    simpa only [Complex.conj_re] using hF (conj z) hcz
  have hy := abs_le.mp hz
  have hy2 : z.im ^ (2 : ℕ) ≤ 1 / 4 := by
    have hp := mul_nonneg
      (show 0 ≤ z.im + 1 / 2 by linarith)
      (show 0 ≤ 1 / 2 - z.im by linarith)
    nlinarith only [hp]
  have hQ : 1 + Complex.normSq z ≤
      (5 / 4 : ℝ) * (1 + z.re ^ (2 : ℕ)) ^ (2 : ℕ) := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg z.re, sq_nonneg (z.re ^ (2 : ℕ))]
  have hdecay : D ^ (2 : ℕ) / (1 + z.re ^ (2 : ℕ)) ^ (2 : ℕ) ≤
      ((5 / 4 : ℝ) * D ^ (2 : ℕ)) / (1 + Complex.normSq z) := by
    apply (div_le_div_iff₀ (by positivity)
      (by linarith [Complex.normSq_nonneg z])).2
    have hm := mul_le_mul_of_nonneg_left hQ (sq_nonneg D)
    nlinarith only [hm]
  rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_conj]
  calc
    _ = (m : ℝ) * (‖F z‖ * ‖F (conj z)‖) := by ring
    _ ≤ (m : ℝ) * ((D / (1 + z.re ^ (2 : ℕ))) *
        (D / (1 + z.re ^ (2 : ℕ)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (hF z hz) hFc (norm_nonneg _) (by positivity))
        (Nat.cast_nonneg m)
    _ = (m : ℝ) * (D ^ (2 : ℕ) /
        (1 + z.re ^ (2 : ℕ)) ^ (2 : ℕ)) := by
      rw [← div_pow]
      ring
    _ ≤ (m : ℝ) * (((5 / 4 : ℝ) * D ^ (2 : ℕ)) /
        (1 + Complex.normSq z)) :=
      mul_le_mul_of_nonneg_left hdecay (Nat.cast_nonneg m)
    _ = _ := by ring

/-- Pointwise convergence and a single common inverse-square bound on the
entire closed half-strip pay summability and convergence of the actual
zeta-zero Weil square. Multiplicities and the original signed product
V(gamma)*conj(V(conj gamma)) are retained. This assumes neither RH nor
positivity, and the zero-count summability is supplied by the existing
actual ZetaSeam theorem rather than an extra convergence premise. -/
theorem actual_zeta_signed_zero_tendsto (hs : ZetaSeam)
    {U : ℂ → ℂ} {V : ℕ → ℂ → ℂ} {D : ℝ} (hD : 0 ≤ D)
    (hbound : ∀ n z, |z.im| ≤ 1 / 2 →
      ‖V n z‖ ≤ D / (1 + z.re ^ (2 : ℕ)))
    (hlim : ∀ z : ℂ, |z.im| ≤ 1 / 2 →
      Tendsto (fun n => V n z) atTop (𝓝 (U z))) :
    (∀ n, Summable (fun ρ : (zetaZeros hs).carrier =>
      (zeroMult ρ : ℂ) * V n (gammaOf ρ) *
        conj (V n (conj (gammaOf ρ))))) ∧
    Summable (fun ρ : (zetaZeros hs).carrier =>
      (zeroMult ρ : ℂ) * U (gammaOf ρ) * conj (U (conj (gammaOf ρ)))) ∧
    Tendsto (fun n => ∑' ρ : (zetaZeros hs).carrier,
      (zeroMult ρ : ℂ) * V n (gammaOf ρ) * conj (V n (conj (gammaOf ρ))))
      atTop (𝓝 (∑' ρ : (zetaZeros hs).carrier,
        (zeroMult ρ : ℂ) * U (gammaOf ρ) * conj (U (conj (gammaOf ρ))))) := by
  have hUb (z : ℂ) (hz : |z.im| ≤ 1 / 2) :
      ‖U z‖ ≤ D / (1 + z.re ^ (2 : ℕ)) :=
    le_of_tendsto' (hlim z hz).norm (fun n => hbound n z hz)
  have hgamma (ρ : (zetaZeros hs).carrier) : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 :=
    abs_gammaOf_im_le ((zetaZeros hs).strip (ρ : ℂ) ρ.2)
  have hsummable := (zero_sum_inv_sq hs).mul_left ((5 / 4 : ℝ) * D ^ (2 : ℕ))
  refine ⟨fun n => hsummable.of_norm_bounded (fun ρ =>
      signed_sample_bound hD (hbound n) (zeroMult ρ) (hgamma ρ)),
    hsummable.of_norm_bounded (fun ρ =>
      signed_sample_bound hD hUb (zeroMult ρ) (hgamma ρ)), ?_⟩
  exact tendsto_tsum_of_dominated_convergence hsummable
    (fun ρ => by
      have hconj : |(conj (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 := by
        simpa only [Complex.conj_im, abs_neg] using hgamma ρ
      exact (tendsto_const_nhds.mul (hlim _ (hgamma ρ))).mul
        ((Complex.continuous_conj.tendsto _).comp (hlim _ hconj)))
    (Eventually.of_forall fun n ρ =>
      signed_sample_bound hD (hbound n) (zeroMult ρ) (hgamma ρ))

#print axioms actual_zeta_signed_zero_tendsto

end D5.S3.Weil.ZetaBridge.ClosedStripSignedZeroPassage
