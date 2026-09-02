/- GID: D5/S3/Analytic/Isolation/GoldenGermFirstPoleAsymptotic
   generality: I
   mirror-B: D5/B/S3/Analytic/Isolation/GoldenGermFirstPoleAsymptotic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden Euler germ has a positive right-hand first-pole asymptotic. -/

import D5.S3.Analytic.EulerGerm.GoldenGermRealAxisPositivity
import D5.S3.Analytic.EulerGerm.GoldenGermZetaFactorization
import D5.S3.Analytic.Isolation.GoldenGermZetaResidue

/- Library-search audit trail (2026-09-03):
   * Repository searches found the exact punctured complex residue limit in
     `golden_germ_zeta_residue`, agreement with the prime product in
     `golden_germ_zeta_factorization`, and real-axis positivity in
     `golden_germ_real_axis_positivity`. No D5 theorem states the right-hand
     quantitative asymptotic or positive blow-up proved below.
   * The repository theorem `log_tendsto_atTop_of_pos_simple_pole` records the
     same positive-residue pattern only after applying `Real.log`; it does not
     imply the required unlogged product limit.
   * Pinned Mathlib supplies the exact filter transport lemma
     `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within`, continuity of
     `Complex.ofReal` and `Complex.re`, `tendsto_inv_nhdsGT_zero`, and
     `Filter.Tendsto.pos_mul_atTop`.

   This theorem concerns only the real convergence ray immediately to the
   right of `1 / phi^2`. It makes no Tauberian, O-5, zero-free, or RH claim. -/

namespace D5.S3.Analytic.Isolation.GoldenGermFirstPoleAsymptotic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Complex Set
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Analytic.EulerGerm.GoldenGermRealAxisPositivity
open D5.S3.Analytic.EulerGerm.GoldenGermZetaFactorization
open D5.S3.Analytic.Isolation.GoldenGermZetaResidue
open scoped Topology

noncomputable section

/-- On the real ray to the right of the first golden boundary, the Euler germ
has the quantitative asymptotic `(sigma - a) P(sigma) -> G(a) / phi^2` in
real and imaginary parts. Its positive residue then forces the real part of
the unscaled product to diverge to positive infinity. -/
theorem golden_germ_first_pole_asymptotic :
    let P : ℝ → ℂ := fun sigma =>
      ∏' p : Nat.Primes, germLocalFactor (sigma : ℂ) p
    let G : ℂ → ℂ := fun s =>
      ∏' p : Nat.Primes,
        (1 - (p : ℂ) ^
            (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))) *
          germLocalFactor s p
    let a : ℝ := 1 / Real.goldenRatio ^ 2
    let c : ℂ := G (a : ℂ) / ((Real.goldenRatio ^ 2 : ℝ) : ℂ)
    Tendsto (fun sigma : ℝ =>
        (((sigma - a : ℝ) : ℂ) * P sigma).re)
      (𝓝[>] a) (𝓝 c.re) ∧
    Tendsto (fun sigma : ℝ =>
        (((sigma - a : ℝ) : ℂ) * P sigma).im)
      (𝓝[>] a) (𝓝 0) ∧
    Tendsto (fun sigma : ℝ => (P sigma).re) (𝓝[>] a) atTop := by
  fail_if_success rfl
  fail_if_success (solve | simp)
  fail_if_success (solve | trivial)
  dsimp only
  let phiSq : ℂ := ((Real.goldenRatio ^ 2 : ℝ) : ℂ)
  let a : ℝ := 1 / Real.goldenRatio ^ 2
  let P : ℝ → ℂ := fun sigma =>
    ∏' p : Nat.Primes, germLocalFactor (sigma : ℂ) p
  let G : ℂ → ℂ := fun s =>
    ∏' p : Nat.Primes,
      (1 - (p : ℂ) ^ (-s * phiSq)) * germLocalFactor s p
  let Z : ℂ → ℂ := fun s => riemannZeta (phiSq * s) * G s
  let c : ℂ := G (a : ℂ) / phiSq
  change Tendsto (fun sigma : ℝ =>
      (((sigma - a : ℝ) : ℂ) * P sigma).re)
      (𝓝[>] a) (𝓝 c.re) ∧
    Tendsto (fun sigma : ℝ =>
      (((sigma - a : ℝ) : ℂ) * P sigma).im)
      (𝓝[>] a) (𝓝 0) ∧
    Tendsto (fun sigma : ℝ => (P sigma).re) (𝓝[>] a) atTop
  have hresidue := golden_germ_zeta_residue
  dsimp only at hresidue
  change meromorphicOrderAt Z (a : ℂ) = (-1 : ℤ) ∧
      Tendsto (fun s : ℂ => (s - (a : ℂ)) * Z s)
        (𝓝[≠] (a : ℂ)) (𝓝 c) ∧
      c.im = 0 ∧ 0 < c.re at hresidue
  rcases hresidue with ⟨_, hresidueLimit, _, hcPos⟩
  rcases golden_germ_zeta_factorization with
    ⟨hfactorization, _, _⟩
  have hofReal :
      Tendsto (fun sigma : ℝ => (sigma : ℂ))
        (𝓝[>] a) (𝓝[≠] (a : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (Complex.continuous_ofReal.tendsto a).mono_left
        (nhdsWithin_le_nhds : (𝓝[>] a) ≤ 𝓝 a)
    · filter_upwards [self_mem_nhdsWithin] with sigma hsigma
      rw [mem_compl_singleton_iff]
      intro hcomplex
      exact (ne_of_gt (show a < sigma from hsigma))
        (Complex.ofReal_injective hcomplex)
  have hscaled :
      Tendsto (fun sigma : ℝ =>
        ((sigma - a : ℝ) : ℂ) * P sigma) (𝓝[>] a) (𝓝 c) := by
    apply (hresidueLimit.comp hofReal).congr'
    filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    have hsigma' : 1 / Real.goldenRatio ^ 2 < sigma := by
      change a < sigma
      exact hsigma
    have hfactorAt : P sigma = Z (sigma : ℂ) :=
      hfactorization (sigma : ℂ) hsigma'
    change ((sigma : ℂ) - (a : ℂ)) * Z (sigma : ℂ) =
      ((sigma - a : ℝ) : ℂ) * P sigma
    rw [← hfactorAt, Complex.ofReal_sub]
  have hre :
      Tendsto (fun sigma : ℝ =>
        (((sigma - a : ℝ) : ℂ) * P sigma).re)
        (𝓝[>] a) (𝓝 c.re) :=
    (Complex.continuous_re.tendsto c).comp hscaled
  have him :
      Tendsto (fun sigma : ℝ =>
        (((sigma - a : ℝ) : ℂ) * P sigma).im)
        (𝓝[>] a) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    have haxis := golden_germ_real_axis_positivity sigma hsigma
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, haxis.1]
    ring
  have hsub :
      Tendsto (fun sigma : ℝ => sigma - a) (𝓝[>] a) (𝓝[>] 0) := by
    have hcontinuous :
        Tendsto (fun sigma : ℝ => sigma - a) (𝓝 a) (𝓝 (a - a)) :=
      tendsto_id.sub (tendsto_const_nhds (x := a))
    have hzero :
        Tendsto (fun sigma : ℝ => sigma - a) (𝓝[>] a) (𝓝 0) := by
      simpa using hcontinuous.mono_left
        (nhdsWithin_le_nhds : (𝓝[>] a) ≤ 𝓝 a)
    refine tendsto_nhdsWithin_iff.mpr ⟨hzero, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    exact sub_pos.mpr (show a < sigma from hsigma)
  have hinv :
      Tendsto (fun sigma : ℝ => (sigma - a)⁻¹) (𝓝[>] a) atTop :=
    tendsto_inv_nhdsGT_zero.comp hsub
  have hblowup :
      Tendsto (fun sigma : ℝ =>
        (((sigma - a : ℝ) : ℂ) * P sigma).re * (sigma - a)⁻¹)
        (𝓝[>] a) atTop :=
    hre.pos_mul_atTop hcPos hinv
  refine ⟨hre, him, ?_⟩
  apply hblowup.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  have hne : sigma - a ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt (show a < sigma from hsigma))
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  field_simp [hne]

private theorem one_is_right_of_golden_boundary :
    1 / Real.goldenRatio ^ 2 < (1 : ℝ) := by
  rw [div_lt_one (sq_pos_of_pos Real.goldenRatio_pos)]
  nlinarith [Real.one_lt_goldenRatio]

#print axioms golden_germ_first_pole_asymptotic

end

end D5.S3.Analytic.Isolation.GoldenGermFirstPoleAsymptotic
