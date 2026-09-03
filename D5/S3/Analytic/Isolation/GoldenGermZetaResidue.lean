/- GID: D5/S3/Analytic/Isolation/GoldenGermZetaResidue
   generality: I
   mirror-B: D5/B/S3/Analytic/Isolation/GoldenGermZetaResidue
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The simple golden boundary pole has the explicit positive residue G(1/phi^2)/phi^2. -/

/- Library-search audit trail (2026-09-03):
   * Repository searches found the exact transported zeta kernel and algebraic
     boundary identity in `golden_germ_zeta_boundary_reduction`, continuity of
     the normalized factor in `golden_germ_normalized_factor_regularity`, and
     order minus one in `golden_germ_zeta_simple_pole`.
   * Pinned Mathlib's `Tendsto.mul`, `ContinuousAt.tendsto`, and filter
     monotonicity combine those frozen inputs. The zeta residue itself is used
     only through the transported limit already frozen by the boundary module.
   * No existing D5 declaration states this explicit residue limit or its
     positive-real value at the golden boundary.

   STOPPING JUSTIFICATION: this theorem identifies the residue only at
   `1 / phi^2`. It makes no pole, zero-free, O-5, or RH claim at any other
   point or on any larger region. -/

import D5.S3.Analytic.Isolation.GoldenGermZetaSimplePole

namespace D5.S3.Analytic.Isolation.GoldenGermZetaResidue

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Complex
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Analytic.EulerGerm.GoldenGermZetaBoundary
open D5.S3.Analytic.Regularity.GoldenGermNormalizedFactorRegularity
open D5.S3.Analytic.Isolation.GoldenGermZetaSimplePole
open scoped Topology

noncomputable section

private noncomputable def phiSq : ℂ :=
  ((Real.goldenRatio ^ 2 : ℝ) : ℂ)

private noncomputable def aPt : ℂ :=
  ((1 / Real.goldenRatio ^ 2 : ℝ) : ℂ)

private noncomputable def bigG : ℂ → ℂ := fun s =>
  ∏' p : Nat.Primes,
    (1 - (p : ℂ) ^ (-s * phiSq)) * germLocalFactor s p

private noncomputable def germZeta : ℂ → ℂ := fun s =>
  riemannZeta (phiSq * s) * bigG s

private theorem boundary_inside_continuation_check :
    1 / Real.goldenRatio ^ 3 < 1 / Real.goldenRatio ^ 2 := by
  apply one_div_lt_one_div_of_lt (pow_pos Real.goldenRatio_pos 2)
  nlinarith [Real.one_lt_goldenRatio,
    sq_pos_of_pos Real.goldenRatio_pos]

private theorem explicit_residue_limit :
    Tendsto (fun s : ℂ => (s - aPt) * germZeta s)
      (𝓝[≠] aPt) (𝓝 (bigG aPt / phiSq)) := by
  obtain ⟨continuedGerm, hcontinued, _, _, hidentity,
      htransported, _, _⟩ := golden_germ_zeta_boundary_reduction
  change (∀ s, continuedGerm s = germZeta s.1) at hcontinued
  change (∀ s,
    (s.1 - aPt) * continuedGerm s =
      ((phiSq * s.1 - 1) * riemannZeta (phiSq * s.1)) *
        (bigG s.1 / phiSq)) at hidentity
  change Tendsto
    (fun s : ℂ => (phiSq * s - 1) * riemannZeta (phiSq * s))
    (𝓝[≠] aPt) (𝓝 1) at htransported
  obtain ⟨_, _, hcontinuous, _⟩ :=
    golden_germ_normalized_factor_regularity
  change ContinuousAt bigG aPt at hcontinuous
  have hfactorLimit :
      Tendsto (fun s : ℂ => bigG s / phiSq)
        (𝓝[≠] aPt) (𝓝 (bigG aPt / phiSq)) := by
    exact (hcontinuous.tendsto.div_const phiSq).mono_left inf_le_left
  have hproduct := htransported.mul hfactorLimit
  have hdomain : ∀ᶠ s : ℂ in 𝓝[≠] aPt,
      1 / Real.goldenRatio ^ 3 < s.re := by
    have hnhds : {s : ℂ | 1 / Real.goldenRatio ^ 3 < s.re} ∈ 𝓝 aPt := by
      apply (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      change 1 / Real.goldenRatio ^ 3 < aPt.re
      rw [aPt, Complex.ofReal_re]
      exact boundary_inside_continuation_check
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds hnhds
  have hrewritten :
      Tendsto (fun s : ℂ => (s - aPt) * germZeta s)
        (𝓝[≠] aPt) (𝓝 (1 * (bigG aPt / phiSq))) := by
    refine hproduct.congr' ?_
    filter_upwards [hdomain] with s hs
    let st : {z : ℂ // 1 / Real.goldenRatio ^ 3 < z.re} := ⟨s, hs⟩
    have hcontinuedAt : continuedGerm st = germZeta s := by
      exact hcontinued st
    calc
      (phiSq * s - 1) * riemannZeta (phiSq * s) *
            (bigG s / phiSq) = (s - aPt) * continuedGerm st := by
        exact (hidentity st).symm
      _ = (s - aPt) * germZeta s := by
        rw [hcontinuedAt]
  simpa only [one_mul] using hrewritten

private theorem explicit_residue_positive_real :
    (bigG aPt / phiSq).im = 0 ∧
      0 < (bigG aPt / phiSq).re := by
  obtain ⟨_, _, _, hpositive, _, _, _, _⟩ :=
    golden_germ_zeta_boundary_reduction
  change 0 < (bigG aPt).re ∧ (bigG aPt).im = 0 at hpositive
  let x : ℝ := (bigG aPt).re
  have hxPositive : 0 < x := by
    exact hpositive.1
  have hGReal : bigG aPt = (x : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using hpositive.2
  have hphiPositive : 0 < Real.goldenRatio ^ 2 := by
    positivity
  have hresidueReal :
      bigG aPt / phiSq =
        ((x / Real.goldenRatio ^ 2 : ℝ) : ℂ) := by
    rw [hGReal, phiSq, Complex.ofReal_div]
  rw [hresidueReal]
  constructor
  · exact Complex.ofReal_im _
  · rw [Complex.ofReal_re]
    exact div_pos hxPositive hphiPositive

/-- At the golden boundary `a = 1 / phi^2`, the continued zeta-normalized
golden germ has a simple pole whose residue is exactly `G(a) / phi^2`. This
residue is real and strictly positive. -/
theorem golden_germ_zeta_residue :
    let G : ℂ → ℂ := fun s =>
      ∏' p : Nat.Primes,
        (1 - (p : ℂ) ^
            (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))) *
          germLocalFactor s p
    let Z : ℂ → ℂ := fun s =>
      riemannZeta (((Real.goldenRatio ^ 2 : ℝ) : ℂ) * s) * G s
    let a : ℂ := ((1 / Real.goldenRatio ^ 2 : ℝ) : ℂ)
    meromorphicOrderAt Z a = (-1 : ℤ) ∧
      Tendsto (fun s : ℂ => (s - a) * Z s)
        (𝓝[≠] a)
        (𝓝 (G a / ((Real.goldenRatio ^ 2 : ℝ) : ℂ))) ∧
      (G a / ((Real.goldenRatio ^ 2 : ℝ) : ℂ)).im = 0 ∧
      0 < (G a / ((Real.goldenRatio ^ 2 : ℝ) : ℂ)).re := by
  dsimp only
  have hsimple := golden_germ_zeta_simple_pole
  dsimp only at hsimple
  change MeromorphicAt germZeta aPt ∧
    meromorphicOrderAt germZeta aPt = (-1 : ℤ) ∧
      Tendsto germZeta (𝓝[≠] aPt) (Bornology.cobounded ℂ) at hsimple
  have horder : meromorphicOrderAt germZeta aPt = (-1 : ℤ) := by
    exact hsimple.2.1
  change meromorphicOrderAt germZeta aPt = (-1 : ℤ) ∧
    Tendsto (fun s : ℂ => (s - aPt) * germZeta s)
      (𝓝[≠] aPt) (𝓝 (bigG aPt / phiSq)) ∧
    (bigG aPt / phiSq).im = 0 ∧
    0 < (bigG aPt / phiSq).re
  exact And.intro horder
    (And.intro explicit_residue_limit explicit_residue_positive_real)

#print axioms golden_germ_zeta_residue

end

end D5.S3.Analytic.Isolation.GoldenGermZetaResidue
