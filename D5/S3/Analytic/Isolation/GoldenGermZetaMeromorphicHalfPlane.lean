/- GID: D5/S3/Analytic/Isolation/GoldenGermZetaMeromorphicHalfPlane
   generality: I
   mirror-B: D5/B/S3/Analytic/Isolation/GoldenGermZetaMeromorphicHalfPlane
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden germ zeta is meromorphic above 1/phi^3 with no pole away from 1/phi^2. -/

/- Library-search audit trail (2026-08-29):
   * Pinned Mathlib was searched for meromorphy on a set, conversion from
     analyticity to meromorphy, the analytic region of the Riemann zeta
     function, and nonnegativity of meromorphic order at analytic points.
     The relevant declarations are `MeromorphicOn`
     (`Mathlib/Analysis/Meromorphic/Basic.lean:473`, definitionally
     `forall x in U, MeromorphicAt f x`), `AnalyticAt.meromorphicAt`
     (`Mathlib/Analysis/Meromorphic/Basic.lean:40`),
     `analyticOn_riemannZeta`
     (`Mathlib/NumberTheory/LSeries/RiemannZeta.lean:144`), and
     `AnalyticAt.meromorphicOrderAt_nonneg`
     (`Mathlib/Analysis/Meromorphic/Order.lean:291`).
   * Repository searches found the meromorphy and exact order at the boundary
     point in `GoldenGermZetaSimplePole`, and normalized-factor analyticity on
     the whole half-plane in `GoldenGermNormalizedFactorRegularity`. No
     existing theorem stating this half-plane result or its unique-pole
     consequence was found.

   STOPPING JUSTIFICATION: this node proves meromorphy on the open half-plane
   and rules out poles there away from `1 / phi^2`. It says nothing about the
   zero set, nothing at or left of `Re s = 1 / phi^3`, and does not compute the
   order at `1 / phi^2`; that is the upstream simple-pole node's job. -/

import D5.S3.Analytic.Isolation.GoldenGermZetaSimplePole

namespace D5.S3.Analytic.Isolation.GoldenGermZetaMeromorphicHalfPlane

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Analytic.Isolation.GoldenGermZetaSimplePole
open D5.S3.Analytic.Regularity.GoldenGermNormalizedFactorRegularity

private noncomputable def aPt : ℂ := ((1 / Real.goldenRatio ^ 2 : ℝ) : ℂ)

private noncomputable def phiSq : ℂ := ((Real.goldenRatio ^ 2 : ℝ) : ℂ)

private noncomputable def bigG : ℂ → ℂ := fun s =>
  ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))) *
    germLocalFactor s p

private noncomputable def germZeta : ℂ → ℂ := fun s =>
  riemannZeta (((Real.goldenRatio ^ 2 : ℝ) : ℂ) * s) *
    ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))) *
      germLocalFactor s p

private theorem w0_phiSq_ne : phiSq ≠ 0 := by
  rw [phiSq]; exact_mod_cast (by positivity : (Real.goldenRatio ^ 2 : ℝ) ≠ 0)

private theorem w0_transport : phiSq * aPt = 1 := by
  have hne : (Real.goldenRatio ^ 2 : ℝ) ≠ 0 := by positivity
  rw [phiSq, aPt, ← Complex.ofReal_mul, mul_one_div, div_self hne, Complex.ofReal_one]

private theorem w1_avoids_pole (s : ℂ) (hs : s ≠ aPt) : phiSq * s ≠ 1 := by
  rw [← w0_transport]
  intro hc
  exact hs (mul_left_cancel₀ w0_phiSq_ne hc)

private theorem w2_zeta_factor_analytic (s : ℂ) (hs : s ≠ aPt) :
    AnalyticAt ℂ (fun z : ℂ => riemannZeta (phiSq * z)) s := by
  have hOuter : AnalyticAt ℂ riemannZeta (phiSq * s) :=
    analyticOn_riemannZeta _ (by simpa using w1_avoids_pole s hs)
  have hInner : AnalyticAt ℂ (fun z : ℂ => phiSq * z) s :=
    analyticAt_const.mul analyticAt_id
  exact hOuter.comp hInner

private theorem w3_G_analytic (s : ℂ) (hs : 1 / Real.goldenRatio ^ 3 < s.re) :
    AnalyticAt ℂ bigG s := by
  obtain ⟨_, _, _, hana⟩ :=
    golden_germ_normalized_factor_regularity
  have h : AnalyticAt ℂ (fun z : ℂ => ∏' p : Nat.Primes,
      (1 - (p : ℂ) ^ (-z * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))) *
        germLocalFactor z p) s := hana _ hs
  exact h

private theorem w4_analytic_off_abscissa (s : ℂ)
    (hreg : 1 / Real.goldenRatio ^ 3 < s.re) (hs : s ≠ aPt) :
    AnalyticAt ℂ germZeta s := by
  have hz : AnalyticAt ℂ (fun z : ℂ => riemannZeta (phiSq * z)) s :=
    w2_zeta_factor_analytic s hs
  have hg : AnalyticAt ℂ bigG s := w3_G_analytic s hreg
  have h : AnalyticAt ℂ (fun z : ℂ => riemannZeta (phiSq * z) * bigG z) s :=
    hz.mul hg
  exact h

private theorem x1_meromorphicOn :
    MeromorphicOn germZeta {s : ℂ | 1 / Real.goldenRatio ^ 3 < s.re} := by
  intro s hs
  by_cases hcase : s = aPt
  · subst hcase
    obtain ⟨hmero, _, _⟩ := golden_germ_zeta_simple_pole
    exact hmero
  · exact (w4_analytic_off_abscissa s hs hcase).meromorphicAt

private theorem x2_unique_pole (s : ℂ)
    (hreg : s ∈ {s : ℂ | 1 / Real.goldenRatio ^ 3 < s.re}) (hs : s ≠ aPt) :
    AnalyticAt ℂ germZeta s :=
  w4_analytic_off_abscissa s hreg hs

private theorem x3_order_nonneg_off_abscissa (s : ℂ)
    (hreg : s ∈ {s : ℂ | 1 / Real.goldenRatio ^ 3 < s.re}) (hs : s ≠ aPt) :
    0 ≤ meromorphicOrderAt germZeta s :=
  (w4_analytic_off_abscissa s hreg hs).meromorphicOrderAt_nonneg

/-- The golden germ zeta function is meromorphic above `1 / phi^3`, and it is
analytic at every point of that half-plane other than `1 / phi^2`. -/
theorem golden_germ_zeta_meromorphic_half_plane :
    let germZeta : ℂ → ℂ := fun s =>
      riemannZeta (((Real.goldenRatio ^ 2 : ℝ) : ℂ) * s) *
        ∏' p : Nat.Primes,
          (1 - (p : ℂ) ^
              (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))) *
            germLocalFactor s p
    MeromorphicOn germZeta {s : ℂ | 1 / Real.goldenRatio ^ 3 < s.re} ∧
      (∀ s ∈ {s : ℂ | 1 / Real.goldenRatio ^ 3 < s.re},
        s ≠ ((1 / Real.goldenRatio ^ 2 : ℝ) : ℂ) → AnalyticAt ℂ germZeta s) ∧
      ∀ s ∈ {s : ℂ | 1 / Real.goldenRatio ^ 3 < s.re},
        s ≠ ((1 / Real.goldenRatio ^ 2 : ℝ) : ℂ) →
          0 ≤ meromorphicOrderAt germZeta s := by
  dsimp only
  exact ⟨x1_meromorphicOn, x2_unique_pole, x3_order_nonneg_off_abscissa⟩

#print axioms golden_germ_zeta_meromorphic_half_plane

end D5.S3.Analytic.Isolation.GoldenGermZetaMeromorphicHalfPlane
