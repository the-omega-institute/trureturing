/- GID: D5/S3/Analytic/Isolation/GoldenGermZetaSimplePole
   generality: I
   mirror-B: D5/B/S3/Analytic/Isolation/GoldenGermZetaSimplePole
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden germ zeta function has a simple pole at the golden boundary point. -/

/- Library-search audit trail (2026-08-29):
   * Pinned Mathlib was searched for meromorphic order, local normal forms,
     cobounded divergence, the zeta residue, removable-singularity extension,
     and the bounded-times-inverse little-o estimate. The relevant declarations
     are `meromorphicOrderAt`, `meromorphicOrderAt_eq_int_iff`,
     `MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt`,
     `tendsto_cobounded_iff_meromorphicOrderAt_neg`,
     `riemannZeta_residue_one`,
     `differentiableOn_update_limUnder_of_isLittleO`, and
     `Filter.IsBoundedUnder.isLittleO_sub_self_inv`.
   * No pinned Mathlib theorem stating that `(s - 1) * riemannZeta s` is
     analytic at `1` was found; the private proof below constructs that
     extension from the located removable-singularity declarations.
   * Repository searches found the exact boundary identities and nonvanishing
     in `GoldenGermZetaBoundary`, and the missing normalized-factor analyticity
     in `GoldenGermNormalizedFactorRegularity`. No existing simple-pole theorem
     for this golden germ was found.

   STOPPING JUSTIFICATION: this node closes the boundary question left open by
   `GoldenGermZetaBoundary`, using the input supplied by
   `GoldenGermNormalizedFactorRegularity`: at `1 / phi^2` the singularity is
   genuine and simple, and the germ tends to the cobounded filter on the
   punctured neighborhood. It says nothing about other points, nothing about
   the zero set, and nothing about the germ away from that stated
   neighborhood. -/

import D5.S3.Analytic.Regularity.GoldenGermNormalizedFactorRegularity
import D5.S3.Analytic.EulerGerm.GoldenGermZetaBoundary

namespace D5.S3.Analytic.Isolation.GoldenGermZetaSimplePole

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Complex Function
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Analytic.Regularity.GoldenGermNormalizedFactorRegularity
open D5.S3.Analytic.EulerGerm.GoldenGermZetaBoundary
open scoped Topology

private noncomputable def zk : ℂ → ℂ := fun s => (s - 1) * riemannZeta s

private noncomputable def zkA : ℂ → ℂ :=
  update zk 1 (limUnder (𝓝[≠] (1 : ℂ)) zk)

private noncomputable def aPt : ℂ := ((1 / Real.goldenRatio ^ 2 : ℝ) : ℂ)

private noncomputable def phiSq : ℂ := ((Real.goldenRatio ^ 2 : ℝ) : ℂ)

private noncomputable def bigG : ℂ → ℂ := fun s =>
  ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s * phiSq)) * germLocalFactor s p

private noncomputable def resid : ℂ → ℂ := fun s =>
  zkA (phiSq * s) * (bigG s / phiSq)

private noncomputable def germZeta : ℂ → ℂ := fun s =>
  riemannZeta (phiSq * s) * bigG s

private theorem u0_phiSq_ne : phiSq ≠ 0 := by
  rw [phiSq]; exact_mod_cast (by positivity : (Real.goldenRatio ^ 2 : ℝ) ≠ 0)

private theorem u1_transport : phiSq * aPt = 1 := by
  have hne : (Real.goldenRatio ^ 2 : ℝ) ≠ 0 := by positivity
  rw [phiSq, aPt, ← Complex.ofReal_mul, mul_one_div, div_self hne, Complex.ofReal_one]

private theorem u2_zkA_at_one : zkA 1 = 1 := by
  rw [zkA, update_self]; exact riemannZeta_residue_one.limUnder_eq

private theorem t1_zkA_analytic : AnalyticAt ℂ zkA 1 := by
  have hd : DifferentiableOn ℂ zkA (Metric.ball (1 : ℂ) 1) := by
    refine differentiableOn_update_limUnder_of_isLittleO
      (Metric.ball_mem_nhds (1 : ℂ) one_pos) ?_ ?_
    · intro z hz
      exact (((differentiable_id.sub_const 1).differentiableAt).mul
        (differentiableAt_riemannZeta (by simpa using hz.2))).differentiableWithinAt
    · exact (((riemannZeta_residue_one.sub_const (zk 1)).norm).isBoundedUnder_le
        ).isLittleO_sub_self_inv
  exact hd.analyticAt (Metric.ball_mem_nhds (1 : ℂ) one_pos)

private theorem t4_G_analytic : AnalyticAt ℂ bigG aPt := by
  obtain ⟨_, _, _, hana⟩ := golden_germ_normalized_factor_regularity
  have h : AnalyticAt ℂ (fun s : ℂ => ∏' p : Nat.Primes,
      (1 - (p : ℂ) ^ (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))) *
        germLocalFactor s p) aPt := by
    refine hana _ ?_
    change 1 / Real.goldenRatio ^ 3 < aPt.re
    rw [aPt]
    simp only [Complex.ofReal_re]
    apply one_div_lt_one_div_of_lt (pow_pos Real.goldenRatio_pos 2)
    nlinarith [Real.one_lt_goldenRatio, sq_pos_of_pos Real.goldenRatio_pos]
  exact h

private theorem t5_resid_analytic : AnalyticAt ℂ resid aPt := by
  have hOuter : AnalyticAt ℂ zkA (phiSq * aPt) := by
    rw [u1_transport]
    exact t1_zkA_analytic
  have hInner : AnalyticAt ℂ (fun s : ℂ => phiSq * s) aPt :=
    analyticAt_const.mul analyticAt_id
  have h : AnalyticAt ℂ (fun s : ℂ => zkA (phiSq * s) * (bigG s / phiSq)) aPt :=
    (hOuter.comp hInner).mul (t4_G_analytic.div analyticAt_const u0_phiSq_ne)
  exact h

private theorem u3_G_ne_zero : bigG aPt ≠ 0 := by
  obtain ⟨_, _, _, hpos, _, _, _, _⟩ := golden_germ_zeta_boundary_reduction
  dsimp only at hpos
  intro h
  rw [bigG, phiSq, aPt] at h
  rw [h, Complex.zero_re] at hpos
  exact lt_irrefl 0 hpos.1

private theorem u5_resid_ne_zero : resid aPt ≠ 0 := by
  have h : resid aPt = bigG aPt / phiSq := by
    rw [resid, u1_transport, u2_zkA_at_one, one_mul]
  rw [h]
  exact div_ne_zero u3_G_ne_zero u0_phiSq_ne

private theorem u4_punctured :
    ∀ᶠ s in 𝓝[≠] aPt, germZeta s = (s - aPt) ^ (-1 : ℤ) • resid s := by
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hsa : s - aPt ≠ 0 := sub_ne_zero.mpr hs
  have hne1 : phiSq * s ≠ 1 := by
    rw [← u1_transport]
    intro hc
    exact hsa (sub_eq_zero.mpr (mul_left_cancel₀ u0_phiSq_ne hc))
  have hzk : zkA (phiSq * s) = (phiSq * s - 1) * riemannZeta (phiSq * s) := by
    rw [zkA, update_of_ne hne1, zk]
  have hfac : phiSq * s - 1 = phiSq * (s - aPt) := by
    rw [mul_sub, u1_transport]
  rw [germZeta, resid, hzk, hfac, zpow_neg, zpow_one, smul_eq_mul]
  field_simp [u0_phiSq_ne]

private theorem v1_meromorphic : MeromorphicAt germZeta aPt :=
  MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mpr
    ⟨(-1 : ℤ), resid, t5_resid_analytic, u4_punctured⟩

private theorem v2_simple_pole : meromorphicOrderAt germZeta aPt = (-1 : ℤ) :=
  (meromorphicOrderAt_eq_int_iff v1_meromorphic).mpr
    ⟨resid, t5_resid_analytic, u5_resid_ne_zero, u4_punctured⟩

private theorem v3_blows_up :
    Tendsto germZeta (𝓝[≠] aPt) (Bornology.cobounded ℂ) := by
  rw [tendsto_cobounded_iff_meromorphicOrderAt_neg v1_meromorphic, v2_simple_pole]
  decide

/-- The golden germ zeta function has a genuine simple pole at `1 / phi^2`
and tends to the cobounded filter on the punctured neighborhood of that point. -/
theorem golden_germ_zeta_simple_pole :
    let germZeta : ℂ → ℂ := fun s =>
      riemannZeta (((Real.goldenRatio ^ 2 : ℝ) : ℂ) * s) *
        ∏' p : Nat.Primes,
          (1 - (p : ℂ) ^
              (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))) *
            germLocalFactor s p
    MeromorphicAt germZeta ((1 / Real.goldenRatio ^ 2 : ℝ) : ℂ) ∧
      meromorphicOrderAt germZeta
          ((1 / Real.goldenRatio ^ 2 : ℝ) : ℂ) = (-1 : ℤ) ∧
        Tendsto germZeta
          (𝓝[≠] ((1 / Real.goldenRatio ^ 2 : ℝ) : ℂ))
          (Bornology.cobounded ℂ) := by
  dsimp only
  exact ⟨v1_meromorphic, v2_simple_pole, v3_blows_up⟩

#print axioms golden_germ_zeta_simple_pole

end D5.S3.Analytic.Isolation.GoldenGermZetaSimplePole
