/- GID: D5/S3/Analytic/EulerGerm/GoldenGermZetaBoundary
   generality: I
   mirror-B: D5/B/S3/Analytic/EulerGerm/GoldenGermZetaBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Boundary data isolate normalized-factor regularity as a sufficient missing input. -/

/- Library-search audit trail (2026-08-28):
   * Pinned Mathlib's `riemannZeta_residue_one` supplies the zeta residue;
     it is transported here and not reproved.
   * `GoldenGermZetaContinuation.golden_germ_zeta_continuation` supplies the
     continued germ and its computation rule on `Re s > 1 / phi^3`.
   * `MultipliableUniformlyOn.lean` has a uniform-product M-test, but the
     frozen factorization exposes only pointwise summability. Its cancellation
     majorants are private, so continuity of `G` at the boundary is not yet a
     declared consequence.

   STOPPING JUSTIFICATION: the complex-neighborhood conclusion remains Rung 1:
   this theorem does not settle whether the abscissa is a genuine singularity.
   It now records the frozen real-ray strength: `G` is positive at the boundary,
   and the divided prime product has the candidate residue as a right-hand real
   limit. The latter is the real-axis analogue of Rung 2, not a pole result:
   pointwise positivity does not prevent `G sigma` from tending to zero as
   `sigma` decreases to the boundary. Rung 3 follows from the sufficient future
   input `ContinuousAt G ((1 / phi^2 : Real) : Complex)` together with the exact
   identity and transported zeta residue. Complex Rung 2 still requires `G` to
   be nonzero on a punctured complex neighborhood. Direct projections or
   standard equivalences from this conjunction are corollaries, not distinct
   contracts: no consumer, independent semantics, dependency barrier, or
   substantial proof content warrants another name. Continuity or complex
   punctured-neighborhood nonvanishing crosses that dependency barrier and
   warrants a distinct future regularity contract. -/

import D5.S3.Analytic.EulerGerm.GoldenGermZetaContinuation

namespace D5.S3.Analytic.EulerGerm.GoldenGermZetaBoundary

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Analytic.EulerGerm.GoldenGermZetaContinuation
open Filter
open scoped Topology

noncomputable section

/-- At `a = 1 / phi^2`, the continued germ's candidate residue is the
transported zeta residue times `G / phi^2`. The normalized factor is positive
at `a`, and the divided prime product has the candidate residue as a right-hand
real limit. No continuity or complex-neighborhood nonvanishing of `G` is
asserted, so the singularity question remains open. -/
theorem golden_germ_zeta_boundary_reduction :
    let G : Complex -> Complex := fun s =>
      ∏' p : Nat.Primes,
        (1 - (p : Complex) ^
            (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))) *
          germLocalFactor s p
    ∃ continuedGerm :
        {s : Complex // 1 / Real.goldenRatio ^ 3 < s.re} -> Complex,
      (∀ s, continuedGerm s =
        riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s.1) * G s.1) ∧
      1 / Real.goldenRatio ^ 3 < 1 / Real.goldenRatio ^ 2 ∧
      (0 < (G ((1 / Real.goldenRatio ^ 2 : Real) : Complex)).re ∧
        (G ((1 / Real.goldenRatio ^ 2 : Real) : Complex)).im = 0) ∧
      (∀ s,
        (s.1 - ((1 / Real.goldenRatio ^ 2 : Real) : Complex)) * continuedGerm s =
          ((((Real.goldenRatio ^ 2 : Real) : Complex) * s.1 - 1) *
              riemannZeta
                (((Real.goldenRatio ^ 2 : Real) : Complex) * s.1)) *
            (G s.1 / ((Real.goldenRatio ^ 2 : Real) : Complex))) ∧
      Tendsto
        (fun s : Complex =>
          (((Real.goldenRatio ^ 2 : Real) : Complex) * s - 1) *
            riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s))
        (𝓝[≠] ((1 / Real.goldenRatio ^ 2 : Real) : Complex)) (𝓝 1) ∧
      Tendsto
        (fun sigma : Real =>
          (((sigma - 1 / Real.goldenRatio ^ 2 : Real) : Complex) *
              ∏' p : Nat.Primes, germLocalFactor (sigma : Complex) p) /
            G (sigma : Complex))
        (𝓝[>] (1 / Real.goldenRatio ^ 2 : Real))
        (𝓝 (1 / ((Real.goldenRatio ^ 2 : Real) : Complex))) ∧
      NeBot (𝓝[≠] ((1 / Real.goldenRatio ^ 2 : Real) : Complex)) := by
  dsimp only
  rcases golden_germ_zeta_continuation with
    ⟨⟨continuedGerm, hcontinued, _⟩, _, hpositive⟩
  have hlt : 1 / Real.goldenRatio ^ 3 < 1 / Real.goldenRatio ^ 2 := by
    apply one_div_lt_one_div_of_lt (pow_pos Real.goldenRatio_pos 2)
    nlinarith [Real.one_lt_goldenRatio, sq_pos_of_pos Real.goldenRatio_pos]
  have hcritical :
      ((Real.goldenRatio ^ 2 : Real) : Complex) *
          ((1 / Real.goldenRatio ^ 2 : Real) : Complex) = 1 := by
    have ha : ((1 / Real.goldenRatio ^ 2 : Real) : Complex) =
        ((Real.goldenRatio ^ 2 : Real) : Complex)⁻¹ := by
      norm_cast
      simp only [one_div]
    rw [ha]
    exact mul_inv_cancel₀ (by
      exact_mod_cast pow_ne_zero 2 Real.goldenRatio_ne_zero)
  have hscale : Tendsto
      (fun s : Complex => ((Real.goldenRatio ^ 2 : Real) : Complex) * s)
      (𝓝[≠] ((1 / Real.goldenRatio ^ 2 : Real) : Complex)) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : Continuous
          (fun s : Complex =>
            ((Real.goldenRatio ^ 2 : Real) : Complex) * s) :=
          continuous_const.mul continuous_id
      have hcAt : Tendsto
          (fun s : Complex =>
            ((Real.goldenRatio ^ 2 : Real) : Complex) * s)
          (nhds ((1 / Real.goldenRatio ^ 2 : Real) : Complex)) (nhds 1) := by
        have hcT := hc.tendsto
          ((1 / Real.goldenRatio ^ 2 : Real) : Complex)
        rw [hcritical] at hcT
        exact hcT
      exact hcAt.mono_left inf_le_left
    · filter_upwards [eventually_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
      intro h
      apply hs
      apply mul_left_cancel₀
        (show ((Real.goldenRatio ^ 2 : Real) : Complex) ≠ 0 by
          exact_mod_cast pow_ne_zero 2 Real.goldenRatio_ne_zero)
      rw [h, hcritical]
  have htransported : Tendsto
      (fun s : Complex =>
        (((Real.goldenRatio ^ 2 : Real) : Complex) * s - 1) *
          riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s))
      (𝓝[≠] ((1 / Real.goldenRatio ^ 2 : Real) : Complex)) (𝓝 1) :=
    riemannZeta_residue_one.comp hscale
  refine ⟨continuedGerm, hcontinued.2, hlt, hpositive _ hlt, ?_,
    htransported, ?_, ?_⟩
  · intro s
    rw [hcontinued.2 s]
    have hphi :
        (((Real.goldenRatio ^ 2 : Real) : Complex) : Complex) ≠ 0 := by
      exact_mod_cast pow_ne_zero 2 Real.goldenRatio_ne_zero
    have ha : ((1 / Real.goldenRatio ^ 2 : Real) : Complex) =
        ((Real.goldenRatio ^ 2 : Real) : Complex)⁻¹ := by
      norm_cast
      simp only [one_div]
    have hlinear :
        s.1 - ((Real.goldenRatio ^ 2 : Real) : Complex)⁻¹ =
          (((Real.goldenRatio ^ 2 : Real) : Complex) * s.1 - 1) /
            ((Real.goldenRatio ^ 2 : Real) : Complex) := by
      change s.1 - ((Real.goldenRatio ^ 2 : Real) : Complex)⁻¹ =
        (((Real.goldenRatio ^ 2 : Real) : Complex) * s.1 - 1) *
          ((Real.goldenRatio ^ 2 : Real) : Complex)⁻¹
      calc
        s.1 - ((Real.goldenRatio ^ 2 : Real) : Complex)⁻¹ =
            1 * s.1 - ((Real.goldenRatio ^ 2 : Real) : Complex)⁻¹ := by ring
        _ = (((Real.goldenRatio ^ 2 : Real) : Complex) *
              ((Real.goldenRatio ^ 2 : Real) : Complex)⁻¹) * s.1 -
            ((Real.goldenRatio ^ 2 : Real) : Complex)⁻¹ := by
          rw [mul_inv_cancel₀ hphi]
        _ = ((((Real.goldenRatio ^ 2 : Real) : Complex) * s.1 - 1) *
            ((Real.goldenRatio ^ 2 : Real) : Complex)⁻¹) := by ring
    rw [ha, hlinear]
    ring
  · have hofReal : Tendsto
        (fun sigma : Real => (sigma : Complex))
        (𝓝[>] (1 / Real.goldenRatio ^ 2 : Real))
        (𝓝[≠] ((1 / Real.goldenRatio ^ 2 : Real) : Complex)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact (Complex.continuous_ofReal.tendsto
          (1 / Real.goldenRatio ^ 2 : Real)).mono_left inf_le_left
      · filter_upwards [eventually_mem_nhdsWithin] with sigma hsigma
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact_mod_cast hsigma.ne'
    have hrealKernel := htransported.comp hofReal
    have hrealScaled := hrealKernel.div_const
      ((Real.goldenRatio ^ 2 : Real) : Complex)
    apply hrealScaled.congr'
    filter_upwards [eventually_mem_nhdsWithin] with sigma hsigma
    have hsigmaDomain :
        1 / Real.goldenRatio ^ 3 < ((sigma : Complex)).re := by
      rw [Complex.ofReal_re]
      exact lt_trans hlt hsigma
    let s : {z : Complex // 1 / Real.goldenRatio ^ 3 < z.re} :=
      ⟨(sigma : Complex), hsigmaDomain⟩
    have hfactor :
        (∏' p : Nat.Primes, germLocalFactor (sigma : Complex) p) =
          riemannZeta
              (((Real.goldenRatio ^ 2 : Real) : Complex) * (sigma : Complex)) *
            ∏' p : Nat.Primes,
              (1 - (p : Complex) ^
                  (-(sigma : Complex) *
                    ((Real.goldenRatio ^ 2 : Real) : Complex))) *
                germLocalFactor (sigma : Complex) p := by
      calc
        (∏' p : Nat.Primes, germLocalFactor (sigma : Complex) p) =
            continuedGerm s := (hcontinued.1 s (by
              simpa [s] using hsigma)).symm
        _ = riemannZeta
              (((Real.goldenRatio ^ 2 : Real) : Complex) * (sigma : Complex)) *
            ∏' p : Nat.Primes,
              (1 - (p : Complex) ^
                  (-(sigma : Complex) *
                    ((Real.goldenRatio ^ 2 : Real) : Complex))) *
                germLocalFactor (sigma : Complex) p := by
          simpa [s] using hcontinued.2 s
    have haxis := hpositive sigma (lt_trans hlt hsigma)
    change
      0 < (∏' p : Nat.Primes,
        (1 - (p : Complex) ^
            (-(sigma : Complex) *
              ((Real.goldenRatio ^ 2 : Real) : Complex))) *
          germLocalFactor (sigma : Complex) p).re ∧
      (∏' p : Nat.Primes,
        (1 - (p : Complex) ^
            (-(sigma : Complex) *
              ((Real.goldenRatio ^ 2 : Real) : Complex))) *
          germLocalFactor (sigma : Complex) p).im = 0 at haxis
    have hG :
        (∏' p : Nat.Primes,
          (1 - (p : Complex) ^
              (-(sigma : Complex) *
                ((Real.goldenRatio ^ 2 : Real) : Complex))) *
            germLocalFactor (sigma : Complex) p) ≠ 0 := by
      intro hzero
      rw [hzero] at haxis
      simpa using haxis.1
    have hphi : ((Real.goldenRatio ^ 2 : Real) : Complex) ≠ 0 := by
      exact_mod_cast pow_ne_zero 2 Real.goldenRatio_ne_zero
    have hlinear :
        ((((Real.goldenRatio ^ 2 : Real) : Complex) * (sigma : Complex) - 1) /
            ((Real.goldenRatio ^ 2 : Real) : Complex)) =
          ((sigma - 1 / Real.goldenRatio ^ 2 : Real) : Complex) := by
      apply (div_eq_iff hphi).2
      rw [Complex.ofReal_sub, sub_mul]
      rw [mul_comm (sigma : Complex),
        mul_comm ((1 / Real.goldenRatio ^ 2 : Real) : Complex), hcritical]
    rw [hfactor]
    rw [← mul_assoc, mul_div_cancel_right₀ _ hG]
    calc
      (((((Real.goldenRatio ^ 2 : Real) : Complex) * (sigma : Complex) - 1) *
            riemannZeta
              (((Real.goldenRatio ^ 2 : Real) : Complex) * (sigma : Complex))) /
          ((Real.goldenRatio ^ 2 : Real) : Complex)) =
          ((((Real.goldenRatio ^ 2 : Real) : Complex) * (sigma : Complex) - 1) /
              ((Real.goldenRatio ^ 2 : Real) : Complex)) *
            riemannZeta
              (((Real.goldenRatio ^ 2 : Real) : Complex) * (sigma : Complex)) := by
        ring
      _ = ((sigma - 1 / Real.goldenRatio ^ 2 : Real) : Complex) *
            riemannZeta
              (((Real.goldenRatio ^ 2 : Real) : Complex) * (sigma : Complex)) := by
        rw [hlinear]
  · infer_instance

#print axioms golden_germ_zeta_boundary_reduction

end

end D5.S3.Analytic.EulerGerm.GoldenGermZetaBoundary
