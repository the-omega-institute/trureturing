/- GID: D5/S3/DivergenceSupport/ZeroSupportDPI
   generality: G
   mirror-B: D5/B/S3/DivergenceSupport/ZeroSupportDPI
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Extend the finite classical data-processing identity to general support. -/

/- Library-search audit trail (2026-08-10):
   * Local pinned-mathlib grep/read terms: `klDiv_compProd_eq_add`, `klDiv_compProd_left`,
     `rnDeriv_compProd_mul_log_eq_mul_add`, `Real.log_mul`, `Real.log_zero`,
     `Finset.sum_eq_zero_iff_of_nonneg`, `Fintype.*klDiv`, and `PMF.*klDiv`.
   * `Mathlib.InformationTheory.KullbackLeibler.ChainRule` proves the measure-valued chain rule
     `InformationTheory.klDiv_compProd_eq_add`. Its divergence is `ENNReal`-valued, and its
     conditional term remains a composition-product divergence; no pinned theorem was found that
     identifies it with the repository's real finite sum and displayed posterior sum.
   * The upstream helper `rnDeriv_compProd_mul_log_eq_mul_add` handles zero factors by cases before
     invoking `Real.log_mul`. The finite proof below follows that support discipline directly.
   * Pinned `Real.log_zero` states `Real.log 0 = 0`, while `Real.log_mul` requires both factors
     nonzero. `Finset.sum_eq_zero_iff_of_nonneg` supplies the finite-support step that turns a zero
     output mass into pointwise zero joint masses.
-/

import D5.S3.Divergence.ClassicalDPI

namespace D5.S3.DivergenceSupport.ZeroSupportDPI

open D5.S3.Divergence.ClassicalDPI

/-- Discrete absolute continuity is preserved by a nonnegative finite channel. -/
theorem channel_output_absolute_continuity {X Y : Type*}
    [Fintype X]
    (p q : X -> Real) (W : X -> Y -> Real)
    (hq : ∀ x, 0 <= q x)
    (hac : ∀ x, q x = 0 -> p x = 0)
    (hW : ∀ x y, 0 <= W x y)
    (y : Y) (hy : channelOutput W q y = 0) :
    channelOutput W p y = 0 := by
  rw [channelOutput] at hy ⊢
  apply Finset.sum_eq_zero
  intro x _
  have hqxW : q x * W x y = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun z _ => mul_nonneg (hq z) (hW z y)).mp hy x
      (Finset.mem_univ x)
  rcases mul_eq_zero.mp hqxW with hqx | hWxy
  · simp [hac x hqx]
  · simp [hWxy]

/-- The explicit zero-output convention: when the output mass under `p` vanishes, its weighted
posterior-divergence contribution is zero. This statement applies to the totalized repository
posterior, whose denominator may be zero. -/
theorem zero_output_weighted_posterior_kl {X Y : Type*}
    [Fintype X]
    (p q : X -> Real) (W : X -> Y -> Real) (y : Y)
    (hy : channelOutput W p y = 0) :
    channelOutput W p y *
        klDivergence (posterior W p y) (posterior W q y) = 0 := by
  rw [hy, zero_mul]

/-- The finite classical data-processing chain identity for nonnegative normalized masses with
discrete absolute continuity and a nonnegative row-stochastic channel. Zero-probability outputs
contribute zero through `zero_output_weighted_posterior_kl`. -/
theorem classical_dpi_identity_zero_support {X Y : Type*}
    [Fintype X] [Fintype Y]
    (p q : X -> Real) (W : X -> Y -> Real)
    (hp : (∀ x, 0 <= p x) ∧ ∑ x, p x = 1)
    (hq : (∀ x, 0 <= q x) ∧ ∑ x, q x = 1)
    (hac : ∀ x, q x = 0 -> p x = 0)
    (hW : (∀ x y, 0 <= W x y) ∧ ∀ x, ∑ y, W x y = 1) :
    klDivergence p q =
      klDivergence (channelOutput W p) (channelOutput W q) +
        ∑ y, channelOutput W p y *
          klDivergence (posterior W p y) (posterior W q y) := by
  classical
  have hOutputPNonneg (y : Y) : 0 <= channelOutput W p y := by
    rw [channelOutput]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (hp.1 x) (hW.1 x y)
  have hOutputQNonneg (y : Y) : 0 <= channelOutput W q y := by
    rw [channelOutput]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (hq.1 x) (hW.1 x y)
  have hOutputAC (y : Y) (hy : channelOutput W q y = 0) :
      channelOutput W p y = 0 :=
    channel_output_absolute_continuity p q W hq.1 hac hW.1 y hy
  have hJointAC (x : X) (y : Y) (hxy : q x * W x y = 0) :
      p x * W x y = 0 := by
    rcases mul_eq_zero.mp hxy with hqx | hWxy
    · simp [hac x hqx]
    · simp [hWxy]
  have hJointPZeroOfOutputZero (x : X) (y : Y)
      (hy : channelOutput W p y = 0) : p x * W x y = 0 := by
    have hy' : (∑ z, p z * W z y) = 0 := by
      simpa [channelOutput] using hy
    exact (Finset.sum_eq_zero_iff_of_nonneg fun z _ =>
      mul_nonneg (hp.1 z) (hW.1 z y)).mp hy' x (Finset.mem_univ x)
  have hInputTerm (x : X) (y : Y) :
      p x * W x y * Real.log (p x * W x y / (q x * W x y)) =
        p x * W x y * Real.log (p x / q x) := by
    by_cases hpx : p x = 0
    · simp [hpx]
    by_cases hWxy : W x y = 0
    · simp [hWxy]
    have hqx : q x ≠ 0 := fun h => hpx (hac x h)
    have hRatio : p x * W x y / (q x * W x y) = p x / q x := by
      field_simp [hqx, hWxy]
    rw [hRatio]
  have hOutputTerm (x : X) (y : Y) :
      p x * W x y * Real.log (p x * W x y / (q x * W x y)) =
        p x * W x y *
            Real.log (channelOutput W p y / channelOutput W q y) +
          channelOutput W p y *
            (posterior W p y x *
              Real.log (posterior W p y x / posterior W q y x)) := by
    by_cases hOutputPZero : channelOutput W p y = 0
    · have hJointPZero := hJointPZeroOfOutputZero x y hOutputPZero
      simp [hOutputPZero, hJointPZero]
    have hOutputPPos : 0 < channelOutput W p y :=
      lt_of_le_of_ne (hOutputPNonneg y) (Ne.symm hOutputPZero)
    have hOutputQNe : channelOutput W q y ≠ 0 := by
      intro hOutputQZero
      exact hOutputPZero (hOutputAC y hOutputQZero)
    have hOutputQPos : 0 < channelOutput W q y :=
      lt_of_le_of_ne (hOutputQNonneg y) (Ne.symm hOutputQNe)
    by_cases hJointPZero : p x * W x y = 0
    · have hPosteriorPZero : posterior W p y x = 0 := by
        simp [posterior, hJointPZero]
      simp [hJointPZero, hPosteriorPZero]
    have hJointQNe : q x * W x y ≠ 0 := fun h =>
      hJointPZero (hJointAC x y h)
    have hJointPPos : 0 < p x * W x y :=
      lt_of_le_of_ne (mul_nonneg (hp.1 x) (hW.1 x y)) (Ne.symm hJointPZero)
    have hJointQPos : 0 < q x * W x y :=
      lt_of_le_of_ne (mul_nonneg (hq.1 x) (hW.1 x y)) (Ne.symm hJointQNe)
    have hPosteriorPPos : 0 < posterior W p y x :=
      div_pos hJointPPos hOutputPPos
    have hPosteriorQPos : 0 < posterior W q y x :=
      div_pos hJointQPos hOutputQPos
    have hOutputPosteriorP :
        channelOutput W p y * posterior W p y x = p x * W x y := by
      simp only [posterior]
      field_simp [hOutputPZero]
    have hChainRatio :
        p x * W x y / (q x * W x y) =
          channelOutput W p y / channelOutput W q y *
            (posterior W p y x / posterior W q y x) := by
      simp only [posterior]
      field_simp [hJointQNe, hOutputPZero, hOutputQNe]
    calc
      p x * W x y * Real.log (p x * W x y / (q x * W x y)) =
          p x * W x y *
            (Real.log (channelOutput W p y / channelOutput W q y) +
              Real.log (posterior W p y x / posterior W q y x)) := by
            rw [hChainRatio, Real.log_mul
              (ne_of_gt (div_pos hOutputPPos hOutputQPos))
              (ne_of_gt (div_pos hPosteriorPPos hPosteriorQPos))]
      _ = p x * W x y *
              Real.log (channelOutput W p y / channelOutput W q y) +
            p x * W x y *
              Real.log (posterior W p y x / posterior W q y x) := by ring
      _ = p x * W x y *
              Real.log (channelOutput W p y / channelOutput W q y) +
            channelOutput W p y *
              (posterior W p y x *
                Real.log (posterior W p y x / posterior W q y x)) := by
            rw [← mul_assoc, hOutputPosteriorP]
  have hJointByInput :
      (∑ y, ∑ x, p x * W x y *
          Real.log (p x * W x y / (q x * W x y))) =
        klDivergence p q := by
    rw [Finset.sum_comm, klDivergence]
    apply Finset.sum_congr rfl
    intro x _
    calc
      (∑ y, p x * W x y *
          Real.log (p x * W x y / (q x * W x y))) =
          ∑ y, p x * W x y * Real.log (p x / q x) := by
            apply Finset.sum_congr rfl
            intro y _
            exact hInputTerm x y
      _ = p x * Real.log (p x / q x) * (∑ y, W x y) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y _
            ring
      _ = p x * Real.log (p x / q x) := by rw [hW.2 x, mul_one]
  have hJointByOutput :
      (∑ y, ∑ x, p x * W x y *
          Real.log (p x * W x y / (q x * W x y))) =
        klDivergence (channelOutput W p) (channelOutput W q) +
          ∑ y, channelOutput W p y *
            klDivergence (posterior W p y) (posterior W q y) := by
    rw [klDivergence]
    calc
      (∑ y, ∑ x, p x * W x y *
          Real.log (p x * W x y / (q x * W x y))) =
          ∑ y, (channelOutput W p y *
              Real.log (channelOutput W p y / channelOutput W q y) +
            channelOutput W p y *
              (∑ x, posterior W p y x *
                Real.log (posterior W p y x / posterior W q y x))) := by
            apply Finset.sum_congr rfl
            intro y _
            calc
              (∑ x, p x * W x y *
                  Real.log (p x * W x y / (q x * W x y))) =
                  ∑ x, (p x * W x y *
                      Real.log (channelOutput W p y / channelOutput W q y) +
                    channelOutput W p y *
                      (posterior W p y x *
                        Real.log (posterior W p y x / posterior W q y x))) := by
                        apply Finset.sum_congr rfl
                        intro x _
                        exact hOutputTerm x y
              _ = (∑ x, p x * W x y *
                    Real.log (channelOutput W p y / channelOutput W q y)) +
                  ∑ x, channelOutput W p y *
                    (posterior W p y x *
                      Real.log (posterior W p y x / posterior W q y x)) := by
                      rw [Finset.sum_add_distrib]
              _ = channelOutput W p y *
                    Real.log (channelOutput W p y / channelOutput W q y) +
                  channelOutput W p y *
                    (∑ x, posterior W p y x *
                      Real.log (posterior W p y x / posterior W q y x)) := by
                      congr 1
                      · rw [channelOutput, Finset.sum_mul]
                      · rw [Finset.mul_sum]
      _ = (∑ y, channelOutput W p y *
              Real.log (channelOutput W p y / channelOutput W q y)) +
            ∑ y, channelOutput W p y *
              (∑ x, posterior W p y x *
                Real.log (posterior W p y x / posterior W q y x)) := by
              rw [Finset.sum_add_distrib]
      _ = klDivergence (channelOutput W p) (channelOutput W q) +
            ∑ y, channelOutput W p y *
              klDivergence (posterior W p y) (posterior W q y) := by
              rfl
  exact hJointByInput.symm.trans hJointByOutput

end D5.S3.DivergenceSupport.ZeroSupportDPI
