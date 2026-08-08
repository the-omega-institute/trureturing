/- GID: D5/S3/Divergence/ClassicalDPI
   generality: G
   mirror-B: D5/B/S3/Divergence/ClassicalDPI
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove the finite classical data-processing identity by two joint KL decompositions. -/

/- Library-search audit trail (2026-08-08):
   * Local mathlib grep terms: `klDiv`, `Kullback`, `relativeEntropy`,
     `InformationTheory`, `klDiv.*sum`, `PMF.*klDiv`, and `llr.*sum`.
   * `Mathlib.InformationTheory.KullbackLeibler.ChainRule` provides the measure-valued chain
     rule `InformationTheory.klDiv_compProd_eq_add` and the common-kernel specialization
     `InformationTheory.klDiv_compProd_left`.
   * The upstream divergence takes values in `ℝ≥0∞` and is stated for measures and Markov
     kernels. No pinned bridge theorem was found that identifies it with the requested real-valued
     finite sum, or that evaluates its conditional term as the displayed posterior sum.
   * This file therefore proves the finite sum identity directly. The proof follows the same
     upstream chain-rule factorization, expanding the common joint distribution first by the input
     coordinate and then by the output coordinate.
-/

import Mathlib

namespace D5.S3.Divergence.ClassicalDPI

/-- Real-valued Kullback-Leibler divergence for two mass functions on a finite type. The theorem
below assumes strict positivity, so every logarithm is evaluated on a positive ratio. -/
noncomputable def klDivergence {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) : ℝ :=
  ∑ i, a i * Real.log (a i / b i)

/-- The output mass function obtained by applying a finite channel. -/
noncomputable def channelOutput {X Y : Type*} [Fintype X]
    (W : X → Y → ℝ) (p : X → ℝ) (y : Y) : ℝ :=
  ∑ x, p x * W x y

/-- The posterior mass function at an output letter. -/
noncomputable def posterior {X Y : Type*} [Fintype X]
    (W : X → Y → ℝ) (p : X → ℝ) (y : Y) (x : X) : ℝ :=
  p x * W x y / channelOutput W p y

/-- The classical data-processing identity for strictly positive finite input distributions and
channels. It is obtained by decomposing the KL divergence of the common-channel joint
distributions first along the input coordinate and then along the output coordinate. -/
theorem classical_dpi_identity {X Y : Type*}
    [Fintype X] [Nonempty X] [Fintype Y]
    (p q : X → ℝ) (W : X → Y → ℝ)
    (hp : (∀ x, 0 < p x) ∧ ∑ x, p x = 1)
    (hq : (∀ x, 0 < q x) ∧ ∑ x, q x = 1)
    (hW : (∀ x y, 0 < W x y) ∧ ∀ x, ∑ y, W x y = 1) :
    klDivergence p q =
      klDivergence (channelOutput W p) (channelOutput W q) +
        ∑ y, channelOutput W p y *
          klDivergence (posterior W p y) (posterior W q y) := by
  classical
  have hOutputPPos (y : Y) : 0 < channelOutput W p y := by
    rw [channelOutput]
    refine Finset.sum_pos' (fun x _ => (mul_pos (hp.1 x) (hW.1 x y)).le) ?_
    let x : X := Classical.choice inferInstance
    exact ⟨x, Finset.mem_univ x, mul_pos (hp.1 x) (hW.1 x y)⟩
  have hOutputQPos (y : Y) : 0 < channelOutput W q y := by
    rw [channelOutput]
    refine Finset.sum_pos' (fun x _ => (mul_pos (hq.1 x) (hW.1 x y)).le) ?_
    let x : X := Classical.choice inferInstance
    exact ⟨x, Finset.mem_univ x, mul_pos (hq.1 x) (hW.1 x y)⟩
  have hJointRatio (x : X) (y : Y) :
      p x * W x y / (q x * W x y) = p x / q x := by
    field_simp [ne_of_gt (hq.1 x), ne_of_gt (hW.1 x y)]
  have hPosteriorPPos (x : X) (y : Y) : 0 < posterior W p y x := by
    exact div_pos (mul_pos (hp.1 x) (hW.1 x y)) (hOutputPPos y)
  have hPosteriorQPos (x : X) (y : Y) : 0 < posterior W q y x := by
    exact div_pos (mul_pos (hq.1 x) (hW.1 x y)) (hOutputQPos y)
  have hChainRatio (x : X) (y : Y) :
      p x * W x y / (q x * W x y) =
        channelOutput W p y / channelOutput W q y *
          (posterior W p y x / posterior W q y x) := by
    rw [hJointRatio]
    simp only [posterior]
    field_simp [ne_of_gt (hq.1 x), ne_of_gt (hW.1 x y),
      ne_of_gt (hOutputPPos y), ne_of_gt (hOutputQPos y)]
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
            rw [hJointRatio]
      _ = p x * Real.log (p x / q x) * ∑ y, W x y := by
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
              ∑ x, posterior W p y x *
                Real.log (posterior W p y x / posterior W q y x)) := by
            apply Finset.sum_congr rfl
            intro y _
            calc
              (∑ x, p x * W x y *
                  Real.log (p x * W x y / (q x * W x y))) =
                  ∑ x, p x * W x y *
                    (Real.log (channelOutput W p y / channelOutput W q y) +
                      Real.log (posterior W p y x / posterior W q y x)) := by
                        apply Finset.sum_congr rfl
                        intro x _
                        rw [hChainRatio]
                        rw [Real.log_mul
                          (ne_of_gt (div_pos (hOutputPPos y) (hOutputQPos y)))
                          (ne_of_gt (div_pos (hPosteriorPPos x y)
                            (hPosteriorQPos x y)))]
              _ = (∑ x, p x * W x y *
                    Real.log (channelOutput W p y / channelOutput W q y)) +
                  ∑ x, p x * W x y *
                    Real.log (posterior W p y x / posterior W q y x) := by
                      rw [← Finset.sum_add_distrib]
                      apply Finset.sum_congr rfl
                      intro x _
                      ring
              _ = channelOutput W p y *
                    Real.log (channelOutput W p y / channelOutput W q y) +
                  channelOutput W p y *
                    ∑ x, posterior W p y x *
                      Real.log (posterior W p y x / posterior W q y x) := by
                      congr 1
                      · rw [channelOutput, Finset.sum_mul]
                      · rw [Finset.mul_sum]
                        apply Finset.sum_congr rfl
                        intro x _
                        simp only [posterior]
                        field_simp [ne_of_gt (hOutputPPos y)]
      _ = (∑ y, channelOutput W p y *
              Real.log (channelOutput W p y / channelOutput W q y)) +
            ∑ y, channelOutput W p y *
              ∑ x, posterior W p y x *
                Real.log (posterior W p y x / posterior W q y x) := by
              rw [Finset.sum_add_distrib]
      _ = klDivergence (channelOutput W p) (channelOutput W q) +
            ∑ y, channelOutput W p y *
              klDivergence (posterior W p y) (posterior W q y) := by
              rfl
  exact hJointByInput.symm.trans hJointByOutput

end D5.S3.Divergence.ClassicalDPI
