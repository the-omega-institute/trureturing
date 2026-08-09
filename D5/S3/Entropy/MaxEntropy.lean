/- GID: D5/S3/Entropy/MaxEntropy
   generality: G
   mirror-B: D5/B/S3/Entropy/MaxEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Define finite Shannon entropy in nats and bound it by the log-cardinality. -/

/- Library-search audit trail (2026-08-09):
   * Local pinned-mathlib grep terms: `shannonEntropy`, `shannon_entropy`,
     `finiteEntropy`, `entropy_le_log_card`, `entropy.*Fintype`,
     `Fintype.*entropy`, `entropy.*Real.log.*card`, `negMulLog`, and entropy filenames.
   * The only entropy families found were dynamical `TopologicalEntropy` and the scalar
     `Real.binEntropy`/`Real.qaryEntropy`; no finite Shannon sum or maximum-entropy bound was found.
   * `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog` owns the scalar Shannon atom and its API,
     so `shannonEntropy` below defines only the genuinely absent finite sum.
   * Repository-wide `D5/` grep terms: `shannon`, `entropy`, `negMulLog`,
     `maximum.*entropy`, `max.*entropy`, `entropy.*Fintype`, `Real.log.*card`,
     `card.*Real.log`, sums containing `Real.log`, and `klDivergence` (including rearranged forms).
   * `Quantum.CloningMachine.binaryEntropyBits` and
     `Constants.RecordEntropy.haar_record_entropy_bits` are scalar/closed-form bit quantities,
     not this finite functional or inequality; no repository duplicate was found.
   * Units here are nats: `Real.log` is the natural logarithm, matching `klDivergence`.
-/

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import D5.S3.Divergence.GrandmotherTheorem

namespace D5.S3.Entropy.MaxEntropy

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Divergence.GrandmotherTheorem

/-- Finite Shannon entropy in nats, using mathlib's endpoint convention for `negMulLog`. -/
noncomputable def shannonEntropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

/-- Shannon entropy on a nonempty finite type is at most the entropy of the uniform law. -/
theorem entropy_le_log_card {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ι → ℝ) (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1) :
    shannonEntropy p ≤ Real.log (Fintype.card ι) := by
  classical
  let u : ι → ℝ := fun _ => (Fintype.card ι : ℝ)⁻¹
  have hcard_pos : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  have hcard_ne : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hu : (∀ i, 0 ≤ u i) ∧ ∑ i, u i = 1 := by
    constructor
    · intro i
      exact (inv_pos.mpr hcard_pos).le
    · simp [u, hcard_ne]
  have hac : ∀ i, u i = 0 → p i = 0 := by
    intro i hui
    exact ((inv_ne_zero hcard_ne) hui).elim
  have hterm (i : ι) :
      p i * Real.log (p i / u i) =
        -Real.negMulLog (p i) + Real.log (Fintype.card ι) * p i := by
    by_cases hpi : p i = 0
    · simp [hpi]
    · rw [show p i / u i = p i * (Fintype.card ι : ℝ) by simp [u]]
      rw [Real.log_mul hpi hcard_ne]
      simp only [Real.negMulLog]
      ring
  have hidentity :
      klDivergence p u = Real.log (Fintype.card ι) - shannonEntropy p := by
    rw [klDivergence, shannonEntropy]
    calc
      (∑ i, p i * Real.log (p i / u i)) =
          ∑ i, (-Real.negMulLog (p i) + Real.log (Fintype.card ι) * p i) := by
            exact Finset.sum_congr rfl fun i _ => hterm i
      _ = -(∑ i, Real.negMulLog (p i)) +
          Real.log (Fintype.card ι) * ∑ i, p i := by
            rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.mul_sum]
      _ = Real.log (Fintype.card ι) - ∑ i, Real.negMulLog (p i) := by
            rw [hp.2]
            ring
  have hkl : 0 ≤ klDivergence p u :=
    kl_divergence_nonneg p u hp hu hac
  rw [hidentity] at hkl
  exact sub_nonneg.mp hkl

end D5.S3.Entropy.MaxEntropy
