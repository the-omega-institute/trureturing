/- GID: D5/S3/Entropy/NamingWindow/GreenClassWindowEntropyEquality
   generality: G
   mirror-B: D5/B/S3/Entropy/NamingWindow/GreenClassWindowEntropyEquality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Characterize equality in the naming-window entropy bound by uniform coordinates. -/

import D5.S3.Entropy.NamingWindow.GreenClassWindowEntropy
import D5.S3.Entropy.EntropyEquality

namespace D5.S3.Entropy.NamingWindow.GreenClassWindowEntropyEquality

open MeasureTheory Measure Finset
open D5.S3.Entropy.EntropyEquality
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.NamingWindow.GreenClassWindowEntropy
open D5.S0.Asymptotics.MetricGeometry.GreenClassHausdorffDimension

noncomputable section

/-- Equality in the naming-window entropy bound holds exactly for uniform coordinates. -/
theorem shannonEntropy_windowLaw_eq_namingDim_iff_uniform {O : Type*} [Fintype O]
    [Nonempty O] [MeasurableSpace O] [MeasurableSingletonClass O]
    (μ : ℕ → Measure O) [∀ i, IsProbabilityMeasure (μ i)] (S : Finset ℕ) :
    shannonEntropy (windowLaw (fun i : (S : Finset ℕ) => coordLaw μ i.1)) =
        S.card * (namingDim O * Real.log 2) ↔
      ∀ i : (S : Finset ℕ), coordLaw μ i.1 = fun _ => (Fintype.card O : ℝ)⁻¹ := by
  classical
  have hcoord (i : ℕ) : ∑ a, coordLaw μ i a = 1 := by
    simp only [coordLaw]
    rw [show (∑ a, (μ i {a}).toReal) = (∑ a, μ i {a}).toReal from
      (ENNReal.toReal_sum fun a _ => measure_ne_top _ _).symm]
    rw [MeasureTheory.sum_measure_singleton]
    simp
  have hlog : Real.log (Fintype.card O) = namingDim O * Real.log 2 := by
    rw [namingDim, Real.logb, div_mul_cancel₀]
    exact Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  rw [shannonEntropy_windowLaw (fun i : (S : Finset ℕ) => coordLaw μ i.1)
    (fun i => hcoord i.1), ← hlog]
  have hle (i : (S : Finset ℕ)) :
      shannonEntropy (coordLaw μ i.1) ≤ Real.log (Fintype.card O) :=
    entropy_le_log_card _ ⟨fun a => ENNReal.toReal_nonneg, hcoord i.1⟩
  constructor
  · intro hsum
    have hsum' :
        (∑ i : (S : Finset ℕ), shannonEntropy (coordLaw μ i.1)) =
          ∑ _i : (S : Finset ℕ), Real.log (Fintype.card O) := by
      simpa [Finset.sum_const, Fintype.card_coe, nsmul_eq_mul] using hsum
    have heq : ∀ i ∈ (Finset.univ : Finset (S : Finset ℕ)),
        shannonEntropy (coordLaw μ i.1) = Real.log (Fintype.card O) :=
      (Finset.sum_eq_sum_iff_of_le fun i _ => hle i).mp hsum'
    intro i
    exact (entropy_eq_log_card_iff_uniform (coordLaw μ i.1)
      ⟨fun a => ENNReal.toReal_nonneg, hcoord i.1⟩).mp (heq i (Finset.mem_univ i))
  · intro huniform
    calc
      (∑ i : (S : Finset ℕ), shannonEntropy (coordLaw μ i.1)) =
          ∑ _i : (S : Finset ℕ), Real.log (Fintype.card O) :=
        Finset.sum_congr rfl fun i _ =>
          (entropy_eq_log_card_iff_uniform (coordLaw μ i.1)
            ⟨fun a => ENNReal.toReal_nonneg, hcoord i.1⟩).mpr (huniform i)
      _ = S.card * Real.log (Fintype.card O) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]

end

end D5.S3.Entropy.NamingWindow.GreenClassWindowEntropyEquality
