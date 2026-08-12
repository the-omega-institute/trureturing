/- GID: D5/S3/QuantumBounds/CollisionEntropyUncertainty
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/CollisionEntropyUncertainty
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bound summed measurement entropy using collision conservation and finite Jensen. -/

/- Library-search audit trail (2026-08-12):
   * Pinned-mathlib queries covered collision entropy, entropy versus purity, finite uncertainty
     sums, Jensen with logarithms, convex negative logarithms, and arithmetic-mean log bounds.
   * `ConcaveOn.le_map_sum` is the exact finite weighted Jensen engine. The proof uses it first
     with the outcome probabilities as weights and then, through negation, with uniform weights
     over the measurement family.
   * No collision-entropy definition, Shannon-versus-collision inequality, or summed measurement
     uncertainty theorem matching this declaration was found in pinned mathlib.
   * Repository searches covered collision and uncertainty vocabulary, entropy-purity formulas,
     squared-probability sums, and rearranged versions of the conclusion. `Entropy.MaxEntropy`
     supplies the finite Shannon entropy definition; no equivalent bound was found under `D5/`.
-/

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import D5.S3.Entropy.MaxEntropy

namespace D5.S3.QuantumBounds.CollisionEntropyUncertainty

open D5.S3.Entropy.MaxEntropy

/-- A complete family of finite measurement laws whose collision probabilities sum to one plus
the state purity satisfies the corresponding summed Shannon-entropy uncertainty bound. -/
theorem collision_entropy_uncertainty {d : Nat} (hd : 0 < d)
    (p : Fin (d + 1) -> Fin d -> Real) (purity : Real)
    (hprob : forall b, (forall i, 0 <= p b i) /\ ∑ i, p b i = 1)
    (hcollision : ∑ b, ∑ i, (p b i) ^ 2 = 1 + purity) :
    (d + 1 : Real) * Real.log ((d + 1 : Real) / (1 + purity)) <=
      ∑ b, shannonEntropy (p b) := by
  classical
  let collision : Fin (d + 1) -> Real := fun b => ∑ i, (p b i) ^ 2
  have hcollision_pos (b : Fin (d + 1)) : 0 < collision b := by
    have hsome : ∃ i, 0 < p b i := by
      by_contra hnone
      simp only [not_exists, not_lt] at hnone
      have hsum_nonpos : ∑ i, p b i <= 0 :=
        Finset.sum_nonpos fun i _ => hnone i
      linarith [(hprob b).2]
    rcases hsome with ⟨i, hi⟩
    apply Finset.sum_pos'
    · intro j _
      exact sq_nonneg (p b j)
    · exact ⟨i, Finset.mem_univ i, sq_pos_of_pos hi⟩
  have hsingle (b : Fin (d + 1)) :
      -Real.log (collision b) <= shannonEntropy (p b) := by
    let positivePart : Fin d -> Real := fun i => if p b i = 0 then 1 else p b i
    have hpositivePart (i : Fin d) : 0 < positivePart i := by
      by_cases hi : p b i = 0
      · simp [positivePart, hi]
      · simp only [positivePart, hi, if_false]
        exact lt_of_le_of_ne ((hprob b).1 i) (Ne.symm hi)
    have haverage : ∑ i, p b i * positivePart i = collision b := by
      change (∑ i, p b i * positivePart i) = ∑ i, (p b i) ^ 2
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : p b i = 0
      · simp [positivePart, hi]
      · simp [positivePart, hi, pow_two]
    have hjensen := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
      (t := Finset.univ) (w := fun i => p b i) (p := positivePart)
      (fun i _ => (hprob b).1 i) (by simpa using (hprob b).2)
      (fun i _ => hpositivePart i)
    simp only [smul_eq_mul] at hjensen
    rw [haverage] at hjensen
    rw [shannonEntropy]
    calc
      -Real.log (collision b) <= -(∑ i, p b i * Real.log (positivePart i)) :=
        neg_le_neg hjensen
      _ = ∑ i, Real.negMulLog (p b i) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : p b i = 0
        · simp [positivePart, hi]
        · simp [positivePart, hi, Real.negMulLog]
  have hfamily_collision : ∑ b, collision b = 1 + purity := by
    simpa only [collision] using hcollision
  have htotal_pos : 0 < 1 + purity := by
    rw [← hfamily_collision]
    apply Finset.sum_pos'
    · intro b _
      exact (hcollision_pos b).le
    · exact ⟨0, Finset.mem_univ 0, hcollision_pos 0⟩
  have hcount_pos : (0 : Real) < d + 1 := by positivity
  have hcount_ne : (d + 1 : Real) ≠ 0 := ne_of_gt hcount_pos
  have hweight_sum : ∑ _ : Fin (d + 1), (d + 1 : Real)⁻¹ = 1 := by
    simp [hcount_ne]
  have hjensen := strictConcaveOn_log_Ioi.neg.convexOn.map_sum_le
    (t := Finset.univ) (w := fun _ : Fin (d + 1) => (d + 1 : Real)⁻¹)
    (p := collision) (fun _ _ => (inv_pos.mpr hcount_pos).le) hweight_sum
    (fun b _ => hcollision_pos b)
  simp only [smul_eq_mul] at hjensen
  have havg : ∑ b, (d + 1 : Real)⁻¹ * collision b =
      (1 + purity) / (d + 1 : Real) := by
    rw [← Finset.mul_sum, hfamily_collision]
    field_simp
  rw [havg] at hjensen
  have hscaled := mul_le_mul_of_nonneg_left hjensen hcount_pos.le
  calc
    (d + 1 : Real) * Real.log ((d + 1 : Real) / (1 + purity)) =
        (d + 1 : Real) * (-Real.log ((1 + purity) / (d + 1 : Real))) := by
      rw [Real.log_div hcount_ne (ne_of_gt htotal_pos),
        Real.log_div (ne_of_gt htotal_pos) hcount_ne]
      ring
    _ <= (d + 1 : Real) *
        (∑ b, (d + 1 : Real)⁻¹ * -Real.log (collision b)) := hscaled
    _ = ∑ b, -Real.log (collision b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      field_simp
    _ <= ∑ b, shannonEntropy (p b) :=
      Finset.sum_le_sum fun b _ => hsingle b

private def deterministicMeasurements : Fin 2 -> Fin 1 -> Real := fun _ _ => 1

/-- Checked evidence that the measurement-family domain is inhabited. -/
example : Fin 2 -> Fin 1 -> Real := deterministicMeasurements

/-- Checked evidence that the hypotheses admit a concrete deterministic family. -/
example :
    (forall b, (forall i, 0 <= deterministicMeasurements b i) /\
      ∑ i, deterministicMeasurements b i = 1) /\
    (∑ b, ∑ i, (deterministicMeasurements b i) ^ 2) = 1 + (1 : Real) := by
  constructor
  · intro b
    constructor
    · intro i
      norm_num [deterministicMeasurements]
    · simp [deterministicMeasurements]
  · norm_num [deterministicMeasurements, Fin.sum_univ_succ]

/-- Checked concrete instance of the uncertainty conclusion. -/
example :
    (1 + 1 : Real) * Real.log ((1 + 1 : Real) / (1 + 1)) <=
      ∑ b, shannonEntropy (deterministicMeasurements b) := by
  simpa only [Nat.cast_one] using
    collision_entropy_uncertainty (d := 1) (by omega) deterministicMeasurements 1
      (by
        intro b
        constructor
        · intro i
          norm_num [deterministicMeasurements]
        · simp [deterministicMeasurements])
      (by norm_num [deterministicMeasurements, Fin.sum_univ_succ])

end D5.S3.QuantumBounds.CollisionEntropyUncertainty
