/- GID: D5/S3/QuantumChannels/FibonacciBathRecordCapacity
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/FibonacciBathRecordCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp Gibbs-relative entropy memory dimension for the six-level bath. -/

import D5.S3.Quantum.Recovery.DiagonalRecordCapacity
import D5.S3.QuantumChannels.FibonacciBathObservation

/-! Exact lossless quantum memory for the Gibbs reference and the terminal bath marginal. -/

noncomputable section

namespace D5.S3.QuantumChannels.FibonacciBathRecordCapacity

open scoped BigOperators
open Matrix
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Recovery.DiagonalRecordCapacity
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceLeft)
open GibbsBathBandwidth (diagonalReal)
open FibonacciBathObservation (outputWeight terminalJoint terminalJoint_eq_diagonal)
open ThermalDegeneracyWitness (bathLevel bathState)
open private rationalGibbsWeight partitionWeight_eq gibbsWeight_eq_rat
  from D5.S3.QuantumChannels.ThermalOperationDegeneracyRefutation

private abbrev Bath := Fin 20

private def outgoingWeight (b : Bath) : ℚ := ∑ s : Fin 3, outputWeight (s, b)

private def ratioClass (b : Bath) : Fin 4 :=
  if bathLevel b = 0 then 0 else if bathLevel b = 4 then 2
  else if bathLevel b = 5 then 3 else 1

private def ratio (j : Fin 4) : ℚ := ![0, 4 / 3, 5 / 3, 7 / 3] j

set_option maxRecDepth 4096 in
private theorem reference_weights :
    (∀ b : Bath, 0 < rationalGibbsWeight b) ∧ ∑ b : Bath, rationalGibbsWeight b = 1 := by
  simp only [rationalGibbsWeight, partitionWeight_eq]
  decide +kernel

set_option maxRecDepth 4096 in
private theorem outgoing_weights :
    (∀ b : Bath, 0 ≤ outgoingWeight b) ∧ ∑ b : Bath, outgoingWeight b = 1 := by
  decide +kernel

/-- The singleton comparison experiment on the actual six-level bath basis. -/
def experiment : DiagonalExperiment Bath Unit where
  reference b := rationalGibbsWeight b
  comparison _ b := outgoingWeight b
  reference_nonneg b := (Rat.cast_pos.mpr (reference_weights.1 b)).le
  reference_sum := by exact_mod_cast reference_weights.2
  comparison_nonneg _ b := Rat.cast_nonneg.mpr (outgoing_weights.1 b)
  comparison_sum _ := by exact_mod_cast outgoing_weights.2
  comparison_zero _ b h := (ne_of_gt (Rat.cast_pos.mpr (reference_weights.1 b)) h).elim

private theorem reference_matrix :
    CStarMatrix.ofMatrix.symm experiment.referenceState.1 = bathState := by
  change diagonal (fun b => ((rationalGibbsWeight b : ℝ) : ℂ)) = bathState
  simp only [bathState, diagonalReal, gibbsWeight_eq_rat]

private theorem outgoing_matrix :
    CStarMatrix.ofMatrix.symm (experiment.comparisonState ()).1 =
      partialTraceLeft terminalJoint := by
  rw [terminalJoint_eq_diagonal]
  change diagonal (fun b => ((outgoingWeight b : ℝ) : ℂ)) = _
  ext b c
  by_cases h : b = c
  · subst c
    simp [partialTraceLeft, outgoingWeight, Complex.ofReal_ratCast, Rat.cast_sum]
  · have hpair (s : Fin 3) : (s, b) ≠ (s, c) := fun hEq => h (congrArg Prod.snd hEq)
    simp [partialTraceLeft, diagonal_apply_ne _ h, diagonal_apply_ne _ (hpair _)]

set_option maxRecDepth 4096 in
private theorem ratios_eq : ∀ b : Bath,
    outgoingWeight b / rationalGibbsWeight b = ratio (ratioClass b) := by
  simp only [rationalGibbsWeight, partitionWeight_eq]
  decide +kernel

private theorem ratio_injective : Function.Injective ratio := by
  change ∀ i j : Fin 4, ratio i = ratio j → i = j
  decide +kernel

private theorem ratioClass_surjective : Function.Surjective ratioClass := by
  have h : ∀ j : Fin 4, ratioClass ((![(0 : Bath), 1, 7, 12] : Fin 4 → Bath) j) = j := by
    decide +kernel
  exact fun j => ⟨_, h j⟩

private theorem likelihood_eq (b : Bath) (i : Unit) :
    experiment.likelihood b i = (ratio (ratioClass b) : ℝ) := by
  change (outgoingWeight b : ℝ) / (rationalGibbsWeight b : ℝ) = _
  exact_mod_cast ratios_eq b

private theorem classes_card : experiment.likelihoodClasses.card = 4 := by
  apply experiment.likelihoodClasses_card_of_labels (label := ratioClass)
  constructor
  · intro j
    obtain ⟨b, hb⟩ := ratioClass_surjective j
    exact ⟨b, Rat.cast_pos.mpr (reference_weights.1 b), hb⟩
  · intro b c _ _
    constructor
    · intro h
      funext i
      rw [likelihood_eq, likelihood_eq, h]
    · intro h
      apply ratio_injective
      have he := congrFun h ()
      rw [likelihood_eq, likelihood_eq] at he
      exact_mod_cast he

open Classical in
/-- The ratios are indexed in increasing order of their bath levels, with
all three interior levels sharing the second ratio. -/
theorem sixLevel_likelihood_ratios :
    experiment.likelihoodClasses = Finset.image (fun j : Fin 4 =>
        fun _ : Unit => ((![0, 4 / 3, 5 / 3, 7 / 3] : Fin 4 → ℝ) j)) Finset.univ := by
  classical
  have hratio (j : Fin 4) : (ratio j : ℝ) = (![0, 4 / 3, 5 / 3, 7 / 3] : Fin 4 → ℝ) j := by
    fin_cases j <;> norm_num [ratio]
  have hvector (b : Bath) : experiment.likelihood b =
      (fun _ : Unit => (![0, 4 / 3, 5 / 3, 7 / 3] : Fin 4 → ℝ) (ratioClass b)) := by
    funext i
    rw [likelihood_eq, hratio]
  ext v
  simp only [DiagonalExperiment.likelihoodClasses, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨b, _, hb⟩
    exact ⟨ratioClass b, (hvector b).symm.trans hb⟩
  · rintro ⟨j, hj⟩
    obtain ⟨b, hb⟩ := ratioClass_surjective j
    exact ⟨b, Rat.cast_pos.mpr (reference_weights.1 b), (hvector b).trans (hb ▸ hj)⟩

/-- For the actual outgoing bath and its input Gibbs reference, every CPTP
encoder preserving relative entropy needs at least four memory dimensions,
and a four-dimensional CPTP encoder attains equality. -/
theorem sixLevel_sharp_gibbs_entropy_dimension :
    ∃ outgoing gibbs : DensityState Bath,
      CStarMatrix.ofMatrix.symm outgoing.1 = partialTraceLeft terminalJoint ∧
      CStarMatrix.ofMatrix.symm gibbs.1 = bathState ∧
      (∀ {d : ℕ} (encoder : QuantumChannel Bath (Fin d)),
        extendedQuantumRelativeEntropy outgoing gibbs =
          extendedQuantumRelativeEntropy (encoder.mapState outgoing) (encoder.mapState gibbs) →
        4 ≤ d) ∧
      ∃ encoder : QuantumChannel Bath (Fin 4),
        extendedQuantumRelativeEntropy outgoing gibbs =
          extendedQuantumRelativeEntropy (encoder.mapState outgoing) (encoder.mapState gibbs) := by
  refine ⟨experiment.comparisonState (), experiment.referenceState, outgoing_matrix,
    reference_matrix, ?_⟩
  have h := experiment.sharp_entropy_dimension
  rw [classes_card] at h
  refine ⟨fun encoder hEq => h.1 encoder (fun i => ?_), ?_⟩
  · cases i
    exact hEq
  · obtain ⟨encoder, hEq⟩ := h.2
    exact ⟨encoder, hEq ()⟩

#print axioms sixLevel_likelihood_ratios
#print axioms sixLevel_sharp_gibbs_entropy_dimension

end D5.S3.QuantumChannels.FibonacciBathRecordCapacity
