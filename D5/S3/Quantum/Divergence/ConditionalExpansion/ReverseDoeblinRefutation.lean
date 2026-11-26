/- GID: D5/S3/Quantum/Divergence/ConditionalExpansion/ReverseDoeblinRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Divergence/ConditionalExpansion/ReverseDoeblinRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Divergence/ConditionalExpansion/ReverseDoeblinRefutation.claim; result=D5/S3/Quantum/Divergence/ConditionalExpansion/ReverseDoeblinRefutation.result; claim=D5/S3/Quantum/Divergence/ConditionalExpansion/ReverseDoeblinRefutation.claim
   digest: Qubit half-depolarization refutes the conditional reverse Doeblin bound. -/

import D5.S3.Quantum.Divergence.UmegakiChannelSupportedExtension
import D5.S3.Quantum.Divergence.CompleteHockeyStickRefutation

/-! Hirche–George–Nuradha–Wilde, arXiv:2608.27171v1, §2.5 and after Proposition 9.
George–Hirche–Nuradha–Wilde, arXiv:2503.22823v3, (6.54)–(6.55) and Proposition 33. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Divergence.ConditionalExpansion.ReverseDoeblinRefutation

open _root_.Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState QuantumChannel)
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
  (E act amp amp_sub_smul ptr ptr_sub_smul)
open D5.S3.Quantum.Divergence.UmegakiChannelSupportedExtension
  (depolarizingChannel act_depolarizingChannel)
open D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation (diagonal_norm)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)

open private identityChannel amp_depolarizing replacementMatrix from
  D5.S3.Quantum.Divergence.UmegakiChannelSupportedExtension
open private diagonalState marginal_diagonal from D5.S3.Quantum.Divergence.FaithfulConditionalGap
open private twice_posTrace from D5.S3.Quantum.Divergence.CompleteHockeyStickRefutation

local notation "raw" => CStarMatrix.ofMatrix.symm

/-- The pointwise form of the proposed extension of the reverse Doeblin bound to
the conditional trace-distance expansion coefficient. For density states, `E 1`
is trace distance. The denominator is positive as in Eq. (2.42) and Remark 2. -/
def claim : Prop :=
  ∀ (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (N : QuantumChannel A B) (post : QuantumChannel B A)
    (p : ℝ) (X : Matrix A A ℂ),
    0 ≤ p → p ≤ 1 → X.IsHermitian →
    (∀ Z : Matrix A A ℂ, act post (act N Z) = (1 - p) • Z + p • (Z.trace • X)) →
    ∀ (R : Type) [Fintype R] [DecidableEq R] (ρ σ : DensityState (R × A)),
      0 < E 1 (raw ρ.1) (raw σ.1) - E 1 (ptr (raw ρ.1)) (ptr (raw σ.1)) →
      1 - p ≤ (E 1 (amp N (raw ρ.1)) (amp N (raw σ.1)) -
        E 1 (ptr (raw ρ.1)) (ptr (raw σ.1))) /
        (E 1 (raw ρ.1) (raw σ.1) - E 1 (ptr (raw ρ.1)) (ptr (raw σ.1)))

private def half : Set.Ioo (0 : ℝ) 1 := ⟨1 / 2, by norm_num, by norm_num⟩

private def mixed : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℝ) • 1

private theorem degradation (Z : Matrix (Fin 2) (Fin 2) ℂ) :
    act (identityChannel (Fin 2)) (act (depolarizingChannel (Fin 2) half) Z) =
      (1 - (1 / 2 : ℝ)) • Z + (1 / 2 : ℝ) • (Z.trace • mixed) := by
  change act (depolarizingChannel (Fin 2) half) Z = _
  rw [act_depolarizingChannel]
  norm_num [half, mixed, Fintype.card_fin]

private def rhoEntries (i : Fin 2 × Fin 2) : ℝ := ![![1, 0], ![0, 0]] i.1 i.2

private def sigmaEntries (i : Fin 2 × Fin 2) : ℝ := ![![0, 1 / 4], ![3 / 4, 0]] i.1 i.2

private def rho : DensityState (Fin 2 × Fin 2) :=
  diagonalState rhoEntries
    (by rintro ⟨r, a⟩; fin_cases r <;> fin_cases a <;> norm_num [rhoEntries])
    (by norm_num [Fintype.sum_prod_type, Fin.sum_univ_two, rhoEntries])

private def sigma : DensityState (Fin 2 × Fin 2) :=
  diagonalState sigmaEntries
    (by rintro ⟨r, a⟩; fin_cases r <;> fin_cases a <;> norm_num [sigmaEntries])
    (by norm_num [Fintype.sum_prod_type, Fin.sum_univ_two, sigmaEntries])

private theorem input_difference :
    raw rho.1 - (1 : ℝ) • raw sigma.1 =
      diagonal (fun i => ((rhoEntries i - sigmaEntries i : ℝ) : ℂ)) := by
  change diagonal (fun i => (rhoEntries i : ℂ)) -
    (1 : ℝ) • diagonal (fun i => (sigmaEntries i : ℂ)) = _
  rw [one_smul, diagonal_sub]
  simp only [Complex.ofReal_sub]

private theorem reference_difference :
    ptr (raw rho.1) - (1 : ℝ) • ptr (raw sigma.1) =
      diagonal (fun i => ((![(3 / 4 : ℝ), -(3 / 4)] i : ℝ) : ℂ)) := by
  rw [← ptr_sub_smul, input_difference]
  change partialTraceRight _ = _
  rw [marginal_diagonal]
  congr 1
  funext r
  fin_cases r <;> norm_num [Fin.sum_univ_two, rhoEntries, sigmaEntries, Complex.ofReal_sub]

private theorem output_difference :
    amp (depolarizingChannel (Fin 2) half) (raw rho.1) -
      (1 : ℝ) • amp (depolarizingChannel (Fin 2) half) (raw sigma.1) =
      diagonal (fun i =>
        ((![![(11 / 16 : ℝ), 1 / 16], ![-(9 / 16), -(3 / 16)]] i.1 i.2 : ℝ) : ℂ)) := by
  rw [← amp_sub_smul, amp_depolarizing, input_difference, replacementMatrix, marginal_diagonal]
  ext ⟨r, a⟩ ⟨s, b⟩
  fin_cases r <;> fin_cases s <;> fin_cases a <;> fin_cases b <;>
    norm_num [half, rhoEntries, sigmaEntries, Fin.sum_univ_two, Matrix.diagonal_apply,
      Matrix.kronecker_apply, Matrix.one_apply, Matrix.add_apply, Matrix.smul_apply,
      Complex.real_smul, Prod.mk.injEq, Complex.ofReal_sub, map_div₀, map_ofNat]

private theorem half_norm_of_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    (d : n → ℝ) (htrace : ∑ i, d i = 0) :
    ConditionalHockeyStickOrthogonalReduction.posTrace (diagonal fun i => (d i : ℂ)) =
      (∑ i, |d i|) / 2 := by
  have hHerm : (diagonal fun i => (d i : ℂ)).IsHermitian :=
    Matrix.isHermitian_diagonal_iff.mpr (fun i => by simp [IsSelfAdjoint])
  have htrace' : RHLinalg.rtrace (diagonal fun i => (d i : ℂ)) = 0 := by
    simp [RHLinalg.rtrace, Matrix.trace_diagonal, ← Complex.ofReal_sum, htrace]
  have h := twice_posTrace _ hHerm
  rw [diagonal_norm, htrace', add_zero] at h
  linarith

private theorem distances :
    E 1 (raw rho.1) (raw sigma.1) = 1 ∧
    E 1 (ptr (raw rho.1)) (ptr (raw sigma.1)) = 3 / 4 ∧
    E 1 (amp (depolarizingChannel (Fin 2) half) (raw rho.1))
      (amp (depolarizingChannel (Fin 2) half) (raw sigma.1)) = 3 / 4 := by
  unfold E
  rw [input_difference, reference_difference, output_difference]
  refine ⟨?_, ?_, ?_⟩ <;> rw [half_norm_of_diagonal] <;>
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_two, rhoEntries, sigmaEntries]

/-- The output trace distance equals the reference trace distance, while the
input distance exceeds it by one quarter. The degradation has weight one half. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨hInput, hRef, hOutput⟩ := distances
  have hHerm : mixed.IsHermitian := by
    exact Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint] : IsSelfAdjoint (1 / 2 : ℝ))
  have hBound := h (Fin 2) (Fin 2) (depolarizingChannel (Fin 2) half)
    (identityChannel (Fin 2)) (1 / 2) mixed (by norm_num) (by norm_num)
    hHerm degradation (Fin 2) rho sigma (by rw [hInput, hRef]; norm_num)
  rw [hInput, hRef, hOutput] at hBound
  norm_num at hBound

#print axioms claim
#print axioms result

end D5.S3.Quantum.Divergence.ConditionalExpansion.ReverseDoeblinRefutation
