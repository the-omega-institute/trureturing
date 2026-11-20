import D5.S3.Quantum.Recovery.PetzActualLikelihoodEntropy
import D5.S3.Quantum.Recovery.PetzLikelihoodRectangularAmplitude
import D5.S3.Quantum.Recovery.PetzSingularInputLimit
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Isometry

/-!
# Uniform ordinary Petz recovery for commuting inputs

The input trace-log is resolved using the spectral pieces of the supported
likelihood operator. After the map, the same pieces give the retained PGM
pair weights and the two matrices in the output trace-log. The result uses
the full trace norm and the natural logarithm.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (density_posSemidef)
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
  (SupportContained finiteTraceLogRelativeEntropy)
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery (spectralInverseSqrt)
open PetzOverlapEntropyDerivative (faithfulRelativeEntropy)
open PetzPositiveTracePostselection (mapDensityState ordinaryPetz)
open PetzPostselectionSpectralJensen (stateMatrix)
open PetzLikelihoodRectangularAmplitude
  (LikelihoodResolution LikelihoodValues commutingResolution likelihoodOperator)
open QuadraticBayesRiskGeometricPetz
  (scoreMoment)
open PetzActualLikelihoodEntropy
  (actualEntropyLoss two_thirds_geometricRisk_sqrt_le_actualEntropyLoss)

open private indicator likelihoodOperator_pos sum_spectral_indicators sqrt_eq_real_cfc from
  D5.S3.Quantum.Recovery.PetzLikelihoodRectangularAmplitude

namespace PetzCommutingInputUniformRecovery

variable {a b : Type*} [Fintype a] [DecidableEq a]

private theorem commutingResolution_weighted_cfc
    (ρ σ : DensityState a) (hComm : Commute (stateMatrix ρ) (stateMatrix σ))
    (hSupp : SupportContained ρ σ) (f : ℝ → ℝ) :
    let L := commutingResolution ρ σ hComm hSupp
    (∑ j, f (L.likelihood j) • L.piece j) =
      CFC.sqrt (stateMatrix σ) * cfc f (likelihoodOperator ρ σ) *
        CFC.sqrt (stateMatrix σ) := by
  let S := CFC.sqrt (stateMatrix σ)
  let K := likelihoodOperator ρ σ
  have hsum : (∑ j : LikelihoodValues ρ σ, f j.val • cfc (indicator j.val) K) = cfc f K :=
    sum_spectral_indicators K (likelihoodOperator_pos ρ σ).isHermitian f
  change (∑ j : LikelihoodValues ρ σ, f j.val • (S * cfc (indicator j.val) K * S)) =
    S * cfc f K * S
  calc
    _ = ∑ j : LikelihoodValues ρ σ, S * (f j.val • cfc (indicator j.val) K) * S := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [Matrix.mul_smul, Matrix.smul_mul]
    _ = _ := by rw [← Matrix.sum_mul, ← Matrix.mul_sum, hsum]

/-- The supported input trace-log is the likelihood entropy of its actual
spectral pieces. The zero eigenvalues contribute by the same trace formula. -/
theorem finiteTraceLog_eq_likelihood
    (ρ σ : DensityState a) (hComm : Commute (stateMatrix ρ) (stateMatrix σ))
    (hSupp : SupportContained ρ σ) :
    let L := commutingResolution ρ σ hComm hSupp
    finiteTraceLogRelativeEntropy ρ σ =
      ∑ j, (L.piece j).trace.re * (L.likelihood j * Real.log (L.likelihood j)) := by
  let L := commutingResolution ρ σ hComm hSupp
  let R := stateMatrix ρ
  let Q := stateMatrix σ
  let S := CFC.sqrt Q
  let K := likelihoodOperator ρ σ
  have hQ : Q.PosSemidef := density_posSemidef σ
  have hK : K.PosSemidef := likelihoodOperator_pos ρ σ
  have hQH : Commute Q (spectralInverseSqrt Q) := by
    change Commute Q (cfc (fun x : ℝ => (Real.sqrt x)⁻¹) Q)
    exact ((Commute.refl Q).cfc_real _).symm
  have hQK : Commute Q K := by
    change Commute Q (spectralInverseSqrt Q * R * spectralInverseSqrt Q)
    exact (hQH.mul_right (show Commute Q R from hComm.symm)).mul_right hQH
  obtain ⟨C, ⟨s, hs⟩, ⟨k, hk⟩⟩ :=
    Commute.exists_cfc hQ.isHermitian hK.isHermitian hQK
  have hC : IsSelfAdjoint C := by
    by_contra hn
    have hQzero : Q = 0 := hs.trans (cfc_apply_of_not_predicate C hn)
    have htrace : Q.trace = 1 := σ.2.2
    rw [hQzero, Matrix.trace_zero] at htrace
    exact zero_ne_one htrace
  have hcontinuous (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ C) :=
    C.finite_real_spectrum.continuousOn f
  have hmul (f g : ℝ → ℝ) :
      cfc f C * cfc g C = cfc (fun x => f x * g x) C :=
    (cfc_mul f g C (hcontinuous f) (hcontinuous g)).symm
  have hsub (f g : ℝ → ℝ) :
      cfc f C - cfc g C = cfc (fun x => f x - g x) C :=
    (cfc_sub f g C (hcontinuous f) (hcontinuous g)).symm
  have hcomp (f g : ℝ → ℝ) : cfc f (cfc g C) = cfc (f ∘ g) C :=
    (cfc_comp f g C hC ((C.finite_real_spectrum.image g).continuousOn f)
      (hcontinuous g)).symm
  have hs_nonneg : ∀ x ∈ spectrum ℝ C, 0 ≤ s x := by
    apply (cfc_nonneg_iff s C (hcontinuous s) hC).mp
    rw [← hs]
    exact hQ.nonneg
  have hS : S = cfc (Real.sqrt ∘ s) C := by
    change CFC.sqrt Q = _
    rw [sqrt_eq_real_cfc hQ, hs, hcomp Real.sqrt s]
  have hSandwich (f : ℝ → ℝ) :
      S * cfc f K * S = cfc (fun x => s x * f (k x)) C := by
    rw [hS, hk, hcomp f k, hmul, hmul]
    apply cfc_congr
    intro x hx
    change Real.sqrt (s x) * f (k x) * Real.sqrt (s x) = s x * f (k x)
    rw [mul_right_comm (Real.sqrt (s x)) (f (k x)), Real.mul_self_sqrt (hs_nonneg x hx)]
  -- The support hypothesis is used in the exact weighted resolution of ρ.
  have hR : R = cfc (fun x => s x * k x) C := by
    calc
      R = ∑ j, L.likelihood j • L.piece j := L.sum_weighted.symm
      _ = S * cfc (fun x : ℝ => x) K * S :=
        commutingResolution_weighted_cfc ρ σ hComm hSupp (fun x => x)
      _ = _ := hSandwich (fun x => x)
  have hTraceMatrix :
      R * (cfc Real.log R - cfc Real.log Q) =
        S * cfc (fun x : ℝ => x * Real.log x) K * S := by
    rw [hSandwich, hR, hs, hcomp Real.log (fun x => s x * k x), hcomp Real.log s, hsub, hmul]
    apply cfc_congr
    intro x _
    change (s x * k x) * (Real.log (s x * k x) - Real.log (s x)) =
      s x * (k x * Real.log (k x))
    by_cases hs0 : s x = 0
    · simp [hs0]
    by_cases hk0 : k x = 0
    · simp [hk0]
    rw [Real.log_mul hs0 hk0]
    ring
  change finiteTraceLogRelativeEntropy ρ σ =
    ∑ j, (L.piece j).trace.re * (L.likelihood j * Real.log (L.likelihood j))
  rw [PetzSingularInputLimit.finiteTraceLog_eq_raw]
  change (R * (cfc Real.log R - cfc Real.log Q)).trace.re = _
  rw [hTraceMatrix, ← commutingResolution_weighted_cfc ρ σ hComm hSupp
    (fun x => x * Real.log x)]
  change (∑ j, (L.likelihood j * Real.log (L.likelihood j)) • L.piece j).trace.re = _
  simp only [Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum, Complex.real_smul,
    Complex.re_ofReal_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

section ImagePieces

variable {ι : Type*} [Fintype ι]
variable {R Q : Matrix a a ℂ} (L : LikelihoodResolution R Q ι) (Φ : MatrixMap a b ℂ)

private theorem sum_image_pieces : (∑ i, Φ (L.piece i)) = Φ Q := by
  rw [← map_sum, L.sum_piece]

private theorem image_scoreMoment : scoreMoment (fun i => Φ (L.piece i)) L.likelihood = Φ R := by
  simp only [scoreMoment, ← LinearMap.map_smul_of_tower, ← map_sum, L.sum_weighted]

end ImagePieces

variable [Fintype b] [DecidableEq b]

/-- The output reference contains the support of the image of ρ, so the output
trace-log is the finite branch of Umegaki entropy. -/
theorem output_supportContained_of_commute
    (ρ σ : DensityState a) (hComm : Commute (stateMatrix ρ) (stateMatrix σ))
    (hSupp : SupportContained ρ σ) (Φ : MatrixMap a b ℂ) (hΦ : Φ.IsPositive)
    (hTP : Φ.IsTracePreserving) :
    SupportContained (mapDensityState Φ hΦ hTP ρ) (mapDensityState Φ hΦ hTP σ) := by
  let L := commutingResolution ρ σ hComm hSupp
  intro v hv
  change Φ (stateMatrix σ) *ᵥ v = 0 at hv
  change Φ (stateMatrix ρ) *ᵥ v = 0
  have hpieces (i : LikelihoodValues ρ σ) : Φ (L.piece i) *ᵥ v = 0 := by
    have hpos := hΦ (L.piece_pos i)
    have hle : Φ (L.piece i) ≤ Φ (stateMatrix σ) := by
      rw [← sum_image_pieces L Φ]
      exact Finset.single_le_sum (fun j _ => (hΦ (L.piece_pos j)).nonneg) (Finset.mem_univ i)
    have hdiff := (Matrix.le_iff.mp hle).dotProduct_mulVec_nonneg v
    rw [Matrix.sub_mulVec, hv, dotProduct_sub, dotProduct_zero, zero_sub] at hdiff
    exact hpos.dotProduct_mulVec_zero_iff.mp
      (le_antisymm (neg_nonneg.mp hdiff) (hpos.dotProduct_mulVec_nonneg v))
  rw [← image_scoreMoment L Φ, scoreMoment, Matrix.sum_mulVec]
  simp only [Matrix.smul_mulVec, hpieces, smul_zero, Finset.sum_const_zero]

private theorem actualEntropyLoss_image
    (ρ σ : DensityState a) (hComm : Commute (stateMatrix ρ) (stateMatrix σ))
    (hSupp : SupportContained ρ σ) (Φ : MatrixMap a b ℂ) (hΦ : Φ.IsPositive)
    (hTP : Φ.IsTracePreserving) :
    let L := commutingResolution ρ σ hComm hSupp
    actualEntropyLoss (fun i => Φ (L.piece i)) L.likelihood =
      finiteTraceLogRelativeEntropy ρ σ -
        finiteTraceLogRelativeEntropy (mapDensityState Φ hΦ hTP ρ) (mapDensityState Φ hΦ hTP σ) := by
  let L := commutingResolution ρ σ hComm hSupp
  have hOutput :
      finiteTraceLogRelativeEntropy (mapDensityState Φ hΦ hTP ρ) (mapDensityState Φ hΦ hTP σ) =
        faithfulRelativeEntropy (Φ (stateMatrix ρ)) (Φ (stateMatrix σ)) :=
    PetzSingularInputLimit.finiteTraceLog_eq_raw
      (mapDensityState Φ hΦ hTP ρ) (mapDensityState Φ hΦ hTP σ)
  change actualEntropyLoss (fun i => Φ (L.piece i)) L.likelihood =
    finiteTraceLogRelativeEntropy ρ σ -
      finiteTraceLogRelativeEntropy (mapDensityState Φ hΦ hTP ρ) (mapDensityState Φ hΦ hTP σ)
  rw [actualEntropyLoss, image_scoreMoment L Φ, sum_image_pieces L Φ, hOutput,
    finiteTraceLog_eq_likelihood ρ σ hComm hSupp]
  have hTrace : ∀ X, (Φ X).trace = X.trace := hTP
  simp only [hTrace, L]

/-- The squared full trace-norm error of ordinary Petz recovery for commuting
density states is at most twelve times their finite Umegaki data-processing
loss under a positive trace-preserving map. -/
theorem traceNorm_sub_ordinaryPetz_sq_le_twelve_umegakiLoss_of_commute
    (ρ σ : DensityState a) (hComm : Commute (stateMatrix ρ) (stateMatrix σ))
    (hSupp : SupportContained ρ σ) (Φ : MatrixMap a b ℂ) (hΦ : Φ.IsPositive)
    (hTP : Φ.IsTracePreserving) :
    traceNorm (stateMatrix ρ - ordinaryPetz Φ (stateMatrix σ) (Φ (stateMatrix ρ))) ^ 2 ≤
      12 * (finiteTraceLogRelativeEntropy ρ σ -
        finiteTraceLogRelativeEntropy
          (mapDensityState Φ hΦ hTP ρ) (mapDensityState Φ hΦ hTP σ)) := by
  let L := commutingResolution ρ σ hComm hSupp
  have hLoss := two_thirds_geometricRisk_sqrt_le_actualEntropyLoss
    (fun i => Φ (L.piece i)) L.likelihood (fun i => hΦ (L.piece_pos i)) L.likelihood_nonneg
  rw [← L.likelihoodMismatch_eq_geometricRisk Φ hΦ,
    actualEntropyLoss_image ρ σ hComm hSupp Φ hΦ hTP] at hLoss
  calc
    _ ≤ 4 * (2 * L.likelihoodMismatch Φ - (L.likelihoodMismatch Φ) ^ 2) :=
      PetzLikelihoodRectangularAmplitude.traceNorm_sub_ordinaryPetz_sq_le_of_commute
        ρ σ hComm hSupp Φ hΦ hTP
    _ ≤ 8 * L.likelihoodMismatch Φ := by nlinarith only [sq_nonneg (L.likelihoodMismatch Φ)]
    _ ≤ _ := by linarith only [hLoss]

end PetzCommutingInputUniformRecovery
