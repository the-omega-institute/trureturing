import D5.S3.Quantum.Recovery.PetzPositiveTracePostselection
import D5.S3.Quantum.Divergence.UmegakiArithmeticBKM
import D5.S3.Quantum.Entanglement.TriangleIndependentSourceNoise
import D5.S3.Quantum.Foundation.FinitePreparationChannel
import D5.S3.Quantum.Recovery.KrausCompletion

/-!
# Common ensemble recovery by the pretty-good measurement

The common CPTP recovery construction is from the accompanying
positive-map-postselected-petz-recovery.txt. The success calculation applies
PetzPostselectionSpectralJensen.exp_half_entropy_le_trace_threeHalves_inverseSqrt
to the actual retained density matrices. The proof of the CFC power identity
follows the private threeHalves_eq_mul_sqrt in PetzPositiveTracePostselection.
The measurement uses KrausCompletion.row_reset_action and
FiniteKrausChannel.finite_kraus_quantum_channel. Its composition with
FinitePreparationChannel.finite_preparation_quantum_channel acts on every
complex input matrix. The bound is pointwise for arbitrary positive priors.
For orthogonal source states it reduces to twice the failure probability,
and for commuting projective postselection the entropy loss controls that
probability.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel (finite_kraus_quantum_channel)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Quantum.Foundation.FinitePreparationChannel (finite_preparation_quantum_channel)
open D5.S3.Quantum.Foundation.FiniteTraceDistance
  (traceNorm traceNorm_add_le traceNorm_of_posSemidef traceNorm_sub_orthogonal)
open D5.S3.Quantum.Entanglement.TriangleIndependentSourceNoise (LocalPOVM)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (density_posSemidef)
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
  (SupportContained finiteTraceLogRelativeEntropy)
open D5.S3.Quantum.Divergence.UmegakiArithmeticBKM (matrixHS hsInner_matrix)
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery (spectralInverseSqrt spectralSupport)
open D5.S3.Quantum.Recovery.KrausCompletion (rowReset row_reset_action)
open D5.S3.Quantum.Lieb.SupportPerspectiveTransport
  (spectral_sqrt_normalization support_of_nonneg_le_smul)
open PetzPostselectionSpectralJensen
  (stateMatrix exp_half_entropy_le_trace_threeHalves_inverseSqrt)
open PetzPositiveTracePostselection (mapDensityState)
open PetzPostselectedReference (finiteTraceLogRelativeEntropy_of_postselection)

namespace PetzCommonEnsembleRecovery

variable {ι a b : Type*} [Fintype ι]
  [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Positive priors on a finite family of actual density states. -/
structure Ensemble (ι a : Type*) [Fintype ι] [Fintype a] [DecidableEq a] where
  weight : ι → ℝ
  weight_pos : ∀ j, 0 < weight j
  weight_sum : ∑ j, weight j = 1
  state : ι → DensityState a

namespace Ensemble

def averageMatrix (e : Ensemble ι a) : Matrix a a ℂ :=
  ∑ j, e.weight j • stateMatrix (e.state j)

def reference (e : Ensemble ι a) : DensityState a := by
  have hpos : e.averageMatrix.PosSemidef :=
    Matrix.posSemidef_sum Finset.univ fun j _ =>
      (density_posSemidef (e.state j)).smul (e.weight_pos j).le
  refine ⟨CStarMatrix.ofMatrix e.averageMatrix,
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hpos.nonneg, ?_⟩
  have htrace (j : ι) : (stateMatrix (e.state j)).trace = 1 := (e.state j).2.2
  change e.averageMatrix.trace = 1
  rw [averageMatrix]
  simp only [Matrix.trace_sum, Matrix.trace_smul, htrace, Complex.real_smul, mul_one,
    ← Complex.ofReal_sum, e.weight_sum, Complex.ofReal_one]

@[simp] theorem reference_matrix (e : Ensemble ι a) :
    stateMatrix e.reference = e.averageMatrix := rfl

def map (e : Ensemble ι a) (Φ : MatrixMap a b ℂ)
    (hΦ : Φ.IsPositive) (hTP : Φ.IsTracePreserving) : Ensemble ι b where
  weight := e.weight
  weight_pos := e.weight_pos
  weight_sum := e.weight_sum
  state j := mapDensityState Φ hΦ hTP (e.state j)

@[simp] theorem map_state_matrix (e : Ensemble ι a) (Φ : MatrixMap a b ℂ)
    (hΦ : Φ.IsPositive) (hTP : Φ.IsTracePreserving) (j : ι) :
    stateMatrix ((e.map Φ hΦ hTP).state j) = Φ (stateMatrix (e.state j)) := rfl

/-- The retained reference is the image of the source reference. -/
theorem reference_map (e : Ensemble ι a) (Φ : MatrixMap a b ℂ)
    (hΦ : Φ.IsPositive) (hTP : Φ.IsTracePreserving) :
    (e.map Φ hΦ hTP).reference = mapDensityState Φ hΦ hTP e.reference := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  change (e.map Φ hΦ hTP).averageMatrix = Φ e.averageMatrix
  unfold averageMatrix
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change e.weight j • Φ (stateMatrix (e.state j)) =
    Φ (e.weight j • stateMatrix (e.state j))
  exact (LinearMap.map_smul_of_tower Φ (e.weight j) (stateMatrix (e.state j))).symm

private theorem state_le_inv_smul_reference (e : Ensemble ι a) (j : ι) :
    stateMatrix (e.state j) ≤ (e.weight j)⁻¹ • stateMatrix e.reference := by
  have hle : e.weight j • stateMatrix (e.state j) ≤ e.averageMatrix :=
    Finset.single_le_sum
      (fun k _ => ((density_posSemidef (e.state k)).smul (e.weight_pos k).le).nonneg)
      (Finset.mem_univ j)
  have hdiff := Matrix.le_iff.mp hle
  apply Matrix.le_iff.mpr
  simpa only [reference_matrix, smul_sub, smul_smul, inv_mul_cancel₀ (e.weight_pos j).ne',
    one_smul] using hdiff.smul (inv_nonneg.mpr (e.weight_pos j).le)

/-- Every probe lies in the support of the actual average, even for singular averages. -/
theorem supportContained_reference (e : Ensemble ι a) (j : ι) :
    SupportContained (e.state j) e.reference := by
  intro v hv
  change stateMatrix e.reference *ᵥ v = 0 at hv
  change stateMatrix (e.state j) *ᵥ v = 0
  have hp := density_posSemidef (e.state j)
  have hnonneg := hp.dotProduct_mulVec_nonneg v
  have hdiff := (Matrix.le_iff.mp (e.state_le_inv_smul_reference j)).dotProduct_mulVec_nonneg v
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hv, smul_zero, dotProduct_sub,
    dotProduct_zero, zero_sub] at hdiff
  exact hp.dotProduct_mulVec_zero_iff.mp (le_antisymm (neg_nonneg.mp hdiff) hnonneg)

def pgmSupportedEffect (e : Ensemble ι a) (j : ι) : Matrix a a ℂ :=
  let H := spectralInverseSqrt (stateMatrix e.reference)
  e.weight j • (H * stateMatrix (e.state j) * H)

variable [DecidableEq ι]

/-- The actual pretty-good measurement on the full carrier, assigning the
orthogonal complement of the retained support to the fixed outcome j₀. -/
def pgm (e : Ensemble ι a) (j₀ : ι) : LocalPOVM a ι := by
  let q := stateMatrix e.reference
  let H := spectralInverseSqrt q
  let Q := spectralSupport q
  have hspec := spectral_sqrt_normalization q (density_posSemidef e.reference)
  refine ⟨fun j => e.pgmSupportedEffect j + if j = j₀ then 1 - Q else 0, ?_, ?_⟩
  · intro j
    obtain ⟨_, hH, hQ, hQQ, _, _, _, _⟩ := hspec
    have hProj : IsStarProjection Q := ⟨hQQ, hQ⟩
    have hbase : (e.pgmSupportedEffect j).PosSemidef := by
      have hsandwich : (H * stateMatrix (e.state j) * H).PosSemidef := by
        change Hᴴ = H at hH
        simpa only [hH] using (density_posSemidef (e.state j)).mul_mul_conjTranspose_same H
      exact hsandwich.smul (e.weight_pos j).le
    apply hbase.add
    split_ifs
    · exact hProj.one_sub_nonneg.posSemidef
    · exact Matrix.PosSemidef.zero
  · obtain ⟨_, _, _, _, _, _, _, hnorm⟩ := hspec
    have hsum : ∑ j, e.pgmSupportedEffect j = Q := by
      have hterm (j : ι) : e.pgmSupportedEffect j =
          H * (e.weight j • stateMatrix (e.state j)) * H := by
        simp only [pgmSupportedEffect, H, q, Matrix.mul_smul, Matrix.smul_mul]
      simp_rw [hterm]
      rw [← Matrix.sum_mul, ← Matrix.mul_sum]
      exact hnorm
    rw [Finset.sum_add_distrib, hsum]
    simp

/-- Every retained probe gives the same Born weight to the supported and completed effects. -/
theorem probe_mul_pgm_effect (e : Ensemble ι a) (j₀ i j : ι) :
    stateMatrix (e.state i) * (e.pgm j₀).effect j =
      stateMatrix (e.state i) * e.pgmSupportedEffect j := by
  let q := stateMatrix e.reference
  let Q := spectralSupport q
  let p := stateMatrix (e.state i)
  obtain ⟨_, _, hQ, _, _, _, hQq, _⟩ := spectral_sqrt_normalization q
    (density_posSemidef e.reference)
  obtain ⟨_, hpQ⟩ := support_of_nonneg_le_smul q p Q hQ hQq
    (density_posSemidef (e.state i)) (e.weight i)⁻¹ (e.state_le_inv_smul_reference i)
  change p * (e.pgmSupportedEffect j + if j = j₀ then 1 - Q else 0) = _
  rw [Matrix.mul_add]
  split_ifs
  · rw [Matrix.mul_sub, Matrix.mul_one, hpQ, sub_self, add_zero]
  · rw [Matrix.mul_zero, add_zero]

end Ensemble

private theorem cfc_threeHalves (P : Matrix b b ℂ) (hP : P.PosSemidef) :
    cfc (fun x : ℝ => x ^ (3 / 2 : ℝ)) P = P * CFC.sqrt P := by
  rw [CFC.sqrt_eq_real_sqrt P hP.nonneg,
    cfcₙ_eq_cfc (f := Real.sqrt) (a := P) (hf0 := by simp)]
  calc
    _ = cfc (fun x : ℝ => x * Real.sqrt x) P := by
      apply cfc_congr
      intro x hx
      have hx₀ := spectrum_nonneg_of_nonneg hP.nonneg hx
      change x ^ (3 / 2 : ℝ) = x * Real.sqrt x
      rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
        Real.rpow_add_of_nonneg hx₀ zero_le_one (by norm_num), Real.rpow_one]
    _ = cfc (fun x : ℝ => x) P * cfc Real.sqrt P :=
      cfc_mul (fun x : ℝ => x) Real.sqrt P continuous_id.continuousOn
        Real.continuous_sqrt.continuousOn
    _ = _ := by rw [cfc_id' ℝ P hP.isHermitian.isSelfAdjoint]

/-- The entropy bound for the unweighted PGM quadratic form on a single probe. -/
theorem exp_entropy_le_pgm_quadratic (p q : DensityState b) (hsupport : SupportContained p q) :
    Real.exp (finiteTraceLogRelativeEntropy p q) ≤
      (stateMatrix p * (spectralInverseSqrt (stateMatrix q) * stateMatrix p *
        spectralInverseSqrt (stateMatrix q))).trace.re := by
  let P := stateMatrix p
  let H := spectralInverseSqrt (stateMatrix q)
  let A := CFC.sqrt P
  let B := A * H * A
  have hA : Aᴴ = A := (CFC.sqrt_nonneg P).posSemidef.isHermitian.eq
  have hAA : A * A = P := CFC.sqrt_mul_sqrt_self P (density_posSemidef p).nonneg
  obtain ⟨_, hH, _, _, _, _, _, _⟩ :=
    spectral_sqrt_normalization (stateMatrix q) (density_posSemidef q)
  change Hᴴ = H at hH
  have hB : Bᴴ = B := by
    simp only [B, Matrix.conjTranspose_mul, hA, hH, Matrix.mul_assoc]
  have hInner (X Y : Matrix b b ℂ) :
      inner ℂ (matrixHS X) (matrixHS Y) = (Xᴴ * Y).trace := hsInner_matrix X Y
  have hGram (X : Matrix b b ℂ) : ‖matrixHS X‖ ^ 2 = (Xᴴ * X).trace.re := by
    simpa only [hInner, RCLike.re_eq_complex_re] using
      (norm_sq_eq_re_inner (𝕜 := ℂ) (matrixHS X))
  have hAnorm : ‖matrixHS A‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    have htrace : P.trace = 1 := p.2.2
    rw [hGram, hA, hAA, htrace, Complex.one_re, one_pow]
  have hcross : (Aᴴ * B).trace =
      (cfc (fun x : ℝ => x ^ (3 / 2 : ℝ)) P * H).trace := by
    calc
      _ = ((A * A) * H * A).trace := by
        simp only [hA, B, Matrix.mul_assoc]
      _ = (P * H * A).trace := by rw [hAA]
      _ = (A * P * H).trace := Matrix.trace_mul_cycle P H A
      _ = _ := by
        rw [cfc_threeHalves P (density_posSemidef p)]
        rw [show A * P = P * A by simp only [← hAA, Matrix.mul_assoc]]
  have hBgram : (Bᴴ * B).trace = (P * (H * P * H)).trace := by
    rw [hB]
    have hprod : B * B = A * (H * P * H) * A := by
      calc
        _ = A * (H * (A * A) * H) * A := by simp only [B, Matrix.mul_assoc]
        _ = _ := by rw [hAA]
    rw [hprod, Matrix.trace_mul_cycle, hAA]
  have hj := exp_half_entropy_le_trace_threeHalves_inverseSqrt p q hsupport
  change Real.exp (finiteTraceLogRelativeEntropy p q / 2) ≤
    (cfc (fun x : ℝ => x ^ (3 / 2 : ℝ)) P * H).trace.re at hj
  have hcs := re_inner_le_norm (𝕜 := ℂ) (matrixHS A) (matrixHS B)
  simp only [hInner, hcross, RCLike.re_eq_complex_re, hAnorm, one_mul] at hcs
  let D := finiteTraceLogRelativeEntropy p q
  calc
    Real.exp D = Real.exp (D / 2) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    _ ≤ ‖matrixHS B‖ ^ 2 :=
      (sq_le_sq₀ (Real.exp_pos _).le (norm_nonneg _)).mpr (hj.trans hcs)
    _ = _ := (hGram B).trans (congrArg Complex.re hBgram)

/-- The Born probability is real, so its real part is the physical probability. -/
def born (p : DensityState b) (E : Matrix b b ℂ) : ℝ :=
  (stateMatrix p * E).trace.re

variable [DecidableEq ι] in
/-- Pointwise success with arbitrary positive priors and arbitrary overlap among probes. -/
theorem pgm_success (e : Ensemble ι b) (j₀ j : ι) :
    e.weight j * Real.exp (finiteTraceLogRelativeEntropy (e.state j) e.reference) ≤
      born (e.state j) ((e.pgm j₀).effect j) := by
  unfold born
  rw [e.probe_mul_pgm_effect j₀ j j]
  unfold Ensemble.pgmSupportedEffect
  simp only [Matrix.mul_smul, Matrix.trace_smul, Complex.real_smul, Complex.re_ofReal_mul]
  exact mul_le_mul_of_nonneg_left
    (exp_entropy_le_pgm_quadratic (e.state j) e.reference (e.supportContained_reference j))
    (e.weight_pos j).le

variable [DecidableEq ι] in
private theorem finite_measurement_channel (M : LocalPOVM b ι) :
    ∃ C : QuantumChannel b ι, ∀ X : Matrix b b ℂ,
      CStarMatrix.ofMatrix.symm (C.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        Matrix.diagonal (fun j => (X * M.effect j).trace) := by
  let V (j : ι) := CFC.sqrt (M.effect j)
  have hV (j : ι) : (V j)ᴴ = V j :=
    (CFC.sqrt_nonneg (M.effect j)).posSemidef.isHermitian.eq
  have hVV (j : ι) : V j * V j = M.effect j :=
    CFC.sqrt_mul_sqrt_self _ (M.positive j).nonneg
  let K (jk : ι × b) := rowReset jk.1 (V jk.1) jk.2
  have hRowGram (j : ι) : (∑ k : b, (rowReset j (V j) k)ᴴ * rowReset j (V j) k) =
      M.effect j := by
    have hSingle :
        (∑ k : b, (Matrix.single j k (1 : ℂ))ᴴ * Matrix.single j k (1 : ℂ)) =
          (1 : Matrix b b ℂ) := by
      calc
        _ = ∑ k : b, Matrix.single k k (1 : ℂ) := by
          apply Finset.sum_congr rfl
          intro k _
          simpa only [Matrix.conjTranspose_single, star_one, one_mul] using
            (Matrix.single_mul_single_same (c := (1 : ℂ)) k j k (1 : ℂ))
        _ = 1 := Matrix.sum_single_one
    calc
      _ = (V j)ᴴ *
          (∑ k : b, (Matrix.single j k (1 : ℂ))ᴴ * Matrix.single j k (1 : ℂ)) * V j := by
        simp only [rowReset, Matrix.conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul,
          Matrix.mul_assoc]
      _ = _ := by rw [hSingle, Matrix.mul_one, hV, hVV]
  have hK : ∑ k, (K k)ᴴ * K k = 1 := by
    simp only [Fintype.sum_prod_type, K, hRowGram, M.complete]
  obtain ⟨C, hC⟩ := finite_kraus_quantum_channel K hK
  refine ⟨C, fun X => ?_⟩
  rw [hC]
  simp only [Fintype.sum_prod_type, K, row_reset_action]
  have htrace (j : ι) : (V j * X * (V j)ᴴ).trace = (X * M.effect j).trace := by
    rw [hV, Matrix.trace_mul_cycle, hVV, Matrix.trace_mul_comm]
  simp only [htrace, Matrix.smul_single, smul_eq_mul, mul_one, Matrix.sum_single_eq_diagonal]

/-- The probability-weighted preparation map is CPTP on the whole complex algebra. -/
theorem finite_measure_prepare_channel (M : LocalPOVM b ι) (ρ : ι → DensityState a) :
    ∃ C : QuantumChannel b a, ∀ X : Matrix b b ℂ,
      CStarMatrix.ofMatrix.symm (C.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        ∑ j, (X * M.effect j).trace • stateMatrix (ρ j) := by
  classical
  obtain ⟨measure, hmeasure⟩ := finite_measurement_channel M
  obtain ⟨prepare, hprepare⟩ := finite_preparation_quantum_channel ρ
  refine ⟨prepare.comp measure, fun X => ?_⟩
  have hmeasure' : measure.toCompletelyPositiveMap (CStarMatrix.ofMatrix X) =
      CStarMatrix.ofMatrix (Matrix.diagonal fun j => (X * M.effect j).trace) := by
    apply CStarMatrix.ofMatrix.symm.injective
    exact hmeasure X
  rw [QuantumChannel.comp_apply, hmeasure', hprepare]
  simp only [Matrix.diagonal_apply_eq]

private theorem born_nonneg (p : DensityState b) {E : Matrix b b ℂ} (hE : E.PosSemidef) :
    0 ≤ born p E :=
  (Complex.nonneg_iff.mp ((density_posSemidef p).trace_mul_nonneg hE)).1

private theorem born_sum (p : DensityState b) (M : LocalPOVM b ι) :
    ∑ j, born p (M.effect j) = 1 := by
  have htr : (stateMatrix p).trace = 1 := p.2.2
  unfold born
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.mul_sum, M.complete,
    Matrix.mul_one, htr, Complex.one_re]

private theorem born_cast (p : DensityState b) {E : Matrix b b ℂ} (hE : E.PosSemidef) :
    (born p E : ℂ) = (stateMatrix p * E).trace := by
  have him := (Complex.nonneg_iff.mp ((density_posSemidef p).trace_mul_nonneg hE)).2
  apply Complex.ext
  · exact Complex.ofReal_re _
  · simpa only [Complex.ofReal_im] using him

variable [DecidableEq ι]

/-- One common channel for all probes. The choice is made over channels with
the same explicit action on every complex input matrix. -/
def recoveryChannel (e : Ensemble ι a) (Φ : MatrixMap a b ℂ)
    (hΦ : Φ.IsPositive) (hTP : Φ.IsTracePreserving) (j₀ : ι) : QuantumChannel b a :=
  (finite_measure_prepare_channel ((e.map Φ hΦ hTP).pgm j₀) e.state).choose

theorem recoveryChannel_apply (e : Ensemble ι a) (Φ : MatrixMap a b ℂ)
    (hΦ : Φ.IsPositive) (hTP : Φ.IsTracePreserving) (j₀ : ι) (X : Matrix b b ℂ) :
    CStarMatrix.ofMatrix.symm
      ((recoveryChannel e Φ hΦ hTP j₀).toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        ∑ k, (X * ((e.map Φ hΦ hTP).pgm j₀).effect k).trace • stateMatrix (e.state k) :=
  (finite_measure_prepare_channel ((e.map Φ hΦ hTP).pgm j₀) e.state).choose_spec X

private theorem recoveryChannel_mapState_matrix (e : Ensemble ι a) (Φ : MatrixMap a b ℂ)
    (hΦ : Φ.IsPositive) (hTP : Φ.IsTracePreserving) (j₀ : ι) (p : DensityState b) :
    stateMatrix ((recoveryChannel e Φ hΦ hTP j₀).mapState p) =
      ∑ k, (stateMatrix p * ((e.map Φ hΦ hTP).pgm j₀).effect k).trace •
        stateMatrix (e.state k) :=
  recoveryChannel_apply e Φ hΦ hTP j₀ (stateMatrix p)

private theorem state_sub_outcomeMixture (M : LocalPOVM b ι) (ρ : ι → DensityState a)
    (p : DensityState b) (j : ι) :
    let X := (1 - born p (M.effect j)) • stateMatrix (ρ j)
    let Y := ∑ k ∈ Finset.univ.erase j, born p (M.effect k) • stateMatrix (ρ k)
    X.PosSemidef ∧ Y.PosSemidef ∧
      X.trace.re = 1 - born p (M.effect j) ∧ Y.trace.re = 1 - born p (M.effect j) ∧
      stateMatrix (ρ j) - (∑ k, (stateMatrix p * M.effect k).trace • stateMatrix (ρ k)) =
        X - Y := by
  let w : ι → ℝ := fun k => born p (M.effect k)
  let R : ι → Matrix a a ℂ := fun k => stateMatrix (ρ k)
  let X := (1 - w j) • R j
  let Y := ∑ k ∈ Finset.univ.erase j, w k • R k
  have hw (k : ι) : 0 ≤ w k := born_nonneg p (M.positive k)
  have htotal : ∑ k, w k = 1 := born_sum p M
  have herase := Finset.sum_erase_add Finset.univ w (Finset.mem_univ j)
  rw [htotal] at herase
  have hmass : ∑ k ∈ Finset.univ.erase j, w k = 1 - w j := eq_sub_of_add_eq herase
  have hfail : 0 ≤ 1 - w j := by
    rw [← hmass]
    exact Finset.sum_nonneg fun k _ => hw k
  have htr (k : ι) : (R k).trace = 1 := (ρ k).2.2
  change X.PosSemidef ∧ Y.PosSemidef ∧ X.trace.re = 1 - w j ∧
    Y.trace.re = 1 - w j ∧
    R j - (∑ k, (stateMatrix p * M.effect k).trace • R k) = X - Y
  refine ⟨(density_posSemidef (ρ j)).smul hfail,
    Matrix.posSemidef_sum _ (fun k _ => (density_posSemidef (ρ k)).smul (hw k)),
    ?_, ?_, ?_⟩
  · simp only [X, Matrix.trace_smul, Complex.real_smul, htr, mul_one, Complex.ofReal_re]
  · simp only [Y, Matrix.trace_sum, Matrix.trace_smul, Complex.real_smul, htr, mul_one,
      Complex.re_sum, Complex.ofReal_re, hmass]
  · have hsplit : Y + w j • R j = ∑ k, w k • R k :=
      Finset.sum_erase_add Finset.univ (fun k => w k • R k) (Finset.mem_univ j)
    have hcoeff (k : ι) : ((stateMatrix p * M.effect k).trace : ℂ) = (w k : ℂ) :=
      (born_cast p (M.positive k)).symm
    simp only [hcoeff, Complex.coe_smul, ← hsplit, X, sub_smul, one_smul]
    abel

omit [DecidableEq ι] in
private theorem traceNorm_outcomeMixture_bound (M : LocalPOVM b ι) (ρ : ι → DensityState a)
    (p : DensityState b) (j : ι) :
    traceNorm (stateMatrix (ρ j) -
      (∑ k, (stateMatrix p * M.effect k).trace • stateMatrix (ρ k))) ≤
        2 * (1 - born p (M.effect j)) := by
  classical
  obtain ⟨hX, hY, hXtr, hYtr, hsplit⟩ := state_sub_outcomeMixture M ρ p j
  rw [hsplit]
  have hnorm {X : Matrix a a ℂ} (h : X.PosSemidef) : traceNorm X = X.trace.re := by
    exact (Complex.ofReal_re (traceNorm X)).symm.trans
      (congrArg Complex.re (traceNorm_of_posSemidef h))
  let X := (1 - born p (M.effect j)) • stateMatrix (ρ j)
  let Y := ∑ k ∈ Finset.univ.erase j, born p (M.effect k) • stateMatrix (ρ k)
  change traceNorm (X - Y) ≤ 2 * (1 - born p (M.effect j))
  calc
    _ ≤ traceNorm X + traceNorm (-Y) := by
      simpa only [sub_eq_add_neg] using traceNorm_add_le X (-Y)
    _ = _ := by
      rw [D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm_neg,
        hnorm hX, hnorm hY, hXtr, hYtr]
      ring

omit [DecidableEq ι] in
private theorem traceNorm_outcomeMixture_orthogonal (M : LocalPOVM b ι)
    (ρ : ι → DensityState a) (p : DensityState b) (j : ι)
    (horth : ∀ k, j ≠ k → stateMatrix (ρ j) * stateMatrix (ρ k) = 0) :
    traceNorm (stateMatrix (ρ j) -
      (∑ k, (stateMatrix p * M.effect k).trace • stateMatrix (ρ k))) =
        2 * (1 - born p (M.effect j)) := by
  classical
  obtain ⟨hX, hY, hXtr, hYtr, hsplit⟩ := state_sub_outcomeMixture M ρ p j
  let X := (1 - born p (M.effect j)) • stateMatrix (ρ j)
  let Y := ∑ k ∈ Finset.univ.erase j, born p (M.effect k) • stateMatrix (ρ k)
  have hXY : X * Y = 0 := by
    change X * (∑ k ∈ Finset.univ.erase j, born p (M.effect k) • stateMatrix (ρ k)) = 0
    rw [Matrix.mul_sum]
    apply Finset.sum_eq_zero
    intro k hk
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    change ((1 - born p (M.effect j)) • stateMatrix (ρ j)) *
      (born p (M.effect k) • stateMatrix (ρ k)) = 0
    rw [Matrix.smul_mul, Matrix.mul_smul, horth k hkj.symm, smul_zero, smul_zero]
  rw [hsplit, traceNorm_sub_orthogonal X Y hX hY hXY, hXtr, hYtr]
  ring

/-- Uniform in the probe, with the actual prior and output relative entropy. -/
theorem traceNorm_recovery_le (e : Ensemble ι a) (Φ : MatrixMap a b ℂ)
    (hΦ : Φ.IsPositive) (hTP : Φ.IsTracePreserving) (j₀ j : ι) :
    let out := e.map Φ hΦ hTP
    traceNorm (stateMatrix (e.state j) -
      stateMatrix ((recoveryChannel e Φ hΦ hTP j₀).mapState (out.state j))) ≤
      2 * (1 - e.weight j * Real.exp
        (finiteTraceLogRelativeEntropy (out.state j) out.reference)) := by
  dsimp only
  rw [recoveryChannel_mapState_matrix]
  have herror := traceNorm_outcomeMixture_bound ((e.map Φ hΦ hTP).pgm j₀) e.state
    ((e.map Φ hΦ hTP).state j) j
  have hsuccess := pgm_success (e.map Φ hΦ hTP) j₀ j
  exact herror.trans (mul_le_mul_of_nonneg_left (sub_le_sub_left hsuccess 1) (by norm_num))

/-- Orthogonal source supports make the trace-norm error exactly twice the
failure probability of the same completed measurement. -/
theorem traceNorm_recovery_eq_two_failure (e : Ensemble ι a) (Φ : MatrixMap a b ℂ)
    (hΦ : Φ.IsPositive) (hTP : Φ.IsTracePreserving) (j₀ j : ι)
    (horth : ∀ k, j ≠ k → stateMatrix (e.state j) * stateMatrix (e.state k) = 0) :
    let out := e.map Φ hΦ hTP
    traceNorm (stateMatrix (e.state j) -
      stateMatrix ((recoveryChannel e Φ hΦ hTP j₀).mapState (out.state j))) =
      2 * (1 - born (out.state j) ((out.pgm j₀).effect j)) := by
  dsimp only
  rw [recoveryChannel_mapState_matrix]
  exact traceNorm_outcomeMixture_orthogonal ((e.map Φ hΦ hTP).pgm j₀) e.state
    ((e.map Φ hΦ hTP).state j) j horth

/-- For a commuting projective postselection, the entropy loss is the input
Umegaki divergence minus the retained divergence. All priors and states belong
to the same ensemble whose average is the reference. -/
theorem traceNorm_recovery_postselection (e : Ensemble ι a) (Φ : MatrixMap a b ℂ)
    (hΦ : Φ.IsPositive) (hTP : Φ.IsTracePreserving) (j₀ : ι)
    (P : ι → Matrix a a ℂ) (hP : ∀ j, IsStarProjection (P j))
    (hComm : ∀ j, Commute (stateMatrix e.reference) (P j))
    (hOrth : ∀ j k, j ≠ k → P j * P k = 0)
    (hState : ∀ j, stateMatrix (e.state j) =
      (e.weight j)⁻¹ • (stateMatrix e.reference * P j)) (j : ι) :
    let out := e.map Φ hΦ hTP
    let Δ := finiteTraceLogRelativeEntropy (e.state j) e.reference -
      finiteTraceLogRelativeEntropy (out.state j) out.reference
    let err := traceNorm (stateMatrix (e.state j) -
      stateMatrix ((recoveryChannel e Φ hΦ hTP j₀).mapState (out.state j)))
    err = 2 * (1 - born (out.state j) ((out.pgm j₀).effect j)) ∧
      err ≤ 2 * (1 - Real.exp (-Δ)) := by
  dsimp only
  have horth (k : ι) (hjk : j ≠ k) :
      stateMatrix (e.state j) * stateMatrix (e.state k) = 0 := by
    let S := stateMatrix e.reference
    have hPS : P j * S = S * P j := (hComm j).symm.eq
    have hz : (S * P j) * (S * P k) = 0 := by
      calc
        _ = S * (P j * S) * P k := by simp only [Matrix.mul_assoc]
        _ = S * S * (P j * P k) := by
          rw [hPS]
          simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hOrth j k hjk, Matrix.mul_zero]
    rw [hState j, hState k, Matrix.smul_mul, Matrix.mul_smul, hz, smul_zero, smul_zero]
  refine ⟨traceNorm_recovery_eq_two_failure e Φ hΦ hTP j₀ j horth, ?_⟩
  have hinput := finiteTraceLogRelativeEntropy_of_postselection (e.state j) e.reference
    (hComm j) (hP j).isIdempotentElem (e.weight_pos j) (hState j)
  rw [hinput, neg_sub, sub_neg_eq_add, Real.exp_add, Real.exp_log (e.weight_pos j),
    mul_comm (Real.exp _)]
  exact traceNorm_recovery_le e Φ hΦ hTP j₀ j

end PetzCommonEnsembleRecovery

