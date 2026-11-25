/- GID: D5/S3/Quantum/Measurement/Auric/CoordinatePinchingEntropy
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/CoordinatePinchingEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual coarse phase pinching gains H(q), with finite support-aware divergence and a common environment marginal. -/

import D5.S3.Quantum.Measurement.Auric.CoordinatePinching
import D5.S3.Quantum.Information.OrthogonalRecordEntropy
import D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
import D5.S3.Quantum.Decoherence.RecordingIsometry

/-! Entropy and actual record marginals for pure phase signals under a coarse coordinate PVM. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Matrix
open Matrix JointRecordDecoding
open D5.S3.Entropy.MaxEntropy
open D5.S3.Quantum.Measurement.Auric.CoordinatePinching
open D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.OrthogonalRecordEntropy
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Decoherence.RecordingIsometry
open D5.S3.Quantum.Information.PartialTraceMutualInformation

namespace D5.S3.Quantum.Measurement.Auric.CoordinatePinchingEntropy

variable {ι : Type*} [Fintype ι] {k : ℕ}

def fiber (c : ι → Fin k) (b : Fin k) : Finset ι :=
  Finset.univ.filter fun i => c i = b

def blockWeight (c : ι → Fin k) (t : ι → ℝ) (b : Fin k) : ℝ :=
  ∑ i ∈ fiber c b, t i ^ 2

theorem sum_blockWeight (c : ι → Fin k) (t : ι → ℝ) :
    ∑ b, blockWeight c t b = ∑ i, t i ^ 2 := by
  simp only [blockWeight, fiber, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

variable [DecidableEq ι]

section Pinching

local instance : NonnegSpectrumClass ℝ (CStarMatrix ι ι ℂ) :=
  NonnegSpectrumClass.of_spectrum_nonneg fun A hA x hx => by
    change x ∈ spectrum ℝ (CStarMatrix.ofMatrix.symm A) at hx
    exact spectrum_nonneg_of_nonneg
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm hA) hx

local instance : ContinuousFunctionalCalculus ℝ (CStarMatrix ι ι ℂ) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

omit [DecidableEq ι] in
theorem blockWeight_nonneg (c : ι → Fin k) (t : ι → ℝ) (b : Fin k) :
    0 ≤ blockWeight c t b := Finset.sum_nonneg fun i _ => sq_nonneg (t i)

omit [DecidableEq ι] in
private theorem phase_self_dot (u : ι → ι → ℂ) (s : ι → ℝ)
    (hu : ∀ j i, ‖u j i‖ = 1) (j : ι) :
    star (phaseVector u s j) ⬝ᵥ phaseVector u s j = ((∑ i, s i ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (starRingEnd ℂ) _ * _ = _
  rw [Complex.normSq_eq_conj_mul_self.symm, Complex.normSq_eq_norm_sq]
  simp [phaseVector, hu]

omit [DecidableEq ι] in
private theorem masked_sq (c : ι → Fin k) (t : ι → ℝ) (b : Fin k) :
    ∑ i, (maskedProfile c t b i) ^ 2 = blockWeight c t b := by
  rw [blockWeight, fiber, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : c i = b <;> simp [maskedProfile, hi]

omit [DecidableEq ι] in
private theorem masked_zero (c : ι → Fin k) (t : ι → ℝ) (b : Fin k)
    (h : blockWeight c t b = 0) : maskedProfile c t b = 0 := by
  rw [← masked_sq c t b] at h
  funext i
  exact ((Finset.sum_sq_eq_zero_iff _ _).mp h) i (Finset.mem_univ i)

private theorem pure_projection (v : ι → ℂ) (hv : star v ⬝ᵥ v = 1) :
    IsIdempotentElem (pureState v hv).1 := by
  change rankOneDensity v * rankOneDensity v = rankOneDensity v
  rw [rankOneDensity, vecMulVec_mul_vecMulVec, hv, one_smul]

theorem pure_entropy (v : ι → ℂ) (hv : star v ⬝ᵥ v = 1) :
    vonNeumannEntropy (pureState v hv) = 0 := by
  rw [entropy_eq_trace_cfc]
  have hid := pure_projection v hv
  have hz : cfc Real.negMulLog (pureState v hv).1 = 0 := by
    calc
      _ = cfc (0 : ℝ → ℝ) (pureState v hv).1 := by
        apply cfc_congr
        intro x hx
        have hem := (isIdempotentElem_iff_spectrum_subset ℝ (pureState v hv).1
          (IsSelfAdjoint.of_nonneg (pureState v hv).2.1)).mp hid hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hem
        rcases hem with rfl | rfl <;> simp
      _ = 0 := cfc_zero ℝ (pureState v hv).1
  rw [hz]
  change (Matrix.trace (0 : Matrix ι ι ℂ)).re = 0
  simp

variable (c : ι → Fin k) (u : ι → ι → ℂ) (t : ι → ℝ)

abbrev PositiveBlock := {b : Fin k // 0 < blockWeight c t b}

def normalizedBlockProfile (b : PositiveBlock c t) (i : ι) : ℝ :=
  (Real.sqrt (blockWeight c t b))⁻¹ * maskedProfile c t b i

omit [DecidableEq ι] in
private theorem normalized_sq_sum (b : PositiveBlock c t) :
    ∑ i, (normalizedBlockProfile c t b i) ^ 2 = 1 := by
  simp only [normalizedBlockProfile, mul_pow, ← Finset.mul_sum, masked_sq, inv_pow,
    Real.sq_sqrt b.2.le]
  exact inv_mul_cancel₀ b.2.ne'

variable (hu : ∀ j i, ‖u j i‖ = 1)

def normalizedBlockState (b : PositiveBlock c t) (j : ι) : DensityState ι :=
  pureState (phaseVector u (normalizedBlockProfile c t b) j)
    (phaseVector_norm u _ hu (normalized_sq_sum c t b) j)

private theorem block_state_orthogonal (j : ι) :
    Pairwise fun b d : PositiveBlock c t =>
      (normalizedBlockState c u t hu b j).1 * (normalizedBlockState c u t hu d j).1 = 0 := by
  intro b d hbd
  change rankOneDensity (phaseVector u (normalizedBlockProfile c t b) j) *
    rankOneDensity (phaseVector u (normalizedBlockProfile c t d) j) = 0
  have hdot : star (phaseVector u (normalizedBlockProfile c t b) j) ⬝ᵥ
      phaseVector u (normalizedBlockProfile c t d) j = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have h : (b : Fin k) ≠ (d : Fin k) := fun he => hbd (Subtype.ext he)
    by_cases hi : c i = (b : Fin k)
    · have hd : c i ≠ (d : Fin k) := hi.trans_ne h
      simp [phaseVector, normalizedBlockProfile, maskedProfile, hd]
    · simp [phaseVector, normalizedBlockProfile, maskedProfile, hi]
  rw [rankOneDensity, rankOneDensity, vecMulVec_mul_vecMulVec, hdot, zero_smul]
  ext i l
  simp

private theorem weighted_block_matrix (b : PositiveBlock c t) (j : ι) :
    blockWeight c t b • CStarMatrix.ofMatrix.symm (normalizedBlockState c u t hu b j).1 =
      rankOneDensity (phaseVector u (maskedProfile c t b) j) := by
  rw [normalizedBlockState, pureState_matrix]
  have fac : blockWeight c t b * ((Real.sqrt (blockWeight c t b))⁻¹) ^ 2 = 1 := by
    rw [inv_pow, Real.sq_sqrt b.2.le, mul_inv_cancel₀ b.2.ne']
  ext i l
  simp only [Matrix.smul_apply, Complex.real_smul, rankOneDensity, vecMulVec_apply, Pi.star_apply,
    phaseVector, normalizedBlockProfile, Complex.ofReal_mul, star_mul, Complex.star_def,
    Complex.conj_ofReal]
  have facC : (blockWeight c t b : ℂ) * (↑((Real.sqrt (blockWeight c t b))⁻¹) : ℂ) ^ 2 = 1 := by
    exact_mod_cast fac
  linear_combination (↑(maskedProfile c t b i) * u j i *
    (↑(maskedProfile c t b l) * (starRingEnd ℂ) (u j l))) * facC

omit [DecidableEq ι] in
private theorem sum_positive_blocks {M : Type*} [AddCommMonoid M] (f : Fin k → M)
    (hf : ∀ b, blockWeight c t b = 0 → f b = 0) :
    ∑ b : PositiveBlock c t, f b = ∑ b, f b := by
  classical
  let s : Finset (Fin k) := Finset.univ.filter fun b => 0 < blockWeight c t b
  have hs : ∀ b, b ∈ s ↔ 0 < blockWeight c t b := by simp [s]
  rw [← Finset.sum_subtype s hs f]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro b _ hb
  apply hf b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hb
  exact le_antisymm hb (blockWeight_nonneg c t b)

variable (hnorm : ∑ i, t i ^ 2 = 1)

omit [DecidableEq ι] in
include hnorm in
private theorem positive_weights_sum :
    ∑ b : PositiveBlock c t, blockWeight c t b = 1 := by
  rw [sum_positive_blocks c t _ (fun _ h => h), sum_blockWeight, hnorm]

theorem pinchedPhaseStates_eq_mixture (j : ι) :
    pinchedPhaseStates c u t hu hnorm j =
      mixtureState (fun b : PositiveBlock c t => blockWeight c t b)
        (fun b => b.2.le) (positive_weights_sum c t hnorm)
        (fun b => normalizedBlockState c u t hu b j) := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  rw [pinchedPhaseStates_matrix]
  change _ = ∑ b : PositiveBlock c t,
    blockWeight c t b • CStarMatrix.ofMatrix.symm (normalizedBlockState c u t hu b j).1
  simp_rw [weighted_block_matrix]
  symm
  refine sum_positive_blocks c t
    (fun b => rankOneDensity (phaseVector u (maskedProfile c t b) j)) ?_
  intro b hb
  rw [masked_zero c t b hb]
  ext i l
  simp [rankOneDensity, vecMulVec_apply, phaseVector]

/-- Natural entropy gain of the actual AURIC nonselective coordinate measurement. -/
theorem phase_pinching_entropy_gain (j : ι) :
    vonNeumannEntropy (pinchedPhaseStates c u t hu hnorm j) -
      vonNeumannEntropy (pureState (phaseVector u t j)
        (phaseVector_norm u t hu hnorm j)) = shannonEntropy (blockWeight c t) := by
  rw [pure_entropy, sub_zero, pinchedPhaseStates_eq_mixture c u t hu hnorm j,
    orthogonal_mixture_entropy _ _ _ _ (block_state_orthogonal c u t hu j)]
  simp only [normalizedBlockState, pure_entropy, mul_zero, Finset.sum_const_zero, add_zero]
  unfold shannonEntropy
  exact sum_positive_blocks c t (fun b => Real.negMulLog (blockWeight c t b))
    (fun b hb => by simp [hb])

private theorem finite_matrix_spectrum (A : CStarMatrix ι ι ℂ) :
    (spectrum ℝ A).Finite :=
  (CStarMatrix.ofMatrix.symm A).finite_real_spectrum

private theorem log_add_orthogonal {A B : CStarMatrix ι ι ℂ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : A * B = 0) :
    CFC.log (A + B) = CFC.log A + CFC.log B := by
  have hD : IsSelfAdjoint (A - B) :=
    (IsSelfAdjoint.of_nonneg hA).sub (IsSelfAdjoint.of_nonneg hB)
  obtain ⟨ha, hb⟩ := CFC.posPart_negPart_unique (a := A - B) rfl hAB hA hB
  rw [CFC.posPart_def, cfcₙ_eq_cfc (by fun_prop) (by simp)] at ha
  rw [CFC.negPart_def, cfcₙ_eq_cfc (by fun_prop) (by simp)] at hb
  have hsum : cfc (fun x : ℝ => x⁺ + x⁻) (A - B) = A + B := by
    rw [cfc_add (A - B) (fun x : ℝ => x⁺) (fun x : ℝ => x⁻), ha, hb]
  have hfin (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ (A - B)) := by
    exact (finite_matrix_spectrum (A - B)).continuousOn f
  unfold CFC.log
  calc
    _ = cfc (fun x : ℝ => Real.log (x⁺ + x⁻)) (A - B) := by
      rw [cfc_comp' Real.log (fun x : ℝ => x⁺ + x⁻) (A - B) (((finite_matrix_spectrum (A - B)).image _).continuousOn _), hsum]
    _ = cfc (fun x : ℝ => Real.log x⁺ + Real.log x⁻) (A - B) := by
      apply cfc_congr
      intro x _
      rcases le_total 0 x with hx | hx
      · simp [posPart_eq_self.mpr hx, negPart_eq_zero.mpr hx]
      · simp [posPart_eq_zero.mpr hx, negPart_eq_neg.mpr hx]
    _ = _ := by
      rw [cfc_add (A - B) (fun x : ℝ => Real.log x⁺) (fun x : ℝ => Real.log x⁻)
        (hfin _) (hfin _),
        cfc_comp' Real.log (fun x : ℝ => x⁺) (A - B) (((finite_matrix_spectrum (A - B)).image _).continuousOn _),
        cfc_comp' Real.log (fun x : ℝ => x⁻) (A - B) (((finite_matrix_spectrum (A - B)).image _).continuousOn _), ha, hb]

private theorem log_sum_orthogonal {B : Type*} [DecidableEq B]
    (s : Finset B) (A : B → CStarMatrix ι ι ℂ) (hA : ∀ i ∈ s, 0 ≤ A i)
    (ho : (s : Set B).Pairwise (fun i j => A i * A j = 0)) :
    CFC.log (∑ i ∈ s, A i) = ∑ i ∈ s, CFC.log (A i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    rw [log_add_orthogonal (hA i (by simp)) (Finset.sum_nonneg (fun j hj => hA j (by simp [hj])))]
    · exact congrArg (CFC.log (A i) + ·)
        (ih (fun j hj => hA j (by simp [hj])) (ho.mono (Finset.subset_insert i s)))
    · rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun j hj => ho (by simp) (by simp [hj])
        (by intro hij; subst j; exact hi hj)

private theorem log_smul_projection (r : ℝ) (P : CStarMatrix ι ι ℂ)
    (hP : IsSelfAdjoint P) (hi : IsIdempotentElem P) :
    CFC.log (r • P) = Real.log r • P := by
  unfold CFC.log
  rw [← cfc_comp_const_mul r Real.log P
    (hf := ((finite_matrix_spectrum P).image _).continuousOn _) (ha := hP)]
  calc
    _ = cfc (fun x : ℝ => Real.log r * x) P := by
      apply cfc_congr
      intro x hx
      have hem := (isIdempotentElem_iff_spectrum_subset ℝ P hP).mp hi hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hem
      rcases hem with rfl | rfl <;> simp
    _ = _ := by
      rw [cfc_const_mul (Real.log r) (fun x : ℝ => x) P, cfc_id' ℝ P]

/-- The finite-spectrum logarithm acts with eigenvalue `log q_b` on each
nonzero normalized record. It vanishes on the complementary kernel. -/
theorem pinchedPhaseStates_log (j : ι) :
    CFC.log (pinchedPhaseStates c u t hu hnorm j).1 =
      ∑ b : PositiveBlock c t, Real.log (blockWeight c t b) •
        (normalizedBlockState c u t hu b j).1 := by
  classical
  rw [pinchedPhaseStates_eq_mixture c u t hu hnorm j]
  let A (b : PositiveBlock c t) := blockWeight c t b • (normalizedBlockState c u t hu b j).1
  change CFC.log (∑ b, A b) = _
  rw [log_sum_orthogonal Finset.univ A (fun b _ =>
    smul_nonneg b.2.le (normalizedBlockState c u t hu b j).2.1)]
  · apply Finset.sum_congr rfl
    intro b _
    exact log_smul_projection _ _ (IsSelfAdjoint.of_nonneg (normalizedBlockState c u t hu b j).2.1)
      (pure_projection _ _)
  · intro b _ d _ hbd
    dsimp only [A]
    rw [smul_mul_assoc, mul_smul_comm, block_state_orthogonal c u t hu j hbd, smul_zero, smul_zero]

private theorem compress_matrix (j : ι) (b : Fin k) :
    (coordinatePVM c).proj b * rankOneDensity (phaseVector u t j) *
      (coordinatePVM c).proj b = rankOneDensity (phaseVector u (maskedProfile c t b) j) := by
  ext i l
  by_cases hi : c i = b <;> by_cases hl : c l = b <;>
    simp [coordinatePVM, mul_diagonal, diagonal_mul, rankOneDensity, vecMulVec_apply, Pi.star_apply,
      phaseVector, maskedProfile, hi, hl]

private theorem sum_compressions (j : ι) :
    CStarMatrix.ofMatrix.symm (pinchedPhaseStates c u t hu hnorm j).1 =
      ∑ b, (coordinatePVM c).proj b * rankOneDensity (phaseVector u t j) *
        (coordinatePVM c).proj b := by
  rw [pinchedPhaseStates_matrix]
  simp_rw [compress_matrix c u t j]

/-- Pinching retains the support of every pure phase input, including singular outputs. -/
theorem phase_supportContained (j : ι) :
    SupportContained (pureState (phaseVector u t j) (phaseVector_norm u t hu hnorm j))
      (pinchedPhaseStates c u t hu hnorm j) := by
  intro x hx
  let v := phaseVector u t j
  let w (b : Fin k) := phaseVector u (maskedProfile c t b) j
  change CStarMatrix.ofMatrix.symm (pinchedPhaseStates c u t hu hnorm j).1 *ᵥ x = 0 at hx
  rw [pinchedPhaseStates_matrix, Matrix.sum_mulVec] at hx
  change (∑ b, rankOneDensity (w b) *ᵥ x) = 0 at hx
  have hdot := congrArg (fun y => star x ⬝ᵥ y) hx
  simp only [dotProduct_sum, dotProduct_zero, rankOneDensity, vecMulVec_mulVec] at hdot
  have hconj (b : Fin k) : star (star (w b) ⬝ᵥ x) = star x ⬝ᵥ w b := by
    simp [dotProduct, Pi.star_apply, mul_comm]
  have hreal : ∑ b, ‖star (w b) ⬝ᵥ x‖ ^ 2 = 0 := by
    have hterm (b : Fin k) :
        star x ⬝ᵥ (MulOpposite.op (star (w b) ⬝ᵥ x) • w b) =
          (‖star (w b) ⬝ᵥ x‖ ^ 2 : ℝ) := by
      rw [dotProduct_smul]
      change (star x ⬝ᵥ w b) * (star (w b) ⬝ᵥ x) = _
      rw [← hconj]
      change (starRingEnd ℂ) _ * _ = _
      rw [Complex.normSq_eq_conj_mul_self.symm, Complex.normSq_eq_norm_sq]
    simp_rw [hterm, ← Complex.ofReal_sum] at hdot
    exact_mod_cast hdot
  have hw (b : Fin k) : star (w b) ⬝ᵥ x = 0 := by
    have hz := ((Finset.sum_sq_eq_zero_iff _ _).mp hreal) b (Finset.mem_univ b)
    exact norm_eq_zero.mp hz
  have hv : v = ∑ b, w b := by
    funext i
    simp [v, w, Finset.sum_apply, phaseVector, maskedProfile, apply_ite]
  have hzero : star v ⬝ᵥ x = 0 := by
    rw [hv, star_sum, sum_dotProduct]
    simp [hw]
  change rankOneDensity v *ᵥ x = 0
  rw [rankOneDensity, vecMulVec_mulVec, hzero]
  simp

private theorem cross_trace_eq (j : ι) :
    let ρ := pureState (phaseVector u t j) (phaseVector_norm u t hu hnorm j)
    let σ := pinchedPhaseStates c u t hu hnorm j
    Matrix.trace (ρ.1 * CFC.log σ.1) = Matrix.trace (σ.1 * CFC.log σ.1) := by
  dsimp only
  let σ := pinchedPhaseStates c u t hu hnorm j
  let L := CStarMatrix.ofMatrix.symm (CFC.log σ.1)
  let X := rankOneDensity (phaseVector u t j)
  let p := coordinatePVM c
  have pp (b d : Fin k) : p.proj b * p.proj d = if b = d then p.proj b else 0 := by
    by_cases h : b = d
    · subst d
      simp [p.idempotent]
    · simp [h, p.orthogonal b d h]
  have hL (b : Fin k) : L * p.proj b = p.proj b * L := by
    change CStarMatrix.ofMatrix.symm (CFC.log σ.1) * p.proj b =
      p.proj b * CStarMatrix.ofMatrix.symm (CFC.log σ.1)
    rw [pinchedPhaseStates_log c u t hu hnorm j]
    change (∑ d : PositiveBlock c t, Real.log (blockWeight c t d) •
      CStarMatrix.ofMatrix.symm (normalizedBlockState c u t hu d j).1) * p.proj b =
      p.proj b * (∑ d : PositiveBlock c t, Real.log (blockWeight c t d) •
        CStarMatrix.ofMatrix.symm (normalizedBlockState c u t hu d j).1)
    rw [Matrix.sum_mul, Matrix.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    let R := CStarMatrix.ofMatrix.symm (normalizedBlockState c u t hu d j).1
    have hweighted : (blockWeight c t d • R) * p.proj b =
        p.proj b * (blockWeight c t d • R) := by
      rw [weighted_block_matrix c u t hu d j, ← compress_matrix c u t j]
      change p.proj d * X * p.proj d * p.proj b = p.proj b * (p.proj d * X * p.proj d)
      rw [Matrix.mul_assoc (p.proj d * X), ← Matrix.mul_assoc (p.proj b),
        ← Matrix.mul_assoc (p.proj b) (p.proj d), pp d b, pp b d]
      by_cases h : (d : Fin k) = b
      · rw [h]
        simp
      · simp [h, Ne.symm h]
    have hR : R * p.proj b = p.proj b * R := by
      have h := congrArg (fun A : Matrix ι ι ℂ => (blockWeight c t d)⁻¹ • A) hweighted
      simpa only [smul_mul_assoc, mul_smul_comm, smul_smul, inv_mul_cancel₀ d.2.ne',
        one_smul] using h
    rw [smul_mul_assoc, mul_smul_comm]
    exact congrArg (Real.log (blockWeight c t d) • ·) hR
  change Matrix.trace (X * L) = Matrix.trace (CStarMatrix.ofMatrix.symm σ.1 * L)
  rw [sum_compressions c u t hu hnorm j, Matrix.sum_mul, Matrix.trace_sum]
  calc
    _ = ∑ b, Matrix.trace (X * (p.proj b * L)) := by
      rw [← Matrix.trace_sum, ← Matrix.mul_sum, ← Matrix.sum_mul, p.complete, one_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      change trace (X * (p.proj b * L)) = trace (p.proj b * X * p.proj b * L)
      rw [Matrix.mul_assoc (p.proj b * X), Matrix.trace_mul_cycle,
        ← hL b, Matrix.mul_assoc L, p.idempotent, trace_mul_comm]

/-- The actual support-aware Umegaki divergence equals the natural entropy gained. -/
theorem phase_pinching_relative_entropy (j : ι) :
    extendedQuantumRelativeEntropy
      (pureState (phaseVector u t j) (phaseVector_norm u t hu hnorm j))
      (pinchedPhaseStates c u t hu hnorm j) =
    (shannonEntropy (blockWeight c t) : WithTop ℝ) := by
  rw [extendedQuantumRelativeEntropy_eq_coe_of_support (phase_supportContained c u t hu hnorm j)]
  congr 1
  change D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition.quantumRelativeEntropy _ _ = _
  rw [quantum_relative_entropy_eq_neg_entropy_sub_cross, cross_trace_eq c u t hu hnorm j]
  have he := phase_pinching_entropy_gain c u t hu hnorm j
  unfold vonNeumannEntropy at he ⊢
  linarith

/-- The same coordinate recording isometry supplies both output registers. -/
def coordinateRecording : Matrix (ι × Fin k) ι ℂ :=
  fun x i => (coordinatePVM c).proj x.2 x.1 i

private theorem recording_laws :
    (coordinateRecording c)ᴴ * coordinateRecording c = 1 ∧
      ∀ (ρ : Matrix ι ι ℂ) (b d : Fin k) (i l : ι),
        (coordinateRecording c * ρ * (coordinateRecording c)ᴴ) (i, b) (l, d) =
          ((coordinatePVM c).proj b * ρ * (coordinatePVM c).proj d) i l := by
  apply recording_isometry_and_state_blocks (coordinatePVM c).proj
    (fun b => ((coordinatePVM c).hermitian b).eq) _ (coordinatePVM c).complete
  intro b d
  by_cases h : b = d
  · subst d
    simp [(coordinatePVM c).idempotent]
  · simp [h, (coordinatePVM c).orthogonal b d h]

private theorem recorded_vec_apply (v : ι → ℂ) (i : ι) (b : Fin k) :
    (coordinateRecording c *ᵥ v) (i, b) = if c i = b then v i else 0 := by
  change ((coordinatePVM c).proj b *ᵥ v) i = _
  rw [coordinatePVM, mulVec_diagonal]
  split_ifs <;> simp

private theorem record_norm (v : ι → ℂ) (hv : star v ⬝ᵥ v = 1) :
    star (coordinateRecording c *ᵥ v) ⬝ᵥ (coordinateRecording c *ᵥ v) = 1 := by
  rw [← hv]
  simp only [dotProduct, Pi.star_apply, Fintype.sum_prod_type, recorded_vec_apply]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∑ b, if c i = b then star (v i) * v i else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hi : c i = b <;> simp [hi]
    _ = _ := by simp

/-- The joint copy of a phase signal is the pure state of the isometrically lifted vector. -/
def copiedPhaseState (j : ι) : DensityState (ι × Fin k) :=
  pureState (coordinateRecording c *ᵥ phaseVector u t j)
    (record_norm c _ (phaseVector_norm u t hu hnorm j))

private theorem copiedPhaseState_matrix (j : ι) :
    CStarMatrix.ofMatrix.symm (copiedPhaseState c u t hu hnorm j).1 =
      coordinateRecording c * rankOneDensity (phaseVector u t j) * (coordinateRecording c)ᴴ := by
  rw [copiedPhaseState, pureState_matrix]
  simp only [rankOneDensity, mul_vecMulVec, vecMulVec_mul]
  change vecMulVec _ _ = vecMulVec _ _
  congr 1
  ext x
  simp [vecMul, mulVec, dotProduct, Pi.star_apply, conjTranspose_apply, star_mul, mul_comm]

/-- The pure recording has residual marginal equal to the actual pinching and
environmental marginal equal to the same block law for every phase label. -/
theorem copiedPhaseState_marginals (j : ι) :
    (coordinateRecording c)ᴴ * coordinateRecording c = 1 ∧
      marginalRight (copiedPhaseState c u t hu hnorm j) =
        pinchedPhaseStates c u t hu hnorm j ∧
      CStarMatrix.ofMatrix.symm (marginalLeft (copiedPhaseState c u t hu hnorm j)).1 =
        diagonal (fun b => (blockWeight c t b : ℂ)) := by
  refine ⟨(recording_laws c).1, ?_, ?_⟩
  · apply Subtype.ext
    apply CStarMatrix.ofMatrix.symm.injective
    change partialTraceRight (CStarMatrix.ofMatrix.symm
      (copiedPhaseState c u t hu hnorm j).1) = _
    rw [copiedPhaseState_matrix, sum_compressions c u t hu hnorm j]
    ext i l
    simp only [partialTraceRight, Matrix.sum_apply]
    change (∑ b, (coordinateRecording c * rankOneDensity (phaseVector u t j) *
      (coordinateRecording c)ᴴ) (i, b) (l, b)) =
      ∑ b, ((coordinatePVM c).proj b * rankOneDensity (phaseVector u t j) *
        (coordinatePVM c).proj b) i l
    exact Finset.sum_congr rfl fun b _ => (recording_laws c).2 _ b b i l
  · ext b d
    change (∑ i, rankOneDensity (coordinateRecording c *ᵥ phaseVector u t j) (i, b) (i, d)) =
      diagonal (fun b => (blockWeight c t b : ℂ)) b d
    by_cases hbd : b = d
    · subst d
      rw [diagonal_apply_eq, ← masked_sq c t b, ← phase_self_dot u _ hu j]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : c i = b <;>
        simp [rankOneDensity, vecMulVec_apply, Pi.star_apply, recorded_vec_apply,
          phaseVector, maskedProfile, hi, mul_comm]
    · rw [diagonal_apply_ne _ hbd]
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : c i = b
      · simp [rankOneDensity, vecMulVec_apply, Pi.star_apply, recorded_vec_apply, hi, hbd]
      · simp [rankOneDensity, vecMulVec_apply, Pi.star_apply, recorded_vec_apply, hi]

/-- The copied environment has zero Holevo information for any prior on the phase labels. -/
theorem copied_environment_holevo_zero (p : ι → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hs : ∑ j, p j = 1) :
    let E := fun j => marginalLeft (copiedPhaseState c u t hu hnorm j)
    vonNeumannEntropy (mixtureState p hp hs E) -
      ∑ j, p j * vonNeumannEntropy (E j) = 0 := by
  dsimp only
  let E := fun j => marginalLeft (copiedPhaseState c u t hu hnorm j)
  have hE (i j : ι) : E i = E j := by
    apply Subtype.ext
    apply CStarMatrix.ofMatrix.symm.injective
    rw [(copiedPhaseState_marginals c u t hu hnorm i).2.2,
      (copiedPhaseState_marginals c u t hu hnorm j).2.2]
  have hι : Nonempty ι := by
    by_contra h
    let : IsEmpty ι := not_nonempty_iff.mp h
    simp at hnorm
  let j : ι := Classical.choice hι
  have hm : mixtureState p hp hs E = E j := by
    apply Subtype.ext
    change (∑ i, p i • (E i).1) = (E j).1
    simp_rw [fun i => hE i j]
    rw [← Finset.sum_smul, hs, one_smul]
  change vonNeumannEntropy (mixtureState p hp hs E) - ∑ i, p i * vonNeumannEntropy (E i) = 0
  rw [hm]
  simp_rw [fun i => hE i j]
  rw [← Finset.sum_mul, hs, one_mul, sub_self]

end Pinching

section ClassicalRecord

private def liftedProfile (c : ι → Fin k) (t : ι → ℝ) (x : ι × Fin k) : ℝ :=
  maskedProfile c t x.2 x.1

private def liftedPhases (u : ι → ι → ℂ) (j x : ι × Fin k) : ℂ := u j.1 x.1

omit [DecidableEq ι] in
private theorem lifted_profile_norm (c : ι → Fin k) (t : ι → ℝ)
    (hnorm : ∑ i, t i ^ 2 = 1) : ∑ x, liftedProfile c t x ^ 2 = 1 := by
  rw [Fintype.sum_prod_type, ← hnorm]
  simp [liftedProfile, maskedProfile]

omit [DecidableEq ι] in
private theorem lifted_block_weight (c : ι → Fin k) (t : ι → ℝ) :
    blockWeight Prod.snd (liftedProfile c t) = blockWeight c t := by
  funext b
  simp only [blockWeight, fiber, Finset.sum_filter, Fintype.sum_prod_type,
    liftedProfile, maskedProfile]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_ite_eq']
  split_ifs <;> simp

variable (c : ι → Fin k) (u : ι → ι → ℂ) (t : ι → ℝ)
  (hu : ∀ j i, ‖u j i‖ = 1) (hnorm : ∑ i, t i ^ 2 = 1)

/-- Dephase the outcome register of the coherent copy, keeping its residual register. -/
def classicalPhaseRecord (j : ι) : DensityState (ι × Fin k) :=
  (pinchingChannel (coordinatePVM (Prod.snd : ι × Fin k → Fin k))).mapState
    (copiedPhaseState c u t hu hnorm j)

private theorem lifted_phase_pinching (j : ι) (b : Fin k) :
    classicalPhaseRecord c u t hu hnorm j =
      pinchedPhaseStates Prod.snd (liftedPhases u) (liftedProfile c t)
        (fun x y => hu x.1 y.1) (lifted_profile_norm c t hnorm) (j, b) := by
  unfold classicalPhaseRecord pinchedPhaseStates
  congr 1
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  rw [copiedPhaseState, pureState_matrix, pureState_matrix]
  congr 1
  funext x
  change ((coordinatePVM c).proj x.2 *ᵥ phaseVector u t j) x.1 = _
  rw [coordinatePVM, mulVec_diagonal]
  by_cases h : c x.1 = x.2 <;>
    simp [h, phaseVector, liftedProfile, liftedPhases, maskedProfile]

private theorem classicalRecord_entry (j i l : ι) (b d : Fin k) :
    CStarMatrix.ofMatrix.symm (classicalPhaseRecord c u t hu hnorm j).1 (i, b) (l, d) =
      if b = d then rankOneDensity (phaseVector u (maskedProfile c t b) j) i l else 0 := by
  rw [lifted_phase_pinching c u t hu hnorm j b, pinchedPhaseStates_matrix]
  simp only [Matrix.sum_apply, rankOneDensity, vecMulVec_apply, Pi.star_apply]
  by_cases h : b = d
  · subst d
    calc
      _ = ∑ e : Fin k, if b = e then
          phaseVector u (maskedProfile c t b) j i *
            star (phaseVector u (maskedProfile c t b) j l) else 0 := by
        apply Finset.sum_congr rfl
        intro e _
        by_cases h : b = e <;>
          simp [phaseVector, maskedProfile, liftedPhases, liftedProfile, h]
      _ = _ := by simp
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro e _
    by_cases he : b = e
    · subst e
      simp [phaseVector, maskedProfile, Ne.symm h]
    · simp [phaseVector, maskedProfile, he]

/-- The joint diagonal readout law of the classical flag and the residual
coordinate PVM has support on equal outcomes. -/
theorem classicalPhaseRecord_readout (j : ι) (b d : Fin k) :
    (∑ i ∈ fiber c d,
      CStarMatrix.ofMatrix.symm (classicalPhaseRecord c u t hu hnorm j).1 (i, b) (i, b)) =
      if b = d then (blockWeight c t b : ℂ) else 0 := by
  simp only [classicalRecord_entry]
  by_cases h : b = d
  · subst d
    simp only [blockWeight, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hm : c i = b := by simpa [fiber] using hi
    have hnormSq : Complex.normSq (phaseVector u t j i) = t i ^ 2 := by
      simp [Complex.normSq_eq_norm_sq, phaseVector, hu]
    have hunit : star (phaseVector u t j i) * phaseVector u t j i = (t i ^ 2 : ℝ) :=
      Complex.normSq_eq_conj_mul_self.symm.trans (congrArg Complex.ofReal hnormSq)
    simpa [rankOneDensity, vecMulVec_apply, Pi.star_apply, phaseVector, maskedProfile, hm, mul_comm]
      using hunit
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro i hi
    have hm : c i = d := by simpa [fiber] using hi
    simp [rankOneDensity, vecMulVec_apply, Pi.star_apply, phaseVector, maskedProfile, hm, Ne.symm h]

/-- The classical outcome flag has zero conditional entropy given the residual register. -/
theorem classicalPhaseRecord_conditional_entropy (j : ι) :
    vonNeumannEntropy (classicalPhaseRecord c u t hu hnorm j) -
      vonNeumannEntropy (marginalRight (classicalPhaseRecord c u t hu hnorm j)) = 0 := by
  have hs : marginalRight (classicalPhaseRecord c u t hu hnorm j) =
      pinchedPhaseStates c u t hu hnorm j := by
    apply Subtype.ext
    apply CStarMatrix.ofMatrix.symm.injective
    rw [pinchedPhaseStates_matrix]
    ext i l
    change partialTraceRight (CStarMatrix.ofMatrix.symm
      (classicalPhaseRecord c u t hu hnorm j).1) i l = _
    simp only [partialTraceRight, Matrix.sum_apply, classicalRecord_entry, ↓reduceIte]
  have hres := phase_pinching_entropy_gain c u t hu hnorm j
  rw [pure_entropy, sub_zero] at hres
  have hjoint : vonNeumannEntropy (classicalPhaseRecord c u t hu hnorm j) =
      shannonEntropy (blockWeight c t) := by
    let b := c j
    have h := phase_pinching_entropy_gain Prod.snd (liftedPhases u) (liftedProfile c t)
      (fun x y => hu x.1 y.1) (lifted_profile_norm c t hnorm) (j, b)
    rw [pure_entropy, sub_zero, lifted_block_weight] at h
    exact (congrArg vonNeumannEntropy (lifted_phase_pinching c u t hu hnorm j b)).trans h
  rw [hs, hres, hjoint, sub_self]

end ClassicalRecord

end D5.S3.Quantum.Measurement.Auric.CoordinatePinchingEntropy
