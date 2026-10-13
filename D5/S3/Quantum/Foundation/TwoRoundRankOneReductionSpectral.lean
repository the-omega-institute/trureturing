/- GID: D5/S3/Quantum/Foundation/TwoRoundRankOneReductionSpectral
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/TwoRoundRankOneReductionSpectral
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Singular event interval machinery and consumed rank-one spectral mass.
-/

import D5.S3.Quantum.Foundation.TwoRoundRankOneReductionPhase
import Mathlib.Analysis.Matrix.Order
noncomputable section
open Matrix Unitary
open scoped BigOperators ComplexOrder MatrixOrder
namespace D5.S3.Quantum.Foundation.TwoRoundSpectralEvents
open D5.S3.Quantum.Foundation.TwoRoundPhaseAverage
variable {n : Type*} [Fintype n] [DecidableEq n]
def EventInterval (M E : Matrix n n ℂ) : Prop :=
  E.PosSemidef ∧ (M - E).PosSemidef
private def spectralRoot {M : Matrix n n ℂ} (hM : M.PosSemidef) : Matrix n n ℂ :=
  hM.isHermitian.cfc Real.sqrt
private theorem conjugate_pos (U : Matrix.unitaryGroup n ℂ)
    {E : Matrix n n ℂ} (hE : E.PosSemidef) :
    (conjStarAlgAut ℂ _ U E).PosSemidef := by
  rw [conjStarAlgAut_apply]
  exact hE.mul_mul_conjTranspose_same _
omit [Fintype n] in
private theorem diagonal_real_star (d : n → ℝ) :
    (diagonal (fun i => (d i : ℂ)))ᴴ = diagonal (fun i => (d i : ℂ)) := by
  simp [diagonal_conjTranspose]
private theorem spectralRoot_sq {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    spectralRoot hM * spectralRoot hM = M := by
  unfold spectralRoot Matrix.IsHermitian.cfc
  rw [← map_mul, diagonal_mul_diagonal]
  conv_rhs => rw [hM.isHermitian.spectral_theorem]
  congr 2
  funext i
  change (Real.sqrt (hM.isHermitian.eigenvalues i) : ℂ) *
    (Real.sqrt (hM.isHermitian.eigenvalues i) : ℂ) = (hM.isHermitian.eigenvalues i : ℂ)
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hM.eigenvalues_nonneg i)]
private theorem spectralRoot_hermitian {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    (spectralRoot hM).IsHermitian := by
  unfold spectralRoot Matrix.IsHermitian.cfc
  rw [conjStarAlgAut_apply]
  exact isHermitian_mul_mul_conjTranspose _
    (isHermitian_diagonal_iff.mpr (fun i => by
      change IsSelfAdjoint (Real.sqrt (hM.isHermitian.eigenvalues i) : ℂ)
      simp [IsSelfAdjoint]))
private theorem spectralRoot_eq_sqrt {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    spectralRoot hM = CFC.sqrt M := by
  have hpos : (spectralRoot hM).PosSemidef := by
    unfold spectralRoot Matrix.IsHermitian.cfc
    rw [conjStarAlgAut_apply]
    apply PosSemidef.mul_mul_conjTranspose_same
    apply PosSemidef.diagonal
    intro i
    change (0 : ℂ) ≤ (Real.sqrt (hM.isHermitian.eigenvalues i) : ℂ)
    exact_mod_cast Real.sqrt_nonneg (hM.isHermitian.eigenvalues i)
  exact (CFC.sqrt_unique (spectralRoot_sq hM) hpos.nonneg).symm
omit [Fintype n] [DecidableEq n] in
private theorem zero_diag_column [Finite n] {E : Matrix n n ℂ} (hE : E.PosSemidef)
    {i : n} (hi : E i i = 0) (j : n) : E j i = 0 := by
  classical
  let := Fintype.ofFinite n
  have hq : star (Pi.single i (1 : ℂ)) ⬝ᵥ E *ᵥ Pi.single i 1 = 0 := by
    simpa using hi
  have hz := (hE.dotProduct_mulVec_zero_iff _).mp hq
  simpa using congrFun hz j
private theorem diagonal_interval_factorization (d : n → ℝ) (hd : ∀ i, 0 ≤ d i)
    {E : Matrix n n ℂ} (hE : EventInterval (diagonal (fun i => (d i : ℂ))) E) :
    ∃ F : Matrix n n ℂ, EventInterval 1 F ∧
      E = diagonal (fun i => (Real.sqrt (d i) : ℂ)) * F *
        diagonal (fun i => (Real.sqrt (d i) : ℂ)) := by
  let s : n → ℝ := fun i => Real.sqrt (d i)
  let r : n → ℝ := fun i => (s i)⁻¹
  let D : Matrix n n ℂ := diagonal (fun i => (s i : ℂ))
  let J : Matrix n n ℂ := diagonal (fun i => (r i : ℂ))
  let P : Matrix n n ℂ := diagonal (fun i => if d i = 0 then 0 else 1)
  let F := J * E * J
  have hs (i : n) : s i = 0 ↔ d i = 0 := Real.sqrt_eq_zero (hd i)
  have hJ : Jᴴ = J := diagonal_real_star r
  have hF : F.PosSemidef := by
    simpa only [hJ] using hE.1.conjTranspose_mul_mul_same J
  have hzero (i : n) (hi : d i = 0) : E i i = 0 := by
    have h₁ := hE.1.diag_nonneg (i := i)
    have h₂ := hE.2.diag_nonneg (i := i)
    simp only [Matrix.sub_apply, diagonal_apply_eq, hi, Complex.ofReal_zero, zero_sub] at h₂
    exact le_antisymm (neg_nonneg.mp h₂) h₁
  have hcol (i j : n) (hi : d i = 0) : E j i = 0 :=
    zero_diag_column hE.1 (hzero i hi) j
  have hrow (i j : n) (hi : d i = 0) : E i j = 0 := by
    apply star_injective
    simpa only [star_zero] using (hE.1.isHermitian.apply j i).trans (hcol i j hi)
  have hJEJ : J * diagonal (fun i => (d i : ℂ)) * J = P := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [J, P, diagonal_mul_diagonal, diagonal_apply_eq]
      by_cases hi : d i = 0
      · simp [r, s, hi]
      · have hsi : s i ≠ 0 := fun h => hi ((hs i).mp h)
        have hdsi : d i = s i * s i := (Real.mul_self_sqrt (hd i)).symm
        simp only [hi, if_false]
        change (r i : ℂ) * (d i : ℂ) * (r i : ℂ) = 1
        rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
        congr 1
        dsimp [r]
        rw [hdsi]
        field_simp
    · simp [J, P, diagonal_mul_diagonal, hij]
  have hPF : (P - F).PosSemidef := by
    have h := hE.2.conjTranspose_mul_mul_same J
    simpa only [hJ, Matrix.mul_sub, Matrix.sub_mul, hJEJ] using h
  have hIP : (1 - P).PosSemidef := by
    dsimp [P]
    rw [show (1 : Matrix n n ℂ) = diagonal (fun _ => 1) from diagonal_one.symm,
      diagonal_sub]
    apply PosSemidef.diagonal
    intro i
    dsimp
    split_ifs <;> norm_num
  refine ⟨F, ⟨hF, ?_⟩, ?_⟩
  · simpa only [sub_add_sub_cancel] using hIP.add hPF
  · change E = D * F * D
    ext i j
    simp only [D, F, J, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hi : d i = 0
    · simp [s, r, hi, hrow i j hi]
    by_cases hj : d j = 0
    · simp [s, r, hj, hcol j i hj]
    have hsi : s i ≠ 0 := fun h => hi ((hs i).mp h)
    have hsj : s j ≠ 0 := fun h => hj ((hs j).mp h)
    have hci : (s i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsi
    have hcj : (s j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsj
    simp only [r, Complex.ofReal_inv]
    field_simp
theorem singular_interval_factorization {M E : Matrix n n ℂ} (hM : M.PosSemidef) :
    EventInterval M E ↔ ∃ F : Matrix n n ℂ,
      EventInterval 1 F ∧ E = CFC.sqrt M * F * CFC.sqrt M := by
  classical
  rw [← spectralRoot_eq_sqrt hM]
  let U := hM.isHermitian.eigenvectorUnitary
  let a := conjStarAlgAut ℂ (Matrix n n ℂ) U
  let d : n → ℝ := hM.isHermitian.eigenvalues
  have hdiag : a.symm M = diagonal (fun i => (d i : ℂ)) := by
    rw [show M = a (diagonal (fun i => (d i : ℂ))) from
      hM.isHermitian.spectral_theorem]
    exact a.symm_apply_apply _
  have hroot : spectralRoot hM = a (diagonal (fun i => (Real.sqrt (d i) : ℂ))) := rfl
  constructor
  · intro hE
    have hE' : EventInterval (diagonal (fun i => (d i : ℂ))) (a.symm E) := by
      refine ⟨?_, ?_⟩
      · have := conjugate_pos (star U) hE.1
        simpa only [a, conjStarAlgAut_symm] using this
      · rw [← hdiag, ← map_sub]
        simpa only [a, conjStarAlgAut_symm] using conjugate_pos (star U) hE.2
    obtain ⟨F, hF, hEF⟩ := diagonal_interval_factorization d hM.eigenvalues_nonneg hE'
    refine ⟨a F, ⟨conjugate_pos U hF.1, ?_⟩, ?_⟩
    · simpa only [map_sub, map_one] using conjugate_pos U hF.2
    · have := congrArg a hEF
      simpa only [StarAlgEquiv.apply_symm_apply, map_mul, ← hroot] using this
  · rintro ⟨F, hF, rfl⟩
    have hH := (spectralRoot_hermitian hM).eq
    refine ⟨?_, ?_⟩
    · simpa only [hH] using hF.1.conjTranspose_mul_mul_same (spectralRoot hM)
    · have := hF.2.conjTranspose_mul_mul_same (spectralRoot hM)
      simpa only [hH, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
        spectralRoot_sq] using this
def eventResponse (X E : Matrix n n ℂ) : ℝ := (trace (X * E)).re
def positiveSpectralMass {X : Matrix n n ℂ} (hX : X.IsHermitian) : ℝ :=
  ∑ i, max (hX.eigenvalues i) 0
private theorem trace_conjugate (U : Matrix.unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    trace (conjStarAlgAut ℂ _ U A) = trace A := by
  rw [conjStarAlgAut_apply, trace_mul_cycle, coe_star_mul_self, Matrix.one_mul]
private theorem trace_spectral_pair {X : Matrix n n ℂ} (hX : X.IsHermitian)
    (F : Matrix n n ℂ) :
    eventResponse X F = ∑ i, hX.eigenvalues i *
      (((conjStarAlgAut ℂ _ hX.eigenvectorUnitary).symm F) i i).re := by
  let a := conjStarAlgAut ℂ (Matrix n n ℂ) hX.eigenvectorUnitary
  have hdiag : X = a (diagonal (fun i => (hX.eigenvalues i : ℂ))) := hX.spectral_theorem
  have hpair : X * F = a (diagonal (fun i => (hX.eigenvalues i : ℂ)) * a.symm F) := by
    rw [map_mul, StarAlgEquiv.apply_symm_apply, ← hdiag]
  unfold eventResponse
  rw [hpair, trace_conjugate]
  simp [Matrix.trace, Matrix.diagonal_mul, Complex.mul_re, a]
private theorem conjugate_interval (U : Matrix.unitaryGroup n ℂ)
    {F : Matrix n n ℂ} (hF : EventInterval 1 F) :
    EventInterval 1 (conjStarAlgAut ℂ _ U F) := by
  refine ⟨conjugate_pos U hF.1, ?_⟩
  simpa only [map_sub, map_one] using conjugate_pos U hF.2
omit [Fintype n] in
private theorem effect_diagonal_bounds {F : Matrix n n ℂ} (hF : EventInterval 1 F)
    (i : n) : 0 ≤ (F i i).re ∧ (F i i).re ≤ 1 := by
  have h₁ := hF.1.diag_nonneg (i := i)
  have h₂ := hF.2.diag_nonneg (i := i)
  constructor
  · exact (RCLike.nonneg_iff.mp h₁).1
  · have := (RCLike.nonneg_iff.mp h₂).1
    simpa using this
private theorem effect_positive_spectral_max {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    ∃ P : Matrix n n ℂ, EventInterval 1 P ∧
      eventResponse X P = positiveSpectralMass hX ∧
      ∀ F, EventInterval 1 F → eventResponse X F ≤ positiveSpectralMass hX := by
  classical
  let a := conjStarAlgAut ℂ (Matrix n n ℂ) hX.eigenvectorUnitary
  let e : n → ℂ := fun i => if 0 < hX.eigenvalues i then 1 else 0
  have he : EventInterval (1 : Matrix n n ℂ) (diagonal e) := by
    constructor
    · apply PosSemidef.diagonal
      intro i
      dsimp [e]
      split_ifs <;> norm_num
    · rw [show (1 : Matrix n n ℂ) = diagonal (fun _ => 1) from diagonal_one.symm,
        diagonal_sub]
      apply PosSemidef.diagonal
      intro i
      dsimp [e]
      split_ifs <;> norm_num
  refine ⟨a (diagonal e), conjugate_interval _ he, ?_, ?_⟩
  · rw [trace_spectral_pair hX]
    change (∑ i, hX.eigenvalues i * ((a.symm (a (diagonal e))) i i).re) = _
    rw [StarAlgEquiv.symm_apply_apply]
    unfold positiveSpectralMass
    apply Finset.sum_congr rfl
    intro i _
    simp only [diagonal_apply_eq, e]
    split_ifs with hi
    · simp [max_eq_left hi.le]
    · simp [max_eq_right (le_of_not_gt hi)]
  · intro F hF
    rw [trace_spectral_pair hX]
    apply Finset.sum_le_sum
    intro i _
    have hF' : EventInterval 1 (a.symm F) := by
      simpa only [a, conjStarAlgAut_symm] using conjugate_interval (star hX.eigenvectorUnitary) hF
    have hb := effect_diagonal_bounds hF' i
    by_cases hi : 0 ≤ hX.eigenvalues i
    · rw [max_eq_left hi]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hb.2 hi
    · rw [max_eq_right (le_of_not_ge hi)]
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hi) hb.1
def weightedOperator (M X : Matrix n n ℂ) : Matrix n n ℂ :=
  (CFC.sqrt M)ᴴ * X * CFC.sqrt M
private theorem weighted_hermitian (M : Matrix n n ℂ) {X : Matrix n n ℂ}
    (hX : X.IsHermitian) : (weightedOperator M X).IsHermitian :=
  isHermitian_conjTranspose_mul_mul _ hX
def weightedPositiveMass (M : Matrix n n ℂ) {X : Matrix n n ℂ} (hX : X.IsHermitian) : ℝ :=
  positiveSpectralMass (weighted_hermitian M hX)
private theorem response_congruence (M X F : Matrix n n ℂ) :
    eventResponse X (CFC.sqrt M * F * CFC.sqrt M) =
      eventResponse (weightedOperator M X) F := by
  have hH : (CFC.sqrt M)ᴴ = CFC.sqrt M :=
    (CFC.sqrt_nonneg M).posSemidef.isHermitian.eq
  unfold eventResponse weightedOperator
  rw [hH]
  congr 1
  calc
    trace (X * (CFC.sqrt M * F * CFC.sqrt M)) =
        trace ((X * CFC.sqrt M * F) * CFC.sqrt M) := by simp only [Matrix.mul_assoc]
    _ = trace (CFC.sqrt M * (X * CFC.sqrt M * F)) := trace_mul_comm _ _
    _ = trace (CFC.sqrt M * X * CFC.sqrt M * F) := by simp only [Matrix.mul_assoc]
private theorem interval_positive_spectral_max {M X : Matrix n n ℂ}
    (hM : M.PosSemidef) (hX : X.IsHermitian) :
    ∃ E : Matrix n n ℂ, EventInterval M E ∧
      eventResponse X E = weightedPositiveMass M hX ∧
      ∀ F, EventInterval M F → eventResponse X F ≤ weightedPositiveMass M hX := by
  obtain ⟨P, hP, hv, hb⟩ := effect_positive_spectral_max (weighted_hermitian M hX)
  refine ⟨CFC.sqrt M * P * CFC.sqrt M, ?_, ?_, ?_⟩
  · exact (singular_interval_factorization hM).mpr ⟨P, hP, rfl⟩
  · simpa only [response_congruence, weightedPositiveMass] using hv
  · intro F hF
    obtain ⟨Q, hQ, rfl⟩ := (singular_interval_factorization hM).mp hF
    rw [response_congruence]
    exact hb Q hQ
theorem attained_two_direction_spectral_events {M X : Matrix n n ℂ}
    (hM : M.PosSemidef) (hX : X.IsHermitian) :
    ∃ Ep En : Matrix n n ℂ,
      EventInterval M Ep ∧ EventInterval M En ∧
      eventResponse X Ep = weightedPositiveMass M hX ∧
      -eventResponse X En = weightedPositiveMass M hX - eventResponse X M ∧
      (∀ E, EventInterval M E →
        eventResponse X E ≤ weightedPositiveMass M hX ∧
        -eventResponse X E ≤ weightedPositiveMass M hX - eventResponse X M) ∧
      IsGreatest {r : ℝ | ∃ E, EventInterval M E ∧ |eventResponse X E| = r}
        (weightedPositiveMass M hX + max (-eventResponse X M) 0) := by
  obtain ⟨Ep, hEp, hv, hb⟩ := interval_positive_spectral_max hM hX
  have hcomp {E : Matrix n n ℂ} (hE : EventInterval M E) : EventInterval M (M - E) :=
    ⟨hE.2, by simpa only [sub_sub_cancel] using hE.1⟩
  have hresp (E : Matrix n n ℂ) :
      eventResponse X (M - E) = eventResponse X M - eventResponse X E := by
    simp [eventResponse, Matrix.mul_sub, Matrix.trace_sub]
  have hneg (E : Matrix n n ℂ) (hE : EventInterval M E) :
      -eventResponse X E ≤ weightedPositiveMass M hX - eventResponse X M := by
    have := hb (M - E) (hcomp hE)
    rw [hresp] at this
    linarith
  have hL : 0 ≤ weightedPositiveMass M hX := by
    have := hb 0 ⟨PosSemidef.zero, by simpa using hM⟩
    simpa [eventResponse] using this
  have hLM : 0 ≤ weightedPositiveMass M hX - eventResponse X M := by
    have := hb M ⟨hM, by simp only [sub_self]; exact PosSemidef.zero⟩
    linarith
  refine ⟨Ep, M - Ep, hEp, hcomp hEp, hv, ?_, fun E hE => ⟨hb E hE, hneg E hE⟩, ?_⟩
  · rw [hresp, hv]
    ring
  · constructor
    · by_cases hT : 0 ≤ eventResponse X M
      · refine ⟨Ep, hEp, ?_⟩
        rw [hv, abs_of_nonneg hL, max_eq_right (neg_nonpos.mpr hT), add_zero]
      · refine ⟨M - Ep, hcomp hEp, ?_⟩
        rw [hresp, hv, abs_of_nonpos (by linarith), max_eq_left (by linarith)]
        ring
    · rintro r ⟨E, hE, rfl⟩
      apply abs_le.mpr
      have hp := hb E hE
      have hn := hneg E hE
      have h₀ : 0 ≤ max (-eventResponse X M) 0 := le_max_right _ _
      have h₁ : -eventResponse X M ≤ max (-eventResponse X M) 0 := le_max_left _ _
      constructor <;> linarith
open D5.S3.Quantum.Foundation.TwoRoundPhaseAverage
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open scoped Kronecker
def testerWeight (q t : ℝ) (ab : AB) : ℝ :=
  if ab.1 = 0 then if ab.2 = 0 then q else 1 - t
  else if ab.2 = 0 then 1 - q else t
def diagonalTester (q t : ℝ) : Matrix AB AB ℂ :=
  diagonal (fun ab => (testerWeight q t ab : ℂ))
def testerNormalization (q t : ℝ) : Matrix Wire Wire ℂ :=
  diagonalTester q t ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)
def compressedNormalization (q t : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  diagonal (fun k => if k = 0 then (q : ℂ) else if k = 1 then (1 - q : ℝ) else t)
def compressedDifference (eps : ℝ) (P : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  (candidate eps).submatrix mainAddress mainAddress - P
private theorem compressed_difference_hermitian (eps : ℝ)
    {P : Matrix (Fin 3) (Fin 3) ℂ} (hP : P.PosSemidef) :
    (compressedDifference eps P).IsHermitian :=
  ((posSemidef_vecMulVec_self_star (candidateVector eps)).isHermitian.submatrix mainAddress).sub
    hP.isHermitian
def compressedPositiveMass (eps q t : ℝ) {P : Matrix (Fin 3) (Fin 3) ℂ}
    (hP : P.PosSemidef) : ℝ :=
  weightedPositiveMass (compressedNormalization q t) (compressed_difference_hermitian eps hP)
private theorem mainAddress_of_support {i : Wire} (hi : MainSupport i) :
    mainAddress i.2 = i := by
  rcases hi with rfl | rfl | rfl <;> decide
private theorem blockEmbedding_gram : blockEmbeddingᴴ * blockEmbedding = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, blockEmbedding, Matrix.conjTranspose_apply, MainSupport,
      Fintype.sum_prod_type, Fin.sum_univ_three]
private theorem block_compression (E : Matrix Wire Wire ℂ) :
    blockEmbeddingᴴ * E * blockEmbedding = E.submatrix mainAddress mainAddress := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, blockEmbedding, Matrix.conjTranspose_apply, MainSupport,
      mainAddress, Fintype.sum_prod_type, Fin.sum_univ_three]
private theorem compress_embed (F : Matrix (Fin 3) (Fin 3) ℂ) :
    blockEmbeddingᴴ * embedBlock F * blockEmbedding = F := by
  calc
    _ = (blockEmbeddingᴴ * blockEmbedding) * F * (blockEmbeddingᴴ * blockEmbedding) := by
      simp only [embedBlock, Matrix.mul_assoc]
    _ = F := by rw [blockEmbedding_gram, Matrix.one_mul, Matrix.mul_one]
private theorem candidate_embed (eps : ℝ) :
    candidate eps = embedBlock ((candidate eps).submatrix mainAddress mainAddress) := by
  classical
  have hz (i : Wire) (hi : ¬ MainSupport i) : candidateVector eps i = 0 := by
    have h0 : i ≠ ((0, 0), 0) := fun h => hi (Or.inl h)
    have h1 : i ≠ ((1, 0), 1) := fun h => hi (Or.inr (Or.inl h))
    have h2 : i ≠ ((1, 1), 2) := fun h => hi (Or.inr (Or.inr h))
    simp [candidateVector, h0, h1, h2]
  ext i j
  rw [embedBlock_entry]
  by_cases hi : MainSupport i
  · by_cases hj : MainSupport j
    · simp only [hi, hj, if_true, Matrix.submatrix_apply,
        mainAddress_of_support hi, mainAddress_of_support hj]
    · simp [hi, hj, candidate, Matrix.vecMulVec_apply, hz j hj, Pi.star_apply]
  · simp [hi, candidate, Matrix.vecMulVec_apply, hz i hi, Pi.star_apply]
private theorem testerWeight_nonneg (q t : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (ab : AB) : 0 ≤ testerWeight q t ab := by
  unfold testerWeight
  split_ifs <;> linarith
private theorem diagonalTester_pos (q t : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) : (diagonalTester q t).PosSemidef := by
  apply PosSemidef.diagonal
  intro ab
  change (0 : ℂ) ≤ (testerWeight q t ab : ℂ)
  exact_mod_cast testerWeight_nonneg q t hq hq1 ht ht1 ab
private theorem diagonalTester_normalized (q t : ℝ) :
    partialTraceLeft (diagonalTester q t) = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [partialTraceLeft, diagonalTester, testerWeight, diagonal, Fin.sum_univ_two]
private theorem testerNormalization_diagonal (q t : ℝ) :
    testerNormalization q t = diagonal (fun i => (testerWeight q t i.1 : ℂ)) := by
  unfold testerNormalization diagonalTester
  rw [← diagonal_one, diagonal_kronecker_diagonal]
  simp only [mul_one]
private theorem testerNormalization_compression (q t : ℝ) :
    blockEmbeddingᴴ * testerNormalization q t * blockEmbedding = compressedNormalization q t := by
  rw [block_compression, testerNormalization_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.submatrix_apply, mainAddress, testerWeight, compressedNormalization, diagonal]
private def outsideDiagonal (w : Wire → ℂ) : Matrix Wire Wire ℂ := by
  classical
  exact diagonal (fun i => if MainSupport i then 0 else w i)
private theorem diagonal_embedding_split (w : Wire → ℂ) :
    diagonal w = embedBlock (diagonal (fun k => w (mainAddress k))) + outsideDiagonal w := by
  classical
  ext i j
  rw [Matrix.add_apply, embedBlock_entry]
  by_cases hi : MainSupport i
  · by_cases hj : MainSupport j
    · have heq : i.2 = j.2 ↔ i = j := by
        constructor
        · intro h
          rw [← mainAddress_of_support hi, ← mainAddress_of_support hj, h]
        · rintro rfl
          rfl
      simp [hi, hj, outsideDiagonal, diagonal, heq, mainAddress_of_support hi]
    · have hij : i ≠ j := fun h => hj (h ▸ hi)
      simp [hi, hj, hij, outsideDiagonal, diagonal]
  · simp [hi, outsideDiagonal, diagonal]
private theorem testerNormalization_split (q t : ℝ) :
    testerNormalization q t = embedBlock (compressedNormalization q t) +
      outsideDiagonal (fun i => (testerWeight q t i.1 : ℂ)) := by
  rw [testerNormalization_diagonal, diagonal_embedding_split]
  congr 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mainAddress, testerWeight, compressedNormalization, diagonal]
private theorem compressedNormalization_pos (q t : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) : (compressedNormalization q t).PosSemidef := by
  have hM := (diagonalTester_pos q t hq hq1 ht ht1).kronecker
    (PosSemidef.one : (1 : Matrix (Fin 3) (Fin 3) ℂ).PosSemidef)
  change (testerNormalization q t).PosSemidef at hM
  simpa only [testerNormalization_compression] using
    hM.conjTranspose_mul_mul_same blockEmbedding
private theorem lift_compressed_event (q t : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) {F : Matrix (Fin 3) (Fin 3) ℂ}
    (hF : EventInterval (compressedNormalization q t) F) :
    EventInterval (testerNormalization q t) (embedBlock F) := by
  classical
  refine ⟨hF.1.mul_mul_conjTranspose_same _, ?_⟩
  rw [testerNormalization_split]
  have ho : (outsideDiagonal (fun i => (testerWeight q t i.1 : ℂ))).PosSemidef := by
    apply PosSemidef.diagonal
    intro i
    dsimp [outsideDiagonal]
    split_ifs
    · exact le_rfl
    · exact_mod_cast testerWeight_nonneg q t hq hq1 ht ht1 i.1
  have h := (hF.2.mul_mul_conjTranspose_same blockEmbedding).add ho
  convert h using 1
  simp only [embedBlock, Matrix.mul_sub, Matrix.sub_mul]
  abel
private theorem compress_full_event (q t : ℝ) {E : Matrix Wire Wire ℂ}
    (hE : EventInterval (testerNormalization q t) E) :
    EventInterval (compressedNormalization q t) (blockEmbeddingᴴ * E * blockEmbedding) := by
  refine ⟨hE.1.conjTranspose_mul_mul_same _, ?_⟩
  have h := hE.2.conjTranspose_mul_mul_same blockEmbedding
  simpa only [Matrix.mul_sub, Matrix.sub_mul, testerNormalization_compression] using h
private theorem response_embed (F : Matrix (Fin 3) (Fin 3) ℂ) (E : Matrix Wire Wire ℂ) :
    eventResponse (embedBlock F) E = eventResponse F (blockEmbeddingᴴ * E * blockEmbedding) := by
  unfold eventResponse embedBlock
  congr 1
  calc
    _ = trace ((blockEmbedding * F) * (blockEmbeddingᴴ * E)) := by
      simp only [Matrix.mul_assoc]
    _ = trace ((blockEmbeddingᴴ * E) * (blockEmbedding * F)) := trace_mul_comm _ _
    _ = trace ((blockEmbeddingᴴ * E * blockEmbedding) * F) := by simp only [Matrix.mul_assoc]
    _ = _ := trace_mul_comm _ _
private theorem diagonal_response (w : Wire → ℝ) (E : Matrix Wire Wire ℂ) :
    eventResponse (diagonal (fun i => (w i : ℂ))) E = ∑ i, w i * (E i i).re := by
  simp [eventResponse, Matrix.trace, Matrix.diagonal_mul, Complex.mul_re]
private theorem completion_response (eps p : ℝ) (P : Matrix (Fin 3) (Fin 3) ℂ)
    (E : Matrix Wire Wire ℂ) :
    eventResponse (candidate eps - causalCompletion p P) E =
      eventResponse (compressedDifference eps P) (blockEmbeddingᴴ * E * blockEmbedding) -
        ∑ i, complementWeight p P i * (E i i).re := by
  rw [candidate_embed eps]
  simp only [causalCompletion, eventResponse, Matrix.sub_mul, Matrix.add_mul,
    Matrix.trace_sub, Matrix.trace_add, Complex.sub_re, Complex.add_re]
  change eventResponse (embedBlock ((candidate eps).submatrix mainAddress mainAddress)) E -
    (eventResponse (embedBlock P) E + eventResponse (diagonal _) E) = _
  rw [response_embed, response_embed, diagonal_response]
  simp only [compressedDifference, eventResponse, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
  ring
private theorem completion_lifted_response (eps p : ℝ) (P F : Matrix (Fin 3) (Fin 3) ℂ) :
    eventResponse (candidate eps - causalCompletion p P) (embedBlock F) =
      eventResponse (compressedDifference eps P) F := by
  classical
  rw [completion_response, compress_embed]
  have hz : ∑ i : Wire, complementWeight p P i * (embedBlock F i i).re = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : MainSupport i
    · have hw : complementWeight p P i = 0 := by
        rcases hi with rfl | rfl | rfl <;> simp [complementWeight]
      simp [hw]
    · simp [embedBlock_entry, hi]
  rw [hz, sub_zero]
private theorem normalization_trace (S : Matrix Wire Wire ℂ)
    (sigma : Matrix (Fin 2) (Fin 2) ℂ) (C : Matrix AB AB ℂ)
    (hSn : partialTraceRight S = Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) sigma)
    (hst : trace sigma = 1) (hCn : partialTraceLeft C = 1) :
    trace (S * (C ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ))) = 1 := by
  have dualR : ∀ {a b : Type} [Fintype a] [Fintype b] [DecidableEq b]
      (T : Matrix (a × b) (a × b) ℂ) (Y : Matrix a a ℂ),
      trace (T * (Y ⊗ₖ (1 : Matrix b b ℂ))) = trace (partialTraceRight T * Y) := by
    intro a b _ _ _ T Y
    simp [Matrix.trace, Matrix.mul_apply, Matrix.kroneckerMap_apply, partialTraceRight,
      Matrix.one_apply, Fintype.sum_prod_type, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have dualL : ∀ {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
      (T : Matrix (a × b) (a × b) ℂ) (Y : Matrix b b ℂ),
      trace (T * ((1 : Matrix a a ℂ) ⊗ₖ Y)) = trace (partialTraceLeft T * Y) := by
    intro a b _ _ _ T Y
    simp [Matrix.trace, Matrix.mul_apply, Matrix.kroneckerMap_apply, partialTraceLeft,
      Matrix.one_apply, Fintype.sum_prod_type, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  calc
    _ = trace (partialTraceRight S * C) := dualR S C
    _ = trace (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ sigma) * C) := by rw [hSn]; rfl
    _ = trace (C * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ sigma)) := trace_mul_comm _ _
    _ = trace (partialTraceLeft C * sigma) := dualL C sigma
    _ = 1 := by rw [hCn, Matrix.one_mul, hst]
private theorem candidate_normalization_response (eps q t : ℝ) (he : 0 ≤ eps) (he1 : eps ≤ 1) :
    eventResponse (candidate eps) (testerNormalization q t) = 1 - eps * (1 - q - t) := by
  rw [testerNormalization_diagonal]
  simp [eventResponse, candidate, candidateVector, testerWeight, Matrix.trace,
    Matrix.mul_diagonal, Matrix.vecMulVec_apply, Pi.star_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, Complex.mul_re,
    Real.mul_self_sqrt he, Real.mul_self_sqrt (sub_nonneg.mpr he1)]
  ring
theorem compressed_completion_tester_value (eps p q t : ℝ)
    (P : Matrix (Fin 3) (Fin 3) ℂ) (he : 0 ≤ eps) (he1 : eps ≤ 1)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hP : P.PosSemidef) (h0 : (P 0 0).re ≤ 1 - p) (h1 : (P 1 1).re ≤ 1 - p)
    (h2 : (P 2 2).re ≤ p) :
    Causal (causalCompletion p P) (diagonalMarginal p) ∧
    ∃ Ep En : Matrix Wire Wire ℂ,
      Tester (diagonalTester q t) Ep ∧ Tester (diagonalTester q t) En ∧
      response (candidate eps - causalCompletion p P) Ep = compressedPositiveMass eps q t hP ∧
      response (causalCompletion p P - candidate eps) En =
        compressedPositiveMass eps q t hP + eps * (1 - q - t) ∧
      (∀ E, Tester (diagonalTester q t) E →
        response (candidate eps - causalCompletion p P) E ≤ compressedPositiveMass eps q t hP ∧
        response (causalCompletion p P - candidate eps) E ≤
          compressedPositiveMass eps q t hP + eps * (1 - q - t)) ∧
      IsGreatest {r : ℝ | ∃ E, Tester (diagonalTester q t) E ∧
        |response (candidate eps - causalCompletion p P) E| = r}
        (compressedPositiveMass eps q t hP + max (eps * (1 - q - t)) 0) := by
  let S := causalCompletion p P
  let X := candidate eps - S
  let M := testerNormalization q t
  have hS := (compressed_block_causal_lift p P hp hp1 hP h0 h1 h2).1
  have hC := diagonalTester_pos q t hq hq1 ht ht1
  have hCn := diagonalTester_normalized q t
  have hM : M.PosSemidef := hC.kronecker PosSemidef.one
  have hX : X.IsHermitian := (posSemidef_vecMulVec_self_star (candidateVector eps)).isHermitian.sub
    hS.1.isHermitian
  have hB := compressedNormalization_pos q t hq hq1 ht ht1
  obtain ⟨F, _, hF, _, hvF, _, hbF, _⟩ :=
    attained_two_direction_spectral_events hB (compressed_difference_hermitian eps hP)
  have hupper (E : Matrix Wire Wire ℂ) (hE : EventInterval M E) :
      eventResponse X E ≤ compressedPositiveMass eps q t hP := by
    have hb := (hbF _ (compress_full_event q t hE)).1
    have hc : 0 ≤ ∑ i, complementWeight p P i * (E i i).re := by
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (complementWeight_nonneg p P hp h0 h1 h2 i)
        (RCLike.nonneg_iff.mp (hE.1.diag_nonneg (i := i))).1
    change eventResponse (candidate eps - causalCompletion p P) E ≤ _
    rw [completion_response]
    dsimp [compressedPositiveMass]
    linarith
  obtain ⟨Ep, En, hEp, hEn, hv, hnv, hb, hgreat⟩ :=
    attained_two_direction_spectral_events hM hX
  have hmass : weightedPositiveMass M hX = compressedPositiveMass eps q t hP := by
    apply le_antisymm
    · have := hupper Ep hEp
      rw [hv] at this
      exact this
    · have hLift := lift_compressed_event q t hq hq1 ht ht1 hF
      have h := (hb (embedBlock F) hLift).1
      change eventResponse (candidate eps - causalCompletion p P) (embedBlock F) ≤ _ at h
      rw [completion_lifted_response, hvF] at h
      exact h
  have htrace : eventResponse X M = -eps * (1 - q - t) := by
    have hst := normalization_trace S (diagonalMarginal p) (diagonalTester q t)
      hS.2.2.2 hS.2.2.1 hCn
    have hR := candidate_normalization_response eps q t he he1
    have h : eventResponse X M = eventResponse (candidate eps) M - 1 := by
      simp [X, eventResponse, Matrix.sub_mul, Matrix.trace_sub, M, testerNormalization, hst]
    rw [h, hR]
    ring
  have hrev (E : Matrix Wire Wire ℂ) :
      response (S - candidate eps) E = -eventResponse X E := by
    simp [X, response, eventResponse, Matrix.sub_mul, trace_sub]
  refine ⟨hS, Ep, En, ⟨hC, hCn, hEp⟩, ⟨hC, hCn, hEn⟩, ?_, ?_, ?_, ?_⟩
  · exact hv.trans hmass
  · rw [hrev, hnv, hmass, htrace]
    ring
  · intro E hE
    have h := hb E ⟨hE.2.2.1, hE.2.2.2⟩
    refine ⟨h.1.trans_eq hmass, ?_⟩
    rw [hrev]
    rw [hmass, htrace] at h
    linarith [h.2]
  · have hset : {r : ℝ | ∃ E, Tester (diagonalTester q t) E ∧ |response X E| = r} =
        {r : ℝ | ∃ E, EventInterval M E ∧ |eventResponse X E| = r} := by
      ext r
      constructor
      · rintro ⟨E, hE, hr⟩
        exact ⟨E, ⟨hE.2.2.1, hE.2.2.2⟩, hr⟩
      · rintro ⟨E, hE, hr⟩
        exact ⟨E, ⟨hC, hCn, hE⟩, hr⟩
    change IsGreatest {r : ℝ | ∃ E, Tester (diagonalTester q t) E ∧ |response X E| = r} _
    rw [hset]
    convert hgreat using 1
    rw [hmass, htrace]
    congr 2
    ring
private theorem completion_phase_fixed (p : ℝ) (P : Matrix (Fin 3) (Fin 3) ℂ) (g : Phase) :
    signConjugate (phaseWire g) (causalCompletion p P) = causalCompletion p P := by
  classical
  have h20 : (2 : Fin 3) ≠ 0 := by simp [Fin.ext_iff]
  have h21 : (2 : Fin 3) ≠ 1 := by simp [Fin.ext_iff]
  have hm (i : Wire) (hi : MainSupport i) : phaseWire g i = 1 := by
    rcases hi with rfl | rfl | rfl <;>
      rcases g with ⟨a, b⟩ <;> fin_cases a <;> fin_cases b <;>
      norm_num [phaseWire, phaseAB, phaseD, bitSign, h20, h21]
  have hs (i : Wire) : phaseWire g i * phaseWire g i = 1 := by
    rcases g with ⟨a, b⟩
    rcases i with ⟨⟨c, d⟩, e⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases e <;>
      norm_num [phaseWire, phaseAB, phaseD, bitSign, h20, h21]
  have he : signConjugate (phaseWire g) (embedBlock P) = embedBlock P := by
    ext i j
    by_cases hi : MainSupport i <;> by_cases hj : MainSupport j <;>
      simp [signConjugate, embedBlock_entry, hi, hj, hm]
  have hd : signConjugate (phaseWire g)
      (diagonal (fun i => (complementWeight p P i : ℂ))) =
      diagonal (fun i => (complementWeight p P i : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [signConjugate, diagonal_apply_eq]
      calc
        _ = (phaseWire g i * phaseWire g i) * (complementWeight p P i : ℂ) := by ring
        _ = _ := by rw [hs]; ring
    · simp [signConjugate, diagonal, hij]
  ext i j
  have heij := congrArg (fun M : Matrix Wire Wire ℂ => M i j) he
  have hdij := congrArg (fun M : Matrix Wire Wire ℂ => M i j) hd
  simpa only [signConjugate, causalCompletion, Matrix.add_apply, mul_add, add_mul] using
    congrArg₂ (fun x y : ℂ => x + y) heij hdij
private theorem diagonal_tester_parameters {C : Matrix AB AB ℂ} (hC : C.PosSemidef)
    (hCn : partialTraceLeft C = 1) (hCd : C.IsDiag) :
    ∃ q t : ℝ, 0 ≤ q ∧ q ≤ 1 ∧ 0 ≤ t ∧ t ≤ 1 ∧ C = diagonalTester q t := by
  let q := (C (0, 0) (0, 0)).re
  let t := (C (1, 1) (1, 1)).re
  have hq : 0 ≤ q := (RCLike.nonneg_iff.mp (hC.diag_nonneg (i := (0, 0)))).1
  have ht : 0 ≤ t := (RCLike.nonneg_iff.mp (hC.diag_nonneg (i := (1, 1)))).1
  have h01 : 0 ≤ (C (0, 1) (0, 1)).re :=
    (RCLike.nonneg_iff.mp (hC.diag_nonneg (i := (0, 1)))).1
  have h10 : 0 ≤ (C (1, 0) (1, 0)).re :=
    (RCLike.nonneg_iff.mp (hC.diag_nonneg (i := (1, 0)))).1
  have hb0 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 0).re) hCn
  have hb1 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 1 1).re) hCn
  simp [partialTraceLeft, Fin.sum_univ_two] at hb0 hb1
  have hq1 : q ≤ 1 := by dsimp [q]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hr (ab : AB) : C ab ab = ((C ab ab).re : ℂ) :=
    Complex.eq_re_of_ofReal_le (r := 0) hC.diag_nonneg
  have hd (ab : AB) : C ab ab = (testerWeight q t ab : ℂ) := by
    rcases ab with ⟨a, b⟩
    fin_cases a <;> fin_cases b
    · change C (0, 0) (0, 0) = (q : ℂ)
      exact hr _
    · change C (0, 1) (0, 1) = ((1 - t : ℝ) : ℂ)
      rw [hr]
      congr 1
      dsimp [t]
      linarith
    · change C (1, 0) (1, 0) = ((1 - q : ℝ) : ℂ)
      rw [hr]
      congr 1
      dsimp [q]
      linarith
    · change C (1, 1) (1, 1) = (t : ℂ)
      exact hr _
  refine ⟨q, t, hq, hq1, ht, ht1, ?_⟩
  calc
    C = diagonal (fun ab => C ab ab) := hCd.diagonal_diag.symm
    _ = diagonalTester q t := congrArg diagonal (funext hd)
theorem full_tester_compressed_objective (eps p : ℝ) (P : Matrix (Fin 3) (Fin 3) ℂ)
    (he : 0 ≤ eps) (he1 : eps ≤ 1) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hP : P.PosSemidef)
    (h0 : (P 0 0).re ≤ 1 - p) (h1 : (P 1 1).re ≤ 1 - p) (h2 : (P 2 2).re ≤ p) (b : ℝ) :
    ErrorBound (candidate eps - causalCompletion p P) b ↔
      ∀ q t : ℝ, 0 ≤ q → q ≤ 1 → 0 ≤ t → t ≤ 1 →
        compressedPositiveMass eps q t hP + max (eps * (1 - q - t)) 0 ≤ b := by
  let S := causalCompletion p P
  have hS := (compressed_block_causal_lift p P hp hp1 hP h0 h1 h2).1
  constructor
  · intro hError q t hq hq1 ht ht1
    obtain ⟨_, _, _, _, _, _, _, hgreat⟩ :=
      (compressed_completion_tester_value eps p q t P he he1 hp hp1 hq hq1 ht ht1
        hP h0 h1 h2).2
    obtain ⟨E, hE, hv⟩ := hgreat.1
    calc
      _ = |response (candidate eps - causalCompletion p P) E| := hv.symm
      _ ≤ b := hError _ _ hE
  · intro hBound C E hCE
    obtain ⟨_, _, _, hAvg, hDiag, _, hRresp, hInv, _⟩ :=
      joint_phase_reduction eps S (diagonalMarginal p) C E hS hCE
    have hSresp := hInv S (fun g => completion_phase_fixed p P g)
    have hresp : response (candidate eps - S) (averageWire E) =
        response (candidate eps - S) E := by
      simpa only [response, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re] using
        congrArg₂ (fun x y : ℝ => x - y) hRresp hSresp
    obtain ⟨q, t, hq, hq1, ht, ht1, hQt⟩ :=
      diagonal_tester_parameters hAvg.1 hAvg.2.1 hDiag
    rw [hQt] at hAvg
    obtain ⟨_, _, _, _, _, _, _, hgreat⟩ :=
      (compressed_completion_tester_value eps p q t P he he1 hp hp1 hq hq1 ht ht1
        hP h0 h1 h2).2
    have h := hgreat.2 ⟨averageWire E, hAvg, rfl⟩
    change |response (candidate eps - S) E| ≤ b
    rw [← hresp]
    exact h.trans (hBound q t hq hq1 ht ht1)
private theorem response_compressed_event (X : Matrix Wire Wire ℂ)
    (F : Matrix (Fin 3) (Fin 3) ℂ) :
    eventResponse X (embedBlock F) = eventResponse (X.submatrix mainAddress mainAddress) F := by
  calc
    _ = eventResponse (embedBlock F) X := congrArg Complex.re (trace_mul_comm X (embedBlock F))
    _ = eventResponse F (blockEmbeddingᴴ * X * blockEmbedding) := response_embed F X
    _ = _ := by rw [block_compression]; exact congrArg Complex.re (trace_mul_comm F _)
theorem causal_compressed_repair_domination (eps : ℝ) (S : Matrix Wire Wire ℂ)
    (sigma : Matrix (Fin 2) (Fin 2) ℂ) (he : 0 ≤ eps) (he1 : eps ≤ 1) (hS : Causal S sigma) :
    let p := (sigma 1 1).re
    let P := S.submatrix mainAddress mainAddress
    Causal (causalCompletion p P) (diagonalMarginal p) ∧
      (causalCompletion p P).submatrix mainAddress mainAddress = P ∧
      diagonalMarginal p 1 1 = sigma 1 1 ∧
      (∀ b : ℝ, ErrorBound (candidate eps - S) b →
        ErrorBound (candidate eps - causalCompletion p P) b) := by
  intro p P
  obtain ⟨hp, hp1, hP, h0, h1, h2⟩ := causal_principal_block_budgets S sigma hS
  have hLift := compressed_block_causal_lift p P hp hp1 hP h0 h1 h2
  refine ⟨hLift.1, hLift.2.1, ?_, ?_⟩
  · rw [hLift.2.2]
    exact (Complex.eq_re_of_ofReal_le (r := 0) hS.2.1.diag_nonneg).symm
  · intro b hError
    apply (full_tester_compressed_objective eps p P he he1 hp hp1 hP h0 h1 h2 b).mpr
    intro q t hq hq1 ht ht1
    let C := diagonalTester q t
    let M := testerNormalization q t
    let X := candidate eps - S
    have hC := diagonalTester_pos q t hq hq1 ht ht1
    have hCn := diagonalTester_normalized q t
    have hB := compressedNormalization_pos q t hq hq1 ht ht1
    obtain ⟨F, _, hF, _, hvF, _, _, _⟩ :=
      attained_two_direction_spectral_events hB (compressed_difference_hermitian eps hP)
    have hE := lift_compressed_event q t hq hq1 ht ht1 hF
    have hCE : Tester C (embedBlock F) := ⟨hC, hCn, hE⟩
    have hCM : Tester C (M - embedBlock F) :=
      ⟨hC, hCn, hE.2, by
        change (M - (M - embedBlock F)).PosSemidef
        simpa only [sub_sub_cancel] using hE.1⟩
    have hval : eventResponse X (embedBlock F) = compressedPositiveMass eps q t hP := by
      rw [response_compressed_event]
      change eventResponse (compressedDifference eps P) F = _
      exact hvF
    have htr : eventResponse X M = -eps * (1 - q - t) := by
      have hst := normalization_trace S sigma C hS.2.2.2 hS.2.2.1 hCn
      have hR := candidate_normalization_response eps q t he he1
      have h : eventResponse X M = eventResponse (candidate eps) M - 1 := by
        simp [X, eventResponse, Matrix.sub_mul, Matrix.trace_sub, M, C, testerNormalization, hst]
      rw [h, hR]
      ring
    have hcomp : eventResponse X (M - embedBlock F) =
        -eps * (1 - q - t) - compressedPositiveMass eps q t hP := by
      have h : eventResponse X (M - embedBlock F) =
          eventResponse X M - eventResponse X (embedBlock F) := by
        simp [eventResponse, Matrix.mul_sub, trace_sub]
      rw [h, htr, hval]
    have hpos : compressedPositiveMass eps q t hP ≤ b := by
      have h := (le_abs_self (eventResponse X (embedBlock F))).trans (hError C (embedBlock F) hCE)
      rwa [hval] at h
    have hneg : compressedPositiveMass eps q t hP + eps * (1 - q - t) ≤ b := by
      have h := (neg_le_abs (eventResponse X (M - embedBlock F))).trans
        (hError C (M - embedBlock F) hCM)
      rw [hcomp] at h
      linarith
    by_cases hc : 0 ≤ eps * (1 - q - t)
    · rw [max_eq_left hc]
      exact hneg
    · rw [max_eq_right (le_of_not_ge hc), add_zero]
      exact hpos
def quadratic {n : Type*} [Fintype n] (A : Matrix n n ℂ) (z : n → ℂ) : ℝ :=
  (star z ⬝ᵥ (A *ᵥ z)).re
theorem quadratic_real {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) (z : n → ℝ) :
    quadratic A (fun i => (z i : ℂ)) = ∑ i, ∑ j, (A i j).re * z i * z j := by
  simp only [quadratic, dotProduct, mulVec, Pi.star_apply,
    Complex.star_def, Complex.conj_ofReal, Finset.mul_sum, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_zero]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
theorem quadratic_le_mass {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (z : n → ℂ) :
    quadratic A z ≤ positiveSpectralMass hA * (star z ⬝ᵥ z).re := by
  classical
  let L := positiveSpectralMass hA
  let U := hA.eigenvectorUnitary
  let a := conjStarAlgAut ℂ (Matrix n n ℂ) U
  have hL (i : n) : hA.eigenvalues i ≤ L := by
    calc
      _ ≤ max (hA.eigenvalues i) 0 := le_max_left _ _
      _ ≤ ∑ j, max (hA.eigenvalues j) 0 :=
        Finset.single_le_sum (fun j _ => le_max_right _ _) (Finset.mem_univ i)
  have hd : diagonal (fun i => ((L - hA.eigenvalues i : ℝ) : ℂ)) =
      (L : ℂ) • (1 : Matrix n n ℂ) - diagonal (fun i => (hA.eigenvalues i : ℂ)) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  have ha : a (diagonal (fun i => ((L - hA.eigenvalues i : ℝ) : ℂ))) =
      (L : ℂ) • (1 : Matrix n n ℂ) - A := by
    rw [hd, map_sub, map_smul, map_one]
    congr 1
    exact hA.spectral_theorem.symm
  have hpos : ((L : ℂ) • (1 : Matrix n n ℂ) - A).PosSemidef := by
    rw [← ha, conjStarAlgAut_apply]
    apply PosSemidef.mul_mul_conjTranspose_same
    exact PosSemidef.diagonal (fun i => Complex.nonneg_iff.mpr
      ⟨by simpa using sub_nonneg.mpr (hL i), by simp⟩)
  have h := hpos.re_dotProduct_nonneg z
  simp only [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul] at h
  change 0 ≤ ((L : ℂ) * (star z ⬝ᵥ z) - star z ⬝ᵥ (A *ᵥ z)).re at h
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at h
  change quadratic A z ≤ L * _
  dsimp [quadratic]
  linarith
theorem real_eigenvalue_le_mass {H : Matrix (Fin 3) (Fin 3) ℝ}
    (hH : H.IsHermitian) {A : Matrix (Fin 3) (Fin 3) ℂ} (hA : A.IsHermitian)
    (hoff : ∀ i j, i ≠ j → 0 ≤ H i j) (hentry : ∀ i j, H i j ≤ (A i j).re)
    {lam : ℝ} (hlam : lam ∈ spectrum ℝ H) : lam ≤ positiveSpectralMass hA := by
  obtain ⟨k, hk⟩ := hH.spectrum_real_eq_range_eigenvalues ▸ hlam
  let v : Fin 3 → ℝ := hH.eigenvectorBasis k
  let z : Fin 3 → ℝ := fun i => |v i|
  have hv : ∑ i, v i ^ 2 = 1 := by
    have hn := hH.eigenvectorBasis.orthonormal.1 k
    have hs := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) (hH.eigenvectorBasis k)
    rw [hn, one_pow] at hs
    simpa [v, Real.norm_eq_abs, sq_abs] using hs.symm
  have he : lam = ∑ i, ∑ j, H i j * v i * v j := by
    rw [← hk, hH.eigenvalues_eq]
    simp only [RCLike.re_to_real, star_trivial, dotProduct, mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hcomp : (∑ i, ∑ j, H i j * v i * v j) ≤
      ∑ i, ∑ j, (A i j).re * z i * z j := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    have hnorm : H i j * v i * v j ≤ H i j * z i * z j := by
      by_cases hij : i = j
      · subst j
        dsimp [z]
        apply le_of_eq
        calc
          _ = H i i * (v i ^ 2) := by ring
          _ = H i i * (|v i| ^ 2) := by rw [sq_abs]
          _ = H i i * |v i| * |v i| := by ring
      · have hb : v i * v j ≤ z i * z j := by
          simpa only [z, abs_mul] using le_abs_self (v i * v j)
        nlinarith [mul_le_mul_of_nonneg_left hb (hoff i j hij)]
    exact hnorm.trans (by
      have hb := mul_le_mul_of_nonneg_right (hentry i j)
        (mul_nonneg (abs_nonneg (v i)) (abs_nonneg (v j)))
      simpa only [mul_assoc, z] using hb)
  have hq := quadratic_le_mass hA (fun i => (z i : ℂ))
  have hz : (star (fun i => (z i : ℂ)) ⬝ᵥ (fun i => (z i : ℂ))).re = 1 := by
    simpa [dotProduct, z, ← Complex.ofReal_mul, ← sq, ← Complex.ofReal_pow,
      sq_abs] using hv
  rw [quadratic_real, hz, mul_one] at hq
  rw [he]
  exact hcomp.trans hq
end D5.S3.Quantum.Foundation.TwoRoundSpectralEvents
namespace D5.S3.Quantum.Foundation.TwoRoundRankOneReduction
open D5.S3.Quantum.Foundation.TwoRoundPhaseAverage
open D5.S3.Quantum.Foundation.TwoRoundSpectralEvents
def realOuter (u : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  vecMulVec (fun i => (u i : ℂ)) (star (fun i => (u i : ℂ)))
def gramU (u : Fin 3 → ℝ) : ℝ := ∑ i, u i ^ 2
def gramW (u v : Fin 3 → ℝ) : ℝ := ∑ i, u i * v i
def positiveRoot (u v : Fin 3 → ℝ) : ℝ :=
  (gramU u - gramU v + Real.sqrt ((gramU u + gramU v) ^ 2 - 4 * gramW u v ^ 2)) / 2
def negativeRoot (u v : Fin 3 → ℝ) : ℝ :=
  (gramU u - gramU v - Real.sqrt ((gramU u + gramU v) ^ 2 - 4 * gramW u v ^ 2)) / 2
theorem gram_nonneg (u v : Fin 3 → ℝ) :
    0 ≤ gramU u ∧ 0 ≤ gramU v ∧ gramW u v ^ 2 ≤ gramU u * gramU v := by
  refine ⟨Finset.sum_nonneg (fun i _ => sq_nonneg _),
    Finset.sum_nonneg (fun i _ => sq_nonneg _), ?_⟩
  dsimp [gramU, gramW]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
theorem root_relations (u v : Fin 3 → ℝ) :
    0 ≤ positiveRoot u v ∧ negativeRoot u v ≤ 0 ∧
      positiveRoot u v + negativeRoot u v = gramU u - gramU v ∧
      positiveRoot u v * negativeRoot u v = gramW u v ^ 2 - gramU u * gramU v := by
  obtain ⟨hU, hV, hW⟩ := gram_nonneg u v
  have hd : 0 ≤ (gramU u + gramU v) ^ 2 - 4 * gramW u v ^ 2 := by
    nlinarith [sq_nonneg (gramU u - gramU v)]
  have hs := Real.sq_sqrt hd
  have hn := Real.sqrt_nonneg ((gramU u + gramU v) ^ 2 - 4 * gramW u v ^ 2)
  have hb : |gramU u - gramU v| ≤
      Real.sqrt ((gramU u + gramU v) ^ 2 - 4 * gramW u v ^ 2) := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (gramU u - gramU v)]
  dsimp [positiveRoot, negativeRoot]
  refine ⟨by linarith [abs_le.mp hb], by linarith [abs_le.mp hb], by ring, ?_⟩
  nlinarith [hs]
theorem difference_charpoly (u v : Fin 3 → ℝ) :
    (realOuter u - realOuter v).charpoly =
      Polynomial.X * (Polynomial.X - Polynomial.C (positiveRoot u v : ℂ)) *
        (Polynomial.X - Polynomial.C (negativeRoot u v : ℂ)) := by
  obtain ⟨_, _, hs, hp⟩ := root_relations u v
  have hs' := congrArg (fun r : ℝ => (r : ℂ)) hs
  have hp' := congrArg (fun r : ℝ => (r : ℂ)) hp
  simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_pow] at hs' hp'
  have hsum : Polynomial.C (positiveRoot u v : ℂ) + Polynomial.C (negativeRoot u v : ℂ) =
      Polynomial.C ((gramU u : ℂ) - (gramU v : ℂ)) := by rw [← map_add, hs']
  have hprod : Polynomial.C (positiveRoot u v : ℂ) * Polynomial.C (negativeRoot u v : ℂ) =
      Polynomial.C ((gramW u v : ℂ) ^ 2 - (gramU u : ℂ) * (gramU v : ℂ)) := by
    rw [← map_mul, hp']
  calc
    _ = Polynomial.X ^ 3 -
        Polynomial.C ((gramU u : ℂ) - (gramU v : ℂ)) * Polynomial.X ^ 2 +
        Polynomial.C ((gramW u v : ℂ) ^ 2 - (gramU u : ℂ) * (gramU v : ℂ)) * Polynomial.X := by
      simp [Matrix.charpoly, Matrix.charmatrix, Matrix.det_fin_three,
        realOuter, Matrix.vecMulVec_apply, Matrix.scalar, Matrix.diagonal,
        gramU, gramW, Fin.sum_univ_three, Polynomial.C_add, Polynomial.C_sub,
        Polynomial.C_mul, Polynomial.C_pow]
      ring
    _ = _ := by rw [← hsum, ← hprod]; ring
theorem positive_mass_diagonal (d : Fin 3 → ℝ)
    (hD : (diagonal (fun i => (d i : ℂ))).IsHermitian) :
    positiveSpectralMass hD = ∑ i, max (d i) 0 := by
  have hr := hD.roots_charpoly_eq_eigenvalues
  rw [charpoly_diagonal, Polynomial.roots_prod] at hr
  · have hm := congrArg (fun s : Multiset ℂ => (s.map (fun z => max z.re 0)).sum) hr
    simpa [positiveSpectralMass, Fin.sum_univ_three, add_assoc] using hm.symm
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => Polynomial.X_sub_C_ne_zero _)
theorem rank_one_positive_mass (u v : Fin 3 → ℝ) :
    positiveSpectralMass
      ((posSemidef_vecMulVec_self_star (fun i => (u i : ℂ))).isHermitian.sub
        (posSemidef_vecMulVec_self_star (fun i => (v i : ℂ))).isHermitian) =
      positiveRoot u v := by
  let hB : (realOuter u - realOuter v).IsHermitian :=
    (posSemidef_vecMulVec_self_star _).isHermitian.sub
      (posSemidef_vecMulVec_self_star _).isHermitian
  let d : Fin 3 → ℝ := ![positiveRoot u v, negativeRoot u v, 0]
  let hD : (diagonal (fun i => (d i : ℂ))).IsHermitian :=
    isHermitian_diagonal_iff.mpr (fun i => by
      change IsSelfAdjoint (d i : ℂ); simp [IsSelfAdjoint])
  have hc : (realOuter u - realOuter v).charpoly = (diagonal (fun i => (d i : ℂ))).charpoly := by
    rw [difference_charpoly, charpoly_diagonal]
    simp [d, Fin.prod_univ_three]
    ring
  have he := (hB.eigenvalues_eq_eigenvalues_iff hD).mpr hc
  change positiveSpectralMass hB = _
  change (∑ i, max (hB.eigenvalues i) 0) = _
  rw [he]
  change positiveSpectralMass hD = _
  rw [positive_mass_diagonal]
  obtain ⟨hp, hn, _, _⟩ := root_relations u v
  simp [d, Fin.sum_univ_three, max_eq_left hp, max_eq_right hn]
end D5.S3.Quantum.Foundation.TwoRoundRankOneReduction
