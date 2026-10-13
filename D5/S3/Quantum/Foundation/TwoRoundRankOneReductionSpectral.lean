/- GID: D5/S3/Quantum/Foundation/TwoRoundRankOneReductionSpectral
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/TwoRoundRankOneReductionSpectral
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Singular event interval machinery and consumed rank-one spectral mass. -/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings
import Mathlib.Analysis.Matrix.Order
noncomputable section
open Matrix Unitary
open scoped BigOperators ComplexOrder MatrixOrder
namespace D5.S3.Quantum.Foundation.TwoRoundSpectralEvents
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
