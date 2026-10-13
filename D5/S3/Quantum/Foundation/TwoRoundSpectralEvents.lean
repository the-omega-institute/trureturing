/- GID: D5/S3/Quantum/Foundation/TwoRoundSpectralEvents
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/TwoRoundSpectralEvents
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Singular normalization and attained full spectral quantum events. -/

import D5.S3.Quantum.Foundation.TwoRoundPhaseAverage
import Mathlib.Analysis.Matrix.Order

noncomputable section

open Matrix Unitary
open scoped BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Foundation.TwoRoundSpectralEvents

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A complete event interval, including singular normalization operators. -/
def EventInterval (M E : Matrix n n ℂ) : Prop :=
  E.PosSemidef ∧ (M - E).PosSemidef

/-- The positive square root expressed in the normalization's spectral basis. -/
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

/-- Every event under a possibly singular normalization is a congruence of a full effect. -/
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


/-- Real trace pairing of arbitrary finite complex matrices. -/
def eventResponse (X E : Matrix n n ℂ) : ℝ := (trace (X * E)).re

/-- The sum of all positive eigenvalues, retaining multiplicity. -/
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
  simp [Matrix.trace, Matrix.diagonal_mul, Complex.mul_re, a, conjStarAlgAut_symm_apply]

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

/-- The weighted Hermitian operator for a full event interval. -/
def weightedOperator (M X : Matrix n n ℂ) : Matrix n n ℂ :=
  (CFC.sqrt M)ᴴ * X * CFC.sqrt M

private theorem weighted_hermitian (M : Matrix n n ℂ) {X : Matrix n n ℂ}
    (hX : X.IsHermitian) : (weightedOperator M X).IsHermitian :=
  isHermitian_conjTranspose_mul_mul _ hX

/-- The full weighted positive spectrum, with no rank or support restriction. -/
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

/-- Both directions and the absolute event error are attained in the complete singular interval.
The backward branch retains the full normalization trace. -/
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

end D5.S3.Quantum.Foundation.TwoRoundSpectralEvents
