/- GID: D5/S3/Quantum/Recovery/WernerHolevoBayesianFeedbackAdvantage
   generality: I
   mirror-B: D5/B/S3/Quantum/Recovery/WernerHolevoBayesianFeedbackAdvantage
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Bayesian feedback beats Markovian feedback for the qutrit Werner--Holevo channel. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-! The qutrit Werner--Holevo channel separates Bayesian and Markovian feedback. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

namespace D5.S3.Quantum.Recovery.WernerHolevoBayesianFeedbackAdvantage

/-- The Matrix (Fin 3) (Fin 3) ℂ Werner--Holevo (transpose-depolarizing) channel. -/
def whChannel (x : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  (1 / 2 : ℂ) • (x.trace • (1 : Matrix (Fin 3) (Fin 3) ℂ) - x.transpose)

/-- A finite Kraus family represents the Werner--Holevo channel. -/
def IsKrausDecomposition {m : ℕ} (k : Fin m → Matrix (Fin 3) (Fin 3) ℂ) : Prop :=
  ∀ x : Matrix (Fin 3) (Fin 3) ℂ, ∑ a, k a * x * (k a)ᴴ = whChannel x

/-- Matrix absolute value, defined by the positive square root of `tᴴ * t`. -/
def absMat (t : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ := CFC.sqrt (tᴴ * t)

/-- The two-step Markovian feedback fidelity from the source. -/
def markovFidelity {m₁ m₂ : ℕ} (k₁ : Fin m₁ → Matrix (Fin 3) (Fin 3) ℂ)
    (k₂ : Fin m₂ → Matrix (Fin 3) (Fin 3) ℂ) : ℝ :=
  (1 / 9 : ℝ) * ∑ a, ∑ b,
    (((absMat (k₂ b) * absMat (k₁ a)).trace).re) ^ 2

/-- The two-step Bayesian feedback fidelity from the source. -/
def bayesFidelity {m₁ m₂ : ℕ} (k₁ : Fin m₁ → Matrix (Fin 3) (Fin 3) ℂ)
    (k₂ : Fin m₂ → Matrix (Fin 3) (Fin 3) ℂ) : ℝ :=
  (1 / 9 : ℝ) * ∑ a, ∑ b,
    (((absMat (k₂ b * absMat (k₁ a))).trace).re) ^ 2

private def crossProduct (z : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ := fun i j =>
  if i.val = 0 then
    if j.val = 0 then 0 else if j.val = 1 then -z 2 else z 1
  else if i.val = 1 then
    if j.val = 0 then z 2 else if j.val = 1 then 0 else -z 0
  else
    if j.val = 0 then -z 1 else if j.val = 1 then z 0 else 0

private def basisVector (i : Fin 3) : Fin 3 → ℂ := fun j => if j = i then 1 else 0

private def canonicalKraus (i : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  ((Real.sqrt 2)⁻¹ : ℂ) • crossProduct (basisVector i)

private def rotationVector (j : Fin 3) : Fin 3 → ℂ :=
  if j.val = 0 then ![((2 : ℂ) / 3), (2 : ℂ) / 3, (-1 : ℂ) / 3]
  else if j.val = 1 then ![((-1 : ℂ) / 3), (2 : ℂ) / 3, (2 : ℂ) / 3]
  else ![((2 : ℂ) / 3), (-1 : ℂ) / 3, (2 : ℂ) / 3]

private def rotationKraus (j : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  ((Real.sqrt 2)⁻¹ : ℂ) • crossProduct (rotationVector j)

private def quad (K : Matrix (Fin 3) (Fin 3) ℂ) (x : Fin 3 → ℂ) : ℂ :=
  dotProduct x (K *ᵥ x)

private def q (z : Fin 3 → ℂ) : ℝ := ∑ i, Complex.normSq (z i)

private def euclideanNorm (z : Fin 3 → ℂ) : ℝ := Real.sqrt (q z)

private theorem quad_identity (K : Matrix (Fin 3) (Fin 3) ℂ) (x : Fin 3 → ℂ) :
    star (star x) ⬝ᵥ ((K * Matrix.vecMulVec x (star x) * Kᴴ) *ᵥ (star x)) =
      quad K x * star (quad K x) := by
  simp only [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMulVec_mulVec]
  unfold quad Matrix.mulVec Matrix.vecMul dotProduct
  simp [Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, Finset.mul_sum,
    Finset.sum_mul, star_mul, star_sum, star_star, Fin.sum_univ_succ]
  ring

private theorem quad_sum_zero {m : ℕ} (K : Fin m → Matrix (Fin 3) (Fin 3) ℂ)
    (hK : IsKrausDecomposition K) (x : Fin 3 → ℂ) : ∑ a, ‖quad (K a) x‖ ^ 2 = 0 := by
  have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ =>
      star (star x) ⬝ᵥ (M *ᵥ (star x)))
    (hK (Matrix.vecMulVec x (star x)))
  have hleft : star (star x) ⬝ᵥ ((∑ a, K a * Matrix.vecMulVec x (star x) * (K a)ᴴ) *ᵥ (star x)) =
      ∑ a, quad (K a) x * star (quad (K a) x) := by
    rw [Matrix.sum_mulVec, dotProduct_sum]
    apply Finset.sum_congr rfl
    intro a ha
    exact quad_identity (K a) x
  rw [hleft] at he
  have hright : star (star x) ⬝ᵥ (whChannel (Matrix.vecMulVec x (star x)) *ᵥ (star x)) = 0 := by
    unfold whChannel Matrix.trace Matrix.mulVec dotProduct
    simp [Matrix.vecMulVec_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Complex.star_def,
      Complex.conj_ofReal]
    ring
  rw [hright] at he
  calc
    ∑ a, ‖quad (K a) x‖ ^ 2 = ∑ a, (quad (K a) x * star (quad (K a) x)).re := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [Complex.mul_re]
    _ = (∑ a, quad (K a) x * star (quad (K a) x)).re := by
      simpa using (map_sum (Complex.re : ℂ → ℝ)
        (fun a => quad (K a) x * star (quad (K a) x)) Finset.univ).symm
    _ = 0 := by rw [he]; norm_num

private theorem quad_zero {m : ℕ} (K : Fin m → Matrix (Fin 3) (Fin 3) ℂ)
    (hK : IsKrausDecomposition K) (x : Fin 3 → ℂ) (a : Fin m) : quad (K a) x = 0 := by
  have hs := quad_sum_zero K hK x
  have hz := (Fintype.sum_eq_zero_iff_of_nonneg (fun b =>
    sq_nonneg (‖quad (K b) x‖))).mp hs
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (congrFun hz a))

private theorem diag_zero {m : ℕ} (K : Fin m → Matrix (Fin 3) (Fin 3) ℂ)
    (hK : IsKrausDecomposition K) (a : Fin m) (i : Fin 3) : K a i i = 0 := by
  have hh := quad_zero K hK (basisVector i) a
  unfold quad Matrix.mulVec dotProduct at hh
  simpa [basisVector, Fin.sum_univ_succ] using hh

private theorem offdiag_zero {m : ℕ} (K : Fin m → Matrix (Fin 3) (Fin 3) ℂ)
    (hK : IsKrausDecomposition K) (a : Fin m) (i j : Fin 3) (hij : i ≠ j) :
    K a i j + K a j i = 0 := by
  have hh := quad_zero K hK (fun k => basisVector i k + basisVector j k) a
  unfold quad Matrix.mulVec dotProduct at hh
  fin_cases i <;> fin_cases j <;>
    simp_all [basisVector, Fin.sum_univ_succ,
      diag_zero K hK a] <;> simpa [add_comm] using hh

private theorem tp {m : ℕ} (K : Fin m → Matrix (Fin 3) (Fin 3) ℂ)
    (hK : IsKrausDecomposition K) : ∑ a, (K a)ᴴ * K a =
      (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  have he := congrArg Matrix.trace (hK (Matrix.single j i 1))
  unfold whChannel Matrix.trace at he
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.single_apply, Fin.sum_univ_succ,
      diag_zero K hK] at he ⊢ <;>
    convert he using 1 <;>
      try simp only [mul_comm, Finset.sum_add_distrib, add_assoc]
  all_goals norm_num

private theorem reprK {m : ℕ} (K : Fin m → Matrix (Fin 3) (Fin 3) ℂ)
    (hK : IsKrausDecomposition K) : ∃ z : Fin m → Fin 3 → ℂ,
      ∀ a, K a = ((Real.sqrt 2)⁻¹ : ℂ) • crossProduct (z a) := by
  let z : Fin m → Fin 3 → ℂ := fun a => (Real.sqrt 2 : ℂ) •
    ![K a 2 1, K a 0 2, K a 1 0]
  have hs : ((Real.sqrt 2 : ℂ)⁻¹) * (Real.sqrt 2 : ℂ) = 1 := by
    field_simp
  refine ⟨z, ?_⟩
  intro a
  ext i j
  have hd := diag_zero K hK a
  have h01 := offdiag_zero K hK a (0 : Fin 3) 1 (by decide)
  have h02 := offdiag_zero K hK a (0 : Fin 3) 2 (by decide)
  have h12 := offdiag_zero K hK a (1 : Fin 3) 2 (by decide)
  have h01' := eq_neg_of_add_eq_zero_left h01
  have h02' := eq_neg_of_add_eq_zero_left h02
  have h12' := eq_neg_of_add_eq_zero_left h12
  fin_cases i <;> fin_cases j <;>
    simp [z, crossProduct, hs, hd, h01, h02, h12, h01', h02', h12']

private theorem frameK {m : ℕ} (K : Fin m → Matrix (Fin 3) (Fin 3) ℂ)
    (hK : IsKrausDecomposition K) (z : Fin m → Fin 3 → ℂ)
    (hr : ∀ a, K a = ((Real.sqrt 2)⁻¹ : ℂ) • crossProduct (z a)) :
    (∑ a, (Matrix.of fun i j => z a i * star (z a j))) =
      (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  have htp := tp K hK
  simp_rw [hr] at htp
  have hs : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (1 / 2 : ℂ) := by
    have hn : ((Real.sqrt 2 : ℂ)) ≠ 0 := by norm_num
    field_simp [hn]
    norm_num [pow_two, Complex.ext_iff, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Real.sq_sqrt]
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 0 0) htp
  have h11 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 1 1) htp
  have h22 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 2 2) htp
  have h01 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 0 1) htp
  have h02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 0 2) htp
  have h12 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 1 2) htp
  simp [crossProduct, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.sum_apply, Matrix.one_apply, Fin.sum_univ_succ,
    Complex.star_def] at h00 h11 h22 h01 h02 h12
  simp only [← mul_assoc] at h00 h11 h22 h01 h02 h12
  have hs' : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    simpa [pow_two] using hs
  simp [hs'] at h00 h11 h22 h01 h02 h12
  simp only [mul_add] at h00 h11 h22
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h00
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h11
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h22
  simp_rw [← Finset.mul_sum] at h00 h11 h22
  simp_rw [mul_assoc] at h01 h02 h12
  rw [← Finset.mul_sum] at h01 h02 h12
  have hz0' : ∑ x, (starRingEnd ℂ) (z x 0) * z x 0 = 1 := by
    linear_combination h11 + h22 - h00
  have hz1' : ∑ x, (starRingEnd ℂ) (z x 1) * z x 1 = 1 := by
    linear_combination h00 + h22 - h11
  have hz2' : ∑ x, (starRingEnd ℂ) (z x 2) * z x 2 = 1 := by
    linear_combination h00 + h11 - h22
  have hz01' : ∑ x, (starRingEnd ℂ) (z x 1) * z x 0 = 0 := by
    linear_combination (2 : ℂ) * h01
  have hz02' : ∑ x, (starRingEnd ℂ) (z x 2) * z x 0 = 0 := by
    linear_combination (2 : ℂ) * h02
  have hz12' : ∑ x, (starRingEnd ℂ) (z x 2) * z x 1 = 0 := by
    linear_combination (2 : ℂ) * h12
  have hz0 : ∑ x, z x 0 * (starRingEnd ℂ) (z x 0) = 1 := by
    simpa [mul_comm] using hz0'
  have hz1 : ∑ x, z x 1 * (starRingEnd ℂ) (z x 1) = 1 := by
    simpa [mul_comm] using hz1'
  have hz2 : ∑ x, z x 2 * (starRingEnd ℂ) (z x 2) = 1 := by
    simpa [mul_comm] using hz2'
  have hz01 : ∑ x, z x 0 * (starRingEnd ℂ) (z x 1) = 0 := by
    simpa [mul_comm] using hz01'
  have hz02 : ∑ x, z x 0 * (starRingEnd ℂ) (z x 2) = 0 := by
    simpa [mul_comm] using hz02'
  have hz12 : ∑ x, z x 1 * (starRingEnd ℂ) (z x 2) = 0 := by
    simpa [mul_comm] using hz12'
  have hz10 : ∑ x, z x 1 * (starRingEnd ℂ) (z x 0) = 0 := by
    have h := congrArg star hz01
    simpa [star_sum, star_mul, star_star, mul_comm] using h
  have hz20 : ∑ x, z x 2 * (starRingEnd ℂ) (z x 0) = 0 := by
    have h := congrArg star hz02
    simpa [star_sum, star_mul, star_star, mul_comm] using h
  have hz21 : ∑ x, z x 2 * (starRingEnd ℂ) (z x 1) = 0 := by
    have h := congrArg star hz12
    simpa [star_sum, star_mul, star_star, mul_comm] using h
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [Matrix.sum_apply] using hz0
  · simpa [Matrix.sum_apply] using hz01
  · simpa [Matrix.sum_apply] using hz02
  · simpa [Matrix.sum_apply] using hz10
  · simpa [Matrix.sum_apply] using hz1
  · simpa [Matrix.sum_apply] using hz12
  · simpa [Matrix.sum_apply] using hz20
  · simpa [Matrix.sum_apply] using hz21
  · simpa [Matrix.sum_apply] using hz2

private theorem kraus_classification {m : ℕ} (K : Fin m → Matrix (Fin 3) (Fin 3) ℂ)
    (hK : IsKrausDecomposition K) :
    ∃ z : Fin m → Fin 3 → ℂ,
      (∀ a, K a = ((Real.sqrt 2)⁻¹ : ℂ) • crossProduct (z a)) ∧
        (∑ a, Matrix.of fun i j => z a i * star (z a j)) =
          (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  obtain ⟨z, hz⟩ := reprK K hK
  exact ⟨z, hz, frameK K hK z hz⟩

private theorem complement_square {n : Type} [Fintype n] [DecidableEq n]
    (c : ℂ) (V : Matrix n n ℂ) (hV : V * V = c • V) :
    (c • (1 : Matrix n n ℂ) - V) * (c • (1 : Matrix n n ℂ) - V) =
      c • (c • (1 : Matrix n n ℂ) - V) := by
  simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, hV, smul_smul]
  module

private theorem complement_scale {n : Type} [Fintype n] [DecidableEq n]
    (r c : ℂ) (hr : r ≠ 0) (hr2 : r ^ 2 = c) (V : Matrix n n ℂ) :
    r • (1 : Matrix n n ℂ) - r⁻¹ • V = r⁻¹ • (c • (1 : Matrix n n ℂ) - V) := by
  simp only [smul_sub, smul_smul]
  field_simp [hr]
  rw [← hr2]
  congr 1
  field_simp [hr]

private theorem complement_root {n : Type} [Fintype n] [DecidableEq n]
    (c : ℂ) (r : ℝ) (hrpos : 0 < r) (hr : (r : ℂ) ≠ 0) (hr2 : (r : ℂ) ^ 2 = c)
    (V : Matrix n n ℂ) (hV : V * V = c • V)
    (hpos : (c • (1 : Matrix n n ℂ) - V).PosSemidef) :
    CFC.sqrt (c • (1 : Matrix n n ℂ) - V) =
      (r : ℂ) • (1 : Matrix n n ℂ) - ((r⁻¹ : ℝ) : ℂ) • V := by
  let H := c • (1 : Matrix n n ℂ) - V
  let S := (r : ℂ) • (1 : Matrix n n ℂ) - (r : ℂ)⁻¹ • V
  have hsq : H * H = c • H := complement_square c V hV
  have hs : S = (r : ℂ)⁻¹ • H := by
    dsimp [S, H]
    exact complement_scale (r : ℂ) c hr hr2 V
  have hss : S * S = H := by
    rw [hs, Matrix.smul_mul, Matrix.mul_smul, hsq]
    have he : ((r : ℂ)⁻¹ * (r : ℂ)⁻¹) * c = 1 := by
      rw [← hr2]
      field_simp [hr]
    simp only [smul_smul]
    rw [← mul_assoc, he, one_smul]
  have hsp : S.PosSemidef := by
    rw [hs]
    apply Matrix.nonneg_iff_posSemidef.mp
    have hp := hpos.smul (show (0 : ℝ) ≤ r⁻¹ by positivity)
    have heq : (r : ℂ)⁻¹ • H = (r⁻¹ : ℝ) • H := by
      ext i j
      simp [Complex.real_smul]
    rw [heq]
    exact hp.nonneg
  have hinv : ((r⁻¹ : ℝ) : ℂ) = (r : ℂ)⁻¹ := by norm_cast
  simpa [S, hinv] using (CFC.sqrt_unique hss hsp.nonneg)

private theorem abs_crossProduct (z : Fin 3 → ℂ) :
    absMat (((Real.sqrt 2)⁻¹ : ℂ) • crossProduct z) =
      if z = 0 then 0 else
        ((Real.sqrt 2)⁻¹ : ℂ) •
          ((euclideanNorm z : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) -
            ((euclideanNorm z)⁻¹ : ℂ) • Matrix.vecMulVec z (star z)) := by
  by_cases hz : z = 0
  · subst z
    have hcp : crossProduct (0 : Fin 3 → ℂ) = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [crossProduct]
    rw [hcp]
    simp [absMat]
  · have hAA : (crossProduct z)ᴴ * crossProduct z =
        (q z : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) - Matrix.vecMulVec z (star z) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [crossProduct, q, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Matrix.vecMulVec_apply, Matrix.one_apply, Fin.sum_univ_succ,
          Complex.normSq_eq_conj_mul_self, Complex.star_def, Complex.mul_re,
          Complex.mul_im] <;> ring
    have hV : Matrix.vecMulVec z (star z) * Matrix.vecMulVec z (star z) =
        (q z : ℂ) • Matrix.vecMulVec z (star z) := by
      rw [Matrix.vecMulVec_mul_vecMulVec]
      unfold dotProduct
      ext i j
      simp [q, Matrix.vecMulVec_apply,
        Complex.normSq_eq_conj_mul_self, Complex.star_def, Fin.sum_univ_succ]
      ring
    have hq : 0 < q z := by
      dsimp [q]
      have hsum : 0 ≤ ∑ i, Complex.normSq (z i) :=
        Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
      by_contra hn
      have hzq : q z = 0 := le_antisymm (not_lt.mp hn) hsum
      have hi := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => Complex.normSq_nonneg (z i))).mp hzq
      exact hz (funext fun i => Complex.normSq_eq_zero.mp (hi i (Finset.mem_univ i)))
    have hr : (euclideanNorm z : ℂ) ≠ 0 := by
      have h : 0 < euclideanNorm z := Real.sqrt_pos.2 hq
      exact_mod_cast ne_of_gt h
    have hr2 : (euclideanNorm z : ℂ) ^ 2 = (q z : ℂ) := by
      exact_mod_cast (Real.sq_sqrt hq.le)
    have hpos : ((q z : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) -
        Matrix.vecMulVec z (star z)).PosSemidef := by
      rw [← hAA]
      exact Matrix.posSemidef_conjTranspose_mul_self _
    have hroot := complement_root (q z : ℂ) (euclideanNorm z) (Real.sqrt_pos.2 hq)
      hr hr2 (Matrix.vecMulVec z (star z)) hV hpos
    have hs := CFC.abs_smul ((Real.sqrt 2)⁻¹ : ℂ) (crossProduct z)
    change absMat (((Real.sqrt 2)⁻¹ : ℂ) • crossProduct z) =
      ‖((Real.sqrt 2)⁻¹ : ℂ)‖ • absMat (crossProduct z) at hs
    dsimp [absMat] at hs ⊢
    rw [hAA, hroot] at hs
    have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have hnorm : ‖((Real.sqrt 2)⁻¹ : ℂ)‖ = (Real.sqrt 2)⁻¹ := by
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsqrt]
    rw [hnorm] at hs
    simp only [hz, if_false]
    convert hs using 1
    ext i j
    simp [Complex.real_smul]

private theorem vec_trace (z : Fin 3 → ℂ) :
    (Matrix.vecMulVec z (star z)).trace = (q z : ℂ) := by
  rw [Matrix.trace_vecMulVec]
  unfold dotProduct
  simp only [q, Complex.normSq_eq_conj_mul_self, Complex.star_def, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Pi.star_apply, starRingEnd_apply]
  ring

private theorem vec_product_trace (w z : Fin 3 → ℂ) :
    (Matrix.vecMulVec w (star w) * Matrix.vecMulVec z (star z)).trace =
      (star w ⬝ᵥ z) * (star z ⬝ᵥ w) := by
  rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec]
  change (∑ x, w x * ((∑ y, (starRingEnd ℂ) (w y) * z y) *
      (starRingEnd ℂ) (z x))) =
    (∑ y, (starRingEnd ℂ) (w y) * z y) *
      ∑ x, (starRingEnd ℂ) (z x) * w x
  let s : ℂ := ∑ y, (starRingEnd ℂ) (w y) * z y
  have hs : ∑ x, w x * (s * (starRingEnd ℂ) (z x)) =
      s * ∑ x, (starRingEnd ℂ) (z x) * w x := by
    calc
      ∑ x, w x * (s * (starRingEnd ℂ) (z x)) =
          ∑ x, s * (w x * (starRingEnd ℂ) (z x)) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = s * ∑ x, w x * (starRingEnd ℂ) (z x) := by
        rw [Finset.mul_sum]
      _ = s * ∑ x, (starRingEnd ℂ) (z x) * w x := by
        congr 1
        apply Finset.sum_congr rfl
        intro x hx
        ring
  simpa [s] using hs

private theorem complement_trace_product (u v : ℂ)
    (V W : Matrix (Fin 3) (Fin 3) ℂ) :
    ((u • (1 : Matrix (Fin 3) (Fin 3) ℂ) - u⁻¹ • V) *
        (v • (1 : Matrix (Fin 3) (Fin 3) ℂ) - v⁻¹ • W)).trace =
      3 * u * v - u * v⁻¹ * W.trace - u⁻¹ * v * V.trace +
        u⁻¹ * v⁻¹ * (V * W).trace := by
  simp only [sub_mul, mul_sub, smul_mul, mul_smul, Matrix.one_mul,
    Matrix.mul_one, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_one, Matrix.smul_mul, Matrix.mul_smul]
  norm_num [Fintype.card_fin]
  ring

private theorem inner_product_re (w z : Fin 3 → ℂ) :
    ((star w ⬝ᵥ z) * (star z ⬝ᵥ w)).re = Complex.normSq (star w ⬝ᵥ z) := by
  have hstar : star (star w ⬝ᵥ z) = star z ⬝ᵥ w := by
    rw [star_dotProduct]
    simp
  have hnorm := congrArg Complex.re
    (Complex.normSq_eq_conj_mul_self (z := star w ⬝ᵥ z))
  rw [← RCLike.star_def] at hnorm
  rw [hstar] at hnorm
  rw [Complex.mul_re]
  have h := hnorm.symm
  rw [Complex.mul_re] at h
  simpa [Complex.ofReal_re, mul_comm] using h

private theorem q_pos {z : Fin 3 → ℂ} (hz : z ≠ 0) : 0 < q z := by
  dsimp [q]
  have hsum : 0 ≤ ∑ i, Complex.normSq (z i) :=
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  by_contra hn
  have hzq : q z = 0 := le_antisymm (not_lt.mp hn) hsum
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Complex.normSq_nonneg (z i))).mp hzq
  exact hz (funext fun i => Complex.normSq_eq_zero.mp (hi i (Finset.mem_univ i)))

private theorem abs_pair_trace (w z : Fin 3 → ℂ) (hw : w ≠ 0) (hz : z ≠ 0) :
    (absMat (((Real.sqrt 2)⁻¹ : ℂ) • crossProduct w) *
        absMat (((Real.sqrt 2)⁻¹ : ℂ) • crossProduct z)).trace =
      (1 / 2 : ℂ) *
        ((euclideanNorm w : ℂ) * (euclideanNorm z : ℂ) +
          ((star w ⬝ᵥ z) * (star z ⬝ᵥ w)) /
            ((euclideanNorm w : ℂ) * (euclideanNorm z : ℂ))) := by
  have hs : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (1 / 2 : ℂ) := by
    have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by norm_num
    field_simp [hn]
    norm_num [pow_two, Complex.ext_iff, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Real.sq_sqrt]
  have hqw : (euclideanNorm w : ℂ) ^ 2 = (q w : ℂ) := by
    exact_mod_cast (Real.sq_sqrt (show 0 ≤ q w from (q_pos hw).le))
  have hqz : (euclideanNorm z : ℂ) ^ 2 = (q z : ℂ) := by
    exact_mod_cast (Real.sq_sqrt (show 0 ≤ q z from (q_pos hz).le))
  have huw : (euclideanNorm w : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (q_pos hw)))
  have huz : (euclideanNorm z : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (q_pos hz)))
  rw [abs_crossProduct w, abs_crossProduct z]
  simp only [if_neg hw, if_neg hz]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul]
  have hs' : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = (1 / 2 : ℂ) := by
    simpa [pow_two] using hs
  rw [hs']
  rw [complement_trace_product, vec_trace, vec_trace, vec_product_trace]
  rw [← hqw, ← hqz]
  have hcancel₁ :
      (euclideanNorm w : ℂ) * (euclideanNorm z : ℂ) *
          (star w ⬝ᵥ z) * (star z ⬝ᵥ w) *
          (euclideanNorm w : ℂ)⁻¹ * (euclideanNorm z : ℂ)⁻¹ =
        (star w ⬝ᵥ z) * (star z ⬝ᵥ w) := by
    calc
      _ = ((star w ⬝ᵥ z) * (star z ⬝ᵥ w)) *
          ((euclideanNorm w : ℂ) * (euclideanNorm w : ℂ)⁻¹) *
          ((euclideanNorm z : ℂ) * (euclideanNorm z : ℂ)⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ huw, mul_inv_cancel₀ huz]; ring
  have hcancel₂ :
      (euclideanNorm w : ℂ) ^ 3 * (euclideanNorm z : ℂ) ^ 3 *
          (euclideanNorm w : ℂ)⁻¹ * (euclideanNorm z : ℂ)⁻¹ =
        (euclideanNorm w : ℂ) ^ 2 * (euclideanNorm z : ℂ) ^ 2 := by
    calc
      _ = ((euclideanNorm w : ℂ) ^ 2 * (euclideanNorm z : ℂ) ^ 2) *
          ((euclideanNorm w : ℂ) * (euclideanNorm w : ℂ)⁻¹) *
          ((euclideanNorm z : ℂ) * (euclideanNorm z : ℂ)⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ huw, mul_inv_cancel₀ huz]; ring
  field_simp [huw, huz]
  change 2 * (euclideanNorm w : ℂ) * (euclideanNorm z : ℂ) *
      ((1 / 2 : ℂ) *
        (((euclideanNorm w : ℂ) ^ 2 * (euclideanNorm z : ℂ) ^ 2 * (3 - 1 - 1) +
          (star w ⬝ᵥ z) * (star z ⬝ᵥ w)) /
          ((euclideanNorm w : ℂ) * (euclideanNorm z : ℂ)))) =
    (euclideanNorm w : ℂ) ^ 2 * (euclideanNorm z : ℂ) ^ 2 +
      (star w ⬝ᵥ z) * (star z ⬝ᵥ w)
  field_simp [huw, huz]
  ring

private theorem div_real_re (c : ℂ) (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    (c / ((x : ℂ) * (y : ℂ))).re = c.re / (x * y) := by
  simp [Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  field_simp [hx, hy]
  

private theorem inner_cauchy (w z : Fin 3 → ℂ) :
    Complex.normSq (star w ⬝ᵥ z) ≤ q w * q z := by
  let ew : EuclideanSpace ℂ (Fin 3) := (EuclideanSpace.equiv (Fin 3) ℂ).symm w
  let ez : EuclideanSpace ℂ (Fin 3) := (EuclideanSpace.equiv (Fin 3) ℂ).symm z
  have h := @inner_mul_inner_self_le ℂ (EuclideanSpace ℂ (Fin 3)) _ _ _ ew ez
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct] at h
  simp [ew, ez] at h
  have hc : z ⬝ᵥ star w = star w ⬝ᵥ z := dotProduct_comm _ _
  have hd : w ⬝ᵥ star z = star z ⬝ᵥ w := dotProduct_comm _ _
  rw [hc, hd] at h
  have hs : star (star w ⬝ᵥ z) = star z ⬝ᵥ w := by rw [star_dotProduct]; simp
  rw [← hs, norm_star] at h
  have hnormw : (↑‖WithLp.toLp 2 w‖ ^ 2 : ℂ).re = ∑ i, Complex.normSq (w i) := by
    rw [pow_two, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [← pow_two, EuclideanSpace.norm_sq_eq]
    simp only [Complex.sq_norm]
  have hnormz : (↑‖WithLp.toLp 2 z‖ ^ 2 : ℂ).re = ∑ i, Complex.normSq (z i) := by
    rw [pow_two, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [← pow_two, EuclideanSpace.norm_sq_eq]
    simp only [Complex.sq_norm]
  rw [Complex.normSq_eq_norm_sq]
  rw [hnormw, hnormz] at h
  simpa [q, pow_two] using h

private theorem abs_pair_bound (w z : Fin 3 → ℂ) :
    (((absMat (((Real.sqrt 2)⁻¹ : ℂ) • crossProduct w) *
        absMat (((Real.sqrt 2)⁻¹ : ℂ) • crossProduct z)).trace).re) ^ 2 ≤
      (q w * q z + 3 * Complex.normSq (star w ⬝ᵥ z)) / 4 := by
  by_cases hw : w = 0
  · subst w
    have hzero : ((Real.sqrt 2)⁻¹ : ℂ) • crossProduct (0 : Fin 3 → ℂ) = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [crossProduct]
    rw [hzero]
    simp [absMat, q]
  by_cases hz : z = 0
  · subst z
    have hzero : ((Real.sqrt 2)⁻¹ : ℂ) • crossProduct (0 : Fin 3 → ℂ) = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [crossProduct]
    rw [hzero]
    simp [absMat, q]
  have htrace := abs_pair_trace w z hw hz
  rw [htrace]
  simp only [Complex.mul_re, Complex.div_re]
  norm_num [Complex.normSq_apply]
  have hdiv := div_real_re (star w ⬝ᵥ z * star z ⬝ᵥ w)
    (euclideanNorm w) (euclideanNorm z)
    (ne_of_gt (Real.sqrt_pos.2 (q_pos hw)))
    (ne_of_gt (Real.sqrt_pos.2 (q_pos hz)))
  rw [hdiv, inner_product_re]
  rw [← Complex.normSq_apply]
  have hu : 0 < euclideanNorm w := Real.sqrt_pos.2 (q_pos hw)
  have hv : 0 < euclideanNorm z := Real.sqrt_pos.2 (q_pos hz)
  have hqw : q w = euclideanNorm w ^ 2 := by
    exact (Real.sq_sqrt (q_pos hw).le).symm
  have hqz : q z = euclideanNorm z ^ 2 := by
    exact (Real.sq_sqrt (q_pos hz).le).symm
  have hc : Complex.normSq (star w ⬝ᵥ z) ≤
      euclideanNorm w ^ 2 * euclideanNorm z ^ 2 := by
    simpa [hqw, hqz] using inner_cauchy w z
  have huv : 0 < euclideanNorm w * euclideanNorm z := mul_pos hu hv
  have hcy : Complex.normSq (star w ⬝ᵥ z) /
      (euclideanNorm w * euclideanNorm z) ≤
      euclideanNorm w * euclideanNorm z := by
    apply (div_le_iff₀ huv).2
    nlinarith [hc]
  have hcn : 0 ≤ Complex.normSq (star w ⬝ᵥ z) /
      (euclideanNorm w * euclideanNorm z) :=
    div_nonneg (Complex.normSq_nonneg _) huv.le
  have hrel : (euclideanNorm w * euclideanNorm z) *
      (Complex.normSq (star w ⬝ᵥ z) /
        (euclideanNorm w * euclideanNorm z)) =
      Complex.normSq (star w ⬝ᵥ z) := by
    field_simp [ne_of_gt huv]
  have hsquare :
      (euclideanNorm w * euclideanNorm z +
        Complex.normSq (star w ⬝ᵥ z) /
          (euclideanNorm w * euclideanNorm z)) ^ 2 ≤
      (euclideanNorm w * euclideanNorm z) ^ 2 +
        3 * Complex.normSq (star w ⬝ᵥ z) := by
    nlinarith [sq_nonneg (euclideanNorm w * euclideanNorm z -
      Complex.normSq (star w ⬝ᵥ z) /
        (euclideanNorm w * euclideanNorm z)), hrel]
  nlinarith [hsquare]

private theorem frame_q_sum {m : ℕ} (z : Fin m → Fin 3 → ℂ)
    (hframe : (∑ a, (Matrix.of fun i j => z a i * star (z a j))) =
      (1 : Matrix (Fin 3) (Fin 3) ℂ)) : ∑ a, q (z a) = 3 := by
  have htr := congrArg Matrix.trace hframe
  rw [Matrix.trace_sum] at htr
  change (∑ a, (Matrix.vecMulVec (z a) (star (z a))).trace) =
      (1 : Matrix (Fin 3) (Fin 3) ℂ).trace at htr
  simp_rw [Matrix.trace_vecMulVec] at htr
  rw [Matrix.trace_one] at htr
  have htrr := congrArg Complex.re htr
  unfold dotProduct at htrr
  simp [Complex.normSq_eq_conj_mul_self, Complex.star_def] at htrr
  exact_mod_cast htrr

private theorem frame_inner_sum {m₁ m₂ : ℕ} (z : Fin m₁ → Fin 3 → ℂ)
    (w : Fin m₂ → Fin 3 → ℂ)
    (hz : (∑ a, (Matrix.of fun i j => z a i * star (z a j))) =
      (1 : Matrix (Fin 3) (Fin 3) ℂ))
    (hw : (∑ b, (Matrix.of fun i j => w b i * star (w b j))) =
      (1 : Matrix (Fin 3) (Fin 3) ℂ)) :
    ∑ a, ∑ b, Complex.normSq (star (w b) ⬝ᵥ z a) = 3 := by
  have hrow (v : Fin 3 → ℂ) :
      ∑ b, Complex.normSq (star (w b) ⬝ᵥ v) = q v := by
    have hc : ∑ b, (star (w b) ⬝ᵥ v) * (star v ⬝ᵥ w b) = (q v : ℂ) := by
      calc
        _ = ∑ b, (Matrix.vecMulVec (w b) (star (w b)) *
            Matrix.vecMulVec v (star v)).trace := by
              simp_rw [vec_product_trace]
        _ = ((∑ b, Matrix.vecMulVec (w b) (star (w b))) *
            Matrix.vecMulVec v (star v)).trace := by
              rw [Matrix.sum_mul, Matrix.trace_sum]
        _ = (q v : ℂ) := by
          change ((∑ b, Matrix.of fun i j => w b i * star (w b j)) *
            Matrix.vecMulVec v (star v)).trace = (q v : ℂ)
          rw [hw, Matrix.one_mul, vec_trace]
    have hre := congrArg Complex.re hc
    rw [Complex.re_sum] at hre
    simpa only [inner_product_re, Complex.ofReal_re] using hre
  simp_rw [hrow]
  exact frame_q_sum z hz

private theorem markov_bound {m₁ m₂ : ℕ} (K₁ : Fin m₁ → Matrix (Fin 3) (Fin 3) ℂ)
    (K₂ : Fin m₂ → Matrix (Fin 3) (Fin 3) ℂ)
    (h₁ : IsKrausDecomposition K₁) (h₂ : IsKrausDecomposition K₂) :
    markovFidelity K₁ K₂ ≤ 1 / 2 := by
  obtain ⟨z, hrz, hfz⟩ := kraus_classification K₁ h₁
  obtain ⟨w, hrw, hfw⟩ := kraus_classification K₂ h₂
  have hqz := frame_q_sum z hfz
  have hqw := frame_q_sum w hfw
  have hinner := frame_inner_sum z w hfz hfw
  have hprod : ∑ a, ∑ b, q (w b) * q (z a) = 9 := by
    simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
    rw [hqw, hqz]
    norm_num
  unfold markovFidelity
  simp_rw [hrz, hrw]
  calc
    _ ≤ (1 / 9 : ℝ) * ∑ a, ∑ b,
        (q (w b) * q (z a) + 3 * Complex.normSq (star (w b) ⬝ᵥ z a)) / 4 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
        abs_pair_bound (w b) (z a)
    _ = 1 / 2 := by
      have he : (∑ a, ∑ b,
          (q (w b) * q (z a) + 3 * Complex.normSq (star (w b) ⬝ᵥ z a)) / 4) =
          ((∑ a, ∑ b, q (w b) * q (z a)) +
            3 * (∑ a, ∑ b, Complex.normSq (star (w b) ⬝ᵥ z a))) / 4 := by
        simp only [div_eq_mul_inv, Finset.sum_add_distrib, Finset.sum_mul,
          Finset.mul_sum, add_mul]
      rw [he, hprod, hinner]
      norm_num

private theorem canonical_is_kraus : IsKrausDecomposition canonicalKraus := by
  have hs : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (1 / 2 : ℂ) := by
    have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by norm_num
    field_simp [hn]
    norm_num [pow_two, Complex.ext_iff, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Real.sq_sqrt]
  intro X
  unfold whChannel Matrix.trace
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [canonicalKraus, crossProduct, basisVector,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
      Fin.sum_univ_succ] <;>
    simp only [← mul_assoc, ← pow_two, hs] <;> ring

private theorem rotation_is_kraus : IsKrausDecomposition rotationKraus := by
  have hs : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (1 / 2 : ℂ) := by
    have hn : ((Real.sqrt 2 : ℂ)) ≠ 0 := by norm_num
    field_simp [hn]
    norm_num [pow_two, Complex.ext_iff, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Real.sq_sqrt]
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    rw [← Complex.star_def]
    norm_num
  have h3 : (starRingEnd ℂ) (3 : ℂ) = 3 := by
    rw [← Complex.star_def]
    norm_num
  intro X
  unfold whChannel Matrix.trace
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotationKraus, rotationVector, crossProduct,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
      Fin.sum_univ_succ, Complex.conj_ofReal, h2, h3] <;>
    simp only [← mul_assoc, ← pow_two, hs] <;> ring

private theorem abs_canonical (i : Fin 3) :
    absMat (canonicalKraus i) = ((Real.sqrt 2)⁻¹ : ℂ) •
      ((1 : Matrix (Fin 3) (Fin 3) ℂ) - Matrix.single i i 1) := by
  have hb : basisVector i ≠ 0 := by
    intro h
    have hi := congrFun h i
    simp [basisVector] at hi
  have hn : euclideanNorm (basisVector i) = 1 := by
    fin_cases i <;> norm_num [euclideanNorm, q, basisVector, Fin.sum_univ_succ]
  have hv : Matrix.vecMulVec (basisVector i) (star (basisVector i)) =
      Matrix.single i i 1 := by
    ext a b
    fin_cases i <;> fin_cases a <;> fin_cases b <;>
      norm_num [basisVector, Matrix.vecMulVec_apply, Matrix.single_apply]
  unfold canonicalKraus
  rw [abs_crossProduct]
  simp only [if_neg hb, hn, Complex.ofReal_one, inv_one, one_smul, hv]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem bayes_pair_trace (i j : Fin 3) :
    (absMat (rotationKraus j * absMat (canonicalKraus i))).trace.re =
      (1 + |(rotationVector j i).re|) / 2 := by
  let p : Matrix (Fin 3) (Fin 3) ℂ := 1 - Matrix.single i i 1
  let b := crossProduct (rotationVector j) * p
  let s : ℝ := |(rotationVector j i).re|
  let root : Matrix (Fin 3) (Fin 3) ℂ :=
    (s / (2 * (1 + s))) • p + (1 / (2 * (1 + s))) • (bᴴ * b)
  have hp : p.PosSemidef := by
    have he : pᴴ * p = p := by
      simp [p, sub_mul, mul_sub]
    rw [← he]
    exact Matrix.posSemidef_conjTranspose_mul_self p
  have hsn : 0 ≤ s := abs_nonneg _
  have hpos : root.PosSemidef := by
    exact (hp.smul (show (0 : ℝ) ≤ s / (2 * (1 + s)) by positivity)).add
      ((Matrix.posSemidef_conjTranspose_mul_self b).smul
        (show (0 : ℝ) ≤ 1 / (2 * (1 + s)) by positivity))
  have hsq : root * root = ((1 / 2 : ℂ) • b)ᴴ * ((1 / 2 : ℂ) • b) := by
    ext a c
    fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases c <;>
      norm_num [root, b, p, s, rotationVector, crossProduct, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.single_apply, Matrix.one_apply, Fin.sum_univ_succ,
        Complex.real_smul, Complex.ext_iff, Complex.mul_re, Complex.mul_im,
        Complex.div_re, Complex.div_im, Complex.normSq_apply]
  have ht : root.trace.re = (1 + s) / 2 := by
    change (∑ k, root k k).re = (1 + s) / 2
    fin_cases i <;> fin_cases j <;>
      norm_num [root, b, p, s, rotationVector, crossProduct, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.single_apply, Matrix.one_apply, Fin.sum_univ_succ,
        Complex.real_smul, Complex.mul_re, Complex.mul_im,
        Complex.div_re, Complex.div_im, Complex.normSq_apply]
  have hs : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = (1 / 2 : ℂ) := by
    have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by norm_num
    field_simp [hn]
    norm_num [pow_two, Complex.ext_iff, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Real.sq_sqrt]
  have hm : rotationKraus j * absMat (canonicalKraus i) = (1 / 2 : ℂ) • b := by
    rw [abs_canonical]
    simp only [rotationKraus, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    change ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) • b = (1 / 2 : ℂ) • b
    rw [hs]
  have hr : absMat ((1 / 2 : ℂ) • b) = root := CFC.sqrt_unique hsq hpos.nonneg
  rw [hm, hr]
  exact ht

private theorem bayesian_witness : 1 / 2 < bayesFidelity canonicalKraus rotationKraus := by
  have he : bayesFidelity canonicalKraus rotationKraus = 11 / 18 := by
    unfold bayesFidelity
    simp_rw [bayes_pair_trace]
    norm_num [rotationVector, Fin.sum_univ_succ, Complex.div_re,
      Complex.div_im, Complex.normSq_apply]
  rw [he]
  norm_num

/-- For the unital Matrix (Fin 3) (Fin 3) ℂ Werner--Holevo channel, every Markovian value is at most
`1/2`, while the canonical/rational-rotation Kraus pair has Bayesian value above `1/2`.
This answers the source's request with a unital channel, hence not an amplitude
damping channel. -/
theorem result :
    (∀ (m₁ m₂ : ℕ) (k₁ : Fin m₁ → Matrix (Fin 3) (Fin 3) ℂ)
      (k₂ : Fin m₂ → Matrix (Fin 3) (Fin 3) ℂ),
      IsKrausDecomposition k₁ → IsKrausDecomposition k₂ →
        markovFidelity k₁ k₂ ≤ 1 / 2) ∧
    (∃ l₁ : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ, ∃ l₂ : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ,
      IsKrausDecomposition l₁ ∧ IsKrausDecomposition l₂ ∧
        1 / 2 < bayesFidelity l₁ l₂) := by
  constructor
  · intro m₁ m₂ k₁ k₂ h₁ h₂
    exact markov_bound k₁ k₂ h₁ h₂
  · exact ⟨canonicalKraus, rotationKraus, canonical_is_kraus, rotation_is_kraus,
      bayesian_witness⟩

end D5.S3.Quantum.Recovery.WernerHolevoBayesianFeedbackAdvantage
