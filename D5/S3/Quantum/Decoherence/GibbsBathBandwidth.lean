/- GID: D5/S3/Quantum/Decoherence/GibbsBathBandwidth
   generality: G
   mirror-B: D5/B/S3/Quantum/Decoherence/GibbsBathBandwidth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp spectral bandwidth for finite Gibbs-bath preparation of a positive record state. -/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Information.CorrelatedGibbsEnergyIdentity
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Minimum Gibbs bandwidth in the reduced erasure orbit

The joint basis is ordered bath first, memory second. The input in this
reduction is the tensor product of the bath and the maximally mixed memory.
-/

set_option autoImplicit false

namespace GibbsBathBandwidth

open Matrix Unitary
open scoped Matrix ComplexOrder MatrixOrder Kronecker
open D5.S3.Quantum.Information.PartialTraceMutualInformation

noncomputable section

variable {M B I : Type*} [Fintype M] [DecidableEq M] [Nonempty M]
  [Fintype B] [DecidableEq B] [Nonempty B] [Fintype I] [DecidableEq I] [Nonempty I]

/-- The extreme values of a real vector on a nonempty finite basis. -/
def minValue (p : I → ℝ) : ℝ :=
  (Finset.univ.image p).min' (Finset.univ_nonempty.image p)

def maxValue (p : I → ℝ) : ℝ :=
  (Finset.univ.image p).max' (Finset.univ_nonempty.image p)

omit [DecidableEq I] in
theorem minValue_le (p : I → ℝ) (i : I) : minValue p ≤ p i :=
  Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))

omit [DecidableEq I] in
theorem le_maxValue (p : I → ℝ) (i : I) : p i ≤ maxValue p :=
  Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))

omit [DecidableEq I] in
theorem minValue_attained (p : I → ℝ) : ∃ i, p i = minValue p := by
  simpa only [minValue, maxValue, Finset.mem_image, Finset.mem_univ, true_and] using
    Finset.min'_mem (Finset.univ.image p) (Finset.univ_nonempty.image p)

omit [DecidableEq I] in
theorem maxValue_attained (p : I → ℝ) : ∃ i, p i = maxValue p := by
  simpa only [minValue, maxValue, Finset.mem_image, Finset.mem_univ, true_and] using
    Finset.max'_mem (Finset.univ.image p) (Finset.univ_nonempty.image p)

def energyWidth (E : I → ℝ) : ℝ := maxValue E - minValue E

def gibbsWeight (β : ℝ) (E : I → ℝ) (i : I) : ℝ :=
  Real.exp (-β * E i) / ∑ j, Real.exp (-β * E j)

omit [DecidableEq I] in
private theorem partition_pos (β : ℝ) (E : I → ℝ) :
    0 < ∑ j, Real.exp (-β * E j) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

omit [DecidableEq I] in
theorem gibbsWeight_pos (β : ℝ) (E : I → ℝ) (i : I) :
    0 < gibbsWeight β E i :=
  div_pos (Real.exp_pos _) (partition_pos β E)

omit [DecidableEq I] in
theorem sum_gibbsWeight (β : ℝ) (E : I → ℝ) : ∑ i, gibbsWeight β E i = 1 := by
  simp only [gibbsWeight]
  rw [← Finset.sum_div, div_self (partition_pos β E).ne']

omit [DecidableEq I] in
private theorem gibbsWeight_antitone {β : ℝ} (hβ : 0 < β) (E : I → ℝ)
    {i j : I} (h : E i ≤ E j) : gibbsWeight β E j ≤ gibbsWeight β E i := by
  apply div_le_div_of_nonneg_right _ (partition_pos β E).le
  exact Real.exp_le_exp.mpr (by nlinarith)

def diagonalReal (p : I → ℝ) : Matrix I I ℂ := diagonal (fun i => (p i : ℂ))

def mixed (I : Type*) [Fintype I] [DecidableEq I] : Matrix I I ℂ :=
  ((Fintype.card I : ℝ)⁻¹ : ℝ) • 1

/-- Matrix Gibbs state in the basis given by the columns of `V`. -/
def gibbsBath (β : ℝ) (E : B → ℝ) (V : unitary (Matrix B B ℂ)) : Matrix B B ℂ :=
  conjStarAlgAut ℂ _ V (diagonalReal (gibbsWeight β E))

/-- A unitary orbit element with the required memory marginal. -/
def Retains (τ : Matrix B B ℂ) (ρ : Matrix M M ℂ)
    (U : unitary (Matrix (B × M) (B × M) ℂ)) : Prop :=
  partialTraceLeft (conjStarAlgAut ℂ _ U (τ ⊗ₖ mixed M)) = ρ

omit [Nonempty I] in
private theorem conj_le_conj_iff (U : unitary (Matrix I I ℂ)) (A C : Matrix I I ℂ) :
    conjStarAlgAut ℂ _ U A ≤ conjStarAlgAut ℂ _ U C ↔ A ≤ C := by
  have hU : IsUnit (U : Matrix I I ℂ) := isUnit_coe
  have h := hU.posSemidef_star_right_conjugate_iff (x := C - A)
  rw [Matrix.le_iff, Matrix.le_iff, ← map_sub, conjStarAlgAut_apply]
  exact h

omit [Nonempty I] in
private theorem conj_scalar (U : unitary (Matrix I I ℂ)) (r : ℝ) :
    conjStarAlgAut ℂ _ U (r • (1 : Matrix I I ℂ)) = r • (1 : Matrix I I ℂ) := by
  change (conjStarAlgAut ℂ _ U) ((r : ℂ) • (1 : Matrix I I ℂ)) = _
  rw [map_smul, map_one]
  rfl

omit [Fintype I] [Nonempty I] in
private theorem diagonalReal_le_iff (p q : I → ℝ) :
    diagonalReal p ≤ diagonalReal q ↔ ∀ i, p i ≤ q i := by
  rw [Matrix.le_iff, diagonalReal, diagonalReal, diagonal_sub, posSemidef_diagonal_iff]
  simp [← Complex.ofReal_sub, Complex.nonneg_iff, sub_nonneg]

omit [Fintype I] [Nonempty I] in
private theorem diagonalReal_const (r : ℝ) :
    diagonalReal (fun _ : I => r) = r • (1 : Matrix I I ℂ) := by
  calc
    diagonalReal (fun _ : I => r) = diagonal (r • (fun _ : I => (1 : ℂ))) := by
      unfold diagonalReal
      apply congrArg diagonal
      funext i
      simp [Pi.smul_apply, Complex.real_smul]
    _ = _ := by rw [diagonal_smul, diagonal_one]

omit [Nonempty B] [Nonempty M] [Fintype M] [DecidableEq M] [DecidableEq B] in
private theorem partialTraceLeft_mono {A C : Matrix (B × M) (B × M) ℂ}
    (h : A ≤ C) : partialTraceLeft A ≤ partialTraceLeft C := by
  have heq : partialTraceLeft (C - A) = partialTraceLeft C - partialTraceLeft A := by
    apply eq_sub_of_add_eq
    rw [← partialTraceLeft_add, sub_add_cancel]
  rw [Matrix.le_iff, ← heq]
  exact partialTraceLeft_posSemidef (Matrix.le_iff.mp h)

omit [Nonempty B] [Nonempty M] [Fintype M] in
private theorem partialTraceLeft_scalar (r : ℝ) :
    partialTraceLeft (r • (1 : Matrix (B × M) (B × M) ℂ)) =
      ((Fintype.card B : ℝ) * r) • (1 : Matrix M M ℂ) := by
  rw [← one_kronecker_one, ← smul_kronecker]
  change partialTraceLeft (Matrix.kronecker (r • (1 : Matrix B B ℂ)) (1 : Matrix M M ℂ)) = _
  rw [partialTraceLeft_kronecker, trace_smul, trace_one]
  change ((r : ℂ) * (Fintype.card B : ℂ)) • (1 : Matrix M M ℂ) = _
  rw [mul_comm]
  change _ = (((Fintype.card B : ℝ) * r : ℝ) : ℂ) • (1 : Matrix M M ℂ)
  push_cast
  rfl

omit [Nonempty M] [Fintype B] [Nonempty B] in
private theorem diagonalReal_kronecker_mixed (p : B → ℝ) :
    diagonalReal p ⊗ₖ mixed M =
      diagonalReal (fun ij : B × M => p ij.1 * (Fintype.card M : ℝ)⁻¹) := by
  rw [mixed, ← diagonalReal_const, diagonalReal, diagonalReal, diagonalReal,
    diagonal_kronecker_diagonal]
  simp [Complex.ofReal_mul]

omit [Nonempty M] in
private def bathUnitary (V : unitary (Matrix B B ℂ)) :
    unitary (Matrix (B × M) (B × M) ℂ) :=
  ⟨(V : Matrix B B ℂ) ⊗ₖ (1 : Matrix M M ℂ), mem_iff.mpr (by
    let A : Matrix B B ℂ := V
    let C : Matrix M M ℂ := 1
    change (A ⊗ₖ C)ᴴ * (A ⊗ₖ C) = 1 ∧ (A ⊗ₖ C) * (A ⊗ₖ C)ᴴ = 1
    rw [conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul]
    simp [A, C, ← Matrix.star_eq_conjTranspose])⟩

omit [Nonempty M] [Nonempty B] in
private theorem conj_bathUnitary (V : unitary (Matrix B B ℂ)) (A : Matrix B B ℂ)
    (C : Matrix M M ℂ) :
    conjStarAlgAut ℂ (Matrix (B × M) (B × M) ℂ) (bathUnitary (M := M) V) (A ⊗ₖ C) =
      (conjStarAlgAut ℂ (Matrix B B ℂ) V A) ⊗ₖ C := by
  let W : Matrix B B ℂ := V
  let J : Matrix M M ℂ := 1
  simp only [conjStarAlgAut_apply]
  change (W ⊗ₖ J) * (A ⊗ₖ C) * (W ⊗ₖ J)ᴴ = (W * A * Wᴴ) ⊗ₖ C
  rw [conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul]
  simp [J]

/-- Partial tracing a unitary orbit element bounds the marginal between the scaled
least and greatest Boltzmann weights. -/
theorem marginal_bounds {β : ℝ} (hβ : 0 < β) (E : B → ℝ)
    (V : unitary (Matrix B B ℂ)) (ρ : Matrix M M ℂ)
    (U : unitary (Matrix (B × M) (B × M) ℂ)) (hU : Retains (gibbsBath β E V) ρ U)
    {iMin iMax : B} (hiMin : E iMin = minValue E) (hiMax : E iMax = maxValue E) :
    (((Fintype.card B : ℝ) * (gibbsWeight β E iMax * (Fintype.card M : ℝ)⁻¹)) •
      (1 : Matrix M M ℂ) ≤ ρ) ∧
    (ρ ≤ ((Fintype.card B : ℝ) * (gibbsWeight β E iMin * (Fintype.card M : ℝ)⁻¹)) •
      (1 : Matrix M M ℂ)) := by
  have hinv : 0 ≤ (Fintype.card M : ℝ)⁻¹ := by positivity
  have htrace (r : ℝ) := partialTraceLeft_scalar (B := B) (M := M) r
  unfold Retains gibbsBath at hU
  rw [← conj_bathUnitary, ← conjStarAlgAut_mul_apply, diagonalReal_kronecker_mixed] at hU
  let W := U * bathUnitary (M := M) V
  let q : B × M → ℝ := fun ij => gibbsWeight β E ij.1 * (Fintype.card M : ℝ)⁻¹
  have hlo : (gibbsWeight β E iMax * (Fintype.card M : ℝ)⁻¹) •
      (1 : Matrix (B × M) (B × M) ℂ) ≤ diagonalReal q := by
    rw [← diagonalReal_const, diagonalReal_le_iff]
    intro ij
    have h : E ij.1 ≤ E iMax := hiMax ▸ le_maxValue E ij.1
    exact mul_le_mul_of_nonneg_right (gibbsWeight_antitone hβ E h) hinv
  have hhi : diagonalReal q ≤ (gibbsWeight β E iMin * (Fintype.card M : ℝ)⁻¹) •
      (1 : Matrix (B × M) (B × M) ℂ) := by
    rw [← diagonalReal_const, diagonalReal_le_iff]
    intro ij
    have h : E iMin ≤ E ij.1 := hiMin ▸ minValue_le E ij.1
    exact mul_le_mul_of_nonneg_right (gibbsWeight_antitone hβ E h) hinv
  have hlo' := (conj_le_conj_iff W _ _).2 hlo
  have hhi' := (conj_le_conj_iff W _ _).2 hhi
  change partialTraceLeft (conjStarAlgAut ℂ _ W (diagonalReal q)) = ρ at hU
  rw [conj_scalar] at hlo' hhi'
  constructor
  · simpa only [htrace, hU] using partialTraceLeft_mono hlo'
  · simpa only [htrace, hU] using partialTraceLeft_mono hhi'

omit [Nonempty M] in
theorem scalar_le_iff_eigenvalues {ρ : Matrix M M ℂ} (hρ : ρ.IsHermitian) (a : ℝ) :
    a • (1 : Matrix M M ℂ) ≤ ρ ↔ ∀ i, a ≤ hρ.eigenvalues i := by
  have hd : ρ = conjStarAlgAut ℂ _ hρ.eigenvectorUnitary
      (diagonalReal hρ.eigenvalues) := hρ.spectral_theorem
  conv_lhs => arg 2; rw [hd]
  rw [← conj_scalar hρ.eigenvectorUnitary a, conj_le_conj_iff, ← diagonalReal_const,
    diagonalReal_le_iff]

omit [Nonempty M] in
theorem le_scalar_iff_eigenvalues {ρ : Matrix M M ℂ} (hρ : ρ.IsHermitian) (a : ℝ) :
    ρ ≤ a • (1 : Matrix M M ℂ) ↔ ∀ i, hρ.eigenvalues i ≤ a := by
  have hd : ρ = conjStarAlgAut ℂ _ hρ.eigenvectorUnitary
      (diagonalReal hρ.eigenvalues) := hρ.spectral_theorem
  conv_lhs => arg 1; rw [hd]
  rw [← conj_scalar hρ.eigenvectorUnitary a, conj_le_conj_iff, ← diagonalReal_const,
    diagonalReal_le_iff]

def requiredWidth (β : ℝ) {ρ : Matrix M M ℂ} (hρ : ρ.PosDef) : ℝ :=
  β⁻¹ * Real.log (maxValue hρ.isHermitian.eigenvalues / minValue hρ.isHermitian.eigenvalues)

omit [DecidableEq B] in
private theorem gibbs_ratio {β : ℝ} (E : B → ℝ) (i j : B) :
    gibbsWeight β E i / gibbsWeight β E j = Real.exp (β * (E j - E i)) := by
  unfold gibbsWeight
  rw [div_div_div_cancel_right₀ (partition_pos β E).ne', ← Real.exp_sub]
  congr 1
  ring

/-- The lower bound holds for every finite nonempty bath dimension and every
energy basis. The same order bound gives a necessary bath dimension. -/
theorem bandwidth_lower_bound {β : ℝ} (hβ : 0 < β) (E : B → ℝ)
    (V : unitary (Matrix B B ℂ)) {ρ : Matrix M M ℂ} (hρ : ρ.PosDef)
    (U : unitary (Matrix (B × M) (B × M) ℂ)) (hU : Retains (gibbsBath β E V) ρ U) :
    requiredWidth β hρ ≤ energyWidth E ∧
      (Fintype.card M : ℝ) * maxValue hρ.isHermitian.eigenvalues ≤ Fintype.card B := by
  obtain ⟨i, hi⟩ := minValue_attained E
  obtain ⟨j, hj⟩ := maxValue_attained E
  obtain ⟨lo, hlo⟩ := minValue_attained hρ.isHermitian.eigenvalues
  obtain ⟨hiIndex, hhi⟩ := maxValue_attained hρ.isHermitian.eigenvalues
  have horder := marginal_bounds hβ E V ρ U hU hi hj
  have hlow := (scalar_le_iff_eigenvalues hρ.isHermitian _).mp horder.1 lo
  have hhigh := (le_scalar_iff_eigenvalues hρ.isHermitian _).mp horder.2 hiIndex
  rw [hlo] at hlow
  rw [hhi] at hhigh
  have hM : 0 < (Fintype.card M : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hB : 0 < (Fintype.card B : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hmin : 0 < minValue hρ.isHermitian.eigenvalues := hlo ▸ hρ.eigenvalues_pos lo
  have hmax : 0 < maxValue hρ.isHermitian.eigenvalues := hhi ▸ hρ.eigenvalues_pos hiIndex
  have hτ : 0 < gibbsWeight β E j := gibbsWeight_pos β E j
  constructor
  · have hscale : 0 < (Fintype.card B : ℝ) * (Fintype.card M : ℝ)⁻¹ := by positivity
    have hratio : maxValue hρ.isHermitian.eigenvalues / minValue hρ.isHermitian.eigenvalues
        ≤ gibbsWeight β E i / gibbsWeight β E j := by
      have h₁ := div_le_div_of_nonneg_right hhigh hmin.le
      have h₂ := div_le_div_of_nonneg_left
        (mul_nonneg hscale.le (gibbsWeight_pos β E i).le)
        (mul_pos hscale hτ) (by simpa only [mul_left_comm, mul_comm, mul_assoc] using hlow)
      rw [show (Fintype.card B : ℝ) * (gibbsWeight β E i * (Fintype.card M : ℝ)⁻¹) =
        ((Fintype.card B : ℝ) * (Fintype.card M : ℝ)⁻¹) * gibbsWeight β E i by ring] at h₁
      exact (h₁.trans h₂).trans_eq (mul_div_mul_left _ _ hscale.ne')
    have hw := Real.log_le_log (div_pos hmax hmin) hratio
    rw [gibbs_ratio E i j, Real.log_exp, hi, hj] at hw
    unfold requiredWidth energyWidth
    rw [← div_eq_inv_mul]
    exact (div_le_iff₀ hβ).2 (by simpa only [mul_comm] using hw)
  · have hτle : gibbsWeight β E i ≤ 1 := by
      rw [← sum_gibbsWeight β E]
      exact Finset.single_le_sum (fun k _ => (gibbsWeight_pos β E k).le) (Finset.mem_univ i)
    have h := mul_le_mul_of_nonneg_right hhigh hM.le
    have hcancel : (Fintype.card M : ℝ)⁻¹ * Fintype.card M = 1 :=
      inv_mul_cancel₀ hM.ne'
    rw [mul_assoc, mul_assoc, hcancel, mul_one] at h
    rw [mul_comm] at h
    exact h.trans (by simpa using mul_le_mul_of_nonneg_left hτle hB.le)

omit [DecidableEq I] in
theorem minValue_eq {p : I → ℝ} (i : I) (h : ∀ j, p i ≤ p j) : minValue p = p i := by
  obtain ⟨j, hj⟩ := minValue_attained p
  exact le_antisymm (minValue_le p i) (hj ▸ h j)

omit [DecidableEq I] in
theorem maxValue_eq {p : I → ℝ} (i : I) (h : ∀ j, p j ≤ p i) : maxValue p = p i := by
  obtain ⟨j, hj⟩ := maxValue_attained p
  exact le_antisymm (hj ▸ h j) (le_maxValue p i)

omit [Nonempty M] in
/-- The tensor swap is the permutation matrix of `(i,j) ↦ (j,i)`. -/
def tensorSwap : unitary (Matrix (M × M) (M × M) ℂ) :=
  let σ : Equiv.Perm (M × M) := Equiv.prodComm M M
  ⟨σ.permMatrix ℂ, mem_iff.mpr (by
    rw [Matrix.star_eq_conjTranspose, conjTranspose_permMatrix, ← permMatrix_mul,
      ← permMatrix_mul, mul_inv_cancel, inv_mul_cancel, permMatrix_one]
    exact ⟨rfl, rfl⟩)⟩

omit [Nonempty M] in
theorem tensorSwap_conj (A C : Matrix M M ℂ) :
    conjStarAlgAut ℂ _ (tensorSwap (M := M)) (A ⊗ₖ C) = C ⊗ₖ A := by
  let σ : Equiv.Perm (M × M) := Equiv.prodComm M M
  rw [conjStarAlgAut_apply]
  change σ.permMatrix ℂ * (A ⊗ₖ C) * (σ.permMatrix ℂ)ᴴ = _
  rw [conjTranspose_permMatrix]
  ext i j
  have hleft (k : M × M) : (σ.permMatrix ℂ * (A ⊗ₖ C)) i k = (A ⊗ₖ C) (σ i) k := by
    rw [Matrix.mul_apply]
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  rw [Matrix.mul_apply]
  simp only [hleft]
  have hentry (k : M × M) : (σ⁻¹).permMatrix ℂ k j = if k = σ j then 1 else 0 := by
    simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.Perm.inv_def,
      Equiv.toPEquiv_apply, Option.mem_some_iff]
    congr 1
    exact propext (σ.symm_apply_eq)
  simp only [hentry, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rcases i with ⟨i, i'⟩
  rcases j with ⟨j, j'⟩
  exact mul_comm (A i' j') (C i j)

theorem trace_mixed : (mixed M).trace = 1 := by
  have hn : (Fintype.card M : ℝ) ≠ 0 := (Nat.cast_pos.mpr Fintype.card_pos).ne'
  rw [mixed, trace_smul, trace_one, Complex.real_smul, ← Complex.ofReal_natCast,
    ← Complex.ofReal_mul, inv_mul_cancel₀ hn, Complex.ofReal_one]

def matchingEnergies (β : ℝ) (p : I → ℝ) (i : I) : ℝ :=
  -β⁻¹ * Real.log (p i)

omit [DecidableEq I] [Nonempty I] in
private theorem gibbsWeight_matching {β : ℝ} (hβ : 0 < β) (p : I → ℝ)
    (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) :
    gibbsWeight β (matchingEnergies β p) = p := by
  have hexp (i : I) : Real.exp (-β * matchingEnergies β p i) = p i := by
    rw [matchingEnergies, ← mul_assoc, neg_mul_neg, mul_inv_cancel₀ hβ.ne',
      one_mul, Real.exp_log (hp i)]
  funext i
  simp only [gibbsWeight, hexp, hsum, div_one]

omit [DecidableEq I] in
private theorem matchingEnergies_width {β : ℝ} (hβ : 0 < β)
    (p : I → ℝ) (hp : ∀ i, 0 < p i) :
    energyWidth (matchingEnergies β p) = β⁻¹ * Real.log (maxValue p / minValue p) := by
  obtain ⟨i, hi⟩ := minValue_attained p
  obtain ⟨j, hj⟩ := maxValue_attained p
  have hanti {k l : I} (hkl : p k ≤ p l) : matchingEnergies β p l ≤ matchingEnergies β p k :=
    mul_le_mul_of_nonpos_left (Real.log_le_log (hp k) hkl) (neg_nonpos.mpr (inv_nonneg.mpr hβ.le))
  rw [energyWidth, maxValue_eq i (fun k => hanti (hi ▸ minValue_le p k)),
    minValue_eq j (fun k => hanti (hj ▸ le_maxValue p k)), ← hi, ← hj,
    Real.log_div (hp j).ne' (hp i).ne', matchingEnergies, matchingEnergies]
  ring

omit [Nonempty M] in
/-- The input bath in the attaining protocol is exactly the target density matrix. -/
theorem matching_bath {β : ℝ} (hβ : 0 < β) {ρ : Matrix M M ℂ}
    (hρ : ρ.PosDef) (htr : ρ.trace = 1) :
    gibbsBath β (matchingEnergies β hρ.isHermitian.eigenvalues)
      hρ.isHermitian.eigenvectorUnitary = ρ := by
  have hsum : ∑ i, hρ.isHermitian.eigenvalues i = 1 := by
    have h := hρ.isHermitian.trace_eq_sum_eigenvalues
    rw [htr] at h
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum, Complex.ofReal_one]
    exact h.symm
  rw [gibbsBath, gibbsWeight_matching hβ _ hρ.eigenvalues_pos hsum]
  exact hρ.isHermitian.spectral_theorem.symm

/-- Attainment with a same-dimension bath and an actual swap, leaving the bath mixed. -/
theorem bandwidth_attained {β : ℝ} (hβ : 0 < β) {ρ : Matrix M M ℂ}
    (hρ : ρ.PosDef) (htr : ρ.trace = 1) :
    let E := matchingEnergies β hρ.isHermitian.eigenvalues
    let τ := gibbsBath β E hρ.isHermitian.eigenvectorUnitary
    energyWidth E = requiredWidth β hρ ∧
      conjStarAlgAut ℂ _ (tensorSwap (M := M)) (τ ⊗ₖ mixed M) = mixed M ⊗ₖ ρ ∧
      Retains τ ρ tensorSwap := by
  dsimp only
  have hτ := matching_bath hβ hρ htr
  have hswap := tensorSwap_conj (gibbsBath β (matchingEnergies β hρ.isHermitian.eigenvalues)
    hρ.isHermitian.eigenvectorUnitary) (mixed M)
  rw [hτ] at hswap
  refine ⟨matchingEnergies_width hβ _ hρ.eigenvalues_pos, ?_, ?_⟩
  · simpa only [hτ] using hswap
  · unfold Retains
    rw [hτ, hswap]
    change partialTraceLeft (Matrix.kronecker (mixed M) ρ) = ρ
    rw [partialTraceLeft_kronecker, trace_mixed, one_smul]

omit [Fintype M] [Nonempty M] in
theorem diagonalReal_posDef (p : M → ℝ) (hp : ∀ i, 0 < p i) : (diagonalReal p).PosDef := by
  rw [diagonalReal, posDef_diagonal_iff]
  intro i
  exact Complex.pos_iff.mpr ⟨hp i, rfl⟩

private theorem conj_diagonal_endpoints (p : M → ℝ) (V : unitary (Matrix M M ℂ))
    {H : Matrix M M ℂ} (h : H.IsHermitian) (hd : H = conjStarAlgAut ℂ _ V (diagonalReal p)) :
    minValue h.eigenvalues = minValue p ∧ maxValue h.eigenvalues = maxValue p := by
  have hlo (r : ℝ) : (∀ i, r ≤ h.eigenvalues i) ↔ ∀ i, r ≤ p i := by
    rw [← scalar_le_iff_eigenvalues, hd, ← conj_scalar V r, conj_le_conj_iff,
      ← diagonalReal_const, diagonalReal_le_iff]
  have hhi (r : ℝ) : (∀ i, h.eigenvalues i ≤ r) ↔ ∀ i, p i ≤ r := by
    rw [← le_scalar_iff_eigenvalues, hd, ← conj_scalar V r, conj_le_conj_iff,
      ← diagonalReal_const, diagonalReal_le_iff]
  obtain ⟨i, hi⟩ := minValue_attained p
  obtain ⟨j, hj⟩ := maxValue_attained p
  obtain ⟨i', hi'⟩ := minValue_attained h.eigenvalues
  obtain ⟨j', hj'⟩ := maxValue_attained h.eigenvalues
  constructor
  · exact le_antisymm (hi ▸ (hlo _).1 (minValue_le _) i)
      (hi' ▸ (hlo _).2 (minValue_le _) i')
  · exact le_antisymm (hj' ▸ (hhi _).2 (le_maxValue _) j')
      (hj ▸ (hhi _).1 (le_maxValue _) j)

/-- The spectral endpoints of a real diagonal matrix are its coordinate extrema. -/
theorem diagonalReal_endpoints (p : M → ℝ) (h : (diagonalReal p).IsHermitian) :
    minValue h.eigenvalues = minValue p ∧ maxValue h.eigenvalues = maxValue p :=
  conj_diagonal_endpoints p 1 h (by rw [map_one]; rfl)

section ThermalState

open NormedSpace
open scoped CStarAlgebra Matrix.Norms.L2Operator
open D5.S3.Quantum.Divergence.GibbsVariationalIdentity (gibbsState partitionFunction)
open D5.S3.Quantum.Information.CorrelatedGibbsEnergyIdentity (thermalState)

omit [Nonempty B] in
theorem hamiltonian_selfAdjoint {H : Matrix B B ℂ} (hH : H.IsHermitian) :
    IsSelfAdjoint (CStarMatrix.ofMatrix H) := by
  change star (CStarMatrix.ofMatrixStarAlgEquiv H) = CStarMatrix.ofMatrixStarAlgEquiv H
  rw [← map_star, hH.star_eq]

private theorem thermalState_eq_of_diagonalization (β : ℝ) {H : Matrix B B ℂ}
    (hH : H.IsHermitian) (E : B → ℝ) (V : unitary (Matrix B B ℂ))
    (hd : H = conjStarAlgAut ℂ _ V (diagonalReal E)) :
    CStarMatrix.ofMatrix.symm (thermalState (CStarMatrix.ofMatrix H)
      (hamiltonian_selfAdjoint hH) β).1 = gibbsBath β E V := by
  let Hβ : CStarMatrix B B ℂ := (-β) • CStarMatrix.ofMatrix H
  let : NormedAlgebra ℚ (CStarMatrix B B ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  let f (i : B) := Real.exp (-β * E i)
  let W : Matrix B B ℂ := V
  have hWinv : W⁻¹ = star W := Matrix.inv_eq_left_inv (coe_star_mul_self V)
  have hscaled : (-β) • H = W * diagonalReal (fun i => -β * E i) * W⁻¹ := by
    rw [hd, conjStarAlgAut_apply, hWinv, ← Matrix.smul_mul, ← Matrix.mul_smul]
    have hdiag : (-β) • diagonalReal E = diagonalReal (fun i => -β * E i) := by
      unfold diagonalReal
      rw [← diagonal_smul]
      apply congrArg diagonal
      funext i
      simp [Pi.smul_apply, Complex.real_smul, Complex.ofReal_mul]
    rw [hdiag]
  have hdiagExp : exp (diagonalReal (fun i => -β * E i)) = diagonalReal f := by
    unfold diagonalReal
    rw [Matrix.exp_diagonal]
    apply congrArg diagonal
    funext i
    rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]
  have hexp : exp ((-β) • H) = W * diagonalReal f * star W := by
    rw [hscaled, Matrix.exp_conj _ _ (isUnit_coe (U := V)), hdiagExp, hWinv]
  have hbridge : CStarMatrix.ofMatrix.symm (exp Hβ) = exp ((-β) • H) :=
    NormedSpace.map_exp CStarMatrix.ofMatrixStarAlgEquiv.symm
      CStarMatrix.ofMatrixL.symm.continuous Hβ
  have hZ : partitionFunction Hβ = ∑ i, f i := by
    rw [partitionFunction, hbridge, hexp, trace_mul_cycle, show star W * W = 1 from
      coe_star_mul_self V, one_mul, diagonalReal, trace_diagonal, ← Complex.ofReal_sum,
      Complex.ofReal_re]
  change (partitionFunction Hβ)⁻¹ • CStarMatrix.ofMatrix.symm (exp Hβ) =
    gibbsBath β E V
  rw [hbridge, hexp, hZ, gibbsBath, conjStarAlgAut_apply, ← Matrix.smul_mul]
  have hdiag : (∑ i, f i)⁻¹ • diagonalReal f = diagonalReal (gibbsWeight β E) := by
    unfold diagonalReal
    rw [← diagonal_smul]
    apply congrArg diagonal
    funext i
    simp [f, gibbsWeight, div_eq_inv_mul, Complex.real_smul, Complex.ofReal_mul]
  rw [← Matrix.mul_smul, hdiag]

/-- The repo's matrix-exponential Gibbs state in the Hamiltonian eigenbasis. -/
theorem thermalState_eq_gibbsBath (β : ℝ) {H : Matrix B B ℂ} (hH : H.IsHermitian) :
    CStarMatrix.ofMatrix.symm (thermalState (CStarMatrix.ofMatrix H)
      (hamiltonian_selfAdjoint hH) β).1 = gibbsBath β hH.eigenvalues hH.eigenvectorUnitary :=
  thermalState_eq_of_diagonalization β hH _ _ hH.spectral_theorem

/-- The lower bound for an arbitrary finite Hermitian bath Hamiltonian, using
the repo's normalized matrix exponential as the input state. -/
theorem thermal_bandwidth_lower_bound {β : ℝ} (hβ : 0 < β)
    {H : Matrix B B ℂ} (hH : H.IsHermitian) {ρ : Matrix M M ℂ} (hρ : ρ.PosDef)
    (U : unitary (Matrix (B × M) (B × M) ℂ))
    (hU : Retains (CStarMatrix.ofMatrix.symm (thermalState (CStarMatrix.ofMatrix H)
      (hamiltonian_selfAdjoint hH) β).1) ρ U) :
    requiredWidth β hρ ≤ energyWidth hH.eigenvalues ∧
      (Fintype.card M : ℝ) * maxValue hρ.isHermitian.eigenvalues ≤ Fintype.card B := by
  rw [thermalState_eq_gibbsBath β hH] at hU
  exact bandwidth_lower_bound hβ _ _ hρ U hU

/-- The minimum among physical Hermitian Hamiltonians is achieved by the aligned
Hamiltonian and the tensor swap on a bath with the memory's dimension. -/
theorem thermal_bandwidth_attained {β : ℝ} (hβ : 0 < β) {ρ : Matrix M M ℂ}
    (hρ : ρ.PosDef) (htr : ρ.trace = 1) :
    ∃ (H : Matrix M M ℂ) (hH : H.IsHermitian),
      energyWidth hH.eigenvalues = requiredWidth β hρ ∧
      Retains (CStarMatrix.ofMatrix.symm (thermalState (CStarMatrix.ofMatrix H)
        (hamiltonian_selfAdjoint hH) β).1) ρ tensorSwap := by
  let E := matchingEnergies β hρ.isHermitian.eigenvalues
  let V := hρ.isHermitian.eigenvectorUnitary
  let H := conjStarAlgAut ℂ _ V (diagonalReal E)
  have hD : (diagonalReal E).IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    simp [isSelfAdjoint_iff]
  have hH : H.IsHermitian := by
    change star H = H
    unfold H
    rw [← map_star, hD.star_eq]
  have hends := conj_diagonal_endpoints E V hH rfl
  refine ⟨H, hH, ?_, ?_⟩
  · unfold energyWidth
    rw [hends.1, hends.2]
    exact (bandwidth_attained hβ hρ htr).1
  · rw [thermalState_eq_of_diagonalization β hH E V rfl]
    exact (bandwidth_attained hβ hρ htr).2.2

end ThermalState

end

end GibbsBathBandwidth
