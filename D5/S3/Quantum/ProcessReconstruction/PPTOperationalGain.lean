/- GID: D5/S3/Quantum/ProcessReconstruction/PPTOperationalGain
   generality: I
   mirror-B: D5/B/S3/Quantum/ProcessReconstruction/PPTOperationalGain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Attains the exact minimum realignment gain by distinct quantum channels. -/

import D5.S3.Quantum.ProcessReconstruction.PauliDiagonalPPTTomography
import D5.S3.Quantum.Entanglement.Witness.PPTWeightedReduction
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Least operational gain for square quantum probes

The output of a probe under a channel difference contracts each
unnormalized Choi slice by the Bob-first realignment. For a Hermitian
probe, a minimizing right singular direction can be chosen Hermitian.

The difference-of-channels construction follows the operational
distinguishability arguments of Caiaffa–Piani (arXiv:1808.10835) and
Lie–Jeong (arXiv:2206.05899). The exact Hilbert–Schmidt gain identifies
the operational quantity in the setting of Singh (arXiv:2605.19182v3,
Proposition 5). The final theorem applies the marginal-weighted PPT
converse to the same attaining channel pair.
-/

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder InnerProductSpace Kronecker MatrixOrder
  Matrix.Norms.L2Operator

set_option autoImplicit false

namespace D5.S3.Quantum.ProcessReconstruction.PPTOperationalGain

open D5.S3.Quantum.Foundation.FiniteKrausChannel
open PhyslibLeaf (MatrixMap)
open Original8340Global (inputChoi inputChoi_index_swap)
open PauliDiagonalPPTTomography (directionChannel hsSquare probeOutput)
open D5.S3.Quantum.FiniteDimensional (qubitZ qubit_weyl_star)
open D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound
  (realign singularVector singularVector_eq_sqrt_rowGram)
open D5.S3.Quantum.Entanglement.Witness.PPTWeightedReduction
  (leastRealignmentSV weighted_converse_of_ppt)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceLeft)
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)

section PhysicalDirection

variable {A : Type} [Fintype A] [DecidableEq A]

private theorem directionChannel_inputChoi (P : Matrix A A ℂ) (e : ℝ) :
    inputChoi (directionChannel P e) =
      (1 / 2 : ℝ) • (1 : Matrix (A × Fin 2) (A × Fin 2) ℂ) + e • (Pᵀ ⊗ₖ qubitZ) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  change ((Matrix.single i j (1 : ℂ)).trace / 2) * (1 : Matrix (Fin 2) (Fin 2) ℂ) a b +
    ((e : ℂ) * (P * Matrix.single i j 1).trace) * qubitZ a b = _
  rw [Matrix.trace_mul_comm, Matrix.trace_single_mul, one_smul]
  by_cases hij : i = j
  · subst j
    by_cases hab : a = b <;>
      norm_num [hab, Matrix.trace_single_eq_same, Matrix.one_apply, Matrix.kronecker_apply,
        Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul] <;> ring
  · simp [hij, Matrix.trace_single_eq_of_ne, Matrix.one_apply, Matrix.kronecker_apply,
      Matrix.transpose_apply, Matrix.smul_apply, Complex.real_smul, mul_assoc]

private theorem halfIdentity_add_posSemidef {I : Type*} [Fintype I] [DecidableEq I]
    (Q : Matrix I I ℂ) (hQ : IsSelfAdjoint Q) (hn : ‖Q‖ ≤ 1 / 2) :
    ((1 / 2 : ℝ) • (1 : Matrix I I ℂ) + Q).PosSemidef := by
  have hlo := IsSelfAdjoint.neg_algebraMap_norm_le_self Q hQ
  rw [Algebra.algebraMap_eq_smul_one] at hlo
  have hp := Matrix.le_iff.mp hlo
  rw [sub_neg_eq_add, add_comm] at hp
  have hδ := (Matrix.PosSemidef.one (n := I) (R := ℂ)).smul (sub_nonneg.mpr hn)
  convert hp.add hδ using 1 <;> module

private theorem directionChannel_cptp_of_norm (H : Matrix A A ℂ) (e : ℝ)
    (hH : H.IsHermitian) (hn : ‖e • (H ⊗ₖ qubitZ)‖ ≤ 1 / 2) :
    (directionChannel Hᵀ e).IsCompletelyPositive ∧
      (directionChannel Hᵀ e).IsTracePreserving := by
  constructor
  · apply (PhyslibLeaf.MatrixMap.choi_PSD_iff_CP_map _).mpr
    suffices hp : (inputChoi (directionChannel Hᵀ e)).PosSemidef by
      rw [inputChoi_index_swap] at hp
      simpa [Matrix.submatrix_submatrix] using hp.submatrix Prod.swap
    rw [directionChannel_inputChoi, Matrix.transpose_transpose]
    apply halfIdentity_add_posSemidef _ _ hn
    change (e • (H ⊗ₖ qubitZ))ᴴ = e • (H ⊗ₖ qubitZ)
    have hz : qubitZᴴ = qubitZ := qubit_weyl_star.2.2.1
    simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_kronecker,
      hH.eq, hz]
  · intro X
    change (((X.trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) +
      ((e : ℂ) * (Hᵀ * X).trace) • qubitZ).trace = X.trace
    have hz : qubitZ.trace = 0 := by
      norm_num [qubitZ, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two]
    simp [Matrix.trace_add, Matrix.trace_smul, hz, smul_eq_mul]

/-- Every Hermitian Choi slice is realized up to a positive scale by two
channels into a qubit. The formula uses input-first, unnormalized Choi
matrices and holds in particular for unit Hilbert–Schmidt directions. -/
theorem exists_cptp_choi_direction (H : Matrix A A ℂ) (hH : H.IsHermitian) :
    ∃ (Φ Ψ : MatrixMap A (Fin 2) ℂ) (t : ℝ),
      Φ.IsCompletelyPositive ∧ Φ.IsTracePreserving ∧
      Ψ.IsCompletelyPositive ∧ Ψ.IsTracePreserving ∧ 0 < t ∧
      inputChoi Φ - inputChoi Ψ = t • (H ⊗ₖ qubitZ) := by
  let K := H ⊗ₖ qubitZ
  let e : ℝ := 1 / (2 * (‖K‖ + 1))
  have hden : 0 < 2 * (‖K‖ + 1) := by positivity
  have he : 0 < e := one_div_pos.mpr hden
  have hp : ‖e • K‖ ≤ 1 / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos he]
    change (1 / (2 * (‖K‖ + 1))) * ‖K‖ ≤ 1 / 2
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hden]
    linarith
  have hm : ‖(-e) • K‖ ≤ 1 / 2 := by simpa only [neg_smul, norm_neg] using hp
  obtain ⟨hpCP, hpTP⟩ := directionChannel_cptp_of_norm H e hH hp
  obtain ⟨hmCP, hmTP⟩ := directionChannel_cptp_of_norm H (-e) hH hm
  refine ⟨_, _, 2 * e, hpCP, hpTP, hmCP, hmTP, by positivity, ?_⟩
  rw [directionChannel_inputChoi, directionChannel_inputChoi, Matrix.transpose_transpose]
  module

end PhysicalDirection

section HilbertSchmidt

variable {I J : Type*} [Fintype I] [Fintype J]

private def vectorSquare (x : I → ℂ) : ℝ :=
  (star x ⬝ᵥ x).re

private theorem vectorSquare_eq_norm_sq (x : I → ℂ) :
    vectorSquare x = ‖(WithLp.toLp 2 x : EuclideanSpace ℂ I)‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), EuclideanSpace.inner_toLp_toLp]
  exact congrArg Complex.re (dotProduct_comm _ _)

private theorem vectorSquare_smul (r : ℝ) (x : I → ℂ) :
    vectorSquare (r • x) = r ^ 2 * vectorSquare x := by
  rw [vectorSquare_eq_norm_sq, vectorSquare_eq_norm_sq]
  change ‖r • (WithLp.toLp 2 x : EuclideanSpace ℂ I)‖ ^ 2 =
    r ^ 2 * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ I)‖ ^ 2
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

private theorem vectorSquare_gram (T : Matrix J I ℂ) (x : I → ℂ) :
    vectorSquare (T *ᵥ x) = (star x ⬝ᵥ ((Tᴴ * T) *ᵥ x)).re := by
  rw [vectorSquare, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

private def matrixVector (H : Matrix I I ℂ) : I × I → ℂ := fun p => H p.1 p.2

private theorem hsSquare_eq_sum (M : Matrix I I ℂ) :
    hsSquare M = ∑ i, ∑ j, (star (M i j) * M i j).re := by
  simp only [hsSquare, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]
  exact Finset.sum_comm

private theorem hsSquare_eq_vectorSquare (H : Matrix I I ℂ) :
    hsSquare H = vectorSquare (matrixVector H) := by
  rw [hsSquare_eq_sum]
  simp only [vectorSquare, dotProduct, matrixVector, Pi.star_apply,
    Fintype.sum_prod_type, Complex.re_sum]

private theorem hsSquare_fibers (M : Matrix (I × J) (I × J) ℂ) :
    hsSquare M = ∑ a : I, ∑ b : I, vectorSquare (fun p : J × J =>
      M (a, p.1) (b, p.2)) := by
  simp only [hsSquare_eq_sum, Fintype.sum_prod_type, vectorSquare, dotProduct,
    Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Finset.sum_comm

private theorem hsSquare_submatrix (M : Matrix I I ℂ) (e : J ≃ I) :
    hsSquare (M.submatrix e e) = hsSquare M := by
  rw [hsSquare, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  exact congrArg Complex.re (Equiv.sum_comp e fun i => (Mᴴ * M) i i)

private theorem vectorSquare_real_weight (r : ℝ) (x : I → ℂ) :
    (star x ⬝ᵥ (r • x)).re = r * vectorSquare x := by
  rw [dotProduct_smul]
  exact Complex.smul_re r (star x ⬝ᵥ x)

end HilbertSchmidt

section Tomography

variable {d : ℕ}
local notation "A" => Fin d

/-- The contraction of the probe against one input-first Choi slice. -/
def tomography (ρ : Matrix (A × A) (A × A) ℂ) (H : Matrix A A ℂ) : Matrix A A ℂ :=
  fun b e => ((realign ρ)ᵀ *ᵥ matrixVector H) (b, e)

private def adjointVector (x : A × A → ℂ) : A × A → ℂ :=
  fun p => star (x p.swap)

private theorem mulVec_adjointVector (T : Matrix (A × A) (A × A) ℂ)
    (hT : ∀ p q, star (T p.swap q.swap) = T p q) (x : A × A → ℂ) :
    T *ᵥ adjointVector x = adjointVector (T *ᵥ x) := by
  funext p
  simp only [Matrix.mulVec, dotProduct, adjointVector, star_sum, star_mul]
  apply Fintype.sum_equiv (Equiv.prodComm A A)
  intro q
  simp only [Equiv.prodComm_apply, hT]
  exact mul_comm _ _

private theorem tomography_adjoint_entries (ρ : Matrix (A × A) (A × A) ℂ)
    (hρ : ρ.IsHermitian) (p q : A × A) :
    star ((realign ρ)ᵀ p.swap q.swap) = (realign ρ)ᵀ p q :=
  congrArg (fun M : Matrix (A × A) (A × A) ℂ => M (q.1, p.1) (q.2, p.2)) hρ.eq

/-- The probe preserves Hermiticity on Choi slices. -/
theorem tomography_conjTranspose (ρ : Matrix (A × A) (A × A) ℂ)
    (hρ : ρ.IsHermitian) (H : Matrix A A ℂ) :
    tomography ρ Hᴴ = (tomography ρ H)ᴴ := by
  ext i j
  exact congrFun (mulVec_adjointVector (realign ρ)ᵀ
    (tomography_adjoint_entries ρ hρ) (matrixVector H)) (i, j)

private theorem rightGram_adjointVector (ρ : Matrix (A × A) (A × A) ℂ)
    (hρ : ρ.IsHermitian) (x : A × A → ℂ) :
    let T := (realign ρ)ᵀ
    (Tᴴ * T) *ᵥ adjointVector x = adjointVector ((Tᴴ * T) *ᵥ x) := by
  dsimp only
  let T := (realign ρ)ᵀ
  have hT := tomography_adjoint_entries ρ hρ
  have hTstar (p q : A × A) : star (Tᴴ p.swap q.swap) = Tᴴ p q := by
    simpa only [Matrix.conjTranspose_apply] using congrArg star (hT q p)
  change (Tᴴ * T) *ᵥ _ = _
  simp only [← Matrix.mulVec_mulVec, mulVec_adjointVector T hT,
    mulVec_adjointVector Tᴴ hTstar]
  rfl

private def lastIndex (hd : 2 ≤ d) : Fin (Fintype.card (A × A)) :=
  ⟨Fintype.card (A × A) - 1, by
    have h : 0 < d * d := Nat.mul_pos (by omega) (by omega)
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega⟩

private theorem leastRealignmentSV_sq_eq_rightGram (hd : 2 ≤ d)
    (ρ : Matrix (A × A) (A × A) ℂ) :
    let T := (realign ρ)ᵀ
    leastRealignmentSV hd ρ ^ 2 =
      T.posSemidef_conjTranspose_mul_self.isHermitian.eigenvalues₀ (lastIndex hd) := by
  dsimp only
  let T := (realign ρ)ᵀ
  let hL := T.posSemidef_self_mul_conjTranspose
  let hR := T.posSemidef_conjTranspose_mul_self
  let j := lastIndex hd
  let i := (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (A × A)))) j
  have he := (hL.isHermitian.eigenvalues_eq_eigenvalues_iff hR.isHermitian).2
    (Matrix.charpoly_mul_comm T Tᴴ)
  have hej : hL.isHermitian.eigenvalues₀ j = hR.isHermitian.eigenvalues₀ j := by
    simpa only [Matrix.IsHermitian.eigenvalues, i, Equiv.symm_apply_apply] using congrFun he i
  have hn : 0 ≤ hL.isHermitian.eigenvalues₀ j := by
    simpa only [Matrix.IsHermitian.eigenvalues, i, Equiv.symm_apply_apply] using hL.eigenvalues_nonneg i
  change singularVector T j ^ 2 = hR.isHermitian.eigenvalues₀ j
  rw [singularVector_eq_sqrt_rowGram, Real.sq_sqrt hn]
  exact hej

private theorem realignment_mulVec_lower (hd : 2 ≤ d)
    (ρ : Matrix (A × A) (A × A) ℂ) (x : A × A → ℂ) :
    leastRealignmentSV hd ρ ^ 2 * vectorSquare x ≤
      vectorSquare ((realign ρ)ᵀ *ᵥ x) := by
  let T := (realign ρ)ᵀ
  let G := Tᴴ * T
  let hG := T.posSemidef_conjTranspose_mul_self.isHermitian
  let g := leastRealignmentSV hd ρ ^ 2
  have hle : algebraMap ℝ (Matrix (A × A) (A × A) ℂ) g ≤ G := by
    refine (algebraMap_le_iff_le_spectrum hG.isSelfAdjoint).2 ?_
    intro r hr
    rw [hG.spectrum_real_eq_range_eigenvalues] at hr
    obtain ⟨i, rfl⟩ := hr
    let j := (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (A × A)))).symm i
    have hj : j ≤ lastIndex hd := by
      have h := j.isLt
      change j.val ≤ Fintype.card (A × A) - 1
      omega
    change g ≤ hG.eigenvalues₀ j
    rw [show g = hG.eigenvalues₀ (lastIndex hd) from leastRealignmentSV_sq_eq_rightGram hd ρ]
    exact hG.eigenvalues₀_antitone hj
  rw [Algebra.algebraMap_eq_smul_one] at hle
  have hq := (Complex.nonneg_iff.mp ((Matrix.le_iff.mp hle).dotProduct_mulVec_nonneg x)).1
  rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, Matrix.smul_mulVec, Matrix.one_mulVec,
    vectorSquare_real_weight, ← vectorSquare_gram] at hq
  exact sub_nonneg.mp hq

/-- The least singular value controls the gain on every complex Choi slice. -/
theorem leastRealignmentSV_sq_mul_hsSquare_le_tomography (hd : 2 ≤ d)
    (ρ : Matrix (A × A) (A × A) ℂ) (H : Matrix A A ℂ) :
    leastRealignmentSV hd ρ ^ 2 * hsSquare H ≤ hsSquare (tomography ρ H) := by
  rw [hsSquare_eq_vectorSquare, hsSquare_eq_vectorSquare]
  exact realignment_mulVec_lower hd ρ (matrixVector H)

private theorem least_rightGram_eigenvector (hd : 2 ≤ d) (ρ : Matrix (A × A) (A × A) ℂ)
    (hρ : ρ.IsHermitian) :
    let T := (realign ρ)ᵀ
    ∃ x : A × A → ℂ, x ≠ 0 ∧ adjointVector x = x ∧
      (Tᴴ * T) *ᵥ x = leastRealignmentSV hd ρ ^ 2 • x := by
  dsimp only
  let T := (realign ρ)ᵀ
  let G := Tᴴ * T
  let hG := T.posSemidef_conjTranspose_mul_self.isHermitian
  let g := leastRealignmentSV hd ρ ^ 2
  let i := (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (A × A)))) (lastIndex hd)
  let v : A × A → ℂ := ⇑(hG.eigenvectorBasis i)
  have he : hG.eigenvalues i = g := by
    rw [Matrix.IsHermitian.eigenvalues, show
      (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (A × A)))).symm i =
        lastIndex hd by simp [i]]
    exact (leastRealignmentSV_sq_eq_rightGram hd ρ).symm
  have hv : G *ᵥ v = g • v := by simpa only [he] using hG.mulVec_eigenvectorBasis i
  have hvn : v ≠ 0 :=
    (WithLp.ofLp_eq_zero 2).ne.2 (hG.eigenvectorBasis.orthonormal.ne_zero i)
  have hjv : G *ᵥ adjointVector v = g • adjointVector v := by
    rw [show G *ᵥ adjointVector v = adjointVector (G *ᵥ v) from
      rightGram_adjointVector ρ hρ v, hv]
    funext p
    simp [adjointVector, star_smul]
  by_cases hsum : v + adjointVector v = 0
  · refine ⟨Complex.I • (v - adjointVector v), ?_, ?_, ?_⟩
    · intro hz
      have hz' : v - adjointVector v = 0 :=
        (smul_eq_zero.mp hz).resolve_left Complex.I_ne_zero
      have htwo : (2 : ℂ) • v = 0 := calc
        _ = v + v := two_smul ℂ v
        _ = v + adjointVector v := congrArg (v + ·) (sub_eq_zero.mp hz')
        _ = 0 := hsum
      exact hvn ((smul_eq_zero.mp htwo).resolve_left (by norm_num))
    · funext p
      simp [adjointVector, Prod.swap_swap, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
        Complex.star_def, Complex.conj_I, mul_sub]
      <;> ring
    · rw [Matrix.mulVec_smul, Matrix.mulVec_sub, hv, hjv, ← smul_sub, smul_comm]
  · refine ⟨v + adjointVector v, hsum, ?_, ?_⟩
    · funext p
      simp [adjointVector, Prod.swap_swap, add_comm]
    · rw [Matrix.mulVec_add, hv, hjv, smul_add]

/-- A unit Hilbert–Schmidt Hermitian Choi slice attains the minimum
complex gain, including at a zero singular value. -/
theorem exists_hermitian_least_direction (hd : 2 ≤ d)
    (ρ : Matrix (A × A) (A × A) ℂ) (hρ : ρ.IsHermitian) :
    ∃ H : Matrix A A ℂ, H.IsHermitian ∧ hsSquare H = 1 ∧
      hsSquare (tomography ρ H) = leastRealignmentSV hd ρ ^ 2 := by
  let T := (realign ρ)ᵀ
  let g := leastRealignmentSV hd ρ ^ 2
  obtain ⟨x, hx, hj, he⟩ := least_rightGram_eigenvector hd ρ hρ
  have hsq : vectorSquare (T *ᵥ x) = g * vectorSquare x := by
    rw [vectorSquare_gram, he, vectorSquare_real_weight]
  let n := ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (A × A))‖
  have hn : 0 < n := norm_pos_iff.mpr ((WithLp.toLp_eq_zero 2).ne.2 hx)
  have hxnorm : vectorSquare x = n ^ 2 := vectorSquare_eq_norm_sq x
  let H : Matrix A A ℂ := fun a b => n⁻¹ • x (a, b)
  have hH : matrixVector H = n⁻¹ • x := rfl
  have hunit : vectorSquare (n⁻¹ • x) = 1 := by
    rw [vectorSquare_smul, hxnorm, ← mul_pow, inv_mul_cancel₀ hn.ne', one_pow]
  refine ⟨H, ?_, ?_, ?_⟩
  · apply Matrix.ext
    intro a b
    have h := congrFun hj (a, b)
    change star (x (b, a)) = x (a, b) at h
    change star (n⁻¹ • x (b, a)) = n⁻¹ • x (a, b)
    rw [star_smul, star_trivial, h]
  · rw [hsSquare_eq_vectorSquare, hH, hunit]
  · rw [hsSquare_eq_vectorSquare]
    change vectorSquare (T *ᵥ matrixVector H) = g
    rw [hH, Matrix.mulVec_smul, vectorSquare_smul, hsq, mul_left_comm,
      ← vectorSquare_smul, hunit, mul_one]

end Tomography

section ChannelGain

variable {d : ℕ}
local notation "A" => Fin d
variable {O : Type*} [Fintype O] [DecidableEq O]

private theorem probeOutput_apply_mulVec
    (ρ : Matrix (A × A) (A × A) ℂ) (Φ : MatrixMap A O ℂ)
    (a b : O) (p : A × A) :
    probeOutput Φ ρ (a, p.1) (b, p.2) =
      ((realign ρ)ᵀ *ᵥ (fun q => inputChoi Φ (q.1, a) (q.2, b))) p := by
  rw [probeOutput, PhyslibLeaf.MatrixMap.kron_def]
  simp only [LinearMap.id_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change (∑ k : A, ∑ l : A,
      Φ (Matrix.single i j 1) a b * Matrix.single k l (1 : ℂ) p.1 p.2 *
        ρ (i, k) (j, l)) = ρ (i, p.1) (j, p.2) * Φ (Matrix.single i j 1) a b
  rw [Finset.sum_eq_single p.1]
  · rw [Finset.sum_eq_single p.2]
    · rw [Matrix.single_apply_same, mul_one, mul_comm]
    · intro l _ hl
      simp [Matrix.single_apply, hl]
    · simp
  · intro k _ hk
    simp [Matrix.single_apply, hk]
  · simp

/-- Each output slice is obtained by multiplying the corresponding Choi
slice by the transposed realignment. -/
theorem probeOutput_sub_mulVec
    (ρ : Matrix (A × A) (A × A) ℂ) (Φ Ψ : MatrixMap A O ℂ)
    (a b : O) (p : A × A) :
    (probeOutput Φ ρ - probeOutput Ψ ρ) (a, p.1) (b, p.2) =
      ((realign ρ)ᵀ *ᵥ
        (fun q => (inputChoi Φ - inputChoi Ψ) (q.1, a) (q.2, b))) p := by
  rw [Matrix.sub_apply, probeOutput_apply_mulVec ρ Φ a b p, probeOutput_apply_mulVec ρ Ψ a b p]
  change _ = ((realign ρ)ᵀ *ᵥ
    ((fun q => inputChoi Φ (q.1, a) (q.2, b)) -
      (fun q => inputChoi Ψ (q.1, a) (q.2, b)))) p
  rw [Matrix.mulVec_sub, Pi.sub_apply]

/-- Every channel difference satisfies the realignment lower bound,
uniformly over finite output sizes. -/
theorem leastRealignmentSV_sq_mul_choi_le_output (hd : 2 ≤ d)
    (ρ : Matrix (A × A) (A × A) ℂ) (Φ Ψ : MatrixMap A O ℂ) :
    leastRealignmentSV hd ρ ^ 2 * hsSquare (inputChoi Φ - inputChoi Ψ) ≤
      hsSquare (probeOutput Φ ρ - probeOutput Ψ ρ) := by
  let C := inputChoi Φ - inputChoi Ψ
  let e := Equiv.prodComm O A
  have hc : hsSquare C = ∑ a : O, ∑ b : O,
      vectorSquare (fun q : A × A => C (q.1, a) (q.2, b)) := by
    rw [← hsSquare_submatrix C e, hsSquare_fibers] <;> rfl
  change leastRealignmentSV hd ρ ^ 2 * hsSquare C ≤ _
  rw [hc, hsSquare_fibers, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun b _ =>
    (realignment_mulVec_lower hd ρ (fun q => C (q.1, a) (q.2, b))).trans_eq
      (congrArg vectorSquare (funext fun p => (probeOutput_sub_mulVec ρ Φ Ψ a b p).symm))

/-- The squared output-to-Choi Hilbert–Schmidt ratio. The operational
minimum ranges over pairs with positive squared Choi distance. -/
def squaredGain (ρ : Matrix (A × A) (A × A) ℂ) (Φ Ψ : MatrixMap A O ℂ) : ℝ :=
  hsSquare (probeOutput Φ ρ - probeOutput Ψ ρ) / hsSquare (inputChoi Φ - inputChoi Ψ)

private theorem hsSquare_real_smul {I : Type*} [Fintype I] (t : ℝ)
    (M : Matrix I I ℂ) : hsSquare (t • M) = t ^ 2 * hsSquare M := by
  simp [hsSquare, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.trace_smul, Complex.real_smul, Complex.mul_re, pow_two]

private theorem hsSquare_kronecker_qubitZ {I : Type*} [Fintype I]
    (M : Matrix I I ℂ) :
    hsSquare (M ⊗ₖ qubitZ) = 2 * hsSquare M ∧
      hsSquare (qubitZ ⊗ₖ M) = 2 * hsSquare M := by
  obtain ⟨-, -, hz, -, hzz⟩ := qubit_weyl_star
  change qubitZᴴ = qubitZ at hz
  have htr : (qubitZᴴ * qubitZ).trace = 2 := by
    rw [hz, ← pow_two, hzz]
    norm_num
  constructor <;>
    simp [hsSquare, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      Matrix.trace_kronecker, htr, Complex.mul_re] <;> ring

private theorem probeOutput_sub_of_choi_direction
    (ρ : Matrix (A × A) (A × A) ℂ) (Φ Ψ : MatrixMap A (Fin 2) ℂ)
    (H : Matrix A A ℂ) (t : ℝ)
    (hC : inputChoi Φ - inputChoi Ψ = t • (H ⊗ₖ qubitZ)) :
    probeOutput Φ ρ - probeOutput Ψ ρ = t • (qubitZ ⊗ₖ tomography ρ H) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  have hv : (fun q : A × A => (inputChoi Φ - inputChoi Ψ) (q.1, a) (q.2, b)) =
      (t • qubitZ a b) • matrixVector H := by
    rw [hC]
    funext q
    simp only [Matrix.smul_apply, Matrix.kronecker_apply, matrixVector, Pi.smul_apply,
      Complex.real_smul, smul_eq_mul]
    ring
  rw [show (probeOutput Φ ρ - probeOutput Ψ ρ) (a, i) (b, j) =
      ((realign ρ)ᵀ *ᵥ
        (fun q => (inputChoi Φ - inputChoi Ψ) (q.1, a) (q.2, b))) (i, j) from
    probeOutput_sub_mulVec ρ Φ Ψ a b (i, j), hv, Matrix.mulVec_smul]
  simp only [tomography, Pi.smul_apply, Matrix.smul_apply, Matrix.kronecker_apply,
    Complex.real_smul, smul_eq_mul]
  ring

/-- Two CPTP maps into a qubit attain the squared least realignment gain.
Their unnormalized Choi matrices have positive distance even when the
probe has a nontrivial kernel. -/
theorem leastRealignmentSV_sq_cptp_attains (hd : 2 ≤ d)
    (ρ : Matrix (A × A) (A × A) ℂ) (hρ : ρ.IsHermitian) :
    ∃ Φ Ψ : MatrixMap A (Fin 2) ℂ,
      Φ.IsCompletelyPositive ∧ Φ.IsTracePreserving ∧
      Ψ.IsCompletelyPositive ∧ Ψ.IsTracePreserving ∧
      0 < hsSquare (inputChoi Φ - inputChoi Ψ) ∧
      squaredGain ρ Φ Ψ = leastRealignmentSV hd ρ ^ 2 := by
  obtain ⟨H, hH, hunit, hout⟩ := exists_hermitian_least_direction hd ρ hρ
  obtain ⟨Φ, Ψ, t, hΦCP, hΦTP, hΨCP, hΨTP, ht, hC⟩ :=
    exists_cptp_choi_direction H hH
  have hD : hsSquare (inputChoi Φ - inputChoi Ψ) = t ^ 2 * 2 := by
    rw [hC, hsSquare_real_smul, (hsSquare_kronecker_qubitZ H).1, hunit, mul_one]
  have hDpos : 0 < hsSquare (inputChoi Φ - inputChoi Ψ) := by
    rw [hD]
    positivity
  refine ⟨Φ, Ψ, hΦCP, hΦTP, hΨCP, hΨTP, hDpos, ?_⟩
  unfold squaredGain
  apply (div_eq_iff hDpos.ne').2
  rw [probeOutput_sub_of_choi_direction ρ Φ Ψ H t hC, hsSquare_real_smul,
    (hsSquare_kronecker_qubitZ (tomography ρ H)).2, hout, hD]
  ring

/-- The squared least realignment singular value is the minimum of the
observable squared gain over distinct CPTP maps into a qubit. -/
theorem leastRealignmentSV_sq_isLeast_cptp_gain (hd : 2 ≤ d)
    (ρ : Matrix (A × A) (A × A) ℂ) (hρ : ρ.IsHermitian) :
    IsLeast {g : ℝ | ∃ Φ Ψ : MatrixMap A (Fin 2) ℂ,
      Φ.IsCompletelyPositive ∧ Φ.IsTracePreserving ∧
      Ψ.IsCompletelyPositive ∧ Ψ.IsTracePreserving ∧
      0 < hsSquare (inputChoi Φ - inputChoi Ψ) ∧ squaredGain ρ Φ Ψ = g}
      (leastRealignmentSV hd ρ ^ 2) := by
  refine ⟨leastRealignmentSV_sq_cptp_attains hd ρ hρ, ?_⟩
  rintro g ⟨Φ, Ψ, _, _, _, _, hpos, rfl⟩
  unfold squaredGain
  exact (le_div_iff₀ hpos).2 (leastRealignmentSV_sq_mul_choi_le_output hd ρ Φ Ψ)

/-- The attaining physical pair for a PPT probe in a basis where the Bob
marginal is diagonal and strictly positive obeys the marginal-weighted
PPT upper bound. -/
theorem exists_cptp_pair_weighted_ppt (hd : 2 ≤ d)
    (ρ : Matrix (A × A) (A × A) ℂ) (hρ : ρ.PosSemidef)
    (ht : ρ.trace = 1) (hppt : (partialTranspose ρ).PosSemidef)
    (r : A → ℝ) (hr : ∀ i, 0 < r i)
    (hb : partialTraceLeft ρ = diagonal (fun i => (r i : ℂ))) :
    ∃ Φ Ψ : MatrixMap A (Fin 2) ℂ,
      Φ.IsCompletelyPositive ∧ Φ.IsTracePreserving ∧
      Ψ.IsCompletelyPositive ∧ Ψ.IsTracePreserving ∧
      0 < hsSquare (inputChoi Φ - inputChoi Ψ) ∧
      squaredGain ρ Φ Ψ = leastRealignmentSV hd ρ ^ 2 ∧
      squaredGain ρ Φ Ψ ≤
        ((d : ℝ) - 1) / ((d : ℝ) ^ 2 * ((∑ i, (r i)⁻¹) - 1)) := by
  obtain ⟨Φ, Ψ, hΦCP, hΦTP, hΨCP, hΨTP, hpos, hgain⟩ :=
    leastRealignmentSV_sq_cptp_attains hd ρ hρ.isHermitian
  refine ⟨Φ, Ψ, hΦCP, hΦTP, hΨCP, hΨTP, hpos, hgain, ?_⟩
  rw [hgain]
  exact weighted_converse_of_ppt hd ρ hρ ht hppt r hr hb

end ChannelGain

end D5.S3.Quantum.ProcessReconstruction.PPTOperationalGain
