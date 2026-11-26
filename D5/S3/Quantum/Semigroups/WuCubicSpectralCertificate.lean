/- GID: D5/S3/Quantum/Semigroups/WuCubicSpectralCertificate
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicSpectralCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform ordinary Wu cubic deficit over complex densities at a fixed spectrum. -/

import D5.S3.Quantum.Semigroups.WuCubicOccupationEnvelope
import D5.S3.Quantum.Semigroups.TwistedTwoModeOUComparison
import D5.S3.Quantum.Semigroups.WuEndpointPauliFrame
import D5.S3.Quantum.Semigroups.WuModularEdgeSpectral
import OmegaBuild.Commands

/-!
# Matrix certificate for the ordinary Wu cubic inequality

Wu, arXiv:2610.33686v1, (2.4), (3.54), and (3.55).
The trace is the ordinary trace on the two-mode occupation basis
\(00,01,10,11\). The Gibbs rates sum to one before the factor two in the
paired generator. The energy and entropy reductions use the same complex
spectral frame of the input density.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder InnerProductSpace Kronecker Matrix MatrixOrder
  Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Semigroups.WuCubicSpectralCertificate

open D5.S3.Quantum.Matrix.SpectralPower (mpow)
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
  (DensityState quantumRelativeEntropy)
open TwistedTwoModeOUComparison (modeJump)
open WuCubicOccupationEnvelope (CARConstraints edgeSum sym orientationMoment
  roots spectrumOf temperature entropyConstant
  scaledCubicEnergy cubicEnergy relativeEntropy sharpCoefficient cubic_deficit_gt)
open WuModularEdgeSpectral (edgeWeight coshEdgeKernel edgeKernel_eq_cosh
  generatorTrace_eq_cosh pairedGenerator)

/-! ## CAR weights in a complex spectral frame -/

private abbrev Mat := Matrix (Fin 4) (Fin 4) ℂ

private abbrev occupationBasis : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv

private theorem basis_symm_zero : occupationBasis.symm 0 = (0, 0) := rfl
private theorem basis_symm_one : occupationBasis.symm 1 = (0, 1) := rfl
private theorem basis_symm_two : occupationBasis.symm 2 = (1, 0) := rfl
private theorem basis_symm_three : occupationBasis.symm 3 = (1, 1) := rfl

/-- The repository lowering jumps, in the flattened occupation basis. -/
private def lowering (k : Fin 2) : Mat :=
  Matrix.reindex occupationBasis occupationBasis (modeJump k)

private theorem lowering_zero :
    lowering 0 = !![0, 0, 1, 0; 0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0] := by
  change Matrix.reindex occupationBasis occupationBasis
    ((!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ 1) = _
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [basis_symm_zero, basis_symm_one, basis_symm_two, basis_symm_three,
      Matrix.reindex_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]

private theorem lowering_one :
    lowering 1 = !![0, -1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1; 0, 0, 0, 0] := by
  change Matrix.reindex occupationBasis occupationBasis
    (diagonal (![-1, 1] : Fin 2 → ℂ) ⊗ₖ
      (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)) = _
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [basis_symm_zero, basis_symm_one, basis_symm_two, basis_symm_three,
      Matrix.reindex_apply, Matrix.kroneckerMap_apply, Matrix.diagonal_apply]

/-- The physical number operator minus the identity. -/
private def charge : Mat := diagonal ![-1, 0, 0, 1]

private theorem lowering_occupations :
    lowering 0 * (lowering 0)ᴴ + lowering 1 * (lowering 1)ᴴ = 1 - charge ∧
    (lowering 0)ᴴ * lowering 0 + (lowering 1)ᴴ * lowering 1 = 1 + charge := by
  constructor <;> apply Matrix.ext <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [lowering_zero, lowering_one, charge, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_four, Matrix.conjTranspose_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.one_apply, Matrix.diagonal_apply]

private def majorana : Fin 4 → Mat :=
  ![lowering 0 + (lowering 0)ᴴ, Complex.I • (lowering 0 - (lowering 0)ᴴ),
    lowering 1 + (lowering 1)ᴴ, Complex.I • (lowering 1 - (lowering 1)ᴴ)]

private theorem majorana_selfAdjoint (k : Fin 4) : (majorana k).IsHermitian := by
  change (majorana k)ᴴ = majorana k
  fin_cases k <;> apply Matrix.ext <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [majorana, lowering_zero, lowering_one, Matrix.conjTranspose_apply,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.star_def,
      Complex.conj_I]

private theorem majorana_sq (k : Fin 4) : majorana k * majorana k = 1 := by
  fin_cases k <;> apply Matrix.ext <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [majorana, lowering_zero, lowering_one, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.conjTranspose_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.one_apply, Complex.I_mul_I]

set_option maxHeartbeats 2000000 in
-- The twelve off-diagonal products are checked entry by entry.
private theorem majorana_anticommute (k l : Fin 4) (h : k ≠ l) :
    majorana k * majorana l = -(majorana l * majorana k) := by
  fin_cases k <;> fin_cases l <;> try exact (h rfl).elim
  all_goals
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [majorana, lowering_zero, lowering_one, Matrix.mul_apply, Fin.sum_univ_four,
        Matrix.conjTranspose_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
        Matrix.smul_apply, smul_eq_mul, Complex.I_mul_I]

variable {ρ : Mat}

private abbrev frame (hρ : ρ.IsHermitian) := hρ.eigenvectorBasis

private abbrev inFrame (hρ : ρ.IsHermitian) : Mat ≃⋆ₐ[ℂ] Mat :=
  (Unitary.conjStarAlgAut ℂ Mat hρ.eigenvectorUnitary).symm

private theorem trace_inFrame (hρ : ρ.IsHermitian) (A : Mat) :
    (inFrame hρ A).trace = A.trace := by
  rw [inFrame, Unitary.conjStarAlgAut_symm_apply]
  exact Matrix.trace_units_conj' (Unitary.toUnits hρ.eigenvectorUnitary) A

private theorem inFrame_adjoint (hρ : ρ.IsHermitian) (A : Mat) :
    inFrame hρ Aᴴ = (inFrame hρ A)ᴴ := map_star (inFrame hρ) A

private theorem inFrame_entry (hρ : ρ.IsHermitian) (A : Mat) (i j : Fin 4) :
    inFrame hρ A i j = (A *ᵥ ⇑(frame hρ j)) ⬝ᵥ star ⇑(frame hρ i) := by
  rw [Unitary.conjStarAlgAut_symm_apply, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.IsHermitian.eigenvectorUnitary_apply,
    Matrix.mulVec, dotProduct, Pi.star_apply]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

private theorem inFrame_density (hρ : ρ.IsHermitian) :
    inFrame hρ ρ = diagonal (fun i => (hρ.eigenvalues i : ℂ)) := by
  calc
    inFrame hρ ρ = Unitary.conjStarAlgAut ℂ Mat (star hρ.eigenvectorUnitary) ρ := by
      unfold inFrame
      rw [Unitary.conjStarAlgAut_symm]
    _ = diagonal (Complex.ofReal ∘ hρ.eigenvalues) :=
      hρ.conjStarAlgAut_star_eigenvectorUnitary
    _ = _ := rfl

/-- Reverse the finite spectral-theorem indices before transferring them to the matrix indices. -/
def ascendingIndex : Equiv.Perm (Fin 4) :=
  Fin.revPerm.trans ((finCongr (Fintype.card_fin 4).symm).trans
    (Fintype.equivOfCardEq (Fintype.card_fin _)))

def eigenvalue (hρ : ρ.IsHermitian) (i : Fin 4) : ℝ :=
  hρ.eigenvalues (ascendingIndex i)

/-- Sum of the two spectral weights. Both endpoints use the same eigenframe. -/
private def weight (hρ : ρ.IsHermitian) (i j : Fin 4) : ℝ :=
  ∑ k : Fin 2, edgeWeight hρ (lowering k) (ascendingIndex i) (ascendingIndex j)

private def empty (hρ : ρ.IsHermitian) (i : Fin 4) : ℝ :=
  Complex.normSq (frame hρ i 0)

private def full (hρ : ρ.IsHermitian) (i : Fin 4) : ℝ :=
  Complex.normSq (frame hρ i 3)

private def evenOccupation (hρ : ρ.IsHermitian) (i : Fin 4) : ℝ :=
  full hρ (ascendingIndex i) + empty hρ (ascendingIndex i)

private def chargeAt (hρ : ρ.IsHermitian) (i : Fin 4) : ℝ := full hρ i - empty hρ i

private theorem inFrame_charge_re (hρ : ρ.IsHermitian) (i : Fin 4) :
    (inFrame hρ charge i i).re = chargeAt hρ i := by
  rw [inFrame_entry]
  norm_num [charge, chargeAt, full, empty, Matrix.mulVec_diagonal, dotProduct,
    Fin.sum_univ_four, Pi.star_apply, Complex.star_def, Complex.mul_conj,
    neg_mul, Complex.neg_re, Complex.add_re, Complex.sub_re]
  ring

private def occupationMoment (hρ : ρ.IsHermitian) : ℝ :=
  ∑ i, eigenvalue hρ i * chargeAt hρ (ascendingIndex i)

/-- The occupation used by the envelope is the ordinary trace of ρ(N − I). -/
private theorem occupationMoment_eq_trace (hρ : ρ.IsHermitian) :
    occupationMoment hρ = (ρ * charge).trace.re := by
  unfold occupationMoment eigenvalue
  calc
    _ = ∑ i, hρ.eigenvalues i * chargeAt hρ i :=
      Equiv.sum_comp ascendingIndex (fun i => hρ.eigenvalues i * chargeAt hρ i)
    _ = _ := by
      rw [← trace_inFrame hρ (ρ * charge)]
      rw [map_mul, inFrame_density]
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul, Complex.re_sum,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        inFrame_charge_re]

private theorem row_normSq (A : Mat) (i : Fin 4) :
    (∑ j, Complex.normSq (A i j)) = ((A * Aᴴ) i i).re := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
    Complex.mul_conj, Complex.re_sum, Complex.ofReal_re]

private theorem column_normSq (A : Mat) (i : Fin 4) :
    (∑ j, Complex.normSq (A j i)) = ((Aᴴ * A) i i).re := by
  simpa only [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_apply,
    Complex.star_def, Complex.normSq_conj] using row_normSq Aᴴ i

private theorem weight_marginals (hρ : ρ.IsHermitian) (i : Fin 4) :
    (∑ j, weight hρ i j) = 1 - chargeAt hρ (ascendingIndex i) ∧
    (∑ j, weight hρ j i) = 1 + chargeAt hρ (ascendingIndex i) := by
  let a := ascendingIndex i
  have hr (k : Fin 2) :
      (∑ j, edgeWeight hρ (lowering k) a (ascendingIndex j)) =
        (inFrame hρ (lowering k * (lowering k)ᴴ) a a).re := by
    change (∑ j, Complex.normSq (inFrame hρ (lowering k) a (ascendingIndex j))) = _
    rw [Equiv.sum_comp ascendingIndex (fun j => Complex.normSq (inFrame hρ (lowering k) a j)),
      row_normSq, map_mul, inFrame_adjoint]
  have hc (k : Fin 2) :
      (∑ j, edgeWeight hρ (lowering k) (ascendingIndex j) a) =
        (inFrame hρ ((lowering k)ᴴ * lowering k) a a).re := by
    change (∑ j, Complex.normSq (inFrame hρ (lowering k) (ascendingIndex j) a)) = _
    rw [Equiv.sum_comp ascendingIndex (fun j => Complex.normSq (inFrame hρ (lowering k) j a)),
      column_normSq, map_mul, inFrame_adjoint]
  change (∑ j, ∑ k : Fin 2, edgeWeight hρ (lowering k) a (ascendingIndex j)) =
      1 - chargeAt hρ a ∧
    (∑ j, ∑ k : Fin 2, edgeWeight hρ (lowering k) (ascendingIndex j) a) =
      1 + chargeAt hρ a
  constructor
  · rw [Finset.sum_comm]
    simp only [hr, Fin.sum_univ_two]
    rw [← Complex.add_re, ← Matrix.add_apply, ← map_add, lowering_occupations.1,
      map_sub, map_one, Matrix.sub_apply, Complex.sub_re, Matrix.one_apply_eq,
      Complex.one_re, inFrame_charge_re]
  · rw [Finset.sum_comm]
    simp only [hc, Fin.sum_univ_two]
    rw [← Complex.add_re, ← Matrix.add_apply, ← map_add, lowering_occupations.2,
      map_add, map_one, Matrix.add_apply, Complex.add_re, Matrix.one_apply_eq,
      Complex.one_re, inFrame_charge_re]

private theorem column_mass (hρ : ρ.IsHermitian) (i : Fin 4) :
    (∑ j, Complex.normSq (frame hρ i j)) = 1 := by
  let U := hρ.eigenvectorUnitary
  have hU : (U : Mat)ᴴ * (U : Mat) = 1 := Unitary.coe_star_mul_self U
  change (∑ j, Complex.normSq ((U : Mat) j i)) = 1
  rw [column_normSq, hU, Matrix.one_apply_eq, Complex.one_re]

private theorem row_mass (hρ : ρ.IsHermitian) (i : Fin 4) :
    (∑ j, Complex.normSq (frame hρ j i)) = 1 := by
  let U := hρ.eigenvectorUnitary
  have hU : (U : Mat) * (U : Mat)ᴴ = 1 := Unitary.coe_mul_star_self U
  change (∑ j, Complex.normSq ((U : Mat) i j)) = 1
  rw [row_normSq, hU, Matrix.one_apply_eq, Complex.one_re]

private theorem weight_diagonal (hρ : ρ.IsHermitian) (i : Fin 4) :
    weight hρ i i = evenOccupation hρ i * (1 - evenOccupation hρ i) := by
  let a := ascendingIndex i
  let x := frame hρ a
  have hodd : Complex.normSq (x 1) + Complex.normSq (x 2) = 1 - evenOccupation hρ i := by
    have h := column_mass hρ a
    change (∑ j, Complex.normSq (x j)) = 1 at h
    change _ = 1 - (Complex.normSq (x 3) + Complex.normSq (x 0))
    simp only [Fin.sum_univ_four] at h
    linarith only [h]
  rw [← hodd]
  change (∑ k : Fin 2, Complex.normSq (inFrame hρ (lowering k) a a)) =
    (Complex.normSq (x 3) + Complex.normSq (x 0)) *
      (Complex.normSq (x 1) + Complex.normSq (x 2))
  simp only [Fin.sum_univ_two, inFrame_entry, lowering_zero, lowering_one]
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.star_apply,
    Complex.normSq_apply, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.neg_re, Complex.neg_im]
  ring

private theorem majorana_pair_normSq (z w : ℂ) :
    Complex.normSq (z + w) + Complex.normSq (Complex.I * (z - w)) =
      2 * (Complex.normSq z + Complex.normSq w) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

/-- Apply the real Bessel bound to the four Majorana images of one eigenvector. -/
private theorem weight_pair_le_one (hρ : ρ.IsHermitian) (i j : Fin 4) :
    weight hρ i j + weight hρ j i ≤ 1 := by
  let a := ascendingIndex i
  let b := ascendingIndex j
  have hBessel := WuEndpointPauliFrame.overlap_le
    (fun k => (majorana k).toEuclideanLin)
    (fun k => Matrix.isSymmetric_toEuclideanLin_iff.mpr (majorana_selfAdjoint k))
    (by
      intro k x
      change ((Matrix.toLpLin 2 2 (majorana k)).comp
        (Matrix.toLpLin 2 2 (majorana k))) x = x
      rw [← Matrix.toLpLin_mul, majorana_sq, Matrix.toLpLin_one, LinearMap.id_apply])
    (by
      intro k l hkl x
      change ((Matrix.toLpLin 2 2 (majorana k)).comp
        (Matrix.toLpLin 2 2 (majorana l))) x =
          -((Matrix.toLpLin 2 2 (majorana l)).comp (Matrix.toLpLin 2 2 (majorana k))) x
      rw [← Matrix.toLpLin_mul, ← Matrix.toLpLin_mul, majorana_anticommute k l hkl,
        map_neg, LinearMap.neg_apply])
    (frame hρ a) (frame hρ b)
  have hinner (k : Fin 4) :
      ⟪frame hρ a, (majorana k).toEuclideanLin (frame hρ b)⟫_ℂ =
        inFrame hρ (majorana k) a b := by
    rw [inFrame_entry, EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanLin,
      Matrix.toLpLin_apply, WithLp.ofLp_toLp]
  have hcap : (∑ k, Complex.normSq (inFrame hρ (majorana k) a b)) ≤ 2 := by
    have hle := (le_add_of_nonneg_left (sq_nonneg ‖⟪frame hρ a, frame hρ b⟫_ℂ‖)).trans hBessel
    simpa only [hinner, ← Complex.normSq_eq_norm_sq, hρ.eigenvectorBasis.orthonormal.1 a,
      hρ.eigenvectorBasis.orthonormal.1 b, one_pow, mul_one] using hle
  have hpair (J : Mat) :
      Complex.normSq (inFrame hρ (J + Jᴴ) a b) +
        Complex.normSq (inFrame hρ (Complex.I • (J - Jᴴ)) a b) =
      2 * (edgeWeight hρ J a b + edgeWeight hρ J b a) := by
    change _ = 2 * (Complex.normSq (inFrame hρ J a b) + Complex.normSq (inFrame hρ J b a))
    rw [map_add, map_smul, map_sub, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.sub_apply, majorana_pair_normSq, inFrame_adjoint, Matrix.conjTranspose_apply]
    simp only [Complex.star_def, Complex.normSq_conj]
  have hsum : (∑ k, Complex.normSq (inFrame hρ (majorana k) a b)) =
      2 * (weight hρ i j + weight hρ j i) := by
    simp only [Fin.sum_univ_four, majorana, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      weight, Fin.sum_univ_two]
    change _ = 2 * ((edgeWeight hρ (lowering 0) a b + edgeWeight hρ (lowering 1) a b) +
      (edgeWeight hρ (lowering 0) b a + edgeWeight hρ (lowering 1) b a))
    linarith only [hpair (lowering 0), hpair (lowering 1)]
  linarith only [hcap, hsum]

private theorem evenOccupation_mem (hρ : ρ.IsHermitian) (i : Fin 4) :
    evenOccupation hρ i ∈ Set.Icc (0 : ℝ) 1 := by
  let a := ascendingIndex i
  have h := column_mass hρ a
  simp only [Fin.sum_univ_four] at h
  change 0 ≤ Complex.normSq (frame hρ a 3) + Complex.normSq (frame hρ a 0) ∧
    Complex.normSq (frame hρ a 3) + Complex.normSq (frame hρ a 0) ≤ 1
  exact ⟨add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _),
    by linarith only [h, Complex.normSq_nonneg (frame hρ a 1),
      Complex.normSq_nonneg (frame hρ a 2)]⟩

private theorem occupation_sums (hρ : ρ.IsHermitian) :
    (∑ i, evenOccupation hρ i) = 2 ∧ (∑ i, chargeAt hρ (ascendingIndex i)) = 0 := by
  have hp : (∑ i, full hρ (ascendingIndex i)) = 1 :=
    (Equiv.sum_comp ascendingIndex (full hρ)).trans (row_mass hρ 3)
  have hq : (∑ i, empty hρ (ascendingIndex i)) = 1 :=
    (Equiv.sum_comp ascendingIndex (empty hρ)).trans (row_mass hρ 0)
  norm_num [evenOccupation, chargeAt, Finset.sum_add_distrib, Finset.sum_sub_distrib, hp, hq]

private theorem occupation_bound (hρ : ρ.IsHermitian) (v : ℝ) :
    |occupationMoment hρ| ≤ ∑ i, evenOccupation hρ i * |eigenvalue hρ i - v| := by
  have hcenter : (∑ i, (eigenvalue hρ i - v) * chargeAt hρ (ascendingIndex i)) =
      occupationMoment hρ := by
    simp [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, (occupation_sums hρ).2,
      occupationMoment]
  rw [← hcenter]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  unfold chargeAt evenOccupation
  rw [abs_le]
  have hp := Complex.normSq_nonneg (frame hρ (ascendingIndex i) 3)
  have hq := Complex.normSq_nonneg (frame hρ (ascendingIndex i) 0)
  unfold full empty
  constructor <;> linarith only [hp, hq]

/-- The column and row occupations are the particle and hole marginals respectively. -/
private theorem orientationMoment_eq_marginals (lam : Fin 4 → ℝ) (w : Fin 4 → Fin 4 → ℝ) :
    orientationMoment lam w =
      ∑ i, lam i * ((∑ j, w j i) - (∑ j, w i j)) := by
  simp only [orientationMoment, edgeSum, Fin.sum_univ_four]
  ring

/-- Supply all eight fields of the scalar envelope directly from the complex eigenframe. -/
private theorem carConstraints (hρ : ρ.IsHermitian) :
    CARConstraints (eigenvalue hρ) (weight hρ) (evenOccupation hρ)
      (occupationMoment hρ) := by
  refine ⟨?_, ?_, fun i j _ => weight_pair_le_one hρ i j, weight_diagonal hρ,
    evenOccupation_mem hρ, (occupation_sums hρ).1, ?_, occupation_bound hρ⟩
  · intro i j
    exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  · intro i
    rw [show (∑ j, sym (weight hρ) i j) =
      (∑ j, weight hρ i j) + (∑ j, weight hρ j i) from Finset.sum_add_distrib]
    linarith only [(weight_marginals hρ i).1, (weight_marginals hρ i).2]
  · rw [orientationMoment_eq_marginals, occupationMoment, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(weight_marginals hρ i).1, (weight_marginals hρ i).2]
    ring

/-- Exact input to the scalar deficit theorem at the certificate spectrum. -/
private theorem certificateConstraints (hρ : ρ.IsHermitian)
    (hspectrum : eigenvalue hρ = WuCubicOccupationEnvelope.spectrum) :
    CARConstraints WuCubicOccupationEnvelope.spectrum (weight hρ) (evenOccupation hρ)
      (occupationMoment hρ) := by
  rw [← hspectrum]
  exact carConstraints hρ

/-! ## The ordinary Wu energy and Gibbs relative entropy -/

local notation "certificateSpectrum" => WuCubicOccupationEnvelope.spectrum
private abbrev rateDenominator : ℝ := 2 * Real.cosh temperature
private def lowerRate : ℝ := Real.exp (-temperature) / rateDenominator
private def upperRate : ℝ := Real.exp temperature / rateDenominator

private theorem rateDenominator_pos : 0 < rateDenominator :=
  mul_pos (by norm_num) (Real.cosh_pos _)

private theorem lowerRate_pos : 0 < lowerRate := div_pos (Real.exp_pos _) rateDenominator_pos
private theorem upperRate_pos : 0 < upperRate := div_pos (Real.exp_pos _) rateDenominator_pos

private theorem exp_temperature : Real.exp temperature = 729 / 512 := by
  unfold temperature
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul,
    Real.exp_log (by norm_num)]
  norm_num

private theorem rates_exact :
    lowerRate = 262144 / 793585 ∧ upperRate = 531441 / 793585 := by
  norm_num [lowerRate, upperRate, rateDenominator, Real.cosh_eq, Real.exp_neg, exp_temperature]

private def gibbsWeights : Fin 4 → ℝ :=
  ![lowerRate ^ 2, lowerRate * upperRate, lowerRate * upperRate, upperRate ^ 2]

/-- The product of two copies of the one-mode Gibbs state with log odds
\(2h\), in the occupation basis with ordinary trace. -/
def gibbsD : Mat := diagonal (fun i => (gibbsWeights i : ℂ))

private theorem gibbsD_pos : gibbsD.PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  have hi : 0 < gibbsWeights i := by
    fin_cases i <;> norm_num [gibbsWeights, rates_exact.1, rates_exact.2]
  exact_mod_cast hi

private theorem gibbsD_trace : gibbsD.trace = 1 := by
  rw [gibbsD, Matrix.trace_diagonal, ← Complex.ofReal_sum]
  norm_num [Fin.sum_univ_four, gibbsWeights, rates_exact.1, rates_exact.2]

private theorem gibbs_modular_relation (k : Fin 2) :
    gibbsD * lowering k * gibbsD⁻¹ = (lowerRate / upperRate) • lowering k := by
  have h (i j : Fin 4) :
      gibbsWeights i * lowering k i j =
        (lowerRate / upperRate * gibbsWeights j : ℝ) * lowering k i j := by
    have h0 : occupationBasis.symm 0 = (0, 0) := rfl
    have h1 : occupationBasis.symm 1 = (0, 1) := rfl
    have h2 : occupationBasis.symm 2 = (1, 0) := rfl
    have h3 : occupationBasis.symm 3 = (1, 1) := rfl
    let J : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]
    have hj : TwistedTwoModeOUComparison.modeJump 0 = J ⊗ₖ 1 := rfl
    have hj' : TwistedTwoModeOUComparison.modeJump 1 =
        (diagonal (![-1, 1] : Fin 2 → ℂ)) ⊗ₖ J := rfl
    fin_cases k <;> fin_cases i <;> fin_cases j <;>
      norm_num [lowering, hj, hj', J,
        Matrix.reindex_apply, Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.diagonal_apply,
        h0, h1, h2, h3, gibbsWeights, rates_exact.1, rates_exact.2]
  have hcomm : gibbsD * lowering k = (lowerRate / upperRate) • (lowering k * gibbsD) := by
    ext i j
    simpa only [gibbsD, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply,
      Complex.real_smul, Complex.ofReal_mul, mul_assoc, mul_comm (lowering k i j)] using h i j
  have hdet : IsUnit gibbsD.det := gibbsD.isUnit_iff_isUnit_det.mp gibbsD_pos.isUnit
  rw [hcomm, Matrix.smul_mul, Matrix.mul_nonsing_inv_cancel_right _ _ hdet]

private theorem gibbsD_log :
    CFC.log gibbsD =
      (-Real.log (rateDenominator ^ 2) : ℂ) • 1 +
        ((2 * temperature : ℝ) : ℂ) • charge := by
  have hweights (i : Fin 4) :
      Real.log (gibbsWeights i) =
        -Real.log (rateDenominator ^ 2) + (2 * temperature) * (![(-1 : ℝ), 0, 0, 1] i) := by
    have hlogneg : Real.log lowerRate = -temperature - Real.log rateDenominator := by
      rw [lowerRate, Real.log_div (Real.exp_pos _).ne' rateDenominator_pos.ne', Real.log_exp]
    have hlogpos : Real.log upperRate = temperature - Real.log rateDenominator := by
      rw [upperRate, Real.log_div (Real.exp_pos _).ne' rateDenominator_pos.ne', Real.log_exp]
    fin_cases i <;>
      norm_num [gibbsWeights, Real.log_pow,
        Real.log_mul lowerRate_pos.ne' upperRate_pos.ne', hlogneg, hlogpos] <;>
      ring
  have hcfc :
      CFC.log gibbsD = diagonal (fun i => (Real.log (gibbsWeights i) : ℂ)) := by
    simpa only [CFC.log, gibbsD, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
      Matrix.cfc_diagonal_real (𝕜 := ℂ) gibbsWeights Real.log
  rw [hcfc]
  ext i j
  by_cases hij : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq, hweights]
    fin_cases i <;> norm_num [charge, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      Matrix.diagonal_apply_eq, Complex.ofReal_add, Complex.ofReal_mul, smul_eq_mul]
  · simp [charge, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hij,
      Matrix.diagonal_apply_ne _ hij]

/-- The embedded generator trace in Wu (2.4) at exponent three, evaluated on
the Gibbs embedding of \(\rho^{1/3}\). -/
def physicalCubicEnergy (ρ : Mat) : ℝ :=
  let G := mpow gibbsD (1 / (2 * 3))
  let H := mpow gibbsD (-(1 / (2 * 3)))
  let M := mpow ρ (1 / 3)
  let X := H * M * H
  (mpow (G * X * G) (3 - 1) * (G *
      (∑ k : Fin 2, pairedGenerator lowerRate upperRate (lowering k) X) * G)).trace.re /
    (4 * (1 / 3 : ℝ) * (1 - 1 / 3))

private theorem roots_pos (i : Fin 4) : 0 < roots i := by
  fin_cases i <;> norm_num [roots]

private theorem spectrum_pos (i : Fin 4) : 0 < certificateSpectrum i :=
  div_pos (pow_pos (roots_pos i) _) (by norm_num)

private theorem mixed_rpow (x : ℝ) (i j : Fin 4) :
    (Real.exp x / rateDenominator * certificateSpectrum i) ^ (1 - 1 / 3 : ℝ) *
      (Real.exp (-x) / rateDenominator * certificateSpectrum j) ^ (1 / 3 : ℝ) =
    (Real.exp (x / 3) / rateDenominator) * (roots i ^ 2 * roots j / 2375254) := by
  let d : ℝ := rateDenominator * 2375254
  have hd : 0 < d := mul_pos rateDenominator_pos (by norm_num)
  have hentry (y : ℝ) (k : Fin 4) :
      Real.exp y / rateDenominator * certificateSpectrum k = Real.exp y * roots k ^ 3 / d := by
    unfold WuCubicOccupationEnvelope.spectrum spectrumOf d
    ring
  rw [hentry, hentry,
    Real.div_rpow (mul_pos (Real.exp_pos x) (pow_pos (roots_pos i) 3)).le hd.le,
    Real.div_rpow (mul_pos (Real.exp_pos (-x)) (pow_pos (roots_pos j) 3)).le hd.le,
    Real.mul_rpow (Real.exp_pos x).le (pow_pos (roots_pos i) 3).le,
    Real.mul_rpow (Real.exp_pos (-x)).le (pow_pos (roots_pos j) 3).le,
    ← Real.exp_mul, ← Real.exp_mul,
    ← Real.rpow_natCast_mul (roots_pos i).le, ← Real.rpow_natCast_mul (roots_pos j).le]
  norm_num only [Nat.cast_ofNat, show (3 * (1 - 1 / 3) : ℝ) = 2 by norm_num,
    show (3 * (1 / 3) : ℝ) = 1 by norm_num, Real.rpow_two, Real.rpow_one]
  rw [div_mul_div_comm, ← Real.rpow_add hd, show (2 / 3 + 1 / 3 : ℝ) = 1 by norm_num,
    Real.rpow_one, mul_mul_mul_comm, ← Real.exp_add,
    show x * (2 / 3) + -x * (1 / 3) = x / 3 by ring]
  unfold d
  ring

private theorem cubic_kernel (i j : Fin 4) :
    2 * Real.cosh temperature *
        coshEdgeKernel (1 / 3) (upperRate * certificateSpectrum i)
          (lowerRate * certificateSpectrum j) =
      (Real.cosh temperature + Real.sinh temperature) / 2 * certificateSpectrum i +
      (Real.cosh temperature - Real.sinh temperature) / 2 * certificateSpectrum j -
      (Real.cosh (temperature / 3) + Real.sinh (temperature / 3)) / 2 *
        (roots i ^ 2 * roots j / 2375254) -
      (Real.cosh (temperature / 3) - Real.sinh (temperature / 3)) / 2 *
        (roots i * roots j ^ 2 / 2375254) := by
  rw [← edgeKernel_eq_cosh (by norm_num : (0 : ℝ) < 1 / 3)
    (by norm_num : (1 / 3 : ℝ) < 1) (mul_nonneg upperRate_pos.le (spectrum_pos i).le)
    (mul_nonneg lowerRate_pos.le (spectrum_pos j).le)]
  change _ * ((_ + _ -
    ((lowerRate * certificateSpectrum j) ^ (1 - 1 / 3 : ℝ) *
       (upperRate * certificateSpectrum i) ^ (1 / 3 : ℝ) +
     (upperRate * certificateSpectrum i) ^ (1 - 1 / 3 : ℝ) *
       (lowerRate * certificateSpectrum j) ^ (1 / 3 : ℝ))) / 2) = _
  have hneg := mixed_rpow (-temperature) j i
  rw [neg_neg, neg_div] at hneg
  rw [lowerRate, upperRate, mixed_rpow temperature i j, hneg]
  simp only [Real.cosh_add_sinh, Real.cosh_sub_sinh]
  field_simp [rateDenominator_pos.ne']
  ring

private theorem sum_ascending (F : Fin 4 → Fin 4 → ℝ) :
    (∑ i, ∑ j, F i j) = ∑ i, ∑ j, F (ascendingIndex i) (ascendingIndex j) := by
  rw [← Equiv.sum_comp ascendingIndex (fun i => ∑ j, F i j)]
  exact Finset.sum_congr rfl fun i _ => (Equiv.sum_comp ascendingIndex (F (ascendingIndex i))).symm

private theorem physicalCubicEnergy_eq {ρ : Mat} (hρ : ρ.PosDef)
    (hspectrum : eigenvalue hρ.isHermitian = certificateSpectrum) :
    physicalCubicEnergy ρ = cubicEnergy (weight hρ.isHermitian) := by
  let K (i j : Fin 4) :=
    coshEdgeKernel (1 / 3) (upperRate * hρ.isHermitian.eigenvalues i)
      (lowerRate * hρ.isHermitian.eigenvalues j)
  let E := ∑ k : Fin 2, ∑ i, ∑ j, edgeWeight hρ.isHermitian (lowering k) i j * K i j
  have htrace := generatorTrace_eq_cosh gibbsD_pos hρ.posSemidef
    (fun _ : Fin 2 => lowerRate) (fun _ => upperRate) lowering
    (s := 3) (by norm_num) (fun _ => lowerRate_pos) (fun _ => upperRate_pos)
    gibbs_modular_relation
  have henergy : physicalCubicEnergy ρ = (9 / 2 : ℝ) * E := by
    let g : ℝ := 1 / (2 * 3)
    let G := mpow gibbsD g
    let H := mpow gibbsD (-g)
    let M := mpow ρ (1 / 3)
    have hinverse (t : ℝ) : mpow gibbsD t * mpow gibbsD (-t) = 1 := by
      unfold mpow
      simp_rw [← CFC.rpow_eq_cfc_real gibbsD_pos.posSemidef.nonneg]
      rw [← CFC.rpow_add gibbsD_pos.isUnit, add_neg_cancel,
        CFC.rpow_zero gibbsD gibbsD_pos.posSemidef.nonneg]
    have hGH : G * H = 1 := hinverse g
    have hHG : H * G = 1 := by
      simpa only [neg_neg] using hinverse (-g)
    have hembed : G * (H * M * H) * G = M := by
      rw [← Matrix.mul_assoc G (H * M) H, ← Matrix.mul_assoc G H M, hGH,
        one_mul, Matrix.mul_assoc M H G, hHG, mul_one]
    unfold physicalCubicEnergy
    dsimp only at htrace ⊢
    change _ = E at htrace
    rw [hembed, ← htrace]
    ring
  have hE : E = ∑ i, ∑ j, weight hρ.isHermitian i j *
      coshEdgeKernel (1 / 3) (upperRate * certificateSpectrum i)
        (lowerRate * certificateSpectrum j) := by
    have hreindex : E = ∑ k : Fin 2, ∑ i, ∑ j,
        edgeWeight hρ.isHermitian (lowering k) (ascendingIndex i) (ascendingIndex j) *
          K (ascendingIndex i) (ascendingIndex j) :=
      Finset.sum_congr rfl (fun k _ => sum_ascending _)
    rw [hreindex]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    unfold weight K
    rw [← Finset.sum_mul]
    change _ * coshEdgeKernel _ (upperRate * eigenvalue hρ.isHermitian i)
      (lowerRate * eigenvalue hρ.isHermitian j) = _
    rw [hspectrum]
  have hscaled : 2 * Real.cosh temperature * E =
      scaledCubicEnergy (Real.cosh temperature) (Real.sinh temperature)
        (Real.cosh (temperature / 3)) (Real.sinh (temperature / 3))
        roots 2375254 (weight hρ.isHermitian) := by
    rw [hE, scaledCubicEnergy]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [mul_left_comm, cubic_kernel]
    rfl
  rw [henergy, cubicEnergy, ← hscaled]
  field_simp [(Real.cosh_pos temperature).ne']
  ring

private theorem trace_mul_cfc_self {ρ : Mat} (hρ : ρ.IsHermitian) (f : ℝ → ℝ) :
    (ρ * cfc f ρ).trace.re = ∑ i, eigenvalue hρ i * f (eigenvalue hρ i) := by
  let U := hρ.eigenvectorUnitary
  let e := Unitary.conjStarAlgAut ℂ Mat U
  have hdiag : e.symm ρ = diagonal (fun i => (hρ.eigenvalues i : ℂ)) := by
    change (Unitary.conjStarAlgAut ℂ Mat U).symm ρ = _
    rw [Unitary.conjStarAlgAut_symm]
    exact hρ.conjStarAlgAut_star_eigenvectorUnitary
  have hcfc : e.symm (cfc f ρ) = diagonal (fun i => (f (hρ.eigenvalues i) : ℂ)) := by
    simp only [hρ.cfc_eq, Matrix.IsHermitian.cfc, e, U, StarAlgEquiv.symm_apply_apply,
      RCLike.ofReal_eq_complex_ofReal]
    rfl
  rw [← trace_inFrame hρ (ρ * cfc f ρ)]
  change (e.symm (ρ * cfc f ρ)).trace.re = _
  rw [map_mul, hdiag, hcfc]
  simp only [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal,
    Complex.re_sum, ← Complex.ofReal_mul, Complex.ofReal_re, eigenvalue]
  exact (Equiv.sum_comp ascendingIndex (fun i => hρ.eigenvalues i * f (hρ.eigenvalues i))).symm

private def density (A : Mat) (hA : A.PosDef) (htr : A.trace = 1) :
    DensityState (Fin 4) :=
  ⟨CStarMatrix.ofMatrix A,
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hA.posSemidef.nonneg, htr⟩

/-- The ordinary relative entropy against the same product Gibbs reference. -/
def physicalRelativeEntropy (ρ : Mat) (hρ : ρ.PosDef) (htr : ρ.trace = 1) : ℝ :=
  quantumRelativeEntropy (density ρ hρ htr) (density gibbsD gibbsD_pos gibbsD_trace)

private theorem physicalRelativeEntropy_eq {ρ : Mat} (hρ : ρ.PosDef) (htr : ρ.trace = 1)
    (hspectrum : eigenvalue hρ.isHermitian = certificateSpectrum) :
    physicalRelativeEntropy ρ hρ htr = relativeEntropy (occupationMoment hρ.isHermitian) := by
  change (ρ * (CFC.log ρ - CFC.log gibbsD)).trace.re = _
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, CFC.log, trace_mul_cfc_self hρ.isHermitian,
    hspectrum, gibbsD_log]
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, htr]
  simp only [Complex.add_re, smul_eq_mul, mul_one, Complex.neg_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero,
    ← occupationMoment_eq_trace hρ.isHermitian]
  have hmass : (∑ i, certificateSpectrum i) = 1 := by
    norm_num [WuCubicOccupationEnvelope.spectrum, spectrumOf, roots, Fin.sum_univ_four]
  have hlogs : (∑ i, certificateSpectrum i * Real.log (4 * certificateSpectrum i)) =
      (∑ i, certificateSpectrum i * Real.log (certificateSpectrum i)) + Real.log 4 := by
    simp_rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (spectrum_pos _).ne', mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hmass, one_mul, add_comm]
  have hZ : Real.log (rateDenominator ^ 2) =
      Real.log 4 + 2 * Real.log (Real.cosh temperature) := by
    rw [show rateDenominator ^ 2 = 4 * Real.cosh temperature ^ 2 by ring,
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (pow_pos (Real.cosh_pos _) _).ne',
      Real.log_pow]
    norm_num
  rw [relativeEntropy, entropyConstant, hlogs, hZ]
  ring

private theorem sharpCoefficient_eq_wu :
    sharpCoefficient =
      (9 / 2 : ℝ) * Real.sinh (temperature / 3) * Real.sinh (2 * temperature / 3) /
        (2 * temperature * Real.sinh temperature) := by
  have ht : 0 < temperature := mul_pos (by norm_num) (Real.log_pos (by norm_num))
  have hdiff : Real.cosh temperature - Real.cosh (temperature / 3) =
      2 * Real.sinh (2 * temperature / 3) * Real.sinh (temperature / 3) := by
    have hadd : 2 * temperature / 3 + temperature / 3 = temperature := by ring
    have hsub : 2 * temperature / 3 - temperature / 3 = temperature / 3 := by ring
    calc
      _ = Real.cosh (2 * temperature / 3 + temperature / 3) -
          Real.cosh (2 * temperature / 3 - temperature / 3) := by rw [hadd, hsub]
      _ = _ := by rw [Real.cosh_add, Real.cosh_sub]; ring
  change 9 / (4 * Real.cosh temperature) *
    ((Real.cosh temperature - Real.cosh (temperature / 3)) *
      Real.cosh temperature / Real.sinh temperature / (2 * temperature)) = _
  rw [hdiff]
  field_simp [(Real.cosh_pos temperature).ne', ht.ne', (Real.sinh_pos_iff.mpr ht).ne']
  ring

/-- At Wu's cubic exponent and the certificate temperature and spectrum, the
physical energy exceeds the sharp coefficient times the Gibbs relative
entropy by a strictly positive, explicit amount for every complex density. -/
theorem matrix_level_Wu_cubic_lower_bound {ρ : Mat}
    (hρ : ρ.PosDef) (htr : ρ.trace = 1)
    (hspectrum : eigenvalue hρ.isHermitian = certificateSpectrum) :
    let α := (9 / 2 : ℝ) * Real.sinh (temperature / 3) * Real.sinh (2 * temperature / 3) /
      (2 * temperature * Real.sinh temperature)
    (1 / 8000 : ℝ) < (4 * Real.cosh temperature / 9) *
      (physicalCubicEnergy ρ - α * physicalRelativeEntropy ρ hρ htr) := by
  dsimp only
  rw [physicalCubicEnergy_eq hρ hspectrum, physicalRelativeEntropy_eq hρ htr hspectrum,
    ← sharpCoefficient_eq_wu]
  exact cubic_deficit_gt (certificateConstraints hρ.isHermitian hspectrum)

end D5.S3.Quantum.Semigroups.WuCubicSpectralCertificate
