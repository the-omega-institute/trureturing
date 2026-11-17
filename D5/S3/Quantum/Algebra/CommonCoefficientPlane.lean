/- GID: D5/S3/Quantum/Algebra/CommonCoefficientPlane
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/CommonCoefficientPlane
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An independent complex 3-by-5 matrix triple with injective stack has a common neutral coefficient plane. -/

import D5.S3.Quantum.Algebra.GramUnitaryExtension
import D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

/-!
# A common complex coefficient plane

For an independent triple of complex maps from dimension five to dimension three,
with injective vertical stack, the Hermitian coefficient kernel has one common
two-dimensional totally isotropic complex subspace. Coefficient changes act on
the forms by adjoint congruence, and the plane is transported by the inverse change.

Scope warning (I): the main conclusion fixes coefficient width three, matrix
dimensions 3 by 5, and plane dimension two. Its rank and kernel arguments use
these dimensions, which remain part of its hypotheses when the result is reused.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix Module
open scoped BigOperators ComplexOrder

namespace D5.S3.Quantum.Algebra.CommonCoefficientPlane

open D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction

def compression {a b : ℕ} (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (T : Matrix (Fin 3) (Fin 3) ℂ) :=
  (stack X)ᴴ * Matrix.kronecker T (1 : Matrix (Fin a) (Fin a) ℂ) * stack X

def mix {a b : ℕ} (A : Matrix (Fin 3) (Fin 3) ℂ)
    (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ) :
    Fin 3 → Matrix (Fin a) (Fin b) ℂ := fun r => ∑ s, A r s • X s

theorem compression_eq_sum {a b : ℕ}
    (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (T : Matrix (Fin 3) (Fin 3) ℂ) :
    compression X T = ∑ r, ∑ s, T r s • ((X r)ᴴ * X s) := by
  classical
  ext j k
  simp only [compression, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, stack, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext s
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem coefficient_rank_le_two
    (X : Fin 3 → Matrix (Fin 3) (Fin 5) ℂ)
    (hinj : Function.Injective (stack X).mulVecLin)
    (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : compression X T = 0) : T.rank ≤ 2 := by
  let S := stack X
  let Q := Matrix.kronecker T (1 : Matrix (Fin 3) (Fin 3) ℂ)
  have hS : S.rank = 5 := by
    change finrank ℂ (LinearMap.range S.mulVecLin) = 5
    rw [LinearMap.finrank_range_of_inj hinj]
    simp
  have hleft := Matrix.rank_mul_ge Sᴴ Q
  have hright := Matrix.rank_mul_ge (Sᴴ * Q) S
  have hQ : Q.rank = 3 * T.rank := rank_kronecker_one T 3
  have hz : (Sᴴ * Q * S).rank = 0 := by rw [show Sᴴ * Q * S = 0 from hT]; simp
  simp only [Matrix.rank_conjTranspose, hS, Fintype.card_prod,
    Fintype.card_fin] at hleft hright
  omega

private theorem semidefinite_coefficient_kernel {a b k : ℕ}
    (X : Fin k → Matrix (Fin a) (Fin b) ℂ)
    (hX : LinearIndependent ℂ X)
    (T : Matrix (Fin k) (Fin k) ℂ) (hT : T.PosSemidef)
    (hPhi : (∑ r, ∑ s, T r s • ((X r)ᴴ * X s)) = 0) : T = 0 := by
  classical
  have hquad (j : Fin b) :
      ∑ i : Fin a, star (fun r => X r i j) ⬝ᵥ
        (T *ᵥ (fun r => X r i j)) = 0 := by
    have hd := congrArg (fun A : Matrix (Fin b) (Fin b) ℂ => A j j) hPhi
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.zero_apply] at hd
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
    calc
      _ = ∑ r : Fin k, ∑ i : Fin a, ∑ s : Fin k,
          star (X r i j) * (T r s * X s i j) := by
        rw [Finset.sum_comm]
      _ = ∑ r : Fin k, ∑ s : Fin k, ∑ i : Fin a,
          star (X r i j) * (T r s * X s i j) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [Finset.sum_comm]
      _ = ∑ r : Fin k, ∑ s : Fin k, T r s * ∑ i : Fin a,
          (star (X r i j) * X s i j) := by
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro s hs
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by simpa only [mul_assoc, mul_left_comm, mul_comm] using hd
  have hker (i : Fin a) (j : Fin b) : T *ᵥ (fun r => X r i j) = 0 := by
    apply hT.dotProduct_mulVec_zero_iff.mp
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin a))) =>
        hT.dotProduct_mulVec_nonneg (fun r => X r i j))).mp (hquad j) i
          (Finset.mem_univ i)
  ext r s
  apply Fintype.linearIndependent_iff.mp hX (fun s => T r s) ?_ s
  ext i j
  simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.zero_apply, Matrix.mulVec, dotProduct, Pi.zero_apply] using
      congrFun (hker i j) r


theorem semidefinite_eq_zero {a b : ℕ}
    (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ) (hX : LinearIndependent ℂ X)
    (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : T.PosSemidef)
    (hPhi : compression X T = 0) : T = 0 := by
  apply semidefinite_coefficient_kernel X hX T hT
  simpa only [compression_eq_sum] using hPhi

private theorem stack_mix {a b : ℕ} (A : Matrix (Fin 3) (Fin 3) ℂ)
    (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ) :
    stack (mix A X) = Matrix.kronecker A (1 : Matrix (Fin a) (Fin a) ℂ) * stack X := by
  classical
  ext ⟨r, i⟩ j
  simp [stack, mix, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.sum_apply, Matrix.smul_apply]

theorem compression_mix {a b : ℕ} (A : Matrix (Fin 3) (Fin 3) ℂ)
    (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (T : Matrix (Fin 3) (Fin 3) ℂ) :
    compression (mix A X) T = compression X (Aᴴ * T * A) := by
  have hstar : (Matrix.kronecker A (1 : Matrix (Fin a) (Fin a) ℂ))ᴴ =
      Matrix.kronecker Aᴴ (1 : Matrix (Fin a) (Fin a) ℂ) := by
    simpa only [Matrix.kronecker, Matrix.conjTranspose_one] using
      Matrix.conjTranspose_kronecker A (1 : Matrix (Fin a) (Fin a) ℂ)
  simp only [compression, stack_mix, Matrix.conjTranspose_mul]
  rw [hstar]
  rw [show (stack X)ᴴ * (Matrix.kronecker Aᴴ (1 : Matrix (Fin a) (Fin a) ℂ)) *
      Matrix.kronecker T (1 : Matrix (Fin a) (Fin a) ℂ) *
      (Matrix.kronecker A (1 : Matrix (Fin a) (Fin a) ℂ) * stack X) =
      (stack X)ᴴ * ((Matrix.kronecker Aᴴ (1 : Matrix (Fin a) (Fin a) ℂ) *
      Matrix.kronecker T (1 : Matrix (Fin a) (Fin a) ℂ)) *
      Matrix.kronecker A (1 : Matrix (Fin a) (Fin a) ℂ)) * stack X by
        simp only [Matrix.mul_assoc]]
  simp only [Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp

private theorem pairing_congruence {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) (T : Matrix m m ℂ) (u v : n → ℂ) :
    star (A *ᵥ u) ⬝ᵥ (T *ᵥ (A *ᵥ v)) =
      star u ⬝ᵥ ((Aᴴ * T * A) *ᵥ v) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem common_plane_transport
    (K : Set (Matrix (Fin 3) (Fin 3) ℂ))
    (A : Matrix (Fin 3) (Fin 3) ℂ) (hA : IsUnit A)
    (L : Submodule ℂ (Fin 3 → ℂ)) (hdim : finrank ℂ L = 2)
    (hL : ∀ T ∈ K, ∀ u ∈ L, ∀ v ∈ L,
      star u ⬝ᵥ ((Aᴴ * T * A) *ᵥ v) = 0) :
    ∃ L' : Submodule ℂ (Fin 3 → ℂ), finrank ℂ L' = 2 ∧
      ∀ T ∈ K, ∀ u ∈ L', ∀ v ∈ L', star u ⬝ᵥ (T *ᵥ v) = 0 := by
  let L' := L.map A.mulVecLin
  refine ⟨L', ?_, ?_⟩
  · have hi : Function.Injective (A.mulVecLin.domRestrict L) :=
      (Matrix.mulVec_injective_iff_isUnit.mpr hA).comp Subtype.val_injective
    have he := LinearMap.finrank_range_of_inj hi
    rw [LinearMap.range_domRestrict] at he
    exact he.trans hdim
  · intro T hT u hu v hv
    obtain ⟨u, hu, rfl⟩ := hu
    obtain ⟨v, hv, rfl⟩ := hv
    exact (pairing_congruence A T u v).trans (hL T hT u hu v hv)

private theorem spectral_signs
    (X : Fin 3 → Matrix (Fin 3) (Fin 5) ℂ) (hX : LinearIndependent ℂ X)
    (hinj : Function.Injective (stack X).mulVecLin)
    (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : T.IsHermitian)
    (hPhi : compression X T = 0) (hne : T ≠ 0) :
    ∃ e : Fin 3 ≃ Fin 3,
      0 < hT.eigenvalues (e 0) ∧ hT.eigenvalues (e 1) < 0 ∧
      hT.eigenvalues (e 2) = 0 := by
  classical
  have hnotP : ¬ T.PosSemidef := fun h => hne (semidefinite_eq_zero X hX T h hPhi)
  have hnotN : ¬ (-T).PosSemidef := by
    intro h
    have hPhiN : compression X (-T) = 0 := by
      rw [compression_eq_sum]
      change (∑ r, ∑ s, -(T r s) • ((X r)ᴴ * X s)) = 0
      simp only [neg_smul, Finset.sum_neg_distrib]
      rw [← compression_eq_sum, hPhi, neg_zero]
    have he := semidefinite_eq_zero X hX (-T) h hPhiN
    exact hne (neg_eq_zero.mp he)
  obtain ⟨j, hj⟩ : ∃ j, hT.eigenvalues j < 0 := by
    by_contra h
    apply hnotP
    apply hT.posSemidef_iff_eigenvalues_nonneg.mpr
    intro j
    exact le_of_not_gt (fun hj => h ⟨j, hj⟩)
  obtain ⟨i, hi⟩ : ∃ i, 0 < hT.eigenvalues i := by
    by_contra h
    have hnonpos : ∀ i, hT.eigenvalues i ≤ 0 := by
      intro i
      exact le_of_not_gt (fun hi => h ⟨i, hi⟩)
    have hd : (Matrix.diagonal (fun i => (-(hT.eigenvalues i) : ℂ))).PosSemidef := by
      apply Matrix.posSemidef_diagonal_iff.mpr
      intro i
      exact_mod_cast neg_nonneg.mpr (hnonpos i)
    have hp := hd.mul_mul_conjTranspose_same (hT.eigenvectorUnitary : Matrix (Fin 3) (Fin 3) ℂ)
    apply hnotN
    have hs := hT.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hs
    rw [hs]
    convert hp using 1
    rw [Matrix.star_eq_conjTranspose]
    simp only [Function.comp_def]
    rw [show (Matrix.diagonal fun i => -(hT.eigenvalues i : ℂ)) =
        -(Matrix.diagonal fun i => (hT.eigenvalues i : ℂ)) by
      ext r s; by_cases hrs : r = s <;> simp [hrs]]
    rw [Matrix.mul_neg, Matrix.neg_mul]
    rfl
  have hij : i ≠ j := by intro he; subst j; linarith
  have hc : ({i, j} : Finset (Fin 3)).card < (Finset.univ : Finset (Fin 3)).card := by
    simp [hij]
  obtain ⟨k, hk, hkn⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  have hki : k ≠ i := by exact fun he => hkn (by simp [he])
  have hkj : k ≠ j := by
    exact fun he => hkn (by simp [he])
  let f : Fin 3 → Fin 3 := ![i, j, k]
  have hf : Function.Injective f := by
    intro r s he
    fin_cases r <;> fin_cases s <;> simp_all [f]
  let e := Equiv.ofBijective f ((Finite.injective_iff_bijective).mp hf)
  have hknz : hT.eigenvalues k = 0 := by
    by_contra hknz
    have hall : ∀ r, hT.eigenvalues r ≠ 0 := by
      intro r
      obtain ⟨s, rfl⟩ := e.surjective r
      fin_cases s
      · exact ne_of_gt hi
      · exact ne_of_lt hj
      · exact hknz
    have hcard : Fintype.card {r // hT.eigenvalues r ≠ 0} = 3 := by
      simp [hall]
    have hr := coefficient_rank_le_two X hinj T hPhi
    rw [hT.rank_eq_card_non_zero_eigs, hcard] at hr
    omega
  exact ⟨e, hi, hj, hknz⟩

def signature : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal ![1, -1, 0]

theorem signature_congruence
    (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : T.IsHermitian)
    (e : Fin 3 ≃ Fin 3)
    (hp : 0 < hT.eigenvalues (e 0)) (hn : hT.eigenvalues (e 1) < 0)
    (hz : hT.eigenvalues (e 2) = 0) :
    ∃ B : Matrix (Fin 3) (Fin 3) ℂ, IsUnit B ∧ Bᴴ * T * B = signature := by
  classical
  let U : Matrix (Fin 3) (Fin 3) ℂ := hT.eigenvectorUnitary
  let E : Matrix (Fin 3) (Fin 3) ℂ := (1 : Matrix (Fin 3) (Fin 3) ℂ).submatrix (Equiv.refl _) e
  let c : Fin 3 → ℂ := ![((Real.sqrt (hT.eigenvalues (e 0)))⁻¹ : ℝ),
    ((Real.sqrt (-hT.eigenvalues (e 1)))⁻¹ : ℝ), 1]
  let C := E * Matrix.diagonal c
  let B := U * C
  have hE : IsUnit E := Matrix.isUnit_submatrix_equiv (Equiv.refl _) e |>.mpr isUnit_one
  have hc : ∀ r, c r ≠ 0 := by
    intro r
    fin_cases r
    · simpa [c] using (inv_ne_zero (Real.sqrt_ne_zero'.mpr hp))
    · simpa [c] using (inv_ne_zero (Real.sqrt_ne_zero'.mpr (neg_pos.mpr hn)))
    · simp [c]
  have hC : IsUnit C := hE.mul (Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr
    (fun r => isUnit_iff_ne_zero.mpr (hc r))))
  have hU : IsUnit U := Unitary.isUnit_coe
  refine ⟨B, hU.mul hC, ?_⟩
  have hs : Uᴴ * T * U = Matrix.diagonal (fun r => (hT.eigenvalues r : ℂ)) := by
    simpa [U, Unitary.conjStarAlgAut_star_apply, Function.comp_def,
      Matrix.star_eq_conjTranspose] using
      hT.conjStarAlgAut_star_eigenvectorUnitary
  have hEdiag : Eᴴ * Matrix.diagonal (fun r => (hT.eigenvalues r : ℂ)) * E =
      Matrix.diagonal (fun r => (hT.eigenvalues (e r) : ℂ)) := by
    ext r s
    simp [E, Matrix.mul_apply, Matrix.one_apply,
      Matrix.diagonal_apply, Equiv.injective e |>.eq_iff]
    split_ifs with hrs
    · subst s; rfl
    · rfl
  change (U * (E * Matrix.diagonal c))ᴴ * T * (U * (E * Matrix.diagonal c)) = _
  simp only [Matrix.conjTranspose_mul]
  calc
    _ = (Matrix.diagonal c)ᴴ * (Eᴴ * (Uᴴ * T * U) * E) * Matrix.diagonal c := by
      simp only [Matrix.mul_assoc]
    _ = (Matrix.diagonal c)ᴴ * Matrix.diagonal (fun r => (hT.eigenvalues (e r) : ℂ)) *
        Matrix.diagonal c := by rw [hs, hEdiag]
    _ = signature := by
      rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      apply congrArg Matrix.diagonal
      funext r
      fin_cases r
      · have he : (Real.sqrt (hT.eigenvalues (e 0)))⁻¹ * hT.eigenvalues (e 0) *
            (Real.sqrt (hT.eigenvalues (e 0)))⁻¹ = 1 := by
          have hsqrt := Real.sq_sqrt hp.le
          have hne := Real.sqrt_ne_zero'.mpr hp
          field_simp
          nlinarith
        simpa [c] using congrArg (fun x : ℝ => (x : ℂ)) he
      · have he : (Real.sqrt (-hT.eigenvalues (e 1)))⁻¹ * hT.eigenvalues (e 1) *
            (Real.sqrt (-hT.eigenvalues (e 1)))⁻¹ = -1 := by
          have hsqrt := Real.sq_sqrt (neg_nonneg.mpr hn.le)
          have hne := Real.sqrt_ne_zero'.mpr (neg_pos.mpr hn)
          field_simp
          nlinarith
        simpa [c] using congrArg (fun x : ℝ => (x : ℂ)) he
      · simp [c, hz]

private theorem linearIndependent_mix {a b : ℕ}
    (A : Matrix (Fin 3) (Fin 3) ℂ) (hA : IsUnit A)
    (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ) (hX : LinearIndependent ℂ X) :
    LinearIndependent ℂ (mix A X) := by
  exact hX.sum_smul_of_nondegenerate
    (Matrix.nondegenerate_of_det_ne_zero ((Matrix.isUnit_iff_isUnit_det A).mp hA).ne_zero)

theorem injective_stack_mix {a b : ℕ}
    (A : Matrix (Fin 3) (Fin 3) ℂ) (hA : IsUnit A)
    (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (hinj : Function.Injective (stack X).mulVecLin) :
    Function.Injective (stack (mix A X)).mulVecLin := by
  have hK : IsUnit (Matrix.kronecker A (1 : Matrix (Fin a) (Fin a) ℂ)) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    simp only [Matrix.kronecker, Matrix.det_kronecker, Matrix.det_one, one_pow, mul_one]
    exact ((Matrix.isUnit_iff_isUnit_det A).mp hA).pow _
  rw [stack_mix, Matrix.mulVecLin_mul]
  exact (Matrix.mulVec_injective_iff_isUnit.mpr hK).comp hinj

private theorem zero_kernel_plane
    (X : Fin 3 → Matrix (Fin 3) (Fin 5) ℂ)
    (hzero : ∀ T : Matrix (Fin 3) (Fin 3) ℂ,
      T.IsHermitian → compression X T = 0 → T = 0) :
    ∃ L : Submodule ℂ (Fin 3 → ℂ), finrank ℂ L = 2 ∧
      ∀ T : Matrix (Fin 3) (Fin 3) ℂ, T.IsHermitian → compression X T = 0 →
        ∀ u ∈ L, ∀ v ∈ L, star u ⬝ᵥ (T *ᵥ v) = 0 := by
  let J : Matrix (Fin 3) (Fin 2) ℂ := !![1, 0; 0, 1; 0, 0]
  have hJ : Function.Injective J.mulVecLin := by
    intro u v he
    funext r
    fin_cases r
    · simpa [J, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun he 0
    · simpa [J, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun he 1
  refine ⟨LinearMap.range J.mulVecLin, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hJ]
    simp
  · intro T hT hPhi u hu v hv
    rw [hzero T hT hPhi]
    simp

def phaseVector (w : ℂ) : Fin 3 → ℂ := ![1, w, 0]

theorem phaseVector_quad (T : Matrix (Fin 3) (Fin 3) ℂ) (w : ℂ) :
    star (phaseVector w) ⬝ᵥ (T *ᵥ phaseVector w) =
      T 0 0 + T 0 1 * w + star w * T 1 0 + star w * T 1 1 * w := by
  simp [phaseVector, Matrix.mulVec, dotProduct, Fin.sum_univ_three, mul_add]
  ring

theorem phase_plane
    (K : Set (Matrix (Fin 3) (Fin 3) ℂ)) (w : ℂ)
    (hK : ∀ T ∈ K, T.IsHermitian ∧ T 2 2 = 0 ∧
      T 2 0 + w * T 2 1 = 0 ∧
      star (phaseVector w) ⬝ᵥ (T *ᵥ phaseVector w) = 0) :
    ∃ L : Submodule ℂ (Fin 3 → ℂ), finrank ℂ L = 2 ∧
      ∀ T ∈ K, ∀ u ∈ L, ∀ v ∈ L, star u ⬝ᵥ (T *ᵥ v) = 0 := by
  classical
  let J : Matrix (Fin 3) (Fin 2) ℂ := !![0, 1; 0, w; 1, 0]
  have hJ : Function.Injective J.mulVecLin := by
    intro u v he
    funext r
    fin_cases r
    · simpa [J, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun he 2
    · simpa [J, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun he 0
  refine ⟨LinearMap.range J.mulVecLin, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hJ]; simp
  · intro T hT u hu v hv
    obtain ⟨u, rfl⟩ := hu
    obtain ⟨v, rfl⟩ := hv
    change star (J *ᵥ u) ⬝ᵥ (T *ᵥ (J *ᵥ v)) = 0
    rw [pairing_congruence]
    have hcomp : Jᴴ * T * J = 0 := by
      obtain ⟨hHerm, h22, hcross, hquad⟩ := hK T hT
      have hreverse : T 0 2 + star w * T 1 2 = 0 := by
        have he := congrArg star hcross
        have h02 : star (T 2 0) = T 0 2 := congrFun (congrFun hHerm 0) 2
        have h12 : star (T 2 1) = T 1 2 := congrFun (congrFun hHerm 1) 2
        simpa only [star_add, star_mul, h02, h12, star_zero, mul_comm] using he
      ext r s
      fin_cases r <;> fin_cases s
      · simpa [J, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_three] using h22
      · simpa [J, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_three,
          mul_comm] using hcross
      · simpa [J, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_three,
          mul_comm] using hreverse
      · simpa [J, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_three,
          phaseVector, dotProduct, Matrix.mulVec, mul_add, add_mul,
          add_assoc, add_comm, add_left_comm, mul_assoc] using hquad
    rw [hcomp]
    simp

private theorem cross_pairing {a b : ℕ} (A B : Matrix (Fin a) (Fin b) ℂ)
    (x y : Fin b → ℂ) :
    star x ⬝ᵥ ((Aᴴ * B) *ᵥ y) = star (A *ᵥ x) ⬝ᵥ (B *ᵥ y) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]

theorem compression_pairing {a b : ℕ}
    (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (T : Matrix (Fin 3) (Fin 3) ℂ) (x y : Fin b → ℂ) :
    star x ⬝ᵥ (compression X T *ᵥ y) =
      ∑ r, ∑ s, T r s * (star (X r *ᵥ x) ⬝ᵥ (X s *ᵥ y)) := by
  rw [compression_eq_sum]
  simp only [Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, cross_pairing]

theorem gram_eq_of_signature {a b : ℕ}
    (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (hSig : compression X signature = 0) : (X 1)ᴴ * X 1 = (X 0)ᴴ * X 0 := by
  rw [compression_eq_sum] at hSig
  have he : (X 0)ᴴ * X 0 - (X 1)ᴴ * X 1 = 0 := by
    simpa [signature, Fin.sum_univ_three, Matrix.diagonal_apply, sub_eq_add_neg] using hSig
  exact (sub_eq_zero.mp he).symm

theorem stack_injective_on_common_kernel {a b : ℕ}
    (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (hinj : Function.Injective (stack X).mulVecLin)
    (x : Fin b → ℂ) (hx : ∀ r, X r *ᵥ x = 0) : x = 0 := by
  apply hinj
  change stack X *ᵥ x = stack X *ᵥ (0 : Fin b → ℂ)
  rw [Matrix.mulVec_zero]
  ext ⟨r, i⟩
  simpa [stack, Matrix.mulVec, dotProduct] using congrFun (hx r) i

theorem kernel_restriction_injective {a b : ℕ}
    (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (hinj : Function.Injective (stack X).mulVecLin)
    (U : Matrix (Fin a) (Fin a) ℂ) (hU : X 1 = U * X 0) :
    Function.Injective ((X 2).mulVecLin.domRestrict (LinearMap.ker (X 0).mulVecLin)) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  apply Subtype.ext
  change x.val = 0
  apply stack_injective_on_common_kernel X hinj
  intro r
  have h0 : X 0 *ᵥ x.val = 0 := x.property
  have h2 : X 2 *ᵥ x.val = 0 := hx
  fin_cases r
  · exact h0
  · change X 1 *ᵥ x.val = 0
    rw [hU, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
  · exact h2

private theorem normalized_rank_cases
    (X : Fin 3 → Matrix (Fin 3) (Fin 5) ℂ)
    (hinj : Function.Injective (stack X).mulVecLin)
    (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : X 1 = U * X 0) :
    (X 0).rank = 2 ∨ (X 0).rank = 3 := by
  have hdim := LinearMap.finrank_le_finrank_of_injective (kernel_restriction_injective X hinj U hU)
  have hsum := (X 0).mulVecLin.finrank_range_add_finrank_ker
  have hupper := (X 0).rank_le_card_height
  change (X 0).rank + finrank ℂ (LinearMap.ker (X 0).mulVecLin) = _ at hsum
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hdim hsum hupper
  omega

private theorem radical_le_neutral_plane
    (P : Submodule ℂ (Fin 3 → ℂ)) (hdim : finrank ℂ P = 2)
    (Q : Matrix (Fin 3) (Fin 3) ℂ) (hQ : Q.IsHermitian) (hne : Q ≠ 0)
    (hP : ∀ x ∈ P, ∀ y ∈ P, star x ⬝ᵥ (Q *ᵥ y) = 0) :
    LinearMap.ker Q.mulVecLin ≤ P := by
  classical
  have hsym (x y : Fin 3 → ℂ) :
      star (Q *ᵥ x) ⬝ᵥ y = star x ⬝ᵥ (Q *ᵥ y) := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hQ]
  by_cases hex : ∃ x ∈ P, Q *ᵥ x ≠ 0
  · obtain ⟨x, hx, hQx⟩ := hex
    let f : (Fin 3 → ℂ) →ₗ[ℂ] ℂ := {
      toFun := fun z => star (Q *ᵥ x) ⬝ᵥ z
      map_add' := fun y z => dotProduct_add _ _ _
      map_smul' := fun c z => dotProduct_smul _ _ _ }
    have hf : f (Q *ᵥ x) ≠ 0 := by
      exact fun he => hQx (dotProduct_star_self_eq_zero.mp he)
    have hsurj : Function.Surjective f := by
      intro c
      refine ⟨(c / f (Q *ᵥ x)) • (Q *ᵥ x), ?_⟩
      rw [map_smul]
      exact div_mul_cancel₀ c hf
    have hkerdim : finrank ℂ (LinearMap.ker f) = 2 := by
      have hs := f.finrank_range_add_finrank_ker
      rw [LinearMap.range_eq_top.mpr hsurj] at hs
      simp only [finrank_top, finrank_self, Module.finrank_fintype_fun_eq_card,
        Fintype.card_fin] at hs
      omega
    have hle : P ≤ LinearMap.ker f := by
      intro y hy
      change star (Q *ᵥ x) ⬝ᵥ y = 0
      rw [hsym]
      exact hP x hx y hy
    have heq : P = LinearMap.ker f := Submodule.eq_of_le_of_finrank_eq hle (hdim.trans hkerdim.symm)
    intro z hz
    rw [heq]
    change star (Q *ᵥ x) ⬝ᵥ z = 0
    rw [hsym, show Q *ᵥ z = 0 from hz]
    simp
  · have hle : P ≤ LinearMap.ker Q.mulVecLin := by
      intro x hx
      exact not_not.mp (fun h => hex ⟨x, hx, h⟩)
    have hproper : LinearMap.ker Q.mulVecLin ≠ ⊤ := by
      intro he
      apply hne
      apply Matrix.toLin'.injective
      change Q.mulVecLin = (0 : Matrix (Fin 3) (Fin 3) ℂ).mulVecLin
      rw [Matrix.mulVecLin_zero, ← LinearMap.ker_eq_top, he]
    have hlt := Submodule.finrank_lt hproper
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hlt
    have heq : P = LinearMap.ker Q.mulVecLin :=
      Submodule.eq_of_le_of_finrank_le hle (by omega)
    exact heq.ge

private theorem eigenphase_of_invariant_submodule
    (U : Matrix.unitaryGroup (Fin 3) ℂ)
    (N : Submodule ℂ (Fin 3 → ℂ)) (hN : 0 < finrank ℂ N)
    (hinv : ∀ v ∈ N, (U : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ v ∈ N) :
    ∃ w : ℂ, ∃ v : Fin 3 → ℂ,
      v ∈ N ∧ v ≠ 0 ∧ (U : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ v = w • v ∧ star w * w = 1 := by
  classical
  let : Nontrivial N := Module.nontrivial_of_finrank_pos hN
  let f : N →ₗ[ℂ] N := ((U : Matrix (Fin 3) (Fin 3) ℂ).mulVecLin.domRestrict N).codRestrict N
    (fun v => hinv v.val v.property)
  obtain ⟨w, hw⟩ := Module.End.exists_eigenvalue f
  obtain ⟨v, hv⟩ := hw.exists_hasEigenvector
  have hvne : v.val ≠ 0 := by
    intro he
    apply hv.2
    exact Subtype.ext he
  have heig : (U : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ v.val = w • v.val :=
    congrArg Subtype.val hv.apply_eq_smul
  refine ⟨w, v.val, v.property, hvne, heig, ?_⟩
  have hunit : (U : Matrix (Fin 3) (Fin 3) ℂ)ᴴ * (U : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self U
  have hnorm : star ((U : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ v.val) ⬝ᵥ
      ((U : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ v.val) = star v.val ⬝ᵥ v.val := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hunit,
      Matrix.one_mulVec]
  rw [heig, star_smul, smul_dotProduct, dotProduct_smul] at hnorm
  change star w * (w * (star v.val ⬝ᵥ v.val)) = star v.val ⬝ᵥ v.val at hnorm
  apply mul_right_cancel₀ (show star v.val ⬝ᵥ v.val ≠ 0 from
    fun he => hvne (dotProduct_star_self_eq_zero.mp he))
  simpa only [mul_assoc, one_mul] using hnorm

private theorem common_unitary_phase {ι : Type*}
    (A : Matrix (Fin 3) (Fin 5) ℂ) (hA : 2 ≤ A.rank)
    (U : Matrix.unitaryGroup (Fin 3) ℂ)
    (Q : ι → Matrix (Fin 3) (Fin 3) ℂ)
    (hHerm : ∀ i, (Q i).IsHermitian)
    (hcomm : ∀ i, Q i * (U : Matrix (Fin 3) (Fin 3) ℂ) = (U : Matrix (Fin 3) (Fin 3) ℂ) * Q i)
    (hcomp : ∀ i, Aᴴ * Q i * A = 0) :
    ∃ w : ℂ, ∃ v : Fin 3 → ℂ,
      v ≠ 0 ∧ (U : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ v = w • v ∧ star w * w = 1 ∧
      ∀ i, star v ⬝ᵥ (Q i *ᵥ v) = 0 := by
  classical
  by_cases hzero : ∀ i, Q i = 0
  · obtain ⟨w, v, hv, hvne, heig, hw⟩ := eigenphase_of_invariant_submodule U ⊤
      (by simp) (by simp)
    refine ⟨w, v, hvne, heig, hw, ?_⟩
    intro i
    rw [hzero i]
    simp
  · obtain ⟨i, hi⟩ := not_forall.mp hzero
    have hrank : A.rank + (Q i).rank + A.rank ≤ 6 := by
      have h1 := Matrix.rank_mul_ge Aᴴ (Q i)
      have h2 := Matrix.rank_mul_ge (Aᴴ * Q i) A
      rw [hcomp i, Matrix.rank_zero] at h2
      simp only [Matrix.rank_conjTranspose, Fintype.card_fin] at h1 h2
      omega
    have hQr : 0 < (Q i).rank := by
      by_contra h
      have hmap : (Q i).mulVecLin = 0 := by
        apply LinearMap.range_eq_bot.mp
        exact Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_not_pos h)
      exact hi (Matrix.toLin'.injective (by simpa only [Matrix.toLin'_apply', map_zero] using hmap))
    have hAr : A.rank = 2 := by omega
    let P := LinearMap.range A.mulVecLin
    have hPdim : finrank ℂ P = 2 := hAr
    have hP (j : ι) : ∀ x ∈ P, ∀ y ∈ P, star x ⬝ᵥ (Q j *ᵥ y) = 0 := by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      change star (A *ᵥ x) ⬝ᵥ (Q j *ᵥ (A *ᵥ y)) = 0
      rw [pairing_congruence, hcomp j]
      simp
    let N := LinearMap.ker (Q i).mulVecLin
    have hNdim : 0 < finrank ℂ N := by
      have hs := (Q i).mulVecLin.finrank_range_add_finrank_ker
      change (Q i).rank + finrank ℂ N = _ at hs
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hs
      omega
    have hNP : N ≤ P := radical_le_neutral_plane P hPdim (Q i) (hHerm i) hi (hP i)
    have hNinv : ∀ v ∈ N, (U : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ v ∈ N := by
      intro v hv
      change Q i *ᵥ ((U : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ v) = 0
      rw [Matrix.mulVec_mulVec, hcomm i, ← Matrix.mulVec_mulVec,
        show Q i *ᵥ v = 0 from hv, Matrix.mulVec_zero]
    obtain ⟨w, v, hv, hvne, heig, hw⟩ := eigenphase_of_invariant_submodule U N hNdim hNinv
    exact ⟨w, v, hvne, heig, hw, fun j => hP j v (hNP hv) v (hNP hv)⟩

private theorem last_coefficient_eq_zero
    (X : Fin 3 → Matrix (Fin 3) (Fin 5) ℂ)
    (hinj : Function.Injective (stack X).mulVecLin)
    (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : X 1 = U * X 0)
    (T : Matrix (Fin 3) (Fin 3) ℂ) (hPhi : compression X T = 0) : T 2 2 = 0 := by
  classical
  let K := LinearMap.ker (X 0).mulVecLin
  have hdim : 0 < finrank ℂ K := by
    have hs := (X 0).mulVecLin.finrank_range_add_finrank_ker
    have hu := (X 0).rank_le_card_height
    change (X 0).rank + finrank ℂ K = _ at hs
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hs hu
    omega
  obtain ⟨x, hxne⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hdim
  have hx0 : X 0 *ᵥ x.val = 0 := x.property
  have hx1 : X 1 *ᵥ x.val = 0 := by
    rw [hU, ← Matrix.mulVec_mulVec, hx0, Matrix.mulVec_zero]
  have hx2 : X 2 *ᵥ x.val ≠ 0 := by
    intro he
    apply hxne
    apply Subtype.ext
    apply stack_injective_on_common_kernel X hinj
    intro r
    fin_cases r <;> assumption
  have he := compression_pairing X T x.val x.val
  rw [hPhi] at he
  simp only [Matrix.zero_mulVec, dotProduct_zero, Fin.sum_univ_three, hx0, hx1,
    star_zero, zero_dotProduct, dotProduct_zero, mul_zero, zero_add, add_zero] at he
  exact (mul_eq_zero.mp he.symm).resolve_right (fun hz => hx2 (dotProduct_star_self_eq_zero.mp hz))

private theorem cross_coefficient_pairing
    (X : Fin 3 → Matrix (Fin 3) (Fin 5) ℂ)
    (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : X 1 = U * X 0)
    (T : Matrix (Fin 3) (Fin 3) ℂ) (hPhi : compression X T = 0) (h22 : T 2 2 = 0)
    (x y : Fin 5 → ℂ) (hx : X 0 *ᵥ x = 0) :
    star (X 2 *ᵥ x) ⬝ᵥ (T 2 0 • (X 0 *ᵥ y) + T 2 1 • (X 1 *ᵥ y)) = 0 := by
  have hx1 : X 1 *ᵥ x = 0 := by
    rw [hU, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
  have he := compression_pairing X T x y
  rw [hPhi] at he
  simp only [Matrix.zero_mulVec, dotProduct_zero, Fin.sum_univ_three, hx, hx1,
    h22, star_zero, zero_dotProduct, zero_mul, mul_zero, zero_add, add_zero] at he
  simpa only [dotProduct_add, dotProduct_smul, smul_eq_mul] using he.symm

private def coefficientOperator (U T : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  (T 0 0 + T 1 1) • 1 + T 0 1 • U + T 1 0 • Uᴴ

private theorem coefficientOperator_isHermitian
    (U T : Matrix (Fin 3) (Fin 3) ℂ) (hT : T.IsHermitian) :
    (coefficientOperator U T).IsHermitian := by
  have h00 : star (T 0 0) = T 0 0 := congrFun (congrFun hT 0) 0
  have h11 : star (T 1 1) = T 1 1 := congrFun (congrFun hT 1) 1
  have h01 : star (T 1 0) = T 0 1 := congrFun (congrFun hT 0) 1
  have h10 : star (T 0 1) = T 1 0 := congrFun (congrFun hT 1) 0
  change (coefficientOperator U T)ᴴ = coefficientOperator U T
  simp only [coefficientOperator, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, Matrix.conjTranspose_conjTranspose, star_add,
    h00, h11, h01, h10]
  abel

private theorem coefficientOperator_commutes
    (U : Matrix.unitaryGroup (Fin 3) ℂ) (T : Matrix (Fin 3) (Fin 3) ℂ) :
    coefficientOperator U T * (U : Matrix (Fin 3) (Fin 3) ℂ) =
      (U : Matrix (Fin 3) (Fin 3) ℂ) * coefficientOperator U T := by
  have hleft : (U : Matrix (Fin 3) (Fin 3) ℂ)ᴴ * (U : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self U
  have hright : (U : Matrix (Fin 3) (Fin 3) ℂ) * (U : Matrix (Fin 3) (Fin 3) ℂ)ᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using U.2.2
  simp only [coefficientOperator, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hleft, hright]

private theorem coefficientOperator_compression
    (X : Fin 3 → Matrix (Fin 3) (Fin 5) ℂ)
    (U : Matrix.unitaryGroup (Fin 3) ℂ) (hU : X 1 = (U : Matrix (Fin 3) (Fin 3) ℂ) * X 0)
    (T : Matrix (Fin 3) (Fin 3) ℂ)
    (h02 : T 0 2 = 0) (h12 : T 1 2 = 0) (h20 : T 2 0 = 0)
    (h21 : T 2 1 = 0) (h22 : T 2 2 = 0) :
    (X 0)ᴴ * coefficientOperator U T * X 0 = compression X T := by
  have hleft : (U : Matrix (Fin 3) (Fin 3) ℂ)ᴴ * (U : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self U
  rw [compression_eq_sum]
  simp only [Fin.sum_univ_three, h02, h12, h20, h21, h22, zero_smul,
    add_zero, coefficientOperator, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU,
    Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (U : Matrix (Fin 3) (Fin 3) ℂ)ᴴ
    (U : Matrix (Fin 3) (Fin 3) ℂ), hleft, Matrix.one_mul]
  module

private theorem adjoint_eigenvector
    (U : Matrix.unitaryGroup (Fin 3) ℂ) (w : ℂ) (v : Fin 3 → ℂ)
    (heig : (U : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ v = w • v) (hw : star w * w = 1) :
    (U : Matrix (Fin 3) (Fin 3) ℂ)ᴴ *ᵥ v = star w • v := by
  have hleft : (U : Matrix (Fin 3) (Fin 3) ℂ)ᴴ * (U : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self U
  have he := congrArg (fun z => (U : Matrix (Fin 3) (Fin 3) ℂ)ᴴ *ᵥ z) heig
  rw [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec, Matrix.mulVec_smul] at he
  calc
    _ = (star w * w) • ((U : Matrix (Fin 3) (Fin 3) ℂ)ᴴ *ᵥ v) := by rw [hw, one_smul]
    _ = star w • v := by rw [mul_smul, ← he]

private theorem coefficient_phase_of_eigenvector
    (U : Matrix.unitaryGroup (Fin 3) ℂ)
    (T : Matrix (Fin 3) (Fin 3) ℂ) (w : ℂ) (v : Fin 3 → ℂ) (hv : v ≠ 0)
    (heig : (U : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ v = w • v) (hw : star w * w = 1)
    (hquad : star v ⬝ᵥ (coefficientOperator U T *ᵥ v) = 0) :
    star (phaseVector w) ⬝ᵥ (T *ᵥ phaseVector w) = 0 := by
  have hadj := adjoint_eigenvector U w v heig hw
  simp only [coefficientOperator, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, heig, hadj, smul_smul, dotProduct_add, dotProduct_smul,
    smul_eq_mul] at hquad
  have hs : T 0 0 + T 1 1 + T 0 1 * w + T 1 0 * star w = 0 := by
    apply (mul_eq_zero.mp (show (T 0 0 + T 1 1 + T 0 1 * w + T 1 0 * star w) *
        (star v ⬝ᵥ v) = 0 by linear_combination hquad)).resolve_right
    exact fun he => hv (dotProduct_star_self_eq_zero.mp he)
  rw [phaseVector_quad]
  linear_combination hs + T 1 1 * hw

private def residualSpace (X : Fin 3 → Matrix (Fin 3) (Fin 5) ℂ) : Submodule ℂ (Fin 3 → ℂ) :=
  LinearMap.range ((X 2).mulVecLin.domRestrict (LinearMap.ker (X 0).mulVecLin))

private theorem residualSpace_finrank
    (X : Fin 3 → Matrix (Fin 3) (Fin 5) ℂ)
    (hinj : Function.Injective (stack X).mulVecLin)
    (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : X 1 = U * X 0) :
    finrank ℂ (residualSpace X) + (X 0).rank = 5 := by
  have he := LinearMap.finrank_range_of_inj (kernel_restriction_injective X hinj U hU)
  have hs := (X 0).mulVecLin.finrank_range_add_finrank_ker
  change finrank ℂ (residualSpace X) = _ at he
  change (X 0).rank + finrank ℂ (LinearMap.ker (X 0).mulVecLin) = _ at hs
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hs
  omega

private theorem cross_zero_of_rank_two
    (X : Fin 3 → Matrix (Fin 3) (Fin 5) ℂ) (hX : LinearIndependent ℂ X)
    (hinj : Function.Injective (stack X).mulVecLin)
    (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : X 1 = U * X 0) (hrank : (X 0).rank = 2)
    (T : Matrix (Fin 3) (Fin 3) ℂ) (hPhi : compression X T = 0) :
    T 2 0 = 0 ∧ T 2 1 = 0 := by
  classical
  have h22 := last_coefficient_eq_zero X hinj U hU T hPhi
  have hRdim := residualSpace_finrank X hinj U hU
  rw [hrank] at hRdim
  have hRtop : residualSpace X = ⊤ := Submodule.eq_top_of_finrank_eq (by
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]; omega)
  have hz (y : Fin 5 → ℂ) : T 2 0 • (X 0 *ᵥ y) + T 2 1 • (X 1 *ᵥ y) = 0 := by
    let z := T 2 0 • (X 0 *ᵥ y) + T 2 1 • (X 1 *ᵥ y)
    have hzR : z ∈ residualSpace X := by rw [hRtop]; trivial
    obtain ⟨x, hx⟩ := hzR
    have he := cross_coefficient_pairing X U hU T hPhi h22 x.val y x.property
    change X 2 *ᵥ x.val = z at hx
    rw [hx] at he
    exact dotProduct_star_self_eq_zero.mp he
  have hmat : T 2 0 • X 0 + T 2 1 • X 1 = 0 := by
    ext i j
    have he := congrFun (hz (Pi.single j 1)) i
    simpa [Matrix.mulVec_single, Matrix.add_apply, Matrix.smul_apply] using he
  let z : Fin 3 → ℂ := ![T 2 0, T 2 1, 0]
  have hsum : ∑ r, z r • X r = 0 := by
    simpa [z, Fin.sum_univ_three] using hmat
  exact ⟨Fintype.linearIndependent_iff.mp hX z hsum 0,
    Fintype.linearIndependent_iff.mp hX z hsum 1⟩

private theorem residual_pairing_of_surjective
    (X : Fin 3 → Matrix (Fin 3) (Fin 5) ℂ)
    (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : X 1 = U * X 0)
    (hsurj : Function.Surjective (X 0).mulVecLin)
    (T : Matrix (Fin 3) (Fin 3) ℂ) (hPhi : compression X T = 0) (h22 : T 2 2 = 0)
    (r : Fin 3 → ℂ) (hr : r ∈ residualSpace X) (v : Fin 3 → ℂ) :
    star r ⬝ᵥ (T 2 0 • v + T 2 1 • (U *ᵥ v)) = 0 := by
  obtain ⟨x, hx⟩ := hr
  obtain ⟨y, hy⟩ := hsurj v
  change X 0 *ᵥ y = v at hy
  change X 2 *ᵥ x.val = r at hx
  have he := cross_coefficient_pairing X U hU T hPhi h22 x.val y x.property
  rw [hx, hU, ← Matrix.mulVec_mulVec, hy] at he
  exact he

private theorem invariant_adjoint_of_pairing
    (R : Submodule ℂ (Fin 3 → ℂ)) (U : Matrix (Fin 3) (Fin 3) ℂ)
    (p q : ℂ) (hq : q ≠ 0)
    (hpair : ∀ r ∈ R, ∀ v, star r ⬝ᵥ (p • v + q • (U *ᵥ v)) = 0) :
    ∀ r ∈ R, Uᴴ *ᵥ r ∈ R := by
  intro r hr
  let z := star p • r + star q • (Uᴴ *ᵥ r)
  have he (v : Fin 3 → ℂ) : star z ⬝ᵥ v = 0 := by
    simp only [z, star_add, star_smul, star_star, add_dotProduct, smul_dotProduct,
      smul_eq_mul, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.conjTranspose_conjTranspose]
    simpa only [dotProduct_add, dotProduct_smul, smul_eq_mul] using hpair r hr v
  have hz : z = 0 := dotProduct_star_self_eq_zero.mp (he z)
  have hmem : star q • (Uᴴ *ᵥ r) ∈ R := by
    have heq : star q • (Uᴴ *ᵥ r) = -(star p • r) :=
      eq_neg_of_add_eq_zero_left (by simpa only [z, add_comm] using hz)
    rw [heq]
    exact R.neg_mem (R.smul_mem (star p) hr)
  have hi := R.smul_mem (star q)⁻¹ hmem
  simpa only [smul_smul, inv_mul_cancel₀ (star_ne_zero.mpr hq), one_smul] using hi

private theorem phase_quad_of_image
    (X : Fin 3 → Matrix (Fin 3) (Fin 5) ℂ)
    (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : T.IsHermitian)
    (hPhi : compression X T = 0) (h22 : T 2 2 = 0)
    (w : ℂ) (hcross : T 2 0 + w * T 2 1 = 0)
    (x : Fin 5 → ℂ) (v : Fin 3 → ℂ) (hv : v ≠ 0)
    (hx0 : X 0 *ᵥ x = v) (hx1 : X 1 *ᵥ x = w • v) :
    star (phaseVector w) ⬝ᵥ (T *ᵥ phaseVector w) = 0 := by
  have hreverse : T 0 2 + star w * T 1 2 = 0 := by
    have he := congrArg star hcross
    have h02 : star (T 2 0) = T 0 2 := congrFun (congrFun hT 0) 2
    have h12 : star (T 2 1) = T 1 2 := congrFun (congrFun hT 1) 2
    simpa only [star_add, star_mul, h02, h12, star_zero, mul_comm] using he
  have he := compression_pairing X T x x
  rw [hPhi] at he
  simp only [Matrix.zero_mulVec, dotProduct_zero, Fin.sum_univ_three,
    hx0, hx1, h22, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    zero_mul, add_zero] at he
  apply (mul_eq_zero.mp (show (star (phaseVector w) ⬝ᵥ (T *ᵥ phaseVector w)) *
      (star v ⬝ᵥ v) = 0 by
    rw [phaseVector_quad]
    linear_combination -he - (star v ⬝ᵥ (X 2 *ᵥ x)) * hreverse -
      (star (X 2 *ᵥ x) ⬝ᵥ v) * hcross)).resolve_right
  exact fun hn => hv (dotProduct_star_self_eq_zero.mp hn)

private theorem normalized_common_plane
    (X : Fin 3 → Matrix (Fin 3) (Fin 5) ℂ) (hX : LinearIndependent ℂ X)
    (hinj : Function.Injective (stack X).mulVecLin) (hSig : compression X signature = 0) :
    ∃ L : Submodule ℂ (Fin 3 → ℂ), finrank ℂ L = 2 ∧
      ∀ T : Matrix (Fin 3) (Fin 3) ℂ, T.IsHermitian → compression X T = 0 →
        ∀ u ∈ L, ∀ v ∈ L, star u ⬝ᵥ (T *ᵥ v) = 0 := by
  classical
  obtain ⟨U, hU⟩ := GramUnitaryExtension.exists_unitary_mul_eq_of_conjTranspose_mul_eq
    (X 1) (X 0) (gram_eq_of_signature X hSig)
  let K : Set (Matrix (Fin 3) (Fin 3) ℂ) := {T | T.IsHermitian ∧ compression X T = 0}
  have h22 (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : T ∈ K) : T 2 2 = 0 :=
    last_coefficient_eq_zero X hinj U hU T hT.2
  have hrank := normalized_rank_cases X hinj U hU
  have hAr : 2 ≤ (X 0).rank := by omega
  suffices hplane : ∃ L : Submodule ℂ (Fin 3 → ℂ), finrank ℂ L = 2 ∧
      ∀ T ∈ K, ∀ u ∈ L, ∀ v ∈ L, star u ⬝ᵥ (T *ᵥ v) = 0 by
    obtain ⟨L, hd, hL⟩ := hplane
    exact ⟨L, hd, fun T hT hPhi => hL T ⟨hT, hPhi⟩⟩
  by_cases hcross : ∀ T ∈ K, T 2 0 = 0 ∧ T 2 1 = 0
  · let Q : K → Matrix (Fin 3) (Fin 3) ℂ := fun T => coefficientOperator U T.val
    have hcomp (T : K) : (X 0)ᴴ * Q T * X 0 = 0 := by
      have h20 := (hcross T.val T.property).1
      have h21 := (hcross T.val T.property).2
      have hHerm := T.property.1
      have h02 : T.val 0 2 = 0 := by
        have he := congrFun (congrFun hHerm 0) 2
        simpa only [Matrix.conjTranspose_apply, h20, star_zero] using he.symm
      have h12 : T.val 1 2 = 0 := by
        have he := congrFun (congrFun hHerm 1) 2
        simpa only [Matrix.conjTranspose_apply, h21, star_zero] using he.symm
      exact (coefficientOperator_compression X U hU T.val h02 h12 h20 h21
        (h22 _ T.property)).trans T.property.2
    obtain ⟨w, v, hv, heig, hw, hQ⟩ := common_unitary_phase (X 0) hAr U Q
      (fun T => coefficientOperator_isHermitian U T.val T.property.1)
      (fun T => coefficientOperator_commutes U T.val) hcomp
    apply phase_plane K w
    intro T hT
    refine ⟨hT.1, h22 T hT, ?_, ?_⟩
    · rw [(hcross T hT).1, (hcross T hT).2]; simp
    · exact coefficient_phase_of_eigenvector U T w v hv heig hw (hQ ⟨T, hT⟩)
  · have hr3 : (X 0).rank = 3 := by
      rcases hrank with hr2 | hr3
      · exact False.elim (hcross (fun T hT => cross_zero_of_rank_two X hX hinj U hU hr2 T hT.2))
      · exact hr3
    have hsurj : Function.Surjective (X 0).mulVecLin := by
      apply LinearMap.range_eq_top.mp
      apply Submodule.eq_top_of_finrank_eq
      change (X 0).rank = finrank ℂ (Fin 3 → ℂ)
      simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hr3
    have hRdim : finrank ℂ (residualSpace X) = 2 := by
      have he := residualSpace_finrank X hinj U hU
      omega
    have hRpos : 0 < finrank ℂ (residualSpace X) := by omega
    obtain ⟨T, hTK, hbad⟩ : ∃ T ∈ K, ¬ (T 2 0 = 0 ∧ T 2 1 = 0) := by
      simpa only [not_forall, exists_prop] using hcross
    have h21 : T 2 1 ≠ 0 := by
      intro hq
      obtain ⟨r, hrne⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hRpos
      have hrval : r.val ≠ 0 := by intro he; exact hrne (Subtype.ext he)
      have he := residual_pairing_of_surjective X U hU hsurj T hTK.2 (h22 T hTK)
        r.val r.property r.val
      simp only [hq, zero_smul, add_zero, dotProduct_smul, smul_eq_mul] at he
      have hp : T 2 0 = 0 := (mul_eq_zero.mp he).resolve_right
        (fun hn => hrval (dotProduct_star_self_eq_zero.mp hn))
      exact hbad ⟨hp, hq⟩
    have hinv : ∀ r ∈ residualSpace X, (U : Matrix (Fin 3) (Fin 3) ℂ)ᴴ *ᵥ r ∈ residualSpace X :=
      invariant_adjoint_of_pairing (residualSpace X) U (T 2 0) (T 2 1) h21
        (residual_pairing_of_surjective X U hU hsurj T hTK.2 (h22 T hTK))
    obtain ⟨nu, v, hvR, hv, heig, hnu⟩ := eigenphase_of_invariant_submodule (star U)
      (residualSpace X) hRpos (by
        intro r hr
        simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using hinv r hr)
    let w := star nu
    have heigU : (U : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ v = w • v := by
      simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose] using adjoint_eigenvector (star U) nu v heig hnu
    have hcrossW (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : T ∈ K) : T 2 0 + w * T 2 1 = 0 := by
      have he := residual_pairing_of_surjective X U hU hsurj T hT.2 (h22 T hT) v hvR v
      rw [heigU] at he
      simp only [smul_smul, dotProduct_add, dotProduct_smul, smul_eq_mul] at he
      apply (mul_eq_zero.mp (show (T 2 0 + w * T 2 1) * (star v ⬝ᵥ v) = 0 by
        linear_combination he)).resolve_right
      exact fun hn => hv (dotProduct_star_self_eq_zero.mp hn)
    obtain ⟨x, hx⟩ := hsurj v
    have hx1 : X 1 *ᵥ x = w • v := by
      rw [hU, ← Matrix.mulVec_mulVec, show X 0 *ᵥ x = v from hx, heigU]
    apply phase_plane K w
    intro T hT
    exact ⟨hT.1, h22 T hT, hcrossW T hT,
      phase_quad_of_image X T hT.1 hT.2 (h22 T hT) w (hcrossW T hT) x v hv hx hx1⟩

theorem common_plane
    (X : Fin 3 → Matrix (Fin 3) (Fin 5) ℂ) (hX : LinearIndependent ℂ X)
    (hinj : Function.Injective (stack X).mulVecLin) :
    ∃ L : Submodule ℂ (Fin 3 → ℂ), finrank ℂ L = 2 ∧
      ∀ T : Matrix (Fin 3) (Fin 3) ℂ, T.IsHermitian →
        (stack X)ᴴ * Matrix.kronecker T (1 : Matrix (Fin 3) (Fin 3) ℂ) * stack X = 0 →
        ∀ u ∈ L, ∀ v ∈ L, star u ⬝ᵥ (T *ᵥ v) = 0 := by
  classical
  change ∃ L : Submodule ℂ (Fin 3 → ℂ), finrank ℂ L = 2 ∧
    ∀ T : Matrix (Fin 3) (Fin 3) ℂ, T.IsHermitian → compression X T = 0 →
      ∀ u ∈ L, ∀ v ∈ L, star u ⬝ᵥ (T *ᵥ v) = 0
  by_cases hzero : ∀ T : Matrix (Fin 3) (Fin 3) ℂ,
      T.IsHermitian → compression X T = 0 → T = 0
  · exact zero_kernel_plane X hzero
  · obtain ⟨T, hT, hPhi, hne⟩ : ∃ T : Matrix (Fin 3) (Fin 3) ℂ,
        T.IsHermitian ∧ compression X T = 0 ∧ T ≠ 0 := by
      simpa only [not_forall, exists_prop] using hzero
    obtain ⟨e, hp, hn, hz⟩ := spectral_signs X hX hinj T hT hPhi hne
    obtain ⟨B, hB, hD⟩ := signature_congruence T hT e hp hn hz
    let A := B⁻¹
    have hA : IsUnit A := Matrix.isUnit_nonsing_inv_iff.mpr hB
    have hBA : B * A = 1 := Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det B).mp hB)
    have hrecover (Q : Matrix (Fin 3) (Fin 3) ℂ) : Aᴴ * (Bᴴ * Q * B) * A = Q := by
      calc
        _ = (B * A)ᴴ * Q * (B * A) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = Q := by rw [hBA]; simp
    let Y := mix A X
    have hY : LinearIndependent ℂ Y := linearIndependent_mix A hA X hX
    have hYinj : Function.Injective (stack Y).mulVecLin := injective_stack_mix A hA X hinj
    have hYSig : compression Y signature = 0 := by
      rw [show Y = mix A X from rfl, compression_mix, ← hD, hrecover, hPhi]
    obtain ⟨L, hdim, hL⟩ := normalized_common_plane Y hY hYinj hYSig
    let K : Set (Matrix (Fin 3) (Fin 3) ℂ) := {Q | Q.IsHermitian ∧ compression X Q = 0}
    have hneutral : ∀ Q ∈ K, ∀ u ∈ L, ∀ v ∈ L,
        star u ⬝ᵥ ((Bᴴ * Q * B) *ᵥ v) = 0 := by
      intro Q hQ
      apply hL (Bᴴ * Q * B) (Matrix.isHermitian_conjTranspose_mul_mul B hQ.1)
      rw [show Y = mix A X from rfl, compression_mix, hrecover]
      exact hQ.2
    obtain ⟨L', hdim', hL'⟩ := common_plane_transport K B hB L hdim hneutral
    exact ⟨L', hdim', fun Q hQ hPhi => hL' Q ⟨hQ, hPhi⟩⟩

end D5.S3.Quantum.Algebra.CommonCoefficientPlane
