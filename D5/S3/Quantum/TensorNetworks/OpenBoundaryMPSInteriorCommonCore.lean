/- GID: D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Kronecker]
   utility: none
   digest: Raw interior observations force a common core for arbitrary competitors. -/

import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityRecovery
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Raw interior windows retain their actual left and right complements. The
common-core conclusion is conditional on target spanning and positive definite
environments. It asserts neither phase recovery nor genericity. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore

open scoped BigOperators Matrix ComplexOrder Kronecker
open Matrix
open PeriodicMPSParentIntersection
open OpenBoundaryMPSMarginalBirationality (mpsState)
open OpenBoundaryMPSDensityRecovery

noncomputable section

/-- Columns retain both actual exterior words, in their original positions. -/
def interiorColumns (p k q : ℕ) (ψ : Word ((p + k) + q) → ℂ) :
    Matrix (Word k) (Word p × Word q) ℂ :=
  fun u ab => ψ (Fin.append (Fin.append ab.1 u) ab.2)

/-- Unnormalized Hermitian interior observation. -/
def rawInterior (p k q : ℕ) (ψ : Word ((p + k) + q) → ℂ) :
    Matrix (Word k) (Word k) ℂ :=
  interiorColumns p k q ψ * (interiorColumns p k q ψ)ᴴ

/-- Trace-pairing coordinates: the matrix entry is deliberately transposed. -/
def feature (A : Fin 2 → Bond) (k : ℕ) : Matrix (Word k) (Fin 2 × Fin 2) ℂ :=
  fun u ij => wordMatrix A u ij.2 ij.1

/-- Actual context coefficients, with right exterior before the left exterior. -/
def context (A : Fin 2 → Bond) (l r : Fin 2 → ℂ) (p q : ℕ) :
    Matrix (Fin 2 × Fin 2) (Word p × Word q) ℂ :=
  fun ij ab => (wordMatrix A ab.2 *ᵥ r) ij.1 * (l ᵥ* wordMatrix A ab.1) ij.2

/-- Dual transfer for bilinear left boundary coordinates. -/
def dualTransfer (A : Fin 2 → Bond) (X : Bond) : Bond :=
  ∑ i : Fin 2, (A i)ᴴ * X * A i

private lemma feature_gamma (A : Fin 2 → Bond) (k : ℕ) (X : Bond) :
    feature A k *ᵥ (fun ij => X ij.1 ij.2) = gamma A k X := by
  funext w
  simp only [feature, mulVec, dotProduct, Fintype.sum_prod_type, gamma,
    trace, diag, mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

private lemma state_gamma (A : Fin 2 → Bond) (l r : Fin 2 → ℂ) (n : ℕ) :
    mpsState n (A 0) (A 1) l r = gamma A n (vecMulVec r l) := by
  funext w
  rw [state_formula, gamma, vecMulVec_mul, trace_vecMulVec, dotProduct_mulVec,
    dotProduct_comm]

private lemma interior_columns_factor (A : Fin 2 → Bond) (l r : Fin 2 → ℂ)
    (p k q : ℕ) :
    interiorColumns p k q (mpsState ((p + k) + q) (A 0) (A 1) l r) =
      feature A k * context A l r p q := by
  ext u ab
  rw [interiorColumns, state_formula, wordMatrix_append, wordMatrix_append]
  simp only [mul_apply, Fintype.sum_prod_type, feature, context]
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
  simp only [mulVec, vecMul, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  ring

private lemma left_boundary_gram (A : Fin 2 → Bond) (l : Fin 2 → ℂ) (p : ℕ) :
    (prefixMap A l p)ᴴ * prefixMap A l p =
      (dualTransfer A)^[p] (vecMulVec (star l) l) := by
  have hs (k : ℕ) : (prefixMap A l k)ᴴ * prefixMap A l k =
      ∑ w : Word k, vecMulVec (star (l ᵥ* wordMatrix A w)) (l ᵥ* wordMatrix A w) := by
    ext i j
    simp only [mul_apply, conjTranspose_apply, prefixMap, Matrix.sum_apply,
      vecMulVec_apply, Pi.star_apply]
  rw [hs]
  induction p with
  | zero => simp [wordMatrix, Function.iterate_zero]
  | succ p ih =>
    rw [Function.iterate_succ_apply', ← ih]
    rw [← (Fin.snocEquiv (fun _ : Fin (p + 1) => Fin 2)).sum_comp]
    rw [Fintype.sum_prod_type]
    simp only [Fin.snocEquiv, Equiv.coe_fn_mk, wordMatrix_snoc, ← vecMul_vecMul]
    simp only [dualTransfer, Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro w _
    simp only [mul_vecMulVec, vecMulVec_mul, star_vecMul]

private lemma context_gram (A : Fin 2 → Bond) (l r : Fin 2 → ℂ) (p q : ℕ) :
    context A l r p q * (context A l r p q)ᴴ =
      (transfer A)^[q] (vecMulVec r (star r)) ⊗ₖ
        ((dualTransfer A)^[p] (vecMulVec (star l) l))ᵀ := by
  rw [← tail_gram, ← left_boundary_gram]
  ext ij kt
  rcases ij with ⟨i, j⟩
  rcases kt with ⟨k, t⟩
  simp only [mul_apply, conjTranspose_apply, context, kronecker_apply,
    transpose_apply, tailMap, prefixMap, Fintype.sum_prod_type, star_mul,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

private lemma interior_density_dictionary (A : Fin 2 → Bond) (l r : Fin 2 → ℂ)
    (p k q : ℕ) :
    rawInterior p k q (mpsState ((p + k) + q) (A 0) (A 1) l r) =
      feature A k * ((transfer A)^[q] (vecMulVec r (star r)) ⊗ₖ
        ((dualTransfer A)^[p] (vecMulVec (star l) l))ᵀ) * (feature A k)ᴴ := by
  rw [rawInterior, interior_columns_factor, conjTranspose_mul]
  simp only [← context_gram, Matrix.mul_assoc]

private lemma feature_injective (A : Fin 2 → Bond) (hA : TwoSiteSpanning A) :
    Function.Injective (feature A 3).mulVec := by
  intro x y h
  have he : gamma A 3 (fun i j => x (i, j)) =
      gamma A 3 (fun i j => y (i, j)) := by
    exact (feature_gamma A 3 (fun i j => x (i, j))).symm.trans
      (h.trans (feature_gamma A 3 (fun i j => y (i, j))))
  have hm := trace_separates A hA 1 _ _ (congrFun he)
  funext ij
  exact congrFun (congrFun hm ij.1) ij.2

private lemma context_surjective (A : Fin 2 → Bond) (l r : Fin 2 → ℂ)
    (p q : ℕ)
    (hP : ((dualTransfer A)^[p] (vecMulVec (star l) l)).PosDef)
    (hH : ((transfer A)^[q] (vecMulVec r (star r))).PosDef) :
    Function.Surjective (context A l r p q).mulVec := by
  have hdetP : ((dualTransfer A)^[p] (vecMulVec (star l) l)).det ≠ 0 :=
    ((isUnit_iff_isUnit_det _).mp hP.isUnit).ne_zero
  have hdetH : ((transfer A)^[q] (vecMulVec r (star r))).det ≠ 0 :=
    ((isUnit_iff_isUnit_det _).mp hH.isUnit).ne_zero
  apply mulVec_surjective_iff_rank_eq_card.mpr
  rw [← rank_self_mul_conjTranspose, context_gram]
  apply rank_of_det_ne_zero
  rw [det_kronecker, det_transpose]
  exact mul_ne_zero (pow_ne_zero _ hdetH) (pow_ne_zero _ hdetP)

private lemma context_range (A : Fin 2 → Bond) (l r : Fin 2 → ℂ) (p k q : ℕ)
    (hK : Function.Surjective (context A l r p q).mulVec) :
    LinearMap.range (interiorColumns p k q
      (mpsState ((p + k) + q) (A 0) (A 1) l r)).mulVecLin =
      LinearMap.range (feature A k).mulVecLin := by
  rw [← gram_range]
  change LinearMap.range (rawInterior p k q
    (mpsState ((p + k) + q) (A 0) (A 1) l r)).mulVecLin = _
  rw [interior_density_dictionary, ← context_gram]
  have hg : feature A k * (context A l r p q * (context A l r p q)ᴴ) *
      (feature A k)ᴴ =
      (feature A k * context A l r p q) * (feature A k * context A l r p q)ᴴ := by
    rw [conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [hg, gram_range, mulVecLin_mul, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr hK, Submodule.map_top]

private lemma observed_all_coefficients (A B : Fin 2 → Bond)
    (l r lprime rprime : Fin 2 → ℂ) (p q : ℕ) (hA : TwoSiteSpanning A)
    (hP : ((dualTransfer A)^[p] (vecMulVec (star l) l)).PosDef)
    (hH : ((transfer A)^[q] (vecMulVec r (star r))).PosDef)
    (hraw : rawInterior p 3 q (mpsState ((p + 3) + q) (B 0) (B 1) lprime rprime) =
      rawInterior p 3 q (mpsState ((p + 3) + q) (A 0) (A 1) l r)) :
    ∀ X : Bond, ∃ Y : Bond, gamma B 3 X = gamma A 3 Y := by
  let CA := interiorColumns p 3 q (mpsState ((p + 3) + q) (A 0) (A 1) l r)
  let CB := interiorColumns p 3 q (mpsState ((p + 3) + q) (B 0) (B 1) lprime rprime)
  have hCA : LinearMap.range CA.mulVecLin = LinearMap.range (feature A 3).mulVecLin :=
    context_range A l r p 3 q (context_surjective A l r p q hP hH)
  have he : LinearMap.range CB.mulVecLin = LinearMap.range CA.mulVecLin := by
    rw [← gram_range CB, ← gram_range CA]
    exact congrArg (fun M => LinearMap.range M.mulVecLin) hraw
  have hrA : Module.finrank ℂ (LinearMap.range CA.mulVecLin) = 4 := by
    rw [hCA, LinearMap.finrank_range_of_inj (feature_injective A hA)]
    norm_num
  have hle : LinearMap.range CB.mulVecLin ≤ LinearMap.range (feature B 3).mulVecLin := by
    dsimp [CB]
    rw [interior_columns_factor, mulVecLin_mul, LinearMap.range_comp]
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨v, rfl⟩
  have hsat : LinearMap.range CB.mulVecLin = LinearMap.range (feature B 3).mulVecLin :=
    Submodule.eq_of_le_of_finrank_le hle (by
      rw [he, hrA]
      simpa only [Matrix.rank, Fintype.card_prod, Fintype.card_fin,
        Nat.reduceMul] using (feature B 3).rank_le_card_width)
  intro X
  have hx : gamma B 3 X ∈ LinearMap.range CB.mulVecLin := by
    rw [hsat]
    exact ⟨fun ij => X ij.1 ij.2, feature_gamma B 3 X⟩
  rw [he, hCA] at hx
  obtain ⟨y, hy⟩ := hx
  refine ⟨fun i j => y (i, j), ?_⟩
  exact hy.symm.trans (feature_gamma A 3 (fun i j => y (i, j)))

/-- Parent propagation for every virtual coefficient of an arbitrary competitor.
The induction generalizes X; no cyclicity of the physical state is assumed. -/
theorem all_coefficient_parent_induction (A B : Fin 2 → Bond) (hA : TwoSiteSpanning A)
    (hthree : ∀ X : Bond, ∃ Y : Bond, gamma B 3 X = gamma A 3 Y)
    (m : ℕ) (X : Bond) :
    ∃ Y : Bond, gamma B (m + 3) X = gamma A (m + 3) Y := by
  classical
  induction m generalizing X with
  | zero => exact hthree X
  | succ m ih =>
    apply (parent_intersection A hA m (gamma B (m + 4) X)).mp
    constructor
    · choose Y hY using fun j => ih (B j * X)
      refine ⟨Y, ?_⟩
      intro w j
      rw [← congrFun (hY j) w]
      simpa only [gamma, wordMatrix_snoc, ← Matrix.mul_assoc] using
        Matrix.trace_mul_cycle X (wordMatrix B w) (B j)
    · choose Y hY using fun i => ih (X * B i)
      refine ⟨Y, ?_⟩
      intro i w
      rw [← congrFun (hY i) w]
      simp only [gamma, wordMatrix_cons, Matrix.mul_assoc]

/-- An actual raw interior three-site observation forces every actual bond-two
competitor to have the target core with one unrestricted virtual coefficient.
Only the target has spanning and positive definite environment hypotheses. -/
theorem interior_common_core (A B : Fin 2 → Bond)
    (l r lprime rprime : Fin 2 → ℂ) (p q : ℕ) (_hp : 1 ≤ p) (_hq : 1 ≤ q)
    (hA : TwoSiteSpanning A)
    (hP : ((dualTransfer A)^[p] (vecMulVec (star l) l)).PosDef)
    (hH : ((transfer A)^[q] (vecMulVec r (star r))).PosDef)
    (hraw : rawInterior p 3 q (mpsState ((p + 3) + q) (B 0) (B 1) lprime rprime) =
      rawInterior p 3 q (mpsState ((p + 3) + q) (A 0) (A 1) l r)) :
    ∃ X : Bond, mpsState ((p + 3) + q) (B 0) (B 1) lprime rprime =
      gamma A ((p + 3) + q) X := by
  have hthree := observed_all_coefficients A B l r lprime rprime p q hA hP hH hraw
  have h := all_coefficient_parent_induction A B hA hthree (p + q) (vecMulVec rprime lprime)
  have hn : p + q + 3 = (p + 3) + q := by omega
  rw [hn] at h
  simpa only [state_gamma] using h

#print axioms all_coefficient_parent_induction
#print axioms interior_common_core

end
end D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore
