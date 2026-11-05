/- GID: D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionDeterminants
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionDeterminants
   mirror-E: none(waiver:source-only-positive-theorem)
   anchors: []
   utility: none
   digest: Exact symbolic determinant identities of the paired tensor operator. -/
import D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionObstructions
import Mathlib.Tactic
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
open Finset Matrix
open scoped Classical Kronecker
namespace D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionDeterminants
open D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionObstructions
open D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionEndpoints

private lemma tensorK_four {R : Type*} [CommRing R] (a b c : R) :
    Matrix.reindex finProdFinEquiv finProdFinEquiv (tensorK a b c) =
      !![(a+1)*(b+1)*(c+1)+a,a*c,a*b,a*b*c;
         a,(a+1)*(b+1),a*b,0;
         a,a*c,(a+1)*(c+1),0;
         a,0,0,a+1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.reindex_apply,finProdFinEquiv,Fin.divNat,Fin.modNat,tensorK,E,F,kroneckerMap_apply] <;> ring

/-- A full symbolic scalar-shift determinant, valid over every commutative ring.
This normalization identity is a helper, with no finite-instance premise. -/
theorem det_tensorK_sub_scalar {R : Type*} [CommRing R] (a b c r : R) :
    (tensorK a b c-r • 1).det =
      (a+1-r)*(((a+1)*(b+1)*(c+1)+a-r)*((a+1)*(b+1)-r)*((a+1)*(c+1)-r)
        -((a+1)*(b+1)*(c+1)+a-r)*a^2*b*c
        -a^2*c*((a+1)*(c+1)-r)-a^2*b*((a+1)*(b+1)-r)+2*a^3*b*c)
        -a^2*b*c*(((a+1)*(b+1)-r)*((a+1)*(c+1)-r)-a^2*b*c) := by
  rw [← Matrix.det_reindex_self (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4)
    (tensorK a b c-r • 1)]
  have he : Matrix.reindex finProdFinEquiv finProdFinEquiv (tensorK a b c-r • 1) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (tensorK a b c)-r • 1 := by
    ext i j
    simp [Matrix.reindex_apply,Matrix.one_apply,finProdFinEquiv.symm.injective.eq_iff]
  rw [he,tensorK_four]
  have hm :
      (!![(a+1)*(b+1)*(c+1)+a,a*c,a*b,a*b*c;
         a,(a+1)*(b+1),a*b,0;
         a,a*c,(a+1)*(c+1),0;
         a,0,0,a+1] : Matrix (Fin 4) (Fin 4) R)-r • 1 =
      !![(a+1)*(b+1)*(c+1)+a-r,a*c,a*b,a*b*c;
         a,(a+1)*(b+1)-r,a*b,0;
         a,a*c,(a+1)*(c+1)-r,0;
         a,0,0,a+1-r] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
  rw [hm,det_succ_row_zero]
  norm_num [Fin.sum_univ_succ,det_fin_three,submatrix_apply,Fin.succAbove]
  ring

/-- The exact H4 endpoint, matching the general integer polynomial. -/
theorem det_two_sub_two {R : Type*} [CommRing R] (b c : R) :
    (tensorK 2 b c-(2 : R) • 1).det = P2 b c := by
  rw [det_tensorK_sub_scalar]
  unfold P2
  ring

/-- The exact H5 endpoint, matching the general integer polynomial. -/
theorem det_three_sub_two {R : Type*} [CommRing R] (b c : R) :
    (tensorK 3 b c-(2 : R) • 1).det = P3 b c := by
  rw [det_tensorK_sub_scalar]
  unfold P3
  ring

/-- The H5 upper-endpoint determinant, in symmetric sum/product coordinates. -/
theorem det_three_sub_three {R : Type*} [CommRing R] (b c : R) :
    (tensorK 3 b c-(3 : R) • 1).det =
      -35*(b*c)^2+8*(b*c)*(b+c)-20*(b+c)^2+149*(b*c)+11*(b+c)+4 := by
  rw [det_tensorK_sub_scalar]
  ring

/-- The determinant used by the infinite congruence-family spectral argument. -/
theorem det_two_add_one {R : Type*} [CommRing R] (b c : R) :
    (tensorK 2 b c+1).det =
      4*(10*(b*c)^2+39*(b*c)*(b+c)+102*(b*c)+24*(b+c)^2+104*(b+c)+96) := by
  have he : tensorK 2 b c+1=tensorK 2 b c-(-1 : R) • 1 := by simp
  rw [he,det_tensorK_sub_scalar]
  ring

/-- The whole positive H5 domain has a strictly negative determinant at three. -/
theorem det_three_sub_three_neg (b c : ℝ) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    (tensorK 3 b c-(3 : ℝ) • 1).det < 0 := by
  rw [det_three_sub_three]
  have hp : 4 ≤ b*c := by nlinarith
  have hs : 4 ≤ b+c := by linarith
  have hsp : b+c ≤ b*c := by nlinarith [mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hc)]
  have hps : 8*(b*c)*(b+c) ≤ 8*(b*c)^2 := by nlinarith
  have hss : -20*(b+c)^2+11*(b+c) ≤ -276 := by nlinarith
  have hq : -27*(b*c)^2+149*(b*c)-272 < 0 := by nlinarith [sq_nonneg (b*c-4)]
  nlinarith


/-- The full H5 tensor domain has a real paired eigenvalue strictly between one
and three. The exact lower bound is shared with H4. -/
theorem three_symmetric_low_eigenpair (b c : ℝ) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    ∃ e : ℝ, 1 < e ∧ e < 3 ∧ ∃ v : Fin 2 × Fin 2 → ℝ,
      v ≠ 0 ∧ symmetricK 3 b c*ᵥ v=e • v := by
  let M := symmetricK 3 b c-(3 : ℝ) • 1
  have hM : M.IsHermitian := (symmetric_hermitian 3 b c).sub (by simp)
  have hdet : M.det < 0 := by
    rw [tensor_symmetric_det_shift 3 b c 3 (by linarith) (by linarith)]
    exact det_three_sub_three_neg b c hb hc
  have hno : ¬M.PosSemidef := fun hp => (not_le_of_gt hdet) hp.det_nonneg
  obtain ⟨e,he,z,hz,hze⟩ := negative_eigenpair_of_not_posSemidef M hM hno
  have hS : symmetricK 3 b c*ᵥ z=(e+3) • z := by
    dsimp [M] at hze
    rw [sub_mulVec,smul_mulVec,one_mulVec] at hze
    ext q
    have hh := congrFun hze q
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at hh ⊢
    linarith
  exact ⟨e+3,symmetric_eigenvalue_gt_one 3 b c (by norm_num)
    (by linarith) (by linarith) _ z hz hS,by linarith,z,hz,hS⟩

end D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionDeterminants
