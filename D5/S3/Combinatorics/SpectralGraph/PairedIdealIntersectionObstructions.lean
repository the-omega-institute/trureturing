/- GID: D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionObstructions
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionObstructions
   mirror-E: none(waiver:source-only-positive-theorem)
   anchors: []
   utility: none
   digest: Paired invariant subspaces and four-prime actual ideal-graph obstructions. -/

import D5.S3.Combinatorics.SpectralGraph.IdealIntersectionObstructions
import D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionEndpoints
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

/-!
The paired support subspace and tensor operator are attributed to
`the-omega-institute/ideal-intersection-laplacian`, public revision
`b93becea662a746badeadba42fdc3d3eb3db9382`, `paper/sections/unit-exponent.tex`.
The endpoint arithmetic follows the completed general mathematical note supplied
2026-11-02. Formal proofs are independently authored.
-/
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped Classical Kronecker
namespace D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionObstructions
open D5.S3.Combinatorics.SpectralGraph.IdealIntersectionSupport
open D5.S3.Combinatorics.SpectralGraph.IdealIntersectionObstructions
open D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionEndpoints

/-- The diagonal factor in the source paired tensor operator. -/
def E {R : Type*} [CommRing R] (k : R) : Matrix (Fin 2) (Fin 2) R :=
  diagonal ![k+1,1]

/-- The weighted disjoint-support factor. -/
def F {R : Type*} [CommRing R] (k : R) : Matrix (Fin 2) (Fin 2) R :=
  !![1,k;1,0]

/-- The source paired operator, with the two tail supports as tensor coordinates. -/
def tensorK {R : Type*} [CommRing R] (a b c : R) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) R :=
  (a+1) • (E b ⊗ₖ E c) + a • (F b ⊗ₖ F c)

/-- Symmetric realization of the weighted two-coordinate factor. -/
def H (k : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1,Real.sqrt k;Real.sqrt k,0]

/-- The real symmetric tensor representative of the paired operator. -/
def symmetricK (a b c : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  (a+1) • (E b ⊗ₖ E c) + a • (H b ⊗ₖ H c)

private lemma E_add_H_posDef (k : ℝ) (hk : 0 ≤ k) : (E k+H k).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [E,H,conjTranspose_apply]
  · intro x hx
    have he : star x ⬝ᵥ ((E k+H k)*ᵥ x) =
        (Real.sqrt k*x 0+x 1)^2+2*(x 0)^2 := by
      simp [dotProduct,mulVec,E,H,Fin.sum_univ_succ]
      ring_nf
      simp [Real.sq_sqrt hk]
    rw [he]
    by_cases hx0 : x 0=0
    · have hx1 : x 1 ≠ 0 := by
        intro h
        apply hx
        ext i
        fin_cases i <;> simp [hx0,h]
      simpa [hx0] using sq_pos_of_ne_zero hx1
    · have hh := sq_pos_of_ne_zero hx0
      nlinarith [sq_nonneg (Real.sqrt k*x 0+x 1)]

private lemma E_sub_H_posSemidef (k : ℝ) (hk : 0 ≤ k) : (E k-H k).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [E,H,conjTranspose_apply]
  · intro x
    have he : star x ⬝ᵥ ((E k-H k)*ᵥ x) = (Real.sqrt k*x 0-x 1)^2 := by
      simp [dotProduct,mulVec,E,H,Fin.sum_univ_succ]
      ring_nf
      simp [Real.sq_sqrt hk]
    rw [he]
    exact sq_nonneg _

private lemma E_posDef (k : ℝ) (hk : 0 ≤ k) : (E k).PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i <;> simp <;> linarith

private lemma E_sub_one_posSemidef (k : ℝ) (hk : 0 ≤ k) : (E k-1).PosSemidef := by
  have he : E k-1=diagonal ![k,0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [E]
  rw [he]
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> simp [hk]

private lemma tensor_EF_posDef (b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (E b ⊗ₖ E c + H b ⊗ₖ H c).PosDef := by
  have hp := (E_add_H_posDef b hb).kronecker (E_add_H_posDef c hc)
  have hm := (E_sub_H_posSemidef b hb).kronecker (E_sub_H_posSemidef c hc)
  have hh := (hp.add_posSemidef hm).smul (show (0 : ℝ)<1/2 by norm_num)
  have he : (1/2 : ℝ) •
      ((E b+H b) ⊗ₖ (E c+H c)+(E b-H b) ⊗ₖ (E c-H c)) =
      E b ⊗ₖ E c + H b ⊗ₖ H c := by
    ext i j
    simp [kroneckerMap_apply]
    ring
  rwa [he] at hh

private lemma tensor_E_sub_one_posSemidef (b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (E b ⊗ₖ E c-1).PosSemidef := by
  have h₁ := (E_sub_one_posSemidef b hb).kronecker (E_posDef c hc).posSemidef
  have h₂ := (Matrix.PosSemidef.one (n := Fin 2) (R := ℝ)).kronecker
    (E_sub_one_posSemidef c hc)
  have he : (E b-1) ⊗ₖ E c+(1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ (E c-1) =
      E b ⊗ₖ E c-1 := by
    ext ⟨i,j⟩ ⟨l,m⟩
    fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases m <;>
      simp [E,kroneckerMap_apply]
    <;> ring
  rw [← he]
  exact h₁.add h₂

/-- The general paired tensor lower bound, before any specialization to two or
three equal exponents. This is a strict quadratic bound on the symmetric
representative of the source's weighted operator. -/
theorem symmetricK_sub_one_posDef (a b c : ℝ) (ha : 0 < a)
    (hb : 0 ≤ b) (hc : 0 ≤ c) : (symmetricK a b c-1).PosDef := by
  have hp := (tensor_EF_posDef b c hb hc).smul ha
  have hn := tensor_E_sub_one_posSemidef b c hb hc
  have he : symmetricK a b c-1 =
      a • (E b ⊗ₖ E c + H b ⊗ₖ H c)+(E b ⊗ₖ E c-1) := by
    ext i j
    simp [symmetricK]
    ring
  rw [he]
  exact hp.add_posSemidef hn


/-- The positive diagonal weights that identify the tensor with its symmetric
representative. -/
def rootWeight (b c : ℝ) (q : Fin 2 × Fin 2) : ℝ :=
  (if q.1 = 0 then 1 else Real.sqrt b)*(if q.2 = 0 then 1 else Real.sqrt c)

private lemma rootWeight_pos (b c : ℝ) (hb : 0 < b) (hc : 0 < c)
    (q : Fin 2 × Fin 2) : 0 < rootWeight b c q := by
  rcases q with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> simp [rootWeight,Real.sqrt_pos.2 hb,Real.sqrt_pos.2 hc]

private lemma weighted_intertwine (a b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    diagonal (rootWeight b c)*tensorK a b c =
      symmetricK a b c*diagonal (rootWeight b c) := by
  ext ⟨i,j⟩ ⟨l,m⟩
  fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases m <;>
    simp [diagonal_mul,mul_diagonal,rootWeight,tensorK,symmetricK,E,F,H,
      kroneckerMap_apply] <;> ring_nf <;> simp [Real.sq_sqrt hb,Real.sq_sqrt hc] <;> ring

/-- Symmetric eigenvectors transport to the original weighted tensor, without
losing nonzero vectors. -/
theorem tensor_eigenpair_of_symmetric (a b c : ℝ) (hb : 0 < b) (hc : 0 < c)
    (e : ℝ) (v : Fin 2 × Fin 2 → ℝ) (hv : v ≠ 0)
    (he : symmetricK a b c *ᵥ v = e • v) :
    ∃ h : Fin 2 × Fin 2 → ℝ, h ≠ 0 ∧ tensorK a b c *ᵥ h = e • h := by
  let D := diagonal (rootWeight b c)
  let h : Fin 2 × Fin 2 → ℝ := fun q => v q/rootWeight b c q
  have hDh : D*ᵥ h = v := by
    ext q
    simp only [D,h,mulVec_diagonal,Pi.mul_apply]
    field_simp [(rootWeight_pos b c hb hc q).ne']
  have hDinj : Function.Injective (D.mulVec) := by
    intro x y hxy
    ext q
    have hh := congrFun hxy q
    simp only [D,mulVec_diagonal,Pi.mul_apply] at hh
    exact mul_left_cancel₀ (rootWeight_pos b c hb hc q).ne' hh
  refine ⟨h,?_,?_⟩
  · intro hh
    apply hv
    rw [← hDh,hh,mulVec_zero]
  · apply hDinj
    rw [mulVec_mulVec,weighted_intertwine a b c hb.le hc.le,← mulVec_mulVec,hDh,
      he,mulVec_smul,hDh]

lemma symmetric_hermitian (a b c : ℝ) : (symmetricK a b c).IsHermitian := by
  ext ⟨i,j⟩ ⟨l,m⟩
  fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases m <;>
    simp [symmetricK,E,H,conjTranspose_apply,kroneckerMap_apply] <;> ring

lemma negative_eigenpair_of_not_posSemidef
    {v : Type*} [Fintype v] [DecidableEq v] (M : Matrix v v ℝ)
    (hM : M.IsHermitian) (hno : ¬M.PosSemidef) :
    ∃ e : ℝ, e < 0 ∧ ∃ z : v → ℝ, z ≠ 0 ∧ M*ᵥ z = e • z := by
  have hh : ¬∀ i, 0 ≤ hM.eigenvalues i := by
    exact fun hall => hno (hM.posSemidef_iff_eigenvalues_nonneg.mpr hall)
  push_neg at hh
  obtain ⟨i,hi⟩ := hh
  exact ⟨hM.eigenvalues i,hi,_,
    (WithLp.ofLp_eq_zero 2).ne.2 (hM.eigenvectorBasis.orthonormal.ne_zero i),
    hM.mulVec_eigenvectorBasis i⟩

lemma symmetric_eigenvalue_gt_one (a b c : ℝ) (ha : 0 < a)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (e : ℝ) (v : Fin 2 × Fin 2 → ℝ)
    (hv : v ≠ 0) (he : symmetricK a b c*ᵥ v=e • v) : 1 < e := by
  have hp := (symmetricK_sub_one_posDef a b c ha hb hc).dotProduct_mulVec_pos hv
  have hn : 0 < dotProduct v v := by
    simpa only [star_trivial] using dotProduct_star_self_pos_iff.mpr hv
  have hh : (symmetricK a b c-1)*ᵥ v = (e-1) • v := by
    rw [sub_mulVec,he,one_mulVec]
    ext q
    simp [sub_mul]
  rw [hh] at hp
  simp only [star_trivial,dotProduct_smul,smul_eq_mul] at hp
  nlinarith

/-- For two equal exponents, a strict negative direction at the upper endpoint
and the general tensor lower bound give an eigenvalue in `(1,3)`. -/
theorem two_symmetric_low_eigenpair (b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    ∃ e : ℝ, 1 < e ∧ e < 3 ∧ ∃ v : Fin 2 × Fin 2 → ℝ,
      v ≠ 0 ∧ symmetricK 2 b c*ᵥ v=e • v := by
  let M := symmetricK 2 b c-(3 : ℝ) • 1
  have hM : M.IsHermitian := (symmetric_hermitian 2 b c).sub (by simp)
  have hno : ¬M.PosSemidef := by
    intro hp
    let d := 3*(b+1)*(c+1)-1
    let z : Fin 2 × Fin 2 → ℝ := fun q =>
      if q=(0,0) then 2*Real.sqrt b*Real.sqrt c else if q=(1,1) then -d else 0
    have hz := hp.dotProduct_mulVec_nonneg z
    have heq : star z ⬝ᵥ (M*ᵥ z) = -4*b*c*d := by
      simp [M,z,d,symmetricK,E,H,mulVec,dotProduct,Fintype.sum_prod_type,
        Fin.sum_univ_succ,kroneckerMap_apply]
      ring_nf
      simp [Real.sq_sqrt hb.le,Real.sq_sqrt hc.le]
      ring
    rw [heq] at hz
    have hd : 0 < d := by dsimp [d]; nlinarith [mul_pos hb hc]
    have hh := mul_pos (mul_pos hb hc) hd
    nlinarith
  obtain ⟨e,he,z,hz,hze⟩ := negative_eigenpair_of_not_posSemidef M hM hno
  have hS : symmetricK 2 b c*ᵥ z=(e+3) • z := by
    dsimp [M] at hze
    rw [sub_mulVec,smul_mulVec,one_mulVec] at hze
    ext q
    have hh := congrFun hze q
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at hh ⊢
    linarith
  exact ⟨e+3,symmetric_eigenvalue_gt_one 2 b c (by norm_num) hb.le hc.le _ z hz hS,
    by linarith,z,hz,hS⟩


/-- The weighted and symmetric matrices have the same characteristic polynomial.
The diagonal conjugacy is proved explicitly with strictly positive weights. -/
theorem tensor_symmetric_charpoly (a b c r : ℝ) (hb : 0 < b) (hc : 0 < c) :
    (symmetricK a b c-r • 1).charpoly=(tensorK a b c-r • 1).charpoly := by
  have hD : (diagonal (rootWeight b c)).det ≠ 0 := by
    rw [det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun q _ => (rootWeight_pos b c hb hc q).ne')
  apply Matrix.charpoly_eq_of_mul_eq_mul hD
  rw [sub_mul,mul_sub,Matrix.smul_mul,Matrix.mul_smul,one_mul,mul_one,
    weighted_intertwine a b c hb.le hc.le]

/-- Scalar-shift determinants agree under the same proved diagonal transport. -/
theorem tensor_symmetric_det_shift (a b c r : ℝ) (hb : 0 < b) (hc : 0 < c) :
    (symmetricK a b c-r • 1).det=(tensorK a b c-r • 1).det := by
  let D := diagonal (rootWeight b c)
  have hD : D.det ≠ 0 := by
    rw [det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun q _ => (rootWeight_pos b c hb hc q).ne')
  have he : D*(tensorK a b c-r • 1)=(symmetricK a b c-r • 1)*D := by
    rw [mul_sub,sub_mul,Matrix.mul_smul,Matrix.smul_mul,mul_one,one_mul,
      weighted_intertwine a b c hb.le hc.le]
  have hh := congrArg Matrix.det he
  rw [det_mul,det_mul] at hh
  apply mul_left_cancel₀ hD
  simpa only [mul_comm] using hh.symm

end D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionObstructions
