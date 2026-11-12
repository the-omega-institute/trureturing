/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/TraceOneTensorSplitting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/TraceOneTensorSplitting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full finite tensors of trace-one two-dimensional operators and field splitting. -/
import D5.S3.Combinatorics.SpectralGraph.Nikandish.RepeatedPairIntegralPolynomial
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Order.Extension.Linear

/-! Source: repeated-pair-modular, PR9 6d491f77b35dec808fc777b69939c56cdae5dc02.
The tensor has every function coordinate. No diagonalizability or distinct
root hypothesis is imposed; zero eigenvalues and repeated roots are retained.
The trace-one hypothesis concerns each actual factor matrix. -/
set_option autoImplicit false
set_option maxRecDepth 2000
noncomputable section
open Finset Matrix Polynomial
open scoped Classical
namespace D5.S3.Combinatorics.SpectralGraph.TraceOneTensorSplitting
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- All coordinates of the ordinary finite tensor, including the empty tensor. -/
def tensor (M : ι → Matrix (Fin 2) (Fin 2) R) :
    Matrix (ι → Fin 2) (ι → Fin 2) R := fun x y => ∏ i, M i (x i) (y i)

/-- Tensor multiplication is the full product-of-sums identity. -/
theorem tensor_mul (M N : ι → Matrix (Fin 2) (Fin 2) R) :
    tensor M*tensor N=tensor (fun i => M i*N i) := by
  ext x y
  simp only [Matrix.mul_apply,tensor]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i j => M i (x i) j*N i j (y i))).symm

theorem tensor_one : tensor (fun _ : ι => (1 : Matrix (Fin 2) (Fin 2) R))=1 := by
  ext x y
  by_cases h : x=y
  · subst y
    simp [tensor]
  · have hi : ∃ i, x i ≠ y i := by
      by_contra! hall
      exact h (funext hall)
    obtain ⟨i,hi⟩ := hi
    simp only [tensor,Matrix.one_apply,if_neg h]
    exact Finset.prod_eq_zero (mem_univ i) (by simp [hi])

/-- Ring maps commute with the entire tensor. -/
theorem tensor_map {S : Type*} [CommRing S] (f : R →+* S)
    (M : ι → Matrix (Fin 2) (Fin 2) R) :
    (tensor M).map f=tensor (fun i => (M i).map f) := by
  ext x y
  simp [tensor,Matrix.map_apply,map_prod]

/-- Every choice of factor eigenpairs gives a nonzero full tensor eigenpair. -/
theorem tensor_eigenpair {K : Type*} [Field K]
    (M : ι → Matrix (Fin 2) (Fin 2) K) (e : ι → K)
    (v : ι → Fin 2 → K) (hv : ∀ i, v i ≠ 0)
    (he : ∀ i, M i*ᵥv i=e i • v i) :
    (fun x : ι → Fin 2 => ∏ i, v i (x i)) ≠ 0 ∧
      tensor M*ᵥ(fun x => ∏ i, v i (x i))=
        (∏ i, e i) • (fun x => ∏ i, v i (x i)) := by
  constructor
  · have hw (i : ι) : ∃ j, v i j ≠ 0 := by
      by_contra! h
      exact hv i (funext h)
    choose j hj using hw
    intro hz
    have ht := congrFun hz j
    exact (Finset.prod_ne_zero_iff.mpr (fun i _ => hj i)) ht
  · ext x
    change (∑ y : ι → Fin 2, (∏ i, M i (x i) (y i))*(∏ i, v i (y i)))=
      (∏ i, e i)*(∏ i, v i (x i))
    simp_rw [← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum (fun i j => M i (x i) j*v i j)]
    have hi (i : ι) : (∑ j, M i (x i) j*v i j)=e i*v i (x i) :=
      congrFun (he i) (x i)
    simp_rw [hi]

/-- Characteristic roots correspond to genuine nonzero eigenvectors. -/
theorem eigenpair_of_root {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (e : K) (he : M.charpoly.IsRoot e) :
    ∃ v : n → K, v ≠ 0 ∧ M*ᵥv=e • v := by
  have hd : (Matrix.scalar n e-M).det=0 := by
    simpa only [Polynomial.IsRoot,Matrix.eval_charpoly] using he
  obtain ⟨v,hv,hM⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  refine ⟨v,hv,?_⟩
  rw [sub_mulVec] at hM
  have hh := sub_eq_zero.mp hM
  ext i
  have hi := congrFun hh.symm i
  simpa [Matrix.scalar, Matrix.mulVec_diagonal, Pi.algebraMap_def] using hi

theorem root_of_eigenpair {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (e : K) (v : n → K) (hv : v ≠ 0)
    (he : M*ᵥv=e • v) : M.charpoly.IsRoot e := by
  change M.charpoly.eval e=0
  rw [Matrix.eval_charpoly]
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨v,hv,?_⟩
  rw [sub_mulVec,he]
  ext i
  simp [Matrix.scalar, Matrix.mulVec_diagonal, Pi.algebraMap_def]

/-- Products of triangular factors remain triangular in a linear extension
of the coordinate order. No factor is assumed diagonalizable. -/
theorem splits_of_triangular {K : Type*} [Field K]
    (M : ι → Matrix (Fin 2) (Fin 2) K) (hM : ∀ i, M i 1 0=0) :
    (tensor M).charpoly.Splits := by
  let e : (ι → Fin 2) ≃ LinearExtension (ι → Fin 2) := Equiv.refl _
  letI : Fintype (LinearExtension (ι → Fin 2)) := Fintype.ofEquiv _ e
  let N := Matrix.reindex e e (tensor M)
  have hN : N.IsUpperTriangular := by
    intro x y hyx
    by_contra hn
    have hxy : e.symm x ≤ e.symm y := by
      change ∀ i, e.symm x i ≤ e.symm y i
      intro i
      by_contra! hlt
      have hxlt := (e.symm x i).isLt
      have hylt := (e.symm y i).isLt
      have hxi : e.symm x i=1 := by omega
      have hyi : e.symm y i=0 := by omega
      apply hn
      apply Finset.prod_eq_zero (mem_univ i)
      simpa [hxi,hyi] using hM i
    exact (not_le_of_gt hyx) ((toLinearExtension (α := ι → Fin 2)).monotone hxy)
  have hc := Matrix.charpoly_of_isUpperTriangular N hN
  rw [Matrix.charpoly_reindex] at hc
  rw [hc]
  exact Polynomial.Splits.prod (fun _ _ => Polynomial.Splits.X_sub_C _)

/-- Any split trace-one factor has a triangular unit conjugacy, including
repeated roots. The nonsymmetric companion calculation retains both entries. -/
theorem triangular_conjugacy {K : Type*} [Field K]
    (M : Matrix (Fin 2) (Fin 2) K) (htr : M.trace=1) (hs : M.charpoly.Splits) :
    ∃ P : (Matrix (Fin 2) (Fin 2) K)ˣ,
      ∃ U : Matrix (Fin 2) (Fin 2) K,
        M*(P : Matrix _ _ K)=(P : Matrix _ _ K)*U ∧ U 1 0=0 := by
  by_cases hc : M 1 0=0
  · exact ⟨1,M,by simp, hc⟩
  obtain ⟨r,hr⟩ := hs.exists_eval_eq_zero (by simp)
  let P : Matrix (Fin 2) (Fin 2) K := !![r-M 1 1,1;M 1 0,0]
  let U : Matrix (Fin 2) (Fin 2) K := !![r,1;0,1-r]
  have hd : P.det ≠ 0 := by simpa [P,Matrix.det_fin_two] using neg_ne_zero.mpr hc
  obtain ⟨Q,hQ⟩ := (Matrix.isUnit_iff_isUnit_det P).mpr (isUnit_iff_ne_zero.mpr hd)
  refine ⟨Q,U,?_,by simp [U]⟩
  rw [hQ]
  have htrace : M 0 0+M 1 1=1 := by simpa [Matrix.trace,Fin.sum_univ_two] using htr
  have hroot : (r-M 0 0)*(r-M 1 1)-M 0 1*M 1 0=0 := by
    simpa [Matrix.eval_charpoly,Matrix.scalar,Matrix.det_fin_two] using hr
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P,U,Matrix.mul_apply,Fin.sum_univ_two]
  all_goals (solve | ring | linear_combination htrace | linear_combination -hroot)

/-- Units of the factors give a unit of the full tensor. -/
def tensorUnit {K : Type*} [Field K]
    (P : ι → (Matrix (Fin 2) (Fin 2) K)ˣ) :
    (Matrix (ι → Fin 2) (ι → Fin 2) K)ˣ where
  val := tensor (fun i => P i)
  inv := tensor (fun i => ((P i)⁻¹ : (Matrix (Fin 2) (Fin 2) K)ˣ))
  val_inv := by rw [tensor_mul]; simpa using (tensor_one (ι := ι) (R := K))
  inv_val := by rw [tensor_mul]; simpa using (tensor_one (ι := ι) (R := K))

/-- The full sufficiency direction of trace-one tensor splitting. -/
theorem splits_of_factors {K : Type*} [Field K]
    (M : ι → Matrix (Fin 2) (Fin 2) K) (htr : ∀ i, (M i).trace=1)
    (hs : ∀ i, (M i).charpoly.Splits) : (tensor M).charpoly.Splits := by
  choose P U hPU hU using fun i => triangular_conjugacy (M i) (htr i) (hs i)
  have he : tensor M*(tensorUnit P : Matrix _ _ K)=
      (tensorUnit P : Matrix _ _ K)*tensor U := by
    change tensor M*tensor (fun i => P i)=tensor (fun i => P i)*tensor U
    rw [tensor_mul,tensor_mul]
    congr 1
    funext i
    exact hPU i
  have hdet : (tensorUnit P).val.det ≠ 0 := by
    have hu := Matrix.isUnits_det_units (tensorUnit P)
    exact hu.ne_zero
  rw [Matrix.charpoly_eq_of_mul_eq_mul hdet he]
  exact splits_of_triangular U hU

end D5.S3.Combinatorics.SpectralGraph.TraceOneTensorSplitting
