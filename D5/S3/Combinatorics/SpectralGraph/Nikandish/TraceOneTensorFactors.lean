/- GID: D5/S3/Combinatorics/SpectralGraph/TraceOneTensorFactors
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/TraceOneTensorFactors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Necessity of factor splitting for every finite trace-one tensor over a field. -/
import D5.S3.Combinatorics.SpectralGraph.TraceOneTensorSplitting

/-! Source: repeated-pair-modular, PR9 6d491f77b35dec808fc777b69939c56cdae5dc02.
The argument fixes nonzero roots only in the other factors. The chosen
factor retains both roots, including zero and a repeated root. Full tensor
splitting forces their products into the original field; their sum recovers
the nonzero other-factor product. -/
set_option autoImplicit false
set_option maxRecDepth 2000
noncomputable section
open Finset Matrix Polynomial
open scoped Classical
namespace D5.S3.Combinatorics.SpectralGraph.TraceOneTensorFactors
open TraceOneTensorSplitting
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The second characteristic root is the trace-one complement, in every
characteristic, including characteristic two and repeated roots. -/
theorem complement_root {K : Type*} [Field K]
    (M : Matrix (Fin 2) (Fin 2) K) (htr : M.trace=1) (r : K)
    (hr : M.charpoly.IsRoot r) : M.charpoly.IsRoot (1-r) := by
  have ht : M 0 0+M 1 1=1 := by simpa [Matrix.trace,Fin.sum_univ_two] using htr
  have he : (r-M 0 0)*(r-M 1 1)-M 0 1*M 1 0=0 := by
    simpa [Polynomial.IsRoot,Matrix.eval_charpoly,Matrix.scalar,Matrix.det_fin_two] using hr
  change M.charpoly.eval (1-r)=0
  rw [Matrix.eval_charpoly]
  simp only [Matrix.det_fin_two, Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  norm_num
  linear_combination he+(2*r-1)*ht

/-- Each trace-one factor has a nonzero characteristic root in an
algebraically closed field. The other root may be zero. -/
theorem nonzero_root {K : Type*} [Field K] [IsAlgClosed K]
    (M : Matrix (Fin 2) (Fin 2) K) (htr : M.trace=1) :
    ∃ r : K, r ≠ 0 ∧ M.charpoly.IsRoot r := by
  obtain ⟨r,hr⟩ := IsAlgClosed.exists_root M.charpoly (by
    rw [Matrix.charpoly_degree_eq_dim]
    norm_num)
  by_cases hz : r=0
  · refine ⟨1,one_ne_zero,?_⟩
    simpa [hz] using complement_root M htr r hr
  · exact ⟨r,hz,hr⟩

/-- Under full tensor splitting, every product of characteristic roots
in a field extension lies in the base-field image. -/
theorem root_product_in_range {K E : Type*} [Field K] [Field E]
    (f : K →+* E) (M : ι → Matrix (Fin 2) (Fin 2) K)
    (hs : (tensor M).charpoly.Splits) (r : ι → E)
    (hr : ∀ i, ((M i).map f).charpoly.IsRoot (r i)) :
    (∏ i, r i) ∈ f.range := by
  choose v hv he using fun i => eigenpair_of_root ((M i).map f) (r i) (hr i)
  obtain ⟨hw,hW⟩ := tensor_eigenpair (fun i => (M i).map f) r v hv he
  have ht := root_of_eigenpair (tensor (fun i => (M i).map f)) (∏ i, r i)
    (fun x => ∏ i, v i (x i)) hw hW
  rw [← tensor_map,Matrix.charpoly_map] at ht
  exact hs.mem_range_of_isRoot (tensor M).charpoly_monic.ne_zero ht

/-- Necessity for arbitrary finite families of actual trace-one matrices,
without a semisimplicity, nonzero-determinant or characteristic restriction. -/
theorem factors_split {K : Type*} [Field K]
    (M : ι → Matrix (Fin 2) (Fin 2) K) (htr : ∀ i, (M i).trace=1)
    (hs : (tensor M).charpoly.Splits) : ∀ i, (M i).charpoly.Splits := by
  let E := AlgebraicClosure K
  let f : K →+* E := algebraMap K E
  have htrE (j : ι) : ((M j).map f).trace=1 := by
    rw [← AddMonoidHom.map_trace]
    simp [htr j]
  choose r hrn hr using fun j => nonzero_root ((M j).map f) (htrE j)
  intro i
  have hsplit : ((M i).charpoly.map f).Splits := IsAlgClosed.splits _
  apply hsplit.of_splits_map_of_injective f.injective
  intro x hx
  have hxroot : ((M i).map f).charpoly.IsRoot x := by
    rw [Matrix.charpoly_map]
    exact (Polynomial.mem_roots (Polynomial.map_ne_zero (M i).charpoly_monic.ne_zero)).mp hx
  have hyroot := complement_root ((M i).map f) (htrE i) x hxroot
  let rx : ι → E := Function.update r i x
  let ry : ι → E := Function.update r i (1-x)
  have hrx (j : ι) : ((M j).map f).charpoly.IsRoot (rx j) := by
    by_cases hj : j=i
    · subst j; simpa [rx] using hxroot
    · simpa [rx,Function.update_of_ne hj] using hr j
  have hry (j : ι) : ((M j).map f).charpoly.IsRoot (ry j) := by
    by_cases hj : j=i
    · subst j; simpa [ry] using hyroot
    · simpa [ry,Function.update_of_ne hj] using hr j
  obtain ⟨u,hu⟩ := root_product_in_range f M hs rx hrx
  obtain ⟨v,hv⟩ := root_product_in_range f M hs ry hry
  let P : E := ∏ j ∈ univ.erase i, r j
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hrn j)
  have hpx : ∏ j, rx j=x*P := by
    rw [← Finset.mul_prod_erase _ _ (mem_univ i)]
    simp only [rx,Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    exact Function.update_of_ne (Finset.mem_erase.mp hj).1 _ _
  have hpy : ∏ j, ry j=(1-x)*P := by
    rw [← Finset.mul_prod_erase _ _ (mem_univ i)]
    simp only [ry,Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    exact Function.update_of_ne (Finset.mem_erase.mp hj).1 _ _
  rw [hpx] at hu
  rw [hpy] at hv
  have hsum : f (u+v)=P := by rw [map_add,hu,hv]; ring
  have hsumne : f (u+v) ≠ 0 := by rwa [hsum]
  refine ⟨u/(u+v),?_⟩
  rw [map_div₀,hu,hsum]
  exact mul_div_cancel_right₀ x hP

/-- The complete trace-one tensor splitting equivalence. -/
theorem tensor_splits_iff {K : Type*} [Field K]
    (M : ι → Matrix (Fin 2) (Fin 2) K) (htr : ∀ i, (M i).trace=1) :
    (tensor M).charpoly.Splits ↔ ∀ i, (M i).charpoly.Splits :=
  ⟨factors_split M htr,splits_of_factors M htr⟩

end D5.S3.Combinatorics.SpectralGraph.TraceOneTensorFactors
