/- GID: D5/S3/Quantum/Analysis/TraceClass/FiniteBlocks
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/TraceClass/FiniteBlocks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive trace-class coordinate compressions on finite Hilbert sums. -/

import D5.S3.Quantum.Analysis.TraceClass.LogRegularization
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! Coordinate compressions keep the full reference Hilbert space. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace BigOperators TensorProduct

namespace TraceClassFiniteBlocks

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The finite Hilbert sum retains one entire reference space in each mode. -/
abbrev Blocks (ι : Type*) (H : Type*) [Fintype ι] := PiLp 2 (fun _ : ι => H)

def coordinate (i : ι) : Blocks ι H →L[ℂ] H := PiLp.proj 2 (fun _ : ι => H) i

def insertion (i : ι) : H →L[ℂ] Blocks ι H := (coordinate i).adjoint

@[simp] private theorem insertion_apply (i : ι) (x : H) :
    insertion i x = PiLp.single 2 i x := by
  apply ext_inner_right ℂ
  intro y
  rw [insertion, ContinuousLinearMap.adjoint_inner_left]
  rw [PiLp.inner_apply, Fintype.sum_eq_single i]
  · simp [coordinate, PiLp.single_apply]
  · intro j hji
    simp [PiLp.single_apply, hji]

@[simp] private theorem coordinate_insertion (i j : ι) (x : H) :
    coordinate i (insertion j x) = if i = j then x else 0 := by
  simp [coordinate, PiLp.single_apply, eq_comm]

/-- Compression onto the reference, rather than an endomorphism of the joint space. -/
def compression (T : Blocks ι H →L[ℂ] Blocks ι H) (i : ι) : H →L[ℂ] H :=
  (coordinate i).comp (T.comp (insertion i))

theorem compression_nonneg {T : Blocks ι H →L[ℂ] Blocks ι H} (hT : 0 ≤ T)
    (i : ι) : 0 ≤ compression T i := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  simpa only [compression, insertion, ContinuousLinearMap.comp_assoc] using
    (ContinuousLinearMap.nonneg_iff_isPositive.mp hT).conj_adjoint (coordinate i)

private theorem block_orthonormal {κ : Type*} (b : HilbertBasis κ ℂ H) :
    Orthonormal ℂ (fun j : ι × κ => insertion j.1 (b j.2)) := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨i,u⟩ ⟨j,v⟩
  by_cases hij : i = j
  · subst j
    simp [PiLp.inner_apply, PiLp.single_apply, apply_ite,
      orthonormal_iff_ite.mp b.orthonormal]
  · simp [PiLp.inner_apply, PiLp.single_apply, apply_ite, hij, Ne.symm hij]

private theorem block_total {κ : Type*} (b : HilbertBasis κ ℂ H) :
    (Submodule.span ℂ (Set.range (fun j : ι × κ => insertion j.1 (b j.2))))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  apply PiLp.ext
  intro i
  have hinner (u : κ) : ⟪b u, x i⟫_ℂ = 0 := by
    have := (Submodule.mem_orthogonal _ _).mp hx _
      (Submodule.subset_span (Set.mem_range_self (i,u)))
    change ⟪insertion i (b u), x⟫_ℂ = 0 at this
    simpa only [insertion, ContinuousLinearMap.adjoint_inner_left, coordinate,
      PiLp.proj_apply] using this
  have hz : b.repr (x i) = 0 := by
    ext u
    simpa only [HilbertBasis.repr_apply_apply, lp.coeFn_zero, Pi.zero_apply] using hinner u
  exact b.repr.injective (by simpa using hz)

private def blockBasis {κ : Type*} (b : HilbertBasis κ ℂ H) :
    HilbertBasis (ι × κ) ℂ (Blocks ι H) :=
  HilbertBasis.mkOfOrthogonalEqBot (block_orthonormal b) (block_total b)

private theorem blockBasis_apply {κ : Type*} (b : HilbertBasis κ ℂ H) (j : ι × κ) :
    blockBasis b j = insertion j.1 (b j.2) := by
  exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) j

private def setBasis {κ : Type*} (b : HilbertBasis κ ℂ H) :
    HilbertBasis (Set.range b) ℂ H :=
  HilbertBasis.mkOfOrthogonalEqBot b.orthonormal.toSubtypeRange (by
    rw [Subtype.range_val, ← Submodule.orthogonal_closure, b.dense_span,
      Submodule.top_orthogonal_eq_bot])

private theorem setBasis_apply {κ : Type*} (b : HilbertBasis κ ℂ H)
    (u : Set.range b) : setBasis b u = u.1 := by
  exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) u

private theorem diagonal_summable {κ : Type*} (b : HilbertBasis κ ℂ H)
    {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    Summable (fun u => ⟪b u, T (b u)⟫_ℂ) := by
  let e := Equiv.ofInjective b b.orthonormal.linearIndependent.injective
  have h := (summable_trace_diagonal_of_isTraceClass hT (setBasis b)).comp_injective
    e.injective
  simpa [setBasis_apply, e, Function.comp_def] using h

private theorem positive_diagonal_summable {κ : Type*} (b : HilbertBasis κ ℂ H)
    {T : H →L[ℂ] H} (hT : IsTraceClass T) (hpos : 0 ≤ T) :
    Summable (fun u => (⟪b u, T (b u)⟫_ℂ).re) := by
  let e := Equiv.ofInjective b b.orthonormal.linearIndependent.injective
  have h := (summable_inner_abs_of_hilbertBasis hT (setBasis b)).comp_injective
    e.injective
  simpa [setBasis_apply, e, Function.comp_def, CFC.abs_of_nonneg T hpos] using h

private theorem trace_on_basis {κ : Type*} (b : HilbertBasis κ ℂ H)
    {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    trace T hT = ∑' u, ⟪b u, T (b u)⟫_ℂ := by
  let e := Equiv.ofInjective b b.orthonormal.linearIndependent.injective
  rw [trace_eq_of_hilbertBasis hT (setBasis b)]
  simpa [setBasis_apply, e] using
    (e.tsum_eq (fun u : Set.range b => ⟪u.1, T u.1⟫_ℂ)).symm

/-- A positive trace-class joint input has trace-class diagonal blocks on an
arbitrary complete reference. No countable basis is required. -/
theorem compression_traceClass {T : Blocks ι H →L[ℂ] Blocks ι H}
    (hT : IsTraceClass T) (hpos : 0 ≤ T) (i : ι) :
    IsTraceClass (compression T i) := by
  obtain ⟨w,b,_⟩ := exists_hilbertBasis ℂ H
  have hs := positive_diagonal_summable (blockBasis (ι := ι) b) hT hpos
  have hi := hs.prod_factor i
  refine ⟨w,b,?_⟩
  rw [CFC.abs_of_nonneg _ (compression_nonneg hpos i)]
  simpa only [blockBasis_apply,
    insertion, ContinuousLinearMap.adjoint_inner_left, compression,
    ContinuousLinearMap.comp_apply] using hi

/-- The diagonal reference traces add to the trace of the same joint input. -/
theorem trace_compression_sum {T : Blocks ι H →L[ℂ] Blocks ι H}
    (hT : IsTraceClass T) (hpos : 0 ≤ T) :
    (∑ i, trace (compression T i) (compression_traceClass hT hpos i)) = trace T hT := by
  obtain ⟨w,b,_⟩ := exists_hilbertBasis ℂ H
  rw [trace_on_basis (blockBasis (ι := ι) b) hT]
  simp_rw [trace_eq_of_hilbertBasis (compression_traceClass hT hpos _) b]
  have hs := diagonal_summable (blockBasis (ι := ι) b) hT
  rw [hs.tsum_prod' hs.prod_factor]
  simp only [tsum_fintype, blockBasis_apply, insertion,
    ContinuousLinearMap.adjoint_inner_left, compression, ContinuousLinearMap.comp_apply]

/-- Embed a reference operator into a fixed joint coordinate. -/
def embedding (A : H →L[ℂ] H) (i : ι) : Blocks ι H →L[ℂ] Blocks ι H :=
  (insertion i).comp (A.comp (coordinate i))

theorem embedding_nonneg {A : H →L[ℂ] H} (hA : 0 ≤ A) (i : ι) :
    0 ≤ embedding A i := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  simpa [embedding, insertion, ContinuousLinearMap.comp_assoc] using
    (ContinuousLinearMap.nonneg_iff_isPositive.mp hA).adjoint_conj (coordinate i)

private theorem embedding_diagonal {κ : Type*} (b : HilbertBasis κ ℂ H)
    (A : H →L[ℂ] H) (i : ι) (j : ι × κ) :
    ⟪blockBasis b j, embedding A i (blockBasis b j)⟫_ℂ =
      if j.1 = i then ⟪b j.2, A (b j.2)⟫_ℂ else 0 := by
  rw [blockBasis_apply, embedding, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, coordinate_insertion]
  by_cases h : j.1 = i
  · subst i
    simp only [if_pos rfl]
    rw [insertion, ContinuousLinearMap.adjoint_inner_right]
    change ⟪coordinate j.1 (insertion j.1 (b j.2)), A (b j.2)⟫_ℂ = _
    simp [coordinate]
  · simp only [if_neg (Ne.symm h), map_zero, inner_zero_right, if_neg h]

/-- A positive reference operator remains trace class in its fixed absorbing block. -/
theorem embedding_traceClass {A : H →L[ℂ] H} (hA : IsTraceClass A)
    (hpos : 0 ≤ A) (i : ι) : IsTraceClass (embedding A i) := by
  classical
  obtain ⟨w,b,_⟩ := exists_hilbertBasis ℂ H
  let B := blockBasis (ι := ι) b
  let e := Equiv.ofInjective B B.orthonormal.linearIndependent.injective
  refine ⟨Set.range B, setBasis B, ?_⟩
  apply e.summable_iff.mp
  simp only [Function.comp_def, setBasis_apply, Equiv.ofInjective_apply,
    CFC.abs_of_nonneg _ (embedding_nonneg hpos i)]
  change Summable (fun j : ι × w => (⟪B j, embedding A i (B j)⟫_ℂ).re)
  simp_rw [B, embedding_diagonal]
  apply (summable_prod_of_nonneg (fun j => by
    split_ifs
    · exact (ContinuousLinearMap.nonneg_iff_isPositive.mp hpos).re_inner_nonneg_right _
    · simp)).mpr
  refine ⟨?_, (hasSum_fintype _).summable⟩
  intro j
  by_cases h : j = i
  · simpa [h] using positive_diagonal_summable b hA hpos
  · simp [h]

/-- Embedding in a fixed mode preserves the actual positive trace and trace norm. -/
theorem embedding_trace_norm {A : H →L[ℂ] H} (hA : IsTraceClass A)
    (hpos : 0 ≤ A) (i : ι) :
    trace (embedding A i) (embedding_traceClass hA hpos i) = trace A hA ∧
    traceNorm (embedding A i) (embedding_traceClass hA hpos i) = traceNorm A hA := by
  classical
  have ht : trace (embedding A i) (embedding_traceClass hA hpos i) = trace A hA := by
    obtain ⟨w,b,_⟩ := exists_hilbertBasis ℂ H
    rw [trace_on_basis (blockBasis (ι := ι) b), trace_eq_of_hilbertBasis hA b]
    have hs := diagonal_summable (blockBasis (ι := ι) b) (embedding_traceClass hA hpos i)
    rw [hs.tsum_prod' hs.prod_factor]
    simp_rw [embedding_diagonal]
    simp only [tsum_fintype]
    have hpiece (j : ι) : (∑' c : w, if j = i then ⟪b c, A (b c)⟫_ℂ else 0) =
        if j = i then ∑' c : w, ⟪b c, A (b c)⟫_ℂ else 0 := by
      split_ifs <;> simp
    simp_rw [hpiece]
    simp
  exact ⟨ht, by rw [QuantumLogEnergy.traceNorm_eq_re_trace _ (embedding_nonneg hpos i),
    QuantumLogEnergy.traceNorm_eq_re_trace _ hpos, ht]⟩

/-- The algebraic tensor correspondence, before verifying its Hilbert norm. -/
private def tensorLinearEquiv : (EuclideanSpace ℂ ι ⊗[ℂ] H) ≃ₗ[ℂ] Blocks ι H :=
  (TensorProduct.congr (WithLp.linearEquiv 2 ℂ (ι → ℂ)) (LinearEquiv.refl ℂ H)) ≪≫ₗ
    TensorProduct.comm ℂ (ι → ℂ) H ≪≫ₗ TensorProduct.piScalarRight ℂ ℂ H ι ≪≫ₗ
      (WithLp.linearEquiv 2 ℂ (ι → H)).symm

private theorem tensorLinearEquiv_tmul (u : EuclideanSpace ℂ ι) (x : H) (i : ι) :
    tensorLinearEquiv (u ⊗ₜ[ℂ] x) i = u i • x := by
  simp [tensorLinearEquiv, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul]

private theorem tensorLinearEquiv_inner (x y : EuclideanSpace ℂ ι ⊗[ℂ] H) :
    ⟪tensorLinearEquiv x, tensorLinearEquiv y⟫_ℂ = ⟪x,y⟫_ℂ := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul u a =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      simp only [PiLp.inner_apply, tensorLinearEquiv_tmul, TensorProduct.inner_tmul,
        inner_smul_left, inner_smul_right]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [RCLike.inner_apply]
      ring
    | add y z hy hz => simpa only [map_add, inner_add_right] using congrArg₂ (· + ·) hy hz
  | add x z hx hz => simpa only [map_add, inner_add_left] using congrArg₂ (· + ·) hx hz

/-- The finite-system tensor product is isometrically and onto the full finite
Hilbert sum, including every reference vector. -/
def tensorCoordinates : (EuclideanSpace ℂ ι ⊗[ℂ] H) ≃ₗᵢ[ℂ] Blocks ι H := by
  exact (tensorLinearEquiv (H := H) (ι := ι)).isometryOfInner
    (fun x y => tensorLinearEquiv_inner x y)

@[simp] theorem tensorCoordinates_tmul (u : EuclideanSpace ℂ ι) (x : H) (i : ι) :
    tensorCoordinates (u ⊗ₜ[ℂ] x) i = u i • x :=
  tensorLinearEquiv_tmul u x i

end TraceClassFiniteBlocks
