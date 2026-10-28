/- GID: D5/S3/Quantum/Analysis/TraceClass/Spectral
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/TraceClass/Spectral
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete positive trace-class spectra retain the kernel and yield actual trace and vector sums with faithful finite or Nat bases. -/

import D5.S3.Quantum.Analysis.TraceClass.Compact
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Data.Set.Countable
import Mathlib.Basic.Denumerable
import Mathlib.Logic.Equiv.Set
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

open scoped ComplexOrder InnerProductSpace
open Filter Topology
noncomputable section

namespace TraceClassSpectral

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Assemble a complete real eigenbasis of the actual compact symmetric operator.
Every eigenspace is a fiber, including eigenvalue zero, over either real or complex
scalars. The resulting carrier is a subset of the original Hilbert space. -/
theorem exists_setIndex_real_eigenbasis_rclike
    {𝕜 : Type} [RCLike 𝕜] {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] {T : E →L[𝕜] E} (hTc : IsCompactOperator T) (hTs : T.IsSymmetric) :
    ∃ (w : Set E) (b : HilbertBasis w 𝕜 E) (s : w → ℝ),
      ∀ i, T (b i) = (s i : 𝕜) • b i := by
  classical
  let K : 𝕜 → Submodule 𝕜 E := fun μ => Module.End.eigenspace T.toLinearMap μ
  letI (μ : 𝕜) : IsClosed (K μ : Set E) := by
    dsimp only [K]
    exact ContinuousLinearMap.isClosed_eigenspace T μ
  letI (μ : 𝕜) : CompleteSpace (K μ) := inferInstance
  have hfiber (μ : 𝕜) :
      ∃ (w : Set (K μ)) (b : HilbertBasis w 𝕜 (K μ)), ⇑b = ((↑) : w → K μ) :=
    exists_hilbertBasis 𝕜 (K μ)
  choose w b hb using hfiber
  let I : Type u := Σ μ : 𝕜, w μ
  let v : I → E := fun i => (b i.1 i.2 : E)
  have hfamily : OrthogonalFamily 𝕜 (fun μ => K μ) (fun μ => (K μ).subtypeₗᵢ) := by
    simpa only [K] using hTs.orthogonalFamily_eigenspaces
  have hv : Orthonormal 𝕜 v :=
    hfamily.orthonormal_sigma_orthonormal (fun μ => (b μ).orthonormal)

  -- Full Hilbert-space completeness, not algebraic internality of a direct sum.
  have horth : (Submodule.span 𝕜 (Set.range v))ᗮ = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    have hfiberOrth (μ : 𝕜) : x ∈ (K μ)ᗮ := by
      let f : K μ →L[𝕜] 𝕜 := (innerSL 𝕜 x).comp (K μ).subtypeL
      have hdense : Dense (Submodule.span 𝕜 (Set.range (b μ)) : Set (K μ)) :=
        Submodule.dense_iff_topologicalClosure_eq_top.mpr (b μ).dense_span
      have hfzero : f = 0 := ContinuousLinearMap.ext_on hdense (by
        rintro _ ⟨i, rfl⟩
        change ⟪x, (b μ i : E)⟫_𝕜 = 0
        exact (Submodule.mem_orthogonal' (Submodule.span 𝕜 (Set.range v)) x).mp hx
          (b μ i : E) (Submodule.subset_span ⟨⟨μ, i⟩, rfl⟩))
      apply (Submodule.mem_orthogonal' (K μ) x).mpr
      intro y hy
      have hfy := congrArg (fun g : K μ →L[𝕜] 𝕜 => g ⟨y, hy⟩) hfzero
      change ⟪x, y⟫_𝕜 = 0 at hfy
      exact hfy
    have hxall : x ∈ (⨆ μ, K μ)ᗮ := by
      rw [← Submodule.iInf_orthogonal]
      exact (Submodule.mem_iInf (fun μ => (K μ)ᗮ)).mpr hfiberOrth
    have hspec : (⨆ μ, K μ)ᗮ = ⊥ := by
      simpa only [K] using
        ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hTc hTs
    rw [hspec] at hxall
    exact hxall

  let B : HilbertBasis I 𝕜 E := HilbertBasis.mkOfOrthogonalEqBot hv horth
  have hB (i : I) : B i = v i :=
    congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot hv horth) i
  have heigen (i : I) : T (B i) = i.1 • B i := by
    rw [hB]
    exact Module.End.mem_eigenspace_iff.mp (b i.1 i.2).property
  have hreal (i : I) : (RCLike.re i.1 : 𝕜) = i.1 := by
    apply RCLike.conj_eq_iff_re.mp
    apply hTs.conj_eigenvalue_eq_self
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (heigen i), B.orthonormal.ne_zero i⟩
  let sI : I → ℝ := fun i => RCLike.re i.1
  have heigenReal (i : I) : T (B i) = (sI i : 𝕜) • B i := by
    change T (B i) = (RCLike.re i.1 : 𝕜) • B i
    rw [hreal i]
    exact heigen i

  -- Actual range carrier bridge: no invented HilbertBasis.reindex interface.
  let W : Set E := Set.range B
  have hBinj : Function.Injective B := B.orthonormal.linearIndependent.injective
  let e : I ≃ W := Equiv.ofInjective B hBinj
  have hWortho : Orthonormal 𝕜 ((↑) : W → E) := B.orthonormal.toSubtypeRange
  have hWrange : Set.range ((↑) : W → E) = Set.range B := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact i.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hWspan : ⊤ ≤ (Submodule.span 𝕜 (Set.range ((↑) : W → E))).topologicalClosure := by
    rw [hWrange]
    exact B.dense_span.ge
  let C : HilbertBasis W 𝕜 E := HilbertBasis.mk hWortho hWspan
  have hC (i : W) : C i = (i : E) :=
    congrFun (HilbertBasis.coe_mk hWortho hWspan) i
  have heback (i : W) : B (e.symm i) = (i : E) :=
    Equiv.apply_ofInjective_symm hBinj i
  let sW : W → ℝ := fun i => sI (e.symm i)
  refine ⟨W, C, sW, ?_⟩
  intro i
  have hCE : C i = B (e.symm i) := (hC i).trans (heback i).symm
  simpa only [hCE, sW] using heigenReal (e.symm i)

private theorem exists_setIndex_real_eigenbasis_of_compact_isSymmetric
    {T : H →L[ℂ] H} (hTc : IsCompactOperator T) (hTs : T.IsSymmetric) :
    ∃ (w : Set H) (b : HilbertBasis w ℂ H) (s : w → ℝ),
      ∀ i, T (b i) = (s i : ℂ) • b i :=
  exists_setIndex_real_eigenbasis_rclike hTc hTs

/-- Nonnegativity uses the genuine nonnegative quadratic form and a nonzero eigenvector;
it never invokes the impossible strict-positive-at-zero API. -/
private theorem exists_setIndex_nonneg_eigenbasis_of_compact
    {T : H →L[ℂ] H} (hTc : IsCompactOperator T) (hTpos : 0 ≤ T) :
    ∃ (w : Set H) (b : HilbertBasis w ℂ H) (s : w → ℝ),
      (∀ i, 0 ≤ s i) ∧ (∀ i, T (b i) = (s i : ℂ) • b i) := by
  have hTp : T.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive).mp hTpos
  obtain ⟨w, b, s, heigen⟩ :=
    exists_setIndex_real_eigenbasis_of_compact_isSymmetric hTc hTp.isSymmetric
  refine ⟨w, b, s, ?_, heigen⟩
  intro i
  apply eigenvalue_nonneg_of_nonneg ?_ hTp.re_inner_nonneg_right
  exact Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.mpr (heigen i), b.orthonormal.ne_zero i⟩

/-- Consume the adopted set-indexed trace and actual diagonal summability suppliers.
This is the trace consumer of the assembled basis, not a reproof of basis independence.
It also applies to general positive trace-class operators with zero spectral weights. -/
private theorem spectral_values_hasSum_trace_re
    {T : H →L[ℂ] H} (hTpos : 0 ≤ T) (hTtc : IsTraceClass T)
    {w : Set H} (b : HilbertBasis w ℂ H) (s : w → ℝ)
    (heigen : ∀ i, T (b i) = (s i : ℂ) • b i) :
    HasSum s (trace T hTtc).re := by
  have hdiag (i : w) : ⟪b i, T (b i)⟫_ℂ = (s i : ℂ) := by
    rw [heigen i, inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp [b.orthonormal.1 i]
  have hs : Summable s := by
    have h := summable_inner_abs_of_hilbertBasis hTtc b
    rw [CFC.abs_of_nonneg T hTpos] at h
    apply h.congr
    intro i
    rw [hdiag i, Complex.ofReal_re]
  have htrace : trace T hTtc = ((∑' i : w, s i : ℝ) : ℂ) := by
    rw [trace_eq_of_hilbertBasis_of_nonneg hTpos hTtc b]
    calc
      (∑' i : w, ⟪b i, T (b i)⟫_ℂ) = ∑' i : w, (s i : ℂ) := tsum_congr hdiag
      _ = ((∑' i : w, s i : ℝ) : ℂ) := (Complex.ofReal_tsum s).symm
  rw [htrace, Complex.ofReal_re]
  exact hs.hasSum

/-- Continuous application of the actual operator to the full basis expansion. -/
private theorem weighted_hasSum {ι : Type*} {T : H →L[ℂ] H}
    (b : HilbertBasis ι ℂ H) (s : ι → ℝ)
    (heigen : ∀ i, T (b i) = (s i : ℂ) • b i) (x : H) :
    HasSum (fun i => (b.repr x i * (s i : ℂ)) • b i) (T x) := by
  simpa only [map_smul, heigen, smul_smul] using (b.hasSum_repr x).mapL T

/-- The full spectrum of the original positive trace-class operator, including its kernel.
Compactness is derived, and summability precedes the trace identification. -/
theorem exists_nonneg_trace_spectral_data
    {T : H →L[ℂ] H} (hTpos : 0 ≤ T) (hTtc : IsTraceClass T) :
    ∃ (w : Set H) (b : HilbertBasis w ℂ H) (s : w → ℝ),
      (∀ i, 0 ≤ s i) ∧ (∀ i, T (b i) = (s i : ℂ) • b i) ∧
      Summable s ∧ HasSum s (trace T hTtc).re ∧
      HasSum (fun i => (s i : ℂ)) (trace T hTtc) ∧
      ∀ x : H, HasSum (fun i => (b.repr x i * (s i : ℂ)) • b i) (T x) := by
  obtain ⟨w, b, s, hnonneg, heigen⟩ := exists_setIndex_nonneg_eigenbasis_of_compact
    (isCompactOperator_of_nonneg_isTraceClass hTtc hTpos) hTpos
  have hsum := spectral_values_hasSum_trace_re hTpos hTtc b s heigen
  have hdiag (i : w) : ⟪b i, T (b i)⟫_ℂ = (s i : ℂ) := by
    rw [heigen i, inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp [b.orthonormal.1 i]
  have hc : HasSum (fun i => (s i : ℂ)) (trace T hTtc) := by
    rw [trace_eq_of_hilbertBasis_of_nonneg hTpos hTtc b]
    simp_rw [hdiag]
    exact (Complex.hasSum_ofReal.mpr hsum.summable.hasSum).summable.hasSum
  exact ⟨w, b, s, hnonneg, heigen, hsum.summable, hsum, hc, weighted_hasSum b s heigen⟩

/-- Faithfulness removes zero weights. Only then does summability make the entire
basis index countable; no separability premise or uniform spectral gap is used. -/
theorem exists_faithful_reference_spectral_data
    {σ : H →L[ℂ] H} (hσpos : 0 ≤ σ) (hσtc : IsTraceClass σ)
    (hker : σ.toLinearMap.ker = ⊥) (htrace : trace σ hσtc = 1) :
    ∃ (w : Set H) (b : HilbertBasis w ℂ H) (s : w → ℝ),
      (∀ i, 0 < s i) ∧ (∀ i, σ (b i) = (s i : ℂ) • b i) ∧
      Summable s ∧ HasSum s 1 ∧ HasSum (fun i => (s i : ℂ)) 1 ∧
      (∀ x : H, HasSum (fun i => (b.repr x i * (s i : ℂ)) • b i) (σ x)) ∧
      Countable w := by
  classical
  obtain ⟨w, b, s, hnonneg, heigen, hs, hsumTrace, hc, hv⟩ :=
    exists_nonneg_trace_spectral_data hσpos hσtc
  have hstrict (i : w) : 0 < s i := by
    apply lt_of_le_of_ne (hnonneg i)
    intro hzero
    have hz : s i = 0 := hzero.symm
    have hσzero : σ (b i) = 0 := by
      simpa only [hz, Complex.ofReal_zero, zero_smul] using heigen i
    have hmem : b i ∈ σ.toLinearMap.ker := hσzero
    have hbzero : b i = 0 := by simpa only [hker, Submodule.mem_bot] using hmem
    exact b.orthonormal.ne_zero i hbzero
  have hsum : HasSum s 1 := by simpa only [htrace, Complex.one_re] using hsumTrace
  have hsupport : Function.support s = Set.univ := by
    ext i
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (hstrict i).ne'
  have hcountSet : (Set.univ : Set w).Countable := by
    rw [← hsupport]
    exact hs.countable_support
  exact ⟨w, b, s, hstrict, heigen, hs, hsum, by simpa only [htrace] using hc,
    hv, Set.countable_univ_iff.mp hcountSet⟩

/-- Reindex a full basis along an actual bijection. -/
private theorem reindex_basis {ι κ : Type*} (b : HilbertBasis ι ℂ H) (e : κ ≃ ι) :
    ∃ B : HilbertBasis κ ℂ H, ∀ i, B i = b (e i) := by
  let v : κ → H := fun i => b (e i)
  have hv : Orthonormal ℂ v := b.orthonormal.comp e e.injective
  have hrange : Set.range v = Set.range b := e.surjective.range_comp b
  have hspan : ⊤ ≤ (Submodule.span ℂ (Set.range v)).topologicalClosure := by
    rw [hrange]
    exact b.dense_span.ge
  exact ⟨HilbertBasis.mk hv hspan, fun i => congrFun (HilbertBasis.coe_mk hv hspan) i⟩

/-- A faithful normalized state has either an actual finite full basis or an actual
Nat full basis. All trace sums and the original-operator vector expansion are retained. -/
theorem faithful_reference_finite_or_nat
    {σ : H →L[ℂ] H} (hσpos : 0 ≤ σ) (hσtc : IsTraceClass σ)
    (hker : σ.toLinearMap.ker = ⊥) (htrace : trace σ hσtc = 1) :
    (∃ (n : ℕ) (b : HilbertBasis (Fin n) ℂ H) (s : Fin n → ℝ),
      FiniteDimensional ℂ H ∧ (∀ i, 0 < s i) ∧
      (∀ i, σ (b i) = (s i : ℂ) • b i) ∧
      Summable s ∧ HasSum s 1 ∧ HasSum (fun i => (s i : ℂ)) 1 ∧
      ∀ x : H, HasSum (fun i => (b.repr x i * (s i : ℂ)) • b i) (σ x)) ∨
    (∃ (w : Set H) (c : HilbertBasis w ℂ H) (e : w ≃ ℕ)
      (b : HilbertBasis ℕ ℂ H) (s : ℕ → ℝ),
      (∀ i, b i = c (e.symm i)) ∧ (∀ i, 0 < s i) ∧ (∀ i, σ (b i) = (s i : ℂ) • b i) ∧
      Summable s ∧ HasSum s 1 ∧ HasSum (fun i => (s i : ℂ)) 1 ∧
      ∀ x : H, HasSum (fun i => (b.repr x i * (s i : ℂ)) • b i) (σ x)) := by
  classical
  obtain ⟨w, b, s, hstrict, heigen, hs, hsum, hc, _, hcount⟩ :=
    exists_faithful_reference_spectral_data hσpos hσtc hker htrace
  letI : Countable w := hcount
  rcases finite_or_infinite w with hfinite | hinfinite
  · letI : Finite w := hfinite
    letI : Fintype w := Fintype.ofFinite w
    let e : Fin (Fintype.card w) ≃ w := (Fintype.equivFin w).symm
    obtain ⟨B, hB⟩ := reindex_basis b e
    have hE (i) : σ (B i) = ((s ∘ e) i : ℂ) • B i := by
      simpa only [hB, Function.comp_apply] using heigen (e i)
    refine Or.inl ⟨Fintype.card w, B, s ∘ e,
      b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite,
      fun i => hstrict (e i), hE, ?_, ?_, ?_, weighted_hasSum B (s ∘ e) hE⟩
    · exact (e.hasSum_iff.mpr hsum).summable
    · exact e.hasSum_iff.mpr hsum
    · exact e.hasSum_iff.mpr hc
  · letI : Infinite w := hinfinite
    letI : Denumerable w := Classical.choice (nonempty_denumerable w)
    let e : w ≃ ℕ := Denumerable.eqv w
    obtain ⟨B, hB⟩ := reindex_basis b e.symm
    have hE (i) : σ (B i) = ((s ∘ e.symm) i : ℂ) • B i := by
      simpa only [hB, Function.comp_apply] using heigen (e.symm i)
    refine Or.inr ⟨w, b, e, B, s ∘ e.symm, hB, fun i => hstrict (e.symm i), hE,
      ?_, ?_, ?_, weighted_hasSum B (s ∘ e.symm) hE⟩
    · exact (e.symm.hasSum_iff.mpr hsum).summable
    · exact e.symm.hasSum_iff.mpr hsum
    · exact e.symm.hasSum_iff.mpr hc

end TraceClassSpectral
