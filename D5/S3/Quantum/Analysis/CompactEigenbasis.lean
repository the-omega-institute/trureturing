/- GID: D5/S3/Quantum/Analysis/CompactEigenbasis
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/CompactEigenbasis
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full set-indexed real eigenbases for compact symmetric real or complex Hilbert operators. -/

import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

open scoped InnerProductSpace
noncomputable section

namespace D5.S3.Quantum.Analysis.CompactEigenbasis

universe u

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

end D5.S3.Quantum.Analysis.CompactEigenbasis
