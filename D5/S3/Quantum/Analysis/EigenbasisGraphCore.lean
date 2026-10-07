/- GID: D5/S3/Quantum/Analysis/EigenbasisGraphCore
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/EigenbasisGraphCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Weighted coefficients characterize the genuine eigenbasis closure and its finite core. -/

/-
The self-adjoint closure is supplied by EigenbasisClosure and its attributed
PhysLean source chain. The graph characterization uses pinned Mathlib's
Hilbert-basis expansion and actual partial-map graph closure directly.
-/

import D5.S3.Quantum.Analysis.EigenbasisClosure

open LinearPMap Filter
open scoped InnerProductSpace Topology ENNReal lp
noncomputable section
namespace D5.S3.Quantum.Analysis.EigenbasisGraphCore
open D5.S3.Quantum.Analysis.EigenbasisClosure

theorem eigenbasis_graph_coefficients
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : Type*} (e : HilbertBasis ι ℂ H) (T : H →ₗ.[ℂ] H) (lam : ι → ℝ)
    (hdom : T.domain = Submodule.span ℂ (Set.range e))
    (heig : ∀ i, T ⟨e i, hdom ▸ Submodule.subset_span ⟨i, rfl⟩⟩ = (lam i : ℂ) • e i)
    (x y : H) :
    ((x, y) ∈ T.closure.graph ↔ ∀ i, ⟪e i, y⟫_ℂ = (lam i : ℂ) * ⟪e i, x⟫_ℂ) ∧
    ((∀ i, ⟪e i, y⟫_ℂ = (lam i : ℂ) * ⟪e i, x⟫_ℂ) →
      ∃ u : Finset ι → T.domain,
        (∀ F, (u F : H) = ∑ i ∈ F, ⟪e i, x⟫_ℂ • e i) ∧
        (∀ F, T (u F) = ∑ i ∈ F, ((lam i : ℂ) * ⟪e i, x⟫_ℂ) • e i) ∧
        Tendsto (fun F => (u F : H)) atTop (𝓝 x) ∧
        Tendsto (fun F => T (u F)) atTop (𝓝 y)) ∧
    (x ∈ T.closure.domain ↔ Memℓp (fun i => (lam i : ℂ) * ⟪e i, x⟫_ℂ) 2) := by
  classical
  obtain ⟨hc, hsa⟩ := eigenbasis_closable_selfAdjoint e T lam hdom heig
  let v : ι → T.domain := fun i => ⟨e i, hdom ▸ Submodule.subset_span ⟨i, rfl⟩⟩
  let u : Finset ι → T.domain := fun F => ∑ i ∈ F, ⟪e i, x⟫_ℂ • v i
  have huv (F : Finset ι) : (u F : H) = ∑ i ∈ F, ⟪e i, x⟫_ℂ • e i := by
    simp [u, v]
  have hui (F : Finset ι) : T (u F) =
      ∑ i ∈ F, ((lam i : ℂ) * ⟪e i, x⟫_ℂ) • e i := by
    change T.toFun (∑ i ∈ F, ⟪e i, x⟫_ℂ • v i) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [LinearMap.map_smul]
    change ⟪e i, x⟫_ℂ • T ⟨e i, _⟩ = _
    rw [heig, smul_smul, mul_comm]
  have huvlim : Tendsto (fun F => (u F : H)) atTop (𝓝 x) := by
    simpa [HasSum, huv, HilbertBasis.repr_apply_apply] using e.hasSum_repr x
  have hcore (w : H) (hw : ∀ i, ⟪e i, w⟫_ℂ = (lam i : ℂ) * ⟪e i, x⟫_ℂ) :
      Tendsto (fun F => T (u F)) atTop (𝓝 w) := by
    simpa [HasSum, hui, ← hw, HilbertBasis.repr_apply_apply] using e.hasSum_repr w
  have hreverse (w : H) (hw : ∀ i, ⟪e i, w⟫_ℂ = (lam i : ℂ) * ⟪e i, x⟫_ℂ) :
      (x, w) ∈ T.closure.graph := by
    rw [← hc.graph_closure_eq_closure_graph, ← SetLike.mem_coe,
      Submodule.topologicalClosure_coe]
    exact mem_closure_of_tendsto (huvlim.prodMk_nhds (hcore w hw))
      (Eventually.of_forall fun F => T.mem_graph (u F))
  have hsym : T.closure.IsFormalAdjoint T.closure := by
    have h := adjoint_isFormalAdjoint hsa.dense_domain
    rwa [isSelfAdjoint_def.mp hsa] at h
  have hforward (w : H) (hw : (x, w) ∈ T.closure.graph) :
      ∀ i, ⟪e i, w⟫_ℂ = (lam i : ℂ) * ⟪e i, x⟫_ℂ := by
    obtain ⟨z, hz, hTz⟩ := (mem_graph_iff T.closure).mp hw
    intro i
    let vi : T.closure.domain := ⟨e i, (le_closure T).1 (v i).2⟩
    have hei : T.closure vi = (lam i : ℂ) • e i :=
      ((le_closure T).2 (x := v i) (y := vi) rfl).symm.trans (heig i)
    have h := hsym vi z
    change ⟪T.closure vi, (z : H)⟫_ℂ = ⟪e i, T.closure z⟫_ℂ at h
    rw [hei, hz, hTz, inner_smul_left] at h
    simpa using h.symm
  refine ⟨⟨hforward y, hreverse y⟩, fun hy => ⟨u, huv, hui, huvlim, hcore y hy⟩, ?_⟩
  constructor
  · intro hx
    obtain ⟨w, hw⟩ := mem_domain_iff.mp hx
    have heq := hforward w hw
    have heqfun : (e.repr w : ι → ℂ) = fun i => (lam i : ℂ) * ⟪e i, x⟫_ℂ :=
      funext fun i => (e.repr_apply_apply w i).trans (heq i)
    exact heqfun ▸ lp.memℓp (e.repr w)
  · intro hx
    let c : ℓ²(ι, ℂ) := ⟨fun i => (lam i : ℂ) * ⟪e i, x⟫_ℂ, hx⟩
    let w := e.repr.symm c
    have hw : ∀ i, ⟪e i, w⟫_ℂ = (lam i : ℂ) * ⟪e i, x⟫_ℂ := by
      intro i
      rw [← HilbertBasis.repr_apply_apply]
      change e.repr (e.repr.symm c) i = c i
      rw [e.repr.apply_symm_apply]
    exact mem_domain_of_mem_graph (hreverse w hw)

#print axioms eigenbasis_graph_coefficients
end D5.S3.Quantum.Analysis.EigenbasisGraphCore
