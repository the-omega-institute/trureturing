/- GID: D5/S3/Quantum/Analysis/EigenbasisClosure
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/EigenbasisClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A real Hilbert eigenbasis gives a genuine self-adjoint operator closure. -/

/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/

/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Gregory J. Loges
-/

/-
Adapted from HEPLean/PhysLean at b9043cc548ef6d63a28454cf3a57fb12a0c2e142:
PhyslibAlpha/AlgebraicFramework/HilbertSpace/Unbounded/RealAnalytic.lean,
isEssentiallySelfAdjoint_of_hilbertBasis_eigenvectors; and the polarization,
adjoint-order, closure-symmetry and resolvent-range arguments in
Physlib/QuantumMechanics/Operators/Unbounded.lean.
Changes: retain one theorem, keeping support local and using pinned Mathlib
partial maps and the full-domain identity directly.
Full license: docs/reports/oscillator-suppliers/physlib-LICENSE.txt.
The authenticated source tree has no NOTICE-named file.
Retirement: an exact direct supplier at this repository's own pinned Mathlib
revision supersedes this recovery when the actual operator consumers validate.
-/

import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic

open Complex LinearPMap Filter
open scoped InnerProductSpace ComplexConjugate Topology ENNReal
namespace D5.S3.Quantum.Analysis.EigenbasisClosure

/-- The finite real-eigenbasis operator is closable and its genuine closure is
self-adjoint, allowing zero and repeated eigenvalues and arbitrary index types. -/
theorem eigenbasis_closable_selfAdjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : Type*} (e : HilbertBasis ι ℂ H) (T : H →ₗ.[ℂ] H) (lam : ι → ℝ)
    (hdom : T.domain = Submodule.span ℂ (Set.range e))
    (heig : ∀ i, T ⟨e i, hdom ▸ Submodule.subset_span ⟨i, rfl⟩⟩ = (lam i : ℂ) • e i) :
    T.IsClosable ∧ IsSelfAdjoint T.closure := by
  classical
  let idP : H →ₗ.[ℂ] H := (LinearMap.id : H →ₗ[ℂ] H).toPMap ⊤
  have hidDom : idP.domain = ⊤ := rfl
  have symm_iff (A : H →ₗ.[ℂ] H) : A.IsFormalAdjoint A ↔
      ∀ x : A.domain, conj ⟪A x, (x : H)⟫_ℂ = ⟪A x, (x : H)⟫_ℂ := by
    have pol (x y : A.domain) : ⟪A y, (x : H)⟫_ℂ =
        (⟪A (x + y), ↑(x + y)⟫_ℂ - ⟪A (x - y), ↑(x - y)⟫_ℂ +
          I * ⟪A (x + I • y), ↑(x + I • y)⟫_ℂ -
          I * ⟪A (x - I • y), ↑(x - I • y)⟫_ℂ) / 4 := by
      simp only [LinearPMap.map_add, Submodule.coe_add, inner_add_right, inner_add_left, LinearPMap.map_sub,
        AddSubgroupClass.coe_sub, inner_sub_right, inner_sub_left, sub_sub,
        LinearPMap.map_smul, SetLike.val_smul, inner_smul_left, conj_I, neg_mul,
        inner_smul_right, mul_add, mul_neg, ← mul_assoc, ← pow_two, I_sq,
        one_mul, neg_neg, sub_neg_eq_add, mul_sub]
      ring
    have pol' (x y : A.domain) : ⟪A x, (y : H)⟫_ℂ =
        (⟪A (x + y), ↑(x + y)⟫_ℂ - ⟪A (x - y), ↑(x - y)⟫_ℂ -
          I * ⟪A (x + I • y), ↑(x + I • y)⟫_ℂ +
          I * ⟪A (x - I • y), ↑(x - I • y)⟫_ℂ) / 4 := by
      simp only [LinearPMap.map_add, Submodule.coe_add, inner_add_right, inner_add_left, LinearPMap.map_sub,
        AddSubgroupClass.coe_sub, inner_sub_right, inner_sub_left, sub_sub,
        LinearPMap.map_smul, SetLike.val_smul, inner_smul_left, conj_I, neg_mul,
        inner_smul_right, mul_add, mul_neg, ← mul_assoc, ← pow_two, I_sq,
        one_mul, neg_neg, sub_neg_eq_add, mul_sub]
      ring
    refine ⟨fun h x ↦ by simp [h x x], fun h x y ↦ ?_⟩
    nth_rw 2 [← inner_conj_symm, pol]
    simp only [map_div₀, _root_.map_sub, _root_.map_add, map_mul, neg_mul,
      conj_ofNat, conj_I, h]
    rw [pol']
    simp [sub_eq_add_neg]
  have adj_antitone {A B : H →ₗ.[ℂ] H}
      (hA : Dense (A.domain : Set H)) (hle : A ≤ B) : B† ≤ A† := by
    have hagree : ∀ w : A.domain, A w = B ⟨w, hle.1 w.2⟩ :=
      fun w ↦ @hle.2 w ⟨w, hle.1 w.2⟩ rfl
    constructor
    · intro v
      let f₁ : A.domain → ℂ := fun w ↦ ⟪v, A w⟫_ℂ
      let f₂ : B.domain → ℂ := fun w ↦ ⟪v, B w⟫_ℂ
      change Continuous f₂ → Continuous f₁
      suffices f₁ = fun w : A.domain ↦ f₂ ⟨w, hle.1 w.2⟩ by rw [this]; fun_prop
      simp [f₁, f₂, hagree]
    · intro u v huv
      have hB : Dense (B.domain : Set H) := hA.mono hle.1
      refine (LinearPMap.adjoint_apply_eq hA v fun w ↦ ?_).symm
      rw [LinearPMap.adjoint_isFormalAdjoint hB u ⟨w, hle.1 w.2⟩, hagree, huv]
  have range_criterion (A : H →ₗ.[ℂ] H) (hsym : A.IsFormalAdjoint A)
      (hdense : Dense (A.domain : Set H))
      (hadd : (A + I • idP).toFun.range = ⊤)
      (hsub : (A - I • idP).toFun.range = ⊤) : IsSelfAdjoint A := by
    have hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ := by
      intro φ
      obtain ⟨ψ, hψ⟩ := LinearMap.range_eq_top.mp hadd φ
      exact ⟨⟨ψ, (Submodule.mem_inf.mp ψ.2).1⟩, hψ⟩
    have hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ := by
      intro φ
      obtain ⟨ψ, hψ⟩ := LinearMap.range_eq_top.mp hsub φ
      exact ⟨⟨ψ, (Submodule.mem_inf.mp ψ.2).1⟩, hψ⟩
    rw [LinearPMap.isSelfAdjoint_def]
    have hle : A ≤ A† := hsym.le_adjoint hdense
    apply le_antisymm _ hle
    apply LinearPMap.le_of_eqLocus_ge
    intro w hw
    let W : A†.domain := ⟨w, hw⟩
    obtain ⟨x, hx⟩ := hminus (A† W - I • (W : H))
    set X : A†.domain := ⟨x, hle.1 x.2⟩ with hX
    have hxeq : A† X = A x := (hle.2 (x := x) (y := X) rfl).symm
    have hdiff : A† (W - X) = I • ((W - X) : H) := by
      rw [LinearPMap.map_sub, hxeq, hX, Subtype.coe_mk, smul_sub,
        sub_eq_sub_iff_sub_eq_sub, hx]
    have hker : ∀ w : A†.domain, A† w = I • (w : H) → (w : H) = 0 := by
      intro w hw
      obtain ⟨v, hv⟩ := hplus (w : H)
      suffices ⟪(w : H), A v + I • (v : H)⟫_ℂ = 0 by
        exact inner_self_eq_zero.mp (hv ▸ this)
      rw [inner_add_right, inner_smul_right,
        ← LinearPMap.adjoint_isFormalAdjoint hdense w v, hw, inner_smul_left, conj_I]
      ring
    obtain rfl : w = (x : H) := sub_eq_zero.mp (hker (W - X) hdiff)
    exact ⟨hw, x.2, hxeq⟩
  have hmem : ∀ i, e i ∈ T.domain := fun i ↦ hdom ▸ Submodule.subset_span ⟨i, rfl⟩
  set v : ι → T.domain := fun i ↦ (⟨e i, hmem i⟩ : T.domain) with hv_def
  set w : ι → H := fun i ↦ (lam i : ℂ) • e i with hw_def
  -- `Finsupp.linearCombination` computes `T` on finite eigenbasis combinations.
  have hcomp : (T.domain.subtype : T.domain →ₗ[ℂ] H) ∘ v = (⇑e) := by
    funext i; simp [hv_def]
  have hcomp2 : (T.toFun : T.domain →ₗ[ℂ] H) ∘ v = w := by
    funext i; simp only [Function.comp_apply, hv_def]; exact heig i
  have hv_coe : ∀ l : ι →₀ ℂ,
      ((Finsupp.linearCombination ℂ v l : T.domain) : H) = Finsupp.linearCombination ℂ (⇑e) l := by
    intro l
    have h := Finsupp.apply_linearCombination ℂ T.domain.subtype v l
    rw [hcomp] at h
    exact h
  have hTapply : ∀ l : ι →₀ ℂ,
      T (Finsupp.linearCombination ℂ v l) = Finsupp.linearCombination ℂ w l := by
    intro l
    rw [← toFun_eq_coe]
    have h := Finsupp.apply_linearCombination ℂ T.toFun v l
    rw [hcomp2] at h
    exact h
  have hspan : ∀ x : T.domain, ∃ l : ι →₀ ℂ, Finsupp.linearCombination ℂ v l = x := by
    intro x
    have hx : (x : H) ∈ Submodule.span ℂ (Set.range e) := hdom ▸ x.2
    rw [← Finsupp.range_linearCombination] at hx
    obtain ⟨l, hl⟩ := LinearMap.mem_range.mp hx
    exact ⟨l, Subtype.ext (by rw [hv_coe, hl])⟩
  -- Symmetry: on eigenbasis combinations `⟪T x, x⟫` reduces to a manifestly real sum.
  have hsym : T.IsFormalAdjoint T := by
    rw [symm_iff T]
    intro x
    obtain ⟨l, hl⟩ := hspan x
    have hlH : (x : H) = Finsupp.linearCombination ℂ (⇑e) l := by rw [← hv_coe l, hl]
    have hTx : T x = Finsupp.linearCombination ℂ w l := hl ▸ hTapply l
    have hTx' : Finsupp.linearCombination ℂ w l
        = ∑ i ∈ l.support, (l i * (lam i : ℂ)) • e i := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [hw_def, smul_smul]
    have hlH' : Finsupp.linearCombination ℂ (⇑e) l = ∑ i ∈ l.support, l i • e i := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum]
    rw [hTx, hlH, hTx', hlH', e.orthonormal.inner_sum (fun i ↦ l i * (lam i : ℂ)) (fun i ↦ l i)
      l.support, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring
  have hdense : Dense (T.domain : Set H) := by
    rw [hdom, dense_iff_closure_eq,
      ← Submodule.topologicalClosure_coe, e.dense_span, Submodule.top_coe]
  have hle : T ≤ T† := hsym.le_adjoint hdense
  have hTclosable : T.IsClosable :=
    LinearPMap.isClosable_iff_exists_closed_extension.mpr
      ⟨T†, LinearPMap.adjoint_isClosed hdense, hle⟩
  have hadj_dense : Dense (T†.domain : Set H) := hdense.mono hle.1
  have hT_le : T ≤ T†† :=
    (LinearPMap.adjoint_isFormalAdjoint hdense).le_adjoint hadj_dense
  have hc : (T††).IsClosed := LinearPMap.adjoint_isClosed hadj_dense
  have hdouble_dense : Dense (T††.domain : Set H) := hdense.mono hT_le.1
  have hdouble_le : T†† ≤ T††† :=
    adj_antitone hdouble_dense (adj_antitone hdense hle)
  have hdouble_sym : (T††).IsFormalAdjoint T†† := by
    intro x y
    rw [hdouble_le.2 (x := x) (y := ⟨x, hdouble_le.1 x.2⟩) rfl]
    exact LinearPMap.adjoint_isFormalAdjoint hdouble_dense _ _
  have hc_eq : (T††).closure = T†† := by
    apply LinearPMap.eq_of_eq_graph
    rw [← hc.isClosable.graph_closure_eq_closure_graph, hc.submodule_topologicalClosure_eq]
  have hclosure_le : T.closure ≤ T†† := by
    simpa only [hc_eq] using hc.isClosable.closure_mono hT_le
  have hTclosure_sym : T.closure.IsFormalAdjoint T.closure := by
    intro x y
    rw [hclosure_le.2 (x := x) (y := ⟨x, hclosure_le.1 x.2⟩) rfl,
      hclosure_le.2 (x := y) (y := ⟨y, hclosure_le.1 y.2⟩) rfl]
    exact hdouble_sym ⟨x, hclosure_le.1 x.2⟩ ⟨y, hclosure_le.1 y.2⟩
  have hTclosure_dense : Dense (T.closure.domain : Set H) :=
    hdense.mono (LinearPMap.le_closure T).1
  -- For `ζ = ± I`, real eigenvalues satisfy `|lam i - ζ| ≥ 1`.
  have hbound : ∀ {ζ : ℂ}, ζ.re = 0 → normSq ζ = 1 → ∀ r : ℝ, 1 ≤ ‖(r : ℂ) - ζ‖ := by
    intro ζ hre hsq r
    have hns : (1 : ℝ) ≤ normSq ((r : ℂ) - ζ) := by
      have h1 : ((r : ℂ) - ζ).re = r := by simp [hre]
      have h2 : ((r : ℂ) - ζ).im = -ζ.im := by simp
      rw [normSq_apply, h1, h2]
      nlinarith [sq_nonneg r, normSq_apply ζ, hsq, hre]
    calc (1 : ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
      _ ≤ Real.sqrt (normSq ((r : ℂ) - ζ)) := Real.sqrt_le_sqrt hns
      _ = ‖(r : ℂ) - ζ‖ := (Complex.norm_def _).symm
  have hne : ∀ {ζ : ℂ}, ζ.re = 0 → normSq ζ = 1 → ∀ i, (lam i : ℂ) - ζ ≠ 0 := by
    intro ζ hre hsq i h
    have := hbound hre hsq (lam i)
    rw [h, norm_zero] at this
    linarith
  -- The core surjectivity fact: `(T.closure - ζ • 1).range = ⊤` for `ζ = ± I`.
  have hrange : ∀ {ζ : ℂ}, ζ.re = 0 → normSq ζ = 1 →
      (T.closure - ζ • idP).toFun.range = ⊤ := by
    intro ζ hre hsq
    rw [LinearMap.range_eq_top]
    intro y
    set c : ι → ℂ := fun i ↦ (inner (𝕜 := ℂ) (e i) y) with hc_def
    have hy_sum : HasSum (fun i ↦ c i • e i) y := by
      have h := e.hasSum_repr y
      simpa [hc_def, HilbertBasis.repr_apply_apply] using h
    have hc_summable : Summable fun i ↦ ‖c i‖ ^ 2 := e.orthonormal.inner_products_summable y
    set g : ι → ℂ := fun i ↦ c i / ((lam i : ℂ) - ζ) with hg_def
    have hg_le : ∀ i, ‖g i‖ ≤ ‖c i‖ := fun i ↦ by
      rw [hg_def, Complex.norm_div]
      exact div_le_self (norm_nonneg _) (hbound hre hsq (lam i))
    have hg_summable : Summable fun i ↦ ‖g i‖ ^ 2 :=
      Summable.of_nonneg_of_le (fun i ↦ sq_nonneg _)
        (fun i ↦ pow_le_pow_left₀ (norm_nonneg _) (hg_le i) 2) hc_summable
    have hg_mem : Memℓp g 2 := by
      apply memℓp_gen
      have hp2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
      rw [hp2]
      simpa [Real.rpow_natCast] using hg_summable
    set z : H := e.repr.symm ⟨g, hg_mem⟩ with hz_def
    have hz_sum : HasSum (fun i ↦ g i • e i) z := e.hasSum_repr_symm ⟨g, hg_mem⟩
    have hterm : ∀ i, g i * (lam i : ℂ) = c i + ζ * g i := fun i ↦ by
      have hdiv : g i * ((lam i : ℂ) - ζ) = c i := by
        rw [hg_def]; exact div_mul_cancel₀ (c i) (hne hre hsq i)
      ring_nf
      ring_nf at hdiv
      linear_combination hdiv
    -- Each single eigenbasis term already lies in `T`'s graph.
    have hmem_graph_single :
        ∀ i, ((g i • e i : H), (c i • e i + ζ • (g i • e i) : H)) ∈ T.graph := by
      intro i
      have hTvi : T (v i) = (lam i : ℂ) • e i := heig i
      have hTe : T (g i • v i) = c i • e i + ζ • (g i • e i) := by
        rw [LinearPMap.map_smul, hTvi, smul_smul, hterm i, add_smul, smul_smul]
      have hco : ((g i • v i : T.domain) : H) = g i • e i := by
        rw [SetLike.val_smul, hv_def]
      simpa [hco, hTe] using T.mem_graph (g i • v i)
    have hu := hz_sum.prodMk (hy_sum.add (hz_sum.const_smul ζ))
    have hgraph_closure : (z, y + ζ • z) ∈ T.graph.topologicalClosure := by
      rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
      refine mem_closure_of_tendsto hu (Eventually.of_forall fun s ↦ ?_)
      exact Submodule.sum_mem _ fun i _ ↦ hmem_graph_single i
    rw [hTclosable.graph_closure_eq_closure_graph] at hgraph_closure
    have hzdom : z ∈ T.closure.domain := mem_domain_of_mem_graph hgraph_closure
    have hTz : T.closure ⟨z, hzdom⟩ = y + ζ • z :=
      ((image_iff hzdom).mpr hgraph_closure).symm
    have hzdom' : z ∈ (T.closure - ζ • idP).domain := by
      rw [LinearPMap.sub_domain, LinearPMap.smul_domain, hidDom, inf_top_eq]
      exact hzdom
    refine ⟨⟨z, hzdom'⟩, ?_⟩
    show (T.closure - ζ • idP) ⟨z, hzdom'⟩ = y
    rw [LinearPMap.sub_apply, LinearPMap.smul_apply]
    have h1 : idP ⟨z, (Submodule.mem_inf.mp hzdom').2⟩ = z := rfl
    rw [h1, show T.closure ⟨z, (Submodule.mem_inf.mp hzdom').1⟩ = T.closure ⟨z, hzdom⟩ from rfl,
        hTz]
    abel
  refine ⟨hTclosable, ?_⟩
  apply range_criterion T.closure hTclosure_sym hTclosure_dense
  · have hI : T.closure + I • idP = T.closure - (-I) • idP :=
      LinearPMap.ext rfl fun x hf hg ↦ by
        simp [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply,
          sub_neg_eq_add]
    rw [hI]
    exact hrange (by simp) (by simp [normSq_apply])
  · exact hrange (by simp) (by simp [normSq_apply])

#print axioms eigenbasis_closable_selfAdjoint
end D5.S3.Quantum.Analysis.EigenbasisClosure
