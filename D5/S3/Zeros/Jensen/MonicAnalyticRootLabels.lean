/- GID: D5/S3/Zeros/Jensen/MonicAnalyticRootLabels
   generality: G
   mirror-B: D5/B/S3/Zeros/Jensen/MonicAnalyticRootLabels
   mirror-E: none(waiver:analytic-polynomial-continuation)
   anchors: [mathlib/module/Mathlib.Topology.Homotopy.Lifting]
   utility: none
   digest: Simple monic analytic families form root coverings and have global analytic labels. -/

import D5.S3.Zeros.Jensen.MonicRootProjectionProper
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Analytic.Order
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u v
open Polynomial Set Filter Topology
open scoped ContDiff Classical

namespace D5.S3.Zeros.Jensen.MonicAnalyticRootLabels

private theorem local_graph_open_embedding
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (R : X × Y → Prop) (U : Set X) (V : Set Y)
    (hU : IsOpen U) (_hV : IsOpen V) (b : X → Y)
    (hb : ContinuousOn b U) (hbV : MapsTo b U V)
    (hR : ∀ x ∈ U, ∀ y ∈ V, R (x,y) ↔ b x = y) :
    IsOpenEmbedding
      (fun e : {e : {p : X × Y // R p} | e.1.1 ∈ U ∧ e.1.2 ∈ V} => e.1.1.1) := by
  let W := {e : {p : X × Y // R p} | e.1.1 ∈ U ∧ e.1.2 ∈ V}
  let chart : W ≃ₜ U := {
    toFun := fun e => ⟨e.1.1.1,e.2.1⟩
    invFun := fun x => ⟨⟨(x.1,b x.1),(hR x.1 x.2 (b x.1) (hbV x.2)).mpr rfl⟩,
      x.2,hbV x.2⟩
    left_inv := by
      intro e
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact (hR e.1.1.1 e.2.1 e.1.1.2 e.2.2).mp e.1.2
    right_inv := by intro x; rfl
    continuous_toFun :=
      (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
    continuous_invFun :=
      ((continuous_subtype_val.prodMk hb.domRestrict).subtype_mk _).subtype_mk _ }
  exact hU.isOpenEmbedding_subtypeVal.comp chart.isOpenEmbedding

private theorem relation_projection_isLocalHomeomorph_of_local_graphs
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (R : X × Y → Prop)
    (hgraphs : ∀ e : {p : X × Y // R p},
      ∃ U : Set X, ∃ V : Set Y, ∃ b : X → Y,
        IsOpen U ∧ e.1.1 ∈ U ∧ IsOpen V ∧ e.1.2 ∈ V ∧
        ContinuousOn b U ∧ MapsTo b U V ∧
        (∀ x ∈ U, ∀ y ∈ V, R (x,y) ↔ b x = y)) :
    IsLocalHomeomorph (fun e : {p : X × Y // R p} => e.1.1) := by
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  intro e
  obtain ⟨U,V,b,hU,heU,hV,heV,hb,hbV,hR⟩ := hgraphs e
  let W := {e : {p : X × Y // R p} | e.1.1 ∈ U ∧ e.1.2 ∈ V}
  have hW : IsOpen W :=
    (hU.preimage continuous_subtype_val.fst).inter
      (hV.preimage continuous_subtype_val.snd)
  exact ⟨W,hW.mem_nhds ⟨heU,heV⟩,
    local_graph_open_embedding R U V hU hV b hb hbV hR⟩

private theorem analytic_branch_supplies_graph_chart
    (R : ℂ × ℂ → Prop) (t z : ℂ) (b : ℂ → ℂ)
    (hb : AnalyticAt ℂ b t) (hbase : b t = z)
    (hzero : ∀ᶠ v in 𝓝 t, R (v,b v))
    (hunique : ∀ᶠ p : ℂ × ℂ in 𝓝 (t,z), R p ↔ b p.1 = p.2) :
    ∃ U : Set ℂ, ∃ V : Set ℂ,
      IsOpen U ∧ t ∈ U ∧ IsOpen V ∧ z ∈ V ∧
      ContinuousOn b U ∧ MapsTo b U V ∧
      (∀ x ∈ U, ∀ y ∈ V, R (x,y) ↔ b x = y) := by
  obtain ⟨U₀,V,hU₀,htU₀,hV,hzV,hUV⟩ := mem_nhds_prod_iff'.mp hunique
  have hpre : b ⁻¹' V ∈ 𝓝 t := hb.continuousAt (hbase ▸ hV.mem_nhds hzV)
  have hgood : U₀ ∩ b ⁻¹' V ∩ {v | ContinuousAt b v} ∩ {v | R (v,b v)} ∈ 𝓝 t :=
    inter_mem (inter_mem (inter_mem (hU₀.mem_nhds htU₀) hpre)
      hb.eventually_continuousAt) hzero
  obtain ⟨U,hUgood,hU,htU⟩ := mem_nhds_iff.mp hgood
  refine ⟨U,V,hU,htU,hV,hzV,?_,?_,?_⟩
  · exact fun x hx => (hUgood hx).1.2.continuousWithinAt
  · intro x hx
    exact (hUgood hx).1.1.2
  · intro x hx y hy
    exact hUV ⟨(hUgood hx).1.1.1,hy⟩

private theorem joint_eval_analytic
    (P : ℂ → Polynomial ℂ) (Ω : Set ℂ) (q : ℕ)
    (hΩ : IsOpen Ω) (hdegree : ∀ t ∈ Ω, (P t).natDegree = q)
    (ha : ∀ i ≤ q, ∀ t ∈ Ω, AnalyticAt ℂ (fun v => (P v).coeff i) t)
    (t z : ℂ) (ht : t ∈ Ω) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => (P p.1).eval p.2) (t,z) := by
  let F : ℂ × ℂ → ℂ := fun p =>
    ∑ i ∈ Finset.range (q+1), (P p.1).coeff i * p.2^i
  have hF : AnalyticAt ℂ F (t,z) := by
    apply Finset.analyticAt_fun_sum
    intro i hi
    have hiq : i ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hc : AnalyticAt ℂ (fun p : ℂ × ℂ => (P p.1).coeff i) (t,z) := by
      simpa only [Function.comp_def] using
        (ha i hiq t ht).comp (analyticAt_fst (𝕜 := ℂ) (p := (t,z)))
    exact hc.mul ((analyticAt_snd (𝕜 := ℂ) (p := (t,z))).pow i)
  have heq : F =ᶠ[𝓝 (t,z)] fun p => (P p.1).eval p.2 := by
    filter_upwards [(hΩ.preimage continuous_fst).mem_nhds ht] with p hp
    dsimp [F]
    rw [Polynomial.eval_eq_sum_range, hdegree p.1 hp]
  exact hF.congr heq

private theorem simple_root_local_branch
    (P : ℂ → Polynomial ℂ) (t z : ℂ)
    (hG : AnalyticAt ℂ (fun p : ℂ × ℂ => (P p.1).eval p.2) (t,z))
    (hz : (P t).eval z = 0) (hs : (P t).derivative.eval z ≠ 0) :
    ∃ b : ℂ → ℂ, b t = z ∧ AnalyticAt ℂ b t ∧
      (∀ᶠ v in 𝓝 t, (P v).eval (b v) = 0) ∧
      (∀ᶠ p : ℂ × ℂ in 𝓝 (t,z), (P p.1).eval p.2 = 0 ↔ b p.1 = p.2) := by
  let G : ℂ × ℂ → ℂ := fun p => (P p.1).eval p.2
  have hright : fderiv ℂ G (t,z) ∘L ContinuousLinearMap.inr ℂ ℂ ℂ =
      ContinuousLinearMap.toSpanSingleton ℂ ((P t).derivative.eval z) := by
    have hcomposition := hG.hasStrictFDerivAt.hasFDerivAt.comp z
      (hasFDerivAt_prodMk_right (𝕜 := ℂ) t z)
    have hdirect : HasFDerivAt (fun w : ℂ => G (t,w))
        (ContinuousLinearMap.toSpanSingleton ℂ ((P t).derivative.eval z)) z :=
      (P t).hasDerivAt z |>.hasFDerivAt
    exact hcomposition.unique hdirect
  let derivativeEquiv : ℂ ≃L[ℂ] ℂ :=
    ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 ((P t).derivative.eval z) hs)
  have hinvertible : (fderiv ℂ G (t,z) ∘L
      ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
    rw [hright]
    have heq : ContinuousLinearMap.toSpanSingleton ℂ ((P t).derivative.eval z) =
        (derivativeEquiv : ℂ →L[ℂ] ℂ) := by
      ext w
      simp [derivativeEquiv, ContinuousLinearEquiv.unitsEquivAut_apply, mul_comm]
    rw [heq]
    exact ContinuousLinearMap.isInvertible_equiv
  have hGcont : ContDiffAt ℂ ω G (t,z) := hG.contDiffAt
  have homega : (ω : ℕ∞ω) ≠ 0 := by simp
  let b : ℂ → ℂ := hGcont.implicitFunction homega hinvertible
  have hbase : b t = z := by
    simpa [b] using hGcont.implicitFunction_apply_self homega hinvertible
  have hzero : ∀ᶠ v in 𝓝 t, (P v).eval (b v) = 0 := by
    simpa [b,G,hz] using hGcont.eventually_apply_implicitFunction homega hinvertible
  have hunique : ∀ᶠ p : ℂ × ℂ in 𝓝 (t,z), (P p.1).eval p.2 = 0 ↔ b p.1 = p.2 := by
    simpa [b,G,hz] using hGcont.eventually_apply_eq_iff_implicitFunction homega hinvertible
  have hb : ContDiffAt ℂ ω b t := by
    simpa [b] using hGcont.contDiffAt_implicitFunction homega hinvertible
  exact ⟨b,hbase,hb.analyticAt,hzero,hunique⟩

/-- The target is the open parameter subtype, so properness is not asserted for the ambient
complex projection. No local charts, root labels, compact base, or global root bound is assumed.
Degree zero and empty fibers are included. -/
theorem monic_analytic_simple_root_projection_isCovering
    (P : ℂ → Polynomial ℂ) (Ω : Set ℂ) (q : ℕ)
    (hΩ : IsOpen Ω) (hm : ∀ t ∈ Ω, (P t).Monic)
    (hd : ∀ t ∈ Ω, (P t).natDegree = q)
    (ha : ∀ i ≤ q, ∀ t ∈ Ω, AnalyticAt ℂ (fun v => (P v).coeff i) t)
    (hs : ∀ t ∈ Ω, ∀ z : ℂ, (P t).eval z = 0 → (P t).derivative.eval z ≠ 0) :
    IsCoveringMap (fun e : {p : Ω × ℂ // (P p.1).eval p.2 = 0} => e.1.1) := by
  let R : Ω × ℂ → Prop := fun p => (P p.1).eval p.2 = 0
  let π : {p : Ω × ℂ // R p} → Ω := fun e => e.1.1
  have hproper : IsProperMap π := by
    apply MonicRootProjectionProper.monic_fixed_degree_root_projection_isProper
      (fun t : Ω => P t) q (fun t => hm t t.2) (fun t => hd t t.2)
    intro i hi
    rw [continuous_iff_continuousAt]
    intro t
    exact (ha i hi t t.2).continuousAt.comp continuous_subtype_val.continuousAt
  have hlocal : IsLocalHomeomorph π := by
    apply relation_projection_isLocalHomeomorph_of_local_graphs R
    intro e
    obtain ⟨b,hbase,hb,hzero,hunique⟩ := simple_root_local_branch P e.1.1 e.1.2
      (joint_eval_analytic P Ω q hΩ hd ha e.1.1 e.1.2 e.1.1.2)
      e.2 (hs e.1.1 e.1.1.2 e.1.2 e.2)
    obtain ⟨U,V,hU,htU,hV,hzV,hcont,hmap,hR⟩ :=
      analytic_branch_supplies_graph_chart (fun p => (P p.1).eval p.2 = 0)
        e.1.1 e.1.2 b hb hbase hzero hunique
    refine ⟨Subtype.val ⁻¹' U,V,fun t : Ω => b t,
      hU.preimage continuous_subtype_val,htU,hV,hzV,?_,?_,?_⟩
    · exact hcont.comp continuous_subtype_val.continuousOn (fun _ hx => hx)
    · intro t ht
      exact hmap ht
    · intro t ht z hz
      exact hR t ht z hz
  have hfinite : ∀ t : Ω, (π ⁻¹' {t}).Finite := by
    intro t
    have hroots : Set.Finite {z : ℂ | (P t).eval z = 0} :=
      Polynomial.finite_setOfPred_isRoot (hm t t.2).ne_zero
    apply Set.Finite.of_finite_image (f := fun e : {p : Ω × ℂ // R p} => e.1.2)
    · exact hroots.subset (by
        rintro z ⟨e, he, rfl⟩
        have ht : e.1.1 = t := he
        simpa [R, ht] using e.2)
    · intro e he e' he' hz
      apply Subtype.ext
      apply Prod.ext
      · exact (show e.1.1 = t from he).trans (show e'.1.1 = t from he').symm
      · exact hz
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  exact hproper.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
    (fun t _ => hfinite t) (by simpa using hlocal.isLocalHomeomorphOn)

private theorem continuous_section_analytic
    (P : ℂ → Polynomial ℂ) (Ω : Set ℂ) (q : ℕ)
    (hΩ : IsOpen Ω) (hd : ∀ t ∈ Ω, (P t).natDegree = q)
    (ha : ∀ i ≤ q, ∀ t ∈ Ω, AnalyticAt ℂ (fun v => (P v).coeff i) t)
    (hs : ∀ t ∈ Ω, ∀ z : ℂ, (P t).eval z = 0 → (P t).derivative.eval z ≠ 0)
    (F : C(Ω, {p : Ω × ℂ // (P p.1).eval p.2 = 0}))
    (hF : ∀ t : Ω, (F t).1.1 = t) :
    ∀ t ∈ Ω, AnalyticAt ℂ
      (fun v => if hv : v ∈ Ω then (F ⟨v, hv⟩).1.2 else 0) t := by
  classical
  let g : ℂ → ℂ := fun v => if hv : v ∈ Ω then (F ⟨v, hv⟩).1.2 else 0
  have hg : ContinuousOn g Ω := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (continuous_snd.comp (continuous_subtype_val.comp F.continuous)).congr
      (fun t => by simp [g, t.2])
  have hroot (t : ℂ) (ht : t ∈ Ω) : (P t).eval (g t) = 0 := by
    have hz := (F ⟨t, ht⟩).2
    simpa [g, ht, hF ⟨t, ht⟩] using hz
  intro t ht
  obtain ⟨b, hbase, hb, hzero, hunique⟩ := simple_root_local_branch P t (g t)
    (joint_eval_analytic P Ω q hΩ hd ha t (g t) ht)
    (hroot t ht) (hs t ht (g t) (hroot t ht))
  have hpair : Tendsto (fun v => (v, g v)) (𝓝 t) (𝓝 (t, g t)) :=
    tendsto_id.prodMk_nhds ((hg t ht).continuousAt (hΩ.mem_nhds ht))
  apply hb.congr
  filter_upwards [hpair.eventually hunique, hΩ.mem_nhds ht] with v hv hvΩ
  exact hv.mp (hroot v hvΩ)

/-- A nonempty simply connected open parameter domain has exactly `q` compatible analytic
root labels. Each fiber is exhausted once; a label is unique on the domain after its base value
is fixed. Ambient values outside the domain are immaterial, including in degree zero. -/
theorem monic_analytic_simple_roots_have_global_labels
    (P : ℂ → Polynomial ℂ) (Ω : Set ℂ) (q : ℕ)
    [SimplyConnectedSpace Ω]
    (hΩ : IsOpen Ω) (hm : ∀ t ∈ Ω, (P t).Monic)
    (hd : ∀ t ∈ Ω, (P t).natDegree = q)
    (ha : ∀ i ≤ q, ∀ t ∈ Ω, AnalyticAt ℂ (fun v => (P v).coeff i) t)
    (hs : ∀ t ∈ Ω, ∀ z : ℂ, (P t).eval z = 0 → (P t).derivative.eval z ≠ 0)
    (t₀ : Ω) :
    ∃ b : Fin q → ℂ → ℂ,
      (∀ i, ∀ t ∈ Ω, AnalyticAt ℂ (b i) t) ∧
      (∀ t ∈ Ω, ∀ z : ℂ, (P t).eval z = 0 ↔ ∃! i, b i t = z) ∧
      (∀ i, ∀ c : ℂ → ℂ,
        (∀ t ∈ Ω, AnalyticAt ℂ c t) →
        (∀ t ∈ Ω, (P t).eval (c t) = 0) → c t₀ = b i t₀ →
        ∀ t ∈ Ω, c t = b i t) := by
  classical
  letI : LocallyPathConnectedSpace Ω := hΩ.locallyPathConnectedSpace
  let E := {p : Ω × ℂ // (P p.1).eval p.2 = 0}
  let π : E → Ω := fun e => e.1.1
  have hcover : IsCoveringMap π :=
    monic_analytic_simple_root_projection_isCovering P Ω q hΩ hm hd ha hs
  let B := (P t₀).rootSet ℂ
  have hB (β : B) : (P t₀).eval β.1 = 0 := by
    simpa using (hm t₀ t₀.2).mem_rootSet.mp β.2
  let seed : B → E := fun β => ⟨(t₀, β.1), hB β⟩
  let F : B → C(Ω, E) := fun β =>
    Classical.choose (hcover.existsUnique_continuousMap_lifts
      (ContinuousMap.id Ω) t₀ (seed β) rfl).exists
  have hF (β : B) : F β t₀ = seed β ∧ π ∘ F β = ContinuousMap.id Ω :=
    Classical.choose_spec (hcover.existsUnique_continuousMap_lifts
      (ContinuousMap.id Ω) t₀ (seed β) rfl).exists
  have hπ (β : B) (t : Ω) : (F β t).1.1 = t := congrFun (hF β).2 t
  let g : B → ℂ → ℂ := fun β v => if hv : v ∈ Ω then (F β ⟨v, hv⟩).1.2 else 0
  have hg (β : B) (t : Ω) : g β t = (F β t).1.2 := by simp [g, t.2]
  have hroot (β : B) (t : Ω) : (P t).eval (g β t) = 0 := by
    simpa [← hg β t, hπ β t] using (F β t).2
  have hinj (t : Ω) : Function.Injective (fun β : B => g β t) := by
    intro β γ heq
    have hpoint : F β t = F γ t := by
      apply Subtype.ext
      apply Prod.ext
      · exact (hπ β t).trans (hπ γ t).symm
      · simpa only [hg] using heq
    have hsections : (F β : Ω → E) = F γ := hcover.eq_of_comp_eq
      (F β).continuous (F γ).continuous ((hF β).2.trans (hF γ).2.symm) t hpoint
    apply Subtype.ext
    have hv := congrArg (fun e : E => e.1.2) (congrFun hsections t₀)
    simpa only [(hF β).1, (hF γ).1] using hv
  have honto (t : Ω) (z : ℂ) (hz : (P t).eval z = 0) : ∃ β : B, g β t = z := by
    let e : E := ⟨(t, z), hz⟩
    obtain ⟨S, hS, _⟩ := hcover.existsUnique_continuousMap_lifts
      (ContinuousMap.id Ω) t e rfl
    have hSπ (v : Ω) : (S v).1.1 = v := congrFun hS.2 v
    let β : B := ⟨(S t₀).1.2, (hm t₀ t₀.2).mem_rootSet.mpr (by
      simpa [hSπ t₀] using (S t₀).2)⟩
    have hbase : F β t₀ = S t₀ := by
      rw [(hF β).1]
      apply Subtype.ext
      apply Prod.ext
      · exact (hSπ t₀).symm
      · rfl
    have hsections : (F β : Ω → E) = S := hcover.eq_of_comp_eq
      (F β).continuous S.continuous ((hF β).2.trans hS.2.symm) t₀ hbase
    refine ⟨β, ?_⟩
    rw [hg, congrFun hsections t, hS.1]
  have hnodup : (P t₀).roots.Nodup := by
    apply Multiset.nodup_iff_count_le_one.mpr
    intro z
    rw [Polynomial.count_roots]
    by_contra h
    have hz := (Polynomial.one_lt_rootMultiplicity_iff_isRoot (hm t₀ t₀.2).ne_zero).mp
      (Nat.lt_of_not_ge h)
    exact hs t₀ t₀.2 z hz.1 hz.2
  have hcard : Fintype.card B = q := by
    have hsep := (Polynomial.nodup_roots_iff_of_splits (hm t₀ t₀.2).ne_zero
      (IsAlgClosed.splits (P t₀))).mp hnodup
    have hsplit : ((P t₀).map (algebraMap ℂ ℂ)).Splits := IsAlgClosed.splits _
    exact (Polynomial.card_rootSet_eq_natDegree hsep hsplit).trans (hd t₀ t₀.2)
  let idx : Fin q ≃ B := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => g (idx i), ?_, ?_, ?_⟩
  · intro i
    exact continuous_section_analytic P Ω q hΩ hd ha hs (F (idx i)) (hπ (idx i))
  · intro t ht z
    constructor
    · intro hz
      obtain ⟨β, hβ⟩ := honto ⟨t, ht⟩ z hz
      refine ⟨idx.symm β, ?_, ?_⟩
      · simpa using hβ
      · intro i hi
        apply idx.injective
        apply hinj ⟨t, ht⟩
        simpa using hi.trans hβ.symm
    · rintro ⟨i, hi, _⟩
      rw [← hi]
      exact hroot (idx i) ⟨t, ht⟩
  · intro i c hc hcz hcbase t ht
    let S : C(Ω, E) := {
      toFun := fun v => ⟨(v, c v), hcz v v.2⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_id.prodMk
          ((continuousOn_iff_continuous_domRestrict.mp
            (fun v hv => (hc v hv).continuousAt.continuousWithinAt))) }
    have hSπ : π ∘ S = ContinuousMap.id Ω := rfl
    have hbase : F (idx i) t₀ = S t₀ := by
      apply Subtype.ext
      apply Prod.ext
      · exact hπ (idx i) t₀
      · change (F (idx i) t₀).1.2 = c t₀
        rw [← hg (idx i) t₀, hcbase]
    have hsections : (F (idx i) : Ω → E) = S := hcover.eq_of_comp_eq
      (F (idx i)).continuous S.continuous ((hF (idx i)).2.trans hSπ.symm) t₀ hbase
    have hval := congrArg (fun e : E => e.1.2)
      (congrFun hsections ⟨t, ht⟩)
    change c t = g (idx i) t
    exact hval.symm.trans (hg (idx i) ⟨t, ht⟩).symm

#print axioms monic_analytic_simple_root_projection_isCovering
#print axioms monic_analytic_simple_roots_have_global_labels

end D5.S3.Zeros.Jensen.MonicAnalyticRootLabels

