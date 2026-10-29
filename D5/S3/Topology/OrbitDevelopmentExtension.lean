/- GID: D5/S3/Topology/OrbitDevelopmentExtension
   generality: G
   mirror-B: D5/B/S3/Topology/OrbitDevelopmentExtension
   mirror-E: none(waiver:original-orbit-development-extension)
   anchors: [mathlib/module/Mathlib.Topology.MetricSpace.Infsep, mathlib/module/Mathlib.Topology.MetricSpace.HausdorffDistance]
   utility: none
   digest: Compatible local placements around a finite actual orbit extend to a total relation-invariant map. -/

import D5.S3.Topology.ChainLocalDevelopment
import Mathlib.Topology.MetricSpace.Infsep
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! All source distances and relations are those of the original datum G. -/

set_option autoImplicit false
noncomputable section
open Set
open scoped ENNReal NNReal

namespace D5.S3.Topology.OrbitDevelopmentExtension

universe u v w z
variable {I : Type u} {J : Type v} {X : I → Type w}
variable [∀ i, EMetricSpace (X i)]
variable (G : FiniteOrbitChainMetric.Datum I J X) (a : Sigma X)

/-- Each center is an actual point of the complete original orbit in its source. -/
abbrev Center (i : I) := {c : X i // G.Rel a ⟨i,c⟩}

/-- The union of source balls; no metric is imposed on the tagged union. -/
def Nearby (t : ℝ≥0∞) (b : Sigma X) : Prop :=
  ∃ c : Center G a b.1, edist c.val b.2 < t

/-- Transport a center through an original forward generator. -/
def forwardCenter (j : J) (c : Center G a (G.src j)) (hc : c.val ∈ G.dom j) :
    Center G a (G.dst j) :=
  ⟨(G.iso j ⟨c.val,hc⟩).val,
    Relation.EqvGen.trans _ _ _ c.property
      (Relation.EqvGen.rel _ _ ⟨j,⟨c.val,hc⟩,rfl,rfl⟩)⟩

/-- Transport a center through an original inverse generator. -/
def backwardCenter (j : J) (c : Center G a (G.dst j)) (hc : c.val ∈ G.ran j) :
    Center G a (G.src j) := by
  refine ⟨((G.iso j).symm ⟨c.val,hc⟩).val, ?_⟩
  apply Relation.EqvGen.trans _ _ _ c.property
  apply Relation.EqvGen.symm
  apply Relation.EqvGen.rel
  refine ⟨j,(G.iso j).symm ⟨c.val,hc⟩,rfl,?_⟩
  simp

/- Compact-closed separation and finite-set separation are reused here. Only
the finite actual orbit and J are enumerated; I itself need not be finite. -/
private theorem guarded_separated_radius [Fintype J]
    (hf : Set.Finite {b : Sigma X | G.Rel a b})
    (R : ℝ≥0) (hR : 0 < R) :
    ∃ r : ℝ≥0, 0 < r ∧ (r : ℝ≥0∞)+r+r < R ∧
      (∀ j (c : Center G a (G.src j)) (x : G.dom j),
        edist c.val x.val < (r : ℝ≥0∞)+r+r → c.val ∈ G.dom j) ∧
      (∀ j (c : Center G a (G.dst j)) (x : G.ran j),
        edist c.val x.val < (r : ℝ≥0∞)+r+r → c.val ∈ G.ran j) ∧
      (∀ i (c d : Center G a i) (x : X i),
        edist c.val x < (r : ℝ≥0∞)+r+r →
        edist d.val x < (r : ℝ≥0∞)+r+r → c = d) := by
  classical
  let C := {b : Sigma X // G.Rel a b}
  letI : Fintype C := hf.fintype
  have fiber_finite (i : I) : Set.Finite {c : X i | G.Rel a ⟨i,c⟩} :=
    FiniteOrbitChainMetric.Datum.finite_fiber G a hf i
  have fsep (j : J) : ∃ s : ℝ≥0, 0 < s ∧
      ∀ c : Center G a (G.src j), c.val ∉ G.dom j →
      ∀ x : G.dom j, (s : ℝ≥0∞) < edist c.val x.val := by
    have hfin : Set.Finite
        ({c : X (G.src j) | G.Rel a ⟨G.src j,c⟩} \ G.dom j) :=
      (fiber_finite (G.src j)).subset Set.sdiff_subset
    obtain ⟨s,hs,hsep⟩ := Metric.exists_pos_forall_lt_edist
      hfin.isCompact (G.closed_dom j) Set.disjoint_sdiff_left
    exact ⟨s,hs,fun c hc x => hsep c.val ⟨c.property,hc⟩ x.val x.property⟩
  have bsep (j : J) : ∃ s : ℝ≥0, 0 < s ∧
      ∀ c : Center G a (G.dst j), c.val ∉ G.ran j →
      ∀ x : G.ran j, (s : ℝ≥0∞) < edist c.val x.val := by
    have hfin : Set.Finite
        ({c : X (G.dst j) | G.Rel a ⟨G.dst j,c⟩} \ G.ran j) :=
      (fiber_finite (G.dst j)).subset Set.sdiff_subset
    obtain ⟨s,hs,hsep⟩ := Metric.exists_pos_forall_lt_edist
      hfin.isCompact (G.closed_ran j) Set.disjoint_sdiff_left
    exact ⟨s,hs,fun c hc x => hsep c.val ⟨c.property,hc⟩ x.val x.property⟩
  choose sF hsF hF using fsep
  choose sB hsB hB using bsep
  let sep : C → ℝ≥0∞ := fun c =>
    {d : X c.val.1 | G.Rel a ⟨c.val.1,d⟩}.einfsep
  have hsep (c : C) : 0 < sep c := (fiber_finite c.val.1).einfsep_pos
  let δ : ℝ≥0∞ := min (R : ℝ≥0∞)
    (min (Finset.univ.inf sep)
      (Finset.univ.inf fun j => min (sF j : ℝ≥0∞) (sB j : ℝ≥0∞)))
  have hδ : 0 < δ := by
    apply lt_min (ENNReal.coe_pos.mpr hR)
    apply lt_min
    · apply (Finset.lt_inf_iff (by simp)).mpr
      intro c _
      exact hsep c
    · apply (Finset.lt_inf_iff (by simp)).mpr
      intro j _
      exact lt_min (ENNReal.coe_pos.mpr (hsF j)) (ENNReal.coe_pos.mpr (hsB j))
  have δR : δ ≤ R := min_le_left _ _
  have δS (c : C) : δ ≤ sep c :=
    (min_le_right _ _).trans ((min_le_left _ _).trans
      (Finset.inf_le (Finset.mem_univ c)))
  have δF (j : J) : δ ≤ (sF j : ℝ≥0∞) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((Finset.inf_le (Finset.mem_univ j)).trans (min_le_left _ _)))
  have δB (j : J) : δ ≤ (sB j : ℝ≥0∞) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((Finset.inf_le (Finset.mem_univ j)).trans (min_le_right _ _)))
  obtain ⟨s,hs,hsδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hδ
  have hspos : 0 < s := ENNReal.coe_pos.mp hs
  let r : ℝ≥0 := s / 8
  have hr : 0 < r := by dsimp [r]; positivity
  have hscale : r * 8 = s := by
    dsimp [r]
    exact div_mul_cancel₀ _ (by norm_num)
  have h3 : r+r+r < s := by linarith
  have h6 : (r+r+r)+(r+r+r) < s := by linarith
  have h3δ : (r : ℝ≥0∞)+r+r < δ := by
    exact (by simpa only [ENNReal.coe_add] using ENNReal.coe_lt_coe.mpr h3).trans hsδ
  have h6δ : ((r : ℝ≥0∞)+r+r)+((r : ℝ≥0∞)+r+r) < δ := by
    exact (by simpa only [ENNReal.coe_add] using ENNReal.coe_lt_coe.mpr h6).trans hsδ
  refine ⟨r,hr,h3δ.trans_le δR,?_,?_,?_⟩
  · intro j c x hx
    by_contra hn
    exact (not_lt_of_ge (δF j)) ((hF j c hn x).trans (hx.trans h3δ))
  · intro j c x hx
    by_contra hn
    exact (not_lt_of_ge (δB j)) ((hB j c hn x).trans (hx.trans h3δ))
  · intro i c d x hc hd
    apply Subtype.ext
    by_contra hne
    have hcd : edist c.val d.val < δ := by
      apply (edist_triangle c.val x d.val).trans_lt
      exact (ENNReal.add_lt_add hc (by simpa only [edist_comm] using hd)).trans h6δ
    let c' : C := ⟨⟨i,c.val⟩,c.property⟩
    have hlow : δ ≤ edist c.val d.val :=
      (δS c').trans (Set.einfsep_le_edist_of_mem c.property d.property hne)
    exact (not_lt_of_ge hlow) hcd

/- The same ball union is transported in both directions by each actual
generator. The inverse implication is needed for the exterior value of F. -/
private theorem nearby_generator_iff (t : ℝ≥0∞)
    (hF : ∀ j (c : Center G a (G.src j)) (x : G.dom j),
      edist c.val x.val < t → c.val ∈ G.dom j)
    (hB : ∀ j (c : Center G a (G.dst j)) (x : G.ran j),
      edist c.val x.val < t → c.val ∈ G.ran j)
    (j : J) (x : G.dom j) :
    Nearby G a t ⟨G.src j,x.val⟩ ↔
      Nearby G a t ⟨G.dst j,(G.iso j x).val⟩ := by
  have forward_near : Nearby G a t ⟨G.src j,x.val⟩ →
      Nearby G a t ⟨G.dst j,(G.iso j x).val⟩ := by
    rintro ⟨c,hc⟩
    let hcdom := hF j c x hc
    refine ⟨forwardCenter G a j c hcdom, ?_⟩
    change edist (G.iso j ⟨c.val,hcdom⟩) (G.iso j x) < t
    rw [(G.iso j).isometry.edist_eq]
    exact hc
  have backward_near (y : G.ran j) : Nearby G a t ⟨G.dst j,y.val⟩ →
      Nearby G a t ⟨G.src j,((G.iso j).symm y).val⟩ := by
    rintro ⟨c,hc⟩
    let hcran := hB j c y hc
    refine ⟨backwardCenter G a j c hcran, ?_⟩
    change edist ((G.iso j).symm ⟨c.val,hcran⟩) ((G.iso j).symm y) < t
    rw [(G.iso j).symm.isometry.edist_eq]
    exact hc
  refine ⟨forward_near, ?_⟩
  intro h
  simpa using backward_near (G.iso j x) h

/-- Compatible local isometries around a finite complete original orbit have a
total extension constant on the entire original relation. Its local values
bound the infimum over the literal original finite chains. -/
theorem exists_saturated_extension [Fintype J]
    (hf : Set.Finite {b : Sigma X | G.Rel a b})
    {Y : Type z} [EMetricSpace Y] (o : Y)
    (D : ∀ i, Center G a i → X i → Y)
    (R : ℝ≥0) (hR : 0 < R)
    (hcenter : ∀ i (c : Center G a i), D i c c.val = o)
    (hiso : ∀ i (c : Center G a i) (x y : X i),
      edist c.val x < (R : ℝ≥0∞) → edist c.val y < (R : ℝ≥0∞) →
      edist (D i c x) (D i c y) = edist x y)
    (hcompat : ∀ j (c : Center G a (G.src j)) (hc : c.val ∈ G.dom j)
      (x : G.dom j), edist c.val x.val < (R : ℝ≥0∞) →
      D (G.src j) c x.val =
        D (G.dst j) (forwardCenter G a j c hc) (G.iso j x).val) :
    ∃ r : ℝ≥0, 0 < r ∧ (r : ℝ≥0∞)+r+r < R ∧
      ∃ F : Sigma X → Y,
        (∀ b c, G.Rel b c → F b = F c) ∧
        (∀ i (c : Center G a i) (x : X i),
          edist c.val x < (r : ℝ≥0∞)+r+r → F ⟨i,x⟩ = D i c x) ∧
        (∀ b, ¬ Nearby G a ((r : ℝ≥0∞)+r+r) b → F b = o) ∧
        F a = o ∧
        (∀ b c, G.Rel b c →
          (Nearby G a ((r : ℝ≥0∞)+r+r) b ↔ Nearby G a ((r : ℝ≥0∞)+r+r) c)) ∧
        (∀ (x y : Sigma X) (cx : Center G a x.1) (cy : Center G a y.1),
          edist cx.val x.2 < (r : ℝ≥0∞) → edist cy.val y.2 < (r : ℝ≥0∞) →
          edist (D x.1 cx x.2) (D y.1 cy y.2) ≤ G.distance x y) := by
  classical
  obtain ⟨r,hr,h3R,hF,hB,hunique⟩ := guarded_separated_radius G a hf R hR
  let t : ℝ≥0∞ := (r : ℝ≥0∞)+r+r
  have htpos : 0 < t :=
    (ENNReal.coe_pos.mpr hr).trans_le (le_self_add.trans le_self_add)
  have step_near (j : J) (x : G.dom j) :
      Nearby G a t ⟨G.src j,x.val⟩ ↔
        Nearby G a t ⟨G.dst j,(G.iso j x).val⟩ :=
    nearby_generator_iff G a t hF hB j x
  have saturated (b c : Sigma X) (h : G.Rel b c) :
      Nearby G a t b ↔ Nearby G a t c := by
    induction h with
    | rel b c h =>
        rcases h with ⟨j,x,rfl,rfl⟩
        exact step_near j x
    | refl b => exact Iff.rfl
    | symm b c h ih => exact ih.symm
    | trans b c d hbc hcd ihbc ihcd => exact ihbc.trans ihcd
  let F : Sigma X → Y := fun b =>
    if h : Nearby G a t b then D b.1 (Classical.choose h) b.2 else o
  have agree (i : I) (c : Center G a i) (x : X i) (hx : edist c.val x < t) :
      F ⟨i,x⟩ = D i c x := by
    have hn : Nearby G a t ⟨i,x⟩ := ⟨c,hx⟩
    change (if h : Nearby G a t ⟨i,x⟩ then D i (Classical.choose h) x else o) = _
    rw [dif_pos hn]
    have heq : Classical.choose hn = c :=
      hunique i (Classical.choose hn) c x (Classical.choose_spec hn) hx
    rw [heq]
  have outside (b : Sigma X) (hb : ¬ Nearby G a t b) : F b = o := by
    dsimp [F]
    rw [dif_neg hb]
  have step_equal (j : J) (x : G.dom j) :
      F ⟨G.src j,x.val⟩ = F ⟨G.dst j,(G.iso j x).val⟩ := by
    by_cases hn : Nearby G a t ⟨G.src j,x.val⟩
    · obtain ⟨c,hc⟩ := hn
      let hcdom := hF j c x hc
      have hnear : edist (forwardCenter G a j c hcdom).val (G.iso j x).val < t := by
        change edist (G.iso j ⟨c.val,hcdom⟩) (G.iso j x) < t
        rw [(G.iso j).isometry.edist_eq]
        exact hc
      rw [agree (G.src j) c x.val hc,
        agree (G.dst j) (forwardCenter G a j c hcdom) (G.iso j x).val hnear]
      exact hcompat j c hcdom x (hc.trans h3R)
    · have hm : ¬ Nearby G a t ⟨G.dst j,(G.iso j x).val⟩ :=
        fun hm => hn ((step_near j x).mpr hm)
      rw [outside _ hn, outside _ hm]
  have desc (b c : Sigma X) (h : G.Rel b c) : F b = F c := by
    induction h with
    | rel b c h =>
        rcases h with ⟨j,x,rfl,rfl⟩
        exact step_equal j x
    | refl b => rfl
    | symm b c h ih => exact ih.symm
    | trans b c d hbc hcd ihbc ihcd => exact ihbc.trans ihcd
  have short (i : I) (c : X i) (hc : G.Rel a ⟨i,c⟩) (x y : X i)
      (hx : edist c x < t) (hy : edist c y < t) :
      edist (F ⟨i,x⟩) (F ⟨i,y⟩) ≤ edist x y := by
    let c' : Center G a i := ⟨c,hc⟩
    rw [agree i c' x hx, agree i c' y hy]
    exact (hiso i c' x y (hx.trans h3R) (hy.trans h3R)).le
  have origin : F a = o := by
    let ca : Center G a a.1 := ⟨a.2,Relation.EqvGen.refl a⟩
    exact (agree a.1 ca a.2 (by simpa using htpos)).trans (hcenter a.1 ca)
  refine ⟨r,hr,h3R,F,desc,agree,outside,origin,saturated,?_⟩
  intro x y cx cy hx hy
  have hrle : (r : ℝ≥0∞) ≤ t := le_self_add.trans le_self_add
  rw [← agree x.1 cx x.2 (hx.trans_le hrle),
    ← agree y.1 cy y.2 (hy.trans_le hrle)]
  exact ChainLocalDevelopment.local_development_distance_le G a F desc r hr short
    (fun j c hc x h => hF j ⟨c,hc⟩ x h)
    (fun j c hc x h => hB j ⟨c,hc⟩ x h)
    x y cx.val cy.val cx.property cy.property hx hy

#print axioms exists_saturated_extension
end D5.S3.Topology.OrbitDevelopmentExtension
