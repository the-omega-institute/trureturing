/- GID: D5/S3/Topology/StableCategory/GraphCarrierContiguity
   generality: G
   mirror-B: none(waiver:support-for-the-tetrahedral-refinement)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Carrier preserving graph maps admit a relative edgewise comparison. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Topology.IntervalSubdivisionCoordinates
import D5.S3.Topology.StableCategory.OrdinaryContiguityLift
import D5.S3.Topology.RelativeIntervalChartGluing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.StableCategory.GraphCarrierContiguity

open BarycentricGraphDistance (Face Vertex oneSkeleton)
open BarycentricNeighborhoodIteration (iteratedAmbient iteratedSubcomplex)
open BarycentricBaseRigidity (Contiguous faceImage retainedVertex)
open D5.S3.Geometry.FiniteAlexanderDualCollapse (simplex)
open GraphSubdivisionIntervals (originalSupport originalSupport_mem
  mem_iteratedSubcomplex_iff graph_subdivision_intervals_oriented)
open IntervalSubdivisionCoordinates (iterate_face iterate_eq_chart_index)
open OrdinaryContiguityLift (Simplicial)
open PathContiguity (intervalComplex IsIntervalMap)
open Relation (ReflTransGen)
open private simplex_le iterated_le_ambient iterated_point_face mem_faceImage_iff
  from D5.S3.Topology.GraphSubdivisionIntervals

noncomputable section

local instance (priority := 2000) (X : Type*) : DecidableEq X := Classical.decEq X

variable {X : Type}

private theorem support_mono (A : PreAbstractSimplicialComplex X) (m : ℕ)
    {s t : Finset (iteratedAmbient A m).1} (h : s ⊆ t) :
    originalSupport A m s ⊆ originalSupport A m t := by
  induction m with
  | zero => exact h
  | succ m ih => exact ih (Finset.biUnion_subset_biUnion_of_subset_left Subtype.val h)

/-- Two maps between ordinary subdivisions of a bipartite graph are
contiguously homotopic if both keep every vertex inside its original carrier.
The interval comparisons fix the vertices supported at a single old vertex. -/
theorem supported_maps_contiguous (A : PreAbstractSimplicialComplex X)
    (hdim : ∀ s ∈ A, (s : Finset X).card ≤ 2) (q : X → ℕ)
    (hq : ∀ s ∈ A, s.image q ∈ intervalComplex 1)
    (left right : {e : Face A // e.val.val.card = 2} → Vertex A)
    (horient : ∀ e, e.val.val = {(left e).val, (right e).val} ∧
      left e ≠ right e ∧ q (left e).val = 0 ∧ q (right e).val = 1)
    (n m : ℕ) [Finite (Vertex (iteratedAmbient A n).2)]
    (f g : Vertex (iteratedAmbient A n).2 → Vertex (iteratedAmbient A m).2)
    (hf : Simplicial f) (hg : Simplicial g)
    (hfSupp : ∀ u, originalSupport A m {(f u).val} ⊆ originalSupport A n {u.val})
    (hgSupp : ∀ u, originalSupport A m {(g u).val} ⊆ originalSupport A n {u.val}) :
    ReflTransGen Contiguous f g := by
  let E := {e : Face A // e.val.val.card = 2}
  let P := (iteratedAmbient A n).2
  let B := (iteratedAmbient A m).2
  let N := 2 ^ m
  let I := Vertex (intervalComplex N)
  let coord := IntervalSubdivisionCoordinates.iterate (K := A) q m
  obtain ⟨chart, hinj, hend, hcharts, _, _⟩ :=
    graph_subdivision_intervals_oriented A hdim m left right
      (fun e => ⟨(horient e).1, (horient e).2.1⟩)
  have coord_face (s : Finset _) (hs : s ∈ B) :
      s.image coord ∈ intervalComplex N := by
    simpa only [Nat.mul_one] using iterate_face q hq m s hs
  have index (v : Vertex B) : coord v.val ≤ N := by
    have hv := coord_face {v.val} v.property
    rw [Finset.image_singleton] at hv
    exact hv.2.1 _ (Finset.mem_singleton_self _)
  let label (v : Vertex B) : I := ⟨coord v.val, Finset.singleton_nonempty _,
    fun k hk => (Finset.mem_singleton.mp hk).symm ▸ index v, fun a ha b hb => by
      rw [Finset.mem_singleton.mp ha, Finset.mem_singleton.mp hb]
      exact Nat.le_succ _⟩
  have coord_chart (e : E) (i : I) : coord (chart e i).val = i.val := by
    have hinjQ : Set.InjOn q {x | ({x} : Finset X) ∈ simplex e.val.val} := by
      intro x hx y hy he
      have hx' : x ∈ e.val.val := hx.2 (Finset.mem_singleton_self _)
      have hy' : y ∈ e.val.val := hy.2 (Finset.mem_singleton_self _)
      rw [(horient e).1] at hx' hy'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx' hy'
      rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
      · rfl
      · exact (Nat.zero_ne_one ((horient e).2.2.1.symm.trans
          (he.trans (horient e).2.2.2))).elim
      · exact (Nat.one_ne_zero ((horient e).2.2.2.symm.trans
          (he.trans (horient e).2.2.1))).elim
      · rfl
    exact iterate_eq_chart_index (simplex_le e.val.property) q hq hinjQ m (chart e) (hinj e)
      (fun s hs => (hcharts e _).2 ⟨s, hs, rfl⟩) (left e) (horient e).2.2.1
      (fun j hj => (hend e j).1 hj) i
  have chart_at (e : E) (v : Vertex B)
      (hv : originalSupport A m {v.val} ⊆ e.val.val) : chart e (label v) = v := by
    have hs := originalSupport_mem m v.property
    have he := (mem_iteratedSubcomplex_iff (B := simplex e.val.val) m v.property).2
      ⟨(A.isRelLowerSet_faces hs).1, hv⟩
    obtain ⟨t, ht, h⟩ := (hcharts e _).1 he
    have hmem : v.val ∈ faceImage (chart e) ht := h.symm ▸ Finset.mem_singleton_self _
    obtain ⟨i, _, hi⟩ := (mem_faceImage_iff (chart e) ht _).mp hmem
    have hEq : label v = i := Subtype.ext (by simpa only [hi] using coord_chart e i)
    exact hEq ▸ Subtype.ext hi
  have fixed (u : Vertex P) (x : Vertex A) (h : originalSupport A n {u.val} ⊆ {x.val}) :
      f u = retainedVertex m x ∧ g u = retainedVertex m x := by
    have onPoint (v : Vertex B) (hv : originalSupport A m {v.val} ⊆ {x.val}) :
        v = retainedVertex m x := by
      have hs := originalSupport_mem m v.property
      have he := (mem_iteratedSubcomplex_iff (B := simplex {x.val}) m v.property).2
        ⟨(A.isRelLowerSet_faces hs).1, hv⟩
      exact Subtype.ext (Finset.singleton_injective (iterated_point_face m x he))
    exact ⟨onPoint _ ((hfSupp u).trans h), onPoint _ ((hgSupp u).trans h)⟩
  let S : Set (Vertex P) := {u | (originalSupport A n {u.val}).card ≠ 2}
  have fixed_on (u : Vertex P) (h : u ∈ S) : f u = g u := by
    have hs := originalSupport_mem n u.property
    have hp := Finset.card_pos.mpr (A.isRelLowerSet_faces hs).1
    have h1 : (originalSupport A n {u.val}).card = 1 := by
      change _ ≠ 2 at h
      have hb := hdim _ hs
      exact Nat.le_antisymm (Nat.lt_succ_iff.mp (lt_of_le_of_ne hb h)) hp
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
    have h := fixed u ⟨x, hx ▸ hs⟩ hx.le
    exact h.1.trans h.2.symm
  let edgeOf (u : Vertex P) (h : (originalSupport A n {u.val}).card = 2) : E :=
    ⟨⟨originalSupport A n {u.val}, originalSupport_mem n u.property⟩, h⟩
  let place (u : Vertex P) (i : I) :=
    if h : (originalSupport A n {u.val}).card = 2 then chart (edgeOf u h) i else f u
  have realizes (j : Vertex P → Vertex B)
      (hj : ∀ u, originalSupport A m {(j u).val} ⊆ originalSupport A n {u.val})
      (hfix : Set.EqOn j f S) (u : Vertex P) : place u (label (j u)) = j u := by
    by_cases h : (originalSupport A n {u.val}).card = 2
    · rw [show place u (label (j u)) = chart (edgeOf u h) (label (j u)) from dif_pos h]
      exact chart_at _ _ (hj u)
    · exact (dif_neg h).trans (hfix h).symm
  have hinterval (j : Vertex P → Vertex B) (hj : Simplicial j) :
      IsIntervalMap (oneSkeleton P) N (fun u => (label (j u)).val) := by
    refine ⟨fun u => index (j u), ?_⟩
    intro u v huv
    let s := ({u.val, v.val} : Finset _)
    have hs : s ∈ P := huv.2
    have ha := (mem_faceImage_iff j hs _).mpr ⟨u, Finset.mem_insert_self _ _, rfl⟩
    have hb := (mem_faceImage_iff j hs _).mpr
      ⟨v, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), rfl⟩
    have ht := coord_face _ (hj _ hs)
    exact ⟨ht.2.2 _ (Finset.mem_image_of_mem _ ha) _ (Finset.mem_image_of_mem _ hb),
      ht.2.2 _ (Finset.mem_image_of_mem _ hb) _ (Finset.mem_image_of_mem _ ha)⟩
  have charts_for_faces : ∀ s ∈ P, ∃ e : I → Vertex B, Simplicial e ∧
      ∀ u : Vertex P, u.val ∈ s → ∀ i : I, (u ∈ S → i = label (f u)) → place u i = e i := by
    intro s hs
    let old := originalSupport A n s
    have ho : old ∈ A := originalSupport_mem n hs
    have hsub u (hu : (u : Vertex P).val ∈ s) :
        originalSupport A n {u.val} ⊆ old := support_mono A n (Finset.singleton_subset_iff.mpr hu)
    by_cases h₂ : old.card = 2
    · let e : E := ⟨⟨old, ho⟩, h₂⟩
      refine ⟨chart e, fun t ht => iterated_le_ambient (simplex_le ho) m
        ((hcharts e _).2 ⟨t, ht, rfl⟩), ?_⟩
      intro u hu i hi
      by_cases h : (originalSupport A n {u.val}).card = 2
      · have he : edgeOf u h = e := Subtype.ext (Subtype.ext
          (Finset.eq_of_subset_of_card_le (hsub u hu) (h₂.trans h.symm).le))
        simp only [place, dif_pos h, he]
      · rw [hi h, show place u (label (f u)) = f u from dif_neg h]
        exact (chart_at e (f u) ((hfSupp u).trans (hsub u hu))).symm
    · have h1 : old.card = 1 := by
        have hb := hdim _ ho
        have hp := Finset.card_pos.mpr (A.isRelLowerSet_faces ho).1
        exact Nat.le_antisymm (Nat.lt_succ_iff.mp (lt_of_le_of_ne hb h₂)) hp
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
      let v : Vertex A := ⟨x, hx ▸ ho⟩
      let e (_ : I) := retainedVertex m v
      refine ⟨e, ?_, ?_⟩
      · intro t ht
        change t.attach.image (fun _ => (retainedVertex m v).val) ∈ B
        rw [Finset.image_const ht.1.attach]
        exact (retainedVertex m v).property
      · intro u hu i hi
        have h := hsub u hu
        have hn : (originalSupport A n {u.val}).card ≠ 2 := by
          intro ht
          have hle := Finset.card_le_card h
          rw [ht, h1] at hle
          exact Nat.not_succ_le_self 1 hle
        rw [hi hn, show place u (label (f u)) = f u from dif_neg hn]
        exact (fixed u v (hx ▸ h)).1
  have h := RelativeIntervalChartGluing.relative_contiguity_of_interval_charts N S
    (label ∘ f) (label ∘ g) (hinterval f hf) (hinterval g hg)
    (fun u hu => congrArg label (fixed_on u hu)) place charts_for_faces
  have hf' := funext (realizes f hfSupp (fun _ _ => rfl))
  have hg' := funext (realizes g hgSupp (fun u hu => (fixed_on u hu).symm))
  simp only [Function.comp_apply] at h
  rw [hf', hg'] at h
  exact ReflTransGen.mono (fun _ _ hab => hab.1) _ _ h

end

end D5.S3.Topology.StableCategory.GraphCarrierContiguity
