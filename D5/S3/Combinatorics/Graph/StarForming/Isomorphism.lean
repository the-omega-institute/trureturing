/- GID: D5/S3/Combinatorics/Graph/StarForming/Isomorphism
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/Isomorphism
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Exact selection and finite-maximum transport through graph isomorphisms. -/

import D5.S3.Combinatorics.Graph.StarForming.FiniteCover
import D5.S3.Combinatorics.Graph.StarForming.Comparison

/-! Finite extrema transport with their actual selected images. Empty types
are included. These bridges are used by binary-lift switching isomorphisms. -/

namespace D5.S3.Combinatorics.Graph.StarForming.Isomorphism
open StarFormingDissociationRefutation

variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]

private theorem twoAt (e : G ≃g H) (S : W → Prop) (v : V) :
    Regular.TwoAt G.Adj (fun x => S (e x)) v ↔ Regular.TwoAt H.Adj S (e v) := by
  constructor
  · rintro (⟨a,b,ha,hb,he,hva,hvb⟩ | ⟨c,l,hc,hl,hvc,hcl⟩)
    · exact Or.inl ⟨e a,e b,ha,hb,fun h => he (e.injective h),
        e.map_rel_iff.mpr hva,e.map_rel_iff.mpr hvb⟩
    · exact Or.inr ⟨e c,e l,hc,hl,e.map_rel_iff.mpr hvc,e.map_rel_iff.mpr hcl⟩
  · rintro (⟨a,b,ha,hb,he,hva,hvb⟩ | ⟨c,l,hc,hl,hvc,hcl⟩)
    · refine Or.inl ⟨e.symm a,e.symm b,by simpa using ha,by simpa using hb,?_,?_,?_⟩
      · intro h; exact he (e.symm.injective h)
      · simpa using e.symm.map_rel_iff.mpr hva
      · simpa using e.symm.map_rel_iff.mpr hvb
    · exact Or.inr ⟨e.symm c,e.symm l,by simpa using hc,by simpa using hl,
        by simpa using e.symm.map_rel_iff.mpr hvc,e.symm.map_rel_iff.mpr hcl⟩

private theorem forms (e : G ≃g H) (S : W → Prop) :
    Regular.Forms G.Adj (fun x => S (e x)) ↔ Regular.Forms H.Adj S := by
  constructor
  · intro h y hy
    simpa using (twoAt e S (e.symm y)).mp (h (e.symm y) (by simpa using hy))
  · intro h x hx
    exact (twoAt e S x).mpr (h (e x) hx)

private theorem minimal (e : G ≃g H) (S : W → Prop) :
    Regular.Minimal G.Adj (fun x => S (e x)) ↔ Regular.Minimal H.Adj S := by
  constructor
  · rintro ⟨hf,hm⟩
    refine ⟨(forms e S).mp hf,?_⟩
    intro T hsub ⟨x,hx,hnot⟩ ht
    apply hm (fun v => T (e v)) (fun v hv => hsub _ hv)
      ⟨e.symm x,by simpa using hx,by simpa using hnot⟩
    exact (forms e T).mpr ht
  · rintro ⟨hf,hm⟩
    refine ⟨(forms e S).mpr hf,?_⟩
    intro T hsub ⟨x,hx,hnot⟩ ht
    apply hm (fun w => T (e.symm w)) (fun w hw => by
      simpa using hsub (e.symm w) hw) ⟨e x,hx,by simpa using hnot⟩
    apply (forms e _).mp
    simpa using ht

/-- The actual image is minimal forming exactly when the original set is. -/
theorem minimal_image_iff (e : G ≃g H) (S : Finset V) :
    IsMinimalStarForming H 2 (S.image e) ↔ IsMinimalStarForming G 2 S := by
  classical
  rw [← regular_minimal_iff,← regular_minimal_iff]
  simpa using (minimal e (fun w => w ∈ S.image e)).symm

/-- Dissociation transports in both directions, preserving the selected set. -/
theorem independent_image_iff (e : G ≃g H) (S : Finset V) :
    IsKIndependent H 2 (S.image e) ↔ IsKIndependent G 2 S := by
  classical
  rw [SubQuorum.DoubleStarGrafting.independent_iff,
    SubQuorum.DoubleStarGrafting.independent_iff]
  constructor
  · intro h v hv a ha b hb hva hvb
    exact e.injective (h (e v) (Finset.mem_image.mpr ⟨v,hv,rfl⟩)
      (e a) (Finset.mem_image.mpr ⟨a,ha,rfl⟩) (e b) (Finset.mem_image.mpr ⟨b,hb,rfl⟩)
      (e.map_rel_iff.mpr hva) (e.map_rel_iff.mpr hvb))
  · intro h v hv a ha b hb hva hvb
    obtain ⟨v',hv',rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨a',ha',rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b',hb',rfl⟩ := Finset.mem_image.mp hb
    exact congrArg e (h v' hv' a' ha' b' hb' (e.map_rel_iff.mp hva) (e.map_rel_iff.mp hvb))

/-- Both finite maxima are graph invariants, with actual attaining images. -/
theorem parameters (e : G ≃g H) : beta G 2 = beta H 2 ∧ SF G 2 = SF H 2 := by
  classical
  have hb {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
      (F : SimpleGraph A) (K : SimpleGraph B) [DecidableRel F.Adj] [DecidableRel K.Adj]
      (f : F ≃g K) : beta F 2 ≤ beta K 2 := by
    obtain ⟨S,hS,hc⟩ := beta_attained F 2
    have hi := (independent_image_iff f S).mpr hS
    have hl : (S.image f).card ≤ beta K 2 :=
      Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,hi⟩)
    rwa [Finset.card_image_of_injective _ f.injective,hc] at hl
  have hs {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
      (F : SimpleGraph A) (K : SimpleGraph B) [DecidableRel F.Adj] [DecidableRel K.Adj]
      (f : F ≃g K) : SF F 2 ≤ SF K 2 := by
    obtain ⟨S,hS,hc⟩ := sf_attained F 2
    have hi := (minimal_image_iff f S).mpr hS
    have hl : (S.image f).card ≤ SF K 2 :=
      Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,hi⟩)
    rwa [Finset.card_image_of_injective _ f.injective,hc] at hl
  exact ⟨le_antisymm (hb G H e) (hb H G e.symm),
    le_antisymm (hs G H e) (hs H G e.symm)⟩

end D5.S3.Combinatorics.Graph.StarForming.Isomorphism
