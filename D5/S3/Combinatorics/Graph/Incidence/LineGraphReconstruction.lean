/- GID: D5/S3/Combinatorics/Graph/Incidence/LineGraphReconstruction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Incidence/LineGraphReconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unique vertex lifts of prescribed line graph isomorphisms for triangle-free graphs. -/

module

public import D5.S3.Combinatorics.Graph.DUFStructure
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Reconstruction from prescribed line graph isomorphisms
-/

public section

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Incidence.LineGraphReconstruction

open SimpleGraph
open scoped Sym2

universe u v

private theorem finite_common {V : Type u} (G : SimpleGraph V) (hG : G.CliqueFree 3)
    (S : Finset G.edgeSet) (hne : S.Nonempty)
    (hi : ∀ a ∈ S, ∀ b ∈ S, ∃ x, x ∈ a.val ∧ x ∈ b.val) :
    ∃ x, ∀ a ∈ S, x ∈ a.val := by
  classical
  let Q := S.biUnion fun a => a.val.toFinset
  let U := {x // x ∈ Q}
  let r (a : G.edgeSet) : Finset U := a.val.toFinset.subtype (· ∈ Q)
  have support (a : G.edgeSet) (ha : a ∈ S) {x : V} (hx : x ∈ a.val) : x ∈ Q :=
    Finset.mem_biUnion.mpr ⟨a, ha, Sym2.mem_toFinset.mpr hx⟩
  have rmap (a : G.edgeSet) (ha : a ∈ S) :
      (r a).map (Function.Embedding.subtype _) = a.val.toFinset :=
    Finset.subtype_map_of_mem (fun _ hx => support a ha (Sym2.mem_toFinset.mp hx))
  let F := S.image r
  have hp : ∀ p ∈ F, p.card = 2 := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    rw [← Finset.card_map (Function.Embedding.subtype _), rmap a ha]
    exact Sym2.card_toFinset_of_not_isDiag _ (G.not_isDiag_of_mem_edgeSet a.property)
  have hinter : D5.S3.Combinatorics.Graph.DUFStructure.Intersecting F := by
    intro p hp q hq hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨x, hx, hy⟩ := hi a ha b hb
    let z : U := ⟨x, support a ha hx⟩
    exact Finset.disjoint_left.mp hd
      (Finset.mem_subtype.mpr (Sym2.mem_toFinset.mpr hx) : z ∈ r a)
      (Finset.mem_subtype.mpr (Sym2.mem_toFinset.mpr hy) : z ∈ r b)
  have hF : F.Nonempty := hne.image r
  rcases D5.S3.Combinatorics.Graph.DUFStructure.intersecting_classification F hp hinter hF with
    ⟨c, A, _, hstar, _⟩ | ⟨T, hT, htri⟩
  · refine ⟨c.val, fun a ha => ?_⟩
    have hc : c ∈ r a := by
      have hr : r a ∈ D5.S3.Combinatorics.Graph.DUFStructure.star c A :=
        hstar ▸ Finset.mem_image.mpr ⟨a, ha, rfl⟩
      obtain ⟨z, _, hz⟩ := Finset.mem_image.mp hr
      rw [← hz]
      simp
    exact Sym2.mem_toFinset.mp (Finset.mem_subtype.mp hc)
  · apply False.elim
    apply hG (T.map (Function.Embedding.subtype _))
    rw [SimpleGraph.isNClique_iff]
    refine ⟨?_, by simpa using hT⟩
    intro x hx y hy hxy
    obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_map.mp hy
    have hne' : x' ≠ y' := fun h => hxy (congrArg Subtype.val h)
    have hpF : ({x', y'} : Finset U) ∈ F := by
      rw [htri]
      exact Finset.mem_powersetCard.mpr
        ⟨Finset.insert_subset_iff.mpr ⟨hx', Finset.singleton_subset_iff.mpr hy'⟩,
          by simp [hne']⟩
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hpF
    have hx : x'.val ∈ a.val := by
      have : x' ∈ r a := he.symm ▸ (by simp)
      exact Sym2.mem_toFinset.mp (Finset.mem_subtype.mp this)
    have hy : y'.val ∈ a.val := by
      have : y' ∈ r a := he.symm ▸ (by simp)
      exact Sym2.mem_toFinset.mp (Finset.mem_subtype.mp this)
    have heq := (Sym2.mem_and_mem_iff hxy).mp ⟨hx, hy⟩
    change s(x'.val, y'.val) ∈ G.edgeSet
    change a.val = s(x'.val, y'.val) at heq
    exact heq ▸ a.property

private theorem two_edges {V : Type u} (G : SimpleGraph V)
    (hd : ∀ x, Nontrivial (G.neighborSet x)) (x : V) :
    ∃ a b : G.edgeSet, a ≠ b ∧ x ∈ a.val ∧ x ∈ b.val := by
  let := hd x
  obtain ⟨y, z, hyz⟩ := exists_pair_ne (G.neighborSet x)
  refine ⟨⟨s(x, y.val), y.property⟩, ⟨s(x, z.val), z.property⟩, ?_, by simp, by simp⟩
  intro h
  apply hyz
  exact Subtype.ext (Sym2.congr_right.mp (congrArg Subtype.val h))

private theorem image_star {V : Type u} {W : Type v}
    (G : SimpleGraph V) (H : SimpleGraph W) (hH : H.CliqueFree 3)
    (hd : ∀ x, Nontrivial (G.neighborSet x)) (e : G.lineGraph ≃g H.lineGraph) (x : V) :
    ∃ y, ∀ a : G.edgeSet, x ∈ a.val → y ∈ (e a).val := by
  classical
  obtain ⟨a, b, hab, hxa, hxb⟩ := two_edges G hd x
  have hab' : H.lineGraph.Adj (e a) (e b) := e.map_rel_iff.mpr ⟨hab, x, hxa, hxb⟩
  obtain ⟨y, hya, hyb⟩ := (SimpleGraph.lineGraph_adj_iff_exists.mp hab').2
  refine ⟨y, fun c hxc => ?_⟩
  let S : Finset H.edgeSet := {e a, e b, e c}
  have hs : ∀ p ∈ S, ∃ d : G.edgeSet, p = e d ∧ x ∈ d.val := by
    intro p hp
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨a, rfl, hxa⟩
    · exact ⟨b, rfl, hxb⟩
    · exact ⟨c, rfl, hxc⟩
  obtain ⟨z, hz⟩ := finite_common H hH S (by simp [S]) (by
    intro p hp q hq
    obtain ⟨d, rfl, hxd⟩ := hs p hp
    obtain ⟨d', rfl, hxd'⟩ := hs q hq
    by_cases he : d = d'
    · subst d'
      rcases e d with ⟨⟨l, r⟩, h⟩
      exact ⟨l, by simp, by simp⟩
    · exact (SimpleGraph.lineGraph_adj_iff_exists.mp (e.map_rel_iff.mpr ⟨he, x, hxd, hxd'⟩)).2)
  have hyz : y = z := by
    by_contra h
    exact hab'.1 (Subtype.ext
      (Sym2.eq_of_ne_mem h hya (hz _ (by simp [S])) hyb (hz _ (by simp [S]))))
  exact hyz.symm ▸ hz _ (by simp [S])

/-- Every prescribed line graph isomorphism has exactly one vertex lift under the
triangle-free and two-distinct-neighbor hypotheses. -/
theorem exists_unique_line_graph_lift {V : Type u} {W : Type v}
    (G : SimpleGraph V) (H : SimpleGraph W)
    (hG : G.CliqueFree 3) (hH : H.CliqueFree 3)
    (hdegG : ∀ x : V, Nontrivial (G.neighborSet x))
    (hdegH : ∀ y : W, Nontrivial (H.neighborSet y))
    (e : G.lineGraph ≃g H.lineGraph) :
    ∃! f : G ≃g H, f.lineGraph = e := by
  classical
  choose f hf using image_star G H hH hdegG e
  choose g hg using image_star H G hG hdegH e.symm
  have gf : ∀ x, g (f x) = x := by
    intro x
    obtain ⟨a, b, hab, hxa, hxb⟩ := two_edges G hdegG x
    have ha : g (f x) ∈ a.val := by
      simpa using hg (f x) (e a) (hf x a hxa)
    have hb : g (f x) ∈ b.val := by
      simpa using hg (f x) (e b) (hf x b hxb)
    by_contra h
    exact hab (Subtype.ext (Sym2.eq_of_ne_mem h ha hxa hb hxb))
  have fg : ∀ y, f (g y) = y := by
    intro y
    obtain ⟨a, b, hab, hya, hyb⟩ := two_edges H hdegH y
    have ha : f (g y) ∈ a.val := by
      simpa using hf (g y) (e.symm a) (hg y a hya)
    have hb : f (g y) ∈ b.val := by
      simpa using hf (g y) (e.symm b) (hg y b hyb)
    by_contra h
    exact hab (Subtype.ext (Sym2.eq_of_ne_mem h ha hya hb hyb))
  have finj : Function.Injective f := Function.LeftInverse.injective gf
  have inc (x : V) (a : G.edgeSet) : f x ∈ (e a).val ↔ x ∈ a.val := by
    refine ⟨fun h => ?_, hf x a⟩
    have hh := hg (f x) (e a) h
    simpa [gf] using hh
  have maps (a : G.edgeSet) : (e a).val = a.val.map f := by
    rcases a with ⟨⟨x, y⟩, hxy⟩
    exact (Sym2.mem_and_mem_iff (finj.ne hxy.ne)).mp
      ⟨hf x _ (by simp), hf y _ (by simp)⟩
  let F : G ≃g H :=
    { toFun := f
      invFun := g
      left_inv := gf
      right_inv := fg
      map_rel_iff' := by
        intro x y
        constructor
        · intro hxy
          let b : H.edgeSet := ⟨s(f x, f y), hxy⟩
          let a := e.symm b
          have hx : x ∈ a.val := (inc x a).mp (by simp [a, b])
          have hy : y ∈ a.val := (inc y a).mp (by simp [a, b])
          have hne : x ≠ y := fun h => hxy.ne (congrArg f h)
          have he := (Sym2.mem_and_mem_iff hne).mp ⟨hx, hy⟩
          change s(x, y) ∈ G.edgeSet
          exact he ▸ a.property
        · intro hxy
          let a : G.edgeSet := ⟨s(x, y), hxy⟩
          have he : (e a).val = s(f x, f y) := maps a
          change s(f x, f y) ∈ H.edgeSet
          exact he ▸ (e a).property }
  have hF : F.lineGraph = e := by
    apply DFunLike.ext
    intro a
    apply Subtype.ext
    exact (maps a).symm
  refine ⟨F, hF, ?_⟩
  intro F' hF'
  ext x
  obtain ⟨a, b, hab, hxa, hxb⟩ := two_edges G hdegG x
  have mem' (c : G.edgeSet) (hc : x ∈ c.val) : F' x ∈ (e c).val := by
    rw [← hF']
    change F' x ∈ c.val.map F'
    exact Sym2.mem_map.mpr ⟨x, hc, rfl⟩
  change F' x = f x
  by_contra h
  exact (e.injective.ne hab) (Subtype.ext
    (Sym2.eq_of_ne_mem h (mem' a hxa) (hf x a hxa) (mem' b hxb) (hf x b hxb)))

end D5.S3.Combinatorics.Graph.Incidence.LineGraphReconstruction
