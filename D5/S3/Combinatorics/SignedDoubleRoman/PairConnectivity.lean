/- GID: D5/S3/Combinatorics/SignedDoubleRoman/PairConnectivity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/PairConnectivity
   mirror-E: none(waiver:elementary-cut-analysis)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Metric]
   utility: none
   digest: Connectivity after deleting vertices in distinct components of a two-vertex cut. -/

import D5.S3.Combinatorics.SignedDoubleRoman.SubcubicColouring
import Mathlib.Combinatorics.SimpleGraph.Metric

set_option autoImplicit false

namespace D5.S3.Combinatorics.SignedDoubleRoman.SubcubicColouring

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Distinct cut components cannot jointly isolate a third component after a swap. -/
theorem pair_preconnected_of_cut_path
    (hsingle : ∀ r, (G.induce {v | v ≠ r}).Preconnected)
    (x y a b : V) (hax : a ≠ x) (hay : a ≠ y) (hbx : b ≠ x) (hby : b ≠ y)
    (hab : ¬(G.induce {v | v ≠ x ∧ v ≠ y}).Reachable ⟨a, hax, hay⟩ ⟨b, hbx, hby⟩)
    (hxy : (G.induce {v | v ≠ a ∧ v ≠ b}).Reachable
      ⟨x, hax.symm, hbx.symm⟩ ⟨y, hay.symm, hby.symm⟩) :
    (G.induce {v | v ≠ a ∧ v ≠ b}).Preconnected := by
  classical
  let Q := G.induce {v | v ≠ a ∧ v ≠ b}
  let H := G.induce {v | v ≠ x ∧ v ≠ y}
  let xr : {v : V | v ≠ a ∧ v ≠ b} := ⟨x, hax.symm, hbx.symm⟩
  let yr : {v : V | v ≠ a ∧ v ≠ b} := ⟨y, hay.symm, hby.symm⟩
  have hroot : Q.connectedComponentMk xr = Q.connectedComponentMk yr :=
    ConnectedComponent.sound hxy
  have hall : ∀ v, Q.Reachable xr v := by
    intro v
    by_contra hv
    let c := Q.connectedComponentMk v
    have hcx : c ≠ Q.connectedComponentMk xr :=
      fun he => hv (ConnectedComponent.exact he.symm)
    have hcavoid : ∀ z : c, z.val.val ≠ x ∧ z.val.val ≠ y := by
      intro z
      constructor
      · intro hz
        have he : z.val = xr := Subtype.ext hz
        exact hcx (z.property.symm.trans (congrArg Q.connectedComponentMk he))
      · intro hz
        have he : z.val = yr := Subtype.ext hz
        exact hcx ((z.property.symm.trans (congrArg Q.connectedComponentMk he)).trans
          hroot.symm)
    let K : Finset V := Finset.univ.filter fun z =>
      ∃ hz : z ≠ a ∧ z ≠ b, Q.connectedComponentMk ⟨z, hz⟩ = c
    have hout : v.val ∈ K := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, v.property, rfl⟩
    have hxK : x ∉ K := by
      simp only [K, mem_filter, mem_univ, true_and]
      rintro ⟨hz, he⟩
      exact hcx he.symm
    have crossing (r s : V) (hrs : r ≠ s) (hvr : v.val ≠ r) (hxr : x ≠ r)
        (hrK : r ∉ K) (hsQ : ∀ z, z ≠ r → z ≠ s → z ≠ a ∧ z ≠ b) :
        ∃ z ∈ K, G.Adj z s := by
      let J := G.induce {z | z ≠ r}
      let T : Finset {z : V | z ≠ r} := Finset.univ.filter fun z => z.val ∈ K
      obtain ⟨z, hz, w, hw, hzw⟩ := reachable_boundary J T
        (hsingle r ⟨v.val, hvr⟩ ⟨x, hxr⟩)
        (by simp [T, hout]) (by simp [T, hxK])
      have hzK : z.val ∈ K := by simpa [T] using hz
      have hwK : w.val ∉ K := by simpa [T] using hw
      have hws : w.val = s := by
        by_contra hws
        obtain ⟨hzQ, hzc⟩ := (show ∃ hzQ : z.val ≠ a ∧ z.val ≠ b,
          Q.connectedComponentMk ⟨z.val, hzQ⟩ = c from by simpa [K] using hzK)
        have hwQ := hsQ w.val w.property hws
        have he : Q.connectedComponentMk ⟨w.val, hwQ⟩ = c :=
          (ConnectedComponent.sound
            (show Q.Adj ⟨w.val, hwQ⟩ ⟨z.val, hzQ⟩ from hzw.symm).reachable).trans hzc
        exact hwK (by simp [K]; exact ⟨hwQ, he⟩)
      exact ⟨z.val, hzK, hws ▸ hzw⟩
    have habne : a ≠ b := by
      intro he
      subst b
      exact hab Reachable.rfl
    have haK : a ∉ K := by simp [K]
    have hbK : b ∉ K := by simp [K]
    obtain ⟨z, hzK, hzb⟩ := crossing a b habne v.property.1 hax.symm haK
      (fun z hza hzb => ⟨hza, hzb⟩)
    obtain ⟨w, hwK, hwa⟩ := crossing b a habne.symm v.property.2 hbx.symm hbK
      (fun z hzb hza => ⟨hza, hzb⟩)
    obtain ⟨hzQ, hzc⟩ := (show ∃ hzQ : z ≠ a ∧ z ≠ b,
      Q.connectedComponentMk ⟨z, hzQ⟩ = c from by simpa [K] using hzK)
    obtain ⟨hwQ, hwc⟩ := (show ∃ hwQ : w ≠ a ∧ w ≠ b,
      Q.connectedComponentMk ⟨w, hwQ⟩ = c from by simpa [K] using hwK)
    let inc : c.toSimpleGraph →g H :=
      { toFun := fun t => ⟨t.val.val, hcavoid t⟩
        map_rel' := fun h => h }
    have hp := (c.reachable_toSimpleGraph hwc hzc).map inc
    have haw : H.Adj ⟨a, hax, hay⟩ (inc ⟨⟨w, hwQ⟩, hwc⟩) := hwa.symm
    have hzb' : H.Adj (inc ⟨⟨z, hzQ⟩, hzc⟩) ⟨b, hbx, hby⟩ := hzb
    exact hab (haw.reachable.trans (hp.trans hzb'.reachable))
  intro u v
  exact (hall u).symm.trans (hall v)

/-- Without a cut vertex, each component of a two-vertex deletion meets either root. -/
theorem two_cut_component_attaches
    (hsingle : ∀ r, (G.induce {v | v ≠ r}).Preconnected)
    (x y : V) (hxy : x ≠ y)
    (c : (G.induce {v | v ≠ x ∧ v ≠ y}).ConnectedComponent) :
    ∃ z : {v : V | v ≠ x ∧ v ≠ y},
      (G.induce {v | v ≠ x ∧ v ≠ y}).connectedComponentMk z = c ∧ G.Adj x z.val := by
  classical
  let H := G.induce {v | v ≠ x ∧ v ≠ y}
  let J := G.induce {v | v ≠ y}
  let T : Finset {v : V | v ≠ y} := Finset.univ.filter fun z =>
    ∃ hz : z.val ≠ x, H.connectedComponentMk ⟨z.val, hz, z.property⟩ = c
  have hout : (⟨c.out.val, c.out.property.2⟩ : {v : V | v ≠ y}) ∈ T := by
    exact Finset.mem_filter.mpr ⟨mem_univ _, c.out.property.1, c.out_eq⟩
  have hxT : (⟨x, hxy⟩ : {v : V | v ≠ y}) ∉ T := by simp [T]
  obtain ⟨z, hz, w, hw, hzw⟩ := reachable_boundary J T
    (hsingle y ⟨c.out.val, c.out.property.2⟩ ⟨x, hxy⟩) hout hxT
  obtain ⟨hzx, hzc⟩ := (show ∃ hzx : z.val ≠ x,
    H.connectedComponentMk ⟨z.val, hzx, z.property⟩ = c from by simpa [T] using hz)
  have hwx : w.val = x := by
    by_contra hwx
    have he : H.connectedComponentMk ⟨w.val, hwx, w.property⟩ = c :=
      (ConnectedComponent.sound
        (show H.Adj ⟨w.val, hwx, w.property⟩ ⟨z.val, hzx, z.property⟩ from
          hzw.symm).reachable).trans hzc
    exact hw (Finset.mem_filter.mpr ⟨mem_univ _, hwx, he⟩)
  exact ⟨⟨z.val, hzx, z.property⟩, hzc, hwx ▸ hzw.symm⟩

/-- A component joining both roots supplies a walk in any set containing the piece. -/
theorem roots_reachable_through_component
    (hsingle : ∀ r, (G.induce {v | v ≠ r}).Preconnected)
    (x y : V) (hxy : x ≠ y)
    (c : (G.induce {v | v ≠ x ∧ v ≠ y}).ConnectedComponent)
    (P : Set V) (hx : x ∈ P) (hy : y ∈ P)
    (hc : ∀ z : c, z.val.val ∈ P) :
    (G.induce P).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  classical
  let H := G.induce {v | v ≠ x ∧ v ≠ y}
  obtain ⟨a, hac, hxa⟩ := two_cut_component_attaches G hsingle x y hxy c
  have hb : ∃ b : {v : V | v ≠ x ∧ v ≠ y}, H.connectedComponentMk b = c ∧
      G.Adj y b.val := by
    have h := two_cut_component_attaches G hsingle y x hxy.symm
    have hs : {v : V | v ≠ y ∧ v ≠ x} = {v : V | v ≠ x ∧ v ≠ y} := by
      ext v
      simp only [Set.mem_ofPred_eq, and_comm]
    rw [hs] at h
    exact h c
  obtain ⟨b, hbc, hyb⟩ := hb
  let inc : c.toSimpleGraph →g G.induce P :=
    { toFun := fun z => ⟨z.val.val, hc z⟩
      map_rel' := fun h => h }
  have hp := (c.reachable_toSimpleGraph hac hbc).map inc
  have hxa' : (G.induce P).Adj ⟨x, hx⟩ (inc ⟨a, hac⟩) := hxa
  have hby' : (G.induce P).Adj (inc ⟨b, hbc⟩) ⟨y, hy⟩ := hyb.symm
  exact hxa'.reachable.trans (hp.trans hby'.reachable)

/-- A shortest walk visits only its first neighbour of its starting vertex. -/
theorem shortest_walk_neighbour_support {x t y : V} (hxt : G.Adj x t)
    (p : G.Walk t y) (hshort : (p.cons hxt).length = G.dist x y)
    (b : V) (hxb : G.Adj x b) (hbt : b ≠ t) : b ∉ (p.cons hxt).support := by
  classical
  intro hb
  have hbx : b ≠ x := (G.ne_of_adj hxb).symm
  have hbp : b ∈ p.support := by simpa [hbx] using hb
  have hi : p.support.idxOf b ≠ 0 := by
    intro hi
    have hh := (List.idxOf_eq_zero_iff_eq_nil_or_head_eq b).mp hi
    rcases hh with hh | hh
    · exact p.support_ne_nil hh
    · have ht : t = b := by cases p <;> simpa using hh
      exact hbt ht.symm
  have hl := G.dist_le ((p.dropUntil b hbp).cons hxb)
  rw [Walk.length_cons, Walk.length_dropUntil] at hl
  simp only [Walk.length_cons] at hshort
  have hi' := List.idxOf_lt_length_of_mem hbp
  rw [Walk.length_support] at hi'
  omega

/-- A cubic graph without a single-vertex cut has a suitable precoloured neighbour pair. -/
theorem exists_nonseparating_neighbours
    (hsingle : ∀ r, (G.induce {v | v ≠ r}).Preconnected)
    (hdeg : ∀ r, (G.neighborFinset r).card = 3)
    (x y : V) (hxy : x ≠ y)
    (hcut : ¬(G.induce {v | v ≠ x ∧ v ≠ y}).Preconnected) :
    ∃ a b, a ≠ b ∧ G.Adj x a ∧ G.Adj x b ∧ ¬G.Adj a b ∧
      (G.induce ({a, b} : Set V)ᶜ).Preconnected := by
  classical
  let H := G.induce {v | v ≠ x ∧ v ≠ y}
  obtain ⟨u, v, huv⟩ : ∃ u v, ¬H.Reachable u v := by
    by_contra! h
    exact hcut h
  let c := H.connectedComponentMk u
  let d := H.connectedComponentMk v
  have hcd : c ≠ d := fun he => huv (ConnectedComponent.exact he)
  obtain ⟨a, hac, hxa⟩ := two_cut_component_attaches G hsingle x y hxy c
  obtain ⟨b, hbd, hxb⟩ := two_cut_component_attaches G hsingle x y hxy d
  have hab : a.val ≠ b.val := by
    intro he
    exact hcd (hac.symm.trans ((congrArg H.connectedComponentMk
      (Subtype.ext he)).trans hbd))
  have finish (a b : {z : V | z ≠ x ∧ z ≠ y})
      (hxa : G.Adj x a.val) (hxb : G.Adj x b.val)
      (habc : H.connectedComponentMk a ≠ H.connectedComponentMk b)
      (hr : (G.induce {z | z ≠ a.val ∧ z ≠ b.val}).Reachable
        ⟨x, a.property.1.symm, b.property.1.symm⟩
        ⟨y, a.property.2.symm, b.property.2.symm⟩) :
      ∃ a b, a ≠ b ∧ G.Adj x a ∧ G.Adj x b ∧ ¬G.Adj a b ∧
        (G.induce ({a, b} : Set V)ᶜ).Preconnected := by
    have hn : ¬H.Reachable a b := fun h => habc (ConnectedComponent.sound h)
    have hne : a.val ≠ b.val := fun he => habc (congrArg H.connectedComponentMk
      (Subtype.ext he))
    refine ⟨a.val, b.val, hne, hxa, hxb, ?_, ?_⟩
    · exact fun h => hn (show H.Adj a b from h).reachable
    · have hh := pair_preconnected_of_cut_path G hsingle x y a.val b.val
        a.property.1 a.property.2 b.property.1 b.property.2 hn hr
      have hs : {z | z ≠ a.val ∧ z ≠ b.val} = ({a.val, b.val} : Set V)ᶜ := by
        ext z
        simp
      rwa [hs] at hh
  by_cases hedge : G.Adj x y
  · exact finish a b hxa hxb (fun he => hcd (hac.symm.trans (he.trans hbd)))
      (show (G.induce {z | z ≠ a.val ∧ z ≠ b.val}).Adj
        ⟨x, a.property.1.symm, b.property.1.symm⟩
        ⟨y, a.property.2.symm, b.property.2.symm⟩ from hedge).reachable
  have hpair : ({a.val, b.val} : Finset V).card = 2 := by simp [hab]
  obtain ⟨t, htN, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({a.val, b.val} : Finset V).card < (G.neighborFinset x).card by
      rw [hpair, hdeg]
      omega)
  have hxt : G.Adj x t := by simpa using htN
  have htx : t ≠ x := (G.ne_of_adj hxt).symm
  have hty : t ≠ y := fun he => hedge (he ▸ hxt)
  let tr : {z : V | z ≠ x ∧ z ≠ y} := ⟨t, htx, hty⟩
  have hta : t ≠ a.val := (by simpa only [mem_insert, mem_singleton, not_or] using ht :
    t ≠ a.val ∧ t ≠ b.val).1
  have htb : t ≠ b.val := (by simpa only [mem_insert, mem_singleton, not_or] using ht :
    t ≠ a.val ∧ t ≠ b.val).2
  let P (e : H.ConnectedComponent) : Set V :=
    {z | z = x ∨ z = y ∨ ∃ hz : z ≠ x ∧ z ≠ y,
      H.connectedComponentMk ⟨z, hz⟩ = e}
  have hPx (e : H.ConnectedComponent) : x ∈ P e := Or.inl rfl
  have hPy (e : H.ConnectedComponent) : y ∈ P e := Or.inr (Or.inl rfl)
  have hPc (e : H.ConnectedComponent) (z : e) : z.val.val ∈ P e :=
    Or.inr (Or.inr ⟨z.val.property, z.property⟩)
  have hmem (e : H.ConnectedComponent) (z : {z : V | z ≠ x ∧ z ≠ y}) :
      z.val ∈ P e ↔ H.connectedComponentMk z = e := by
    constructor
    · intro hz
      rcases hz with hz | hz | ⟨hp, he⟩
      · exact False.elim (z.property.1 hz)
      · exact False.elim (z.property.2 hz)
      · exact he
    · intro hz
      exact Or.inr (Or.inr ⟨z.property, hz⟩)
  have double (e : H.ConnectedComponent) (s t b : {z : V | z ≠ x ∧ z ≠ y})
      (hse : H.connectedComponentMk s = e) (hte : H.connectedComponentMk t = e)
      (hbe : H.connectedComponentMk b ≠ e) (hst : s.val ≠ t.val)
      (hxs : G.Adj x s.val) (hxt : G.Adj x t.val) (hxb : G.Adj x b.val) :
      ∃ a b, a ≠ b ∧ G.Adj x a ∧ G.Adj x b ∧ ¬G.Adj a b ∧
        (G.induce ({a, b} : Set V)ᶜ).Preconnected := by
    let J := G.induce (P e)
    have hroot := roots_reachable_through_component G hsingle x y hxy e
      (P e) (hPx e) (hPy e) (hPc e)
    obtain ⟨p, hp⟩ := hroot.exists_walk_length_eq_dist
    cases p with
    | nil => exact False.elim (hxy rfl)
    | @cons _ w _ hxw p =>
      obtain ⟨z, hze, hxz, hzw⟩ : ∃ z : {z : V | z ≠ x ∧ z ≠ y},
          H.connectedComponentMk z = e ∧ G.Adj x z.val ∧ z.val ≠ w.val := by
        by_cases hs : s.val = w.val
        · exact ⟨t, hte, hxt, fun he => hst (hs.trans he.symm)⟩
        · exact ⟨s, hse, hxs, hs⟩
      let zr : P e := ⟨z.val, (hmem e z).mpr hze⟩
      have hn : zr ∉ (p.cons hxw).support := shortest_walk_neighbour_support J hxw p hp
        zr hxz (fun he => hzw (congrArg Subtype.val he))
      let q := (p.cons hxw).map (SimpleGraph.Embedding.induce (G := G) (P e)).toHom
      have hsupport : ∀ k ∈ q.support, k ≠ z.val ∧ k ≠ b.val := by
        intro k hk
        change k ∈ ((p.cons hxw).map
          (SimpleGraph.Embedding.induce (G := G) (P e)).toHom).support at hk
        rw [Walk.support_map] at hk
        obtain ⟨kr, hkr, rfl⟩ := List.mem_map.mp hk
        constructor
        · intro he
          exact hn ((Subtype.ext he : kr = zr) ▸ hkr)
        · intro he
          exact hbe ((hmem e b).mp (he ▸ kr.property))
      exact finish z b hxz hxb (fun he => hbe (he.symm.trans hze))
        ⟨q.induce {k | k ≠ z.val ∧ k ≠ b.val} hsupport⟩
  by_cases htc : H.connectedComponentMk tr = c
  · exact double c a tr b hac htc (fun he => hcd (he.symm.trans hbd)) hta.symm
      hxa hxt hxb
  by_cases htd : H.connectedComponentMk tr = d
  · exact double d b tr a hbd htd (fun he => hcd (hac.symm.trans he)) htb.symm
      hxb hxt hxa
  have haP : a.val ∉ P (H.connectedComponentMk tr) :=
    fun h => htc ((hmem _ a).mp h |>.symm.trans hac)
  have hbP : b.val ∉ P (H.connectedComponentMk tr) :=
    fun h => htd ((hmem _ b).mp h |>.symm.trans hbd)
  let inc : G.induce (P (H.connectedComponentMk tr)) →g
      G.induce {z | z ≠ a.val ∧ z ≠ b.val} :=
    { toFun := fun z => ⟨z.val, fun he => haP (he ▸ z.property),
        fun he => hbP (he ▸ z.property)⟩
      map_rel' := fun h => h }
  exact finish a b hxa hxb (fun he => hcd (hac.symm.trans (he.trans hbd)))
    ((roots_reachable_through_component G hsingle x y hxy (H.connectedComponentMk tr)
      (P _) (hPx _) (hPy _) (hPc _)).map inc)

#print axioms pair_preconnected_of_cut_path
#print axioms shortest_walk_neighbour_support

end D5.S3.Combinatorics.SignedDoubleRoman.SubcubicColouring
