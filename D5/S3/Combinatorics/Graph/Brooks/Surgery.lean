/- GID: D5/S3/Combinatorics/Graph/Brooks/Surgery
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Brooks/Surgery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Rabern clique and odd-cycle surgery for the arbitrary-degree Brooks induction. -/

import D5.S3.Combinatorics.Graph.Brooks.CliqueExtension

/-
Copyright (c) 2026 Brian Rabern. All rights reserved.
Released under Apache 2.0 license as described in
`docs/reports/brooks-suppliers/BrooksLean-LICENSE.txt`.
Authors: Brian Rabern and Opus 5

Source: https://github.com/brianrabern/BrooksLean/tree/1d990050d881327fc79dd51e82ba4449b4e2467d
Units: BrooksLean/OddCycle.lean, BrooksLean/VertexLemmas.lean, BrooksLean/Brooks.lean.
Modified from the retained General source by capacity partition on 2026-10-19.
Only module framing, imports and consumed helper visibility are adapted here.
The low-degree deletion extension is imported from its existing native owner.
The mathematical argument is Landon Rabern, Yet another proof of Brooks' theorem,
Discrete Mathematics 346 (2023), 113261, DOI 10.1016/j.disc.2022.113261.
Retire each transplanted statement when this repository's pinned Mathlib contains
an equivalent statement, replacing its consumers by direct applications.
-/

section

universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {n : ℕ}

/-- Combine a colouring of `Qᶜ` with a path-extension across a spanning `y,z`-path in `Q`,
following Rabern: colour `y` with the colour of `z*`, then greedily along the path
(internal vertices have an uncoloured neighbour; `z` sees `y` and `z*` the same colour). -/
private theorem Colorable.of_rabern_path_extension [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {n : ℕ} [NeZero n] {Q : Finset V} {y z : V}
    (p : G.Walk y z) (hp : p.IsPath)
    (hspan : p.support.toFinset = Q)
    (C : (G.induce ((↑Q : Set V)ᶜ)).Coloring (Fin n))
    (star : V → V)
    (hstarQc : ∀ v ∈ Q, star v ∈ ((↑Q : Set V)ᶜ))
    (hstarAdj : ∀ v ∈ Q, G.Adj v (star v))
    (honly : ∀ v ∈ Q, ∀ w ∈ ((↑Q : Set V)ᶜ), G.Adj v w → w = star v)
    (hyzAdj : G.Adj y z)
    (hne : C ⟨star y, by
        have : y ∈ Q := by rw [← hspan]; exact List.mem_toFinset.2 p.start_mem_support
        exact hstarQc y this⟩ ≠
      C ⟨star z, by
        have : z ∈ Q := by rw [← hspan]; exact List.mem_toFinset.2 p.end_mem_support
        exact hstarQc z this⟩)
    (hdeg : ∀ v ∈ Q, (G.neighborFinset v).card ≤ n) :
    G.Colorable n := by
  classical
  have hyQ : y ∈ Q := by rw [← hspan]; exact List.mem_toFinset.2 p.start_mem_support
  have hzQ : z ∈ Q := by rw [← hspan]; exact List.mem_toFinset.2 p.end_mem_support
  set a : Fin n := C ⟨star z, hstarQc z hzQ⟩
  have hy_not : y ∉ (Qᶜ : Finset V) := Finset.notMem_compl.2 hyQ
  -- Build the colouring of `insert y Qᶜ` directly from `C`.
  set sY : Finset V := insert y (Qᶜ : Finset V)
  let colorY : ↥(↑sY : Set V) → Fin n := fun u =>
    if h : u.1 = y then a
    else C ⟨u.1, by
      have hu : u.1 ∈ sY := by simpa [sY] using u.property
      have hu' : u.1 ∈ (Qᶜ : Finset V) := (Finset.mem_insert.1 (by simpa [sY] using hu)).resolve_left h
      simpa using hu'⟩
  have hCy_valid : ∀ {x y' : ↥(↑sY : Set V)},
      (G.induce (↑sY : Set V)).Adj x y' → colorY x ≠ colorY y' := by
    intro x y' hxy
    have hadj : G.Adj x.1 y'.1 := hxy
    dsimp [colorY]
    by_cases hx : x.1 = y <;> by_cases hy' : y'.1 = y
    · exact absurd (hx.trans hy'.symm) hadj.ne
    · simp only [hx, hy', ↓reduceDIte]
      have hyQc : y'.1 ∈ ((↑Q : Set V)ᶜ) := by
        have : y'.1 ∈ (Qᶜ : Finset V) :=
          (Finset.mem_insert.1 (by simpa [sY] using y'.property)).resolve_left hy'
        simpa using this
      have : y'.1 = star y := honly y hyQ y'.1 hyQc (hx ▸ hadj)
      simpa [this, a] using Ne.symm hne
    · simp only [hx, hy', ↓reduceDIte]
      have hxQc : x.1 ∈ ((↑Q : Set V)ᶜ) := by
        have : x.1 ∈ (Qᶜ : Finset V) :=
          (Finset.mem_insert.1 (by simpa [sY] using x.property)).resolve_left hx
        simpa using this
      have : x.1 = star y := honly y hyQ x.1 hxQc (hy' ▸ hadj.symm)
      simpa [this, a] using hne
    · simp only [hx, hy', ↓reduceDIte]
      exact C.valid hadj
  let Cy : (G.induce (↑sY : Set V)).Coloring (Fin n) :=
    Coloring.mk colorY hCy_valid
  have hCy_y : Cy ⟨y, by simp [sY]⟩ = a := by
    change colorY _ = a; simp [colorY]
  have hzstar_Qc : star z ∈ (Qᶜ : Finset V) := by simpa using hstarQc z hzQ
  have hzstar_mem : star z ∈ sY := by simp [sY, hzstar_Qc]
  have hCy_zstar : Cy ⟨star z, hzstar_mem⟩ = a := by
    change colorY _ = a
    have hne_zy : (star z : V) ≠ y := fun h => hy_not (h ▸ hzstar_Qc)
    simp [colorY, hne_zy]
    rfl
  -- Length induction keeps the path endpoint `z` fixed (Walk induction would generalize it).
  -- Here `q` is the *uncoloured* suffix of the spanning path: colour its vertices in order,
  -- using a free colour at internal vertices and the `y`/`star z` collision at `z`.
  have along :
      ∀ (k : ℕ) {u : V} (q : G.Walk u z), q.length = k → q.IsPath →
        ∀ (s : Finset V) (Cs : (G.induce (↑s : Set V)).Coloring (Fin n))
          (hyS : y ∈ s) (hzS : star z ∈ s),
          Cs ⟨y, hyS⟩ = a → Cs ⟨star z, hzS⟩ = a →
          (∀ x ∈ q.support, x ∈ Q) →
          (∀ x ∈ q.support, x ∉ s) →
          (G.induce (↑(s ∪ q.support.toFinset) : Set V)).Colorable n := by
    intro k
    induction k with
    | zero =>
      intro u q hk hq s Cs hyS hzS hyC hzC hQin hfresh
      have hnil : q.Nil := Walk.length_eq_zero_iff.1 hk
      have huz : u = z := hnil.eq
      have hu_not : u ∉ s := hfresh u (by
        rw [(Walk.nil_iff_support_eq (p := q)).1 hnil]; simp)
      let f : V → Fin n := fun t => if ht : t ∈ s then Cs ⟨t, ht⟩ else 0
      have himg : ((G.neighborFinset u ∩ s).image f).card < n := by
        have hyN : y ∈ G.neighborFinset u ∩ s :=
          Finset.mem_inter.2 ⟨(mem_neighborFinset _ _ _).2 (huz ▸ hyzAdj.symm), hyS⟩
        have hsN : star z ∈ G.neighborFinset u ∩ s :=
          Finset.mem_inter.2 ⟨(mem_neighborFinset _ _ _).2
            (huz ▸ hstarAdj z hzQ), hzS⟩
        have hyne : y ≠ star z := fun h =>
          (Set.notMem_of_mem_compl (hstarQc z hzQ)) (h ▸ hyQ)
        have hfy : f y = a := by simp [f, hyS, hyC]
        have hfs : f (star z) = a := by simp [f, hzS, hzC]
        have hcoll : f y = f (star z) := hfy.trans hfs.symm
        by_cases hlt : (G.neighborFinset u ∩ s).card < n
        · exact Finset.card_image_le.trans_lt hlt
        · have hcardNs : (G.neighborFinset u ∩ s).card = n := by
            have : (G.neighborFinset u ∩ s).card ≤ n :=
              (Finset.card_le_card Finset.inter_subset_left).trans
                (huz ▸ hdeg z hzQ)
            omega
          have hnotInj : ¬ Set.InjOn f ↑(G.neighborFinset u ∩ s) := fun hInj =>
            hyne (hInj hyN hsN hcoll)
          refine Nat.lt_of_le_of_ne
            (Finset.card_image_le.trans (le_of_eq hcardNs)) fun heq => hnotInj ?_
          exact Finset.card_image_iff.1 (heq.trans hcardNs.symm)
      have hcolz := Colorable.of_induce_insert_image (C := Cs) (v := u)
        (by simpa [f] using himg)
      have hsets : s ∪ q.support.toFinset = insert u s := by
        rw [(Walk.nil_iff_support_eq (p := q)).1 hnil]
        change s ∪ {u} = insert u s
        rw [Finset.union_comm, ← Finset.insert_eq]
      exact hsets ▸ hcolz
    | succ k ih =>
      intro u q hk hq s Cs hyS hzS hyC hzC hQin hfresh
      have hnnil : ¬ q.Nil := by
        rw [Walk.not_nil_iff_lt_length]; omega
      obtain ⟨v, hadj, q', rfl⟩ := Walk.not_nil_iff.1 hnnil
      have hq' : q'.IsPath := ((Walk.cons_isPath_iff hadj q').1 hq).1
      have hu_not_q' : u ∉ q'.support := ((Walk.cons_isPath_iff hadj q').1 hq).2
      have huQ : u ∈ Q := hQin u (by simp [Walk.support_cons])
      have hu_not : u ∉ s := hfresh u (by simp [Walk.support_cons])
      have hlen' : q'.length = k := by simp [Walk.length_cons] at hk; omega
      -- Colour `u`; the next path vertex `v` is still uncoloured.
      have hv_fresh : v ∉ s := hfresh v (by simp [Walk.support_cons])
      have hlt : (G.neighborFinset u ∩ s).card < n := by
        have hvN : v ∈ G.neighborFinset u := (mem_neighborFinset _ _ _).2 hadj
        have hsub : G.neighborFinset u ∩ s ⊆ (G.neighborFinset u).erase v := by
          intro t ht
          exact Finset.mem_erase.2 ⟨fun he => hv_fresh (he ▸ (Finset.mem_inter.1 ht).2),
            (Finset.mem_inter.1 ht).1⟩
        have hle := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hvN] at hle
        have := hdeg u huQ
        omega
      obtain ⟨Cs', hpres⟩ := exists_coloring_induce_insert hu_not Cs hlt
      have hyS' : y ∈ insert u s := Finset.mem_insert_of_mem hyS
      have hzS' : star z ∈ insert u s := Finset.mem_insert_of_mem hzS
      have hyC' : Cs' ⟨y, hyS'⟩ = a := (hpres y hyS).trans hyC
      have hzC' : Cs' ⟨star z, hzS'⟩ = a := (hpres (star z) hzS).trans hzC
      have hsets : s ∪ (Walk.cons hadj q').support.toFinset =
          insert u s ∪ q'.support.toFinset := by
        rw [Walk.support_cons, List.toFinset_cons, Finset.union_insert, Finset.insert_union]
      rw [hsets]
      exact ih q' hlen' hq' (insert u s) Cs' hyS' hzS' hyC' hzC'
        (fun x hx => hQin x (by simp [Walk.support_cons, hx]))
        (fun x hx => by
          simp only [Finset.mem_insert, not_or]
          exact ⟨fun h => hu_not_q' (h ▸ hx),
            hfresh x (by simp [Walk.support_cons, hx])⟩)
  cases p with
  | nil => exact (hyzAdj.ne rfl).elim
  | cons hadj q =>
    -- `p` starts at already-coloured `y`; colour the suffix `q`.
    have hq : q.IsPath := ((Walk.cons_isPath_iff hadj q).1 hp).1
    have hy_not_q : y ∉ q.support := ((Walk.cons_isPath_iff hadj q).1 hp).2
    have hfinal := along q.length q rfl hq sY Cy (by simp [sY]) hzstar_mem hCy_y hCy_zstar
      (fun v hv => by
        have : v ∈ (Walk.cons hadj q).support.toFinset := by
          simp [Walk.support_cons, List.mem_toFinset] at hv ⊢; exact Or.inr hv
        simpa [← hspan] using this)
      (fun v hv => by
        simp only [sY, Finset.mem_insert, not_or]
        exact ⟨fun hvy => hy_not_q (hvy ▸ hv), by
          have hvQ : v ∈ Q := by
            have : v ∈ (Walk.cons hadj q).support.toFinset := by
              simp [Walk.support_cons, List.mem_toFinset] at hv ⊢; exact Or.inr hv
            simpa [← hspan] using this
          exact Finset.notMem_compl.2 hvQ⟩)
    have hsets : sY ∪ q.support.toFinset = Finset.univ := by
      ext x
      constructor
      · intro; exact Finset.mem_univ _
      · intro _
        by_cases hxQ : x ∈ Q
        · -- `x` lies on the spanning path `y :: q.support`.
          have hxsup : x ∈ (Walk.cons hadj q).support.toFinset := by
            rwa [hspan]
          refine Finset.mem_union.2 ?_
          have hxmem : x = y ∨ x ∈ q.support.toFinset := by
            simpa [Walk.support_cons, List.toFinset_cons, Finset.mem_insert] using hxsup
          rcases hxmem with rfl | hxmem
          · exact Or.inl (Finset.mem_insert_self _ _)
          · exact Or.inr hxmem
        · exact Finset.mem_union.2 (Or.inl (Finset.mem_insert_of_mem (Finset.mem_compl.2 hxQ)))
    rw [hsets, Finset.coe_univ] at hfinal
    exact (colorable_congr G.induceUnivIso).1 hfinal

/-- Clique-block assembly of Rabern surgery. -/
private theorem brooksSurgery_clique
    {V : Type u} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    {Δ : ℕ} (hΔ3 : 3 ≤ Δ) (hcf : G.CliqueFree (Δ + 1))
    (hH : ¬ cliqueMinusEdge (Δ - 1) ⊑ G) (hreg' : G.IsRegularOfDegree Δ)
    {I : Set V} (hI : Maximal G.IsIndepSet I) [DecidablePred (· ∈ I)]
    {k : ℕ} (hcardV : Fintype.card V ≤ k + 1)
    (ih : ∀ {V : Type u} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      Fintype.card V ≤ k → G.CliqueFree (G.maxDegree + 1) →
        (G.maxDegree = 2 → ¬G.HasOddCycle) → G.Colorable G.maxDegree)
    (Q : Set V) [DecidablePred (· ∈ Q)]
    (hQI : Q ⊆ (Iᶜ : Set V)) (hQcard : Q.ncard = Δ) (hQclique : G.IsClique Q) :
    G.Colorable Δ := by
  classical
  let Qf : Finset V := Q.toFinset
  have hQf_coe : (Qf : Set V) = Q := Set.coe_toFinset _
  have hQf_card : Qf.card = Δ := by
    rw [← Set.ncard_eq_toFinset_card' Q, hQcard]
  have hQcard_f : Fintype.card ↥Q = Δ := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hQcard]
  have hQreg : (G.induce Q).IsRegularOfDegree (Δ - 1) :=
    isRegularOfDegree_induce_of_isClique hQclique hQcard_f
  have hQne : Nonempty ↥Q :=
    Set.Nonempty.to_subtype ((Set.ncard_pos).1 (by omega : 0 < Q.ncard))
  have hQconn : (G.induce Q).Connected := connected_induce_of_isClique (Q := Q) hQclique
  have hstarU : ∀ v ∈ Q, ∃! w, w ∈ I ∧ G.Adj v w := fun v hv =>
    existsUnique_adj_mem_of_isRegular (by omega) hreg' hI hQI hQreg v hv
  let star : V → V := fun v =>
    if hv : v ∈ Q then Classical.choose (hstarU v hv).exists else v
  have hstar : ∀ v ∈ Q, star v ∈ I ∧ G.Adj v (star v) := by
    intro v hv
    simpa [star, hv] using Classical.choose_spec (hstarU v hv).exists
  have hstar_ne : ∃ y ∈ Q, ∃ z ∈ Q, star y ≠ star z := by
    by_contra h
    push Not at h
    obtain ⟨y0⟩ := hQne
    have hwI : star ↑y0 ∈ I := (hstar y0 y0.property).1
    have hadj : ∀ v ∈ Qf, G.Adj v (star ↑y0) := fun v hv => by
      have hvQ : v ∈ Q := by simpa [← hQf_coe] using hv
      exact (h v hvQ ↑y0 y0.property) ▸ (hstar v hvQ).2
    have : G.IsNClique (Δ + 1) (Qf ∪ {star ↑y0}) :=
      isNClique_of_const_star hQf_card (by simpa [hQf_coe] using hQclique)
        (by simpa [hQf_coe] using hQI) hwI hadj (hreg' _)
    exact hcf _ this
  obtain ⟨y0, hy0, z0, hz0, hne0⟩ := hstar_ne
  obtain ⟨y, z, hyzAdj, hstars_ne⟩ :=
    Connected.exists_adj_ne_of_ne hQconn (fun v : ↥Q => star ↑v)
      (show star ↑(⟨y0, hy0⟩ : ↥Q) ≠ star ↑(⟨z0, hz0⟩ : ↥Q) from hne0)
  set ystar := star ↑y
  set zstar := star ↑z
  have hyAdj : G.Adj ↑y ystar := (hstar _ y.property).2
  have hzAdj : G.Adj ↑z zstar := (hstar _ z.property).2
  have hystar_Qc : ystar ∈ (Qᶜ : Set V) := fun h =>
    absurd (hstar _ y.property).1 (Set.notMem_of_mem_compl (hQI h))
  have hzstar_Qc : zstar ∈ (Qᶜ : Set V) := fun h =>
    absurd (hstar _ z.property).1 (Set.notMem_of_mem_compl (hQI h))
  have hcardQc : Fintype.card ↥(Qᶜ : Set V) ≤ k := by
    have := Fintype.card_compl_set Q
    omega
  obtain ⟨Cstar⟩ := colorable_surgery_graph (G := G) hΔ3 hH hreg' hcardQc ih
    hystar_Qc hzstar_Qc hstars_ne y.property z.property hyAdj hzAdj
  let C : (G.induce (Qᶜ : Set V)).Coloring (Fin Δ) :=
    Cstar.comp (.ofLE le_sup_left)
  have hneC :
      C ⟨ystar, hystar_Qc⟩ ≠ C ⟨zstar, hzstar_Qc⟩ := by
    have hadj :
        (G.induce (Qᶜ : Set V) ⊔
          edge (⟨ystar, hystar_Qc⟩ : ↥(Qᶜ : Set V)) ⟨zstar, hzstar_Qc⟩).Adj
          ⟨ystar, hystar_Qc⟩ ⟨zstar, hzstar_Qc⟩ := by
      refine Or.inr ?_
      rw [edge_adj]
      exact ⟨Or.inl ⟨rfl, rfl⟩, fun h => hstars_ne (congrArg Subtype.val h)⟩
    simpa [C] using Cstar.valid hadj
  exact Colorable.of_clique_block_with_stars hQclique hQcard hQI C star hstar
    (fun v hv w hw hadj =>
      eq_star_of_adj_mem_compl hreg' (by omega) hQI hQreg hv hw hadj (hstar v hv))
    y.property z.property (by simpa [ystar, zstar] using hneC)

set_option maxHeartbeats 800000 in
-- Cycle surgery transports support, adjacency and induced colorings simultaneously.

/-- Longer odd-cycle assembly of Rabern surgery (`C₅`, `C₇`, …). -/
private theorem brooksSurgery_longOddCycle
    {V : Type u} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    {Δ : ℕ} (hΔeq : Δ = 3) (hΔ3 : 3 ≤ Δ) (_hcf : G.CliqueFree (Δ + 1))
    (hH : ¬ cliqueMinusEdge (Δ - 1) ⊑ G) (hreg' : G.IsRegularOfDegree Δ)
    {I : Set V} (hI : Maximal G.IsIndepSet I) [DecidablePred (· ∈ I)]
    {k : ℕ} (hcardV : Fintype.card V ≤ k + 1)
    (ih : ∀ {V : Type u} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      Fintype.card V ≤ k → G.CliqueFree (G.maxDegree + 1) →
        (G.maxDegree = 2 → ¬G.HasOddCycle) → G.Colorable G.maxDegree)
    (hΔ2 : (G.induce (Iᶜ : Set V)).maxDegree = 2)
    {v0 : ↥(Iᶜ : Set V)} {c : (G.induce (Iᶜ : Set V)).Walk v0 v0}
    (hc : c.IsCycle) (hlen : Odd c.length) (htri : c.length ≠ 3) :
    G.Colorable Δ := by
  classical
  have hlen_ge : 5 ≤ c.length := by
    have h3le := hc.three_le_length
    rcases hlen with ⟨t, ht⟩
    omega
  let φ : G.induce (Iᶜ : Set V) →g G := (Embedding.induce (G := G) (Iᶜ : Set V)).toHom
  let cG : G.Walk (φ v0) (φ v0) := c.map φ
  have hcG : cG.IsCycle :=
    (Walk.isCycle_map_iff_of_injective (G := G.induce (Iᶜ : Set V)) (G' := G)
      Subtype.val_injective).2 hc
  let Qf : Finset V := cG.support.toFinset
  let Q : Set V := ↑Qf
  have : DecidablePred (· ∈ Q) := Classical.decPred _
  have hQI : Q ⊆ (Iᶜ : Set V) := by
    intro x hx
    have hx' : x ∈ cG.support := List.mem_toFinset.1 (by simpa [Q, Qf] using hx)
    have hx'' : x ∈ c.support.map φ := by simpa [cG, Walk.support_map] using hx'
    rcases List.mem_map.1 hx'' with ⟨y, _, rfl⟩
    exact y.property
  have hQcard_len : Q.ncard = c.length := by
    rw [Set.ncard_coe_finset]
    change cG.support.toFinset.card = c.length
    rw [hcG.support_toFinset_card]
    simp [cG, Walk.length_map]
  have hQne : Nonempty ↥Q :=
    Set.Nonempty.to_subtype ((Set.ncard_pos).1 (by omega : 0 < Q.ncard))
  have mem_support_of_mem_Q {x : V} (hx : x ∈ Q) : x ∈ cG.support :=
    List.mem_toFinset.1 (by simpa [Q, Qf] using hx)
  have mem_Q_of_mem_support {x : V} (hx : x ∈ cG.support) : x ∈ Q := by
    simpa [Q, Qf] using List.mem_toFinset.2 hx
  -- 2-regularity under maxDegree 2.
  have hQreg : (G.induce Q).IsRegularOfDegree (Δ - 1) := by
    rw [show Δ - 1 = 2 by omega]
    intro v
    refine le_antisymm ?_ ?_
    · have hvI : (v : V) ∈ (Iᶜ : Set V) := hQI v.property
      let vI : ↥(Iᶜ : Set V) := ⟨↑v, hvI⟩
      have hsub :
          ((G.induce Q).neighborFinset v).map (Function.Embedding.subtype (· ∈ Q)) ⊆
            ((G.induce (Iᶜ : Set V)).neighborFinset vI).map
              (Function.Embedding.subtype (· ∈ (Iᶜ : Set V))) := by
        intro x hx
        rcases Finset.mem_map.1 hx with ⟨a, ha, rfl⟩
        have hadj : G.Adj ↑v ↑a := (mem_neighborFinset (G.induce Q) _ _).1 ha
        refine Finset.mem_map.2 ⟨⟨↑a, hQI a.property⟩, ?_, rfl⟩
        exact (mem_neighborFinset (G.induce (Iᶜ : Set V)) _ _).2 hadj
      have hle := Finset.card_le_card hsub
      rw [Finset.card_map, Finset.card_map, card_neighborFinset_eq_degree,
        card_neighborFinset_eq_degree] at hle
      exact hle.trans ((G.induce (Iᶜ : Set V)).degree_le_maxDegree vI |>.trans_eq hΔ2)
    · have hvsupp : (v : V) ∈ cG.support := mem_support_of_mem_Q v.property
      have hn : (cG.toSubgraph.neighborSet ↑v).ncard = 2 :=
        hcG.ncard_neighborSet_toSubgraph_eq_two hvsupp
      let N := (cG.toSubgraph.neighborSet ↑v).toFinset
      have hNcard : N.card = 2 := by simpa [N, ← Set.ncard_eq_toFinset_card'] using hn
      have hsub : N ⊆ ((G.induce Q).neighborFinset v).map
          (Function.Embedding.subtype (· ∈ Q)) := by
        intro w hw
        have hadj : cG.toSubgraph.Adj ↑v w := by simpa [N, Set.mem_toFinset] using hw
        have hwsupp : w ∈ cG.support :=
          cG.mem_verts_toSubgraph.1 (cG.toSubgraph.edge_vert hadj.symm)
        refine Finset.mem_map.2 ⟨⟨w, mem_Q_of_mem_support hwsupp⟩, ?_, rfl⟩
        exact (mem_neighborFinset (G.induce Q) _ _).2 (cG.toSubgraph.adj_sub hadj)
      have hle := Finset.card_le_card hsub
      rwa [hNcard, Finset.card_map, card_neighborFinset_eq_degree] at hle
  have hQconn : (G.induce Q).Connected := by
    refine (connected_iff _).2 ⟨?_, hQne⟩
    intro a b
    have ha : ↑a ∈ cG.support := mem_support_of_mem_Q a.property
    have hb : ↑b ∈ cG.support := mem_support_of_mem_Q b.property
    let cRot := cG.rotate ↑a ha
    have hb' : ↑b ∈ cRot.support := (Walk.mem_support_rotate_iff _ _ _).2 hb
    let pG := cRot.takeUntil ↑b hb'
    have hpsupp : ∀ x ∈ pG.support, x ∈ Q := fun x hx =>
      mem_Q_of_mem_support ((Walk.mem_support_rotate_iff _ _ _).1
        (Walk.support_takeUntil_subset_support cRot hb' hx))
    exact ⟨pG.induce Q hpsupp⟩
  have hΔ1 : 1 ≤ Δ := by simp [hΔeq]
  have hstarU : ∀ v ∈ Q, ∃! w, w ∈ I ∧ G.Adj v w := fun v hv =>
    existsUnique_adj_mem_of_isRegular hΔ1 hreg' hI hQI (by convert hQreg) v hv
  let star : V → V := fun v =>
    if hv : v ∈ Q then Classical.choose (hstarU v hv).exists else v
  have hstar : ∀ v ∈ Q, star v ∈ I ∧ G.Adj v (star v) := by
    intro v hv
    simpa [star, hv] using Classical.choose_spec (hstarU v hv).exists
  have hstar_ne : ∃ y ∈ Q, ∃ z ∈ Q, star y ≠ star z := by
    by_contra h
    push Not at h
    obtain ⟨y0⟩ := hQne
    have hadjAll : ∀ v ∈ Qf, G.Adj v (star ↑y0) := fun v hv => by
      have hvQ : v ∈ Q := by simpa [Q] using hv
      exact (h v hvQ ↑y0 y0.property) ▸ (hstar v hvQ).2
    have hcard_le : Qf.card ≤ G.degree (star ↑y0) := by
      have hsub : Qf ⊆ G.neighborFinset (star ↑y0) := fun v hv =>
        (mem_neighborFinset _ _ _).2 (hadjAll v hv).symm
      exact (Finset.card_le_card hsub).trans_eq (by rw [card_neighborFinset_eq_degree])
    have : Q.ncard ≤ Δ := by
      simpa [Set.ncard_coe_finset, Q, hreg' (star ↑y0)] using hcard_le
    omega
  obtain ⟨y0, hy0, z0, hz0, hne0⟩ := hstar_ne
  obtain ⟨y, z, hyzAdjQ, hstars_ne⟩ :=
    Connected.exists_adj_ne_of_ne hQconn (fun v : ↥Q => star ↑v)
      (show star ↑(⟨y0, hy0⟩ : ↥Q) ≠ star ↑(⟨z0, hz0⟩ : ↥Q) from hne0)
  set ystar := star ↑y
  set zstar := star ↑z
  have hyAdj : G.Adj ↑y ystar := (hstar _ y.property).2
  have hzAdj : G.Adj ↑z zstar := (hstar _ z.property).2
  have hystar_Qc : ystar ∈ (Qᶜ : Set V) := fun h =>
    absurd (hstar _ y.property).1 (Set.notMem_of_mem_compl (hQI h))
  have hzstar_Qc : zstar ∈ (Qᶜ : Set V) := fun h =>
    absurd (hstar _ z.property).1 (Set.notMem_of_mem_compl (hQI h))
  have hcardQc : Fintype.card ↥(Qᶜ : Set V) ≤ k := by
    have hsplit := Fintype.card_compl_set Q
    have hQcardF : Fintype.card ↥Q = Q.ncard := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    have : 1 ≤ Fintype.card ↥Q := by rw [hQcardF]; omega
    omega
  obtain ⟨Cstar⟩ := colorable_surgery_graph (G := G) hΔ3 hH hreg' hcardQc ih
    hystar_Qc hzstar_Qc hstars_ne y.property z.property hyAdj hzAdj
  let C : (G.induce (Qᶜ : Set V)).Coloring (Fin Δ) :=
    Cstar.comp (.ofLE le_sup_left)
  have hneC :
      C ⟨ystar, hystar_Qc⟩ ≠ C ⟨zstar, hzstar_Qc⟩ := by
    have hadj :
        (G.induce (Qᶜ : Set V) ⊔
          edge (⟨ystar, hystar_Qc⟩ : ↥(Qᶜ : Set V)) ⟨zstar, hzstar_Qc⟩).Adj
          ⟨ystar, hystar_Qc⟩ ⟨zstar, hzstar_Qc⟩ := by
      refine Or.inr ?_
      rw [edge_adj]
      exact ⟨Or.inl ⟨rfl, rfl⟩, fun h => hstars_ne (congrArg Subtype.val h)⟩
    simpa [C] using Cstar.valid hadj
  -- Spanning cycle in `induce Q` based at `y`.
  have hy_supp : ↑y ∈ cG.support := mem_support_of_mem_Q y.property
  let cGy : G.Walk ↑y ↑y := cG.rotate ↑y hy_supp
  have hcGy : cGy.IsCycle := hcG.rotate hy_supp
  have hsuppGy : ∀ x ∈ cGy.support, x ∈ Q := fun x hx =>
    mem_Q_of_mem_support ((Walk.mem_support_rotate_iff _ _ _).1 hx)
  let cQ : (G.induce Q).Walk y y := cGy.induce Q hsuppGy
  have hcQ : cQ.IsCycle := by
    have hmap : cQ.map (Embedding.induce (G := G) Q).toHom = cGy := by
      simpa [cQ] using Walk.map_induce cGy hsuppGy
    exact (Walk.isCycle_map_iff_of_injective (G := G.induce Q) (G' := G)
      Subtype.val_injective).1 (hmap.symm ▸ hcGy)
  have hspanQ : ∀ t : ↥Q, t ∈ cQ.support := by
    intro t
    have ht : ↑t ∈ cGy.support :=
      (Walk.mem_support_rotate_iff _ _ _).2 (mem_support_of_mem_Q t.property)
    simpa [cQ, Walk.support_induce, List.mem_attachWith] using ht
  have hyzAdjG : G.Adj ↑y ↑z := hyzAdjQ
  -- Cycle subgraph neighbours at `y` coincide with `induce Q` neighbours.
  have hadj_cycleG : cGy.toSubgraph.Adj ↑y ↑z := by
    have hnY : (cGy.toSubgraph.neighborSet ↑y).ncard = 2 :=
      hcGy.ncard_neighborSet_toSubgraph_eq_two cGy.start_mem_support
    have himage :
        cGy.toSubgraph.neighborSet ↑y ⊆
          Subtype.val '' ((G.induce Q).neighborSet y) := by
      intro w hw
      have hadj : cGy.toSubgraph.Adj ↑y w := hw
      have hwsupp : w ∈ cGy.support :=
        cGy.mem_verts_toSubgraph.1 (cGy.toSubgraph.edge_vert hadj.symm)
      refine ⟨⟨w, hsuppGy w hwsupp⟩, ?_, rfl⟩
      exact (mem_neighborSet (G.induce Q) _ _).2 (cGy.toSubgraph.adj_sub hadj)
    have hcard_image :
        (Subtype.val '' ((G.induce Q).neighborSet y)).ncard = 2 := by
      have hdeg : (G.induce Q).degree y = 2 := by
        simpa [show Δ - 1 = 2 by omega] using hQreg y
      rw [Set.ncard_image_of_injective _ Subtype.val_injective]
      have : ((G.induce Q).neighborSet y).ncard = (G.induce Q).degree y := by
        rw [Set.ncard_eq_toFinset_card', ← card_neighborFinset_eq_degree]
        rfl
      rw [this, hdeg]
    have heq : cGy.toSubgraph.neighborSet ↑y =
        Subtype.val '' ((G.induce Q).neighborSet y) :=
      Set.eq_of_subset_of_ncard_le himage (by rw [hcard_image, hnY]) (Set.toFinite _)
    exact (heq ▸ ⟨z, (mem_neighborSet _ _ _).2 hyzAdjQ, rfl⟩ :
      ↑z ∈ cGy.toSubgraph.neighborSet ↑y)
  have hadj_cycleQ : cQ.toSubgraph.Adj y z := by
    have hmap : cQ.map (Embedding.induce (G := G) Q).toHom = cGy := by
      simpa [cQ] using Walk.map_induce cGy hsuppGy
    have heq : cGy.toSubgraph =
        cQ.toSubgraph.map (Embedding.induce (G := G) Q).toHom := by
      rw [← hmap]
      exact Walk.toSubgraph_map (Embedding.induce (G := G) Q).toHom cQ
    have h := hadj_cycleG
    rw [heq, Subgraph.map_adj] at h
    obtain ⟨y', z', hadj, hy', hz'⟩ := h
    obtain rfl := Subtype.ext hy'
    obtain rfl := Subtype.ext hz'
    exact hadj
  obtain ⟨cQ', hcQ', hsnd, hverts⟩ := hcQ.exists_isCycle_snd_verts_eq hadj_cycleQ
  have hspanQ' : ∀ t : ↥Q, t ∈ cQ'.support := fun t => by
    rw [← Walk.mem_verts_toSubgraph, hverts, Walk.mem_verts_toSubgraph]
    exact hspanQ t
  obtain ⟨pQ0, hpQ0⟩ :=
    exists_isHamiltonian_walk_of_isCycle_snd (c := cQ') hcQ' hspanQ'
  let pQ : (G.induce Q).Walk y z := by
    rw [← hsnd]; exact pQ0
  have hpQ : pQ.IsHamiltonian := by
    subst hsnd; exact hpQ0
  let p : G.Walk ↑y ↑z := pQ.map (Embedding.induce (G := G) Q).toHom
  have hp : p.IsPath :=
    (Walk.isPath_map_iff_of_injective Subtype.val_injective).2 hpQ.isPath
  have hspan : p.support.toFinset = Qf := by
    ext x
    constructor
    · intro hx
      have hxsup : x ∈ (pQ.map (Embedding.induce (G := G) Q).toHom).support := by
        simpa [p] using List.mem_toFinset.1 hx
      rw [Walk.support_map] at hxsup
      rcases List.mem_map.1 hxsup with ⟨x', _, rfl⟩
      simpa [Q, Qf] using x'.property
    · intro hx
      have hxQ : x ∈ Q := by simpa [Q] using hx
      have hxmem : (⟨x, hxQ⟩ : ↥Q) ∈ pQ.support := hpQ.mem_support _
      refine List.mem_toFinset.2 ?_
      change x ∈ (pQ.map (Embedding.induce (G := G) Q).toHom).support
      rw [Walk.support_map]
      exact List.mem_map.2 ⟨⟨x, hxQ⟩, hxmem, rfl⟩
  have : NeZero Δ := ⟨by omega⟩
  have hstarQc : ∀ v ∈ Qf, star v ∈ ((↑Qf : Set V)ᶜ) := fun v hv => by
    have hvQ : v ∈ Q := by simpa [Q] using hv
    exact fun h => absurd (hstar v hvQ).1 (Set.notMem_of_mem_compl (hQI h))
  have hstarAdj' : ∀ v ∈ Qf, G.Adj v (star v) := fun v hv =>
    (hstar v (by simpa [Q] using hv)).2
  have honly : ∀ v ∈ Qf, ∀ w ∈ ((↑Qf : Set V)ᶜ), G.Adj v w → w = star v :=
    fun v hv w hw hadj =>
      eq_star_of_adj_mem_compl hreg' hΔ1 hQI (by convert hQreg)
        (by simpa [Q] using hv) (by simpa [Q] using hw) hadj
        (hstar v (by simpa [Q] using hv))
  have hdeg : ∀ v ∈ Qf, (G.neighborFinset v).card ≤ Δ := fun v _ => by
    rw [card_neighborFinset_eq_degree, hreg' v]
  let C' : (G.induce ((↑Qf : Set V)ᶜ)).Coloring (Fin Δ) := by convert C
  have hne' :
      C' ⟨star ↑y, hstarQc ↑y (by simpa [Q, Qf] using y.property)⟩ ≠
        C' ⟨star ↑z, hstarQc ↑z (by simpa [Q, Qf] using z.property)⟩ := by
    change C ⟨ystar, hystar_Qc⟩ ≠ C ⟨zstar, hzstar_Qc⟩
    exact hneC
  exact Colorable.of_rabern_path_extension (n := Δ) (Q := Qf) p hp hspan C' star
    hstarQc hstarAdj' honly hyzAdjG hne' hdeg

/-- Core of Rabern's surgery: given a maximal independent set whose deletion yields a Brooks
counterexample containing `K_Δ` or an odd cycle, colour `G` with `Δ` colours. -/
theorem brooksSurgery
    {V : Type u} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    {Δ : ℕ} (hΔdef : Δ = G.maxDegree) (hΔ3 : 3 ≤ Δ)
    (hcf : G.CliqueFree (Δ + 1)) (hH : ¬ cliqueMinusEdge (Δ - 1) ⊑ G)
    (hreg' : G.IsRegularOfDegree Δ)
    {I : Set V} (hI : Maximal G.IsIndepSet I)
    [DecidablePred (· ∈ I)] [Nonempty ↥(Iᶜ : Set V)]
    (hΔ'eq : (G.induce (Iᶜ : Set V)).maxDegree = Δ - 1)
    {k : ℕ} (hcardV : Fintype.card V ≤ k + 1)
    (_hcard' : Fintype.card ↥(Iᶜ : Set V) ≤ k)
    (hQcase : ¬ (G.induce (Iᶜ : Set V)).CliqueFree Δ ∨
      ((G.induce (Iᶜ : Set V)).maxDegree = 2 ∧ (G.induce (Iᶜ : Set V)).HasOddCycle))
    (ih : ∀ {V : Type u} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      Fintype.card V ≤ k → G.CliqueFree (G.maxDegree + 1) →
        (G.maxDegree = 2 → ¬G.HasOddCycle) → G.Colorable G.maxDegree) :
    G.Colorable Δ := by
  classical
  rcases hQcase with hNotCF | ⟨hΔ2, hoddQ⟩
  · obtain ⟨ψ⟩ := (not_cliqueFree_iff_top_isContained Δ).1 hNotCF
    obtain ⟨Q, hQI, hQcard, hQclique⟩ := exists_clique_set_of_copy (I := I) ψ
    exact brooksSurgery_clique (G := G) hΔ3 hcf hH hreg' hI hcardV ih Q hQI hQcard hQclique
  · -- Odd-cycle case: necessarily `Δ = 3`.
    have hΔeq : Δ = 3 := by omega
    obtain ⟨v0, c, hc, hlen⟩ := hoddQ
    by_cases htri : c.length = 3
    · -- Triangle in `G'`: lift to a `K_3` in `G` and use the clique block.
      obtain ⟨s, hs⟩ :=
        (is3Clique_iff_exists_cycle_length_three
          (G := G.induce (Iᶜ : Set V))).2 ⟨v0, c, hc, htri⟩
      let Q : Set V := ↑(Finset.map ⟨Subtype.val, Subtype.val_injective⟩ s)
      have : DecidablePred (· ∈ Q) := Classical.decPred _
      have hQI : Q ⊆ (Iᶜ : Set V) := by
        intro x hx
        have hx' : x ∈ Finset.map ⟨Subtype.val, Subtype.val_injective⟩ s := by
          simpa [Q] using hx
        rcases Finset.mem_map.1 hx' with ⟨⟨_, hxI⟩, _, rfl⟩
        exact hxI
      have hQcard : Q.ncard = Δ := by
        rw [Set.ncard_coe_finset, Finset.card_map, hs.card_eq, hΔeq]
      have hQclique : G.IsClique Q := by
        intro a ha b hb hne
        have ha' : a ∈ Finset.map ⟨Subtype.val, Subtype.val_injective⟩ s := by
          simpa [Q] using ha
        have hb' : b ∈ Finset.map ⟨Subtype.val, Subtype.val_injective⟩ s := by
          simpa [Q] using hb
        rcases Finset.mem_map.1 ha' with ⟨a', haS, rfl⟩
        rcases Finset.mem_map.1 hb' with ⟨b', hbS, rfl⟩
        have hne' : a' ≠ b' := fun h => hne (congrArg Subtype.val h)
        exact hs.isClique haS hbS hne'
      exact brooksSurgery_clique (G := G) hΔ3 hcf hH hreg' hI hcardV ih Q hQI hQcard hQclique
    · -- Longer odd cycle: Rabern path endgame.
      exact brooksSurgery_longOddCycle (G := G) hΔeq hΔ3 hcf hH hreg' hI hcardV ih hΔ2 hc hlen htri




end SimpleGraph

end
