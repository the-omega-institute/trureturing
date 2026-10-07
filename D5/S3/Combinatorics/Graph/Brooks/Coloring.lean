/- GID: D5/S3/Combinatorics/Graph/Brooks/Coloring
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Brooks/Coloring
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Licensed greedy, low-degree extension and gluing lemmas for graph coloring. -/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finset.Max
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring


/-!
This source transplant is from Juan Pablo Traverso Gianini's BrooksSubcubic proof:
https://github.com/Vilin97/lean-pool/tree/91c154506e3d08a1a25e4966c22c99212bf9df54/LeanPool/BrooksSubcubic
Author source: https://github.com/jtraverso/lean-pool/tree/aced439fd4161d118bf167a1e8d10553f28913fe
The complete Apache-2.0 license and NOTICE chain are retained in
`docs/reports/brooks-suppliers/lean-pool-LICENSE.txt` and `lean-pool-NOTICE.txt`.
Packaging is adapted to repository imports; `dif_pos` and `dif_neg` implement
this repository's pinned API for dependent-if reduction.
Retire these transplants when this repository's pinned Mathlib provides equivalent
statements, and replace all consumers by direct applications of those declarations.
-/

/- Source unit: LeanPool/BrooksSubcubic/Greedy.lean. -/
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/


/-!
# Subcubic Brooks theorem: Greedy

Part of the proof that a finite subcubic K₄-free graph is three-colourable.
-/


section

open SimpleGraph Finset

namespace BrooksSubcubic

variable {V : Type*} [Fintype V]

/-- Greedy colouring picking the LEAST unused colour, with control: a vertex whose set of
strictly-lower-ranked neighbours is empty receives colour `0`. -/
theorem greedy_coloring_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk : 0 < k) (rank : V → ℕ) (hrank : Function.Injective rank)
    (h : ∀ v, ((G.neighborFinset v).filter fun w => rank w < rank v).card < k) :
    ∃ c : V → Fin k, (∀ u v, G.Adj u v → c u ≠ c v) ∧
      (∀ v, ((G.neighborFinset v).filter fun w => rank w < rank v).card = 0 → c v = ⟨0, hk⟩) := by
  classical
  have hwf : WellFounded (fun v w : V => rank v < rank w) := by
    constructor
    intro a
    have key : ∀ n, ∀ a, rank a = n → Acc (fun v w : V => rank v < rank w) a := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih => intro a ha; subst ha; exact Acc.intro a fun b hb => ih (rank b) hb b rfl
    exact key (rank a) a rfl
  let f : (v : V) → ((w : V) → rank w < rank v → Fin k) → Fin k := fun v x =>
    let lower : Finset V := (G.neighborFinset v).filter fun w => rank w < rank v
    let used : Finset (Fin k) := lower.attach.image fun ⟨w, hw⟩ => x w (Finset.mem_filter.mp hw).2
    let free : Finset (Fin k) := Finset.univ \ used
    have hfree : free.Nonempty := by
      rw [Finset.sdiff_nonempty]
      intro hsub
      have hcard_le : (Finset.univ : Finset (Fin k)).card ≤ used.card := Finset.card_le_card hsub
      have h1 : used.card ≤ lower.card := (Finset.card_image_le).trans (by rw [Finset.card_attach])
      have h2 : lower.card < k := h v
      rw [Finset.card_univ, Fintype.card_fin] at hcard_le
      omega
    free.min' hfree
  let c : V → Fin k := hwf.fix f
  have hc_eq : ∀ v, c v = f v (fun w _ => c w) := fun v => WellFounded.fix_eq hwf f v
  have hnotused : ∀ v, c v ∉ ((G.neighborFinset v).filter fun w => rank w < rank v).attach.image
      (fun p => c p.1) := by
    intro v hmem
    rw [hc_eq v] at hmem
    have hmin := Finset.min'_mem
      (Finset.univ \ (((G.neighborFinset v).filter fun w => rank w < rank v).attach.image
        (fun p => c p.1)))
      (by
        rw [Finset.sdiff_nonempty]; intro hsub
        have hcard_le := Finset.card_le_card hsub
        have h1 : (((G.neighborFinset v).filter fun w => rank w < rank v).attach.image
            (fun p => c p.1)).card ≤ ((G.neighborFinset v).filter fun w => rank w < rank v).card :=
          (Finset.card_image_le).trans (by rw [Finset.card_attach])
        have h2 := h v
        rw [Finset.card_univ, Fintype.card_fin] at hcard_le
        omega)
    rw [Finset.mem_sdiff] at hmin
    exact hmin.2 hmem
  refine ⟨c, ?_, ?_⟩
  · -- properness
    intro u v huv
    rcases lt_trichotomy (rank u) (rank v) with hlt | heq | hgt
    · have hu_low : u ∈ (G.neighborFinset v).filter fun w => rank w < rank v := by
        rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset]; exact ⟨huv.symm, hlt⟩
      intro hcuv
      apply hnotused v
      rw [Finset.mem_image]
      exact ⟨⟨u, hu_low⟩, Finset.mem_attach _ _, hcuv⟩
    · exact absurd (hrank heq) huv.ne
    · have hv_low : v ∈ (G.neighborFinset u).filter fun w => rank w < rank u := by
        rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset]; exact ⟨huv, hgt⟩
      intro hcuv
      apply hnotused u
      rw [Finset.mem_image]
      exact ⟨⟨v, hv_low⟩, Finset.mem_attach _ _, hcuv.symm⟩
  · -- control: empty lower ⟹ colour 0
    intro v hv0
    have hempty : ((G.neighborFinset v).filter fun w => rank w < rank v) = ∅ :=
      Finset.card_eq_zero.mp hv0
    have himg : (((G.neighborFinset v).filter fun w => rank w < rank v).attach.image
        (fun p => c p.1)) = ∅ := by rw [hempty]; simp
    rw [hc_eq v]
    change (Finset.univ \ (((G.neighborFinset v).filter fun w => rank w < rank v).attach.image
        (fun p => c p.1))).min' _ = ⟨0, hk⟩
    have hmem0 : (⟨0, hk⟩ : Fin k) ∈ Finset.univ \ (((G.neighborFinset v).filter
        fun w => rank w < rank v).attach.image (fun p => c p.1)) :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by rw [himg]; simp⟩
    apply le_antisymm
    · exact Finset.min'_le _ _ hmem0
    · exact Fin.le_def.mpr (Nat.zero_le _)

end BrooksSubcubic
end

/- Source unit: LeanPool/BrooksSubcubic/NonRegular.lean. -/
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/


/-!
# Subcubic Brooks theorem: NonRegular

Part of the proof that a finite subcubic K₄-free graph is three-colourable.
-/


section

open SimpleGraph

namespace BrooksSubcubic

variable {V : Type*} [Fintype V]

/-- Greedy colouring along an injective rank (helper). -/
theorem colorable_of_lower_neighbors_lt (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (rank : V → ℕ) (hrank : Function.Injective rank)
    (h : ∀ v, ((G.neighborFinset v).filter fun w => rank w < rank v).card < k) :
    G.Colorable k := by
  classical
  by_cases hk : 0 < k
  · obtain ⟨c, hc, _⟩ := greedy_coloring_zero G k hk rank hrank h
    exact ⟨⟨c, fun {u v} huv => hc u v huv⟩⟩
  · have : IsEmpty V := ⟨fun v => by have hv := h v; omega⟩
    exact SimpleGraph.Colorable.of_isEmpty k

omit [Fintype V] in
/-- In a connected graph, any `u ≠ v₀` has a neighbour `w`
strictly closer to `v₀` (the second vertex of a geodesic from `u` to `v₀`). -/
theorem exists_closer_neighbor (G : SimpleGraph V)
    (hconn : G.Connected) (v₀ u : V) (hu : u ≠ v₀) :
    ∃ w, G.Adj u w ∧ G.dist v₀ w < G.dist v₀ u := by
  classical
  have hreach : G.Reachable u v₀ := hconn.preconnected u v₀
  obtain ⟨q, hq⟩ := hreach.exists_walk_length_eq_dist
  have hne0 : G.dist u v₀ ≠ 0 := by
    rw [ne_eq, SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable, not_or, not_not]
    exact ⟨hu, hreach⟩
  have hnp : ¬ q.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]; omega
  refine ⟨q.snd, ?_, ?_⟩
  · exact q.adj_snd hnp
  · have htail : G.dist q.snd v₀ ≤ q.tail.length := SimpleGraph.dist_le q.tail
    have hlen : q.tail.length + 1 = q.length := q.length_tail_add_one hnp
    have hc1 : G.dist v₀ q.snd = G.dist q.snd v₀ := SimpleGraph.dist_comm
    have hc2 : G.dist v₀ u = G.dist u v₀ := SimpleGraph.dist_comm
    rw [hc1, hc2, ← hq]
    omega

/-- A connected subcubic graph with a vertex of degree below three is three-colourable. -/
theorem connected_colorable_three_of_exists_degree_lt
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v ≤ 3) (hlow : ∃ v, G.degree v < 3) : G.Colorable 3 := by
  classical
  obtain ⟨v₀, hv₀⟩ := hlow
  set N := Fintype.card V with hN
  let e : V → ℕ := fun x => ((Fintype.equivFin V) x : ℕ)
  have he_lt : ∀ x, e x < N := fun x => ((Fintype.equivFin V) x).isLt
  have he_inj : Function.Injective e := fun a b h => (Fintype.equivFin V).injective (Fin.ext h)
  set rank : V → ℕ := fun x => N * (N - G.dist v₀ x) + e x with hrank_def
  have hrank_inj : Function.Injective rank := by
    intro a b hab
    have hmod : ∀ x, rank x % N = e x := fun x => by
      simp only [hrank_def, Nat.mul_add_mod, Nat.mod_eq_of_lt (he_lt x)]
    have : e a = e b := by rw [← hmod a, ← hmod b, hab]
    exact he_inj this
  have hdist_lt : ∀ u, G.dist v₀ u < N := by
    intro u
    obtain ⟨p, hp, hlen⟩ := (hconn.preconnected v₀ u).exists_path_of_dist
    rw [← hlen]; exact hp.length_lt
  apply colorable_of_lower_neighbors_lt G 3 rank hrank_inj
  intro u
  by_cases hu : u = v₀
  · subst hu
    calc ((G.neighborFinset u).filter fun w => rank w < rank u).card
        ≤ (G.neighborFinset u).card := Finset.card_filter_le _ _
      _ = G.degree u := (G.card_neighborFinset_eq_degree u)
      _ < 3 := hv₀
  · obtain ⟨w, hadj, hwlt⟩ := exists_closer_neighbor G hconn v₀ u hu
    have hblock : N - G.dist v₀ u < N - G.dist v₀ w := by have := hdist_lt u; omega
    have hrank_wu : rank u < rank w := by
      rw [hrank_def]; simp only
      have h1 : N * (N - G.dist v₀ u) + e u < N * (N - G.dist v₀ u) + N := by
        have := he_lt u; omega
      have h2 : N * (N - G.dist v₀ u) + N ≤ N * (N - G.dist v₀ w) := by
        have hb : (N - G.dist v₀ u) + 1 ≤ (N - G.dist v₀ w) := by omega
        calc N * (N - G.dist v₀ u) + N = N * ((N - G.dist v₀ u) + 1) := by ring
          _ ≤ N * (N - G.dist v₀ w) := by gcongr
      omega
    have hwmem : w ∈ G.neighborFinset u := by rw [SimpleGraph.mem_neighborFinset]; exact hadj
    have hsub : ((G.neighborFinset u).filter fun x => rank x < rank u)
        ⊆ (G.neighborFinset u).erase w := by
      intro x hx
      rw [Finset.mem_filter] at hx; rw [Finset.mem_erase]
      refine ⟨?_, hx.1⟩
      rintro rfl; omega
    calc ((G.neighborFinset u).filter fun x => rank x < rank u).card
        ≤ ((G.neighborFinset u).erase w).card := Finset.card_le_card hsub
      _ = G.degree u - 1 := by rw [Finset.card_erase_of_mem hwmem, G.card_neighborFinset_eq_degree]
      _ < 3 := by have := hdeg u; omega

end BrooksSubcubic
end

/- Source unit: LeanPool/BrooksSubcubic/ColouringGlue.lean. -/
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/


/-!
# Subcubic Brooks theorem: ColouringGlue

Part of the proof that a finite subcubic K₄-free graph is three-colourable.
-/


section

open SimpleGraph Finset

namespace BrooksSubcubic

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Glue lemma at a cut vertex.** If A and B cover V, x belongs to both,
no G-edge joins A∖{x} to B∖{x}, and both induced subgraphs
`G[A]`, `G[B]` are 3-colourable, then `G` is 3-colourable. Proof: pick colourings `cA, cB`;
recolour `B` by the transposition `swap (cB x) (cA x)` so both agree at `x`; glue with `A` taking
priority. Every edge lies inside `A` or inside `B` — a cross edge would violate the no-cross
hypothesis — so the glued map inherits properness, and the alignment at `x` handles the boundary. -/
theorem colorable_glue_at_vertex (G : SimpleGraph V)
    (A B : Finset V) (x : V)
    (hcover : A ∪ B = Finset.univ)
    (hxA : x ∈ A) (hxB : x ∈ B)
    (hcross : ∀ u ∈ A, ∀ w ∈ B, u ≠ x → w ≠ x → ¬ G.Adj u w)
    (hA : (G.induce (A : Set V)).Colorable 3)
    (hB : (G.induce (B : Set V)).Colorable 3) :
    G.Colorable 3 := by
  classical
  obtain ⟨cA⟩ := hA
  obtain ⟨cB⟩ := hB
  set α : Fin 3 := cA ⟨x, by exact_mod_cast hxA⟩ with hα
  set β : Fin 3 := cB ⟨x, by exact_mod_cast hxB⟩ with hβ
  set σ : Equiv.Perm (Fin 3) := Equiv.swap β α with hσ
  have hmemB : ∀ v : V, v ∉ A → v ∈ B := by
    intro v hv
    have h : v ∈ A ∪ B := by rw [hcover]; exact Finset.mem_univ v
    exact (Finset.mem_union.mp h).resolve_left hv
  let c : V → Fin 3 := fun v =>
    if hv : v ∈ A then cA ⟨v, by exact_mod_cast hv⟩
    else σ (cB ⟨v, by exact_mod_cast hmemB v hv⟩)
  have hcA_val : ∀ (v : V) (hv : v ∈ A), c v = cA ⟨v, by exact_mod_cast hv⟩ := by
    intro v hv; simp only [c, dif_pos hv]
  have hcB_val : ∀ (v : V) (hv : v ∉ A),
      c v = σ (cB ⟨v, by exact_mod_cast hmemB v hv⟩) := by
    intro v hv; simp only [c, dif_neg hv]
  have hAadj : ∀ (u v : V) (hu : u ∈ A) (hv : v ∈ A), G.Adj u v →
      cA ⟨u, by exact_mod_cast hu⟩ ≠ cA ⟨v, by exact_mod_cast hv⟩ := by
    intro u v hu hv hadj
    exact cA.valid (by simpa using hadj)
  have hBadj : ∀ (u v : V) (hu : u ∈ B) (hv : v ∈ B), G.Adj u v →
      cB ⟨u, by exact_mod_cast hu⟩ ≠ cB ⟨v, by exact_mod_cast hv⟩ := by
    intro u v hu hv hadj
    exact cB.valid (by simpa using hadj)
  have hαβ : α = σ β := by rw [hσ, Equiv.swap_apply_left]
  refine ⟨Coloring.mk c ?_⟩
  intro u v hadj
  by_cases hua : u ∈ A
  · by_cases hva : v ∈ A
    · rw [hcA_val u hua, hcA_val v hva]
      exact hAadj u v hua hva hadj
    · have hvB : v ∈ B := hmemB v hva
      have hvx : v ≠ x := fun h => hva (h ▸ hxA)
      by_cases hux : u = x
      · subst hux
        rw [hcA_val u hua, hcB_val v hva]
        have hxeq : cA ⟨u, by exact_mod_cast hua⟩ = α := by rw [hα]
        rw [hxeq, hαβ]
        intro hcontra
        have hinj : β = cB ⟨v, by exact_mod_cast hvB⟩ := σ.injective hcontra
        exact hBadj u v hxB hvB hadj (by rw [← hβ]; exact hinj)
      · exact absurd hadj (hcross u hua v hvB hux hvx)
  · have huB : u ∈ B := hmemB u hua
    have hux : u ≠ x := fun h => hua (h ▸ hxA)
    by_cases hva : v ∈ A
    · by_cases hvx : v = x
      · subst hvx
        rw [hcA_val v hva, hcB_val u hua]
        have hxeq : cA ⟨v, by exact_mod_cast hva⟩ = α := by rw [hα]
        rw [hxeq, hαβ]
        intro hcontra
        have hinj : cB ⟨u, by exact_mod_cast huB⟩ = β := σ.injective hcontra
        exact hBadj u v huB hxB hadj (by rw [← hβ]; exact hinj)
      · exact absurd hadj.symm (hcross v hva u huB hvx hux)
    · have hvB : v ∈ B := hmemB v hva
      rw [hcB_val u hua, hcB_val v hva]
      intro hcontra
      have hinj : cB ⟨u, by exact_mod_cast huB⟩ = cB ⟨v, by exact_mod_cast hvB⟩ :=
        σ.injective hcontra
      exact hBadj u v huB hvB hadj hinj

end BrooksSubcubic
end

/-!
Low-degree vertex extension from Brian Rabern's BrooksLean:
https://github.com/brianrabern/BrooksLean/blob/1d990050d881327fc79dd51e82ba4449b4e2467d/BrooksLean/VertexLemmas.lean
The complete Apache-2.0 license is retained in
`docs/reports/brooks-suppliers/BrooksLean-LICENSE.txt`.
The same pinned-Mathlib retirement condition applies to this declaration.
-/
universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {n : ℕ}

/-- If deleting a vertex `v` leaves an `n`-colorable graph and `v` has fewer than `n` neighbors,
then `G` itself is `n`-colorable: color `G` with `v` removed, then give `v` one of the colors that
does not appear on any neighbor of `v`. -/
theorem Colorable.of_induce_compl_singleton {v : V} [Fintype (G.neighborSet v)]
    (h : (G.induce {v}ᶜ).Colorable n) (hv : G.degree v < n) : G.Colorable n := by
  classical
  obtain ⟨C⟩ := h
  have : NeZero n := ⟨by lia⟩
  -- Extend `C` to all of `V`; the color it assigns to `v` itself is irrelevant.
  obtain ⟨f, hf⟩ : ∃ f : V → Fin n, ∀ (u : V) (hu : u ≠ v),
      f u = C ⟨u, Set.mem_compl_singleton_iff.2 hu⟩ :=
    ⟨fun u => if hu : u = v then 0 else C ⟨u, Set.mem_compl_singleton_iff.2 hu⟩,
      fun _ hu => dif_neg hu⟩
  -- As `v` has fewer than `n` neighbors, some color `a` is unused on them.
  obtain ⟨a, ha⟩ : ∃ a, a ∉ (G.neighborFinset v).image f := by
    have hlt : ((G.neighborFinset v).image f).card < n := by
      refine lt_of_le_of_lt Finset.card_image_le ?_
      rwa [card_neighborFinset_eq_degree]
    obtain ⟨a, ha⟩ : (((G.neighborFinset v).image f)ᶜ).Nonempty := by
      rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]
      lia
    exact ⟨a, Finset.mem_compl.1 ha⟩
  have key : ∀ {q : V}, G.Adj v q → Function.update f v a v ≠ Function.update f v a q := by
    intro q hq
    rw [Function.update_self, Function.update_of_ne (G.ne_of_adj hq).symm]
    intro hc
    apply ha
    rw [hc]
    exact Finset.mem_image_of_mem f ((G.mem_neighborFinset v q).2 hq)
  have hvalid : ∀ {x y : V}, G.Adj x y →
      Function.update f v a x ≠ Function.update f v a y := by
    intro x y hxy
    rcases eq_or_ne x v with hx | hx
    · rw [hx] at hxy ⊢
      exact key hxy
    rcases eq_or_ne y v with hy | hy
    · rw [hy] at hxy ⊢
      exact (key hxy.symm).symm
    rw [Function.update_of_ne hx, Function.update_of_ne hy, hf x hx, hf y hy]
    exact C.valid hxy
  exact ⟨Coloring.mk (Function.update f v a) hvalid⟩

end SimpleGraph

