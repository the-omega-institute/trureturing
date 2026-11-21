/- GID: D5/S3/Combinatorics/SpectralGraph/CographVicinalWidth
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/CographVicinalWidth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Vicinal chains under complementation and component cuts. -/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.SetTheory.Cardinal.Finite
import D5.S3.Combinatorics.SpectralGraph.MandalMannaDQDilworthRefutation

/-! # Vicinal chain covers of unions and joins -/

namespace D5.S3.Combinatorics.SpectralGraph.CographVicinalWidth

open SimpleGraph
open MandalMannaDQDilworthRefutation (vicinal HasChainCover dilworthNumber)

private theorem vicinal_iff {V : Type} (G : SimpleGraph V) (u v : V) :
    vicinal G u v ↔ ∀ ⦃x⦄, x ≠ u → x ≠ v → G.Adj u x → G.Adj v x := by
  constructor
  · intro h x _ hx hux
    exact (Set.mem_insert_iff.mp (h hux)).resolve_left hx
  · intro h x hux
    by_cases hx : x = v
    · exact Set.mem_insert_iff.mpr (Or.inl hx)
    · exact Set.mem_insert_of_mem _ (h hux.ne.symm hx hux)

/-- Complementation reverses vicinal comparison. -/
theorem vicinal_compl_iff {V : Type} (G : SimpleGraph V) (u v : V) :
    vicinal Gᶜ u v ↔ vicinal G v u := by
  classical
  simp only [vicinal_iff, compl_adj]
  constructor
  · intro h x hxv hxu hvx
    by_contra hux
    exact (h hxu hxv ⟨Ne.symm hxu, hux⟩).2 hvx
  · intro h x hxu hxv hux
    exact ⟨Ne.symm hxv, fun hvx => hux.2 (h hxv hxu hvx)⟩

/-- Each chain assignment still works after complementation. -/
theorem hasChainCover_compl_iff {V : Type} (G : SimpleGraph V) (k : ℕ) :
    HasChainCover Gᶜ k ↔ HasChainCover G k := by
  unfold HasChainCover
  simp only [vicinal_compl_iff, or_comm]

private theorem exists_chainCover {V : Type} [Finite V] (G : SimpleGraph V) :
    ∃ k, HasChainCover G k := by
  classical
  let := Fintype.ofFinite V
  exact ⟨_, Fintype.equivFin V, fun u v h => by
    obtain rfl := (Fintype.equivFin V).injective h
    exact Or.inl fun _ hx => Set.mem_insert_of_mem _ hx⟩

/-- The least feasible chain-cover size on a finite graph, as a natural number. -/
noncomputable def width {V : Type} [Finite V] (G : SimpleGraph V) : ℕ := by
  classical
  exact Nat.find (exists_chainCover G)

private theorem cover_width {V : Type} [Finite V] (G : SimpleGraph V) :
    HasChainCover G (width G) := by
  classical
  exact Nat.find_spec (exists_chainCover G)

private theorem width_le {V : Type} [Finite V] {G : SimpleGraph V} {k : ℕ}
    (h : HasChainCover G k) : width G ≤ k := by
  classical
  exact Nat.find_min' (exists_chainCover G) h

/-- On finite graphs the existing extended width is attained at the natural width. -/
theorem dilworthNumber_eq_width {V : Type} [Finite V] (G : SimpleGraph V) :
    dilworthNumber G = (width G : ℕ∞) := by
  apply le_antisymm
  · exact sInf_le ⟨width G, rfl, cover_width G⟩
  · apply le_sInf
    rintro k ⟨n, rfl, hn⟩
    exact_mod_cast width_le hn

/-- The natural width is invariant under complementation. -/
theorem width_compl {V : Type} [Finite V] (G : SimpleGraph V) :
    width Gᶜ = width G :=
  le_antisymm (width_le ((hasChainCover_compl_iff G _).2 (cover_width G)))
    (width_le ((hasChainCover_compl_iff G _).1 (cover_width Gᶜ)))

private theorem width_pos {V : Type} [Finite V] [Nonempty V] (G : SimpleGraph V) :
    1 ≤ width G := by
  obtain ⟨c, _⟩ := cover_width G
  obtain ⟨v⟩ := ‹Nonempty V›
  exact (Nat.zero_le _).trans_lt (c v).isLt

/-- The width of a graph on one vertex is one. -/
theorem width_singleton {V : Type} [Finite V] [Nonempty V] [Subsingleton V]
    (G : SimpleGraph V) : width G = 1 := by
  apply le_antisymm _ (width_pos G)
  exact width_le ⟨fun _ => 0, fun u v _ => by
    obtain rfl := Subsingleton.elim u v
    exact Or.inl fun _ hx => Set.mem_insert_of_mem _ hx⟩

private theorem vicinal_component_iff {V : Type} {G : SimpleGraph V}
    (C : G.ConnectedComponent) (u v : C.supp) :
    vicinal (G.induce C.supp) u v ↔ vicinal G u.val v.val := by
  constructor
  · intro h x hx
    let y : C.supp := ⟨x, C.mem_supp_of_adj_mem_supp u.property hx⟩
    rcases Set.mem_insert_iff.mp (h (show (G.induce C.supp).Adj u y from hx)) with hy | hy
    · exact Set.mem_insert_iff.mpr (Or.inl (congrArg Subtype.val hy))
    · exact Set.mem_insert_of_mem _ hy
  · intro h x hx
    rcases Set.mem_insert_iff.mp (h (show G.Adj u.val x.val from hx)) with he | he
    · exact Set.mem_insert_iff.mpr (Or.inl (Subtype.ext he))
    · exact Set.mem_insert_of_mem _ he

/-- Components with at least two actual vertices are the summands in the width cut. -/
abbrev NontrivialComponent {V : Type} (G : SimpleGraph V) :=
  {C : G.ConnectedComponent // Nontrivial C.supp}

private theorem not_vicinal_of_component_ne {V : Type} {G : SimpleGraph V}
    (C D : NontrivialComponent G) (hCD : C ≠ D) (u : C.val.supp) (v : D.val.supp) :
    ¬vicinal G u.val v.val := by
  let := C.property
  obtain ⟨z, hz⟩ := C.val.connected_toSimpleGraph.preconnected.exists_adj_of_nontrivial u
  intro h
  rcases Set.mem_insert_iff.mp (h (show G.Adj u.val z.val from hz)) with he | he
  · exact hCD (Subtype.ext (C.val.eq_of_common_vertex z.property (he ▸ v.property)))
  · exact hCD (Subtype.ext (C.val.eq_of_common_vertex z.property
      (D.val.mem_supp_of_adj_mem_supp v.property he)))

private theorem isolated_vicinal {V : Type} {G : SimpleGraph V} (u v : V)
    (h : ¬Nontrivial (G.connectedComponentMk u).supp) : vicinal G u v := by
  have hs : Subsingleton (G.connectedComponentMk u).supp := by
    simpa only [not_nontrivial_iff_subsingleton] using h
  intro x hx
  have he : (⟨u, rfl⟩ : (G.connectedComponentMk u).supp) =
      ⟨x, ConnectedComponent.connectedComponentMk_eq_of_adj hx.symm⟩ := hs.elim _ _
  exact (hx.ne (congrArg Subtype.val he)).elim

private theorem width_component_le_range {V : Type} [Finite V] {G : SimpleGraph V}
    (C : G.ConnectedComponent) {k : ℕ} (c : V → Fin k)
    (hc : ∀ u v, c u = c v → vicinal G u v ∨ vicinal G v u)
    [Fintype (Set.range (fun u : C.supp => c u.val))] :
    width (G.induce C.supp) ≤ Fintype.card (Set.range (fun u : C.supp => c u.val)) := by
  let e := Fintype.equivFin (Set.range (fun u : C.supp => c u.val))
  apply width_le
  refine ⟨fun u => e ⟨c u.val, ⟨u, rfl⟩⟩, fun u v huv => ?_⟩
  have he := congrArg Subtype.val (e.injective huv)
  exact (hc u.val v.val he).imp ((vicinal_component_iff C u v).2)
    ((vicinal_component_iff C v u).2)

/-- For every finite nonempty graph, add the widths of its nontrivial
components, with one chain available for singleton components. -/
theorem width_components {V : Type} [Finite V] [Nonempty V] (G : SimpleGraph V)
    [Fintype (NontrivialComponent G)] :
    width G = max 1 (∑ C : NontrivialComponent G, width (G.induce C.val.supp)) := by
  classical
  let Child (C : NontrivialComponent G) := G.induce C.val.supp
  let Colors := Σ C : NontrivialComponent G, Fin (width (Child C))
  let e := Fintype.equivFin Colors
  have hsum : Fintype.card Colors = ∑ C : NontrivialComponent G, width (Child C) := by
    simp [Colors]
  change width G = max 1 (∑ C : NontrivialComponent G, width (Child C))
  apply le_antisymm
  · choose c hc using fun C : NontrivialComponent G => cover_width (Child C)
    let n := max 1 (Fintype.card Colors)
    have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
    let assign : V → Fin n := fun u =>
      if hu : Nontrivial (G.connectedComponentMk u).supp then
        Fin.castLE (le_max_right _ _) (e ⟨⟨G.connectedComponentMk u, hu⟩, c _ ⟨u, rfl⟩⟩)
      else ⟨0, hn⟩
    rw [← hsum]
    apply width_le
    refine ⟨assign, fun u v huv => ?_⟩
    by_cases hu : Nontrivial (G.connectedComponentMk u).supp
    · by_cases hv : Nontrivial (G.connectedComponentMk v).supp
      · have hlabels := e.injective (Fin.castLE_injective (le_max_right 1 (Fintype.card Colors))
          (by simpa only [assign, dite_eq_left hu, dite_eq_left hv] using huv))
        let C : NontrivialComponent G := ⟨G.connectedComponentMk u, hu⟩
        let D : NontrivialComponent G := ⟨G.connectedComponentMk v, hv⟩
        have compare (C D : NontrivialComponent G) (a : C.val.supp) (b : D.val.supp)
            (h : (⟨C, c C a⟩ : Colors) = ⟨D, c D b⟩) :
            vicinal G a.val b.val ∨ vicinal G b.val a.val := by
          have he : C = D := congrArg Sigma.fst h
          subst D
          have hchain := hc C a b (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
          exact hchain.imp ((vicinal_component_iff C.val a b).1)
            ((vicinal_component_iff C.val b a).1)
        exact compare C D ⟨u, rfl⟩ ⟨v, rfl⟩ hlabels
      · exact Or.inr (isolated_vicinal v u hv)
    · exact Or.inl (isolated_vicinal u v hu)
  · refine max_le (width_pos G) ?_
    obtain ⟨c, hc⟩ := cover_width G
    let Used (C : NontrivialComponent G) := Set.range (fun u : C.val.supp => c u.val)
    let (C : NontrivialComponent G) : Fintype (Used C) := Fintype.ofFinite _
    let flatten : (Σ C, Used C) → Fin (width G) := fun p => p.2.val
    have hinj : Function.Injective flatten := by
      rintro ⟨C, a, u, hu⟩ ⟨D, b, v, hv⟩ hab
      have he : C = D := by
        by_contra hne
        rcases hc u.val v.val (hu.trans (hab.trans hv.symm)) with h | h
        · exact not_vicinal_of_component_ne C D hne u v h
        · exact not_vicinal_of_component_ne D C (Ne.symm hne) v u h
      subst D
      exact congrArg (Sigma.mk C) (Subtype.ext hab)
    have hcard := Fintype.card_le_of_injective flatten hinj
    rw [Fintype.card_sigma, Fintype.card_fin] at hcard
    exact (Finset.sum_le_sum fun C _ => width_component_le_range C.val c hc).trans hcard

end D5.S3.Combinatorics.SpectralGraph.CographVicinalWidth
