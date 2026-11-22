/- GID: D5/S3/Combinatorics/Graph/ZeroForcing/PathConnectedForcing
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/ZeroForcing/PathConnectedForcing
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Hasse]
   utility: none
   digest: The connected forcing polynomial of the path P_n is 2x + sum_(i=2)^n (n-i+1) x^i. -/

import D5.S3.Combinatorics.Graph.ZeroForcing.ConnectedForcingCrossingRefutation
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-! The connected forcing polynomial of the path, Proposition 7.7 of B. Brimkov, Graph Coloring,
Zero Forcing, and Related Problems (PhD thesis, Rice University, 2017): for `n ≥ 2`,
`Z_c(P_n; x) = 2x + Σ_{i=2}^n (n - i + 1) x^i`. The coefficients are the frozen
`ConnectedForcingCrossingRefutation.coefficient` (connected zero forcing sets of each size) for
Mathlib's `pathGraph n`.

`connected_forcing_iff` characterizes the connected forcing sets of `P_n`, `n ≥ 2`: the intervals
with at least two vertices and the two end vertices. A walk in an induced subgraph of the path
passes every intermediate vertex, so a connected set is an interval; an interval with two
vertices forces outward from both ends; an end vertex forces its unique neighbour; an interior
vertex alone forces nothing.

admission_basis: escape-witness. Escape witnesses: walk_hits with convex_of_connected (connected
induced subgraphs of the path are intervals), interval_connected (intervals induce connected
subgraphs), forcing_interval and forcing_end (the forcing
chains), interior_black (an interior singleton stays alone), coeff_ge and coeff_one (the
interval counts). -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.Graph.ZeroForcing.PathConnectedForcing

open SimpleGraph
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThree
open D5.S3.Combinatorics.Graph.ZeroForcing.ConnectedForcingCrossingRefutation


variable {n : ℕ}


/-- A walk in an induced subgraph of the path passes through every intermediate vertex. -/
private theorem walk_hits (S : Set (Fin n)) {u v : S} (w : ((pathGraph n).induce S).Walk u v)
    (z : Fin n) (h1 : u.1.val ≤ z.val) (h2 : z.val ≤ v.1.val) : z ∈ S := by
  induction w with
  | nil => have : z = _ := Fin.ext (le_antisymm h2 h1); exact this ▸ (‹S›).2
  | @cons u u' v h p ih =>
    by_cases hz : u'.1.val ≤ z.val
    · exact ih hz h2
    · push Not at hz
      have : z = u.1 := Fin.ext (by
        rcases (show (pathGraph n).Adj u.1 u'.1 from h) |> pathGraph_adj.mp with h' | h' <;> omega)
      exact this ▸ u.2

/-- A connected induced subgraph of the path is order-convex. -/
private theorem convex_of_connected {S : Set (Fin n)} (hS : ((pathGraph n).induce S).Connected)
    {x y z : Fin n} (hx : x ∈ S) (hy : y ∈ S) (hxz : x ≤ z) (hzy : z ≤ y) : z ∈ S := by
  obtain ⟨w⟩ := hS.preconnected ⟨x, hx⟩ ⟨y, hy⟩
  exact walk_hits S w z hxz hzy

private theorem interval_connected (a b : Fin n) (hab : a ≤ b) :
    ((pathGraph n).induce (Set.Icc a b)).Connected := by
  have : Nonempty (Set.Icc a b) := ⟨⟨a, le_rfl, hab⟩⟩
  have key : ∀ d : ℕ, ∀ (x : Fin n) (hx : x ∈ Set.Icc a b), x.val - a.val = d →
      ((pathGraph n).induce (Set.Icc a b)).Reachable ⟨a, le_rfl, hab⟩ ⟨x, hx⟩ := by
    intro d
    induction d with
    | zero =>
      intro x hx hd
      have : x = a := Fin.ext (by have := hx.1; rw [Fin.le_def] at this; omega)
      subst this; rfl
    | succ d ih =>
      intro x hx hd
      have hxa := hx.1; rw [Fin.le_def] at hxa
      let y : Fin n := ⟨x.val - 1, by omega⟩
      have hy : y ∈ Set.Icc a b :=
        ⟨Fin.le_def.mpr (by simp [y]; omega), Fin.le_def.mpr (by
          have := hx.2; rw [Fin.le_def] at this; simp [y]; omega)⟩
      refine (ih y hy (by simp [y]; omega)).trans (SimpleGraph.Adj.reachable ?_)
      show (pathGraph n).Adj y x
      rw [pathGraph_adj]; left; simp [y]; omega
  refine ⟨fun u v => ?_⟩
  exact (key _ u.1 u.2 rfl).symm.trans (key _ v.1 v.2 rfl)

/-- An interval with at least two vertices is a zero forcing set of the path. -/
private theorem forcing_interval (a b : Fin n) (hab : a < b) :
    IsZeroForcing (pathGraph n) (Set.Icc a b) := by
  rw [Fin.lt_def] at hab
  have up : ∀ d : ℕ, ∀ v : Fin n, a.val ≤ v.val → v.val ≤ b.val + d →
      Black (pathGraph n) (Set.Icc a b) v := by
    intro d
    induction d with
    | zero => intro v h1 h2; exact .init ⟨Fin.le_def.mpr h1, Fin.le_def.mpr (by omega)⟩
    | succ d ih =>
      intro v h1 h2
      by_cases hv : v.val ≤ b.val + d
      · exact ih v h1 hv
      · let u : Fin n := ⟨v.val - 1, by omega⟩
        refine .force (u := u) (ih u (by simp [u]; omega) (by simp [u]; omega))
          (pathGraph_adj.mpr (Or.inl (by simp [u]; omega))) fun x hx hxw => ?_
        rcases pathGraph_adj.mp hx with h | h
        · exact absurd (Fin.ext (by simp [u] at h; omega)) hxw
        · exact ih x (by simp [u] at h; omega) (by simp [u] at h; omega)
  have down : ∀ d : ℕ, ∀ v : Fin n, v.val ≤ b.val → a.val ≤ v.val + d →
      Black (pathGraph n) (Set.Icc a b) v := by
    intro d
    induction d with
    | zero => intro v h1 h2; exact .init ⟨Fin.le_def.mpr (by omega), Fin.le_def.mpr h1⟩
    | succ d ih =>
      intro v h1 h2
      by_cases hv : a.val ≤ v.val + d
      · exact ih v h1 hv
      · let u : Fin n := ⟨v.val + 1, by omega⟩
        refine .force (u := u) (ih u (by simp [u]; omega) (by simp [u]; omega))
          (pathGraph_adj.mpr (Or.inr (by simp [u]))) fun x hx hxw => ?_
        rcases pathGraph_adj.mp hx with h | h
        · exact ih x (by simp [u] at h; omega) (by simp [u] at h; omega)
        · exact absurd (Fin.ext (by simp [u] at h; omega)) hxw
  intro v
  by_cases hv : a.val ≤ v.val
  · exact up v.val v hv (by omega)
  · exact down a.val v (by omega) (by omega)

/-- An end vertex of the path forces the whole path. -/
private theorem forcing_end (hn : 2 ≤ n) (e : Fin n) (he : e.val = 0 ∨ e.val + 1 = n) :
    IsZeroForcing (pathGraph n) {e} := by
  -- the neighbour of the end
  obtain ⟨f, hf, hef⟩ : ∃ f : Fin n, (pathGraph n).Adj e f ∧
      ∀ x : Fin n, (pathGraph n).Adj e x → x = f := by
    rcases he with he | he
    · refine ⟨⟨1, by omega⟩, pathGraph_adj.mpr (Or.inl (by simp; omega)), fun x hx => ?_⟩
      rcases pathGraph_adj.mp hx with h | h <;> exact Fin.ext (by simp; omega)
    · refine ⟨⟨n - 2, by omega⟩, pathGraph_adj.mpr (Or.inr (by simp; omega)), fun x hx => ?_⟩
      rcases pathGraph_adj.mp hx with h | h <;> exact Fin.ext (by simp; omega)
  have hbf : Black (pathGraph n) {e} f :=
    .force (.init rfl) hf fun x hx hxf => absurd (hef x hx) hxf
  have hpair : ∀ x ∈ Set.Icc (min e f) (max e f), Black (pathGraph n) {e} x := by
    intro x hx
    have hx1 := hx.1; have hx2 := hx.2
    rcases pathGraph_adj.mp hf with h | h
    · have : x = e ∨ x = f := by
        simp only [Fin.le_def, Fin.val_min, Fin.val_max] at hx1 hx2
        rcases Nat.lt_or_ge x.val (e.val + 1) with hh | hh
        · left; exact Fin.ext (by omega)
        · right; exact Fin.ext (by omega)
      rcases this with rfl | rfl
      · exact .init rfl
      · exact hbf
    · have : x = e ∨ x = f := by
        simp only [Fin.le_def, Fin.val_min, Fin.val_max] at hx1 hx2
        rcases Nat.lt_or_ge x.val (f.val + 1) with hh | hh
        · right; exact Fin.ext (by omega)
        · left; exact Fin.ext (by omega)
      rcases this with rfl | rfl
      · exact .init rfl
      · exact hbf
  have hlt : min e f < max e f := by
    rcases pathGraph_adj.mp hf with h | h
    · rw [min_eq_left (Fin.le_def.mpr (by omega)), max_eq_right (Fin.le_def.mpr (by omega))]
      exact Fin.lt_def.mpr (by omega)
    · rw [min_eq_right (Fin.le_def.mpr (by omega)), max_eq_left (Fin.le_def.mpr (by omega))]
      exact Fin.lt_def.mpr (by omega)
  exact fun v => Black.bind hpair (forcing_interval _ _ hlt v)

/-- An interior vertex alone forces nothing. -/
private theorem interior_black (v : Fin n) (h0 : 0 < v.val) (h1 : v.val + 1 < n) :
    ∀ w, Black (pathGraph n) {v} w → w = v := by
  intro w hw
  induction hw with
  | init h => exact h
  | @force u w' hu huw hall ihu ihall =>
    subst ihu
    rcases pathGraph_adj.mp huw with h | h
    · -- w' = u + 1; the other neighbour u - 1 must be black
      have := ihall ⟨u.val - 1, by omega⟩ (pathGraph_adj.mpr (Or.inr (by simp; omega)))
        (fun he => by have := congrArg Fin.val he; simp at this; omega)
      have := congrArg Fin.val this; simp at this; omega
    · have := ihall ⟨u.val + 1, by omega⟩ (pathGraph_adj.mpr (Or.inl (by simp)))
        (fun he => by have := congrArg Fin.val he; simp at this; omega)
      have := congrArg Fin.val this; simp at this

/-- The connected zero forcing sets of the path: intervals with at least two vertices, and the two
end vertices. -/
theorem connected_forcing_iff (hn : 2 ≤ n) (S : Finset (Fin n)) :
    connectedForcing (pathGraph n) S ↔
      ∃ a b : Fin n, S = Finset.Icc a b ∧ (a < b ∨ (a = b ∧ (a.val = 0 ∨ a.val + 1 = n))) := by
  constructor
  · rintro ⟨hconn, hforce⟩
    have hne : S.Nonempty := by
      obtain ⟨⟨x, hx⟩⟩ := hconn.nonempty
      exact ⟨x, hx⟩
    refine ⟨S.min' hne, S.max' hne, ?_, ?_⟩
    · ext z; constructor
      · intro hz; exact Finset.mem_Icc.mpr ⟨S.min'_le z hz, S.le_max' z hz⟩
      · intro hz
        rw [Finset.mem_Icc] at hz
        exact convex_of_connected hconn (S.min'_mem hne) (S.max'_mem hne) hz.1 hz.2
    · rcases lt_or_eq_of_le (S.min'_le_max' hne) with h | h
      · exact Or.inl h
      · right; refine ⟨h, ?_⟩
        by_contra hint
        push Not at hint
        set v := S.min' hne
        have hS : S = {v} := by
          ext z; constructor
          · intro hz
            exact Finset.mem_singleton.mpr (le_antisymm (h ▸ S.le_max' z hz) (S.min'_le z hz))
          · intro hz; rw [Finset.mem_singleton.mp hz]; exact S.min'_mem hne
        have hv0 : 0 < v.val := Nat.pos_of_ne_zero hint.1
        have hv1 : v.val + 1 < n := by have := v.isLt; omega
        obtain ⟨w, hw⟩ : ∃ w : Fin n, w ≠ v := ⟨⟨0, by omega⟩, fun h' => by
          have := congrArg Fin.val h'; simp at this; omega⟩
        have := hforce w
        rw [hS, Finset.coe_singleton] at this
        exact hw (interior_black v hv0 hv1 w this)
  · rintro ⟨a, b, rfl, h⟩
    rw [connectedForcing, Finset.coe_Icc]
    rcases h with h | ⟨rfl, he⟩
    · exact ⟨interval_connected a b h.le, forcing_interval a b h⟩
    · refine ⟨interval_connected a a le_rfl, ?_⟩
      rw [Set.Icc_self]
      exact forcing_end hn a he


private theorem count_starts (i : ℕ) (hi : 1 ≤ i) :
    (Finset.univ.filter fun a : Fin n => a.val + i ≤ n).card = n + 1 - i := by
  rw [← Finset.card_map Fin.valEmbedding, ← Finset.card_range (n + 1 - i)]
  congr 1
  ext m
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
    Finset.mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩; omega
  · intro hm; exact ⟨⟨m, by omega⟩, by simp; omega, rfl⟩

private theorem min_Icc (a b : Fin n) (hab : a ≤ b) (h : (Finset.Icc a b).Nonempty) :
    (Finset.Icc a b).min' h = a :=
  le_antisymm (Finset.min'_le _ a (Finset.mem_Icc.mpr ⟨le_rfl, hab⟩))
    (Finset.le_min' _ _ _ fun _ hz => (Finset.mem_Icc.mp hz).1)

/-- For `i ≥ 2` the coefficient of `x^i` counts the `n + 1 - i` intervals of length `i`. -/
private theorem coeff_ge (hn : 2 ≤ n) (i : ℕ) (hi : 2 ≤ i) :
    coefficient (pathGraph n) i = n + 1 - i := by
  classical
  unfold coefficient
  rw [← count_starts i (by omega)]
  have shape : ∀ S, S ∈ Finset.univ.filter (fun S : Finset (Fin n) =>
      S.card = i ∧ connectedForcing (pathGraph n) S) →
      ∃ a b : Fin n, a ≤ b ∧ S = Finset.Icc a b ∧ b.val + 1 - a.val = i := by
    intro S hS
    obtain ⟨-, hc, hcf⟩ := Finset.mem_filter.mp hS
    obtain ⟨a, b, rfl, hab⟩ := (connected_forcing_iff hn S).mp hcf
    have hab' : a ≤ b := by rcases hab with h | ⟨h, -⟩ <;> [exact h.le; exact h.le]
    exact ⟨a, b, hab', rfl, by rw [← Fin.card_Icc]; exact hc⟩
  refine Finset.card_bij (fun S hS => S.min' ?_) ?_ ?_ ?_
  · obtain ⟨-, hc, -⟩ := Finset.mem_filter.mp hS
    exact Finset.card_pos.mp (by omega)
  · intro S hS
    obtain ⟨a, b, hab, rfl, hc⟩ := shape S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [min_Icc a b hab]
    have := b.isLt; omega
  · intro S hS S' hS' heq
    obtain ⟨a, b, hab, rfl, hc⟩ := shape S hS
    obtain ⟨a', b', hab', rfl, hc'⟩ := shape S' hS'
    rw [min_Icc a b hab, min_Icc a' b' hab'] at heq
    subst heq
    have : b = b' := Fin.ext (by rw [Fin.le_def] at hab hab'; omega)
    rw [this]
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    let b : Fin n := ⟨a.val + i - 1, by omega⟩
    have hab : a < b := Fin.lt_def.mpr (by simp [b]; omega)
    refine ⟨Finset.Icc a b, ?_, min_Icc a b hab.le _⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨by rw [Fin.card_Icc]; simp [b]; omega,
      (connected_forcing_iff hn _).mpr ⟨a, b, rfl, Or.inl hab⟩⟩

/-- The coefficient of `x` is `2`: the two end vertices. -/
private theorem coeff_one (hn : 2 ≤ n) : coefficient (pathGraph n) 1 = 2 := by
  classical
  unfold coefficient
  let e0 : Fin n := ⟨0, by omega⟩
  let e1 : Fin n := ⟨n - 1, by omega⟩
  have hne : e0 ≠ e1 := fun h => by have := congrArg Fin.val h; simp [e0, e1] at this; omega
  have : Finset.univ.filter (fun S : Finset (Fin n) =>
      S.card = 1 ∧ connectedForcing (pathGraph n) S) = {{e0}, {e1}} := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hc, hcf⟩
      obtain ⟨a, b, rfl, hab⟩ := (connected_forcing_iff hn _).mp hcf
      rw [Fin.card_Icc] at hc
      rcases hab with h | ⟨rfl, he⟩
      · rw [Fin.lt_def] at h; omega
      · rw [Finset.Icc_self]
        rcases he with he | he
        · left; congr 1; exact Fin.ext (by simp [e0, he])
        · right; congr 1; exact Fin.ext (by simp [e1]; omega)
    · rintro (rfl | rfl)
      · refine ⟨rfl, (connected_forcing_iff hn _).mpr
          ⟨e0, e0, by rw [Finset.Icc_self], Or.inr ⟨rfl, Or.inl rfl⟩⟩⟩
      · refine ⟨rfl, (connected_forcing_iff hn _).mpr ⟨e1, e1, by rw [Finset.Icc_self],
          Or.inr ⟨rfl, Or.inr (by simp [e1]; omega)⟩⟩⟩
  rw [this, Finset.card_pair (fun h => hne (Finset.singleton_injective h))]

/-- No empty set is connected. -/
private theorem coeff_zero : coefficient (pathGraph n) 0 = 0 := by
  classical
  unfold coefficient
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro S - ⟨hc, hconn, -⟩
  obtain ⟨⟨x, hx⟩⟩ := hconn.nonempty
  rw [Finset.card_eq_zero] at hc
  subst hc
  exact absurd hx (by simp)

/-- Proposition 7.7 of Brimkov (2017): for `n ≥ 2`, `Z_c(P_n; x) = 2x + Σ_{i=2}^n (n - i + 1) x^i`,
coefficientwise; the coefficient vanishes for `i = 0` and for `i > n`. -/
theorem result (hn : 2 ≤ n) :
    coefficient (pathGraph n) 0 = 0 ∧ coefficient (pathGraph n) 1 = 2 ∧
      ∀ i : ℕ, 2 ≤ i → coefficient (pathGraph n) i = n + 1 - i :=
  ⟨coeff_zero, coeff_one hn, coeff_ge hn⟩

end D5.S3.Combinatorics.Graph.ZeroForcing.PathConnectedForcing
