/- GID: D5/S3/Combinatorics/Graph/ZeroForcing/CycleConnectedForcing
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/ZeroForcing/CycleConnectedForcing
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.CycleGraph]
   utility: none
   digest: The connected forcing polynomial of the cycle C_n is n sum_(i=2)^(n-1) x^i + x^n for n >= 3, with the cases n <= 2 also determined. -/

import D5.S3.Combinatorics.Graph.ZeroForcing.ConnectedForcingCrossingRefutation
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-! The connected forcing polynomial of the cycle, Proposition 7.8 of B. Brimkov, Graph Coloring,
Zero Forcing, and Related Problems (PhD thesis, Rice University, 2017): for `n ≥ 3`,
`Z_c(C_n; x) = n Σ_{i=2}^{n-1} x^i + x^n`. The coefficients are the frozen
`ConnectedForcingCrossingRefutation.coefficient` for Mathlib's `cycleGraph n`.

`connected_forcing_iff` characterizes the connected forcing sets of `C_n` for every `n`: the
arcs `{x | (x - a).val < i}` with `i ≥ 2`, and on two vertices also the single vertices. A
connected set missing a vertex `v` is an arc, since a walk avoiding `v` moves the offset from
`v + 1` by one at each step; an arc with two vertices forces around the cycle from its last
vertex; a single vertex has two white neighbours and forces nothing once `n ≥ 3`. `result` gives
the coefficients for every `n`; for `n ≥ 3` they are those of Proposition 7.8.

admission_basis: escape-witness. Escape witnesses: offset_step with walk_hits and
eq_arc_of_connected (connected proper sets are arcs), arc_connected, forcing_arc and
singleton_stuck (the forcing behaviour of arcs), card_arc and arc_injective (the counts), cf_one and
cf_two (the cycles on one and two vertices). -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.Graph.ZeroForcing.CycleConnectedForcing

open SimpleGraph
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThree
open D5.S3.Combinatorics.Graph.ZeroForcing.ConnectedForcingCrossingRefutation

variable {m : ℕ}

/-- The arc of the vertices `a, a + 1, …, a + (i - 1)` of the cycle on `Fin (m + 3)`. -/
private def arc (a : Fin (m + 3)) (i : ℕ) : Finset (Fin (m + 3)) :=
  Finset.univ.filter fun x => (x - a).val < i

private theorem mem_arc {a x : Fin (m + 3)} {i : ℕ} : x ∈ arc a i ↔ (x - a).val < i := by
  simp [arc]

private theorem adj_iff {u v : Fin (m + 3)} :
    (cycleGraph (m + 3)).Adj u v ↔ u = v + 1 ∨ v = u + 1 := by
  rw [show (cycleGraph (m + 3)).Adj u v ↔ u - v = 1 ∨ v - u = 1 from cycleGraph_adj]
  constructor <;> rintro (h | h)
  · left; rw [← h]; abel
  · right; rw [← h]; abel
  · left; rw [h]; abel
  · right; rw [h]; abel

private theorem val_one' : (1 : Fin (m + 3)).val = 1 := Fin.val_one (m + 1)

private theorem sub_one_ne_add_one (u : Fin (m + 3)) : u - 1 ≠ u + 1 := by
  intro h
  have h2 : (1 : Fin (m + 3)) + 1 = 0 := by
    have : (1 : Fin (m + 3)) + 1 = (u + 1) - (u - 1) := by abel
    rw [this, ← h, sub_self]
  have := congrArg Fin.val h2
  rw [Fin.val_add, val_one'] at this
  simp at this
  rw [Nat.mod_eq_of_lt (by omega)] at this
  omega

private theorem add_one_ne (u : Fin (m + 3)) : u + 1 ≠ u := by
  intro h
  have := congrArg Fin.val (show (1 : Fin (m + 3)) = 0 by
    have := congrArg (· - u) h; simp at this)
  rw [val_one'] at this; simp at this

/-- `a + j`, written with the natural number `j < m + 3`. -/
private def pt (a : Fin (m + 3)) (j : ℕ) (hj : j < m + 3) : Fin (m + 3) := a + ⟨j, hj⟩

private theorem pt_sub (a : Fin (m + 3)) (j : ℕ) (hj : j < m + 3) : (pt a j hj - a).val = j := by
  simp [pt]

private theorem pt_succ (a : Fin (m + 3)) (j : ℕ) (hj : j + 1 < m + 3) :
    pt a (j + 1) hj = pt a j (by omega) + 1 := by
  rw [pt, pt, add_assoc]
  congr 1
  ext
  rw [Fin.val_add, val_one', Nat.mod_eq_of_lt hj]

private theorem eq_pt (a x : Fin (m + 3)) : x = pt a (x - a).val (x - a).isLt := by
  simp [pt]

/-- A single vertex of the cycle forces nothing. -/
private theorem singleton_stuck (u : Fin (m + 3)) :
    ∀ w, Black (cycleGraph (m + 3)) ({u} : Set (Fin (m + 3))) w → w = u := by
  intro w hw
  induction hw with
  | init h => exact h
  | @force u' w hu' huw hall ihu ihall =>
    subst ihu
    have hx : ∃ x, (cycleGraph (m + 3)).Adj u' x ∧ x ≠ w := by
      rcases adj_iff.mp huw with h | h
      · exact ⟨u' + 1, adj_iff.mpr (Or.inr rfl), fun e => sub_one_ne_add_one u' (by
          rw [e, h]; abel)⟩
      · exact ⟨u' - 1, adj_iff.mpr (Or.inl (by abel)), fun e => sub_one_ne_add_one u' (by
          rw [e, h])⟩
    obtain ⟨x, hx, hxw⟩ := hx
    have := ihall x hx hxw
    subst this
    exact ((cycleGraph (m + 3)).loopless.irrefl _ hx).elim

/-- An arc with at least two vertices forces the cycle. -/
private theorem forcing_arc (a : Fin (m + 3)) (i : ℕ) (hi : 2 ≤ i) :
    IsZeroForcing (cycleGraph (m + 3)) (arc a i : Set (Fin (m + 3))) := by
  have key : ∀ j (hj : j < m + 3), Black (cycleGraph (m + 3)) (arc a i) (pt a j hj) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      by_cases hji : j < i
      · exact .init (by simp only [Finset.mem_coe, mem_arc, pt_sub]; exact hji)
      obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
      have hu := ih (k + 1) (by omega) (by omega)
      have hs : pt a (k + 2) hj = pt a (k + 1) (by omega) + 1 := pt_succ a (k + 1) hj
      refine .force hu (adj_iff.mpr (Or.inr hs)) fun x hx hxw => ?_
      rcases adj_iff.mp hx with h | h
      · have : x = pt a k (by omega) := by
          rw [pt_succ a k (by omega)] at h
          exact (add_right_cancel h).symm
        exact this ▸ ih k (by omega) (by omega)
      · exact absurd (h.trans hs.symm) hxw
  intro w
  rw [eq_pt a w]
  exact key _ _

/-- An arc with at least one vertex induces a connected subgraph. -/
private theorem arc_connected (a : Fin (m + 3)) (i : ℕ) (hi : 1 ≤ i) :
    ((cycleGraph (m + 3)).induce (arc a i : Set (Fin (m + 3)))).Connected := by
  have ha : a ∈ (arc a i : Set (Fin (m + 3))) := by
    simp only [Finset.mem_coe, mem_arc, sub_self, Fin.val_zero]; omega
  have reach : ∀ j (hj : j < m + 3) (hji : j < i),
      ((cycleGraph (m + 3)).induce (arc a i : Set (Fin (m + 3)))).Reachable ⟨a, ha⟩
        ⟨pt a j hj, by simp only [Finset.mem_coe, mem_arc, pt_sub]; exact hji⟩ := by
    intro j
    induction j with
    | zero =>
      intro hj hji
      have e : (⟨pt a 0 hj, by simp only [Finset.mem_coe, mem_arc, pt_sub]; exact hji⟩ :
          ↥(arc a i : Set (Fin (m + 3)))) = ⟨a, ha⟩ := Subtype.ext (by simp [pt])
      rw [e]
    | succ j ih =>
      intro hj hji
      exact (ih (by omega) (by omega)).trans (SimpleGraph.Adj.reachable
        (show (cycleGraph (m + 3)).Adj (pt a j (by omega)) (pt a (j + 1) hj) from
          adj_iff.mpr (Or.inr (pt_succ a j hj))))
  have : Nonempty ↥(arc a i : Set (Fin (m + 3))) := ⟨⟨a, ha⟩⟩
  have hx : ∀ x : ↥(arc a i : Set (Fin (m + 3))),
      ((cycleGraph (m + 3)).induce (arc a i : Set (Fin (m + 3)))).Reachable ⟨a, ha⟩ x := by
    intro x
    have hxi : (x.1 - a).val < i := by
      have := x.2; simpa only [Finset.mem_coe, mem_arc] using this
    have := reach (x.1 - a).val (x.1 - a).isLt hxi
    convert this using 1
    exact Subtype.ext (eq_pt a x.1)
  exact ⟨fun x y => (hx x).symm.trans (hx y)⟩

/-- The vertex just before `a` is the only one at offset `m + 2` from `a`. -/
private theorem offset_top (a x : Fin (m + 3)) (h : (x - a).val = m + 2) : x + 1 = a := by
  have hx := eq_pt a x
  rw [hx, pt, add_assoc]
  conv_rhs => rw [← add_zero a]
  congr 1
  ext
  rw [Fin.val_add, val_one', h, Fin.val_zero]
  exact Nat.mod_self (m + 3)

/-- Away from offset `m + 2`, adjacent vertices have offsets differing by one. -/
private theorem offset_step (a u u' : Fin (m + 3)) (hu : (u - a).val ≠ m + 2)
    (hu' : (u' - a).val ≠ m + 2) (h : (cycleGraph (m + 3)).Adj u u') :
    (u' - a).val = (u - a).val + 1 ∨ (u - a).val = (u' - a).val + 1 := by
  have succ_val : ∀ y : Fin (m + 3), (y - a).val ≠ m + 2 →
      (y + 1 - a).val = (y - a).val + 1 := fun y hy => by
    rw [show y + 1 - a = (y - a) + 1 by abel, Fin.val_add, val_one']
    have := (y - a).isLt
    exact Nat.mod_eq_of_lt (by omega)
  rcases adj_iff.mp h with h | h
  · right; rw [h]; exact succ_val u' hu'
  · left; rw [h]; exact succ_val u hu

/-- A walk inside a set avoiding offset `m + 2` passes every intermediate offset. -/
private theorem walk_hits (a : Fin (m + 3)) (S : Set (Fin (m + 3)))
    (hS : ∀ x ∈ S, (x - a).val ≠ m + 2)
    {u w : S} (p : ((cycleGraph (m + 3)).induce S).Walk u w) (k : ℕ)
    (h1 : (u.1 - a).val ≤ k) (h2 : k ≤ (w.1 - a).val) : ∃ z ∈ S, (z - a).val = k := by
  induction p with
  | nil => exact ⟨_, (‹S›).2, by omega⟩
  | @cons u u' w h p ih =>
    by_cases hk : (u'.1 - a).val ≤ k
    · exact ih hk h2
    · rcases offset_step a u.1 u'.1 (hS _ u.2) (hS _ u'.2) h with e | e
      · exact ⟨u.1, u.2, by omega⟩
      · omega

/-- A connected set missing some vertex is an arc. -/
private theorem eq_arc_of_connected (S : Finset (Fin (m + 3))) (v : Fin (m + 3)) (hv : v ∉ S)
    (hS : ((cycleGraph (m + 3)).induce (S : Set (Fin (m + 3)))).Connected) :
    ∃ u L, 1 ≤ L ∧ S = arc u L := by
  set a := v + 1
  have htop : ∀ x ∈ S, (x - a).val ≠ m + 2 := fun x hx h =>
    hv (by have := offset_top a x h; rw [← add_right_cancel this]; exact hx)
  obtain ⟨⟨x0, hx0⟩⟩ := hS.nonempty
  set P := S.image fun x => (x - a).val
  have hP : P.Nonempty := ⟨_, Finset.mem_image_of_mem _ hx0⟩
  obtain ⟨u, hu, hup⟩ := Finset.mem_image.mp (P.min'_mem hP)
  obtain ⟨w, hw, hwq⟩ := Finset.mem_image.mp (P.max'_mem hP)
  have hq : P.max' hP ≤ m + 1 := by
    have := htop w hw; have := (w - a).isLt; omega
  have mem : ∀ x, x ∈ S ↔ P.min' hP ≤ (x - a).val ∧ (x - a).val ≤ P.max' hP := by
    intro x
    constructor
    · intro hx
      exact ⟨P.min'_le _ (Finset.mem_image_of_mem _ hx),
        P.le_max' _ (Finset.mem_image_of_mem _ hx)⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨p⟩ := hS.preconnected ⟨u, hu⟩ ⟨w, hw⟩
      obtain ⟨z, hz, hzx⟩ := walk_hits a (S : Set (Fin (m + 3))) htop p (x - a).val
        (by rw [hup]; exact h1) (by rw [hwq]; exact h2)
      have : z = x := by
        have : z - a = x - a := Fin.ext hzx
        exact sub_left_inj.mp this
      exact this ▸ hz
  have hpq : P.min' hP ≤ P.max' hP := P.min'_le _ (P.max'_mem hP)
  refine ⟨u, P.max' hP - P.min' hP + 1, by omega, ?_⟩
  ext x
  rw [mem x, mem_arc, show x - u = (x - a) - (u - a) by abel, hup.symm]
  by_cases hle : u - a ≤ x - a
  · rw [Fin.sub_val_of_le hle]
    have := Fin.le_iff_val_le_val.mp hle
    constructor <;> intro h <;> omega
  · push Not at hle
    rw [Fin.coe_sub_iff_lt.mpr hle]
    have := Fin.lt_def.mp hle
    constructor <;> intro h <;> omega

private theorem card_arc (a : Fin (m + 3)) (i : ℕ) : (arc a i).card = min (m + 3) i := by
  have : arc a i = (Finset.univ.filter fun y : Fin (m + 3) => (y : ℕ) < i).map
      (addLeftEmbedding a) := by
    ext x
    simp only [mem_arc, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      addLeftEmbedding_apply]
    constructor
    · intro h; exact ⟨x - a, h, by abel⟩
    · rintro ⟨y, hy, rfl⟩; simpa using hy
  rw [this, Finset.card_map, Fin.card_filter_val_lt]

private theorem arc_one (u : Fin (m + 3)) : (arc u 1 : Set (Fin (m + 3))) = {u} := by
  ext x
  simp only [Finset.mem_coe, mem_arc, Set.mem_singleton_iff, Nat.lt_one_iff]
  constructor
  · intro h; exact sub_eq_zero.mp (Fin.ext h)
  · rintro rfl; simp

private theorem arc_full (a : Fin (m + 3)) : arc a (m + 3) = Finset.univ := by
  ext x; simp [mem_arc, (x - a).isLt]

/-- The connected forcing sets of the cycle on `m + 3` vertices are the arcs with at least two
vertices. -/
private theorem cf_iff (S : Finset (Fin (m + 3))) :
    connectedForcing (cycleGraph (m + 3)) S ↔ ∃ a i, 2 ≤ i ∧ S = arc a i := by
  constructor
  · rintro ⟨hconn, hforce⟩
    by_cases hfull : ∀ v, v ∈ S
    · exact ⟨0, m + 3, by omega, by rw [arc_full]; ext x; simp [hfull x]⟩
    push Not at hfull
    obtain ⟨v, hv⟩ := hfull
    obtain ⟨u, L, hL, rfl⟩ := eq_arc_of_connected S v hv hconn
    refine ⟨u, L, ?_, rfl⟩
    by_contra hL2
    obtain rfl : L = 1 := by omega
    have := hforce (u + 1)
    rw [arc_one] at this
    exact add_one_ne u (singleton_stuck u _ this)
  · rintro ⟨a, i, hi, rfl⟩
    exact ⟨arc_connected a i (by omega), forcing_arc a i hi⟩

private theorem arc_injective (i : ℕ) (hi : 1 ≤ i) (him : i < m + 3) :
    Function.Injective fun a : Fin (m + 3) => arc a i := by
  intro a b hab
  simp only at hab
  have ha : a ∈ arc b i := by rw [← hab, mem_arc, sub_self, Fin.val_zero]; omega
  rw [mem_arc] at ha
  by_contra hne
  have hpos : (1 : Fin (m + 3)) ≤ a - b := by
    rw [Fin.le_iff_val_le_val, val_one']
    have : a - b ≠ 0 := fun h => hne (sub_eq_zero.mp h)
    have : (a - b).val ≠ 0 := fun h => this (Fin.ext h)
    omega
  have hm : a - 1 ∈ arc b i := by
    rw [mem_arc, show a - 1 - b = (a - b) - 1 by abel, Fin.sub_val_of_le hpos, val_one']
    omega
  rw [← hab, mem_arc, show a - 1 - a = 0 - 1 by abel,
    Fin.coe_sub_iff_lt.mpr (by rw [Fin.lt_def, val_one', Fin.val_zero]; omega), val_one',
    Fin.val_zero] at hm
  omega

/-- The coefficients of the connected forcing polynomial of the cycle on `m + 3` vertices. -/
private theorem coeff_formula (i : ℕ) :
    coefficient (cycleGraph (m + 3)) i =
      if i = m + 3 then 1 else if 2 ≤ i ∧ i < m + 3 then m + 3 else 0 := by
  classical
  unfold coefficient
  have hfilter : (Finset.univ.filter fun S : Finset (Fin (m + 3)) =>
      S.card = i ∧ connectedForcing (cycleGraph (m + 3)) S) =
      Finset.univ.filter fun S : Finset (Fin (m + 3)) =>
        S.card = i ∧ ∃ a j, 2 ≤ j ∧ S = arc a j := by
    ext S; simp only [Finset.mem_filter, Finset.mem_univ, true_and, cf_iff]
  rw [hfilter]
  split_ifs with h1 h2
  · subst h1
    rw [Finset.card_eq_one]
    refine ⟨Finset.univ, ?_⟩
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hc, -⟩; exact Finset.eq_univ_of_card S (by rw [hc, Fintype.card_fin])
    · rintro rfl; exact ⟨by simp, 0, m + 3, by omega, (arc_full 0).symm⟩
  · have heq : (Finset.univ.filter fun S : Finset (Fin (m + 3)) =>
        S.card = i ∧ ∃ a j, 2 ≤ j ∧ S = arc a j) = Finset.univ.image fun a => arc a i := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨hc, a, j, hj, rfl⟩
        refine ⟨a, ?_⟩
        rw [card_arc] at hc
        have : j = i := by omega
        rw [this]
      · rintro ⟨a, rfl⟩
        exact ⟨by rw [card_arc]; omega, a, i, h2.1, rfl⟩
    rw [heq, Finset.card_image_of_injective _ (arc_injective i (by omega) h2.2), Finset.card_univ,
      Fintype.card_fin]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro S - ⟨hc, a, j, hj, rfl⟩
    rw [card_arc] at hc
    omega

/-- On one vertex the only connected forcing set is the vertex itself. -/
private theorem cf_one (S : Finset (Fin 1)) :
    connectedForcing (cycleGraph 1) S ↔ S = Finset.univ := by
  constructor
  · rintro ⟨h, -⟩
    obtain ⟨⟨x, hx⟩⟩ := h.nonempty
    ext y; simp only [Finset.mem_univ, iff_true]; rw [Subsingleton.elim y x]; exact hx
  · rintro rfl
    have : Nonempty ↥((Finset.univ : Finset (Fin 1)) : Set (Fin 1)) := ⟨⟨0, by simp⟩⟩
    exact ⟨⟨fun x y => by rw [Subsingleton.elim x y]⟩,
      fun v => .init (Finset.mem_coe.mpr (Finset.mem_univ v))⟩

/-- On two vertices every nonempty set is a connected forcing set. -/
private theorem cf_two (S : Finset (Fin 2)) : connectedForcing (cycleGraph 2) S ↔ S.Nonempty := by
  rw [cycleGraph_two_eq_top]
  constructor
  · rintro ⟨h, -⟩; obtain ⟨⟨x, hx⟩⟩ := h.nonempty; exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    refine ⟨?_, ?_⟩
    · have : Nonempty ↥((S : Set (Fin 2))) := ⟨⟨x, hx⟩⟩
      refine ⟨fun u v => ?_⟩
      by_cases h : u = v
      · rw [h]
      · exact SimpleGraph.Adj.reachable (show (⊤ : SimpleGraph (Fin 2)).Adj u.1 v.1 from
          fun e => h (Subtype.ext e))
    · intro v
      by_cases hv : v = x
      · exact .init (hv ▸ hx)
      · refine .force (.init hx) (by simpa [eq_comm] using hv) ?_
        intro y hy hyv
        have : y ≠ x := fun e => hy (e ▸ rfl)
        omega

variable {n : ℕ}

/-- The connected forcing sets of the cycle `C_n`: the arcs `{x | (x - a).val < i}` with `i ≥ 2`
(all of `C_n` once `i ≥ n`), and on two vertices also the single vertices (`i = 1`). -/
theorem connected_forcing_iff (S : Finset (Fin n)) :
    connectedForcing (cycleGraph n) S ↔
      ∃ a : Fin n, ∃ i, 1 ≤ i ∧ (2 ≤ i ∨ n = 2) ∧
        S = Finset.univ.filter fun x => (x - a).val < i := by
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · rcases Nat.lt_or_ge n 1 with h1 | h1
    · obtain rfl : n = 0 := by omega
      constructor
      · rintro ⟨h, -⟩; obtain ⟨⟨x, -⟩⟩ := h.nonempty; exact x.elim0
      · rintro ⟨a, -⟩; exact a.elim0
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · obtain rfl : n = 1 := by omega
      rw [cf_one]
      have hall : ∀ (a : Fin 1) (i : ℕ), 1 ≤ i →
          (Finset.univ.filter fun x : Fin 1 => (x - a).val < i) = Finset.univ := by
        intro a i hi; ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        have := (x - a).isLt; omega
      constructor
      · rintro rfl; exact ⟨0, 2, by omega, Or.inl le_rfl, (hall 0 2 (by omega)).symm⟩
      · rintro ⟨a, i, hi, -, rfl⟩; exact hall a i hi
    obtain rfl : n = 2 := by omega
    rw [cf_two]
    constructor
    · intro hS
      have key : ∀ T : Finset (Fin 2), T.Nonempty → ∃ a : Fin 2, ∃ i ∈ ({1, 2} : Finset ℕ),
          T = Finset.univ.filter fun x => (x - a).val < i := by decide
      obtain ⟨a, i, hi, h⟩ := key S hS
      exact ⟨a, i, by simp at hi; omega, Or.inr rfl, h⟩
    · rintro ⟨a, i, hi, -, rfl⟩
      exact ⟨a, by simp only [Finset.mem_filter, Finset.mem_univ, true_and, sub_self,
        Fin.val_zero]; omega⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [cf_iff]
    constructor
    · rintro ⟨a, i, hi, rfl⟩; exact ⟨a, i, by omega, Or.inl hi, rfl⟩
    · rintro ⟨a, i, -, hi, rfl⟩; exact ⟨a, i, by omega, rfl⟩

/-- The connected forcing polynomial of the cycle `C_n` for every `n`, and Proposition 7.8 of
Brimkov: `Z_c(C_n; x) = n Σ_{i=2}^{n-1} x^i + x^n` for `n ≥ 3`, which also holds for `n = 1`. -/
theorem result :
    (∀ i, coefficient (cycleGraph n) i =
      if i = n ∧ n ≠ 0 then 1 else if 1 ≤ i ∧ i < n ∧ (2 ≤ i ∨ n = 2) then n else 0) ∧
    (n ≠ 0 → n ≠ 2 → ∀ i, coefficient (cycleGraph n) i =
      if i = n then 1 else if 2 ≤ i ∧ i < n then n else 0) := by
  classical
  have general : ∀ i, coefficient (cycleGraph n) i =
      if i = n ∧ n ≠ 0 then 1 else if 1 ≤ i ∧ i < n ∧ (2 ≤ i ∨ n = 2) then n else 0 := by
    intro i
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · rcases Nat.lt_or_ge n 1 with h1 | h1
      · obtain rfl : n = 0 := by omega
        unfold coefficient
        rw [Finset.card_eq_zero.mpr]
        · simp
        rw [Finset.filter_eq_empty_iff]
        rintro S - ⟨-, h, -⟩
        obtain ⟨⟨x, -⟩⟩ := h.nonempty
        exact x.elim0
      rcases Nat.lt_or_ge n 2 with h2 | h2
      · obtain rfl : n = 1 := by omega
        unfold coefficient
        have hfilter : (Finset.univ.filter fun S : Finset (Fin 1) =>
            S.card = i ∧ connectedForcing (cycleGraph 1) S) =
            Finset.univ.filter fun S : Finset (Fin 1) => S.card = i ∧ S = Finset.univ := by
          ext S; simp only [Finset.mem_filter, Finset.mem_univ, true_and, cf_one]
        rw [hfilter]
        by_cases h1 : i = 1
        · subst h1
          rw [Finset.card_eq_one.mpr ⟨Finset.univ, by
            ext S; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            constructor
            · rintro ⟨-, rfl⟩; rfl
            · rintro rfl; exact ⟨by simp, rfl⟩⟩]
          simp
        · rw [Finset.card_eq_zero.mpr]
          · split_ifs <;> omega
          rw [Finset.filter_eq_empty_iff]
          rintro S - ⟨hc, rfl⟩
          simp at hc; omega
      obtain rfl : n = 2 := by omega
      unfold coefficient
      simp only [cf_two]
      rcases Nat.lt_or_ge i 3 with h | h
      · interval_cases i <;> decide
      · rw [Finset.card_eq_zero.mpr]
        · split_ifs <;> omega
        rw [Finset.filter_eq_empty_iff]
        rintro S - ⟨hc, -⟩
        have := S.card_le_univ; simp at this; omega
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      rw [coeff_formula]
      split_ifs <;> omega
  refine ⟨general, fun h0 h2 i => ?_⟩
  rw [general i]
  split_ifs <;> omega

end D5.S3.Combinatorics.Graph.ZeroForcing.CycleConnectedForcing
