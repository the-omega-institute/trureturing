/- GID: D5/S3/Combinatorics/Graph/DeltaY/TwoColorInvariant
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DeltaY/TwoColorInvariant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finite]
   utility: none
   digest: A two-color invariant forces reachable reverse sites to be independent. -/

import D5.S3.Combinatorics.Graph.DeltaY.MoveModel
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
Crossing edges weigh two and monochromatic edges weigh one. The invariant requires
weighted degree at least six, monochromatic triangles, and no four-cycle consisting
of crossing edges. The all-one-color initialization and the move updates give the
invariant along arbitrary finite ordinary histories.
-/

set_option autoImplicit false
set_option warningAsError true

namespace DeltaY

open Finset Relation
open scoped BigOperators

universe u v

private def Cross (G : State) (C : ℕ → Bool) (x y : ℕ) : Prop := G.Adj x y ∧ C x ≠ C y

private theorem Cross.symm {G : State} {C : ℕ → Bool} {x y : ℕ} (h : Cross G C x y) :
    Cross G C y x := ⟨State.adj_symm h.1, h.2.symm⟩

private def Monochromatic (G : State) (C : ℕ → Bool) : Prop :=
  ∀ ⦃x y z⦄, G.Adj x y → G.Adj y z → G.Adj z x → C x = C y

private def NoCrossSquare (G : State) (C : ℕ → Bool) : Prop :=
  ∀ ⦃x y u v⦄, x ≠ y → u ≠ v →
    Cross G C x u → Cross G C y u → Cross G C x v → Cross G C y v → False

private def Weight (C : ℕ → Bool) (x y : ℕ) : ℕ := if C x = C y then 1 else 2

private def weighted (G : State) (C : ℕ → Bool) (x : ℕ) : ℕ :=
  ∑ y ∈ G.neighbors x, Weight C x y

private structure Invariant (G : State) (C : ℕ → Bool) : Prop where
  weighted_ge : ∀ x ∈ G.active, 6 ≤ weighted G C x
  mono : Monochromatic G C
  square : NoCrossSquare G C

private def paint (C : ℕ → Bool) (o a : ℕ) : ℕ → Bool :=
  fun x => if x = o then !(C a) else C x

private theorem paint_old {C : ℕ → Bool} {o a x : ℕ} (hne : x ≠ o) : paint C o a x = C x := by
  simp [paint, hne]

private theorem paint_center (C : ℕ → Bool) (o a : ℕ) : paint C o a o = !(C a) := by
  simp [paint]

private theorem triple_mono {G : State} {C : ℕ → Bool} {T : Triple} {o : ℕ}
    (hm : Monochromatic G C) (h : ForwardOK G T o) :
    ∀ x ∈ T.verts, C x = C T.a := by
  have ha : T.a ∈ T.verts := by simp [Triple.mem_verts]
  have hb : T.b ∈ T.verts := by simp [Triple.mem_verts]
  have hc : T.c ∈ T.verts := by simp [Triple.mem_verts]
  have hab := tri_adj h ha hb T.ab
  have hac := tri_adj h ha hc T.ac
  have hbc := tri_adj h hb hc T.bc
  intro x hx
  rcases (T.mem_verts x).mp hx with rfl | rfl | rfl
  · rfl
  · exact hm (State.adj_symm hab) hac (State.adj_symm hbc)
  · exact hm (State.adj_symm hac) hab hbc

private theorem sum_triple (T : Triple) (f : ℕ → ℕ) :
    ∑ y ∈ T.verts, f y = f T.a + f T.b + f T.c := by
  have h₁ : T.a ∉ ({T.b, T.c} : Finset ℕ) := by simp [T.ab, T.ac]
  have h₂ : T.b ∉ ({T.c} : Finset ℕ) := by simp [T.bc]
  simp [Triple.verts, sum_insert h₁, sum_insert h₂, Nat.add_assoc]

private theorem reverse_all_cross {G : State} {C : ℕ → Bool} {T : Triple} {o : ℕ}
    (h : ReverseOK G T o) (hw : 6 ≤ weighted G C o) :
    ∀ x ∈ T.verts, C o ≠ C x := by
  have hw' := hw
  rw [weighted, h.2, sum_triple] at hw'
  intro x hx
  rcases (T.mem_verts x).mp hx with rfl | rfl | rfl <;>
    unfold Weight at hw' <;> split at hw' <;> split at hw' <;> split at hw' <;> omega

private theorem reverse_independent {G : State} {C : ℕ → Bool} {T : Triple} {o : ℕ}
    (hG : G.Valid) (h : ReverseOK G T o) (i : Invariant G C) : Independent G T := by
  rw [independent_iff]
  intro x y hx hy _ hxy
  have hox := (h.adj hG x).mpr hx
  have hoy := (h.adj hG y).mpr hy
  exact reverse_all_cross h (i.weighted_ge o h.1) x hx (i.mono hox hxy (State.adj_symm hoy))

private theorem reverse_triple_mono {G : State} {C : ℕ → Bool} {T : Triple} {o : ℕ}
    (h : ReverseOK G T o) (hw : 6 ≤ weighted G C o) :
    ∀ ⦃x y⦄, x ∈ T.verts → y ∈ T.verts → C x = C y := by
  intro x y hx hy
  have hox := reverse_all_cross h hw x hx
  have hoy := reverse_all_cross h hw y hy
  cases ho : C o <;> cases hx' : C x <;> cases hy' : C y <;> simp_all

private theorem forward_center_neighbors {G : State} {T : Triple} {o : ℕ}
    (hG : G.Valid) (h : ForwardOK G T o) : (G.forward T o).neighbors o = T.verts := by
  ext y
  rw [State.mem_neighbors (forward_valid hG h.1 h.2.1), forward_center_adj hG h]

private theorem forward_center_weighted {G : State} {T : Triple} {o : ℕ} {C : ℕ → Bool}
    (hG : G.Valid) (h : ForwardOK G T o) (same : ∀ x ∈ T.verts, C x = C T.a) :
    weighted (G.forward T o) (paint C o T.a) o = 6 := by
  rw [weighted, forward_center_neighbors hG h]
  have hh : ∀ y ∈ T.verts, Weight (paint C o T.a) o y = 2 := by
    intro y hy
    have hyo : y ≠ o := fun he => h.2.1 (he ▸ h.1 hy)
    rw [Weight, paint_center, paint_old hyo, same y hy]
    cases C T.a <;> rfl
  rw [sum_congr rfl hh]
  simp [T.card_verts]

private theorem forward_weighted_old {G : State} {T : Triple} {o x : ℕ} {C : ℕ → Bool}
    (hG : G.Valid) (h : ForwardOK G T o) (same : ∀ y ∈ T.verts, C y = C T.a)
    (hx : x ∈ G.active) :
    weighted (G.forward T o) (paint C o T.a) x = weighted G C x := by
  have hxo : x ≠ o := fun he => h.2.1 (he ▸ hx)
  have hf := forward_valid hG h.1 h.2.1
  have hneigh : ∀ ⦃y⦄, y ∈ G.neighbors x → y ≠ o :=
    fun {y} hy he => h.2.1 (he ▸ (hG ((G.mem_neighbors hG).mp hy)).2.1)
  have hwold : ∀ ⦃y⦄, y ≠ o → Weight (paint C o T.a) x y = Weight C x y := by
    intro y hy
    simp [Weight, paint_old hxo, paint_old hy]
  by_cases hxT : x ∈ T.verts
  · let rest := G.neighbors x \ T.verts
    have hrest : Disjoint rest (T.verts.erase x) := by
      rw [Finset.disjoint_left]
      exact fun _ hy hz => (mem_sdiff.mp hy).2 (mem_of_mem_erase hz)
    have hold : G.neighbors x = rest ∪ T.verts.erase x := by
      ext y
      simp only [rest, mem_union, mem_sdiff, mem_erase]
      have hm := G.mem_neighbors hG (x := x) (y := y)
      have htri : y ∈ T.verts → y ≠ x → G.Adj x y :=
        fun hy hne => tri_adj h hxT hy hne.symm
      have hl : G.Adj x y → y ≠ x := fun ha => (hG ha).2.2.symm
      grind
    have hnew : (G.forward T o).neighbors x = insert o rest := by
      ext y
      rw [State.mem_neighbors hf]
      by_cases hy : y = o
      · subst y
        rw [← show (G.forward T o).Adj o x ↔ (G.forward T o).Adj x o from
          ⟨State.adj_symm, State.adj_symm⟩, forward_center_adj hG h]
        simp [hxT]
      · rw [forward_old_adj hxo hy]
        simp only [rest, mem_insert, hy, false_or, mem_sdiff, State.mem_neighbors hG]
        have hl : G.Adj x y → x ≠ y := fun ha => (hG ha).2.2
        grind
    have hno : o ∉ rest := fun hy => hneigh (mem_sdiff.mp hy).1 rfl
    have hwrest : ∑ y ∈ rest, Weight (paint C o T.a) x y = ∑ y ∈ rest, Weight C x y :=
      sum_congr rfl (fun _ hy => hwold (hneigh (mem_sdiff.mp hy).1))
    have hwspoke : Weight (paint C o T.a) x o = 2 := by
      rw [Weight, paint_old hxo, paint_center, same x hxT]
      cases C T.a <;> rfl
    have hwpairs : ∑ y ∈ T.verts.erase x, Weight C x y = 2 := by
      have hh : ∀ y ∈ T.verts.erase x, Weight C x y = 1 := by
        intro y hy
        simp [Weight, same x hxT, same y (mem_of_mem_erase hy)]
      rw [sum_congr rfl hh]
      simp [card_erase_of_mem hxT, T.card_verts]
    unfold weighted
    rw [hnew, hold, sum_insert hno, sum_union hrest, hwrest, hwspoke, hwpairs]
    omega
  · have hn : (G.forward T o).neighbors x = G.neighbors x := by
      ext y
      rw [State.mem_neighbors hf, State.mem_neighbors hG]
      by_cases hy : y = o
      · subst y
        rw [← show (G.forward T o).Adj o x ↔ (G.forward T o).Adj x o from
          ⟨State.adj_symm, State.adj_symm⟩, forward_center_adj hG h]
        exact iff_of_false hxT (fun ha => h.2.1 (hG ha).2.1)
      · simp [forward_old_adj hxo hy, hxT]
    unfold weighted
    rw [hn]
    exact sum_congr rfl (fun _ hy => hwold (hneigh hy))

private theorem State.ext_parts {G H : State} (ha : G.active = H.active) (he : G.edges = H.edges) :
    G = H := by
  cases G
  cases H
  cases ha
  cases he
  rfl

private theorem forward_after_reverse {G : State} {T : Triple} {o : ℕ} (hG : G.Valid)
    (h : ReverseOK G T o) (hi : Independent G T) :
    (G.reverse T o).forward T o = G := by
  apply State.ext_parts
  · exact insert_erase h.1
  · ext e
    induction e using Sym2.ind with
    | h x y =>
      change ((G.reverse T o).forward T o).Adj x y ↔ G.Adj x y
      by_cases hx : x = o
      · subst x
        rw [forward_center_adj (reverse_valid hG h) (reverse_forward_ok hG h), h.adj hG]
      · by_cases hy : y = o
        · subst y
          rw [← show ((G.reverse T o).forward T o).Adj o x ↔
            ((G.reverse T o).forward T o).Adj x o from ⟨State.adj_symm, State.adj_symm⟩,
            forward_center_adj (reverse_valid hG h) (reverse_forward_ok hG h)]
          exact (h.adj hG x).symm.trans ⟨State.adj_symm, State.adj_symm⟩
        · rw [forward_old_adj hx hy, reverse_old_adj hx hy]
          have hi' := independent_iff.mp hi (x := x) (y := y)
          grind

private theorem reverse_weighted_survives {G : State} {T : Triple} {o x : ℕ} {C : ℕ → Bool}
    (hG : G.Valid) (h : ReverseOK G T o) (i : Invariant G C)
    (hx : x ∈ (G.reverse T o).active) :
    weighted (G.reverse T o) C x = weighted G C x := by
  have ha : T.a ∈ T.verts := by simp [Triple.mem_verts]
  have same : ∀ y ∈ T.verts, C y = C T.a :=
    fun _ hy => reverse_triple_mono h (i.weighted_ge o h.1) hy ha
  have hp : paint C o T.a = C := by
    funext x
    by_cases he : x = o
    · subst x
      rw [paint_center]
      have := reverse_all_cross h (i.weighted_ge o h.1) T.a ha
      cases ho : C o <;> cases ha' : C T.a <;> simp_all
    · exact paint_old he
  have hw := forward_weighted_old (reverse_valid hG h) (reverse_forward_ok hG h) same hx
  rw [forward_after_reverse hG h (reverse_independent hG h i), hp] at hw
  exact hw.symm

private theorem forward_cross_old {G : State} {T : Triple} {o x y : ℕ} {C : ℕ → Bool}
    (hx : x ≠ o) (hy : y ≠ o) :
    Cross (G.forward T o) (paint C o T.a) x y → Cross G C x y := by
  intro he
  exact ⟨((forward_old_adj hx hy).mp he.1).1, by simpa [paint_old hx, paint_old hy] using he.2⟩

private theorem forward_no_center_triangle {G : State} {T : Triple} {o x y : ℕ}
    (hG : G.Valid) (h : ForwardOK G T o)
    (hox : (G.forward T o).Adj o x) (hxy : (G.forward T o).Adj x y)
    (hyo : (G.forward T o).Adj y o) : False := by
  have hf := forward_valid hG h.1 h.2.1
  have hx : x ≠ o := (hf hox).2.2.symm
  have hy : y ≠ o := (hf hyo).2.2
  exact ((forward_old_adj hx hy).mp hxy).2
    ⟨(forward_center_adj hG h).mp hox, (forward_center_adj hG h).mp (State.adj_symm hyo),
      (hf hxy).2.2⟩

private theorem forward_monochromatic {G : State} {T : Triple} {o : ℕ} {C : ℕ → Bool}
    (hG : G.Valid) (h : ForwardOK G T o) (hm : Monochromatic G C) :
    Monochromatic (G.forward T o) (paint C o T.a) := by
  intro x y z hxy hyz hzx
  by_cases hx : x = o
  · subst x
    exact False.elim (forward_no_center_triangle hG h hxy hyz hzx)
  by_cases hy : y = o
  · subst y
    exact False.elim (forward_no_center_triangle hG h hyz hzx hxy)
  by_cases hz : z = o
  · subst z
    exact False.elim (forward_no_center_triangle hG h hzx hxy hyz)
  rw [paint_old hx, paint_old hy]
  exact hm ((forward_old_adj hx hy).mp hxy).1 ((forward_old_adj hy hz).mp hyz).1
    ((forward_old_adj hz hx).mp hzx).1

private theorem forward_no_center_square {G : State} {T : Triple} {o x y z : ℕ} {C : ℕ → Bool}
    (hG : G.Valid) (h : ForwardOK G T o) (hm : Monochromatic G C)
    (hxy : x ≠ y) (hoz : o ≠ z)
    (hox : Cross (G.forward T o) (paint C o T.a) o x)
    (hoy : Cross (G.forward T o) (paint C o T.a) o y)
    (hxz : Cross (G.forward T o) (paint C o T.a) x z)
    (hyz : Cross (G.forward T o) (paint C o T.a) y z) : False := by
  have hf := forward_valid hG h.1 h.2.1
  have hx : x ≠ o := (hf hox.1).2.2.symm
  have hy : y ≠ o := (hf hoy.1).2.2.symm
  have hxT := (forward_center_adj hG h).mp hox.1
  have hyT := (forward_center_adj hG h).mp hoy.1
  have hxz' := forward_cross_old hx hoz.symm hxz
  have hyz' := forward_cross_old hy hoz.symm hyz
  have hxy' := tri_adj h hxT hyT hxy
  exact hxz'.2 (hm (State.adj_symm hxz'.1) hxy' hyz'.1).symm

private theorem forward_no_cross_square {G : State} {T : Triple} {o : ℕ} {C : ℕ → Bool}
    (hG : G.Valid) (h : ForwardOK G T o) (hm : Monochromatic G C)
    (hs : NoCrossSquare G C) :
    NoCrossSquare (G.forward T o) (paint C o T.a) := by
  intro x y u v hxy huv hxu hyu hxv hyv
  by_cases hx : x = o
  · subst x
    exact forward_no_center_square hG h hm huv hxy hxu hxv hyu.symm hyv.symm
  by_cases hy : y = o
  · subst y
    exact forward_no_center_square hG h hm huv hxy.symm hyu hyv hxu.symm hxv.symm
  by_cases hu : u = o
  · subst u
    exact forward_no_center_square hG h hm hxy huv hxu.symm hyu.symm hxv hyv
  by_cases hv : v = o
  · subst v
    exact forward_no_center_square hG h hm hxy huv.symm hxv.symm hyv.symm hxu hyu
  exact hs hxy huv (forward_cross_old hx hu hxu) (forward_cross_old hy hu hyu)
    (forward_cross_old hx hv hxv) (forward_cross_old hy hv hyv)

private theorem reverse_cross_old {G : State} {T : Triple} {o x y : ℕ} {C : ℕ → Bool}
    (h : ReverseOK G T o) (hw : 6 ≤ weighted G C o)
    (he : Cross (G.reverse T o) C x y) : Cross G C x y := by
  rcases reverse_adj.mp he.1 with ⟨ho, _⟩ | ⟨hx, hy, _⟩
  · exact ⟨ho, he.2⟩
  · exact False.elim (he.2 (reverse_triple_mono h hw hx hy))

private theorem reverse_no_cross_square {G : State} {T : Triple} {o : ℕ} {C : ℕ → Bool}
    (h : ReverseOK G T o) (i : Invariant G C) : NoCrossSquare (G.reverse T o) C := by
  intro x y u v hxy huv hxu hyu hxv hyv
  have old := fun {x y : ℕ} => reverse_cross_old (x := x) (y := y) h (i.weighted_ge o h.1)
  exact i.square hxy huv (old hxu) (old hyu) (old hxv) (old hyv)

private theorem reverse_new_pair_no_mixed {G : State} {T : Triple} {o x y z : ℕ} {C : ℕ → Bool}
    (hG : G.Valid) (h : ReverseOK G T o) (i : Invariant G C)
    (hx : x ∈ T.verts) (hy : y ∈ T.verts) (hxy : x ≠ y)
    (hxz : (G.reverse T o).Adj x z) (hyz : (G.reverse T o).Adj y z) :
    C x = C z := by
  by_contra hcross
  have hw := i.weighted_ge o h.1
  have hyz' : C y ≠ C z := (reverse_triple_mono h hw hx hy) ▸ hcross
  have hzo : z ≠ o := (mem_erase.mp ((reverse_valid hG h hxz).2.1)).1
  have hxo : Cross G C x o :=
    ⟨State.adj_symm ((h.adj hG x).mpr hx), (reverse_all_cross h hw x hx).symm⟩
  have hyo : Cross G C y o :=
    ⟨State.adj_symm ((h.adj hG y).mpr hy), (reverse_all_cross h hw y hy).symm⟩
  exact i.square hxy hzo.symm hxo hyo (reverse_cross_old h hw ⟨hxz, hcross⟩)
    (reverse_cross_old h hw ⟨hyz, hyz'⟩)

private theorem reverse_monochromatic {G : State} {T : Triple} {o : ℕ} {C : ℕ → Bool}
    (hG : G.Valid) (h : ReverseOK G T o) (i : Invariant G C) :
    Monochromatic (G.reverse T o) C := by
  intro x y z hxy hyz hzx
  by_contra hn
  have hxy' := (reverse_cross_old h (i.weighted_ge o h.1) ⟨hxy, hn⟩).1
  rcases reverse_adj.mp hyz with ⟨hyz', _⟩ | ⟨hy, hz, hne⟩
  · rcases reverse_adj.mp hzx with ⟨hzx', _⟩ | ⟨hz, hx, hne⟩
    · exact hn (i.mono hxy' hyz' hzx')
    · exact hn (reverse_new_pair_no_mixed hG h i hx hz hne.symm hxy (State.adj_symm hyz))
  · exact hn (reverse_new_pair_no_mixed hG h i hy hz hne (State.adj_symm hxy) hzx).symm

private theorem forward_invariant {G : State} {T : Triple} {o : ℕ} {C : ℕ → Bool}
    (hG : G.Valid) (h : ForwardOK G T o) (i : Invariant G C) :
    Invariant (G.forward T o) (paint C o T.a) := by
  refine ⟨?_, forward_monochromatic hG h i.mono, forward_no_cross_square hG h i.mono i.square⟩
  intro x hx
  have s := triple_mono i.mono h
  rcases mem_insert.mp hx with rfl | hold
  · exact (forward_center_weighted hG h s).ge
  · rw [forward_weighted_old hG h s hold]
    exact i.weighted_ge x hold

private theorem reverse_invariant {G : State} {T : Triple} {o : ℕ} {C : ℕ → Bool}
    (hG : G.Valid) (h : ReverseOK G T o) (i : Invariant G C) :
    Invariant (G.reverse T o) C := by
  refine ⟨?_, reverse_monochromatic hG h i, reverse_no_cross_square h i⟩
  intro x hx
  rw [reverse_weighted_survives hG h i hx]
  exact i.weighted_ge x (mem_of_mem_erase hx)

private theorem step_strengthens {G H : State} {C : ℕ → Bool} (hG : G.Valid)
    (i : Invariant G C) (m : Move false G H) :
    Move true G H ∧ ∃ C' : ℕ → Bool, (∀ x ∈ G.active, x ∈ H.active → C' x = C x) ∧
      Invariant H C' := by
  cases m with
  | forward T o ok =>
    refine ⟨Move.forward T o ok, paint C o T.a, ?_, forward_invariant hG ok i⟩
    exact fun x hx _ => paint_old (fun he => ok.2.1 (he ▸ hx))
  | reverse T o ok _ =>
    exact ⟨Move.reverse T o ok (fun _ => reverse_independent hG ok i), C,
      fun _ _ _ => rfl, reverse_invariant hG ok i⟩

private theorem initial_invariant {G : State} (hd : G.MinDegree 6) :
    Invariant G (fun _ => false) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simpa [weighted, Weight, State.degree] using hd x hx
  · intro x y z _ _ _
    rfl
  · intro x y u v _ _ h _ _ _
    exact h.2 rfl

private theorem source_reachable_invariant {G H : FiniteGraph.{u}}
    (hd : G.MinDegree 6) (h : SourceReach false G H) :
    SourceReach true G H ∧
      ∃ T : State, ∃ hT : T.Valid, Nonempty (H.graph ≃g T.graph hT) ∧
        ∃ C : ℕ → Bool, Invariant T C := by
  obtain ⟨S, hS, ⟨e⟩⟩ := every_finite_graph_realized G.graph
  have h0 : S.MinDegree 6 := by
    intro x hx
    obtain ⟨a, ha⟩ := e.toEquiv.surjective ⟨x, hx⟩
    have he := iso_degree_of_state hS e a
    rw [show e a = ⟨x, hx⟩ from ha] at he
    exact (hd a).trans_eq he
  induction h with
  | refl =>
    exact ⟨ReflTransGen.refl, S, hS, ⟨e⟩, _, initial_invariant h0⟩
  | tail _ m ih =>
    obtain ⟨oldHistory, T, hT, ⟨i⟩, C, inv⟩ := ih
    obtain ⟨U, step, ⟨j⟩⟩ := lift_move hT i m
    obtain ⟨strongStep, D, _, inv'⟩ := step_strengthens hT inv step
    have sourceStep := (realize_move hT strongStep).transport i.symm j.symm
    exact ⟨oldHistory.tail sourceStep, U, step.valid hT, ⟨j⟩, D, inv'⟩

theorem source_degree_six_histories {G H : FiniteGraph.{u}}
    (hd : G.MinDegree 6) : SourceReach false G H ↔ SourceReach true G H :=
  ⟨fun h => (source_reachable_invariant hd h).1, source_strong_to_ordinary⟩

theorem source_reachable_reverse_independent {G H : FiniteGraph.{u}} {K : FiniteGraph.{v}}
    (hd : G.MinDegree 6) (h : SourceReach false G H) (m : ReverseSpec H.graph K.graph) :
    m.Independent := by
  obtain ⟨_, S, hS, ⟨e⟩, _, i⟩ := source_reachable_invariant hd h
  obtain ⟨ok, hi, _⟩ := lift_reverse hS (m.relabelSource e)
  exact (m.relabelSource_independent e).mp (hi.mp (reverse_independent hS ok i))

end DeltaY
