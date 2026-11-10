/- GID: D5/S3/Combinatorics/Graph/Walks/MengerCertificates
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/MengerCertificates
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Paths, mathlib/module/Mathlib.Data.Set.Card]
   utility: none
   digest: Finite vertex separators attain pairwise disjoint path certificates and sharp arbitrary-walk weak duality. -/

import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Push

/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in
 docs/reports/licenses/menger-hamiltonian-LICENSE.txt.
Authors: Juan Pablo Traverso Gianini

Adapted source: jtraverso/menger-hamiltonian,
commit 35c5f684f9bfbd244bd0999ce725623ab571adb6,
MengerHamilton/MengerCore.lean through fam_of_le and the set-form portion of
MengerHamilton/Menger.lean. The namespace, visibility, imports and public endpoint
are adapted for this receiver; the induction and splicing proof is the source proof.
The source follows the second proof of Diestel, Graph Theory, Theorem 3.3.1
(Boehme, Goering, Harant). No originality is claimed.
Retire this port when this repository's own pinned Mathlib supplies the equivalent
entire finite set-form certificate and arbitrary-walk duality, after migrating all
consumers lawfully to direct applications.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.MengerCertificates

open SimpleGraph

variable {V : Type*}

/-- `X` separates `A` from `B` in `G`. -/
def Separates (G : SimpleGraph V) (A B X : Finset V) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ∀ p : G.Walk a b, ∃ x ∈ X, x ∈ p.support

private lemma Separates.symm {G : SimpleGraph V} {A B X : Finset V} (h : Separates G A B X) : Separates G B A X := by
  intro b hb a ha p
  obtain ⟨x, hx, hxp⟩ := h a ha b hb p.reverse
  exact ⟨x, hx, by simpa using hxp⟩

/-- `w` is reachable from `A` in `H` by a walk avoiding `Y`. -/
private def R (H : SimpleGraph V) (A Y : Finset V) (w : V) : Prop :=
  ∃ a ∈ A, ∃ p : H.Walk a w, ∀ u ∈ p.support, u ∉ Y

private lemma R.not_mem {H : SimpleGraph V} {A Y : Finset V} {w : V} (h : R H A Y w) : w ∉ Y := by
  obtain ⟨a, -, p, hp⟩ := h
  exact hp w p.end_mem_support

private lemma R.of_mem {H : SimpleGraph V} {A Y : Finset V} {w : V} (hw : w ∈ A) (hY : w ∉ Y) :
    R H A Y w :=
  ⟨w, hw, Walk.nil, by simpa using hY⟩

private lemma R_disj {H : SimpleGraph V} {A B Y : Finset V} (hY : Separates H A B Y) {w : V}
    (hA : R H A Y w) (hB : R H B Y w) : False := by
  obtain ⟨a, ha, p, hp⟩ := hA
  obtain ⟨b, hb, q, hq⟩ := hB
  obtain ⟨x, hx, hxs⟩ := hY a ha b hb (p.append q.reverse)
  rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hxs
  rcases hxs with h | h
  · exact hp x h hx
  · exact hq x h hx

private lemma path_takeUntil_end_not_mem [DecidableEq V] {H : SimpleGraph V} {a v w : V}
    (p : H.Walk a v) (hp : p.IsPath) (hw : w ∈ p.support) (hne : w ≠ v) :
    v ∉ (p.takeUntil w hw).support := by
  intro hv
  have hnd := hp.support_nodup
  rw [← p.take_spec hw, Walk.support_append] at hnd
  have h2 : v ∈ (p.dropUntil w hw).support.tail := Walk.end_mem_tail_support_of_ne hne _
  exact List.disjoint_of_nodup_append hnd hv h2

/-- The vertices other than the end of a path from `A` meeting `X ⊇ Y` only at its end are
reachable from `A` avoiding `Y`. -/
private lemma path_R {H : SimpleGraph V} {A X Y : Finset V} (hYX : Y ⊆ X) {a v : V} (ha : a ∈ A)
    (p : H.Walk a v) (hp : p.IsPath) (hX : ∀ w ∈ p.support, w ∈ X → w = v) {w : V}
    (hw : w ∈ p.support) (hne : w ≠ v) : R H A Y w := by
  classical
  refine ⟨a, ha, p.takeUntil w hw, fun u hu huY => ?_⟩
  have hu' := p.support_takeUntil_subset_support hw hu
  have := hX u hu' (hYX huY)
  subst this
  exact path_takeUntil_end_not_mem p hp hw hne hu

/-- `k` pairwise disjoint `A`–`B` paths, each meeting `A` only at its start and `B` only at its
end. -/
def Fam (G : SimpleGraph V) (A B : Finset V) (k : ℕ) : Prop :=
  ∃ P : Fin k → Σ a b : V, G.Walk a b,
    (∀ i, (P i).1 ∈ A ∧ (P i).2.1 ∈ B ∧ (P i).2.2.IsPath ∧
      (∀ w ∈ (P i).2.2.support, w ∈ A → w = (P i).1) ∧
      (∀ w ∈ (P i).2.2.support, w ∈ B → w = (P i).2.1)) ∧
    ∀ i j, i ≠ j → ∀ w ∈ (P i).2.2.support, w ∉ (P j).2.2.support

private lemma Fam.mono {G G' : SimpleGraph V} (hle : G ≤ G') {A B : Finset V} {k : ℕ}
    (h : Fam G A B k) : Fam G' A B k := by
  obtain ⟨P, hP, hd⟩ := h
  refine ⟨fun i => ⟨(P i).1, (P i).2.1, (P i).2.2.mapLe hle⟩, fun i => ?_, fun i j hij => ?_⟩
  · simp only [Walk.support_mapLe_eq_support, Walk.isPath_mapLe]
    exact hP i
  · simp only [Walk.support_mapLe_eq_support]
    exact hd i j hij

private lemma fam_base {G : SimpleGraph V} (hG : ∀ x y, ¬ G.Adj x y) {A B : Finset V} {k : ℕ}
    (hk : ∀ X, Separates G A B X → k ≤ X.card) : Fam G A B k := by
  classical
  have hsep : Separates G A B (A ∩ B) := by
    intro a ha b hb p
    cases p with
    | nil => exact ⟨a, Finset.mem_inter.2 ⟨ha, hb⟩, Walk.start_mem_support _⟩
    | cons h _ => exact absurd h (hG _ _)
  have hkc := hk _ hsep
  obtain ⟨f⟩ : Nonempty (Fin k ↪ (A ∩ B : Finset V)) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hkc)
  refine ⟨fun i => ⟨f i, f i, Walk.nil⟩, fun i => ?_, fun i j hij => ?_⟩
  · have := (f i).2
    rw [Finset.mem_inter] at this
    refine ⟨this.1, this.2, Walk.IsPath.nil, ?_, ?_⟩ <;> simp
  · simp only [Walk.support_nil, List.mem_singleton]
    rintro w rfl h
    exact hij (f.injective (Subtype.ext h))

private lemma first_use {G : SimpleGraph V} {e : Sym2 V} {A B Y : Finset V}
    (hY : Separates (G.deleteEdges {e}) A B Y) :
    ∀ {u b : V} (q : G.Walk u b), b ∈ B → R (G.deleteEdges {e}) A Y u →
      (∀ w ∈ q.support, w ∉ Y) →
      ∃ z w, G.Adj z w ∧ s(z, w) = e ∧ R (G.deleteEdges {e}) A Y z := by
  intro u b q
  induction q with
  | nil =>
    intro hb hR hq
    exact (R_disj hY hR (R.of_mem hb (hq _ (Walk.start_mem_support _)))).elim
  | @cons u w b' h q ih =>
    intro hb hR hq
    by_cases hs : s(u, w) = e
    · exact ⟨u, w, h, hs, hR⟩
    · apply ih hb ?_ (fun x hx => hq x (by simp [hx]))
      obtain ⟨a, ha, r, hr⟩ := hR
      have hadj : (G.deleteEdges {e}).Adj u w := by simp [h, hs]
      refine ⟨a, ha, r.concat hadj, fun x hx => ?_⟩
      rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hr x hx
      · exact hq x (by simp)

private lemma orient {G : SimpleGraph V} {e : Sym2 V} {A B Y : Finset V}
    (hY : Separates (G.deleteEdges {e}) A B Y) (hG : ¬ Separates G A B Y) :
    ∃ x y, G.Adj x y ∧ s(x, y) = e ∧ R (G.deleteEdges {e}) A Y x ∧
      R (G.deleteEdges {e}) B Y y := by
  simp only [Separates, not_forall, not_exists, not_and] at hG
  obtain ⟨a, ha, b, hb, p, hp⟩ := hG
  have hp' : ∀ w ∈ p.support, w ∉ Y := fun w hw hwY => hp w hwY hw
  obtain ⟨z0, w0, h0, he0, hR0⟩ :=
    first_use hY p hb (R.of_mem ha (hp' a p.start_mem_support)) hp'
  obtain ⟨z1, w1, h1, he1, hR1⟩ :=
    first_use hY.symm p.reverse ha (R.of_mem hb (hp' b p.end_mem_support)) (by simpa using hp')
  have he := he0.trans he1.symm
  rw [Sym2.eq_iff] at he
  rcases he with ⟨h2, -⟩ | ⟨h2, h3⟩
  · subst h2
    exact (R_disj hY hR0 hR1).elim
  · exact ⟨z0, w0, h0, he0, hR0, h3 ▸ hR1⟩

private lemma sep_transfer [DecidableEq V] {G : SimpleGraph V} {e : Sym2 V} {x y : V} (he : s(x, y) = e)
    {A B Y Z : Finset V} (hY : Separates (G.deleteEdges {e}) A B Y)
    (hy : ¬ R (G.deleteEdges {e}) A Y y)
    (hZ : Separates (G.deleteEdges {e}) A (insert x Y) Z) : Separates G A B Z := by
  have key : ∀ {u b : V} (q : G.Walk u b), b ∈ B → (∀ w ∈ q.support, w ∉ Z) →
      (∃ a ∈ A, ∃ r : (G.deleteEdges {e}).Walk a u, ∀ w ∈ r.support, w ∉ Z ∧ w ∉ insert x Y) →
      False := by
    intro u b q
    induction q with
    | nil =>
      rintro hb - ⟨a, ha, r, hr⟩
      obtain ⟨v, hv, hvr⟩ := hY a ha _ hb r
      exact (hr v hvr).2 (Finset.mem_insert_of_mem hv)
    | @cons u w b h q ih =>
      rintro hb hq ⟨a, ha, r, hr⟩
      have huX := (hr u r.end_mem_support).2
      have hwZ : w ∉ Z := hq w (by simp)
      by_cases hs : s(u, w) = e
      · rw [← he, Sym2.eq_iff] at hs
        rcases hs with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact huX (h1 ▸ Finset.mem_insert_self _ _)
        · subst h1
          exact hy ⟨a, ha, r, fun v hv hvY => (hr v hv).2 (Finset.mem_insert_of_mem hvY)⟩
      · have hadj : (G.deleteEdges {e}).Adj u w := by simp [h, hs]
        by_cases hwX : w ∈ insert x Y
        · obtain ⟨z, hz, hzr⟩ := hZ a ha w hwX (r.concat hadj)
          rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hzr
          rcases hzr with hzr | rfl
          · exact (hr z hzr).1 hz
          · exact hwZ hz
        · refine ih hb (fun v hv => hq v (by simp [hv])) ⟨a, ha, r.concat hadj, fun v hv => ?_⟩
          rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hv
          rcases hv with hv | rfl
          · exact hr v hv
          · exact ⟨hwZ, hwX⟩
  intro a ha b hb p
  by_contra hcon
  push Not at hcon
  have hp : ∀ w ∈ p.support, w ∉ Z := fun w hw hwZ => hcon w hwZ hw
  by_cases haX : a ∈ insert x Y
  · obtain ⟨z, hz, hzs⟩ := hZ a ha a haX Walk.nil
    simp only [Walk.support_nil, List.mem_singleton] at hzs
    subst hzs
    exact hp _ p.start_mem_support hz
  · refine key p hb hp ⟨a, ha, Walk.nil, fun w hw => ?_⟩
    simp only [Walk.support_nil, List.mem_singleton] at hw
    subst hw
    exact ⟨hp _ p.start_mem_support, haX⟩

private lemma surj_of_inj {k : ℕ} {X : Finset V} (f : Fin k → V) (hf : ∀ i, f i ∈ X)
    (hinj : Function.Injective f) (hc : X.card ≤ k) : ∀ v ∈ X, ∃ i, f i = v := by
  classical
  have hsub : Finset.univ.image f ⊆ X := by
    intro v hv
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
    exact hf i
  have hcard : X.card ≤ (Finset.univ.image f).card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    exact hc
  have := Finset.eq_of_subset_of_card_le hsub hcard
  intro v hv
  rw [← this] at hv
  obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hv
  exact ⟨i, hi⟩

private lemma fam_step {G : SimpleGraph V} {e : Sym2 V} {x y : V} (hxy : G.Adj x y)
    (he : s(x, y) = e) {A B Y : Finset V} {k : ℕ}
    (hY : Separates (G.deleteEdges {e}) A B Y) (hYk : Y.card < k)
    (hk : ∀ X, Separates G A B X → k ≤ X.card)
    (hRx : R (G.deleteEdges {e}) A Y x) (hRy : R (G.deleteEdges {e}) B Y y)
    (IH : ∀ A' B' : Finset V, (∀ X, Separates (G.deleteEdges {e}) A' B' X → k ≤ X.card) →
      Fam (G.deleteEdges {e}) A' B' k) : Fam G A B k := by
  classical
  have hle : G.deleteEdges {e} ≤ G := G.deleteEdges_le _
  have hdisj : ∀ w, R (G.deleteEdges {e}) A Y w → R (G.deleteEdges {e}) B Y w → False :=
    fun w h1 h2 => R_disj hY h1 h2
  have hxY : x ∉ Y := hRx.not_mem
  have hyY : y ∉ Y := hRy.not_mem
  have hxney : x ≠ y := hxy.ne
  have hsep1 : Separates G A B (insert x Y) := by
    intro a ha b hb q
    by_cases hq : e ∈ q.edges
    · exact ⟨x, Finset.mem_insert_self _ _, q.fst_mem_support_of_mem_edges (by rw [he]; exact hq)⟩
    · obtain ⟨v, hv, hvs⟩ := hY a ha b hb (q.toDeleteEdges {e} (fun e' he' h' => hq (by
        rw [Set.mem_singleton_iff] at h'
        exact h' ▸ he')))
      exact ⟨v, Finset.mem_insert_of_mem hv, by rwa [Walk.support_transfer] at hvs⟩
  have hc1 : (insert x Y).card = Y.card + 1 := Finset.card_insert_of_notMem hxY
  have hk1 := hk _ hsep1
  have hk0 : 0 < k := by omega
  have hc2 : (insert y Y).card = k := by rw [Finset.card_insert_of_notMem hyY]; omega
  have hc1' : (insert x Y).card = k := by omega
  obtain ⟨P, hP, hPd⟩ := IH A (insert x Y)
    (fun Z hZ => hk Z (sep_transfer he hY (fun h => hdisj y h hRy) hZ))
  obtain ⟨Q, hQ, hQd⟩ := IH B (insert y Y)
    (fun Z hZ => hk Z (sep_transfer (x := y) (y := x) (by rw [Sym2.eq_swap]; exact he) hY.symm
      (fun h => hdisj x hRx h) hZ).symm)
  have FP : ∀ i, ∀ w ∈ (P i).2.2.support, w = (P i).2.1 ∨ R (G.deleteEdges {e}) A Y w := by
    intro i w hw
    by_cases h : w = (P i).2.1
    · exact Or.inl h
    · exact Or.inr (path_R (Finset.subset_insert _ _) (hP i).1 _ (hP i).2.2.1 (hP i).2.2.2.2 hw h)
  have FQ : ∀ j, ∀ w ∈ (Q j).2.2.support, w = (Q j).2.1 ∨ R (G.deleteEdges {e}) B Y w := by
    intro j w hw
    by_cases h : w = (Q j).2.1
    · exact Or.inl h
    · exact Or.inr (path_R (Finset.subset_insert _ _) (hQ j).1 _ (hQ j).2.2.1 (hQ j).2.2.2.2 hw h)
  have hQinj : Function.Injective (fun j => (Q j).2.1) := by
    intro j j' h
    by_contra hne
    exact hQd j j' hne _ (Q j).2.2.end_mem_support
      (by simp only at h; rw [h]; exact (Q j').2.2.end_mem_support)
  have hQsurj := surj_of_inj (fun j => (Q j).2.1) (fun j => (hQ j).2.1) hQinj hc2.le
  have hJex : ∀ v, ∃ j : Fin k, v ∈ insert y Y → (Q j).2.1 = v := by
    intro v
    by_cases hv : v ∈ insert y Y
    · obtain ⟨j, hj⟩ := hQsurj v hv
      exact ⟨j, fun _ => hj⟩
    · exact ⟨⟨0, hk0⟩, fun h => absurd h hv⟩
  choose J hJ using hJex
  let σ : V → V := fun v => if v = x then y else v
  have hσX : ∀ v ∈ insert x Y, σ v ∈ insert y Y := by
    intro v hv
    by_cases h : v = x
    · simp [σ, h]
    · simp only [σ, h, ite_false]
      exact Finset.mem_insert_of_mem ((Finset.mem_insert.1 hv).resolve_left h)
  have hσinj : ∀ v ∈ insert x Y, ∀ v' ∈ insert x Y, σ v = σ v' → v = v' := by
    intro v hv v' hv' h
    by_cases h1 : v = x <;> by_cases h2 : v' = x <;> simp only [σ, h1, h2, ite_true, ite_false] at h
    · rw [h1, h2]
    · exact absurd ((Finset.mem_insert.1 hv').resolve_left h2) (h ▸ hyY)
    · exact absurd ((Finset.mem_insert.1 hv).resolve_left h1) (h ▸ hyY)
    · exact h
  let jj : Fin k → Fin k := fun i => J (σ (P i).2.1)
  have hm : ∀ i, (Q (jj i)).2.1 = σ (P i).2.1 := fun i => hJ _ (hσX _ (hP i).2.1)
  have hlink : ∀ i, ∃ l : G.Walk (P i).2.1 (Q (jj i)).2.1,
      ∀ w ∈ l.support, w = (P i).2.1 ∨ w = (Q (jj i)).2.1 := by
    intro i
    by_cases hv : (P i).2.1 = x
    · have h1 : (Q (jj i)).2.1 = y := by rw [hm]; simp [σ, hv]
      refine ⟨(Walk.cons hxy Walk.nil).copy hv.symm h1.symm, fun w hw => ?_⟩
      simp only [Walk.support_copy, Walk.support_cons, Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact Or.inl hv.symm
      · exact Or.inr h1.symm
    · have h1 : (Q (jj i)).2.1 = (P i).2.1 := by rw [hm]; simp [σ, hv]
      refine ⟨Walk.nil.copy rfl h1.symm, fun w hw => ?_⟩
      simp only [Walk.support_copy, Walk.support_nil, List.mem_singleton] at hw
      exact Or.inl hw
  choose L hL using hlink
  let W : Fin k → Σ a b : V, G.Walk a b := fun i =>
    ⟨(P i).1, (Q (jj i)).1, (((P i).2.2.mapLe hle).append
      ((L i).append ((Q (jj i)).2.2.reverse.mapLe hle))).bypass⟩
  have hWsupp : ∀ i, ∀ w ∈ (W i).2.2.support,
      w ∈ (P i).2.2.support ∨ w ∈ (Q (jj i)).2.2.support := by
    intro i w hw
    have hw' := Walk.support_bypass_subset_support _ hw
    simp only [Walk.mem_support_append_iff, Walk.support_mapLe_eq_support, Walk.support_reverse,
      List.mem_reverse] at hw'
    rcases hw' with h | h | h
    · exact Or.inl h
    · rcases hL i w h with rfl | rfl
      · exact Or.inl (P i).2.2.end_mem_support
      · exact Or.inr (Q (jj i)).2.2.end_mem_support
    · exact Or.inr h
  have hvinj : ∀ i i', i ≠ i' → (P i).2.1 ≠ (P i').2.1 := by
    intro i i' h heq
    have h2 : (P i).2.1 ∈ (P i').2.2.support := by rw [heq]; exact (P i').2.2.end_mem_support
    exact hPd i i' h _ (P i).2.2.end_mem_support h2
  have hjinj : ∀ i i', i ≠ i' → jj i ≠ jj i' := by
    intro i i' h heq
    have : σ (P i).2.1 = σ (P i').2.1 := by rw [← hm, ← hm, heq]
    exact hvinj i i' h (hσinj _ (hP i).2.1 _ (hP i').2.1 this)
  have hPQ : ∀ i i', i ≠ i' → ∀ w ∈ (P i).2.2.support, w ∉ (Q (jj i')).2.2.support := by
    intro i i' hii w hw hw'
    have hvX : (P i).2.1 ∈ insert x Y := (hP i).2.1
    rcases FP i w hw with h1 | h1 <;> rcases FQ (jj i') w hw' with h2 | h2
    · rw [hm] at h2
      by_cases hv' : (P i').2.1 = x
      · simp only [σ, hv', ite_true] at h2
        rw [← h1, h2] at hvX
        rcases Finset.mem_insert.1 hvX with h | h
        · exact hxney h.symm
        · exact hyY h
      · simp only [σ, hv', ite_false] at h2
        exact hvinj i i' hii (h1.symm.trans h2)
    · rw [← h1] at hvX
      rcases Finset.mem_insert.1 hvX with h | h
      · exact hdisj x (h ▸ hRx) (h ▸ h2)
      · exact h2.not_mem h
    · have hmX : (Q (jj i')).2.1 ∈ insert y Y := (hQ _).2.1
      rw [← h2] at hmX
      rcases Finset.mem_insert.1 hmX with h | h
      · exact hdisj y (h ▸ h1) hRy
      · exact h1.not_mem h
    · exact hdisj w h1 h2
  refine ⟨W, fun i => ⟨(hP i).1, (hQ (jj i)).1, Walk.bypass_isPath _, ?_, ?_⟩, ?_⟩
  · intro w hw hwA
    rcases hWsupp i w hw with h | h
    · exact (hP i).2.2.2.1 w h hwA
    · rcases FQ (jj i) w h with h' | h'
      · rw [hm] at h'
        by_cases hv : (P i).2.1 = x
        · simp only [σ, hv, ite_true] at h'
          subst h'
          exact (hdisj _ (R.of_mem hwA hyY) hRy).elim
        · simp only [σ, hv, ite_false] at h'
          exact (hP i).2.2.2.1 w (h' ▸ (P i).2.2.end_mem_support) hwA
      · exact (hdisj w (R.of_mem hwA h'.not_mem) h').elim
  · intro w hw hwB
    rcases hWsupp i w hw with h | h
    · rcases FP i w h with h' | h'
      · by_cases hv : (P i).2.1 = x
        · rw [hv] at h'
          subst h'
          exact (hdisj _ hRx (R.of_mem hwB hxY)).elim
        · have : w = (Q (jj i)).2.1 := by rw [hm]; simp [σ, hv, h']
          exact (hQ (jj i)).2.2.2.1 w (this ▸ (Q (jj i)).2.2.end_mem_support) hwB
      · exact (hdisj w h' (R.of_mem hwB h'.not_mem)).elim
    · exact (hQ (jj i)).2.2.2.1 w h hwB
  · intro i i' hii w hw hw'
    rcases hWsupp i w hw with h | h <;> rcases hWsupp i' w hw' with h' | h'
    · exact hPd i i' hii w h h'
    · exact hPQ i i' hii w h h'
    · exact hPQ i' i (Ne.symm hii) w h' h
    · exact hQd _ _ (hjinj i i' hii) w h h'

/-- Core of Menger's theorem: if every `A`–`B` separator has at least `k` vertices, there are
`k` disjoint `A`–`B` paths. -/
theorem fam_of_le [Finite V] (n : ℕ) : ∀ (G : SimpleGraph V), G.edgeSet.ncard = n →
    ∀ (A B : Finset V) (k : ℕ), (∀ X, Separates G A B X → k ≤ X.card) → Fam G A B k := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G hn A B k hk
  by_cases hG : ∀ x y, ¬ G.Adj x y
  · exact fam_base hG hk
  push Not at hG
  obtain ⟨x, y, hxy⟩ := hG
  have hlt : (G.deleteEdges {s(x, y)}).edgeSet.ncard < n := by
    rw [edgeSet_deleteEdges, ← hn]
    exact Set.ncard_sdiff_singleton_lt_of_mem hxy (Set.toFinite _)
  have IH := fun A' B' => ih _ hlt (G.deleteEdges {s(x, y)}) rfl A' B' k
  by_cases hall : ∀ X, Separates (G.deleteEdges {s(x, y)}) A B X → k ≤ X.card
  · exact (IH A B hall).mono (G.deleteEdges_le _)
  push Not at hall
  obtain ⟨Y, hY, hYk⟩ := hall
  have hGY : ¬ Separates G A B Y := fun h => absurd (hk Y h) (by omega)
  obtain ⟨x', y', hadj, he', hRx, hRy⟩ := orient hY hGY
  exact fam_step hadj he' hY hYk hk hRx hRy IH

/-- Finite set-form Menger certificates, together with weak duality for every
pairwise vertex-disjoint family of arbitrary walks. Empty and overlapping terminal
sets are allowed; supports include endpoints and nil paths are permitted. -/
theorem exists_separator_paths_and_weak_duality [Finite V] (G : SimpleGraph V)
    (A B : Finset V) :
    (∃ X : Finset V, Separates G A B X ∧
      ∃ (a b : Fin X.card → V) (p : ∀ i, G.Walk (a i) (b i)),
        (∀ i, a i ∈ A ∧ b i ∈ B ∧ (p i).IsPath) ∧
        ∀ i j, i ≠ j → ∀ x ∈ (p i).support, x ∉ (p j).support) ∧
    (∀ Y : Finset V, Separates G A B Y →
      ∀ (m : ℕ) (a b : Fin m → V) (p : ∀ i, G.Walk (a i) (b i)),
        (∀ i, a i ∈ A) → (∀ i, b i ∈ B) →
        (∀ i j, i ≠ j → ∀ x ∈ (p i).support, x ∉ (p j).support) →
        m ≤ Y.card) := by
  classical
  constructor
  · have := Fintype.ofFinite V
    obtain ⟨X, hXmem, hXmin⟩ := Finset.exists_min_image
      (Finset.univ.filter (fun X : Finset V => Separates G A B X)) Finset.card
      ⟨A, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun a ha b _ p => ⟨a, ha, p.start_mem_support⟩⟩⟩
    rw [Finset.mem_filter] at hXmem
    obtain ⟨P, hP, hd⟩ := fam_of_le _ G rfl A B X.card
      (fun Z hZ => hXmin Z (Finset.mem_filter.2 ⟨Finset.mem_univ _, hZ⟩))
    exact ⟨X, hXmem.2, fun i => (P i).1, fun i => (P i).2.1, fun i => (P i).2.2,
      fun i => ⟨(hP i).1, (hP i).2.1, (hP i).2.2.1⟩, hd⟩
  · intro Y hY m a b p hA hB hdisj
    have h : ∀ i, ∃ x ∈ Y, x ∈ (p i).support := fun i => hY _ (hA i) _ (hB i) (p i)
    choose f hfY hfp using h
    have hinj : Set.InjOn f ((Finset.univ : Finset (Fin m)) : Set (Fin m)) := by
      intro i _ j _ hij
      by_contra hne
      exact hdisj i j hne _ (hfp i) (by rw [hij]; exact hfp j)
    simpa using Finset.card_le_card_of_injOn f (fun i _ => hfY i) hinj

end D5.S3.Combinatorics.Graph.Walks.MengerCertificates
