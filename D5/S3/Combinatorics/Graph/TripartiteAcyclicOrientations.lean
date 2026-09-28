/- GID: D5/S3/Combinatorics/Graph/TripartiteAcyclicOrientations
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/TripartiteAcyclicOrientations
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Proves clause (4) of Conjecture 1 of Mühlherr and Poullot (arXiv:2609.02249): for all m, n, p >= 1 not all odd, the complete tripartite graph K_{m,n,p} has a number of acyclic orientations congruent to 2 modulo 4 (the value T(2, 0) of its Tutte polynomial, the q = -1 point of the Potts model). -/

/-
proof_shape: result: content
escape_witness: form (2): the conclusion `result` itself, produced on its live path by the Klein
  lemma `klein` (two commuting involutions acting freely with their product force 4 | card), the
  twin lemma `twin` (for non-adjacent twins u, v and an edge avoiding them, the acyclic
  orientations of G and of G - v agree modulo 4, through the reversal, the swap of u and v, and
  the bijection between swap-fixed orientations and those of G - v), the count `k3` of the
  acyclic orientations of the triangle and the induction `main` over three-coloured complete
  multipartite graphs
admission_basis: open-problem-resolution (issue #11156)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.TripartiteAcyclicOrientations

open Finset

/-!
L. Mühlherr and G. Poullot, "Hamiltonicity of graphs of acyclic orientations and acyclic
polynomials" (arXiv:2609.02249, 2026), Conjecture 1: for the listed graphs the number ψ(G) of
acyclic orientations is congruent to 2 modulo 4; clause (4) lists the complete tripartite graphs
K_{m,n,p} with m, n, p not all odd. ψ(G) = (-1)^|V| χ_G(-1) = T_G(2, 0) is the value of the Tutte
polynomial at the q = -1 point of the Potts model. The proof below gives the congruence for all
m, n, p ≥ 1.
-/

/-- `d` orients the simple graph `G`: every edge `{a, b}` carries exactly one of the arcs `a → b`,
`b → a`, and there is no other arc. -/
def IsOrientation {V : Type*} (G : SimpleGraph V) (d : V → V → Bool) : Prop :=
  ∀ a b, d a b = true ↔ (G.Adj a b ∧ d b a = false)

/-- `d` has no directed cycle: its transitive closure has no loop. -/
def IsAcyclic {V : Type*} (d : V → V → Bool) : Prop :=
  ∀ a, ¬ Relation.TransGen (fun x y => d x y = true) a a

/-- ψ(G), the number of acyclic orientations of `G`. -/
noncomputable def acyclicOrientationCount {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  Nat.card {d : V → V → Bool // IsOrientation G d ∧ IsAcyclic d}

/-- Clause (4) of Conjecture 1: for m, n, p ≥ 1 not all odd, the complete tripartite graph
K_{m,n,p} (Mathlib's complete multipartite graph with parts of sizes m, n, p) has ψ ≡ 2 mod 4. -/
def claim : Prop :=
  ∀ m n p : ℕ, 1 ≤ m → 1 ≤ n → 1 ≤ p → ¬ (Odd m ∧ Odd n ∧ Odd p) →
    acyclicOrientationCount
      (SimpleGraph.completeMultipartiteGraph (fun i : Fin 3 => Fin (![m, n, p] i))) % 4 = 2

theorem result : claim := by
  classical
  -- Klein lemma
  have klein : ∀ {α : Type} [DecidableEq α] (Y : Finset α) (r s : α → α),
      (∀ x, r (r x) = x) → (∀ x, s (s x) = x) → (∀ x, r (s x) = s (r x)) →
      (∀ x ∈ Y, r x ∈ Y) → (∀ x ∈ Y, s x ∈ Y) →
      (∀ x ∈ Y, r x ≠ x) → (∀ x ∈ Y, s x ≠ x) → (∀ x ∈ Y, r (s x) ≠ x) → 4 ∣ Y.card := by
    intro α _ Y r s hr hs hrs
    induction Y using Finset.strongInduction with
    | H Y ih =>
      intro cr cs fr fs frs
      rcases Y.eq_empty_or_nonempty with h | ⟨x, hx⟩
      · simp [h]
      set O : Finset α := {x, r x, s x, r (s x)} with hO
      have hOY : O ⊆ Y := by
        intro y hy
        simp only [hO, mem_insert, mem_singleton] at hy
        rcases hy with rfl | rfl | rfl | rfl
        · exact hx
        · exact cr _ hx
        · exact cs _ hx
        · exact cr _ (cs _ hx)
      have h1 := fr x hx
      have h2 := fs x hx
      have h3 := frs x hx
      have hOcard : O.card = 4 := by
        have a1 : x ≠ r x := fun h => h1 h.symm
        have a2 : x ≠ s x := fun h => h2 h.symm
        have a3 : x ≠ r (s x) := fun h => h3 h.symm
        have a4 : r x ≠ s x := by
          intro h; apply h3; rw [← h, hr]
        have a5 : r x ≠ r (s x) := by
          intro h; apply h2
          have := congrArg r h; rw [hr, hr] at this; exact this.symm
        have a6 : s x ≠ r (s x) := by
          intro h; exact fr _ (cs _ hx) h.symm
        rw [hO, card_insert_of_notMem (by simp [a1, a2, a3]),
          card_insert_of_notMem (by simp [a4, a5]), card_insert_of_notMem (by simp [a6]),
          card_singleton]
      have hmemO : ∀ y, y ∈ O ↔ y = x ∨ y = r x ∨ y = s x ∨ y = r (s x) := by
        intro y; simp [hO]
      have closeR : ∀ y, y ∈ O ↔ r y ∈ O := by
        intro y; rw [hmemO, hmemO]
        constructor
        · rintro (rfl | rfl | rfl | rfl) <;> simp [hr, hrs]
        · intro h
          rcases h with h | h | h | h
          · right; left; rw [← h, hr]
          · left; rw [← hr y, h, hr]
          · right; right; right; rw [← hr y, h, hrs]
          · right; right; left; rw [← hr y, h, hr]
      have closeS : ∀ y, y ∈ O ↔ s y ∈ O := by
        intro y; rw [hmemO, hmemO]
        constructor
        · rintro (rfl | rfl | rfl | rfl) <;> simp [hs, hrs]
        · intro h
          rcases h with h | h | h | h
          · right; right; left; rw [← h, hs]
          · right; right; right; rw [← hs y, h, ← hrs]
          · left; rw [← hs y, h, hs]
          · right; left; rw [← hs y, h, ← hrs, hs]
      have hsub : Y \ O ⊂ Y := by
        refine ⟨sdiff_subset, fun h => ?_⟩
        have : x ∈ Y \ O := h hx
        simp [hO] at this
      have hrec := ih (Y \ O) hsub
        (fun y hy => by
          rw [mem_sdiff] at hy ⊢
          exact ⟨cr _ hy.1, fun h => hy.2 ((closeR y).mpr h)⟩)
        (fun y hy => by
          rw [mem_sdiff] at hy ⊢
          exact ⟨cs _ hy.1, fun h => hy.2 ((closeS y).mpr h)⟩)
        (fun y hy => fr y (mem_sdiff.mp hy).1) (fun y hy => fs y (mem_sdiff.mp hy).1)
        (fun y hy => frs y (mem_sdiff.mp hy).1)
      have hcard : Y.card = (Y \ O).card + O.card := (card_sdiff_add_card_eq_card hOY).symm
      rw [hcard, hOcard]
      exact Nat.dvd_add hrec (dvd_refl 4)
  -- ranking lemma
  have rank : ∀ {V : Type} (d : V → V → Bool) (f : V → ℕ),
      (∀ a b, d a b = true → f a < f b) → IsAcyclic d := by
    intro V d f hf a h
    have key : ∀ x y, Relation.TransGen (fun x y => d x y = true) x y → f x < f y := by
      intro x y hxy
      induction hxy with
      | single hab => exact hf _ _ hab
      | tail _ hbc ih => exact ih.trans (hf _ _ hbc)
    exact lt_irrefl _ (key a a h)
  -- K3
  have k3 : acyclicOrientationCount (⊤ : SimpleGraph (Fin 3)) = 6 := by
    let bit : Bool × Bool × Bool → Fin 3 → Fin 3 → Bool := fun t a b =>
      if a = 0 ∧ b = 1 then t.1 else if a = 0 ∧ b = 2 then t.2.1 else t.2.2
    let D : Bool × Bool × Bool → Fin 3 → Fin 3 → Bool := fun t a b =>
      if a < b then bit t a b else if b < a then !bit t b a else false
    have hDor : ∀ t, IsOrientation (⊤ : SimpleGraph (Fin 3)) (D t) := by
      intro t a b
      simp only [SimpleGraph.top_adj]
      revert t a b
      decide
    have hDeq : ∀ d, IsOrientation (⊤ : SimpleGraph (Fin 3)) d → d = D (d 0 1, d 0 2, d 1 2) := by
      intro d hd
      have dd : ∀ a, d a a = false := by
        intro a
        cases h : d a a
        · rfl
        · have := (hd a a).mp h
          simp at this
      have anti : ∀ a b, a ≠ b → d b a = !d a b := by
        intro a b hab
        have h1 := hd a b
        rw [SimpleGraph.top_adj] at h1
        cases h : d a b <;> cases h' : d b a <;> simp_all
      funext a b
      fin_cases a <;> fin_cases b <;>
        simp [D, bit, dd, anti 0 1 (by decide), anti 0 2 (by decide), anti 1 2 (by decide)]
    let good : Bool × Bool × Bool → Prop := fun t =>
      t ≠ (true, false, true) ∧ t ≠ (false, true, false)
    have acyc : ∀ t, good t → IsAcyclic (D t) := by
      intro t ht
      refine rank (D t) (fun a => (Finset.univ.filter (fun b => D t b a = true)).card) ?_
      revert t
      decide
    have goodOf : ∀ d, IsOrientation (⊤ : SimpleGraph (Fin 3)) d → IsAcyclic d →
        good (d 0 1, d 0 2, d 1 2) := by
      intro d hd ha
      have e := hDeq d hd
      have o : ∀ a b : Fin 3, d a b = true ↔ (a ≠ b ∧ d b a = false) := by
        intro a b; rw [hd a b, SimpleGraph.top_adj]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · simp only [Prod.mk.injEq] at h
        obtain ⟨h01, h02, h12⟩ := h
        have h20 : d 2 0 = true := (o 2 0).mpr ⟨by decide, h02⟩
        exact ha 0 (Relation.TransGen.tail (Relation.TransGen.tail
          (Relation.TransGen.single h01) h12) h20)
      · simp only [Prod.mk.injEq] at h
        obtain ⟨h01, h02, h12⟩ := h
        have h21 : d 2 1 = true := (o 2 1).mpr ⟨by decide, h12⟩
        have h10 : d 1 0 = true := (o 1 0).mpr ⟨by decide, h01⟩
        exact ha 0 (Relation.TransGen.tail (Relation.TransGen.tail
          (Relation.TransGen.single h02) h21) h10)
    have e : {d : Fin 3 → Fin 3 → Bool // IsOrientation (⊤ : SimpleGraph (Fin 3)) d ∧ IsAcyclic d}
        ≃ {t : Bool × Bool × Bool // good t} :=
      { toFun := fun d => ⟨(d.1 0 1, d.1 0 2, d.1 1 2), goodOf d.1 d.2.1 d.2.2⟩
        invFun := fun t => ⟨D t.1, hDor t.1, acyc t.1 t.2⟩
        left_inv := fun d => Subtype.ext (hDeq d.1 d.2.1).symm
        right_inv := fun t => by
          rcases t with ⟨⟨x, y, z⟩, _⟩
          cases x <;> cases y <;> cases z <;> rfl }
    rw [acyclicOrientationCount, Nat.card_congr e, Nat.card_eq_fintype_card]
    decide
  -- counting through a finset
  have cardEq : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      acyclicOrientationCount G =
        (Finset.univ.filter (fun d : V → V → Bool => IsOrientation G d ∧ IsAcyclic d)).card := by
    intro V _ _ G
    classical
    rw [acyclicOrientationCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  -- twin lemma
  have twin : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (u v : V),
      u ≠ v → ¬ G.Adj u v → (∀ w, G.Adj u w ↔ G.Adj v w) →
      (∃ a b, G.Adj a b ∧ a ≠ u ∧ a ≠ v ∧ b ≠ u ∧ b ≠ v) →
      acyclicOrientationCount G % 4 = acyclicOrientationCount (G.induce {w | w ≠ v}) % 4 := by
    intro V _ _ G u v huv hnadj htw hedge
    classical
    obtain ⟨a0, b0, hab0, ha0u, ha0v, hb0u, hb0v⟩ := hedge
    let sw := Equiv.swap u v
    have autAdj1 : ∀ a b, G.Adj a b → G.Adj (sw a) (sw b) := by
      intro a b h
      by_cases hau : a = u
      · subst hau
        by_cases hbv : b = v
        · exact absurd (hbv ▸ h) hnadj
        · have hbu : b ≠ a := fun e => G.irrefl (e ▸ h)
          rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hbu hbv]
          exact (htw b).mp h
      · by_cases hav : a = v
        · subst hav
          by_cases hbu : b = u
          · exact absurd (hbu ▸ h).symm hnadj
          · have hbv : b ≠ a := fun e => G.irrefl (e ▸ h)
            rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hbu hbv]
            exact (htw b).mpr h
        · rw [Equiv.swap_apply_of_ne_of_ne hau hav]
          by_cases hbu : b = u
          · subst hbu; rw [Equiv.swap_apply_left]; exact ((htw a).mp h.symm).symm
          · by_cases hbv : b = v
            · subst hbv; rw [Equiv.swap_apply_right]; exact ((htw a).mpr h.symm).symm
            · rw [Equiv.swap_apply_of_ne_of_ne hbu hbv]; exact h
    have autAdj : ∀ a b, G.Adj (sw a) (sw b) ↔ G.Adj a b := by
      intro a b
      refine ⟨fun h => ?_, autAdj1 a b⟩
      have := autAdj1 _ _ h
      simpa [sw, Equiv.swap_apply_self] using this
    let P : (V → V → Bool) → Prop := fun d => IsOrientation G d ∧ IsAcyclic d
    let X := Finset.univ.filter P
    let S : (V → V → Bool) → V → V → Bool := fun d a b => d (sw a) (sw b)
    let R : (V → V → Bool) → V → V → Bool := fun d a b => d b a
    have hSP : ∀ d, P d → P (S d) := by
      intro d ⟨ho, hac⟩
      refine ⟨fun a b => ?_, fun x hx => ?_⟩
      · show d (sw a) (sw b) = true ↔ G.Adj a b ∧ d (sw b) (sw a) = false
        rw [ho, autAdj]
      · exact hac (sw x) (Relation.TransGen.lift sw (fun a b h => h) x x hx)
    have hRP : ∀ d, P d → P (R d) := by
      intro d ⟨ho, hac⟩
      refine ⟨fun a b => ?_, fun x hx => ?_⟩
      · show d b a = true ↔ G.Adj a b ∧ d a b = false
        rw [ho, G.adj_comm]
      · exact hac x (Relation.transGen_swap.mp hx)
    have hSS : ∀ d, S (S d) = d := by
      intro d; funext a b; simp [S, sw, Equiv.swap_apply_self]
    have hRR : ∀ d, R (R d) = d := fun d => rfl
    have hRS : ∀ d, R (S d) = S (R d) := fun d => rfl
    have edgeNe : ∀ d, P d → d b0 a0 ≠ d a0 b0 := by
      intro d ⟨ho, _⟩ h
      have o1 := ho a0 b0
      cases hx : d a0 b0
      · rw [hx] at h
        have : ¬ (G.Adj a0 b0 ∧ d b0 a0 = false) := fun hh => by simpa [hx] using o1.mpr hh
        exact this ⟨hab0, h⟩
      · rw [hx] at h
        have := (o1.mp hx).2
        rw [h] at this; exact Bool.noConfusion this
    have sw_a0 : sw a0 = a0 := Equiv.swap_apply_of_ne_of_ne ha0u ha0v
    have sw_b0 : sw b0 = b0 := Equiv.swap_apply_of_ne_of_ne hb0u hb0v
    let Y := X.filter (fun d => ¬ S d = d)
    have hY : 4 ∣ Y.card := by
      refine klein Y R S hRR hSS hRS ?_ ?_ ?_ ?_ ?_
      · intro d hd
        simp only [Y, X, Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
        refine ⟨hRP d hd.1, fun h => hd.2 ?_⟩
        have := congrArg R h
        simp only [hRS, hRR] at this
        exact this
      · intro d hd
        simp only [Y, X, Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
        refine ⟨hSP d hd.1, fun h => hd.2 ?_⟩
        rw [hSS] at h; exact h.symm
      · intro d hd h
        simp only [Y, X, Finset.mem_filter, Finset.mem_univ, true_and] at hd
        exact edgeNe d hd.1 (congrFun (congrFun h a0) b0)
      · intro d hd
        simp only [Y, X, Finset.mem_filter, Finset.mem_univ, true_and] at hd
        exact hd.2
      · intro d hd h
        simp only [Y, X, Finset.mem_filter, Finset.mem_univ, true_and] at hd
        have := congrFun (congrFun h a0) b0
        simp only [R, S, sw_a0, sw_b0] at this
        exact edgeNe d hd.1 this
    -- fixed points of S versus orientations of G - v
    let W := {w : V // w ∈ ({w | w ≠ v} : Set V)}
    let G' := G.induce {w | w ≠ v}
    let P' : (W → W → Bool) → Prop := fun d => IsOrientation G' d ∧ IsAcyclic d
    let φ : V → W := fun a => if h : a = v then ⟨u, huv⟩ else ⟨a, h⟩
    have φval : ∀ a, (φ a).1 = if a = v then u else a := by
      intro a; by_cases h : a = v <;> simp [φ, h]
    have adjφ : ∀ a b, G.Adj a b ↔ G.Adj (φ a).1 (φ b).1 := by
      intro a b
      rw [φval, φval]
      by_cases ha : a = v <;> by_cases hb : b = v
      · subst ha; subst hb; simp
      · subst ha; simp [hb, htw b]
      · subst hb; simp [ha, G.adj_comm a, htw a]
      · simp [ha, hb]
    have φsw : ∀ a, φ (sw a) = φ a := by
      intro a
      apply Subtype.ext
      rw [φval, φval]
      by_cases hau : a = u
      · subst hau; simp [sw, huv]
      · by_cases hav : a = v
        · subst hav; simp [sw]
        · simp [sw, Equiv.swap_apply_of_ne_of_ne hau hav, hav]
    have hfix : (X.filter (fun d => S d = d)).card = (Finset.univ.filter P').card := by
      refine Finset.card_bij' (fun d _ x y => d x.1 y.1) (fun d _ a b => d (φ a) (φ b))
        ?_ ?_ ?_ ?_
      · intro d hd
        simp only [X, Finset.mem_filter, Finset.mem_univ, true_and] at hd
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨fun x y => ?_, fun x hx => ?_⟩
        · rw [hd.1.1 x.1 y.1]; rfl
        · exact hd.1.2 x.1 (Relation.TransGen.lift Subtype.val (fun a b h => h) x x hx)
      · intro d hd
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
        simp only [X, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨⟨fun a b => ?_, fun x hx => ?_⟩, ?_⟩
        · show d (φ a) (φ b) = true ↔ G.Adj a b ∧ d (φ b) (φ a) = false
          rw [hd.1 (φ a) (φ b), adjφ]; rfl
        · exact hd.2 (φ x) (Relation.TransGen.lift φ (fun a b h => h) x x hx)
        · funext a b; show d (φ (sw a)) (φ (sw b)) = d (φ a) (φ b); rw [φsw, φsw]
      · intro d hd
        simp only [X, Finset.mem_filter, Finset.mem_univ, true_and] at hd
        obtain ⟨⟨ho, _⟩, hS⟩ := hd
        have noArc : ∀ a b, ¬ G.Adj a b → d a b = false := by
          intro a b h
          cases hx : d a b
          · rfl
          · exact absurd (ho a b |>.mp hx).1 h
        have fixed : ∀ a b, d (sw a) (sw b) = d a b := fun a b => congrFun (congrFun hS a) b
        funext a b
        show d (φ a).1 (φ b).1 = d a b
        rw [φval, φval]
        by_cases ha : a = v <;> by_cases hb : b = v
        · simp only [if_pos ha, if_pos hb]
          rw [ha, hb, noArc u u G.irrefl, noArc v v G.irrefl]
        · subst ha
          simp only [if_true, hb, if_false]
          by_cases hbu : b = u
          · subst hbu
            rw [noArc b b G.irrefl, noArc a b (fun h => hnadj h.symm)]
          · have := fixed a b
            rwa [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hbu hb] at this
        · subst hb
          simp only [if_true, ha, if_false]
          by_cases hau : a = u
          · subst hau
            rw [noArc a a G.irrefl, noArc a b hnadj]
          · have := fixed a b
            rwa [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hau ha] at this
        · simp [ha, hb]
      · intro d _
        funext x y
        have hx : φ x.1 = x := by
          apply Subtype.ext; rw [φval]; simp [show x.1 ≠ v from x.2]
        have hy : φ y.1 = y := by
          apply Subtype.ext; rw [φval]; simp [show y.1 ≠ v from y.2]
        show d (φ x.1) (φ y.1) = d x y
        rw [hx, hy]
    have split := Finset.card_filter_add_card_filter_not (s := X) (fun d => S d = d)
    have hX : acyclicOrientationCount G =
        (X.filter (fun d => S d = d)).card + (X.filter (fun d => ¬ S d = d)).card := by
      rw [cardEq G]; exact split.symm
    have hF : (X.filter (fun d => S d = d)).card =
        acyclicOrientationCount (G.induce {w | w ≠ v}) := by
      rw [hfix, cardEq]
    have hY' : 4 ∣ (X.filter (fun d => ¬ S d = d)).card := hY
    rw [hX, hF]
    omega
  -- invariance under a bijection of the vertices
  have iso : ∀ {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] (e : V ≃ W)
      (H : SimpleGraph W), acyclicOrientationCount (H.comap e) = acyclicOrientationCount H := by
    intro V W _ _ _ _ e H
    rw [acyclicOrientationCount, acyclicOrientationCount]
    refine Nat.card_congr
      { toFun := fun d => ⟨fun a b => d.1 (e.symm a) (e.symm b), fun a b => ?_, fun x hx => ?_⟩
        invFun := fun d => ⟨fun a b => d.1 (e a) (e b), fun a b => ?_, fun x hx => ?_⟩
        left_inv := fun d => Subtype.ext (by funext a b; simp)
        right_inv := fun d => Subtype.ext (by funext a b; simp) }
    · have h := d.2.1 (e.symm a) (e.symm b)
      simpa [SimpleGraph.comap_adj] using h
    · exact d.2.2 (e.symm x) (Relation.TransGen.lift e.symm (fun a b h => h) x x hx)
    · have h := d.2.1 (e a) (e b)
      simpa [SimpleGraph.comap_adj] using h
    · exact d.2.2 (e x) (Relation.TransGen.lift e (fun a b h => h) x x hx)
  -- induction on the number of vertices of a three-coloured complete multipartite graph
  have main : ∀ (N : ℕ) (V : Type) [Fintype V] [DecidableEq V] (c : V → Fin 3),
      Fintype.card V = N → Function.Surjective c →
      acyclicOrientationCount ((⊤ : SimpleGraph (Fin 3)).comap c) % 4 = 2 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro V _ _ c hN hc
      by_cases hdup : ∃ u v, u ≠ v ∧ c u = c v
      · obtain ⟨u, v, huv, hcuv⟩ := hdup
        have adj : ∀ a b, ((⊤ : SimpleGraph (Fin 3)).comap c).Adj a b ↔ c a ≠ c b := by
          intro a b; simp
        have colours : ∀ k : Fin 3, k + 1 ≠ k ∧ k + 2 ≠ k ∧ k + 1 ≠ k + 2 := by decide
        obtain ⟨a, ha⟩ := hc (c u + 1)
        obtain ⟨b, hb⟩ := hc (c u + 2)
        obtain ⟨k1, k2, k12⟩ := colours (c u)
        have htw := twin ((⊤ : SimpleGraph (Fin 3)).comap c) u v huv
          (by rw [adj]; exact not_not.mpr hcuv) (fun w => by rw [adj, adj, hcuv])
          ⟨a, b, by rw [adj, ha, hb]; exact k12,
            fun h => k1 (by rw [← ha, h]), fun h => k1 (by rw [← ha, h, hcuv]),
            fun h => k2 (by rw [← hb, h]), fun h => k2 (by rw [← hb, h, hcuv])⟩
        rw [htw]
        have hind : ((⊤ : SimpleGraph (Fin 3)).comap c).induce {w | w ≠ v} =
            (⊤ : SimpleGraph (Fin 3)).comap (fun w : {w // w ∈ {w : V | w ≠ v}} => c w.1) := by
          ext x y; simp
        rw [hind]
        have hcard : Fintype.card {w // w ∈ {w : V | w ≠ v}} = N - 1 := by
          rw [← hN]; exact Set.card_ne_eq v
        have hpos : 2 ≤ N := by
          rw [← hN]; exact Fintype.one_lt_card_iff.mpr ⟨u, v, huv⟩
        refine ih (N - 1) (by omega) _ (fun w => c w.1) hcard ?_
        intro k
        obtain ⟨w, hw⟩ := hc k
        by_cases hwv : w = v
        · exact ⟨⟨u, huv⟩, by rw [← hw, hwv, ← hcuv]⟩
        · exact ⟨⟨w, hwv⟩, hw⟩
      · have hinj : Function.Injective c := by
          intro x y h
          by_contra hxy
          exact hdup ⟨x, y, hxy, h⟩
        have h6 : acyclicOrientationCount ((⊤ : SimpleGraph (Fin 3)).comap c) = 6 := by
          rw [← k3]
          exact iso (Equiv.ofBijective c ⟨hinj, hc⟩) ⊤
        rw [h6]
  intro m n p hm hn hp _
  refine main _ (Σ i : Fin 3, Fin (![m, n, p] i)) Sigma.fst rfl ?_
  intro i
  fin_cases i
  · exact ⟨⟨0, ⟨0, by simp; omega⟩⟩, rfl⟩
  · exact ⟨⟨1, ⟨0, by simp; omega⟩⟩, rfl⟩
  · exact ⟨⟨2, ⟨0, by simp; omega⟩⟩, rfl⟩

end D5.S3.Combinatorics.Graph.TripartiteAcyclicOrientations
