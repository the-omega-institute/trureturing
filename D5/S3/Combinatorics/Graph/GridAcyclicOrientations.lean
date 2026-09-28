/- GID: D5/S3/Combinatorics/Graph/GridAcyclicOrientations
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/GridAcyclicOrientations
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/GridAcyclicOrientations.claim; result=D5/S3/Combinatorics/Graph/GridAcyclicOrientations.result; claim=D5/S3/Combinatorics/Graph/GridAcyclicOrientations.claim
   digest: Refutes clause (1) of Conjecture 1 of Mühlherr and Poullot (arXiv:2609.02249): the 7 x 7 grid graph P_7 x P_7 has a number of acyclic orientations divisible by 4 (the value T(2, 0) of its Tutte polynomial, the q = -1 point of the Potts model), through the congruence psi(P_{2a+1} x P_n) = psi(P_{a+1} x P_n) mod 4. -/

/-
proof_shape: result: content
escape_witness: form (1): the orbit lemma `orbitAO` (commuting involutions with the arc reversal
  free give |Y| = |Fix s| + |Fix rs| mod 4), the fold lemma `fold` (the invariant acyclic
  orientations of a graph with an involutive automorphism correspond to the acyclic orientations
  of a half), the odd-grid congruence `oddFold` (psi(P_{2a+1} x P_n) = psi(P_{a+1} x P_n) mod 4)
  and the count `four` of the 4 x 4 grid modulo 4 (a rotation-invariant orientation has a directed
  cycle around the centre, and reversing the corner edges acts freely)
admission_basis: open-problem-resolution (issue #11166)
Direct frozen dependencies: D5/S3/Combinatorics/Graph/TripartiteAcyclicOrientations (definitions)
-/

import D5.S3.Combinatorics.Graph.TripartiteAcyclicOrientations
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.GridAcyclicOrientations

open Finset
open D5.S3.Combinatorics.Graph.TripartiteAcyclicOrientations
  (IsOrientation IsAcyclic acyclicOrientationCount)

/-!
L. Mühlherr and G. Poullot, "Hamiltonicity of graphs of acyclic orientations and acyclic
polynomials" (arXiv:2609.02249, 2026), Conjecture 1, clause (1): for m, n ≥ 3 both odd, the grid
graph P_m × P_n has a number ψ of acyclic orientations congruent to 2 modulo 4. ψ(G) = T_G(2, 0)
is the value of the Tutte polynomial at the q = -1 point of the Potts model. The proof below shows
ψ(P_{2a+1} × P_n) ≡ ψ(P_{a+1} × P_n) (mod 4) and ψ(P_4 × P_4) ≡ 0 (mod 4), so ψ(P_7 × P_7) ≡ 0.
-/

/-- Clause (1) of Conjecture 1: for m, n ≥ 3 both odd, the grid graph P_m × P_n (Mathlib's box
product of two path graphs) has ψ ≡ 2 mod 4. -/
def claim : Prop :=
  ∀ m n : ℕ, 3 ≤ m → 3 ≤ n → Odd m → Odd n →
    acyclicOrientationCount (SimpleGraph.pathGraph m □ SimpleGraph.pathGraph n) % 4 = 2

theorem result : ¬ claim := by
  classical
  intro hclaim
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
  -- orbit lemma: |Y| ≡ |Fix s| + |Fix rs| (mod 4) when r is free on Y
  have orbit : ∀ {α : Type} [DecidableEq α] (Y : Finset α) (r s : α → α),
      (∀ x, r (r x) = x) → (∀ x, s (s x) = x) → (∀ x, r (s x) = s (r x)) →
      (∀ x ∈ Y, r x ∈ Y) → (∀ x ∈ Y, s x ∈ Y) → (∀ x ∈ Y, r x ≠ x) →
      Y.card % 4 = ((Y.filter (fun x => s x = x)).card +
        (Y.filter (fun x => r (s x) = x)).card) % 4 := by
    intro α _ Y r s hr hs hrs cr cs fr
    have hZ : 4 ∣ (Y.filter (fun x => ¬ s x = x ∧ ¬ r (s x) = x)).card := by
      refine klein _ r s hr hs hrs ?_ ?_ ?_ ?_ ?_
      · intro x hx
        rw [mem_filter] at hx ⊢
        refine ⟨cr x hx.1, fun h => hx.2.1 ?_, fun h => hx.2.2 ?_⟩
        · have h2 : r (s x) = r x := by rw [hrs]; exact h
          have := congrArg r h2
          rwa [hr, hr] at this
        · rw [hrs, hr] at h
          rw [h, hr]
      · intro x hx
        rw [mem_filter] at hx ⊢
        refine ⟨cs x hx.1, fun h => hx.2.1 ?_, fun h => hx.2.2 ?_⟩
        · rw [hs] at h; exact h.symm
        · rw [hs] at h
          rw [← h, hr]
      · intro x hx; exact fr x (mem_filter.mp hx).1
      · intro x hx; exact (mem_filter.mp hx).2.1
      · intro x hx; exact (mem_filter.mp hx).2.2
    have e1 := (Finset.card_filter_add_card_filter_not (s := Y) (p := fun x => s x = x))
    have e2 := (Finset.card_filter_add_card_filter_not
      (s := Y.filter (fun x => ¬ s x = x)) (p := fun x => r (s x) = x))
    have e3 : (Y.filter (fun x => ¬ s x = x)).filter (fun x => r (s x) = x) =
        Y.filter (fun x => r (s x) = x) := by
      rw [filter_filter]
      apply filter_congr
      intro x hx
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨fun h' => fr x hx ?_, h⟩
        rw [h'] at h; exact h
    have e4 : (Y.filter (fun x => ¬ s x = x)).filter (fun x => ¬ r (s x) = x) =
        Y.filter (fun x => ¬ s x = x ∧ ¬ r (s x) = x) := by
      rw [filter_filter]
    rw [e3, e4] at e2
    omega
  have edgeNe : ∀ {V : Type} (G : SimpleGraph V) (d : V → V → Bool) (a b : V),
      IsOrientation G d → G.Adj a b → d a b ≠ d b a := by
    intro V G d a b hd hab h
    cases hx : d a b
    · have hba : d b a = false := by rw [← h, hx]
      have := (hd a b).mpr ⟨hab, hba⟩
      rw [hx] at this
      exact Bool.false_ne_true this
    · have := ((hd a b).mp hx).2
      rw [← h, hx] at this
      exact absurd this (by decide)
  have revAO : ∀ {V : Type} (G : SimpleGraph V) (d : V → V → Bool),
      IsOrientation G d ∧ IsAcyclic d →
      IsOrientation G (fun a b => d b a) ∧ IsAcyclic (fun a b => d b a) := by
    intro V G d ⟨ho, hac⟩
    refine ⟨fun a b => ?_, fun a h => hac a (Relation.transGen_swap.mp h)⟩
    show d b a = true ↔ G.Adj a b ∧ d a b = false
    rw [ho b a, G.adj_comm]
  have transAO : ∀ {V : Type} (G : SimpleGraph V) (σ : V → V) (d : V → V → Bool),
      (∀ a b, G.Adj (σ a) (σ b) ↔ G.Adj a b) → IsOrientation G d ∧ IsAcyclic d →
      IsOrientation G (fun a b => d (σ a) (σ b)) ∧ IsAcyclic (fun a b => d (σ a) (σ b)) := by
    intro V G σ d hG ⟨ho, hac⟩
    refine ⟨fun a b => ?_, fun a h => hac (σ a) (Relation.TransGen.lift σ (fun x y hxy => hxy) _ _ h)⟩
    show d (σ a) (σ b) = true ↔ G.Adj a b ∧ d (σ b) (σ a) = false
    rw [ho, hG]
  -- fold lemma
  have fold : ∀ {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
      (G : SimpleGraph V) (K : SimpleGraph W) (σ : V → V) (ρ : V → W) (ι : W → V),
      (∀ a b, G.Adj (σ a) (σ b) ↔ G.Adj a b) → (∀ x, ρ (σ x) = ρ x) → (∀ w, ρ (ι w) = w) →
      (∀ x, ι (ρ x) = x ∨ ι (ρ x) = σ x) → (∀ w w', K.Adj w w' ↔ G.Adj (ι w) (ι w')) →
      (∀ a b, G.Adj a b → ι (ρ a) = a → ι (ρ b) ≠ b → σ a = a) →
      ((univ.filter (fun d : V → V → Bool => IsOrientation G d ∧ IsAcyclic d)).filter
        (fun d => (fun a b => d (σ a) (σ b)) = d)).card = acyclicOrientationCount K := by
    intro V W _ _ _ _ G K σ ρ ι hG hρσ hρι hιρ hK hmix
    have hom : ∀ a b, G.Adj a b → K.Adj (ρ a) (ρ b) := by
      intro a b hab
      rw [hK]
      by_cases ha : ι (ρ a) = a <;> by_cases hb : ι (ρ b) = b
      · rw [ha, hb]; exact hab
      · have hσa := hmix a b hab ha hb
        rw [ha, (hιρ b).resolve_left hb]
        have := (hG a b).mpr hab
        rwa [hσa] at this
      · have hσb := hmix b a hab.symm hb ha
        rw [(hιρ a).resolve_left ha, hb]
        have := (hG a b).mpr hab
        rwa [hσb] at this
      · rw [(hιρ a).resolve_left ha, (hιρ b).resolve_left hb]
        exact (hG a b).mpr hab
    let E : (V → V → Bool) → (W → W → Bool) := fun d w w' => d (ι w) (ι w')
    let D : (W → W → Bool) → (V → V → Bool) := fun e a b => decide (G.Adj a b) && e (ρ a) (ρ b)
    have hE : ∀ d, IsOrientation G d ∧ IsAcyclic d → IsOrientation K (E d) ∧ IsAcyclic (E d) := by
      intro d ⟨ho, hac⟩
      refine ⟨fun w w' => ?_,
        fun w h => hac (ι w) (Relation.TransGen.lift ι (fun x y hxy => hxy) _ _ h)⟩
      show d (ι w) (ι w') = true ↔ K.Adj w w' ∧ d (ι w') (ι w) = false
      rw [ho, hK]
    have hD : ∀ e, IsOrientation K e ∧ IsAcyclic e →
        (IsOrientation G (D e) ∧ IsAcyclic (D e)) ∧ (fun a b => D e (σ a) (σ b)) = D e := by
      intro e ⟨ho, hac⟩
      refine ⟨⟨fun a b => ?_, fun a h => hac (ρ a) ?_⟩, ?_⟩
      · show (decide (G.Adj a b) && e (ρ a) (ρ b)) = true ↔
          G.Adj a b ∧ (decide (G.Adj b a) && e (ρ b) (ρ a)) = false
        by_cases hab : G.Adj a b
        · have hba : G.Adj b a := hab.symm
          simp only [hab, hba, decide_true, Bool.true_and, true_and]
          constructor
          · intro h; exact ((ho _ _).mp h).2
          · intro h; exact (ho _ _).mpr ⟨hom a b hab, h⟩
        · simp [hab]
      · refine Relation.TransGen.lift ρ (fun x y hxy => ?_) _ _ h
        simp only [D, Bool.and_eq_true] at hxy
        exact hxy.2
      · funext a b
        show (decide (G.Adj (σ a) (σ b)) && e (ρ (σ a)) (ρ (σ b))) =
          (decide (G.Adj a b) && e (ρ a) (ρ b))
        rw [hρσ, hρσ]
        by_cases hab : G.Adj a b
        · simp [hab, (hG a b).mpr hab]
        · have : ¬ G.Adj (σ a) (σ b) := fun h => hab ((hG a b).mp h)
          simp [hab, this]
    have hDE : ∀ d, IsOrientation G d → (fun a b => d (σ a) (σ b)) = d → D (E d) = d := by
      intro d ho hinv
      have hinv' : ∀ a b, d (σ a) (σ b) = d a b := fun a b => congrFun (congrFun hinv a) b
      funext a b
      show (decide (G.Adj a b) && d (ι (ρ a)) (ι (ρ b))) = d a b
      by_cases hab : G.Adj a b
      · simp only [hab, decide_true, Bool.true_and]
        by_cases ha : ι (ρ a) = a <;> by_cases hb : ι (ρ b) = b
        · rw [ha, hb]
        · rw [ha, (hιρ b).resolve_left hb, ← hinv' a b, hmix a b hab ha hb]
        · rw [(hιρ a).resolve_left ha, hb, ← hinv' a b, hmix b a hab.symm hb ha]
        · rw [(hιρ a).resolve_left ha, (hιρ b).resolve_left hb, hinv']
      · have hf : d a b = false := by
          cases h : d a b
          · rfl
          · exact absurd ((ho a b).mp h).1 hab
        simp [hab, hf]
    have hED : ∀ e, IsOrientation K e → E (D e) = e := by
      intro e ho
      funext w w'
      show (decide (G.Adj (ι w) (ι w')) && e (ρ (ι w)) (ρ (ι w'))) = e w w'
      rw [hρι, hρι]
      cases h : e w w'
      · simp
      · have := ((ho w w').mp h).1
        rw [hK] at this
        simp [this]
    rw [filter_filter, ← Fintype.card_subtype, acyclicOrientationCount, Nat.card_eq_fintype_card]
    exact Fintype.card_congr
      { toFun := fun d => ⟨E d.1, hE d.1 d.2.1⟩
        invFun := fun e => ⟨D e.1, hD e.1 e.2⟩
        left_inv := fun d => Subtype.ext (hDE d.1 d.2.1.1 d.2.2)
        right_inv := fun e => Subtype.ext (hED e.1 e.2.1) }
  have cardAO : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      acyclicOrientationCount G =
        (univ.filter (fun d : V → V → Bool => IsOrientation G d ∧ IsAcyclic d)).card := by
    intro V _ _ G
    rw [acyclicOrientationCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have gridAdj : ∀ {m n : ℕ} (x y : Fin m × Fin n),
      (SimpleGraph.pathGraph m □ SimpleGraph.pathGraph n).Adj x y ↔
        ((x.1.val + 1 = y.1.val ∨ y.1.val + 1 = x.1.val) ∧ x.2.val = y.2.val) ∨
        ((x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val) ∧ x.1.val = y.1.val) := by
    intro m n x y
    simp only [SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj, Fin.ext_iff]
  -- odd grids fold onto their first half
  have oddFold : ∀ a n : ℕ, 2 ≤ n →
      acyclicOrientationCount (SimpleGraph.pathGraph (2 * a + 1) □ SimpleGraph.pathGraph n) % 4 =
        acyclicOrientationCount (SimpleGraph.pathGraph (a + 1) □ SimpleGraph.pathGraph n) % 4 := by
    intro a n hn
    let σ : Fin (2 * a + 1) × Fin n → Fin (2 * a + 1) × Fin n := fun x => (Fin.rev x.1, x.2)
    let ρ : Fin (2 * a + 1) × Fin n → Fin (a + 1) × Fin n := fun x =>
      (⟨min x.1.val (2 * a - x.1.val), by have := x.1.isLt; omega⟩, x.2)
    let ι : Fin (a + 1) × Fin n → Fin (2 * a + 1) × Fin n := fun w =>
      (⟨w.1.val, by have := w.1.isLt; omega⟩, w.2)
    have hGσ : ∀ x y, (SimpleGraph.pathGraph (2 * a + 1) □ SimpleGraph.pathGraph n).Adj (σ x) (σ y) ↔
        (SimpleGraph.pathGraph (2 * a + 1) □ SimpleGraph.pathGraph n).Adj x y := by
      intro x y
      rw [gridAdj, gridAdj]
      simp only [σ, Fin.val_rev]
      omega
    have hfold := fold (SimpleGraph.pathGraph (2 * a + 1) □ SimpleGraph.pathGraph n)
      (SimpleGraph.pathGraph (a + 1) □ SimpleGraph.pathGraph n) σ ρ ι hGσ
      (fun x => Prod.ext (Fin.ext (by simp only [ρ, σ, Fin.val_rev]; omega)) rfl)
      (fun w => Prod.ext (Fin.ext (by simp only [ρ, ι]; have := w.1.isLt; omega)) rfl)
      (fun x => by
        by_cases hx : x.1.val ≤ a
        · left; exact Prod.ext (Fin.ext (by simp only [ρ, ι]; omega)) rfl
        · right; exact Prod.ext (Fin.ext (by simp only [ρ, ι, σ, Fin.val_rev]; omega)) rfl)
      (fun w w' => by rw [gridAdj, gridAdj])
      (fun x y hxy hx hy => by
        rw [gridAdj] at hxy
        simp only [ne_eq, Prod.ext_iff, Fin.ext_iff, ρ, ι, σ, Fin.val_rev, and_true] at hx hy ⊢
        omega)
    have p0 : (⟨a, by omega⟩ : Fin (2 * a + 1)) = Fin.rev ⟨a, by omega⟩ := by
      ext; simp only [Fin.val_rev]; omega
    have horb := orbit
      (univ.filter (fun d => IsOrientation (SimpleGraph.pathGraph (2 * a + 1) □
        SimpleGraph.pathGraph n) d ∧ IsAcyclic d))
      (fun d x y => d y x) (fun d x y => d (σ x) (σ y))
      (fun d => rfl)
      (fun d => by funext x y; simp only [σ, Fin.rev_rev])
      (fun d => rfl)
      (fun d hd => by
        rw [mem_filter] at hd ⊢; exact ⟨mem_univ _, revAO _ d hd.2⟩)
      (fun d hd => by
        rw [mem_filter] at hd ⊢; exact ⟨mem_univ _, transAO _ σ d hGσ hd.2⟩)
      (fun d hd h => by
        rw [mem_filter] at hd
        refine edgeNe _ d (⟨0, by omega⟩, ⟨0, by omega⟩) (⟨0, by omega⟩, ⟨1, by omega⟩) hd.2.1
          (by rw [gridAdj]; simp) ?_
        exact (congrFun (congrFun h _) _).symm)
    have hanti : (univ.filter (fun d => IsOrientation (SimpleGraph.pathGraph (2 * a + 1) □
        SimpleGraph.pathGraph n) d ∧ IsAcyclic d)).filter
        (fun d => (fun x y => (fun x y => d (σ x) (σ y)) y x) = d) = ∅ := by
      rw [filter_eq_empty_iff]
      intro d hd h
      rw [mem_filter] at hd
      have hp : σ (⟨a, by omega⟩, ⟨0, by omega⟩) = (⟨a, by omega⟩, ⟨0, by omega⟩) :=
        Prod.ext p0.symm rfl
      have hq : σ (⟨a, by omega⟩, ⟨1, by omega⟩) = (⟨a, by omega⟩, ⟨1, by omega⟩) :=
        Prod.ext p0.symm rfl
      refine edgeNe _ d (⟨a, by omega⟩, ⟨0, by omega⟩) (⟨a, by omega⟩, ⟨1, by omega⟩) hd.2.1
        (by rw [gridAdj]; simp) ?_
      have := congrFun (congrFun h (⟨a, by omega⟩, ⟨0, by omega⟩)) (⟨a, by omega⟩, ⟨1, by omega⟩)
      simp only [hp, hq] at this
      exact this.symm
    rw [cardAO, horb, hanti, card_empty, add_zero, hfold]
  have kleinCard : ∀ {α : Type} [Fintype α] [DecidableEq α] (P : α → Prop) (r s : α → α),
      (∀ x, r (r x) = x) → (∀ x, s (s x) = x) → (∀ x, r (s x) = s (r x)) →
      (∀ x, P x → P (r x)) → (∀ x, P x → P (s x)) →
      (∀ x, P x → r x ≠ x) → (∀ x, P x → s x ≠ x) → (∀ x, P x → r (s x) ≠ x) →
      4 ∣ Nat.card {x // P x} := by
    intro α _ _ P r s hr hs hrs cr cs fr fs frs
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact klein _ r s hr hs hrs
      (fun x hx => mem_filter.mpr ⟨mem_univ _, cr x (mem_filter.mp hx).2⟩)
      (fun x hx => mem_filter.mpr ⟨mem_univ _, cs x (mem_filter.mp hx).2⟩)
      (fun x hx => fr x (mem_filter.mp hx).2) (fun x hx => fs x (mem_filter.mp hx).2)
      (fun x hx => frs x (mem_filter.mp hx).2)
  have orbitCard : ∀ {α : Type} [Fintype α] [DecidableEq α] (P : α → Prop) (r s : α → α),
      (∀ x, r (r x) = x) → (∀ x, s (s x) = x) → (∀ x, r (s x) = s (r x)) →
      (∀ x, P x → P (r x)) → (∀ x, P x → P (s x)) → (∀ x, P x → r x ≠ x) →
      Nat.card {x // P x} % 4 =
        (Nat.card {x // P x ∧ s x = x} + Nat.card {x // P x ∧ r (s x) = x}) % 4 := by
    intro α _ _ P r s hr hs hrs cr cs fr
    have h := orbit (univ.filter P) r s hr hs hrs
      (fun x hx => mem_filter.mpr ⟨mem_univ _, cr x (mem_filter.mp hx).2⟩)
      (fun x hx => mem_filter.mpr ⟨mem_univ _, cs x (mem_filter.mp hx).2⟩)
      (fun x hx => fr x (mem_filter.mp hx).2)
    rw [filter_filter, filter_filter] at h
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
    convert h using 3
  -- orbit lemma on acyclic orientations with an extra property P
  have orbitAO : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      (P : (V → V → Bool) → Prop) (σ : V → V) (p q : V),
      (∀ x, σ (σ x) = x) → (∀ a b, G.Adj (σ a) (σ b) ↔ G.Adj a b) → G.Adj p q →
      (∀ d, P d → P (fun a b => d b a)) → (∀ d, P d → P (fun a b => d (σ a) (σ b))) →
      Nat.card {d : V → V → Bool // (IsOrientation G d ∧ IsAcyclic d) ∧ P d} % 4 =
        (Nat.card {d : V → V → Bool // (IsOrientation G d ∧ IsAcyclic d) ∧
            (P d ∧ ∀ a b, d (σ a) (σ b) = d a b)} +
          Nat.card {d : V → V → Bool // (IsOrientation G d ∧ IsAcyclic d) ∧
            (P d ∧ ∀ a b, d (σ b) (σ a) = d a b)}) % 4 := by
    intro V _ _ G P σ p q hσ hG hpq hPR hPT
    have h := orbitCard (fun d : V → V → Bool => (IsOrientation G d ∧ IsAcyclic d) ∧ P d)
      (fun d a b => d b a) (fun d a b => d (σ a) (σ b)) (fun d => rfl)
      (fun d => by funext a b; simp only [hσ]) (fun d => rfl)
      (fun d hd => ⟨revAO G d hd.1, hPR d hd.2⟩)
      (fun d hd => ⟨transAO G σ d hG hd.1, hPT d hd.2⟩)
      (fun d hd h => edgeNe G d p q hd.1.1 hpq (congrFun (congrFun h p) q).symm)
    have e1 : Nat.card {d : V → V → Bool // ((IsOrientation G d ∧ IsAcyclic d) ∧ P d) ∧
        (fun a b => d (σ a) (σ b)) = d} = Nat.card {d : V → V → Bool //
          (IsOrientation G d ∧ IsAcyclic d) ∧ (P d ∧ ∀ a b, d (σ a) (σ b) = d a b)} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun d => by simp only [funext_iff, and_assoc]))
    have e2 : Nat.card {d : V → V → Bool // ((IsOrientation G d ∧ IsAcyclic d) ∧ P d) ∧
        (fun a b => d (σ b) (σ a)) = d} = Nat.card {d : V → V → Bool //
          (IsOrientation G d ∧ IsAcyclic d) ∧ (P d ∧ ∀ a b, d (σ b) (σ a) = d a b)} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun d => by simp only [funext_iff, and_assoc]))
    rw [e1, e2] at h
    exact h
  -- an involution that swaps the two ends of an edge fixes no orientation
  have invEmpty : ∀ {V : Type} (G : SimpleGraph V) (σ : V → V) (p q : V) (d : V → V → Bool),
      G.Adj p q → σ p = q → σ q = p → IsOrientation G d →
      (∀ a b, d (σ a) (σ b) = d a b) → False := by
    intro V G σ p q d hpq hp hq hd hinv
    have := hinv p q
    rw [hp, hq] at this
    exact edgeNe G d p q hd hpq this.symm
  -- lemma: the first and last arcs of a path
  have lastArc : ∀ {V : Type} (r : V → V → Prop) (x z : V),
      Relation.TransGen r x z → ∃ w, r w z := by
    intro V r x z h
    cases h with
    | single h => exact ⟨x, h⟩
    | tail _ h => exact ⟨_, h⟩
  have firstArc : ∀ {V : Type} (r : V → V → Prop) (x z : V),
      Relation.TransGen r x z → ∃ w, r x w := by
    intro V r x z h
    induction h with
    | single h => exact ⟨_, h⟩
    | tail _ _ ih => exact ih
  -- the 4 × 4 grid
  have four : acyclicOrientationCount (SimpleGraph.pathGraph 4 □ SimpleGraph.pathGraph 4) % 4 = 0 := by
    let sM : Fin 4 × Fin 4 → Fin 4 × Fin 4 := fun x => (x.1, Fin.rev x.2)
    let uM : Fin 4 × Fin 4 → Fin 4 × Fin 4 := fun x => (Fin.rev x.1, x.2)
    let tM : Fin 4 × Fin 4 → Fin 4 × Fin 4 := fun x => (x.2, x.1)
    have hS : ∀ a b, (SimpleGraph.pathGraph 4 □ SimpleGraph.pathGraph 4).Adj (sM a) (sM b) ↔
        (SimpleGraph.pathGraph 4 □ SimpleGraph.pathGraph 4).Adj a b := by
      intro a b; rw [gridAdj, gridAdj]; simp only [sM, Fin.val_rev]; omega
    have hU : ∀ a b, (SimpleGraph.pathGraph 4 □ SimpleGraph.pathGraph 4).Adj (uM a) (uM b) ↔
        (SimpleGraph.pathGraph 4 □ SimpleGraph.pathGraph 4).Adj a b := by
      intro a b; rw [gridAdj, gridAdj]; simp only [uM, Fin.val_rev]; omega
    have hT : ∀ a b, (SimpleGraph.pathGraph 4 □ SimpleGraph.pathGraph 4).Adj (tM a) (tM b) ↔
        (SimpleGraph.pathGraph 4 □ SimpleGraph.pathGraph 4).Adj a b := by
      intro a b; rw [gridAdj, gridAdj]; simp only [tM]; omega
    have adj : ∀ a b : Fin 4 × Fin 4,
        (SimpleGraph.pathGraph 4 □ SimpleGraph.pathGraph 4).Adj a b ↔
          ((a.1.val + 1 = b.1.val ∨ b.1.val + 1 = a.1.val) ∧ a.2.val = b.2.val) ∨
          ((a.2.val + 1 = b.2.val ∨ b.2.val + 1 = a.2.val) ∧ a.1.val = b.1.val) :=
      fun a b => gridAdj a b
    -- steps 1–3: reflections and the transpose
    have s1 := orbitAO (SimpleGraph.pathGraph 4 □ SimpleGraph.pathGraph 4) (fun _ => True) sM
      (0, 1) (0, 2) (fun x => by simp [sM]) hS (by rw [adj]; decide)
      (fun _ _ => trivial) (fun _ _ => trivial)
    have s2 := orbitAO (SimpleGraph.pathGraph 4 □ SimpleGraph.pathGraph 4)
      (fun d => True ∧ ∀ a b, d (sM b) (sM a) = d a b) uM
      (1, 0) (2, 0) (fun x => by simp [uM]) hU (by rw [adj]; decide)
      (fun d h => ⟨trivial, fun a b => h.2 b a⟩) (fun d h => ⟨trivial, fun a b => h.2 (uM a) (uM b)⟩)
    have s3 := orbitAO (SimpleGraph.pathGraph 4 □ SimpleGraph.pathGraph 4)
      (fun d => (True ∧ ∀ a b, d (sM b) (sM a) = d a b) ∧ ∀ a b, d (uM b) (uM a) = d a b) tM
      (0, 0) (0, 1) (fun x => rfl) hT (by rw [adj]; decide)
      (fun d h => ⟨⟨trivial, fun a b => h.1.2 b a⟩, fun a b => h.2 b a⟩)
      (fun d h => ⟨⟨trivial, fun a b => h.2 (tM a) (tM b)⟩, fun a b => h.1.2 (tM a) (tM b)⟩)
    have z1 : Nat.card {d : Fin 4 × Fin 4 → Fin 4 × Fin 4 → Bool //
        (IsOrientation (SimpleGraph.pathGraph 4 □ SimpleGraph.pathGraph 4) d ∧ IsAcyclic d) ∧
          (True ∧ ∀ a b, d (sM a) (sM b) = d a b)} = 0 :=
      Nat.card_eq_zero.mpr (Or.inl ⟨fun x =>
        invEmpty _ sM (0, 1) (0, 2) x.1 (by rw [adj]; decide) rfl rfl x.2.1.1 x.2.2.2⟩)
    have z2 : Nat.card {d : Fin 4 × Fin 4 → Fin 4 × Fin 4 → Bool //
        (IsOrientation (SimpleGraph.pathGraph 4 □ SimpleGraph.pathGraph 4) d ∧ IsAcyclic d) ∧
          ((True ∧ ∀ a b, d (sM b) (sM a) = d a b) ∧ ∀ a b, d (uM a) (uM b) = d a b)} = 0 :=
      Nat.card_eq_zero.mpr (Or.inl ⟨fun x =>
        invEmpty _ uM (1, 0) (2, 0) x.1 (by rw [adj]; decide) rfl rfl x.2.1.1 x.2.2.2⟩)
    -- step 4: anti-invariance under s and t forces a directed cycle around the centre
    have z4 : Nat.card {d : Fin 4 × Fin 4 → Fin 4 × Fin 4 → Bool //
        (IsOrientation (SimpleGraph.pathGraph 4 □ SimpleGraph.pathGraph 4) d ∧ IsAcyclic d) ∧
          (((True ∧ ∀ a b, d (sM b) (sM a) = d a b) ∧ ∀ a b, d (uM b) (uM a) = d a b) ∧
            ∀ a b, d (tM b) (tM a) = d a b)} = 0 := by
      refine Nat.card_eq_zero.mpr (Or.inl ⟨fun x => ?_⟩)
      obtain ⟨d, ⟨ho, hac⟩, ⟨⟨_, hAs⟩, _⟩, hAt⟩ := x
      have hφ : ∀ a b, d (sM (tM a)) (sM (tM b)) = d a b :=
        fun a b => (hAs (tM b) (tM a)).trans (hAt a b)
      have e12 : d (1, 2) (2, 2) = d (1, 1) (1, 2) := hφ (1, 1) (1, 2)
      have e23 : d (2, 2) (2, 1) = d (1, 2) (2, 2) := hφ (1, 2) (2, 2)
      have e34 : d (2, 1) (1, 1) = d (2, 2) (2, 1) := hφ (2, 2) (2, 1)
      have e21 : d (2, 2) (1, 2) = d (1, 2) (1, 1) := hφ (1, 2) (1, 1)
      have e32 : d (2, 1) (2, 2) = d (2, 2) (1, 2) := hφ (2, 2) (1, 2)
      have e43 : d (1, 1) (2, 1) = d (2, 1) (2, 2) := hφ (2, 1) (2, 2)
      cases h12 : d (1, 1) (1, 2)
      · have h21 : d (1, 2) (1, 1) = true := (ho _ _).mpr ⟨by rw [adj]; decide, h12⟩
        have h32 : d (2, 2) (1, 2) = true := e21.trans h21
        have h43 : d (2, 1) (2, 2) = true := e32.trans h32
        have h14 : d (1, 1) (2, 1) = true := e43.trans h43
        exact hac (1, 1) (.tail (.tail (.tail (.single h14) h43) h32) h21)
      · have h23 : d (1, 2) (2, 2) = true := e12.trans h12
        have h34 : d (2, 2) (2, 1) = true := e23.trans h23
        have h41 : d (2, 1) (1, 1) = true := e34.trans h34
        exact hac (1, 1) (.tail (.tail (.tail (.single h12) h23) h34) h41)
    -- step 5: in the remaining set every corner is a source or a sink; reversing the corner
    -- edges and reversing all edges generate a free Klein four-group
    let C : Fin 4 × Fin 4 → Bool := fun x => (x.1 == 0 || x.1 == 3) && (x.2 == 0 || x.2 == 3)
    let F : (Fin 4 × Fin 4 → Fin 4 × Fin 4 → Bool) → Fin 4 × Fin 4 → Fin 4 × Fin 4 → Bool :=
      fun d a b => if (C a || C b) = true then d b a else d a b
    have hCs : ∀ x, C (sM x) = C x := by decide
    have hCu : ∀ x, C (uM x) = C x := by decide
    have hCt : ∀ x, C (tM x) = C x := by decide
    have hCsymm : ∀ a b, (C a || C b) = (C b || C a) := fun a b => Bool.or_comm _ _
    have hFF : ∀ d, F (F d) = d := by
      intro d; funext a b
      by_cases h : (C a || C b) = true
      · have h' : (C b || C a) = true := by rw [hCsymm]; exact h
        simp only [F, h, h', if_true]
      · have h' : ¬ (C b || C a) = true := by rw [hCsymm]; exact h
        simp only [F, h, h', Bool.false_eq_true, if_false]
    have hRF : ∀ d, (fun a b => F d b a) = F (fun a b => d b a) := by
      intro d; funext a b
      by_cases h : (C a || C b) = true
      · have h' : (C b || C a) = true := by rw [hCsymm]; exact h
        simp only [F, h, h', if_true]
      · have h' : ¬ (C b || C a) = true := by rw [hCsymm]; exact h
        simp only [F, h, h', Bool.false_eq_true, if_false]
    -- a source or sink at a corner moves along the reflections
    have ssMove : ∀ (σ : Fin 4 × Fin 4 → Fin 4 × Fin 4) (d : Fin 4 × Fin 4 → Fin 4 × Fin 4 → Bool)
        (c : Fin 4 × Fin 4), (∀ x, σ (σ x) = x) → (∀ a b, d (σ b) (σ a) = d a b) →
        (∀ x y, d x c = true → d c y = true → False) →
        ∀ x y, d x (σ c) = true → d (σ c) y = true → False := by
      intro σ d c hσ hA hc x y h1 h2
      apply hc (σ y) (σ x)
      · have := hA (σ c) y; rw [hσ] at this; rw [this]; exact h2
      · have := hA x (σ c); rw [hσ] at this; rw [this]; exact h1
    have nbr : ∀ x y : Fin 4 × Fin 4,
        (SimpleGraph.pathGraph 4 □ SimpleGraph.pathGraph 4).Adj x (0, 0) →
        (SimpleGraph.pathGraph 4 □ SimpleGraph.pathGraph 4).Adj (0, 0) y → x = y ∨ x = tM y := by
      intro x y hx hy
      rw [adj] at hx hy
      simp only [Prod.ext_iff, Fin.ext_iff, tM, Fin.val_zero] at hx hy ⊢
      omega
    have corners : ∀ c, C c = true → c = (0, 0) ∨ c = sM (0, 0) ∨ c = uM (0, 0) ∨
        c = uM (sM (0, 0)) := by
      set_option maxRecDepth 4000 in decide
    have hss : ∀ d : Fin 4 × Fin 4 → Fin 4 × Fin 4 → Bool,
        IsOrientation (SimpleGraph.pathGraph 4 □ SimpleGraph.pathGraph 4) d →
        (∀ a b, d (sM b) (sM a) = d a b) → (∀ a b, d (uM b) (uM a) = d a b) →
        (∀ a b, d (tM a) (tM b) = d a b) →
        ∀ c, C c = true → ∀ x y, d x c = true → d c y = true → False := by
      intro d ho hAs hAu hIt
      have h0 : ∀ x y, d x (0, 0) = true → d (0, 0) y = true → False := by
        intro x y h1 h2
        have ax := ((ho x (0, 0)).mp h1).1
        have ay := ((ho (0, 0) y).mp h2).1
        have h2' : d (0, 0) (tM y) = true := by
          have := hIt (0, 0) y; exact this.trans h2
        have hx : d (0, 0) x = true := by
          rcases nbr x y ax ay with rfl | rfl
          · exact h2
          · exact h2'
        have := ((ho (0, 0) x).mp hx).2
        rw [h1] at this; exact absurd this (by decide)
      have hsM := ssMove sM d (0, 0) (fun x => by simp [sM]) hAs h0
      have huM := ssMove uM d (0, 0) (fun x => by simp [uM]) hAu h0
      have hsuM := ssMove uM d (sM (0, 0)) (fun x => by simp [uM]) hAu hsM
      intro c hc
      rcases corners c hc with rfl | rfl | rfl | rfl
      · exact h0
      · exact hsM
      · exact huM
      · exact hsuM
    have key : 4 ∣ Nat.card {d : Fin 4 × Fin 4 → Fin 4 × Fin 4 → Bool //
        (IsOrientation (SimpleGraph.pathGraph 4 □ SimpleGraph.pathGraph 4) d ∧ IsAcyclic d) ∧
          (((True ∧ ∀ a b, d (sM b) (sM a) = d a b) ∧ ∀ a b, d (uM b) (uM a) = d a b) ∧
            ∀ a b, d (tM a) (tM b) = d a b)} := by
      refine kleinCard _ (fun d a b => d b a) F (fun d => rfl) hFF hRF ?_ ?_ ?_ ?_ ?_
      · intro d hd
        obtain ⟨hAO, ⟨⟨_, hAs⟩, hAu⟩, hIt⟩ := hd
        exact ⟨revAO _ d hAO, ⟨⟨trivial, fun a b => hAs b a⟩, fun a b => hAu b a⟩,
          fun a b => hIt b a⟩
      · intro d hd
        obtain ⟨⟨ho, hac⟩, ⟨⟨_, hAs⟩, hAu⟩, hIt⟩ := hd
        have ssd := hss d ho hAs hAu hIt
        refine ⟨⟨fun a b => ?_, ?_⟩, ⟨⟨trivial, fun a b => ?_⟩, fun a b => ?_⟩, fun a b => ?_⟩
        · by_cases h : (C a || C b) = true
          · have h' : (C b || C a) = true := by rw [hCsymm]; exact h
            simp only [F, h, h', if_true]
            rw [ho b a, SimpleGraph.adj_comm]
          · have h' : ¬ (C b || C a) = true := by rw [hCsymm]; exact h
            simp only [F, h, h', Bool.false_eq_true, if_false]
            exact ho a b
        · -- a directed cycle of F d avoids the corners, hence is a cycle of d
          have ssF : ∀ c, C c = true → ∀ x y, F d x c = true → F d c y = true → False := by
            intro c hc x y h1 h2
            have h1' : d c x = true := by
              have : (C x || C c) = true := by rw [hc, Bool.or_true]
              simp only [F, this, if_true] at h1; exact h1
            have h2' : d y c = true := by
              have : (C c || C y) = true := by rw [hc, Bool.true_or]
              simp only [F, this, if_true] at h2; exact h2
            exact ssd c hc y x h2' h1'
          have avoid : ∀ x y, Relation.TransGen (fun u v => F d u v = true) x y →
              C x = false → C y = false → Relation.TransGen (fun u v => d u v = true) x y := by
            intro x y h
            induction h with
            | single hxy =>
              rename_i w
              intro hx hy
              have : ¬ (C x || C w) = true := by simp [hx, hy]
              simp only [F, this] at hxy
              exact .single hxy
            | tail hxz hzy ih =>
              intro hx hy
              rename_i z w
              cases hz : C z
              · have : ¬ (C z || C w) = true := by simp [hz, hy]
                simp only [F, this] at hzy
                exact .tail (ih hx hz) hzy
              · obtain ⟨v, hv⟩ := lastArc _ _ _ hxz
                exact absurd (ssF z hz v w hv hzy) id
          intro a ha
          cases hca : C a
          · exact hac a (avoid a a ha hca hca)
          · obtain ⟨v, hv⟩ := lastArc _ _ _ ha
            obtain ⟨w, hw⟩ := firstArc _ _ _ ha
            exact ssF a hca v w hv hw
        · show F d (sM b) (sM a) = F d a b
          simp only [F, hCs]
          rw [hAs a b, hAs b a, hCsymm]
        · show F d (uM b) (uM a) = F d a b
          simp only [F, hCu]
          rw [hAu a b, hAu b a, hCsymm]
        · show F d (tM a) (tM b) = F d a b
          simp only [F, hCt]
          rw [hIt a b, hIt b a]
      · intro d hd h
        exact edgeNe _ d (0, 0) (0, 1) hd.1.1 (by rw [adj]; decide)
          (congrFun (congrFun h (0, 0)) (0, 1)).symm
      · intro d hd h
        have := congrFun (congrFun h (0, 0)) (0, 1)
        have hc : (C (0, 0) || C (0, 1)) = true := by decide
        simp only [F, hc, if_true] at this
        exact edgeNe _ d (0, 0) (0, 1) hd.1.1 (by rw [adj]; decide) this.symm
      · intro d hd h
        have := congrFun (congrFun h (1, 1)) (1, 2)
        have hc : ¬ (C (1, 2) || C (1, 1)) = true := by decide
        simp only [F, hc, Bool.false_eq_true, if_false] at this
        exact edgeNe _ d (1, 1) (1, 2) hd.1.1 (by rw [adj]; decide) this.symm
    have e0 : Nat.card {d : Fin 4 × Fin 4 → Fin 4 × Fin 4 → Bool //
        (IsOrientation (SimpleGraph.pathGraph 4 □ SimpleGraph.pathGraph 4) d ∧ IsAcyclic d) ∧
          True} = Nat.card {d : Fin 4 × Fin 4 → Fin 4 × Fin 4 → Bool //
        IsOrientation (SimpleGraph.pathGraph 4 □ SimpleGraph.pathGraph 4) d ∧ IsAcyclic d} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun d => Iff.of_eq (and_true _)))
    rw [acyclicOrientationCount, ← e0, s1, z1, zero_add, s2, z2, zero_add, s3, z4, add_zero]
    exact Nat.mod_eq_zero_of_dvd key
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
  have swap : ∀ m n : ℕ,
      acyclicOrientationCount (SimpleGraph.pathGraph m □ SimpleGraph.pathGraph n) =
        acyclicOrientationCount (SimpleGraph.pathGraph n □ SimpleGraph.pathGraph m) := by
    intro m n
    rw [← iso (Equiv.prodComm (Fin m) (Fin n)) (SimpleGraph.pathGraph n □ SimpleGraph.pathGraph m)]
    congr 1
    ext x y
    rw [SimpleGraph.comap_adj, gridAdj, gridAdj]
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    omega
  have h77 := hclaim 7 7 (by omega) (by omega) ⟨3, rfl⟩ ⟨3, rfl⟩
  have f1 : acyclicOrientationCount (SimpleGraph.pathGraph 7 □ SimpleGraph.pathGraph 7) % 4 =
      acyclicOrientationCount (SimpleGraph.pathGraph 4 □ SimpleGraph.pathGraph 7) % 4 :=
    oddFold 3 7 (by omega)
  have f2 : acyclicOrientationCount (SimpleGraph.pathGraph 7 □ SimpleGraph.pathGraph 4) % 4 =
      acyclicOrientationCount (SimpleGraph.pathGraph 4 □ SimpleGraph.pathGraph 4) % 4 :=
    oddFold 3 4 (by omega)
  have f3 := swap 4 7
  omega

end D5.S3.Combinatorics.Graph.GridAcyclicOrientations
