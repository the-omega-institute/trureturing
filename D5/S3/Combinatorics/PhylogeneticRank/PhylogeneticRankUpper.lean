/- GID: D5/S3/Combinatorics/PhylogeneticRank/PhylogeneticRankUpper
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PhylogeneticRank/PhylogeneticRankUpper
   mirror-E: none(waiver:distance-coordinate-construction)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Hasse]
   utility: none
   digest: Unit path trees realize integer intervals for distance-coordinate embeddings. -/

import D5.S3.Combinatorics.PhylogeneticRank.PhylogeneticRankTree
import Mathlib.Combinatorics.SimpleGraph.Hasse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PhylogeneticRank

open SimpleGraph PhylogeneticRankDefs

/-- The consecutive-edge bijection and monotone walks construct the unit interval tree. -/
theorem exists_unit_path_tree (n : ℕ) :
    ∃ T : MetricTree, T.m = n + 1 ∧
      ∀ x y : Fin T.m, T.dist x y = |(x.val : ℝ) - (y.val : ℝ)| := by
  classical
  let P := pathGraph (n + 1)
  let f : Fin n → P.edgeSet := fun i =>
    ⟨s(i.castSucc, i.succ), (pathGraph_adj).mpr (Or.inl (by simp))⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j he
      have he' := Sym2.eq_iff.mp (congrArg Subtype.val he)
      rcases he' with ⟨h, _⟩ | ⟨h₁, h₂⟩
      · apply Fin.ext
        exact congrArg (fun z : Fin (n + 1) => z.val) h
      · have h₁' := congrArg Fin.val h₁
        have h₂' := congrArg Fin.val h₂
        simp only [Fin.val_castSucc, Fin.val_succ] at h₁' h₂'
        omega
    · rintro ⟨e, he⟩
      induction e using Sym2.inductionOn with
      | hf x y =>
        have hxy : P.Adj x y := he
        have hx := x.isLt
        have hy := y.isLt
        rcases pathGraph_adj.mp hxy with h | h
        · refine ⟨⟨x.val, by omega⟩, ?_⟩
          apply Subtype.ext
          change s(_, _) = s(x, y)
          apply Sym2.eq_iff.mpr
          left
          constructor
          · apply Fin.ext; rfl
          · apply Fin.ext; exact h
        · refine ⟨⟨y.val, by omega⟩, ?_⟩
          apply Subtype.ext
          change s(_, _) = s(x, y)
          apply Sym2.eq_iff.mpr
          right
          constructor
          · apply Fin.ext; rfl
          · apply Fin.ext; exact h
  have hcard : Nat.card P.edgeSet = n := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_of_bijective hf, Fintype.card_fin]
  have ht : P.IsTree := isTree_iff_connected_and_card.mpr
    ⟨pathGraph_connected n, by rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fin]⟩
  let T : MetricTree :=
    { m := n + 1
      graph := P
      isTree := ht
      len := fun _ _ => 1
      len_symm := fun _ _ => rfl
      len_pos := fun _ _ _ => zero_lt_one }
  refine ⟨T, rfl, ?_⟩
  have hlen : ∀ {x y : Fin (n + 1)} (w : P.Walk x y),
      T.walkLength w = (w.length : ℝ) := by
    intro x y w
    induction w with
    | nil => simp [MetricTree.walkLength]
    | cons h w ih => simp [MetricTree.walkLength, T, ih, add_comm]
  have hlower : ∀ {x y : Fin (n + 1)} (w : P.Walk x y),
      |(x.val : ℝ) - (y.val : ℝ)| ≤ T.walkLength w := by
    intro x y w
    induction w with
    | nil => simp [MetricTree.walkLength]
    | @cons x z y h w ih =>
      have hz : |(x.val : ℝ) - (z.val : ℝ)| = 1 := by
        rcases pathGraph_adj.mp h with h | h
        · have hh : (x.val : ℝ) + 1 = z.val := by exact_mod_cast h
          rw [show (x.val : ℝ) - z.val = -1 by linarith]
          norm_num
        · have hh : (z.val : ℝ) + 1 = x.val := by exact_mod_cast h
          rw [show (x.val : ℝ) - z.val = 1 by linarith]
          norm_num
      calc
        |(x.val : ℝ) - (y.val : ℝ)| ≤ |(x.val : ℝ) - (z.val : ℝ)| + |(z.val : ℝ) - (y.val : ℝ)| :=
          abs_sub_le _ _ _
        _ ≤ T.walkLength (.cons h w) := by
          simpa [hz, MetricTree.walkLength, T] using add_le_add_right ih 1
  have hwalk : ∀ d : ℕ, ∀ x y : Fin (n + 1), x.val ≤ y.val → y.val - x.val = d →
      ∃ w : P.Walk x y, w.length = d := by
    intro d
    induction d with
    | zero =>
      intro x y hxy hd
      have he : x = y := Fin.ext (by omega)
      subst y
      exact ⟨.nil, rfl⟩
    | succ d ih =>
      intro x y hxy hd
      let z : Fin (n + 1) := ⟨x.val + 1, by omega⟩
      obtain ⟨w, hw⟩ := ih z y (by dsimp [z]; omega) (by dsimp [z]; omega)
      have hxz : P.Adj x z := pathGraph_adj.mpr (Or.inl rfl)
      exact ⟨.cons hxz w, by simp [hw]⟩
  intro x y
  obtain ⟨p, hp, _⟩ := ht.existsUnique_path x y
  rw [tree_dist_eq_path_length T p hp]
  apply le_antisymm
  · have hex : ∃ w : P.Walk x y, T.walkLength w = |(x.val : ℝ) - (y.val : ℝ)| := by
      by_cases hxy : x.val ≤ y.val
      · obtain ⟨w, hw⟩ := hwalk (y.val - x.val) x y hxy rfl
        refine ⟨w, ?_⟩
        rw [hlen, hw, Nat.cast_sub hxy, abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hxy))]
        ring
      · have hyx : y.val ≤ x.val := by omega
        obtain ⟨w, hw⟩ := hwalk (x.val - y.val) y x hyx rfl
        refine ⟨w.reverse, ?_⟩
        rw [hlen, Walk.length_reverse, hw, Nat.cast_sub hyx,
          abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hyx))]
    obtain ⟨w, hw⟩ := hex
    have hb : BddBelow (Set.range (fun q : P.Walk x y => T.walkLength q)) :=
      ⟨0, by rintro _ ⟨q, rfl⟩; exact (hlower q).trans' (abs_nonneg _)⟩
    rw [← tree_dist_eq_path_length T p hp]
    exact (csInf_le hb ⟨w, rfl⟩).trans_eq hw
  · exact hlower p

/-- Distance coordinates, omitting one endpoint index, give an isometric tree embedding. -/
theorem connected_has_tree_embedding {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n))
    (hG : G.Connected) : HasTreeEmbedding G (n - 1) := by
  classical
  obtain ⟨T, hm, hd⟩ := exists_unit_path_tree (n - 1)
  have hmn : T.m = n := by omega
  have : Nonempty (Fin (n - 1)) := ⟨⟨0, by omega⟩⟩
  let c : Fin (n - 1) → Fin n := Fin.castLE (Nat.sub_le n 1)
  have hbound : ∀ a u : Fin n, G.dist a u < T.m := by
    intro a u
    obtain ⟨w, hw, hl⟩ := hG.exists_path_of_dist a u
    have hlt := hw.length_lt
    rw [Fintype.card_fin, hl] at hlt
    omega
  let f : Fin (n - 1) → Fin n → Fin T.m := fun i u =>
    ⟨G.dist (c i) u, hbound (c i) u⟩
  refine ⟨fun _ => T, f, ?_⟩
  intro a b
  have he : ∀ i, T.dist (f i a) (f i b) =
      |(G.dist (c i) a : ℝ) - (G.dist (c i) b : ℝ)| := fun i => hd _ _
  have hdom : ∀ i, T.dist (f i a) (f i b) ≤ (G.dist a b : ℝ) := by
    intro i
    rw [he]
    apply abs_le.mpr
    have ha := hG.dist_triangle (u := c i) (v := a) (w := b)
    have hb := hG.dist_triangle (u := c i) (v := b) (w := a)
    rw [G.dist_comm (u := b) (v := a)] at hb
    have ha' : (G.dist (c i) b : ℝ) ≤ G.dist (c i) a + G.dist a b :=
      by exact_mod_cast ha
    have hb' : (G.dist (c i) a : ℝ) ≤ G.dist (c i) b + G.dist a b :=
      by exact_mod_cast hb
    constructor <;> linarith
  have hsup : BddAbove (Set.range (fun i => T.dist (f i a) (f i b))) :=
    ⟨G.dist a b, by rintro _ ⟨i, rfl⟩; exact hdom i⟩
  apply le_antisymm
  · by_cases hab : a = b
    · subst b
      have hi : T.dist (f ⟨0, by omega⟩ a) (f ⟨0, by omega⟩ a) = 0 := by
        rw [he]
        simp
      rw [G.dist_self, Nat.cast_zero]
      exact le_ciSup_of_le hsup ⟨0, by omega⟩ hi.ge
    · have hindex : a.val < n - 1 ∨ b.val < n - 1 := by
        have ha := a.isLt
        have hb := b.isLt
        have hne : a.val ≠ b.val := fun he => hab (Fin.ext he)
        omega
      rcases hindex with ha | hb
      · let i : Fin (n - 1) := ⟨a.val, ha⟩
        have hci : c i = a := Fin.ext rfl
        have hi : T.dist (f i a) (f i b) = (G.dist a b : ℝ) := by
          rw [he, hci, G.dist_self, Nat.cast_zero, zero_sub, abs_neg,
            abs_of_nonneg (Nat.cast_nonneg _)]
        exact le_ciSup_of_le hsup i hi.ge
      · let i : Fin (n - 1) := ⟨b.val, hb⟩
        have hci : c i = b := Fin.ext rfl
        have hi : T.dist (f i a) (f i b) = (G.dist a b : ℝ) := by
          rw [he, hci, G.dist_self, Nat.cast_zero, sub_zero,
            abs_of_nonneg (Nat.cast_nonneg _), G.dist_comm (u := b) (v := a)]
        exact le_ciSup_of_le hsup i hi.ge
  · exact ciSup_le hdom

#print axioms exists_unit_path_tree
#print axioms connected_has_tree_embedding

end D5.S3.Combinatorics.PhylogeneticRank
