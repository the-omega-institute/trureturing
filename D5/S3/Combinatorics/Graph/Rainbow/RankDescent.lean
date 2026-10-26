/- GID: D5/S3/Combinatorics/Graph/Rainbow/RankDescent
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Rainbow/RankDescent
   mirror-E: none(waiver:general-deterministic-theorems)
   anchors: [mathlib/module/Mathlib.Combinatorics.Quiver.Path.Vertices]
   utility: none
   digest: Forbidden-set rank induction on actual robust layers and the exceptional final edge. -/

import D5.S3.Combinatorics.Graph.Rainbow.RobustLayers
import D5.S3.Combinatorics.Graph.Rainbow.TwoEdgeChoices
import Mathlib.Combinatorics.Quiver.Path.Vertices
import Mathlib.Combinatorics.Quiver.Path.Weight
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
The deterministic path implication in the colour-aware repair of the connecting
lemma, arXiv:2503.01825v2, Section 4.3. The sampled counts are hypotheses here;
their simultaneous probability estimate and B1/B2 are separate obligations.
The exceptional set is the actual repeated-colour set of `TwoEdgeChoices`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [local instance] Classical.propDecidable

open Finset
open D5.S3.Combinatorics.Graph.Rainbow.RobustLayers

namespace D5.S3.Combinatorics.Graph.Rainbow.RankDescent

variable {V C : Type*} [Fintype V]

/-- The ordinary quiver of proofs of directed adjacency. -/
abbrev graphQuiver (G : Digraph V) : Quiver V := ⟨fun u v => PLift (G.Adj u v)⟩

abbrev DPath (G : Digraph V) (u v : V) := @Quiver.Path V (graphQuiver G) u v

/-- The word consists of the given literal edge colours in their directed order. -/
def colours (G : Digraph V) (c : V → V → C) {u v : V} (P : DPath G u v) : List C :=
  letI : Quiver V := graphQuiver G
  (P.weightOfEPs (fun x y => FreeMonoid.of (c x y))).toList

/-- Only internal vertices are restricted; the two endpoints remain arbitrary. -/
def Allowed (G : Digraph V) (c : V → V → C) (R A : Finset V) (S D : Finset C)
    {u v : V} (P : DPath G u v) : Prop :=
  letI : Quiver V := graphQuiver G
  P.vertices.Nodup ∧ (colours G c P).Nodup ∧
    (∀ x ∈ P.vertices, x ≠ u → x ≠ v → x ∈ R ∧ x ∉ A) ∧
    (∀ d ∈ colours G c P, d ∈ S ∧ d ∉ D)

/-- The actual sampled rainbow two-edge choices. -/
noncomputable def sampledBase (G : Digraph V) (c : V → V → C)
    (R : Finset V) (S : Finset C) (u w : V) : Finset V := by
  classical
  exact (layer G 0 u 0).filter (fun x => G.Adj x w ∧ c u x ≠ c x w ∧
    x ∈ R ∧ c u x ∈ S ∧ c x w ∈ S)

/-- Sampled incoming edges, with their literal colours. -/
noncomputable def sampledPred (G : Digraph V) (c : V → V → C)
    (R : Finset V) (S : Finset C) (T : Finset V) (w : V) : Finset V := by
  classical
  exact (predecessors G T w).filter (fun x => x ∈ R ∧ c x w ∈ S)

private theorem append_allowed (G : Digraph V) (c : V → V → C)
    (R A : Finset V) (S D : Finset C) {u x w : V}
    (P : DPath G u x) (e : G.Adj x w)
    (hP : Allowed G c R (insert w A) S (insert (c x w) D) P)
    (hwu : w ≠ u) (hwx : w ≠ x) (hx : x ∈ R ∧ x ∉ A)
    (hc : c x w ∈ S ∧ c x w ∉ D) :
    letI : Quiver V := graphQuiver G
    Allowed G c R A S D (P.cons (PLift.up e)) := by
  letI : Quiver V := graphQuiver G
  classical
  have hw : w ∉ P.vertices := by
    intro h
    have hh := hP.2.2.1 w h hwu hwx
    exact hh.2 (mem_insert_self _ _)
  have hd : c x w ∉ colours G c P := by
    intro h
    exact (hP.2.2.2 _ h).2 (mem_insert_self _ _)
  have hcol : colours G c (P.cons (PLift.up e)) = colours G c P ++ [c x w] := by
    simp [colours, Quiver.Path.weightOfEPs_cons]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Quiver.Path.vertices_cons, List.nodup_concat]
    exact ⟨hw, hP.1⟩
  · rw [hcol, ← List.concat_eq_append, List.nodup_concat]
    exact ⟨hd, hP.2.1⟩
  · intro y hy hyu hyw
    rcases (Quiver.Path.mem_vertices_cons _ _).mp hy with hy | rfl
    · by_cases hyx : y = x
      · simpa [hyx] using hx
      · have hh := hP.2.2.1 y hy hyu hyx
        exact ⟨hh.1, fun ha => hh.2 (mem_insert_of_mem ha)⟩
    · exact (hyw rfl).elim
  · intro d hd'
    rw [hcol] at hd'
    rcases List.mem_append.mp hd' with hd' | hd'
    · have hh := hP.2.2.2 d hd'
      exact ⟨hh.1, fun h => hh.2 (mem_insert_of_mem h)⟩
    · simp only [List.mem_singleton] at hd'
      simpa [hd'] using hc

private theorem base_path (G : Digraph V) (c : V → V → C)
    (hloop : ∀ x, ¬ G.Adj x x)
    (hout : ∀ u, Set.InjOn (c u) {x | G.Adj u x})
    (hin : ∀ w, Set.InjOn (fun x => c x w) {x | G.Adj x w})
    (R A : Finset V) (S D : Finset C) (u w : V) (huw : u ≠ w)
    (hcount : A.card + 2 * D.card < (sampledBase G c R S u w).card) :
    letI : Quiver V := graphQuiver G
    ∃ P : DPath G u w, Allowed G c R A S D P ∧ P.length ≤ 2 := by
  letI : Quiver V := graphQuiver G
  classical
  let T := sampledBase G c R S u w
  let L := T.filter (fun x => c u x ∈ D)
  let H := T.filter (fun x => c x w ∈ D)
  have hL : L.card ≤ D.card := by
    apply card_le_card_of_injOn (c u)
    · intro x hx
      exact (mem_filter.mp hx).2
    · intro x hx y hy hxy
      have hxt := (mem_filter.mp (mem_filter.mp hx).1).1
      have hyt := (mem_filter.mp (mem_filter.mp hy).1).1
      exact hout u (mem_filter.mp hxt).2 (mem_filter.mp hyt).2 hxy
  have hH : H.card ≤ D.card := by
    apply card_le_card_of_injOn (fun x => c x w)
    · intro x hx
      exact (mem_filter.mp hx).2
    · intro x hx y hy hxy
      exact hin w (mem_filter.mp (mem_filter.mp hx).1).2.1
        (mem_filter.mp (mem_filter.mp hy).1).2.1 hxy
  have hbad : (A ∪ L ∪ H).card < T.card := by
    have h1 := card_union_le A L
    have h2 := card_union_le (A ∪ L) H
    dsimp [T] at *
    omega
  obtain ⟨x, hxt, hx⟩ := exists_mem_notMem_of_card_lt_card hbad
  have hxA : x ∉ A := fun h => hx (mem_union_left _ (mem_union_left _ h))
  have hleft : c u x ∉ D := by
    intro hd
    exact hx (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hxt, hd⟩)))
  have hright : c x w ∉ D := by
    intro hd
    exact hx (mem_union_right _ (mem_filter.mpr ⟨hxt, hd⟩))
  have hdata := (mem_filter.mp hxt).2
  have hux : G.Adj u x := (mem_filter.mp (mem_filter.mp hxt).1).2
  have hxu : x ≠ u := fun h => hloop u (h ▸ hux)
  have hxw : x ≠ w := fun h => hloop w (h ▸ hdata.1)
  let P : DPath G u w := (Quiver.Path.nil.cons (PLift.up hux)).cons (PLift.up hdata.1)
  refine ⟨P, ?_, by simp [P]⟩
  have hv : P.vertices = [u, x, w] := by simp [P]
  have hc : colours G c P = [c u x, c x w] := by
    simp [P, colours, Quiver.Path.weightOfEPs_cons, Quiver.Path.weightOfEPs_nil]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hv, hxu, hxw, huw, Ne.symm hxu]
  · simp [hc, hdata.2.1]
  · intro y hy hyu hyw
    simp only [hv, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · exact (hyu rfl).elim
    · exact ⟨hdata.2.2.1, hxA⟩
    · exact (hyw rfl).elim
  · intro d hd
    simp only [hc, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨hdata.2.2.2.1, hleft⟩
    · exact ⟨hdata.2.2.2.2, hright⟩

private theorem rank_path (G : Digraph V) (c : V → V → C)
    (hloop : ∀ x, ¬ G.Adj x x)
    (hout : ∀ u, Set.InjOn (c u) {x | G.Adj u x})
    (hin : ∀ w, Set.InjOn (fun x => c x w) {x | G.Adj x w})
    (ν : ℝ) (hν : 0 < ν) (R B : Finset V) (S : Finset C)
    (u : V) (m a d : ℕ) (Tb Tr : ℝ)
    (hbase : ∀ w, u ≠ w → w ∉ B →
      w ∈ robust G (ν / 4) (layer G ν u 0) →
      Tb ≤ ((sampledBase G c R S u w).card : ℝ))
    (hrank : ∀ i, i ≤ m → ∀ w,
      w ∈ robust G (ν / 4) (layer G ν u i \ layer G ν u 0) →
      Tr ≤ ((sampledPred G c R S (layer G ν u i \ layer G ν u 0) w).card : ℝ))
    (hb : (a : ℝ) + 2 * d + 3 * m < Tb)
    (hr : (a : ℝ) + d + 2 * m + B.card + 1 < Tr) :
    letI : Quiver V := graphQuiver G
    ∀ i, i ≤ m → ∀ w, u ≠ w → w ∉ B →
      w ∈ robust G (ν / 2) (layer G ν u i) →
      ∀ (A : Finset V) (D : Finset C), A.card + i ≤ a + m → D.card + i ≤ d + m →
      ∃ P : DPath G u w, Allowed G c R A S D P ∧ P.length ≤ i + 2 := by
  letI : Quiver V := graphQuiver G
  classical
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro him w huw hw hrob A D hA hD
    by_cases hzero : w ∈ robust G (ν / 4) (layer G ν u 0)
    · have hc := hbase w huw hw hzero
      have hAR : (A.card : ℝ) + i ≤ a + m := by exact_mod_cast hA
      have hDR : (D.card : ℝ) + i ≤ d + m := by exact_mod_cast hD
      have hcount : A.card + 2 * D.card < (sampledBase G c R S u w).card := by
        have hiR : (0 : ℝ) ≤ i := Nat.cast_nonneg _
        have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg _
        have : (A.card : ℝ) + 2 * D.card < (sampledBase G c R S u w).card := by linarith
        exact_mod_cast this
      obtain ⟨P, hp, hl⟩ := base_path G c hloop hout hin R A S D u w huw hcount
      exact ⟨P, hp, by omega⟩
    · have hbig : w ∈ robust G (ν / 4) (layer G ν u i \ layer G ν u 0) := by
        have hfull := (mem_filter.mp hrob).2
        have hsmall : ((predecessors G (layer G ν u 0) w).card : ℝ) <
            ν / 4 * Fintype.card V := by
          simpa only [robust, mem_filter, mem_univ, true_and, not_le] using hzero
        have hsplit : (predecessors G (layer G ν u i) w \ predecessors G (layer G ν u 0) w)
            = predecessors G (layer G ν u i \ layer G ν u 0) w := by
          ext x
          simp only [predecessors, mem_filter, mem_sdiff]
          tauto
        have hcard := card_le_card_sdiff_add_card
          (s := predecessors G (layer G ν u i) w) (t := predecessors G (layer G ν u 0) w)
        rw [hsplit] at hcard
        have hcardR : ((predecessors G (layer G ν u i) w).card : ℝ) ≤
            (predecessors G (layer G ν u i \ layer G ν u 0) w).card +
              (predecessors G (layer G ν u 0) w).card := by exact_mod_cast hcard
        exact mem_filter.mpr ⟨mem_univ _, by linarith⟩
      let T := sampledPred G c R S (layer G ν u i \ layer G ν u 0) w
      let H := T.filter (fun x => c x w ∈ D)
      have hH : H.card ≤ D.card := by
        apply card_le_card_of_injOn (fun x => c x w)
        · intro x hx
          exact (mem_filter.mp hx).2
        · intro x hx y hy hxy
          exact hin w (mem_filter.mp (mem_filter.mp (mem_filter.mp hx).1).1).2
            (mem_filter.mp (mem_filter.mp (mem_filter.mp hy).1).1).2 hxy
      have hbad : (A ∪ B ∪ {u} ∪ H).card < T.card := by
        have hc := hrank i him w hbig
        have h1 := card_union_le A B
        have h2 := card_union_le (A ∪ B) ({u} : Finset V)
        have h3 := card_union_le (A ∪ B ∪ {u}) H
        have hnat : (A ∪ B ∪ {u} ∪ H).card ≤ a + d + 2 * m + B.card + 1 := by
          simp only [card_singleton] at h2
          omega
        have hR : ((A ∪ B ∪ {u} ∪ H).card : ℝ) ≤
            (a : ℝ) + d + 2 * m + B.card + 1 := by exact_mod_cast hnat
        exact_mod_cast (show ((A ∪ B ∪ {u} ∪ H).card : ℝ) < T.card by linarith)
      obtain ⟨x, hxT, hxbad⟩ := exists_mem_notMem_of_card_lt_card hbad
      have hxA : x ∉ A := fun h => hxbad
        (mem_union_left _ (mem_union_left _ (mem_union_left _ h)))
      have hxB : x ∉ B := fun h => hxbad
        (mem_union_left _ (mem_union_left _ (mem_union_right _ h)))
      have hxu : x ≠ u := by
        intro h
        exact hxbad (mem_union_left _ (mem_union_right _ (mem_singleton.mpr h)))
      have hcd : c x w ∉ D := fun h => hxbad
        (mem_union_right _ (mem_filter.mpr ⟨hxT, h⟩))
      have hxPred := (mem_filter.mp hxT).1
      have hxRes := (mem_filter.mp hxT).2
      have hxlayer := mem_sdiff.mp (mem_filter.mp hxPred).1
      have hxw : G.Adj x w := (mem_filter.mp hxPred).2
      obtain ⟨j, hji, hxj⟩ := earlier_rank G ν u x i hxlayer.1 hxlayer.2
      have hxhalf : x ∈ robust G (ν / 2) (layer G ν u j) := by
        apply mem_filter.mpr
        refine ⟨mem_univ _, ?_⟩
        have hh := (mem_filter.mp hxj).2
        have hnν := mul_nonneg hν.le (Nat.cast_nonneg (Fintype.card V) : (0 : ℝ) ≤ _)
        linarith
      obtain ⟨P, hp, hl⟩ := ih j hji (by omega) x (Ne.symm hxu) hxB hxhalf
        (insert w A) (insert (c x w) D)
        (by have hh := card_insert_le w A; omega)
        (by have hh := card_insert_le (c x w) D; omega)
      refine ⟨P.cons (PLift.up hxw), ?_, ?_⟩
      · exact append_allowed G c R A S D P hxw hp (Ne.symm huw)
          (fun h => hloop w (h.symm ▸ hxw)) ⟨hxRes.1, hxA⟩ ⟨hxRes.2, hcd⟩
      · simp only [Quiver.Path.length_cons]
        omega

/-- Fixed sampled base, rank and incoming-star counts imply one deterministic
connector for every post-selection forbidden pair. The early covering layer is
proved from exterior expansion, and the exceptional target uses the spare edge.
Here `b` is the total deletion budget, equal to `p^3 * ν * n / 100` in the
probabilistic connecting lemma. -/
theorem robust_connector (G : Digraph V) (c : V → V → C)
    (hloop : ∀ x, ¬ G.Adj x x)
    (hout : ∀ u, Set.InjOn (c u) {x | G.Adj u x})
    (hin : ∀ w, Set.InjOn (fun x => c x w) {x | G.Adj x w})
    (ν τ α p b : ℝ) (hν : 0 < ν) (hτ : 0 < τ) (hp : 0 < p) (hpone : p ≤ 1)
    (hparams : ν + τ ≤ α)
    (hscale : 144 * Real.log (Fintype.card V) ≤ p ^ 3 * ν ^ 2 * Fintype.card V)
    (hexp : ExteriorExpander G ν τ)
    (houtdeg : ∀ u, α * Fintype.card V ≤ ((layer G ν u 0).card : ℝ))
    (hindeg : ∀ w, α * Fintype.card V ≤ ((predecessors G univ w).card : ℝ))
    (R : Finset V) (S : Finset C)
    (hbase : ∀ u w, u ≠ w →
      w ∉ TwoEdgeChoices.exceptions G c u (ν * Fintype.card V / 16) →
      w ∈ robust G (ν / 4) (layer G ν u 0) →
      3 * b + 5 / ν ≤ ((sampledBase G c R S u w).card : ℝ))
    (hrank : ∀ u i, i + 2 ≤ ⌊ν⁻¹⌋₊ → ∀ w,
      w ∈ robust G (ν / 4) (layer G ν u i \ layer G ν u 0) →
      2 * b + 20 / ν ≤
        ((sampledPred G c R S (layer G ν u i \ layer G ν u 0) w).card : ℝ))
    (hincoming : ∀ w, 2 * b + 20 / ν ≤
      ((sampledPred G c R S univ w).card : ℝ)) :
    letI : Quiver V := graphQuiver G
    ∀ u v, u ≠ v → ∀ (A : Finset V) (D : Finset C),
      (A.card : ℝ) ≤ b → (D.card : ℝ) ≤ b →
      ∃ P : DPath G u v, Allowed G c R A S D P ∧ (P.length : ℝ) ≤ ν⁻¹ + 1 := by
  letI : Quiver V := graphQuiver G
  classical
  intro u v huv A D hA hD
  let B : V → Finset V := fun z =>
    TwoEdgeChoices.exceptions G c z (ν * Fintype.card V / 16)
  have hB (z : V) : ((B z).card : ℝ) < 16 / ν :=
    (TwoEdgeChoices.deterministic_rainbow_choice_core G c hout hin hloop ν hν
      (Fintype.card_pos_iff.mpr ⟨u⟩) z).1
  obtain ⟨hhalf, hα, hupper⟩ := graph_parameter_bounds G ν τ α hν hτ hparams
    hloop hexp u (houtdeg u)
  have hn : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast Fintype.card_pos_iff.mpr (show Nonempty V from ⟨u⟩)
  have hn2 : (2 : ℝ) ≤ Fintype.card V := by
    have hαpos : 0 < α := lt_of_lt_of_le (add_pos hν hτ) hparams
    have hh : (1 : ℝ) < Fintype.card V := by nlinarith [mul_pos hαpos hn]
    have hnat : 1 < Fintype.card V := by exact_mod_cast hh
    exact_mod_cast (show 2 ≤ Fintype.card V by omega)
  have hnlarge : 4 < ν * Fintype.card V := by
    have hp3 : p ^ 3 ≤ (1 : ℝ) := pow_le_one₀ hp.le hpone
    have hνsq : ν ^ 2 ≤ ν := by
      have hh := mul_le_mul_of_nonneg_right (show ν ≤ 1 by linarith) hν.le
      nlinarith
    have hcoef : p ^ 3 * ν ^ 2 ≤ ν :=
      (mul_le_mul_of_nonneg_right hp3 (sq_nonneg ν)).trans (by simpa using hνsq)
    have hscale' := mul_le_mul_of_nonneg_right hcoef hn.le
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have hh := Real.one_sub_inv_le_log_of_pos (x := (2 : ℝ)) (by norm_num)
      norm_num at hh
      exact hh
    have hlogn := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hn2
    linarith
  obtain ⟨m, hm, _hsize, hcover⟩ := early_covering_layer G ν τ α hν hhalf hparams
    hα hnlarge hexp houtdeg hindeg u
  have hinv : 0 < ν⁻¹ := inv_pos.mpr hν
  have hmR : (m : ℝ) + 2 ≤ ν⁻¹ := by
    have hcast : (m : ℝ) + 2 ≤ (⌊ν⁻¹⌋₊ : ℝ) := by exact_mod_cast hm
    exact hcast.trans (Nat.floor_le hinv.le)
  have hmnonneg : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hinv2 : (2 : ℝ) ≤ ν⁻¹ := by linarith
  have hconnect : ∀ z, u ≠ z → z ∉ B u →
      ∀ (A' : Finset V) (D' : Finset C), (A'.card : ℝ) ≤ b + 1 →
      (D'.card : ℝ) ≤ b + 1 →
      ∃ P : DPath G u z, Allowed G c R A' S D' P ∧ P.length ≤ m + 2 := by
    intro z huz hz A' D' hA' hD'
    apply rank_path G c hloop hout hin ν hν R (B u) S u m A'.card D'.card
      (3 * b + 5 / ν) (2 * b + 20 / ν)
      (hbase u) (fun i hi => hrank u i (by omega))
      (by rw [div_eq_mul_inv]; nlinarith)
      (by have hh := hB u; rw [div_eq_mul_inv] at hh ⊢; nlinarith)
      m le_rfl z huz hz (hcover z) A' D' le_rfl le_rfl
  by_cases hv : v ∉ B u
  · obtain ⟨P, hp, hl⟩ := hconnect v huv hv A D (by linarith) (by linarith)
    refine ⟨P, hp, ?_⟩
    have hlR : (P.length : ℝ) ≤ (m : ℝ) + 2 := by exact_mod_cast hl
    linarith
  · let T := sampledPred G c R S univ v
    let H := T.filter (fun x => c x v ∈ D)
    have hH : H.card ≤ D.card := by
      apply card_le_card_of_injOn (fun x => c x v)
      · intro x hx
        exact (mem_filter.mp hx).2
      · intro x hx y hy hxy
        exact hin v (mem_filter.mp (mem_filter.mp (mem_filter.mp hx).1).1).2
          (mem_filter.mp (mem_filter.mp (mem_filter.mp hy).1).1).2 hxy
    have hbad : (A ∪ B u ∪ {u} ∪ H).card < T.card := by
      have h1 := card_union_le A (B u)
      have h2 := card_union_le (A ∪ B u) ({u} : Finset V)
      have h3 := card_union_le (A ∪ B u ∪ {u}) H
      have hnat : (A ∪ B u ∪ {u} ∪ H).card ≤ A.card + (B u).card + 1 + D.card := by
        simp only [card_singleton] at h2
        omega
      have hR : ((A ∪ B u ∪ {u} ∪ H).card : ℝ) ≤
          A.card + (B u).card + 1 + D.card := by exact_mod_cast hnat
      have hh := hB u
      have hc := hincoming v
      rw [div_eq_mul_inv] at hh hc
      exact_mod_cast (show ((A ∪ B u ∪ {u} ∪ H).card : ℝ) < T.card by
        dsimp only [T]; nlinarith)
    obtain ⟨x, hxT, hxbad⟩ := exists_mem_notMem_of_card_lt_card hbad
    have hxA : x ∉ A := fun h => hxbad
      (mem_union_left _ (mem_union_left _ (mem_union_left _ h)))
    have hxB : x ∉ B u := fun h => hxbad
      (mem_union_left _ (mem_union_left _ (mem_union_right _ h)))
    have hxu : x ≠ u := by
      intro h
      exact hxbad (mem_union_left _ (mem_union_right _ (mem_singleton.mpr h)))
    have hcd : c x v ∉ D := fun h => hxbad
      (mem_union_right _ (mem_filter.mpr ⟨hxT, h⟩))
    have hxPred := (mem_filter.mp hxT).1
    have hxRes := (mem_filter.mp hxT).2
    have hxv : G.Adj x v := (mem_filter.mp hxPred).2
    obtain ⟨P, hp, hl⟩ := hconnect x (Ne.symm hxu) hxB (insert v A) (insert (c x v) D)
      (by have hh : ((insert v A).card : ℝ) ≤ A.card + 1 := by
            exact_mod_cast card_insert_le v A
          linarith)
      (by have hh : ((insert (c x v) D).card : ℝ) ≤ D.card + 1 := by
            exact_mod_cast card_insert_le (c x v) D
          linarith)
    refine ⟨P.cons (PLift.up hxv), ?_, ?_⟩
    · exact append_allowed G c R A S D P hxv hp (Ne.symm huv)
        (fun h => hloop v (h.symm ▸ hxv)) ⟨hxRes.1, hxA⟩ ⟨hxRes.2, hcd⟩
    · have hlR : (P.length : ℝ) ≤ (m : ℝ) + 2 := by exact_mod_cast hl
      simp only [Quiver.Path.length_cons, Nat.cast_add, Nat.cast_one]
      linarith

end D5.S3.Combinatorics.Graph.Rainbow.RankDescent
