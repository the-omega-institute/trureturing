/- GID: D5/S3/Combinatorics/Graph/Rainbow/RobustLayers
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Rainbow/RobustLayers
   mirror-E: none(waiver:general-deterministic-theorems)
   anchors: [mathlib/module/Mathlib.Combinatorics.Digraph.Basic]
   utility: none
   digest: Exterior robust expansion gives an early covering layer and genuine predecessor ranks. -/

import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
Deterministic layers for the connecting lemma of arXiv:2503.01825v2,
Section 4.3. The early size threshold leaves room for one additional final edge.
Every robust threshold is normalized by the cardinality of the original graph.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [local instance] Classical.propDecidable

open Finset

namespace D5.S3.Combinatorics.Graph.Rainbow.RobustLayers

variable {V : Type*} [Fintype V]

/-- Incoming neighbours in an actual vertex set. -/
noncomputable def predecessors (G : Digraph V) (S : Finset V) (w : V) : Finset V := by
  classical
  exact S.filter (fun x => G.Adj x w)

/-- The threshold always uses the original number of vertices. -/
noncomputable def robust (G : Digraph V) (ν : ℝ) (S : Finset V) : Finset V := by
  classical
  exact univ.filter (fun w => ν * Fintype.card V ≤ (predecessors G S w).card)

/-- Exterior robust expansion, rather than a neighbourhood cardinality convention. -/
def ExteriorExpander (G : Digraph V) (ν τ : ℝ) : Prop :=
  ∀ S : Finset V, τ * Fintype.card V ≤ (S.card : ℝ) →
    (S.card : ℝ) ≤ (1 - τ) * Fintype.card V →
    ν * Fintype.card V ≤ ((robust G ν S \ S).card : ℝ)

/-- Zero-based indexing: layer zero is the root's outgoing star. -/
noncomputable def layer (G : Digraph V) (ν : ℝ) (u : V) : ℕ → Finset V
  | 0 => univ.filter (G.Adj u)
  | i + 1 => layer G ν u i ∪ robust G ν (layer G ν u i)

/-- The integer boundary is valid even when the expansion interval contains no integer.
Looplessness and one outgoing semidegree supply the strict upper boundary. -/
theorem graph_parameter_bounds (G : Digraph V) (ν τ α : ℝ)
    (hν : 0 < ν) (hτ : 0 < τ) (hparams : ν + τ ≤ α)
    (hloop : ∀ x, ¬ G.Adj x x) (hexp : ExteriorExpander G ν τ)
    (u : V) (hdeg : α * Fintype.card V ≤ ((layer G ν u 0).card : ℝ)) :
    ν < 1 / 2 ∧ 2 * ν * Fintype.card V - 1 < α * Fintype.card V ∧
      α * Fintype.card V + 1 ≤ Fintype.card V := by
  classical
  let n : ℝ := Fintype.card V
  have hnNat : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨u⟩
  have hn : 0 < n := by dsimp [n]; exact_mod_cast hnNat
  have hparamsN := mul_le_mul_of_nonneg_right hparams hn.le
  have hνn := mul_pos hν hn
  have hτn := mul_pos hτ hn
  have hsub : layer G ν u 0 ⊆ univ.erase u := by
    intro x hx
    refine mem_erase.mpr ⟨?_, mem_univ _⟩
    intro h
    exact hloop u (h ▸ (mem_filter.mp hx).2)
  have hcard := card_le_card hsub
  rw [card_erase_of_mem (mem_univ u), card_univ] at hcard
  have huNat : (layer G ν u 0).card + 1 ≤ Fintype.card V := by omega
  have huR : ((layer G ν u 0).card : ℝ) + 1 ≤ n := by
    dsimp only [n]
    exact_mod_cast huNat
  have hupper : α * n + 1 ≤ n := by dsimp [n] at *; linarith
  have hτone : τ < 1 := (mul_lt_mul_iff_right₀ hn).mp (by nlinarith)
  have hy : 0 ≤ (1 - τ) * n := mul_nonneg (by linarith) hn.le
  let m : ℕ := ⌊(1 - τ) * n⌋₊
  have hmlo : (m : ℝ) ≤ (1 - τ) * n := Nat.floor_le hy
  have hmhi : (1 - τ) * n < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmN : m ≤ Fintype.card V := by
    apply Nat.floor_le_of_le
    dsimp [n]
    nlinarith
  have hclose : ν * n < τ * n + 1 := by
    by_cases hinterval : τ * n ≤ (m : ℝ)
    · obtain ⟨T, _hT, hTc⟩ := exists_subset_card_eq
        (show m ≤ (univ : Finset V).card by simpa using hmN)
      have he := hexp T (by simpa [hTc, n] using hinterval)
        (by simpa [hTc, n] using hmlo)
      have hcomp : robust G ν T \ T ⊆ univ \ T := by
        intro x hx
        exact mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp hx).2⟩
      have hc := card_le_card hcomp
      have hp := card_sdiff_add_card_eq_card (subset_univ T)
      rw [card_univ, hTc] at hp
      have hcR : ((robust G ν T \ T).card : ℝ) + m ≤ n := by
        dsimp only [n]
        exact_mod_cast (show (robust G ν T \ T).card + m ≤ Fintype.card V by omega)
      dsimp [n] at *
      nlinarith
    · let k : ℕ := Fintype.card V / 2
      have hk1 : 2 * k ≤ Fintype.card V := by dsimp [k]; omega
      have hk2 : Fintype.card V ≤ 2 * k + 1 := by dsimp [k]; omega
      have hk1R : 2 * (k : ℝ) ≤ n := by
        dsimp only [n]
        exact_mod_cast hk1
      have hk2R : n ≤ 2 * (k : ℝ) + 1 := by
        dsimp only [n]
        exact_mod_cast hk2
      have hτk : (k : ℝ) < τ * n := by
        by_contra! h
        have hk : (k : ℝ) ≤ (1 - τ) * n := by nlinarith
        have hkm : k ≤ m := Nat.le_floor hk
        have hkmR : (k : ℝ) ≤ m := by exact_mod_cast hkm
        exact hinterval (by linarith)
      dsimp [n] at *
      nlinarith
  dsimp [n] at *
  constructor
  · apply (mul_lt_mul_iff_right₀ hn).mp
    nlinarith
  · exact ⟨by nlinarith, hupper⟩

private theorem layer_mono (G : Digraph V) (ν : ℝ) (u : V) :
    Monotone (layer G ν u) :=
  monotone_nat_of_le_succ (fun _ => subset_union_left)

/-- Membership outside the initial star supplies a strictly earlier robust rank.
The ranks are obtained from the graph recurrence, not assumed as routing data. -/
theorem earlier_rank (G : Digraph V) (ν : ℝ) (u x : V) (i : ℕ)
    (hx : x ∈ layer G ν u i) (hbase : x ∉ layer G ν u 0) :
    ∃ j < i, x ∈ robust G ν (layer G ν u j) := by
  classical
  revert hx
  induction i with
  | zero => intro hx; exact (hbase hx).elim
  | succ i ih =>
    intro hx
    rcases mem_union.mp hx with h | h
    · obtain ⟨j, hj, hxj⟩ := ih h
      exact ⟨j, Nat.lt_succ_of_lt hj, hxj⟩
    · exact ⟨i, Nat.lt_succ_self i, h⟩

private theorem step_growth (G : Digraph V) (ν τ α : ℝ) (u : V)
    (hν : 0 < ν) (hparams : ν + τ ≤ α)
    (hexp : ExteriorExpander G ν τ)
    (hdeg : α * Fintype.card V ≤ ((layer G ν u 0).card : ℝ))
    (i : ℕ)
    (hsmall : ((layer G ν u i).card : ℝ) <
      (1 - α + ν / 2) * Fintype.card V) :
    ((layer G ν u i).card : ℝ) + ν * Fintype.card V ≤
      ((layer G ν u (i + 1)).card : ℝ) := by
  classical
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hparamsN := mul_le_mul_of_nonneg_right hparams hn
  have hinit := card_le_card (layer_mono G ν u (Nat.zero_le i))
  have hinitR : ((layer G ν u 0).card : ℝ) ≤ (layer G ν u i).card := by
    exact_mod_cast hinit
  have hlo : τ * Fintype.card V ≤ ((layer G ν u i).card : ℝ) := by
    nlinarith
  have hhi : ((layer G ν u i).card : ℝ) ≤ (1 - τ) * Fintype.card V := by
    nlinarith
  have he := hexp (layer G ν u i) hlo hhi
  have hc := card_sdiff_add_card_eq_card
    (subset_union_left : layer G ν u i ⊆ layer G ν u i ∪ robust G ν (layer G ν u i))
  have heq : (layer G ν u i ∪ robust G ν (layer G ν u i)) \ layer G ν u i =
      robust G ν (layer G ν u i) \ layer G ν u i := by
    ext x
    simp only [mem_sdiff, mem_union]
    tauto
  rw [heq] at hc
  have hcR : ((robust G ν (layer G ν u i) \ layer G ν u i).card : ℝ) +
      (layer G ν u i).card = (layer G ν u (i + 1)).card := by
    exact_mod_cast hc
  linarith

private theorem predecessor_complement_bound (G : Digraph V) (S : Finset V) (w : V) :
    ((predecessors G univ w).card : ℝ) + S.card ≤
      (predecessors G S w).card + Fintype.card V := by
  classical
  have hsub : predecessors G univ w ⊆ predecessors G S w ∪ (univ \ S) := by
    intro x hx
    by_cases hs : x ∈ S
    · exact mem_union_left _ (mem_filter.mpr ⟨hs, (mem_filter.mp hx).2⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_univ _, hs⟩)
  have hcard := (card_le_card hsub).trans (card_union_le _ _)
  have hcomp := card_sdiff_add_card_eq_card (subset_univ S)
  rw [card_univ] at hcomp
  exact_mod_cast (show (predecessors G univ w).card + S.card ≤
    (predecessors G S w).card + Fintype.card V by omega)

/-- An actual robust layer reaches every target at half threshold two indices before
the reciprocal bound. The three numerical hypotheses are the arithmetic consequences
used by the early-stop argument; no layer growth or stopping conclusion is supplied. -/
theorem early_covering_layer (G : Digraph V) (ν τ α : ℝ)
    (hν : 0 < ν) (hhalf : ν < 1 / 2) (hparams : ν + τ ≤ α)
    (hα : 2 * ν * Fintype.card V - 1 < α * Fintype.card V)
    (hnlarge : 4 < ν * Fintype.card V)
    (hexp : ExteriorExpander G ν τ)
    (hout : ∀ u, α * Fintype.card V ≤ ((layer G ν u 0).card : ℝ))
    (hin : ∀ w, α * Fintype.card V ≤ ((predecessors G univ w).card : ℝ))
    (u : V) :
    ∃ m : ℕ, m + 2 ≤ ⌊ν⁻¹⌋₊ ∧
      (1 - α + ν / 2) * Fintype.card V ≤ ((layer G ν u m).card : ℝ) ∧
      ∀ w, w ∈ robust G (ν / 2) (layer G ν u m) := by
  classical
  let n : ℝ := Fintype.card V
  let K : ℕ := ⌊ν⁻¹⌋₊
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast Fintype.card_pos_iff.mpr (show Nonempty V from ⟨u⟩)
  have hK : 2 ≤ K := by
    apply Nat.le_floor
    change (2 : ℝ) ≤ ν⁻¹
    apply (mul_le_mul_iff_right₀ hν).mp
    rw [mul_inv_cancel₀ (ne_of_gt hν)]
    linarith
  have hfloor := Nat.lt_floor_add_one (ν⁻¹)
  have hKν : 1 < ((K : ℝ) + 1) * ν := by
    have hh := (mul_lt_mul_iff_left₀ hν).mpr hfloor
    dsimp [K]
    nlinarith [mul_inv_cancel₀ (ne_of_gt hν)]
  have hhit : ∃ m : ℕ, m + 2 ≤ K ∧
      (1 - α + ν / 2) * n ≤ ((layer G ν u m).card : ℝ) := by
    by_contra! hmiss
    have hlower : ∀ j : ℕ, j ≤ K - 2 →
        (α + (j : ℝ) * ν) * n ≤ ((layer G ν u j).card : ℝ) := by
      intro j
      induction j with
      | zero => intro _; simpa [n] using hout u
      | succ j ih =>
        intro hj
        have hi := ih (by omega)
        have hs := step_growth G ν τ α u hν hparams hexp (hout u) j
          (hmiss j (by omega))
        dsimp only [n] at hi ⊢
        push_cast
        nlinarith
    have hlow := hlower (K - 2) le_rfl
    have hsmall := hmiss (K - 2) (by omega)
    have hsub : ((K - 2 : ℕ) : ℝ) = (K : ℝ) - 2 := by
      rw [Nat.cast_sub hK]
      norm_num
    rw [hsub] at hlow
    have hprod : n < (2 * α + ((K : ℝ) - 5 / 2) * ν) * n := by
      have hpos := mul_pos (sub_pos.mpr hKν) hn
      dsimp [n] at hnlarge hα ⊢
      nlinarith
    nlinarith
  obtain ⟨m, hm, hsize⟩ := hhit
  refine ⟨m, hm, hsize, ?_⟩
  intro w
  have hc := predecessor_complement_bound G (layer G ν u m) w
  have hd := hin w
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  dsimp [n] at hsize
  nlinarith

end D5.S3.Combinatorics.Graph.Rainbow.RobustLayers
