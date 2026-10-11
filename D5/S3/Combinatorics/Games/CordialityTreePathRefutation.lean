/- GID: D5/S3/Combinatorics/Games/CordialityTreePathRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Games/CordialityTreePathRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Games/CordialityTreePathRefutation.claim; result=D5/S3/Combinatorics/Games/CordialityTreePathRefutation.result; claim=D5/S3/Combinatorics/Games/CordialityTreePathRefutation.claim
   digest: A ten-vertex tree exceeds the path's game cordiality number. -/

/-
result:
proof_shape: content
escape_witness: none
admission_basis: open-problem-resolution (#15128; Refuted)
Direct frozen dependency (where used):
D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.instDecidableRelFinAdjPathGraph_d5
(statement_id sha256:337ad150a1d9869c2b2aaa2ac02c4f7553b8d5dfacb80d6baf8dbdaf6ece292c).
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).

Declaration classification (each dependency identity is the declaration identity above).
free: proof_shape: bind-only; escape_witness: none; direct frozen dependencies: none; consumer:
  aCheckFast, aCheckFast_sound, aWin, free_insert_eq_erase, gameValue, gameValue_ge_of_iWin,
  gameValue_le_of_aWin, iWin, pairedDisjoint_step, paired_partner_free, paired_step,
  pairingValue, pairingValue_ge_three, pairingValue_le_gameValue, terminal_bound.
e1: proof_shape: bind-only; escape_witness: none; direct frozen dependencies: none; consumer:
  discrepancy, e0.
e0: proof_shape: bind-only; escape_witness: none; direct frozen dependencies: none; consumer:
  discrepancy.
discrepancy: proof_shape: bind-only; escape_witness: none; direct frozen dependencies: none;
  consumer: aCheckFast_sound, aWin, gameValue, gameValue_ge_of_iWin, gameValue_le_of_aWin, iWin,
  pairingValue_ge_three, pairingValue_le_gameValue, path_discrepancy_eq_all,
  path_discrepancy_eq_all_row_0, path_discrepancy_eq_all_row_1, path_discrepancy_eq_all_row_2,
  path_discrepancy_eq_all_row_3, path_discrepancy_eq_all_row_4, path_discrepancy_eq_all_row_5,
  path_discrepancy_eq_all_row_6, path_discrepancy_eq_all_row_7, terminal_bound,
  witness_discrepancy_eq_all, witness_discrepancy_eq_all_row_0,
  witness_discrepancy_eq_all_row_1, witness_discrepancy_eq_all_row_2,
  witness_discrepancy_eq_all_row_3, witness_discrepancy_eq_all_row_4,
  witness_discrepancy_eq_all_row_5, witness_discrepancy_eq_all_row_6,
  witness_discrepancy_eq_all_row_7.
free_insert_eq_erase: proof_shape: bind-only; escape_witness: none; direct frozen dependencies:
  none; consumer: aCheckFast, aCheckFast_sound, aWin, gameValue, gameValue_ge_of_iWin,
  gameValue_le_of_aWin, pairingValue_le_gameValue.
gameValue: proof_shape: content; escape_witness: none; direct frozen dependencies: none;
  consumer: cg, gameValue_ge_of_iWin, gameValue_le_of_aWin, pairingValue_le_gameValue,
  witness_lower.
cg: proof_shape: bind-only; escape_witness: none; direct frozen dependencies: none; consumer:
  claim, result, witness_lower.
witnessEdges: proof_shape: bind-only; escape_witness: none; direct frozen dependencies: none;
  consumer: pairingValue_ge_three, pairingValue_le_gameValue, result, terminal_bound, witness,
  witness_connected, witness_discrepancy_eq_all, witness_discrepancy_eq_all_row_0,
  witness_discrepancy_eq_all_row_1, witness_discrepancy_eq_all_row_2,
  witness_discrepancy_eq_all_row_3, witness_discrepancy_eq_all_row_4,
  witness_discrepancy_eq_all_row_5, witness_discrepancy_eq_all_row_6,
  witness_discrepancy_eq_all_row_7, witness_edge_card, witness_lower.
witness: proof_shape: bind-only; escape_witness: none; direct frozen dependencies: none;
  consumer: pairingValue_ge_three, pairingValue_le_gameValue, result, terminal_bound,
  witness_connected, witness_discrepancy_eq_all, witness_discrepancy_eq_all_row_0,
  witness_discrepancy_eq_all_row_1, witness_discrepancy_eq_all_row_2,
  witness_discrepancy_eq_all_row_3, witness_discrepancy_eq_all_row_4,
  witness_discrepancy_eq_all_row_5, witness_discrepancy_eq_all_row_6,
  witness_discrepancy_eq_all_row_7, witness_edge_card, witness_isTree, witness_lower.
aWin: proof_shape: content; escape_witness: none; direct frozen dependencies: none; consumer:
  aCheckFast_sound, gameValue_le_of_aWin.
iWin: proof_shape: content; escape_witness: none; direct frozen dependencies: none; consumer:
  gameValue_ge_of_iWin, pairingValue_le_gameValue.
gameValue_le_of_aWin: proof_shape: content; escape_witness: none; direct frozen dependencies:
  none; consumer: path_upper.
gameValue_ge_of_iWin: proof_shape: content; escape_witness: none; direct frozen dependencies:
  none; consumer: pairingValue_le_gameValue.
pathTable: proof_shape: bind-only; escape_witness: none; direct frozen dependencies: none;
  consumer: pathStrategy.
pathStrategy: proof_shape: bind-only; escape_witness: none; direct frozen dependencies: none;
  consumer: path_upper.
cutCount: proof_shape: bind-only; escape_witness: none; direct frozen dependencies: none;
  consumer: fastDiscrepancy.
fastDiscrepancy: proof_shape: bind-only; escape_witness: none; direct frozen dependencies: none;
  consumer: aCheckFast, aCheckFast_sound, pairingValue, pairingValue_ge_three,
  pairingValue_le_gameValue, path_discrepancy_eq_all, path_discrepancy_eq_all_row_0,
  path_discrepancy_eq_all_row_1, path_discrepancy_eq_all_row_2, path_discrepancy_eq_all_row_3,
  path_discrepancy_eq_all_row_4, path_discrepancy_eq_all_row_5, path_discrepancy_eq_all_row_6,
  path_discrepancy_eq_all_row_7, witness_discrepancy_eq_all, witness_discrepancy_eq_all_row_0,
  witness_discrepancy_eq_all_row_1, witness_discrepancy_eq_all_row_2,
  witness_discrepancy_eq_all_row_3, witness_discrepancy_eq_all_row_4,
  witness_discrepancy_eq_all_row_5, witness_discrepancy_eq_all_row_6,
  witness_discrepancy_eq_all_row_7.
pathEdges: proof_shape: bind-only; escape_witness: none; direct frozen dependencies: none;
  consumer: aCheckFast_sound, path_discrepancy_eq_all, path_discrepancy_eq_all_row_0,
  path_discrepancy_eq_all_row_1, path_discrepancy_eq_all_row_2, path_discrepancy_eq_all_row_3,
  path_discrepancy_eq_all_row_4, path_discrepancy_eq_all_row_5, path_discrepancy_eq_all_row_6,
  path_discrepancy_eq_all_row_7, path_upper.
witnessEdgesFast: proof_shape: bind-only; escape_witness: none; direct frozen dependencies:
  none; consumer: pairingValue_ge_three, pairingValue_le_gameValue, witness_discrepancy_eq_all,
  witness_discrepancy_eq_all_row_0, witness_discrepancy_eq_all_row_1,
  witness_discrepancy_eq_all_row_2, witness_discrepancy_eq_all_row_3,
  witness_discrepancy_eq_all_row_4, witness_discrepancy_eq_all_row_5,
  witness_discrepancy_eq_all_row_6, witness_discrepancy_eq_all_row_7, witness_lower.
partner: proof_shape: bind-only; escape_witness: none; direct frozen dependencies: none;
  consumer: paired, pairedDisjoint_step, paired_card, paired_partner_free, paired_step,
  pairingValue, pairingValue_ge_three, pairingValue_le_gameValue, partner_involutive,
  partner_ne, terminal_bound.
aCheckFast: proof_shape: content; escape_witness: none; direct frozen dependencies: none;
  consumer: aCheckFast_sound, path_upper.
pairingValue: proof_shape: content; escape_witness: none; direct frozen dependencies: none;
  consumer: pairingValue_ge_three, pairingValue_le_gameValue, witness_lower.
path_discrepancy_eq_all_row_0: proof_shape: bind-only; escape_witness: none; direct frozen
  dependencies: path-graph instance above; consumer: path_discrepancy_eq_all.
path_discrepancy_eq_all_row_1: proof_shape: bind-only; escape_witness: none; direct frozen
  dependencies: path-graph instance above; consumer: path_discrepancy_eq_all.
path_discrepancy_eq_all_row_2: proof_shape: bind-only; escape_witness: none; direct frozen
  dependencies: path-graph instance above; consumer: path_discrepancy_eq_all.
path_discrepancy_eq_all_row_3: proof_shape: bind-only; escape_witness: none; direct frozen
  dependencies: path-graph instance above; consumer: path_discrepancy_eq_all.
path_discrepancy_eq_all_row_4: proof_shape: bind-only; escape_witness: none; direct frozen
  dependencies: path-graph instance above; consumer: path_discrepancy_eq_all.
path_discrepancy_eq_all_row_5: proof_shape: bind-only; escape_witness: none; direct frozen
  dependencies: path-graph instance above; consumer: path_discrepancy_eq_all.
path_discrepancy_eq_all_row_6: proof_shape: bind-only; escape_witness: none; direct frozen
  dependencies: path-graph instance above; consumer: path_discrepancy_eq_all.
path_discrepancy_eq_all_row_7: proof_shape: bind-only; escape_witness: none; direct frozen
  dependencies: path-graph instance above; consumer: path_discrepancy_eq_all.
path_discrepancy_eq_all: proof_shape: bind-only; escape_witness: none; direct frozen
  dependencies: path-graph instance above; consumer: aCheckFast_sound.
fold_and_true_iff: proof_shape: bind-only; escape_witness: none; direct frozen dependencies:
  none; consumer: aCheckFast_sound.
aCheckFast_sound: proof_shape: content; escape_witness: none; direct frozen dependencies:
  path-graph instance above; consumer: path_upper.
witness_discrepancy_eq_all_row_0: proof_shape: bind-only; escape_witness: none; direct frozen
  dependencies: none; consumer: witness_discrepancy_eq_all.
witness_discrepancy_eq_all_row_1: proof_shape: bind-only; escape_witness: none; direct frozen
  dependencies: none; consumer: witness_discrepancy_eq_all.
witness_discrepancy_eq_all_row_2: proof_shape: bind-only; escape_witness: none; direct frozen
  dependencies: none; consumer: witness_discrepancy_eq_all.
witness_discrepancy_eq_all_row_3: proof_shape: bind-only; escape_witness: none; direct frozen
  dependencies: none; consumer: witness_discrepancy_eq_all.
witness_discrepancy_eq_all_row_4: proof_shape: bind-only; escape_witness: none; direct frozen
  dependencies: none; consumer: witness_discrepancy_eq_all.
witness_discrepancy_eq_all_row_5: proof_shape: bind-only; escape_witness: none; direct frozen
  dependencies: none; consumer: witness_discrepancy_eq_all.
witness_discrepancy_eq_all_row_6: proof_shape: bind-only; escape_witness: none; direct frozen
  dependencies: none; consumer: witness_discrepancy_eq_all.
witness_discrepancy_eq_all_row_7: proof_shape: bind-only; escape_witness: none; direct frozen
  dependencies: none; consumer: witness_discrepancy_eq_all.
witness_discrepancy_eq_all: proof_shape: bind-only; escape_witness: none; direct frozen
  dependencies: none; consumer: pairingValue_ge_three, pairingValue_le_gameValue.
paired: proof_shape: bind-only; escape_witness: none; direct frozen dependencies: none;
  consumer: pairedDisjoint, pairedDisjoint_step, paired_card, paired_partner_free, paired_step,
  pairingValue_ge_three, pairingValue_le_gameValue, witness_lower.
partner_involutive: proof_shape: bind-only; escape_witness: none; direct frozen dependencies:
  none; consumer: paired_card, paired_partner_free.
partner_ne: proof_shape: bind-only; escape_witness: none; direct frozen dependencies: none;
  consumer: pairedDisjoint_step, paired_partner_free.
paired_card: proof_shape: bind-only; escape_witness: none; direct frozen dependencies: none;
  consumer: pairingValue_le_gameValue.
paired_partner_free: proof_shape: bind-only; escape_witness: none; direct frozen dependencies:
  none; consumer: pairedDisjoint_step, pairingValue_le_gameValue.
paired_step: proof_shape: bind-only; escape_witness: none; direct frozen dependencies: none;
  consumer: pairedDisjoint_step, pairingValue_le_gameValue.
pairingValue_le_gameValue: proof_shape: content; escape_witness: none; direct frozen
  dependencies: none; consumer: witness_lower.
terminal_bound: proof_shape: bind-only; escape_witness: none; direct frozen dependencies: none;
  consumer: pairingValue_ge_three.
pairedDisjoint: proof_shape: bind-only; escape_witness: none; direct frozen dependencies: none;
  consumer: pairedDisjoint_step, pairingValue_ge_three.
pairedDisjoint_step: proof_shape: bind-only; escape_witness: none; direct frozen dependencies:
  none; consumer: pairingValue_ge_three.
pairingValue_ge_three: proof_shape: content; escape_witness: none; direct frozen dependencies:
  none; consumer: witness_lower.
path_upper: proof_shape: content; escape_witness: none; direct frozen dependencies: path-graph
  instance above; consumer: result.
witness_connected: proof_shape: bind-only; escape_witness: none; direct frozen dependencies:
  none; consumer: witness_isTree.
witness_edge_card: proof_shape: bind-only; escape_witness: none; direct frozen dependencies:
  none; consumer: witness_isTree.
claim: proof_shape: bind-only; escape_witness: none; direct frozen dependencies: none; consumer:
  result.
witness_isTree: proof_shape: bind-only; escape_witness: none; direct frozen dependencies: none;
  consumer: result.
witness_lower: proof_shape: content; escape_witness: none; direct frozen dependencies: none;
  consumer: result.
result: proof_shape: content; escape_witness: none; direct frozen dependencies: path-graph
  instance above; consumer: settling result.
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.Colex
import D5.S3.StatisticalMechanics.Percolation.DirectProductCyclePathBootstrap

set_option autoImplicit false

namespace D5.S3.Combinatorics.Games.CordialityTreePathRefutation

open scoped BigOperators

def free {n : Nat} (A B : Finset (Fin n)) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)) \ (A ∪ B)

def e1 {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) : Nat :=
  ((G.edgeFinset).filter (fun e => ∃ u ∈ e, ∃ v ∈ e, u ∈ A ∧ v ∉ A)).card

def e0 {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) : Nat :=
  G.edgeFinset.card - e1 G A

def discrepancy {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) : Nat :=
  Int.natAbs ((e1 G A : Int) - e0 G A)

private lemma free_insert_eq_erase {n : Nat} {A B : Finset (Fin n)} {v : Fin n}
    : free (insert v A) B = (free A B).erase v := by
  simp only [free, Finset.insert_union, Finset.sdiff_insert]

def gameValue {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) : Nat :=
  if h : free A B = ∅ then discrepancy G A
  else if A.card = B.card then
    let U := free A B
    (U.attach.image (fun v => gameValue G (insert v.1 A) B)).min'
      (Finset.image_nonempty.mpr (Finset.Nonempty.attach
        (Finset.nonempty_iff_ne_empty.mpr (by simpa [U] using h))))
  else
    let U := free A B
    (U.attach.image (fun v => gameValue G A (insert v.1 B))).max'
      (Finset.image_nonempty.mpr (Finset.Nonempty.attach
        (Finset.nonempty_iff_ne_empty.mpr (by simpa [U] using h))))
termination_by (free A B).card
decreasing_by
  next =>
    have hcard : (free (insert v.1 A) B).card < (free A B).card := by
      rw [free_insert_eq_erase]
      exact Finset.card_erase_lt_of_mem v.2
    exact hcard
  next =>
    have hcard : (free A (insert v.1 B)).card < (free A B).card := by
      rw [show free A (insert v.1 B) = (free A B).erase v.1 by
        ext x
        by_cases hx : x = v.1 <;> simp [free, hx]]
      exact Finset.card_erase_lt_of_mem v.2
    exact hcard

def cg {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Nat := gameValue G ∅ ∅

private def witnessEdges : Finset (Sym2 (Fin 10)) :=
  {s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 5), s(5, 6), s(6, 7), s(0, 8), s(0, 9)}

@[reducible]
private def witness : SimpleGraph (Fin 10) :=
  SimpleGraph.fromEdgeSet (witnessEdges : Set (Sym2 (Fin 10)))

private def aWin {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : Nat) (σ : Finset (Fin n) → Finset (Fin n) → Fin n)
    (A B : Finset (Fin n)) : Prop :=
  if _h : free A B = ∅ then discrepancy G A ≤ k
  else if A.card = B.card then
    if _hσ : σ A B ∈ free A B then aWin G k σ (insert (σ A B) A) B else False
  else
    ∀ v : free A B, aWin G k σ A (insert v.1 B)
termination_by (free A B).card
decreasing_by
  next =>
    rw [free_insert_eq_erase]
    exact Finset.card_erase_lt_of_mem ‹_›
  next =>
    rw [show free A (insert v.1 B) = (free A B).erase v.1 by
      ext x
      by_cases hx : x = v.1 <;> simp [free, hx]]
    exact Finset.card_erase_lt_of_mem v.2

private def iWin {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : Nat) (τ : Finset (Fin n) → Finset (Fin n) → Fin n)
    (A B : Finset (Fin n)) : Prop :=
  if _h : free A B = ∅ then k ≤ discrepancy G A
  else if A.card = B.card then
    ∀ v : free A B, iWin G k τ (insert v.1 A) B
  else
    if _hτ : τ A B ∈ free A B then iWin G k τ A (insert (τ A B) B) else False
termination_by (free A B).card
decreasing_by
  next =>
    rw [show free (insert v.1 A) B = (free A B).erase v.1 by
      ext x
      by_cases hx : x = v.1 <;> simp [free, hx]]
    exact Finset.card_erase_lt_of_mem v.2
  next =>
    rw [show free A (insert (τ A B) B) = (free A B).erase (τ A B) by
      ext x
      by_cases hx : x = τ A B <;> simp [free, hx]]
    exact Finset.card_erase_lt_of_mem ‹_›

private theorem gameValue_le_of_aWin {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : Nat) (σ : Finset (Fin n) → Finset (Fin n) → Fin n)
    (A B : Finset (Fin n)) (hσ : aWin G k σ A B) : gameValue G A B ≤ k := by
  induction hcard : (free A B).card using Nat.strong_induction_on generalizing A B with
  | h m ih =>
      by_cases hfree : free A B = ∅
      · rw [gameValue]
        rw [dif_pos hfree]
        rw [aWin] at hσ
        rw [dif_pos hfree] at hσ
        exact hσ
      · by_cases hturn : A.card = B.card
        · rw [gameValue]
          rw [dif_neg hfree, if_pos hturn]
          have hσ' := hσ
          rw [aWin] at hσ'
          rw [dif_neg hfree, if_pos hturn] at hσ'
          have hw : σ A B ∈ free A B := by
            split at hσ'
            · assumption
            · contradiction
          have hrec : aWin G k σ (insert (σ A B) A) B := by
            rw [dif_pos hw] at hσ'
            exact hσ'
          have hlt : (free (insert (σ A B) A) B).card < m := by
            calc
              (free (insert (σ A B) A) B).card < (free A B).card := by
                rw [free_insert_eq_erase]
                exact Finset.card_erase_lt_of_mem hw
              _ = m := hcard
          have hv := ih _ hlt _ _ hrec rfl
          apply le_trans (Finset.min'_le _ _ ?_) hv
          exact Finset.mem_image.mpr ⟨⟨σ A B, hw⟩,
            Finset.mem_attach _ _, rfl⟩
        · rw [gameValue]
          rw [dif_neg hfree, if_neg hturn]
          refine Finset.max'_le _
            (Finset.image_nonempty.mpr
              (Finset.Nonempty.attach (Finset.nonempty_iff_ne_empty.mpr hfree))) k ?_
          intro z hz
          rcases Finset.mem_image.mp hz with ⟨v, hv, rfl⟩
          have hrec : aWin G k σ A (insert v.1 B) := by
            have hσ' := hσ
            rw [aWin] at hσ'
            rw [dif_neg hfree, if_neg hturn] at hσ'
            exact hσ' v
          have hlt : (free A (insert v.1 B)).card < m := by
            calc
              (free A (insert v.1 B)).card < (free A B).card := by
                rw [show free A (insert v.1 B) = (free A B).erase v.1 by
                  ext x
                  by_cases hx : x = v.1 <;> simp [free, hx]]
                exact Finset.card_erase_lt_of_mem v.2
              _ = m := hcard
          exact ih _ hlt _ _ hrec rfl

private theorem gameValue_ge_of_iWin {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : Nat) (τ : Finset (Fin n) → Finset (Fin n) → Fin n)
    (A B : Finset (Fin n)) (hτ : iWin G k τ A B) : k ≤ gameValue G A B := by
  induction hcard : (free A B).card using Nat.strong_induction_on generalizing A B with
  | h m ih =>
      by_cases hfree : free A B = ∅
      · rw [gameValue]
        rw [dif_pos hfree]
        rw [iWin] at hτ
        rw [dif_pos hfree] at hτ
        exact hτ
      · by_cases hturn : A.card = B.card
        · rw [gameValue]
          rw [dif_neg hfree, if_pos hturn]
          have hτ' := hτ
          rw [iWin] at hτ'
          rw [dif_neg hfree, if_pos hturn] at hτ'
          refine Finset.le_min' _
            (Finset.image_nonempty.mpr
              (Finset.Nonempty.attach (Finset.nonempty_iff_ne_empty.mpr hfree))) k ?_
          intro z hz
          rcases Finset.mem_image.mp hz with ⟨v, hv, rfl⟩
          have hrec : iWin G k τ (insert v.1 A) B := by
              exact hτ' v
          have hlt : (free (insert v.1 A) B).card < m := by
            calc
              (free (insert v.1 A) B).card < (free A B).card := by
                rw [show free (insert v.1 A) B = (free A B).erase v.1 by
                  ext x
                  by_cases hx : x = v.1 <;> simp [free, hx]]
                exact Finset.card_erase_lt_of_mem v.2
              _ = m := hcard
          exact ih _ hlt _ _ hrec rfl
        · rw [gameValue]
          rw [dif_neg hfree, if_neg hturn]
          have hτ' := hτ
          rw [iWin] at hτ'
          rw [dif_neg hfree, if_neg hturn] at hτ'
          have hw : τ A B ∈ free A B := by
            split at hτ'
            · assumption
            · contradiction
          have hrec : iWin G k τ A (insert (τ A B) B) := by
            rw [dif_pos hw] at hτ'
            exact hτ'
          have hlt : (free A (insert (τ A B) B)).card < m := by
            calc
              (free A (insert (τ A B) B)).card < (free A B).card := by
                rw [show free A (insert (τ A B) B) = (free A B).erase (τ A B) by
                  ext x
                  by_cases hx : x = τ A B <;> simp [free, hx]]
                exact Finset.card_erase_lt_of_mem hw
              _ = m := hcard
          apply le_trans (ih _ hlt _ _ hrec rfl)
          apply Finset.le_max'
          exact Finset.mem_image.mpr ⟨⟨τ A B, hw⟩,
            Finset.mem_attach _ _, rfl⟩

private def pathTable : List (Nat × List (Nat × Fin 10)) :=
  [(0, [(0,0)]), (1, [(2,3), (4,1), (8,1), (16,7), (32,3), (64,1), (128,1), (256,1),
   (512,3)]), (3, [(12,4), (20,5), (24,2), (36,3), (40,2), (68,3), (72,2), (80,5), (96,3),
   (132,4), (136,2), (144,2), (160,2), (192,2), (260,3), (264,2), (272,6), (288,2), (320,2),
   (384,4), (516,3), (520,2), (576,2), (640,4), (768,4)]), (7, [(56,6), (88,5), (104,4),
   (152,5), (168,4), (176,6), (200,4), (208,5), (224,4), (280,5), (296,4), (304,9), (328,4),
   (336,5), (352,4), (392,4), (400,9), (416,4), (448,9), (536,5), (552,4), (584,4), (592,5),
   (608,4), (648,4), (656,8), (672,4), (704,8), (776,4), (800,4), (832,7)]), (9, [(6,4),
   (18,7), (34,2), (36,1), (48,7), (66,2), (96,1), (130,4), (160,4), (258,2), (288,4),
   (514,2), (516,1), (528,6), (544,1), (576,4), (640,4), (768,4)]), (11, [(52,7), (84,8),
   (100,4), (112,8), (164,4), (196,4), (224,4), (276,6), (292,4), (324,4), (352,4), (388,4),
   (532,6), (548,4), (560,7), (580,4), (608,4), (644,4), (672,4), (772,4), (800,4)]), (13,
   [(50,7), (82,8), (98,4), (162,4), (194,4), (274,6), (290,4), (322,4), (386,4), (530,6),
   (546,4), (578,4), (642,4), (770,4)]), (19, [(44,7), (76,5), (140,5), (164,3), (196,3),
   (268,5), (388,3), (392,2), (416,2), (448,9), (524,5), (644,3), (648,2), (672,2), (704,8),
   (772,3), (776,2), (800,2), (832,7), (896,6)]), (23, [(232,8), (360,7), (424,6), (456,9),
   (480,9), (616,7), (680,6), (712,8), (736,8), (808,6), (840,7), (864,7), (904,6),
   (928,6)]), (25, [(38,7), (70,5), (134,5), (162,2), (164,1), (194,2), (224,1), (262,5),
   (290,2), (292,1), (352,1), (386,2), (416,1), (518,5), (578,2), (580,1), (608,1), (642,2),
   (644,1), (672,1), (704,8), (770,2), (772,1), (800,1), (832,7), (896,6)]), (27, [(228,8),
   (356,7), (420,6), (452,9), (480,9), (612,7), (676,6), (708,8), (736,8), (804,6), (836,7),
   (864,7), (900,6), (928,6)]), (29, [(226,8), (354,7), (418,6), (450,9), (610,7), (674,6),
   (706,8), (802,6), (834,7), (898,6)]), (35, [(28,6), (84,8), (88,2), (148,6), (208,2),
   (276,6), (336,2), (532,6), (592,2)]), (39, [(216,8), (344,7), (408,9), (464,9), (600,7),
   (664,8), (720,8), (792,7), (848,7)]), (51, [(204,8), (332,7), (396,9), (588,7), (652,8),
   (780,7)]), (57, [(198,8), (326,7), (390,9), (582,7), (646,8), (774,7)]), (67, [(276,3),
   (280,9), (304,7), (400,5), (784,3)]), (71, [(184,8), (312,9), (432,9), (568,8), (688,8)]),
   (73, [(530,2), (532,1), (560,7), (656,5), (784,1)]), (75, [(308,7), (404,5), (564,7),
   (660,5), (788,5), (816,7), (912,5)]), (77, [(306,7), (402,5), (562,7), (658,5), (786,5)]),
   (83, [(900,3), (904,2), (928,2)]), (89, [(898,2), (900,1), (928,1)]), (99, [(156,8),
   (284,9), (404,3), (408,9), (540,8), (660,3), (788,3), (912,3)]), (105, [(658,2), (660,1),
   (912,1)]), (129, [(18,2), (20,3), (24,2), (48,3), (80,8), (272,6), (528,3)]), (133,
   [(26,6), (50,3), (56,8), (82,8), (88,1), (274,6), (280,1), (530,3), (536,5)]), (135,
   [(120,9), (312,9), (344,5), (600,5), (792,5), (840,4), (848,5), (864,4)]), (137, [(22,6),
   (50,2), (52,1), (82,8), (84,8), (112,8), (274,6), (276,6), (304,6), (530,2), (532,1),
   (560,1), (592,8), (784,6)]), (139, [(116,8), (308,6), (564,6), (596,8), (624,8), (788,6),
   (816,6)]), (141, [(114,8), (306,6), (562,6), (594,8), (786,6)]), (147, [(108,8), (300,6),
   (556,6), (836,3), (840,2), (864,2)]), (153, [(102,8), (294,6), (550,6), (834,2), (836,1),
   (864,1)]), (165, [(538,6), (600,1), (792,1)]), (193, [(274,2), (276,1), (280,5), (304,1),
   (784,2)]), (195, [(284,9), (308,3), (312,9), (788,3), (816,3)]), (197, [(58,8), (282,5),
   (306,3), (538,5), (786,3), (792,5), (816,3)]), (201, [(54,8), (278,5), (306,2), (308,1),
   (534,5), (562,2), (564,1), (786,2), (788,1), (816,1)]), (225, [(282,2), (284,9),
   (792,2)]), (263, [(664,5), (688,6), (712,4), (720,5), (736,4)]), (267, [(116,7), (212,9),
   (240,9), (596,7), (624,7)]), (269, [(114,7), (210,9), (594,7)]), (275, [(708,3), (712,2),
   (736,2)]), (281, [(706,2), (708,1), (736,1)]), (291, [(92,7), (212,9), (596,7)]), (385,
   [(82,2), (84,1), (88,5), (112,2), (592,1)]), (387, [(92,5), (116,3), (596,3), (600,5),
   (624,3)]), (389, [(58,6), (90,9), (114,3), (120,9), (568,6), (594,3), (624,3)]), (393,
   [(86,9), (114,2), (116,1), (594,2), (596,1), (624,1)]), (417, [(90,9), (92,1), (600,1)]),
   (519, [(312,6), (368,7), (408,5), (432,6), (456,4), (464,5), (480,4)]), (531, [(452,3),
   (456,2), (480,2)]), (579, [(284,5), (312,2), (408,2)])]

private def pathStrategy (A B : Finset (Fin 10)) : Fin 10 :=
  (((pathTable.lookup (Finset.equivBitIndices.symm (A.image Fin.val))).getD []).lookup
    (Finset.equivBitIndices.symm (B.image Fin.val))).getD 0

private def cutCount (E : Finset (Fin 10 × Fin 10)) (A : Finset (Fin 10)) : Nat :=
  (E.filter (fun e => (e.1 ∈ A ∧ e.2 ∉ A) ∨ (e.2 ∈ A ∧ e.1 ∉ A))).card

private def fastDiscrepancy (E : Finset (Fin 10 × Fin 10)) (A : Finset (Fin 10)) : Nat :=
  Int.natAbs ((cutCount E A : Int) - (E.card - cutCount E A : Int))

private def pathEdges : Finset (Fin 10 × Fin 10) :=
  {(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8), (8, 9)}

private def witnessEdgesFast : Finset (Fin 10 × Fin 10) :=
  {(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (0, 8), (0, 9)}

private def partner (v : Fin 10) : Fin 10 :=
  if v = 0 then 4 else if v = 4 then 0 else
  if v = 1 then 5 else if v = 5 then 1 else
  if v = 2 then 6 else if v = 6 then 2 else
  if v = 3 then 7 else if v = 7 then 3 else
  if v = 8 then 9 else 8

private def aCheckFast (E : Finset (Fin 10 × Fin 10)) (k : Nat)
    (σ : Finset (Fin 10) → Finset (Fin 10) → Fin 10)
    (A B : Finset (Fin 10)) : Bool :=
  if _h : free A B = ∅ then decide (fastDiscrepancy E A ≤ k)
  else if A.card = B.card then
    if _hσ : σ A B ∈ free A B then aCheckFast E k σ (insert (σ A B) A) B else false
  else
    Finset.fold (· && ·) true (fun v => aCheckFast E k σ A (insert v.1 B))
      (free A B).attach
termination_by (free A B).card
decreasing_by
  next =>
    rw [free_insert_eq_erase]
    exact Finset.card_erase_lt_of_mem ‹_›
  next =>
    rw [show free A (insert v.1 B) = (free A B).erase v.1 by
      ext x
      by_cases hx : x = v.1 <;> simp [free, hx]]
    exact Finset.card_erase_lt_of_mem v.2

private def pairingValue (E : Finset (Fin 10 × Fin 10))
    (A B : Finset (Fin 10)) : Nat :=
  if h : free A B = ∅ then fastDiscrepancy E A
  else
    (free A B).attach.image
      (fun v => pairingValue E (insert v.1 A) (insert (partner v.1) B)) |>.min'
      (Finset.image_nonempty.mpr
        (Finset.Nonempty.attach (Finset.nonempty_iff_ne_empty.mpr h)))
termination_by (free A B).card
decreasing_by
  have hsub : free (insert v.1 A) (insert (partner v.1) B) ⊆
      (free A B).erase v.1 := by
    intro x hx
    simp only [free, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_union,
      Finset.mem_insert, Finset.mem_univ] at hx ⊢
    rcases hx with ⟨_, hxnot⟩
    refine ⟨?_, True.intro, ?_⟩
    · intro hxeq
      apply hxnot
      simp [hxeq]
    · intro hxmem
      apply hxnot
      rcases hxmem with hxa | hxb <;> aesop
  exact lt_of_le_of_lt (Finset.card_le_card hsub)
    (Finset.card_erase_lt_of_mem v.2)

private theorem path_discrepancy_eq_all_row_0 : ∀ A : Finset (Fin 10),
    0 ∉ A → 1 ∉ A → 2 ∉ A →
    fastDiscrepancy pathEdges A = discrepancy (SimpleGraph.pathGraph 10) A := by
  decide +kernel

private theorem path_discrepancy_eq_all_row_1 : ∀ A : Finset (Fin 10),
    0 ∈ A → 1 ∉ A → 2 ∉ A →
    fastDiscrepancy pathEdges A = discrepancy (SimpleGraph.pathGraph 10) A := by
  decide +kernel

private theorem path_discrepancy_eq_all_row_2 : ∀ A : Finset (Fin 10),
    0 ∉ A → 1 ∈ A → 2 ∉ A →
    fastDiscrepancy pathEdges A = discrepancy (SimpleGraph.pathGraph 10) A := by
  decide +kernel

private theorem path_discrepancy_eq_all_row_3 : ∀ A : Finset (Fin 10),
    0 ∈ A → 1 ∈ A → 2 ∉ A →
    fastDiscrepancy pathEdges A = discrepancy (SimpleGraph.pathGraph 10) A := by
  decide +kernel

private theorem path_discrepancy_eq_all_row_4 : ∀ A : Finset (Fin 10),
    0 ∉ A → 1 ∉ A → 2 ∈ A →
    fastDiscrepancy pathEdges A = discrepancy (SimpleGraph.pathGraph 10) A := by
  decide +kernel

private theorem path_discrepancy_eq_all_row_5 : ∀ A : Finset (Fin 10),
    0 ∈ A → 1 ∉ A → 2 ∈ A →
    fastDiscrepancy pathEdges A = discrepancy (SimpleGraph.pathGraph 10) A := by
  decide +kernel

private theorem path_discrepancy_eq_all_row_6 : ∀ A : Finset (Fin 10),
    0 ∉ A → 1 ∈ A → 2 ∈ A →
    fastDiscrepancy pathEdges A = discrepancy (SimpleGraph.pathGraph 10) A := by
  decide +kernel

private theorem path_discrepancy_eq_all_row_7 : ∀ A : Finset (Fin 10),
    0 ∈ A → 1 ∈ A → 2 ∈ A →
    fastDiscrepancy pathEdges A = discrepancy (SimpleGraph.pathGraph 10) A := by
  decide +kernel

private theorem path_discrepancy_eq_all (A : Finset (Fin 10)) :
    fastDiscrepancy pathEdges A = discrepancy (SimpleGraph.pathGraph 10) A := by
  by_cases hzero : (0 : Fin 10) ∈ A <;>
    by_cases hone : (1 : Fin 10) ∈ A <;>
      by_cases htwo : (2 : Fin 10) ∈ A
  · exact path_discrepancy_eq_all_row_7 A hzero hone htwo
  · exact path_discrepancy_eq_all_row_3 A hzero hone htwo
  · exact path_discrepancy_eq_all_row_5 A hzero hone htwo
  · exact path_discrepancy_eq_all_row_1 A hzero hone htwo
  · exact path_discrepancy_eq_all_row_6 A hzero hone htwo
  · exact path_discrepancy_eq_all_row_2 A hzero hone htwo
  · exact path_discrepancy_eq_all_row_4 A hzero hone htwo
  · exact path_discrepancy_eq_all_row_0 A hzero hone htwo

private lemma fold_and_true_iff {α : Type*} (s : Finset α) (f : α → Bool) :
    Finset.fold (· && ·) true f s = true ↔ ∀ x ∈ s, f x = true := by
  simpa using (Finset.fold_op_rel_iff_and (op := Bool.and) (s := s) (b := true)
    (f := f) (r := fun (_ : Bool) x => x = true) (c := true)
    (by intros; simp only [Bool.and_eq_true]))

private theorem aCheckFast_sound {k : Nat}
    (σ : Finset (Fin 10) → Finset (Fin 10) → Fin 10)
    (A B : Finset (Fin 10))
    (h : aCheckFast pathEdges k σ A B = true) :
    aWin (SimpleGraph.pathGraph 10) k σ A B := by
  induction hcard : (free A B).card using Nat.strong_induction_on generalizing A B with
  | h m ih =>
      by_cases hfree : free A B = ∅
      · rw [aWin, dif_pos hfree]
        have hh := h
        rw [aCheckFast] at hh
        rw [dif_pos hfree] at hh
        rw [← path_discrepancy_eq_all A]
        exact of_decide_eq_true hh
      · by_cases hturn : A.card = B.card
        · have hh' := h
          rw [aCheckFast] at hh'
          rw [dif_neg hfree, if_pos hturn] at hh'
          have hw : σ A B ∈ free A B := by
            split at hh'
            · assumption
            · contradiction
          have hh := h
          rw [aCheckFast] at hh
          rw [dif_neg hfree, if_pos hturn, dif_pos hw] at hh
          rw [aWin, dif_neg hfree, if_pos hturn, dif_pos hw]
          have hlt : (free (insert (σ A B) A) B).card < m := by
            calc
              (free (insert (σ A B) A) B).card < (free A B).card := by
                rw [free_insert_eq_erase]
                exact Finset.card_erase_lt_of_mem hw
              _ = m := hcard
          exact ih _ hlt _ _ hh rfl
        · have hh := h
          rw [aCheckFast] at hh
          rw [dif_neg hfree, if_neg hturn] at hh
          rw [aWin, dif_neg hfree, if_neg hturn]
          intro v
          have hrec := (fold_and_true_iff _ _).mp hh v (Finset.mem_attach _ _)
          have hlt : (free A (insert v.1 B)).card < m := by
            calc
              (free A (insert v.1 B)).card < (free A B).card := by
                rw [show free A (insert v.1 B) = (free A B).erase v.1 by
                  ext x
                  by_cases hx : x = v.1 <;> simp [free, hx]]
                exact Finset.card_erase_lt_of_mem v.2
              _ = m := hcard
          exact ih _ hlt _ _ hrec rfl



private theorem witness_discrepancy_eq_all_row_0 : ∀ A : Finset (Fin 10),
    0 ∉ A → 1 ∉ A → 2 ∉ A → fastDiscrepancy witnessEdgesFast A = discrepancy witness A := by
  decide +kernel

private theorem witness_discrepancy_eq_all_row_1 : ∀ A : Finset (Fin 10),
    0 ∈ A → 1 ∉ A → 2 ∉ A → fastDiscrepancy witnessEdgesFast A = discrepancy witness A := by
  decide +kernel

private theorem witness_discrepancy_eq_all_row_2 : ∀ A : Finset (Fin 10),
    0 ∉ A → 1 ∈ A → 2 ∉ A → fastDiscrepancy witnessEdgesFast A = discrepancy witness A := by
  decide +kernel

private theorem witness_discrepancy_eq_all_row_3 : ∀ A : Finset (Fin 10),
    0 ∈ A → 1 ∈ A → 2 ∉ A → fastDiscrepancy witnessEdgesFast A = discrepancy witness A := by
  decide +kernel

private theorem witness_discrepancy_eq_all_row_4 : ∀ A : Finset (Fin 10),
    0 ∉ A → 1 ∉ A → 2 ∈ A → fastDiscrepancy witnessEdgesFast A = discrepancy witness A := by
  decide +kernel

private theorem witness_discrepancy_eq_all_row_5 : ∀ A : Finset (Fin 10),
    0 ∈ A → 1 ∉ A → 2 ∈ A → fastDiscrepancy witnessEdgesFast A = discrepancy witness A := by
  decide +kernel

private theorem witness_discrepancy_eq_all_row_6 : ∀ A : Finset (Fin 10),
    0 ∉ A → 1 ∈ A → 2 ∈ A → fastDiscrepancy witnessEdgesFast A = discrepancy witness A := by
  decide +kernel

private theorem witness_discrepancy_eq_all_row_7 : ∀ A : Finset (Fin 10),
    0 ∈ A → 1 ∈ A → 2 ∈ A → fastDiscrepancy witnessEdgesFast A = discrepancy witness A := by
  decide +kernel

private theorem witness_discrepancy_eq_all (A : Finset (Fin 10)) :
    fastDiscrepancy witnessEdgesFast A = discrepancy witness A := by
  by_cases hzero : (0 : Fin 10) ∈ A <;>
    by_cases hone : (1 : Fin 10) ∈ A <;>
      by_cases htwo : (2 : Fin 10) ∈ A
  · exact witness_discrepancy_eq_all_row_7 A hzero hone htwo
  · exact witness_discrepancy_eq_all_row_3 A hzero hone htwo
  · exact witness_discrepancy_eq_all_row_5 A hzero hone htwo
  · exact witness_discrepancy_eq_all_row_1 A hzero hone htwo
  · exact witness_discrepancy_eq_all_row_6 A hzero hone htwo
  · exact witness_discrepancy_eq_all_row_2 A hzero hone htwo
  · exact witness_discrepancy_eq_all_row_4 A hzero hone htwo
  · exact witness_discrepancy_eq_all_row_0 A hzero hone htwo



private def paired (A B : Finset (Fin 10)) : Prop := B = A.image partner

private lemma partner_involutive : ∀ v : Fin 10, partner (partner v) = v := by decide

private lemma partner_ne : ∀ v : Fin 10, partner v ≠ v := by decide

private lemma paired_card {A B : Finset (Fin 10)} (h : paired A B) : A.card = B.card := by
  subst B
  symm
  exact Finset.card_image_of_injective A (Function.Involutive.injective partner_involutive)

private lemma paired_partner_free {A B : Finset (Fin 10)} (hpair : paired A B)
    {v : Fin 10} (hv : v ∈ free A B) : partner v ∈ free (insert v A) B := by
  subst B
  have hv' : v ∉ A ∪ A.image partner := by
    simpa only [free, Finset.mem_sdiff, Finset.mem_univ, true_and] using hv
  have hvA : v ∉ A := by
    intro h
    exact hv' (by simp [h])
  have hvB : v ∉ A.image partner := by
    intro h
    exact hv' (by simp [h])
  have hnot_insert : partner v ∉ insert v A := by
    intro h
    simp only [Finset.mem_insert] at h
    rcases h with h | h
    · exact partner_ne v h
    · exact hvB (Finset.mem_image.mpr ⟨partner v, h, partner_involutive v⟩)
  have hnot_image : partner v ∉ A.image partner := by
    intro h
    rcases Finset.mem_image.mp h with ⟨a, ha, hae⟩
    apply hvA
    have hav : a = v := by
      apply (Function.Involutive.injective partner_involutive)
      simpa [partner_involutive] using hae
    exact hav ▸ ha
  change partner v ∈ (Finset.univ : Finset (Fin 10)) \ (insert v A ∪ A.image partner)
  rw [Finset.mem_sdiff]
  constructor
  · exact Finset.mem_univ _
  · intro h
    simp only [Finset.mem_union] at h
    rcases h with h | h
    · exact hnot_insert h
    · exact hnot_image h

private lemma paired_step {A B : Finset (Fin 10)} (hpair : paired A B)
    {v : Fin 10} (hv : v ∈ free A B) :
    paired (insert v A) (insert (partner v) B) := by
  subst B
  simp [paired, Finset.image_insert]

private lemma pairingValue_le_gameValue {A B : Finset (Fin 10)}
    (hpair : paired A B) :
    pairingValue witnessEdgesFast A B ≤ gameValue witness A B := by
  induction hcard : (free A B).card using Nat.strong_induction_on generalizing A B with
  | h m ih =>
      by_cases hfree : free A B = ∅
      · rw [pairingValue, dif_pos hfree, witness_discrepancy_eq_all A]
        apply gameValue_ge_of_iWin witness (discrepancy witness A) (fun _ _ => 0) A B
        rw [iWin, dif_pos hfree]
      · have hturn : A.card = B.card := paired_card hpair
        conv_rhs => rw [gameValue]
        rw [dif_neg hfree, if_pos hturn]
        apply Finset.le_min' _
        intro z hz
        rcases Finset.mem_image.mp hz with ⟨⟨v, hv⟩, _, rfl⟩
        have hvfree : v ∈ free A B := hv
        have hvfree' : v ∉ A ∧ v ∉ B := by
          simpa only [free, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union,
            true_and, not_or] using hvfree
        have hp : partner v ∈ free (insert v A) B := paired_partner_free hpair hvfree
        have hstep : paired (insert v A) (insert (partner v) B) :=
          paired_step hpair hvfree
        have hlt : (free (insert v A) (insert (partner v) B)).card < m := by
          have hsub : free (insert v A) (insert (partner v) B) ⊆
              (free A B).erase v := by
            intro x hx
            simp only [free, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_union,
              Finset.mem_insert, Finset.mem_univ] at hx ⊢
            rcases hx with ⟨_, hxnot⟩
            refine ⟨?_, True.intro, ?_⟩
            · intro hxeq
              apply hxnot
              simp [hxeq]
            · intro hxmem
              apply hxnot
              rcases hxmem with hxa | hxb <;> aesop
          calc
            (free (insert v A) (insert (partner v) B)).card ≤
                ((free A B).erase v).card := Finset.card_le_card hsub
            _ < (free A B).card := Finset.card_erase_lt_of_mem hvfree
            _ = m := hcard
        have hpv : pairingValue witnessEdgesFast (insert v A)
              (insert (partner v) B) ≤
            gameValue witness (insert v A) (insert (partner v) B) :=
          ih _ hlt hstep rfl
        calc
          pairingValue witnessEdgesFast A B ≤
              pairingValue witnessEdgesFast (insert v A) (insert (partner v) B) := by
                conv_lhs => rw [pairingValue]
                rw [dif_neg hfree]
                apply Finset.min'_le
                exact Finset.mem_image.mpr ⟨⟨v, hvfree⟩, Finset.mem_attach _ _, rfl⟩
          _ ≤ gameValue witness (insert v A) (insert (partner v) B) := hpv
          _ ≤ gameValue witness (insert v A) B := by
            have hfreechild : free (insert v A) B ≠ ∅ := by
              intro hzero
              rw [hzero] at hp
              exact (by simpa using hp)
            have hnot : v ∉ A := by
              intro hvin
              exact hvfree'.1 hvin
            have hcardneq : (insert v A).card ≠ B.card := by
              intro heq
              have : B.card + 1 = B.card := by
                simpa [Finset.card_insert_of_notMem hnot, hturn] using heq
              omega
            conv_rhs => rw [gameValue]
            rw [dif_neg hfreechild, if_neg hcardneq]
            apply Finset.le_max'
            exact Finset.mem_image.mpr ⟨⟨partner v, hp⟩, Finset.mem_attach _ _, rfl⟩


private theorem terminal_bound : ∀ A : Finset (Fin 10),
    free A (A.image partner) = ∅ →
    Disjoint A (A.image partner) →
    3 ≤ discrepancy witness A := by
  decide +kernel


private def pairedDisjoint (A B : Finset (Fin 10)) : Prop :=
  paired A B ∧ Disjoint A B

private lemma pairedDisjoint_step {A B : Finset (Fin 10)}
    (hpair : pairedDisjoint A B) {v : Fin 10} (hv : v ∈ free A B) :
    pairedDisjoint (insert v A) (insert (partner v) B) := by
  refine ⟨paired_step hpair.1 hv, ?_⟩
  have hvU : v ∉ A ∪ B := (Finset.mem_sdiff.mp hv).2
  have hp := paired_partner_free hpair.1 hv
  have hpU : partner v ∉ insert v A ∪ B := (Finset.mem_sdiff.mp hp).2
  apply Finset.disjoint_left.mpr
  intro x hxA hxB
  simp only [Finset.mem_insert] at hxA hxB
  rcases hxA with hxv | hxA
  · subst x
    rcases hxB with h | h
    · exact partner_ne v h.symm
    · exact hvU (by simp [h])
  · rcases hxB with h | h
    · apply hpU
      apply Finset.mem_union.mpr
      left
      simp only [Finset.mem_insert]
      exact Or.inr (by simpa [h] using hxA)
    · exact (Finset.disjoint_left.mp hpair.2) hxA h

private lemma pairingValue_ge_three {A B : Finset (Fin 10)}
    (hpair : pairedDisjoint A B) :
    3 ≤ pairingValue witnessEdgesFast A B := by
  induction hcard : (free A B).card using Nat.strong_induction_on generalizing A B with
  | h m ih =>
      by_cases hfree : free A B = ∅
      · have hrel : B = A.image partner := hpair.1
        subst B
        rw [pairingValue, dif_pos hfree]
        rw [witness_discrepancy_eq_all A]
        exact terminal_bound A hfree hpair.2
      · rw [pairingValue, dif_neg hfree]
        apply Finset.le_min' _
        intro z hz
        rcases Finset.mem_image.mp hz with ⟨⟨v, hv⟩, _, rfl⟩
        have hstep := pairedDisjoint_step hpair hv
        have hlt : (free (insert v A) (insert (partner v) B)).card < m := by
          have hsub : free (insert v A) (insert (partner v) B) ⊆
              (free A B).erase v := by
            intro x hx
            simp only [free, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_union,
              Finset.mem_insert, Finset.mem_univ] at hx ⊢
            rcases hx with ⟨_, hxnot⟩
            refine ⟨?_, True.intro, ?_⟩
            · intro hxeq
              apply hxnot
              simp [hxeq]
            · intro hxmem
              apply hxnot
              rcases hxmem with hxa | hxb <;> aesop
          calc
            (free (insert v A) (insert (partner v) B)).card ≤
                ((free A B).erase v).card := Finset.card_le_card hsub
            _ < (free A B).card := Finset.card_erase_lt_of_mem hv
            _ = m := hcard
        exact ih _ hlt hstep rfl


private theorem path_upper : cg (SimpleGraph.pathGraph 10) ≤ 1 := by
  apply gameValue_le_of_aWin (G := SimpleGraph.pathGraph 10) (k := 1) pathStrategy ∅ ∅
  exact aCheckFast_sound pathStrategy ∅ ∅ (by decide +kernel)


private lemma witness_connected : witness.Connected := by
  have w10 : witness.Walk 1 0 := SimpleGraph.Walk.cons (by decide) SimpleGraph.Walk.nil
  have w20 : witness.Walk 2 0 := SimpleGraph.Walk.cons (by decide) w10
  have w30 : witness.Walk 3 0 := SimpleGraph.Walk.cons (by decide) w20
  have w40 : witness.Walk 4 0 := SimpleGraph.Walk.cons (by decide) w30
  have w50 : witness.Walk 5 0 := SimpleGraph.Walk.cons (by decide) w40
  have w60 : witness.Walk 6 0 := SimpleGraph.Walk.cons (by decide) w50
  have w70 : witness.Walk 7 0 := SimpleGraph.Walk.cons (by decide) w60
  have w80 : witness.Walk 8 0 := SimpleGraph.Walk.cons (by decide) SimpleGraph.Walk.nil
  have w90 : witness.Walk 9 0 := SimpleGraph.Walk.cons (by decide) SimpleGraph.Walk.nil
  have to0 : ∀ u : Fin 10, witness.Reachable u 0 := by
    intro u
    fin_cases u
    · exact ⟨SimpleGraph.Walk.nil⟩
    · exact ⟨w10⟩
    · exact ⟨w20⟩
    · exact ⟨w30⟩
    · exact ⟨w40⟩
    · exact ⟨w50⟩
    · exact ⟨w60⟩
    · exact ⟨w70⟩
    · exact ⟨w80⟩
    · exact ⟨w90⟩
  refine SimpleGraph.Connected.mk ?_
  intro u v
  exact (to0 u).trans (to0 v).symm

private lemma witness_edge_card : Nat.card witness.edgeSet = 9 := by
  let _ : Fintype witness.edgeSet := SimpleGraph.fintypeEdgeSet witness
  rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
  decide



def claim : Prop := ∀ (n : Nat) (T : SimpleGraph (Fin n))
    [dT : DecidableRel T.Adj]
    [dP : DecidableRel (SimpleGraph.pathGraph n).Adj],
    T.IsTree → @cg n T dT ≤ @cg n (SimpleGraph.pathGraph n) dP

private theorem witness_isTree : witness.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨witness_connected, ?_⟩
  rw [witness_edge_card, Nat.card_fin]

private theorem witness_lower : 3 ≤ cg witness := by
  have hpv := pairingValue_ge_three (A := (∅ : Finset (Fin 10))) (B := ∅)
    ⟨by simp [paired], by simp⟩
  have hpg := pairingValue_le_gameValue (A := (∅ : Finset (Fin 10))) (B := ∅)
    (by simp [paired])
  exact le_trans hpv hpg

theorem result : ¬ claim := by
  classical
  intro h
  have hc := @h 10 witness inferInstance inferInstance witness_isTree
  have hl := witness_lower
  have hu := path_upper
  omega


end D5.S3.Combinatorics.Games.CordialityTreePathRefutation
