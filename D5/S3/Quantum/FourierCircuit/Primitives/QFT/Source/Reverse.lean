/- GID: D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse
   mirror-E: none(waiver:source-transfer-proof)
   anchors: []
   utility: none
   digest: Licensed original QFT circuit proof support. -/

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0; the full license is in
Library/Fourier/qudeleap2026qft.md.
Modified for receiver module paths and the retained QFT proof slice.
Source: QudeLeap/Lean-QuantumAlg@971dc8be8a153a116b6d7cd748f984d545861b00.
Original file: QuantumAlg/Primitives/QFT/Source/Reverse.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source.Reverse.Layout
import all D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source.Reverse.Layout
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum.Embedding.Composition
import all D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source.Primitive
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Realization.Placement
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit

/-!
# One actual parallel layer of symmetric Fourier swaps

Each member is the original native SWAP on its own two physical wires. The
prefix and the next pair have disjoint embeddings in their union. Embedding
the complete layer into the bank retains every spectator, including the
middle wire at odd width, without adding a gate or a dependency.
-/

namespace QuantumAlg.QuantumFourierTransform.Source

noncomputable section

open QFTPrimitive (layout)

/-- One native SWAP exchanging the selected symmetric pair. -/
public def swapStep (oracles : OracleModel) (n : Nat) (index : Fin (n / 2)) :
    UnitaryCircuit FourierGate.model oracles (layout n) :=
  (QFTPrimitive.swap (swapLeft n index) (swapRight n index)
    (swap_distinct n index)).sourceCircuit oracles

namespace ReverseLayout

private def identityPlacement {count : Nat} (physical : QuantumLayout count) :
    QuantumLayout.Embedding physical physical where
  position := Function.Embedding.refl _
  wire_eq _ := rfl

/-- Execute the exact same occurrence on only its own two physical systems. -/
def localSwap (oracles : OracleModel) (n : Nat) (index : Fin (n / 2)) :
    UnitaryCircuit FourierGate.model oracles (pair n index) :=
  .native { occurrence := (application n index).occurrence
            embedding := identityPlacement (pair n index) }

private lemma localSwap_matrix (oracles : OracleModel) (n : Nat)
    (index : Fin (n / 2))
    (environment : oracles.Interpretation) :
    ((localSwap oracles n index).matrix environment) = (application n index).occurrence.operator
      := by
  change (identityPlacement (pair n index)).liftOperator
    (application n index).occurrence.operator = (application n index).occurrence.operator
  apply Subtype.ext
  ext row column
  refine (QuantumLayout.Embedding.liftOperator_entry_of_surjective
    (identityPlacement (pair n index)) Function.surjective_id
    (application n index).occurrence.operator row column).trans ?_
  congr 1

/-- Grow the real disjoint SWAP layer inside exactly its active physical subsystem. -/
def word (oracles : OracleModel) (n : Nat) :
    (count : Nat) → (bounded : count ≤ n / 2) →
      UnitaryCircuit FourierGate.model oracles (subsystem n count bounded)
  | 0, _ => .identity FourierGate.model oracles _
  | count + 1, bounded =>
      .parallel (word oracles n count (Nat.le_of_succ_le bounded))
        (localSwap oracles n ⟨count, Nat.lt_of_succ_le bounded⟩)
        (earlier n count bounded) (next n count bounded) (disjoint n count bounded)

lemma word_eventTrace (oracles : OracleModel) (n count : Nat)
    (bounded : count ≤ n / 2) :
    (word oracles n count bounded).eventTrace =
      List.replicate count
        (Resource.Event.gate (model := .quantum FourierGate.model oracles) .swap) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change (word oracles n count _).eventTrace ++ [.gate .swap] = _
      rw [ih, List.replicate_add]
      rfl

end ReverseLayout

/-- The first supplied symmetric pairs execute as one disjoint native layer. -/
public def reversePrefix (oracles : OracleModel) (n count : Nat) (bounded : count ≤ n / 2) :
    UnitaryCircuit FourierGate.model oracles (layout n) :=
  (ReverseLayout.word oracles n count bounded).embed (ReverseLayout.complete n count bounded)

/-- A zero-pair prefix is exactly identity on the complete bank. -/
lemma reversePrefix_zero_matrix (oracles : OracleModel) (n : Nat)
    (bounded : 0 ≤ n / 2)
    (environment : oracles.Interpretation) :
    ((reversePrefix oracles n 0 bounded).matrix environment) = 1 := by
  rw [reversePrefix, UnitaryCircuit.embed_matrix, ReverseLayout.word,
    UnitaryCircuit.identity_matrix, QuantumLayout.Embedding.embedding_liftOperator_one]

/-- The parallel extension has the same full operator order as the next symmetric swap. -/
lemma reversePrefix_succ_matrix (oracles : OracleModel) (n count : Nat)
    (bounded : count + 1 ≤ n / 2)
    (environment : oracles.Interpretation) :
    ((reversePrefix oracles n (count + 1) bounded).matrix environment) =
      ((swapStep oracles n ⟨count, Nat.lt_of_succ_le bounded⟩).matrix environment) *
        ((reversePrefix oracles n count (Nat.le_of_succ_le bounded)).matrix environment) := by
  rw [reversePrefix, UnitaryCircuit.embed_matrix, ReverseLayout.word,
    UnitaryCircuit.parallel_matrix_raw, QuantumLayout.Embedding.embedding_lift_mul,
    QuantumLayout.Embedding.embedding_lift_compose, QuantumLayout.Embedding.embedding_lift_compose,
    ReverseLayout.next_complete, ReverseLayout.earlier_complete,
    ReverseLayout.localSwap_matrix (environment := environment)]
  rfl

/-- Every symmetric SWAP remains present in the actual event traversal. -/
lemma reversePrefix_eventTrace (oracles : OracleModel) (n count : Nat)
    (bounded : count ≤ n / 2) :
    (reversePrefix oracles n count bounded).eventTrace =
      List.replicate count
        (Resource.Event.gate (model := .quantum FourierGate.model oracles) .swap) := by
  rw [reversePrefix, UnitaryCircuit.embed_eventTrace, ReverseLayout.word_eventTrace]

/-- The complete symmetric reversal is one parallel layer on the original bank. -/
public def bitReverse (oracles : OracleModel) (n : Nat) :
    UnitaryCircuit FourierGate.model oracles (layout n) :=
  reversePrefix oracles n (n / 2) le_rfl

end

end QuantumAlg.QuantumFourierTransform.Source
