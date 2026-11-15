/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement
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
Original file: QuantumAlg/Core/Base/UnitaryCircuit/Placement.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Realization.Placement
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Realization.Placement
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Physical
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum.Relabeling
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum.Embedding.Operator
import Mathlib.Logic.Equiv.Fintype

/-!
# Placing a complete native word at dimension-correct positions

The selected positions determine the physical addresses of every actual gate
and query in the construction. A finite injective address assignment extends
to a permutation of addresses; only the original wires occur in the relocated
word. Embedding then leaves every unselected ambient system unchanged.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

variable {gates : GateModel} {oracles : OracleModel}
variable {small large : Nat} (source : QuantumLayout small) (target : QuantumLayout large)
variable (position : Fin small ↪ Fin large)
variable (dimensions : ∀ index,
  (source.wire index).dimension = (target.wire (position index)).dimension)

private def addressPermutation : Equiv.Perm Nat :=
  Classical.choose (Equiv.Perm.exists_extending_pair
    (fun index => (source.wire index).identity)
    (fun index => (target.wire (position index)).identity)
    source.identityInjective (target.identityInjective.comp position.injective))

private lemma addressPermutation_apply (index : Fin small) :
    addressPermutation source target position (source.wire index).identity =
      (target.wire (position index)).identity :=
  Classical.choose_spec (Equiv.Perm.exists_extending_pair
    (fun index => (source.wire index).identity)
    (fun index => (target.wire (position index)).identity)
    source.identityInjective (target.identityInjective.comp position.injective)) index

private def relocatedPlacement :
    QuantumLayout.Embedding
      (source.relabel (addressPermutation source target position).toEmbedding) target where
  position := position
  wire_eq index := by
    symm
    have identities := addressPermutation_apply source target position index
    have sizes := dimensions index
    change QuantumWire.relabel _ (source.wire index) = target.wire (position index)
    cases first : source.wire index with
    | mk firstIdentity firstDimension =>
      cases second : target.wire (position index) with
      | mk secondIdentity secondDimension =>
        simp only [first, second] at identities sizes
        change QuantumWire.mk (addressPermutation source target position firstIdentity)
          firstDimension = QuantumWire.mk secondIdentity secondDimension
        rw [identities, sizes]

/-- Extend the independent source operator by identity at the selected physical positions. -/
public def operatorAt (operator : UnitaryOperator source.register) :
    UnitaryOperator target.register :=
  (relocatedPlacement source target position dimensions).liftOperator
    (UnitaryOperator.reindex
      (QuantumLayout.relabelBasis source
        (addressPermutation source target position).toEmbedding) operator)


/-- Relocate and embed the actual native construction at the selected dimension-correct wires. -/
public def placeAt (body : UnitaryCircuit gates oracles source) :
    UnitaryCircuit gates oracles target :=
  (body.relabel (addressPermutation source target position).toEmbedding).embed
    (relocatedPlacement source target position dimensions)

/-- Placement preserves the full operator, including phase and all spectator coherences. -/
public lemma placeAt_matrix (body : UnitaryCircuit gates oracles source) (environment :
  oracles.Interpretation) :
    ((placeAt source target position dimensions body).matrix environment) =
      operatorAt source target position dimensions (body.matrix environment) := by
  rw [placeAt, embed_matrix, relabel_matrix]
  rfl


/-- Physical placement retains the exact native occurrence order. -/
public lemma placeAt_eventTrace (body : UnitaryCircuit gates oracles source) :
    (placeAt source target position dimensions body).eventTrace = body.eventTrace := by
  rw [placeAt, embed_eventTrace, relabel_eventTrace]


end

end QuantumAlg.UnitaryCircuit
