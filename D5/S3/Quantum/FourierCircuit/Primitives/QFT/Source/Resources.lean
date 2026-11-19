/- GID: D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Resources
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Resources
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
Original file: QuantumAlg/Primitives/QFT/Source/Resources.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source
import all D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source
import all D5.S3.Quantum.FourierCircuit.Primitives.QFT.Primitive
import all D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source.Primitive
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Placement
import all D5.S3.Quantum.FourierCircuit.Core.Base.Accounting.ResourcePool
import Mathlib.Data.Nat.Choose.Basic

/-!
# Native event counts of the recursive QFT word

Each count is a projection of the actual native source construction. Every
other event coordinate has zero occurrences.
-/

namespace QuantumAlg.QuantumFourierTransform.Source

noncomputable section

variable (oracles : OracleModel)
variable (event : Resource.Event (.quantum FourierGate.model oracles))

private lemma phaseStep_count (n : Nat) (offset : Fin n) :
    ResourcePool.count event (phaseStep oracles n offset).eventCost =
      if .gate .controlledPhase = event then 1 else 0 := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost]
  change ResourcePool.count event (ResourcePool.ofList [.gate .controlledPhase]) = _
  simp

private lemma phasePrefix_count (n count : Nat) (bounded : count ≤ n) :
    ResourcePool.count event (phasePrefix oracles n count bounded).eventCost =
      count * (if .gate .controlledPhase = event then 1 else 0) := by
  induction count with
  | zero => simp [phasePrefix]
  | succ count ih =>
      rw [phasePrefix, UnitaryCircuit.seq_eventCost, ResourcePool.count_add, ih,
        phaseStep_count]
      ring

private lemma leadingHadamard_count (n : Nat) :
    ResourcePool.count event (leadingHadamard oracles n).eventCost =
      if .gate .hadamard = event then 1 else 0 := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost]
  change ResourcePool.count event (ResourcePool.ofList [.gate .hadamard]) = _
  rw [ResourcePool.count_ofList]
  simp only [List.count_cons, List.count_nil, beq_iff_eq, Nat.zero_add]

private lemma tailLayer_count (n : Nat)
    (body : UnitaryCircuit FourierGate.model oracles (QFTPrimitive.layout n)) :
    ResourcePool.count event (tailLayer oracles n body).eventCost =
      ResourcePool.count event body.eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    ← UnitaryCircuit.ofList_eventTrace_eq_eventCost body]
  rw [tailLayer, UnitaryCircuit.placeAt_eventTrace]

private lemma noSwap_count (n : Nat) :
    ResourcePool.count event (noSwap oracles n).eventCost =
      n * (if .gate .hadamard = event then 1 else 0) +
        n.choose 2 * (if .gate .controlledPhase = event then 1 else 0) := by
  induction n with
  | zero => simp [noSwap]
  | succ n ih =>
      rw [noSwap, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
        UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
        leadingHadamard_count, phaseLayer, phasePrefix_count, tailLayer_count, ih]
      simp only [Nat.choose_succ_succ, Nat.choose_one_right]
      ring

private lemma reversePrefix_count (n count : Nat) (bounded : count ≤ n / 2) :
    ResourcePool.count event (reversePrefix oracles n count bounded).eventCost =
      count * (if .gate .swap = event then 1 else 0) := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, reversePrefix_eventTrace]
  by_cases same : Resource.Event.gate
      (model := .quantum FourierGate.model oracles) .swap = event <;>
    simp [ResourcePool.count_ofList, List.count_replicate, same]

/-- The three exact source counts come from actual native instruction occurrences. -/
public lemma qftSource_circuit_event_count (n : Nat) :
    ResourcePool.count event (circuit oracles n).eventCost =
      n * (if .gate .hadamard = event then 1 else 0) +
        n.choose 2 * (if .gate .controlledPhase = event then 1 else 0) +
          (n / 2) * (if .gate .swap = event then 1 else 0) := by
  rw [circuit, UnitaryCircuit.seq_eventCost, ResourcePool.count_add, noSwap_count,
    bitReverse, reversePrefix_count]


end
end QuantumAlg.QuantumFourierTransform.Source
