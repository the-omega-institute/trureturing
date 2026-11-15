/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum
   mirror-E: none(waiver:source-transfer-proof)
   anchors: []
   utility: none
   digest: Licensed original QFT circuit proof support. -/

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0; the full license is in
Library/Quantum/qudeleap2026qft.md.
Modified for receiver module paths and the retained QFT proof slice.
Source: QudeLeap/Lean-QuantumAlg@971dc8be8a153a116b6d7cd748f984d545861b00.
Original file: QuantumAlg/Core/Base/Layout/Quantum.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Core.Base.Register
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Count

/-!
# Finite-dimensional quantum layouts

A wire has one physical identity and one positive dimension. A layout is an
ordered collection of wires with distinct identities, even when dimensions
differ. Its register basis is the dependent product of the individual wire
bases. Space counts retain the dimension of each physical system; the Hilbert
dimension does not determine a qubit count.
-/

section

namespace QuantumAlg

open scoped BigOperators

/-- One physical quantum system and its finite computational-basis dimension. -/
public structure QuantumWire where
  /-- Physical identity, independent of the system's dimension. -/
  identity : Nat
  /-- A system has a nonempty finite computational basis. -/
  dimension : ℕ+
deriving DecidableEq
ght
  simp_all

/-- Ordered finite quantum systems with an injective physical placement. -/
public structure QuantumLayout (systemCount : Nat) where
  /-- The actual physical system at each logical position. -/
  wire : Fin systemCount → QuantumWire
  /-- One physical identity cannot occupy two logical positions. -/
  identityInjective : Function.Injective (fun index => (wire index).identity)

namespace QuantumLayout
st rightWire
          rfl

  List.ofFn layout.wire
 index).identity
ndex).dimension
QuantumLayout systemCount) : layout.wires.length = systemCount := by
  simp [wires]
umLayout systemCount) : layout.identities.length = systemCount := by
  simp [identities]
umLayout systemCount) : layout.dimensions.length = systemCount := by
  simp [dimensions]
Fn.mpr layout.identityInjective
jective sameIdentity
comp', List.ofFn_get]
    exact distinct
stinct).wires = wireList :=
  List.ofFn_get wireList
fWires wireList distinct)
  else none
.map QuantumWire.identity).Nodup <;>
    simp [tryOfWires, distinct]
entity, leftDimension⟩, ⟨identity, rightDimension⟩] = none := by
  simp [tryOfWires]

/-- Computational-basis labels record one finite value for every physical wire. -/
public abbrev Basis {systemCount : Nat} (layout : QuantumLayout systemCount) :=
  (index : Fin systemCount) → Fin (layout.wire index).dimension

/-- The register is derived from the physical systems and their dimensions. -/
@[expose, implicit_reducible]
public def register {systemCount : Nat} (layout : QuantumLayout systemCount) : Register where
  Index := layout.Basis
  fintype := inferInstance
  decEq := inferInstance
antumLayout systemCount) : layout.Basis :=
  fun index => ⟨0, (layout.wire index).dimension.pos⟩
(layout : QuantumLayout systemCount) : Nat :=
  ∏ index, ((layout.wire index).dimension : Nat)
i, Fintype.card_fin, basisCardinality]
out.dimensions.count dimension
y index, dimension⟩
  identityInjective := distinct
unt := by
  simp [basisCardinality, uniform]
.ofFn_const, List.count_replicate, equal]
g
      left.identities_nodup.append right.identities_nodup disjoint
t.wires ++ right.wires := by
  simp [wires, append, List.ofFn_fin_append]
[List.ofFn_comp', List.ofFn_fin_append, List.map_append, List.map_ofFn, List.map_ofFn]
  rfl
t.dimensionCount dimension := by
  simp [dimensionCount, dimensions_append]

end QuantumLayout

end QuantumAlg

end
