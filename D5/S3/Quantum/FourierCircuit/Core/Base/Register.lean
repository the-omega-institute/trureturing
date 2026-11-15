/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/Register
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/Register
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
Original file: QuantumAlg/Core/Base/Register.lean.
Authors: QudeLeap Team
-/

module

import Mathlib.Init
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.PNat.Defs

/-!
# Finite quantum registers

`Register` is the finite-dimensional basis interface shared by states, gates,
operators, measurements, and circuits.  `Qubits n` is the specialization whose
basis labels are the current big-endian `Fin (2^n)` computational basis.
-/

section

namespace QuantumAlg

/-- A finite-dimensional quantum register. -/
public structure Register where
  /-- Basis labels for the register. -/
  Index : Type
  /-- The basis is finite. -/
  fintype : Fintype Index
  /-- Basis labels have decidable equality. -/
  decEq : DecidableEq Index

attribute [instance] Register.fintype Register.decEq

namespace Register

/-- Product/tensor register. -/
@[expose, implicit_reducible]
public def prod (left right : Register) : Register := by
  letI : Fintype left.Index := left.fintype
  letI : DecidableEq left.Index := left.decEq
  letI : Fintype right.Index := right.fintype
  letI : DecidableEq right.Index := right.decEq
  exact
    { Index := left.Index × right.Index
      fintype := inferInstance
      decEq := inferInstance }

/-- The explicit product type is canonically equivalent to the index type of
the product register. -/
@[expose]
public def prodIndexEquiv (left right : Register) :
    left.Index × right.Index ≃ (prod left right).Index := by
  unfold prod
  exact Equiv.refl _

end Register


/-- The `n`-qubit register with big-endian computational basis labels. -/
public abbrev Qubits (n : Nat) : Register where
  Index := Fin (2 ^ n)
  fintype := inferInstance
  decEq := inferInstance

end QuantumAlg

end
