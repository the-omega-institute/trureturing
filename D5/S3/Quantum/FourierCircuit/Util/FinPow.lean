/- GID: D5/S3/Quantum/FourierCircuit/Util/FinPow
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Util/FinPow
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
Original file: QuantumAlg/Util/FinPow.lean.
Authors: QudeLeap Team
-/

module

import Mathlib.Init
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.SuccPred
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# Index plumbing for `Fin (2 ^ n)` registers (quantum-free)

The big-endian pairing of computational-basis labels used to compose qubit
registers, factored out of the quantum framework so it carries no dependency
on `Gate`/`PureState`.

## Main definition

- `QuantumAlg.prodEquiv` — `Fin (2 ^ m) × Fin (2 ^ n) ≃ Fin (2 ^ (m + n))`,
  `(x, y) ↦ y + 2 ^ n * x`, so the first (lower-qubit-index) factor carries
  the most significant bits.

Pinned Mathlib API: `finProdFinEquiv` (`(x, y) ↦ y + n * x`), `finCongr`.
-/

section

namespace QuantumAlg

variable {m n : ℕ}

/-- Big-endian pairing of basis labels: `(x, y) ↦ y + 2 ^ n * x`, so the
first (lower-qubit-index) factor carries the most significant bits. -/
@[expose] public def prodEquiv : Fin (2 ^ m) × Fin (2 ^ n) ≃ Fin (2 ^ (m + n)) :=
  finProdFinEquiv.trans (finCongr (pow_add (2 : ℕ) m n).symm)


/-! ## Bit reconstruction helpers -/

/-- Reconstructing a natural number from `n + 1` little-endian bits can be
split into the lower `n` bits plus the final most-significant bit. -/
lemma nat_ofBits_succ_last {n : ℕ} (f : Fin (n + 1) → Bool) :
    Nat.ofBits f =
      Nat.ofBits (f ∘ Fin.castSucc) +
        2 ^ n * (f (Fin.last n)).toNat := by
  induction n with
  | zero =>
      rw [Nat.ofBits_succ]
      simp
  | succ n ih =>
      rw [Nat.ofBits_succ]
      rw [ih (f ∘ Fin.succ)]
      rw [Nat.ofBits_succ]
      have hcomp :
          (f ∘ Fin.succ) ∘ Fin.castSucc =
            (f ∘ Fin.castSucc) ∘ Fin.succ := by
        funext i
        rfl
      rw [hcomp]
      simp [Fin.succ_last, Nat.pow_succ, Nat.mul_add, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm]


end QuantumAlg

end
