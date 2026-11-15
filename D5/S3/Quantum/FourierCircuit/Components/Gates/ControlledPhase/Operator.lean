/- GID: D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Operator
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Operator
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
Original file: QuantumAlg/Components/Gates/ControlledPhase/Operator.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Core.Base.WireAddress

import Mathlib.Init
public import D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary
import all D5.S3.Quantum.FourierCircuit.Util.Complex

/-!
# Mathematical addressed controlled phase

The original computational-basis operator fixes the phase on the selected
wire values independently of the native realization and its accounting.
It supplies the target for an actual default-model gate expansion.
-/

namespace QuantumAlg

noncomputable section

/-- Computational-basis phase contributed by one addressed controlled-phase
rotation.  The phase is present exactly when both addressed wires are set. -/
public def qftControlledPhaseFactor {n : Nat} (control target : Fin n)
    (angle : Real) (basis : Fin (2 ^ n)) : Complex :=
  if basis.val.testBit (WireAddress.bitIndex control).val &&
      basis.val.testBit (WireAddress.bitIndex target).val then
    Complex.exp (angle * Complex.I)
  else 1

/-- Certified addressed controlled-phase operator. -/
public def qftControlledPhaseOperator {n : Nat} (control target : Fin n)
    (angle : Real) : UnitaryOperator (Qubits n) :=
  UnitaryOperator.ofMatrix
    (Matrix.diagonal (qftControlledPhaseFactor control target angle)) (by
      rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      by_cases hij : i = j
      · subst j
        rw [Matrix.mul_apply, Matrix.one_apply, if_pos rfl]
        simp only [Matrix.star_apply]
        rw [Finset.sum_eq_single i]
        · simp only [Matrix.diagonal_apply_eq]
          by_cases hphase :
              i.val.testBit (WireAddress.bitIndex control).val &&
                i.val.testBit (WireAddress.bitIndex target).val
          · simp only [qftControlledPhaseFactor, hphase, if_pos]
            change Complex.exp ((angle : Complex) * Complex.I) *
                starRingEnd Complex
                  (Complex.exp ((angle : Complex) * Complex.I)) = 1
            rw [conj_exp_I, exp_I_mul_exp_neg_I]
          · simp [qftControlledPhaseFactor, hphase]
        · intro k _ hki
          rw [Matrix.diagonal_apply_ne _ (Ne.symm hki), zero_mul]
        · simp
      · rw [Matrix.mul_apply, Matrix.one_apply, if_neg hij]
        simp only [Matrix.star_apply]
        apply Finset.sum_eq_zero
        intro k _
        by_cases hik : i = k
        · subst k
          rw [Matrix.diagonal_apply_eq,
            Matrix.diagonal_apply_ne _ (Ne.symm hij)]
          simp
        · rw [Matrix.diagonal_apply_ne _ hik, zero_mul])

end

end QuantumAlg
