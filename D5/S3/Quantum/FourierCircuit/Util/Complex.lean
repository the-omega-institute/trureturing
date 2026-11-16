/- GID: D5/S3/Quantum/FourierCircuit/Util/Complex
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Util/Complex
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
Original file: QuantumAlg/Util/Complex.lean.
Authors: QudeLeap Team
-/

module

import Mathlib.Init
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace QuantumAlg
open Complex

lemma conj_exp_I (φ : ℝ) :
    starRingEnd ℂ (Complex.exp (φ * Complex.I)) =
      Complex.exp (-(φ * Complex.I)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp

lemma exp_I_mul_exp_neg_I (φ : ℝ) :
    Complex.exp (φ * Complex.I) * Complex.exp (-(φ * Complex.I)) = 1 := by
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
end QuantumAlg
