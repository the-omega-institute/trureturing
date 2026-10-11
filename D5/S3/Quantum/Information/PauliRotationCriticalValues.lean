/- GID: D5/S3/Quantum/Information/PauliRotationCriticalValues
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/PauliRotationCriticalValues
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/PauliRotationCriticalValues.claim; result=D5/S3/Quantum/Information/PauliRotationCriticalValues.result; claim=D5/S3/Quantum/Information/PauliRotationCriticalValues.claim
   digest: Two-qubit Pauli rotation circuits and their critical-value Hausdorff dimension. -/

import D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.MetricSpace.HausdorffDimension

set_option linter.style.longLine false

open MeasureTheory
open scoped Matrix.Norms.Frobenius ENNReal

namespace D5.S3.Quantum.Information.PauliRotationCriticalValues

open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
  (Pauli wordOp)

abbrev BasisState := Fin 2 → Fin 2
abbrev Mat := Matrix BasisState BasisState ℂ
abbrev Param := Fin 15 → ℝ
abbrev NonIdentityPauli :=
  {p : Fin 2 → Pauli // p ≠ (fun _ => Pauli.I)}

noncomputable def rotation (p : NonIdentityPauli) (a : ℝ) : Mat :=
  Real.cos (a / 2) • (1 : Mat) -
    Real.sin (a / 2) • (Complex.I • wordOp p.val)

noncomputable def circuit (P : Fin 15 → NonIdentityPauli)
    (α : Param) : Mat :=
  (List.ofFn (fun j : Fin 15 => rotation (P j) (α j))).prod

noncomputable def derivativeRank (P : Fin 15 → NonIdentityPauli)
    (α : Param) : ℕ :=
  Module.finrank ℝ
    (LinearMap.range ((fderiv ℝ (circuit P) α).toLinearMap))

def critical (P : Fin 15 → NonIdentityPauli) : Set Param :=
  {α | derivativeRank P α < 15}

def claim : Prop :=
  ∀ P : Fin 15 → NonIdentityPauli,
    (∀ᵐ α ∂(volume : Measure Param), derivativeRank P α = 15) →
      dimH (circuit P '' critical P) ≤ (13 : ℝ≥0∞)

end D5.S3.Quantum.Information.PauliRotationCriticalValues
