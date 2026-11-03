/- GID: D5/S3/Quantum/Measurements/DetectorSensorStrictAveragingRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurements/DetectorSensorStrictAveragingRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurements/DetectorSensorStrictAveragingRefutation.claim; result=D5/S3/Quantum/Measurements/DetectorSensorStrictAveragingRefutation.result; claim=D5/S3/Quantum/Measurements/DetectorSensorStrictAveragingRefutation.claim
   digest: Two optimal three-sensor layers refute strict improvement by averaging. -/

import D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality

noncomputable section

open scoped BigOperators
open D5.S3.Quantum.Entanglement.TriangleIndependentSourceNoise
open D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality

namespace D5.S3.Quantum.Measurements.DetectorSensorStrictAveragingRefutation

def optSuccess {n : ℕ} (θ : ℝ) (ψ : (Fin n → Bool) → ℂ) : ℝ :=
  ⨆ M : LocalPOVM (Fin n → Bool) (Fin n), isoSuccess θ ψ M

def errorProb {n : ℕ} (θ : ℝ) (ψ : (Fin n → Bool) → ℂ) : ℝ :=
  1 - optSuccess θ ψ

def average {n : ℕ} (ψ ψ' : (Fin n → Bool) → ℂ) :
    (Fin n → Bool) → ℂ :=
  fun x => (Real.sqrt ((Complex.normSq (ψ x) + Complex.normSq (ψ' x)) / 2) : ℂ)

def claim : Prop :=
  ∀ n : ℕ, ∀ θ : ℝ, 0 < θ → θ < Real.pi →
  ∀ ψ ψ' : (Fin n → Bool) → ℂ,
    ∑ x, Complex.normSq (ψ x) = 1 →
    ∑ x, Complex.normSq (ψ' x) = 1 →
    (∃ x, Complex.normSq (ψ x) ≠ Complex.normSq (ψ' x)) →
    errorProb θ ψ = errorProb θ ψ' →
    errorProb θ (average ψ ψ') < errorProb θ ψ'

private def layer (l : ℕ) : (Fin 3 → Bool) → ℂ :=
  fun x => if (Finset.univ.filter (fun j => x j = true)).card = l then
    (Real.sqrt (1 / (3.choose l : ℝ)) : ℂ) else 0

private theorem layer_squares (l : ℕ) (x : Fin 3 → Bool) :
    Complex.normSq (layer l x) =
      if (Finset.univ.filter (fun j => x j = true)).card = l then
        1 / (3.choose l : ℝ) else 0 := by
  sorry

private theorem threshold_value : T 3 = Real.pi / 3 := by
  sorry

private theorem angle_admissible : 0 < Real.pi / 4 ∧ Real.pi / 4 ≤ T 3 := by
  sorry

private theorem counts (k : Fin 4) :
    rCount 3 0 1 k = 1 ∧
    lCount 3 0 1 k = if k = 1 ∨ k = 2 then 2 else 0 := by
  sorry

private theorem layer_minimizes (l : ℕ) (hl : l = 1 ∨ l = 2) :
    IsMinOn (fun k : ℕ =>
      ((rCount 3 0 1 k : ℝ) + Real.cos (2 * (Real.pi / 4)) * lCount 3 0 1 k) /
        ((rCount 3 0 1 k : ℝ) + lCount 3 0 1 k)) (Set.Iic 3) l := by
  sorry

private theorem different_layers :
    ∃ x, Complex.normSq (layer 1 x) ≠ Complex.normSq (layer 2 x) := by
  sorry

private theorem povm_nonempty : Nonempty (LocalPOVM (Fin 3 → Bool) (Fin 3)) := by
  sorry

private theorem bounded_success (ψ : (Fin 3 → Bool) → ℂ)
    (hψ : ∑ x, Complex.normSq (ψ x) = 1) :
    BddAbove (Set.range (isoSuccess (Real.pi / 4) ψ)) := by
  sorry

private theorem layer_optimal (l : ℕ) (hl : l = 1 ∨ l = 2)
    (ψ : (Fin 3 → Bool) → ℂ) (hψ : ∑ x, Complex.normSq (ψ x) = 1)
    (M : LocalPOVM (Fin 3 → Bool) (Fin 3)) :
    ∃ M' : LocalPOVM (Fin 3 → Bool) (Fin 3),
      isoSuccess (Real.pi / 4) ψ M ≤ isoSuccess (Real.pi / 4) (layer l) M' := by
  sorry

private theorem optimal_sup (l : ℕ) (hl : l = 1 ∨ l = 2)
    (ψ : (Fin 3 → Bool) → ℂ) (hψ : ∑ x, Complex.normSq (ψ x) = 1) :
    optSuccess (Real.pi / 4) ψ ≤ optSuccess (Real.pi / 4) (layer l) := by
  sorry

private theorem average_normalized {n : ℕ} (ψ ψ' : (Fin n → Bool) → ℂ)
    (hψ : ∑ x, Complex.normSq (ψ x) = 1)
    (hψ' : ∑ x, Complex.normSq (ψ' x) = 1) :
    ∑ x, Complex.normSq (average ψ ψ' x) = 1 := by
  sorry

private theorem equal_error :
    errorProb (Real.pi / 4) (layer 1) = errorProb (Real.pi / 4) (layer 2) := by
  sorry

private theorem average_no_improvement :
    errorProb (Real.pi / 4) (layer 2) ≤
      errorProb (Real.pi / 4) (average (layer 1) (layer 2)) := by
  sorry

theorem result : ¬ claim := by
  intro h
  exact (not_lt_of_ge average_no_improvement)
    (h 3 (Real.pi / 4) angle_admissible.1 (by linarith [Real.pi_pos])
      (layer 1) (layer 2)
      (dicke_normalized 1 (by decide) (layer 1) (layer_squares 1))
      (dicke_normalized 2 (by decide) (layer 2) (layer_squares 2))
      different_layers equal_error)

end D5.S3.Quantum.Measurements.DetectorSensorStrictAveragingRefutation
