/- GID: D5/S3/Quantum/Measurements/DetectorSensorStrictAveragingRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurements/DetectorSensorStrictAveragingRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurements/DetectorSensorStrictAveragingRefutation.claim; result=D5/S3/Quantum/Measurements/DetectorSensorStrictAveragingRefutation.result; claim=D5/S3/Quantum/Measurements/DetectorSensorStrictAveragingRefutation.claim
   digest: Two optimal three-sensor layers refute strict improvement by averaging. -/

import D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality
import D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance

/-!
# Strict averaging fails for optimal detector-sensor probes

The uniform weight-one and weight-two probes on three sensors both minimize error at
angle π/4. Their coefficient squares differ, while global optimality prevents their
coefficient-square average from having strictly smaller error.
-/

noncomputable section

open scoped BigOperators ComplexOrder Matrix
open D5.S3.Quantum.Entanglement.TriangleIndependentSourceNoise
open D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality
open D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance (dickeCoefficient)

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
  fun x => dickeCoefficient 3 (Finset.univ.filter (fun j => x j = true)).card l

private theorem layer_squares (l : ℕ) (x : Fin 3 → Bool) :
    Complex.normSq (layer l x) =
      if (Finset.univ.filter (fun j => x j = true)).card = l then
        1 / ((3 : ℕ).choose l : ℝ) else 0 := by
  classical
  dsimp only [layer, dickeCoefficient]
  split_ifs
  · rw [Complex.normSq_inv, Complex.normSq_ofReal,
      Real.mul_self_sqrt (Nat.cast_nonneg _), one_div]
  · exact Complex.normSq_zero

private theorem threshold_value : T 3 = Real.pi / 3 := by
  have hc : Real.arccos (1 / 2 : ℝ) = Real.pi / 3 := by
    rw [← Real.cos_pi_div_three]
    exact Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])
  change Real.arccos (-(((2 : ℝ) - 1) / 2)) / 2 = Real.pi / 3
  norm_num only
  rw [Real.arccos_neg, hc]
  ring

private theorem angle_admissible : 0 < Real.pi / 4 ∧ Real.pi / 4 ≤ T 3 := by
  rw [threshold_value]
  constructor <;> linarith [Real.pi_pos]

private theorem counts (k : ℕ) (hk : k ≤ 3) :
    rCount 3 0 1 k = 1 ∧
    lCount 3 0 1 k = if k = 1 ∨ k = 2 then 2 else 0 := by
  have hp := pair_count_product 3 (0 : Fin 3) 1 (by decide) k
  have ht := counts_partition 3 (0 : Fin 3) 1 k
  interval_cases k <;> norm_num at hp ht ⊢ <;> omega

private theorem layer_minimizes (l : ℕ) (hl : l = 1 ∨ l = 2) :
    IsMinOn (fun k : ℕ =>
      ((rCount 3 0 1 k : ℝ) + Real.cos (2 * (Real.pi / 4)) * lCount 3 0 1 k) /
        ((rCount 3 0 1 k : ℝ) + lCount 3 0 1 k)) (Set.Iic 3) l := by
  rcases hl with rfl | rfl <;> intro k hk <;>
    have hk' : k ≤ 3 := hk <;> interval_cases k <;>
    norm_num [show 2 * (Real.pi / 4) = Real.pi / 2 by ring,
      Real.cos_pi_div_two,
      (counts 0 (by decide)).1, (counts 0 (by decide)).2,
      (counts 1 (by decide)).1, (counts 1 (by decide)).2,
      (counts 2 (by decide)).1, (counts 2 (by decide)).2,
      (counts 3 (by decide)).1, (counts 3 (by decide)).2]

private theorem different_layers :
    ∃ x, Complex.normSq (layer 1 x) ≠ Complex.normSq (layer 2 x) := by
  refine ⟨fun j => decide (j = 0), ?_⟩
  rw [layer_squares, layer_squares]
  have hx : (Finset.univ.filter
      (fun j : Fin 3 => decide (j = 0) = true)).card = 1 := by
    simp [Finset.filter_eq']
  rw [hx]
  norm_num

private theorem povm_nonempty : Nonempty (LocalPOVM (Fin 3 → Bool) (Fin 3)) := by
  classical
  refine ⟨⟨fun i => if i = 0 then 1 else 0, ?_, ?_⟩⟩
  · intro i
    split_ifs
    · exact Matrix.PosSemidef.one
    · exact Matrix.PosSemidef.zero
  · simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private theorem bounded_success (ψ : (Fin 3 → Bool) → ℂ)
    (hψ : ∑ x, Complex.normSq (ψ x) = 1) :
    BddAbove (Set.range (isoSuccess (Real.pi / 4) ψ)) := by
  refine ⟨d 3 (cstar 3 (Real.pi / 4))^2, ?_⟩
  rintro y ⟨M, rfl⟩
  exact global_success_upper_bound 3 (by norm_num) (Real.pi / 4)
    (Or.inl angle_admissible) ψ hψ M

private theorem layer_optimal (l : ℕ) (hl : l = 1 ∨ l = 2)
    (ψ : (Fin 3 → Bool) → ℂ) (hψ : ∑ x, Complex.normSq (ψ x) = 1)
    (M : LocalPOVM (Fin 3 → Bool) (Fin 3)) :
    ∃ M' : LocalPOVM (Fin 3 → Bool) (Fin 3),
      isoSuccess (Real.pi / 4) ψ M ≤ isoSuccess (Real.pi / 4) (layer l) M' := by
  exact D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.result
    3 (by decide) (Real.pi / 4) (Or.inl angle_admissible) l
    (by rcases hl with rfl | rfl <;> decide) (layer_minimizes l hl)
    (layer l) (layer_squares l) ψ hψ M

private theorem optimal_sup (l : ℕ) (hl : l = 1 ∨ l = 2)
    (ψ : (Fin 3 → Bool) → ℂ) (hψ : ∑ x, Complex.normSq (ψ x) = 1) :
    optSuccess (Real.pi / 4) ψ ≤ optSuccess (Real.pi / 4) (layer l) := by
  let _ := povm_nonempty
  exact ciSup_mono_of_forall_exists
    (bounded_success (layer l)
      (dicke_normalized l (by rcases hl with rfl | rfl <;> decide)
        (layer l) (layer_squares l)))
    (layer_optimal l hl ψ hψ)

private theorem average_normalized {n : ℕ} (ψ ψ' : (Fin n → Bool) → ℂ)
    (hψ : ∑ x, Complex.normSq (ψ x) = 1)
    (hψ' : ∑ x, Complex.normSq (ψ' x) = 1) :
    ∑ x, Complex.normSq (average ψ ψ' x) = 1 := by
  have hs (x : Fin n → Bool) :
      Complex.normSq (average ψ ψ' x) =
        (Complex.normSq (ψ x) + Complex.normSq (ψ' x)) / 2 := by
    dsimp only [average]
    rw [Complex.normSq_ofReal, Real.mul_self_sqrt
      (div_nonneg (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
        (by norm_num))]
  simp only [hs]
  rw [← Finset.sum_div, Finset.sum_add_distrib, hψ, hψ']
  norm_num

private theorem equal_error :
    errorProb (Real.pi / 4) (layer 1) = errorProb (Real.pi / 4) (layer 2) := by
  apply congrArg (fun x : ℝ => 1 - x)
  exact le_antisymm
    (optimal_sup 2 (Or.inr rfl) (layer 1)
      (dicke_normalized 1 (by decide) (layer 1) (layer_squares 1)))
    (optimal_sup 1 (Or.inl rfl) (layer 2)
      (dicke_normalized 2 (by decide) (layer 2) (layer_squares 2)))

private theorem average_no_improvement :
    errorProb (Real.pi / 4) (layer 2) ≤
      errorProb (Real.pi / 4) (average (layer 1) (layer 2)) := by
  exact sub_le_sub_left
    (optimal_sup 2 (Or.inr rfl) (average (layer 1) (layer 2))
      (average_normalized (layer 1) (layer 2)
        (dicke_normalized 1 (by decide) (layer 1) (layer_squares 1))
        (dicke_normalized 2 (by decide) (layer 2) (layer_squares 2)))) 1

theorem result : ¬ claim := by
  intro h
  exact (not_lt_of_ge average_no_improvement)
    (h 3 (Real.pi / 4) angle_admissible.1 (by linarith [Real.pi_pos])
      (layer 1) (layer 2)
      (dicke_normalized 1 (by decide) (layer 1) (layer_squares 1))
      (dicke_normalized 2 (by decide) (layer 2) (layer_squares 2))
      different_layers equal_error)

end D5.S3.Quantum.Measurements.DetectorSensorStrictAveragingRefutation
