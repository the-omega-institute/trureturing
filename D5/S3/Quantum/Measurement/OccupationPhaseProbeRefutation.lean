/- GID: D5/S3/Quantum/Measurement/OccupationPhaseProbeRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/OccupationPhaseProbeRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurement/OccupationPhaseProbeRefutation.claim; result=D5/S3/Quantum/Measurement/OccupationPhaseProbeRefutation.result; claim=D5/S3/Quantum/Measurement/OccupationPhaseProbeRefutation.claim
   digest: A joint occupation phase violates a bound obeyed by every linear occupation phase. -/

/-
proof_shape: result, linear_lower_bound: content
escape_witness: a weighted sum-of-squares domination of the entire linear
  occupation family and a strictly smaller nonlinear occupation quotient.
admission_basis: escape-witness
Direct frozen dependencies: none (pinned Mathlib only).
proof_shape: carrier_value, partition_value, linear_certificate,
  quadratic_values: bind-only; consumed by linear_lower_bound or result.
The refuted assertion is probe sufficiency, not the activity two-edge conjecture.
-/

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8000

open scoped BigOperators

namespace D5.S3.Quantum.Measurement.OccupationPhaseProbeRefutation

/-- Site digits in a five-site binary word, with the first site least significant. -/
def bit (s i : ℕ) : ℕ := (s / 2 ^ i) % 2

/-- Exactly the five-site words with no two adjacent occupied sites. -/
def legalWords : Finset ℕ :=
  (Finset.range 32).filter fun s => ∀ i : Fin 4, bit s i * bit s (i + 1) = 0

noncomputable def activity : Fin 5 → ℝ := ![100, 1, 100, 1, 100]

noncomputable def weight : Fin 5 → ℝ :=
  ![368 / 2565, 5101 / 17955, 289 / 1995, 5101 / 17955, 368 / 2565]

noncomputable def mass (s : ℕ) : ℝ := ∏ i : Fin 5, activity i ^ bit s i

noncomputable def partition : ℝ := ∑ s ∈ legalWords, mass s

noncomputable def probability (s : ℕ) : ℝ := mass s / partition

noncomputable def occupation (s : ℕ) (i : Fin 5) : ℝ := bit s i

/-- Variance under the same positive constrained activity law. -/
noncomputable def variance (f : ℕ → ℝ) : ℝ :=
  (∑ s ∈ legalWords, probability s * f s ^ 2) -
    (∑ s ∈ legalWords, probability s * f s) ^ 2

/-- Each empty-to-occupied legal edge is counted once with its insertion flux. -/
noncomputable def energy (f : ℕ → ℝ) : ℝ :=
  ∑ s ∈ legalWords, ∑ i : Fin 5,
    if bit s i = 0 ∧ s + 2 ^ (i : ℕ) ∈ legalWords then
      probability s * weight i * (activity i / (1 + activity i)) *
        (f s - f (s + 2 ^ (i : ℕ))) ^ 2
    else 0

noncomputable def linear (c : Fin 5 → ℝ) (s : ℕ) : ℝ :=
  ∑ i : Fin 5, c i * occupation s i

/-- A nonlinear phase involving the joint occupation of sites one and three. -/
noncomputable def quadratic (s : ℕ) : ℝ :=
  (1 - occupation s 0) * (1 - occupation s 2) + occupation s 1

/-- The assertion that testing all linear occupations suffices for the full phase bound. -/
def claim : Prop :=
  (∀ c : Fin 5 → ℝ, variance (linear c) / 10 ≤ energy (linear c)) →
    ∀ f : ℕ → ℝ, variance f / 10 ≤ energy f

private theorem carrier_value :
    legalWords = {0, 1, 2, 4, 5, 8, 9, 10, 16, 17, 18, 20, 21} := by
  decide

private theorem partition_value : partition = 1030504 := by
  norm_num [partition, carrier_value, mass, activity, bit, Fin.prod_univ_succ]

private noncomputable def sos (c : Fin 5 → ℝ) : ℝ :=
  296233677576200 * (c 0) ^ 2 +
  201992930717100 * (c 1 / 10) ^ 2 +
  197414496485100 * (c 2) ^ 2 +
  201992930717100 * (c 3 / 10) ^ 2 +
  296233677576200 * (c 4) ^ 2 +
  94354426341000 * (c 0 + c 1 / 10) ^ 2 +
  9341106705000 * (c 0 - c 2) ^ 2 +
  915794775000 * (c 0 + c 3 / 10) ^ 2 +
  90672750000 * (c 0 - c 4) ^ 2 +
  94345177720500 * (c 1 / 10 + c 2) ^ 2 +
  9249527227500 * (c 1 / 10 - c 3 / 10) ^ 2 +
  915794775000 * (c 1 / 10 + c 4) ^ 2 +
  94345177720500 * (c 2 + c 3 / 10) ^ 2 +
  9341106705000 * (c 2 - c 4) ^ 2 +
  94354426341000 * (c 3 / 10 + c 4) ^ 2

set_option maxHeartbeats 2000000 in
-- Expanding every legal insertion edge and the full variance requires extra reduction fuel.
private theorem linear_certificate (c : Fin 5 → ℝ) :
    energy (linear c) - variance (linear c) / 10 =
      sos c / 962888835832892640 := by
  norm_num [energy, variance, linear, probability, partition_value, carrier_value,
    mass, activity, weight, occupation, bit, Fin.sum_univ_succ, Fin.prod_univ_succ,
    sos]
  ring

private theorem linear_lower_bound (c : Fin 5 → ℝ) :
    variance (linear c) / 10 ≤ energy (linear c) := by
  have hs : 0 ≤ sos c / 962888835832892640 := by
    unfold sos
    positivity
  have he := linear_certificate c
  linarith

private theorem quadratic_values :
    energy quadratic = 8757839 / 207641403480 ∧
      variance quadratic = 131365851 / 265484623504 := by
  norm_num [energy, variance, quadratic, probability, partition_value, carrier_value,
    mass, activity, weight, occupation, bit, Fin.sum_univ_succ, Fin.prod_univ_succ]

/-- Every linear occupation phase obeys the bound, but the joint-occupation phase fails it. -/
theorem result : ¬ claim := by
  intro h
  have hq := h linear_lower_bound quadratic
  rcases quadratic_values with ⟨he, hv⟩
  rw [he, hv] at hq
  norm_num at hq

#print axioms result

end D5.S3.Quantum.Measurement.OccupationPhaseProbeRefutation
