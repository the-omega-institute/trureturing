/- GID: D5/S3/QuantumContext/SingleMeasurementPseudobroadcastingRefutation
   generality: I
   mirror-B: D5/B/S3/QuantumContext/SingleMeasurementPseudobroadcastingRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuantumContext/SingleMeasurementPseudobroadcastingRefutation.claim; result=D5/S3/QuantumContext/SingleMeasurementPseudobroadcastingRefutation.result; claim=D5/S3/QuantumContext/SingleMeasurementPseudobroadcastingRefutation.claim
   digest: One qubit measurement permits one-copy pseudo-broadcasting but is contextual. -/

import D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
import D5.S3.Quantum.Recovery.PurifiedLocalPath
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import Mathlib.Analysis.Convex.Hull

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators ComplexOrder
open D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsDensity)
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)
open D5.S3.Quantum.Recovery.ProductPrefixRigidity (productMap)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)

namespace D5.S3.QuantumContext.SingleMeasurementPseudobroadcastingRefutation

def Subtheory {d : ℕ} (t a : Set (Matrix (Fin d) (Fin d) ℂ)) : Prop :=
  Convex ℝ t ∧ (∀ ρ ∈ t, IsDensity ρ) ∧ Convex ℝ a ∧
    (∀ e ∈ a, e.PosSemidef ∧ (1 - e).PosSemidef) ∧
    1 ∈ a ∧ ∀ e ∈ a, 1 - e ∈ a

def postprocessings {d m : ℕ} (p : Fin m → Matrix (Fin d) (Fin d) ℂ) :
    Set (Matrix (Fin d) (Fin d) ℂ) :=
  {e | ∃ c : Fin m → ℝ, (∀ o, 0 ≤ c o ∧ c o ≤ 1) ∧ e = ∑ o, (c o : ℂ) • p o}

def GeneratedBy {d : ℕ} (a : Set (Matrix (Fin d) (Fin d) ℂ)) (k : ℕ) : Prop :=
  ∃ (m : Fin k → ℕ) (p : ∀ j, Fin (m j) → Matrix (Fin d) (Fin d) ℂ),
    (∀ j, IsPOVM (p j)) ∧ a = convexHull ℝ (⋃ j, postprocessings (p j))

def partialTraceKeep {d n : ℕ} (i : Fin n)
    (x : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  partialTraceRight (x.submatrix
    (fun z : Fin d × ({j : Fin n // j ≠ i} → Fin d) =>
      fun j => if h : j = i then z.1 else z.2 ⟨j, h⟩)
    (fun z : Fin d × ({j : Fin n // j ≠ i} → Fin d) =>
      fun j => if h : j = i then z.1 else z.2 ⟨j, h⟩))

def PseudoBroadcastable {d : ℕ} (t a : Set (Matrix (Fin d) (Fin d) ℂ)) (n : ℕ) :
    Prop :=
  ∃ ξ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ,
    (∀ x, (ξ x).trace = x.trace) ∧
    (∀ i, ∀ ρ ∈ t, ∀ e ∈ a, (e * partialTraceKeep i (ξ ρ)).trace = (e * ρ).trace) ∧
    ∀ ρ ∈ t, ∀ e : Fin n → Matrix (Fin d) (Fin d) ℂ,
      (∀ i, e i ∈ a) → 0 ≤ (ξ ρ * productMap (fun _ => Fin d) e).trace

def Noncontextual {d : ℕ} (t a : Set (Matrix (Fin d) (Fin d) ℂ)) : Prop :=
  ∃ (ι : Type) (g s : ι → Matrix (Fin d) (Fin d) ℂ),
    (∀ l, ∀ ρ ∈ t, 0 ≤ (ρ * g l).trace) ∧
    (∀ ρ ∈ t, HasSum (fun l => (ρ * g l).trace) 1) ∧
    (∀ l, ∀ e ∈ a, 0 ≤ (s l * e).trace) ∧ (∀ l, (s l).trace = 1) ∧
    ∀ ρ ∈ t, ∀ e ∈ a,
      HasSum (fun l => (ρ * g l).trace * (s l * e).trace) (ρ * e).trace

def claim : Prop :=
  ∀ (d k : ℕ) (t a : Set (Matrix (Fin d) (Fin d) ℂ)),
    Subtheory t a → GeneratedBy a k → (PseudoBroadcastable t a k ↔ Noncontextual t a)

private def rho (j : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 10 : ℝ) • Matrix.vecMulVec
    (![![3, 1], ![1, 3], ![3, -1], ![1, -3]] j : Fin 2 → ℂ)
    (star (![![3, 1], ![1, 3], ![3, -1], ![1, -3]] j : Fin 2 → ℂ))

private def measurement (o : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  (![1 / 4, 1 / 4, 1 / 2, 1 / 2] o : ℝ) • Matrix.vecMulVec
    (![![1, 1], ![1, -1], ![1, 0], ![0, 1]] o : Fin 2 → ℂ)
    (star (![![1, 1], ![1, -1], ![1, 0], ![0, 1]] o : Fin 2 → ℂ))

private def preparations : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
  convexHull ℝ (Set.range rho)

private def effects : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
  convexHull ℝ (postprocessings measurement)

private lemma rho_density (j : Fin 4) : IsDensity (rho j) := by
  sorry

private lemma measurement_povm : IsPOVM measurement := by
  sorry

private lemma witness_subtheory : Subtheory preparations effects := by
  sorry

private lemma witness_generated : GeneratedBy effects 1 := by
  sorry

private lemma one_copy {d : ℕ} {t a : Set (Matrix (Fin d) (Fin d) ℂ)}
    (h : Subtheory t a) : PseudoBroadcastable t a 1 := by
  sorry

private lemma corner_bound (u v w z x y : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hz : 0 ≤ z)
    (ht : u + z = v + w) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hx' : x ≤ 1 / 2) (hy' : y ≤ 1 / 2) :
    (u * (x + y) + v * (x + (1 / 2 - y)) +
      w * ((1 / 2 - x) + y) + z * ((1 / 2 - x) + (1 / 2 - y))) / 4 ≤
      3 / 8 * (u + z) := by
  sorry

private lemma witness_contextual : ¬ Noncontextual preparations effects := by
  sorry

theorem result : ¬ claim := by
  intro h
  exact witness_contextual ((h 2 1 preparations effects witness_subtheory witness_generated).mp
    (one_copy witness_subtheory))

end D5.S3.QuantumContext.SingleMeasurementPseudobroadcastingRefutation
