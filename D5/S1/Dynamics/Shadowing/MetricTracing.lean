/- GID: D5/S1/Dynamics/Shadowing/MetricTracing
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/MetricTracing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict metric shadowing, noncompact uniform tracing and infinite diagonal splicing. -/

import D5.S1.Dynamics.Shadowing.UniformTracing
import Mathlib.Dynamics.SymbolicDynamics.Basic

open Function Set Filter
open scoped Uniformity

namespace D5.S1.Dynamics.Shadowing

/-- Strict forward errors, on an entire infinite sequence. -/
def MetricPseudoOrbit {X : Type*} [PseudoMetricSpace X] (f : X → X)
    (δ : ℝ) (z : ℕ → X) : Prop := ∀ i, dist (f (z i)) (z (i + 1)) < δ

/-- Strict tracing at every natural time, including zero. -/
def MetricTraces {X : Type*} [PseudoMetricSpace X] (f : X → X)
    (ε : ℝ) (z : ℕ → X) (y : X) : Prop := ∀ i, dist (f^[i] y) (z i) < ε

def MetricHasShadowing {X : Type*} [PseudoMetricSpace X] (f : X → X) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ z : ℕ → X, MetricPseudoOrbit f δ z →
    ∃ y, MetricTraces f ε z y

def HasLipschitzShadowing {X : Type*} [PseudoMetricSpace X] (f : X → X) : Prop :=
  ∃ L > 0, ∃ δ₀ > 0, ∀ δ > 0, δ ≤ δ₀ → ∀ z : ℕ → X,
    MetricPseudoOrbit f δ z → ∃ y, MetricTraces f (L * δ) z y

/-- The metric entourage basis identifies the two infinite tracing contracts.
No compactness or finite open cover is involved. -/
theorem metric_shadowing_iff_uniform {X : Type*} [PseudoMetricSpace X] (f : X → X) :
    MetricHasShadowing f ↔ UniformHasShadowing f := by
  constructor
  · intro h E hE
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_uniformity_dist.mp hE
    obtain ⟨δ, hδ, ht⟩ := h ε hε
    refine ⟨{p | dist p.1 p.2 < δ}, Metric.dist_mem_uniformity hδ, ?_⟩
    intro z hz
    obtain ⟨y, hy⟩ := ht z hz
    exact ⟨y, fun i => hsub (hy i)⟩
  · intro h ε hε
    obtain ⟨D, hD, ht⟩ := h {p | dist p.1 p.2 < ε} (Metric.dist_mem_uniformity hε)
    obtain ⟨δ, hδ, hsub⟩ := Metric.mem_uniformity_dist.mp hD
    refine ⟨δ, hδ, fun z hz => ?_⟩
    exact ht z (fun i => hsub (hz i))

/-- Lipschitz tracing supplies ordinary tracing by choosing a small positive control. -/
theorem HasLipschitzShadowing.metricHasShadowing {X : Type*} [PseudoMetricSpace X]
    {f : X → X} (h : HasLipschitzShadowing f) : MetricHasShadowing f := by
  obtain ⟨L, hL, δ₀, hδ₀, ht⟩ := h
  intro ε hε
  let δ := min δ₀ (ε / (2 * L))
  have hδ : 0 < δ := lt_min hδ₀ (div_pos hε (by positivity))
  refine ⟨δ, hδ, fun z hz => ?_⟩
  obtain ⟨y, hy⟩ := ht δ hδ (min_le_left _ _) z hz
  refine ⟨y, fun i => (hy i).trans_le ?_⟩
  have hb := mul_le_mul_of_nonneg_left (min_le_right δ₀ (ε / (2 * L))) hL.le
  have he : L * (ε / (2 * L)) = ε / 2 := by field_simp
  exact hb.trans (by rw [he]; linarith)

/-- The existing symbolic shift by one has the expected natural iterates. -/
theorem shift_one_iterate_apply {A : Type*} (x : ℕ → A) (i j : ℕ) :
    (SymbolicDynamics.FullShift.shift (1 : ℕ))^[i] x j = x (i + j) := by
  induction i generalizing x j with
  | zero => simp
  | succ i ih =>
    rw [iterate_succ_apply', SymbolicDynamics.FullShift.shift_apply, ih]
    congr 1
    omega

/-- The full product always contains the diagonal splice. -/
def diagonalSplice {A : Type*} (z : ℕ → ℕ → A) : ℕ → A := fun k => z k 0

/-- Overlap through N propagates through N+1 for every time in an infinite sequence. -/
theorem diagonal_splice_overlap {A : Type*} (z : ℕ → ℕ → A) (N : ℕ)
    (h : ∀ i j, j ≤ N → z i (j + 1) = z (i + 1) j) :
    ∀ i j, j ≤ N + 1 → diagonalSplice z (i + j) = z i j := by
  intro i j
  induction j generalizing i with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have hs := ih (i + 1) (by omega)
    have he := h i j (by omega)
    simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using hs.trans he.symm

/-- A diagonal mismatch telescopes to an earlier edge mismatch, with both indices bounded. -/
theorem diagonal_mismatch_edge {A : Type*} (z : ℕ → ℕ → A) (i j : ℕ)
    (h : diagonalSplice z (i + j) ≠ z i j) :
    ∃ t k, i ≤ t ∧ t < i + j ∧ k < j ∧ z t (k + 1) ≠ z (t + 1) k := by
  induction j generalizing i with
  | zero => exact (h rfl).elim
  | succ j ih =>
    by_cases he : z i (j + 1) = z (i + 1) j
    · have hh : diagonalSplice z ((i + 1) + j) ≠ z (i + 1) j := by
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, he] using h
      obtain ⟨t, k, hit, ht, hk, hne⟩ := ih (i + 1) hh
      exact ⟨t, k, by omega, by omega, by omega, hne⟩
    · exact ⟨i, j, le_rfl, by omega, by omega, he⟩

#print axioms metric_shadowing_iff_uniform
#print axioms diagonal_splice_overlap
#print axioms diagonal_mismatch_edge

end D5.S1.Dynamics.Shadowing
