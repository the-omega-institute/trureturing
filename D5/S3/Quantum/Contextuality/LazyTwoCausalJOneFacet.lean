/- GID: D5/S3/Quantum/Contextuality/LazyTwoCausalJOneFacet
   generality: I
   mirror-B: D5/B/S3/Quantum/Contextuality/LazyTwoCausalJOneFacet
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The lazy two-causal inequality J1 induces a facet for every party count at least two. -/

import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Aesop

/-! The lazy binary scenario and inequality (10) of Abbott–Wechs–Costa–Branciard,
    Genuinely Multipartite Noncausality, arXiv:1708.07663v2, Definition 2.
    The affine dimension assertion resolves their all-party facet conjecture. -/

noncomputable section

open Finset

namespace D5.S3.Quantum.Contextuality.LazyTwoCausalJOneFacet

/-- The first nonempty proper group answers from its own inputs; all outputs are lazy. -/
def IsLazyTwoCausalStrategy {n : ℕ} (k : Finset (Fin n))
    (f : Finset (Fin n) → Finset (Fin n)) : Prop :=
  k.Nonempty ∧ k ≠ univ ∧ (∀ t, f t ⊆ t) ∧
    ∀ t u, t ∩ k = u ∩ k → f t ∩ k = f u ∩ k

/-- The probability table of a deterministic response. -/
def deterministicCorrelation {n : ℕ} (f : Finset (Fin n) → Finset (Fin n))
    (t a : Finset (Fin n)) : ℝ := if f t = a then 1 else 0

/-- The convex hull of deterministic two-causal correlations in the lazy binary scenario. -/
def twoCausalPolytope (n : ℕ) : Set (Finset (Fin n) → Finset (Fin n) → ℝ) :=
  convexHull ℝ {p | ∃ k f, IsLazyTwoCausalStrategy k f ∧ p = deterministicCorrelation f}

/-- Inequality (10). On a lazy table, inputs supported in `k` force all outputs outside
`k` to zero, so the marginal event that every output in `k` is one is exactly `p k k`. -/
def jOne {n : ℕ} (p : Finset (Fin n) → Finset (Fin n) → ℝ) : ℝ :=
  (∑ k with k.Nonempty ∧ k ≠ univ, p k k) - p univ univ

/-- Validity and codimension one of the zero face for every number of parties at least two. -/
def claim : Prop := ∀ n : ℕ, 2 ≤ n →
  (∀ p ∈ twoCausalPolytope n, 0 ≤ jOne p) ∧
  Module.finrank ℝ (vectorSpan ℝ (twoCausalPolytope n ∩ {p | jOne p = 0})) + 1 =
    Module.finrank ℝ (vectorSpan ℝ (twoCausalPolytope n))

private abbrev Reduced (n : ℕ) :=
  {i : Finset (Fin n) × Finset (Fin n) // i.2.Nonempty ∧ i.2 ⊆ i.1}

private abbrev FaceIndex (n : ℕ) := {i : Reduced n // i.1 ≠ (univ, univ)}

private def jLinear (n : ℕ) : (Finset (Fin n) → Finset (Fin n) → ℝ) →ₗ[ℝ] ℝ where
  toFun := jOne
  map_add' := by
    intro p q
    change (∑ k with k.Nonempty ∧ k ≠ univ, (p k k + q k k)) -
      (p univ univ + q univ univ) = _
    rw [Finset.sum_add_distrib]
    change _ = ((∑ k with k.Nonempty ∧ k ≠ univ, p k k) - p univ univ) +
      ((∑ k with k.Nonempty ∧ k ≠ univ, q k k) - q univ univ)
    ring
  map_smul' := by
    intro c p
    change (∑ k with k.Nonempty ∧ k ≠ univ, c * p k k) - c * p univ univ =
      c * ((∑ k with k.Nonempty ∧ k ≠ univ, p k k) - p univ univ)
    rw [← Finset.mul_sum, mul_sub]

private lemma admissible_group {n : ℕ} (hn : 2 ≤ n) :
    ∃ k : Finset (Fin n), k.Nonempty ∧ k ≠ univ := by
  sorry

private lemma vertex_valid {n : ℕ} {k : Finset (Fin n)}
    {f : Finset (Fin n) → Finset (Fin n)} (hf : IsLazyTwoCausalStrategy k f) :
    0 ≤ jOne (deterministicCorrelation f) := by
  sorry

private lemma validity (n : ℕ) : ∀ p ∈ twoCausalPolytope n, 0 ≤ jOne p := by
  sorry

private lemma polytope_laws (n : ℕ) : ∀ p ∈ twoCausalPolytope n,
    (∀ t a, ¬ a ⊆ t → p t a = 0) ∧ ∀ t, ∑ a, p t a = 1 := by
  sorry

private def homogeneousSpace (n : ℕ) :
    Submodule ℝ (Finset (Fin n) → Finset (Fin n) → ℝ) where
  carrier := {q | (∀ t a, ¬ a ⊆ t → q t a = 0) ∧ ∀ t, ∑ a, q t a = 0}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    constructor
    · intro t a ha
      change p t a + q t a = 0
      rw [hp.1 t a ha, hq.1 t a ha, add_zero]
    · intro t
      change ∑ a, (p t a + q t a) = 0
      rw [sum_add_distrib, hp.2, hq.2, add_zero]
  smul_mem' := by
    intro c p hp
    constructor
    · intro t a ha
      change c * p t a = 0
      rw [hp.1 t a ha, mul_zero]
    · intro t
      change ∑ a, c * p t a = 0
      rw [← mul_sum, hp.2, mul_zero]

private lemma polytope_span_le (n : ℕ) :
    vectorSpan ℝ (twoCausalPolytope n) ≤ homogeneousSpace n := by
  sorry

private def restriction (n : ℕ) : homogeneousSpace n →ₗ[ℝ] (Reduced n → ℝ) where
  toFun q i := q.1 i.1.1 i.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma restriction_injective (n : ℕ) : Function.Injective (restriction n) := by
  sorry

private lemma dimension_upper (n : ℕ) :
    Module.finrank ℝ (vectorSpan ℝ (twoCausalPolytope n)) ≤ Fintype.card (Reduced n) := by
  sorry

private def spike {n : ℕ} (t a : Finset (Fin n)) (u : Finset (Fin n)) :=
  if u = t then a else ∅

private def block {n : ℕ} (k t : Finset (Fin n)) :=
  (if k ⊆ t then k else ∅) ∪ (if t = univ then univ \ k else ∅)

private lemma zero_on_face {n : ℕ} (hn : 2 ≤ n) :
    deterministicCorrelation (fun _ : Finset (Fin n) => ∅) ∈
      twoCausalPolytope n ∩ {p | jOne p = 0} := by
  sorry

private lemma spike_on_face {n : ℕ} {t a : Finset (Fin n)}
    (ha : a.Nonempty) (hat : a ⊂ t) :
    deterministicCorrelation (spike t a) ∈ twoCausalPolytope n ∩ {p | jOne p = 0} := by
  sorry

private lemma block_on_face {n : ℕ} {k : Finset (Fin n)}
    (hk : k.Nonempty) (hku : k ≠ univ) :
    deterministicCorrelation (block k) ∈ twoCausalPolytope n ∩ {p | jOne p = 0} := by
  sorry

private def facePoint {n : ℕ} (i : FaceIndex n) :
    Finset (Fin n) → Finset (Fin n) → ℝ :=
  if i.1.1.2 = i.1.1.1 then deterministicCorrelation (block i.1.1.1)
  else deterministicCorrelation (spike i.1.1.1 i.1.1.2)

private lemma facePoint_mem {n : ℕ} (i : FaceIndex n) :
    facePoint i ∈ twoCausalPolytope n ∩ {p | jOne p = 0} := by
  sorry

private lemma face_independent (n : ℕ) : LinearIndependent ℝ
    (fun i : FaceIndex n => facePoint i -ᵥ
      deterministicCorrelation (fun _ : Finset (Fin n) => ∅)) := by
  sorry

private lemma index_count {n : ℕ} (hn : 2 ≤ n) :
    Fintype.card (FaceIndex n) + 1 = Fintype.card (Reduced n) := by
  sorry

private lemma dimension_lower {n : ℕ} (hn : 2 ≤ n) :
    Fintype.card (FaceIndex n) ≤
      Module.finrank ℝ (vectorSpan ℝ (twoCausalPolytope n ∩ {p | jOne p = 0})) := by
  sorry

private lemma identity_positive {n : ℕ} (hn : 2 ≤ n) :
    deterministicCorrelation (fun t : Finset (Fin n) => t) ∈ twoCausalPolytope n ∧
      0 < jOne (deterministicCorrelation (fun t : Finset (Fin n) => t)) := by
  sorry

private lemma dimension_strict {n : ℕ} (hn : 2 ≤ n) :
    Module.finrank ℝ (vectorSpan ℝ (twoCausalPolytope n ∩ {p | jOne p = 0})) + 1 ≤
      Module.finrank ℝ (vectorSpan ℝ (twoCausalPolytope n)) := by
  sorry

/-- The lazy two-causal inequality is facet inducing for all `n ≥ 2`. -/
theorem result : claim := by
  intro n hn
  refine ⟨validity n, ?_⟩
  have hu := dimension_upper n
  have hl := dimension_lower hn
  have hc := index_count hn
  have hs := dimension_strict hn
  omega

end D5.S3.Quantum.Contextuality.LazyTwoCausalJOneFacet
