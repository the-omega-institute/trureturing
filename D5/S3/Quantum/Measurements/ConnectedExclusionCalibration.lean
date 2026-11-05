/- GID: D5/S3/Quantum/Measurements/ConnectedExclusionCalibration
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/ConnectedExclusionCalibration
   mirror-E: none(waiver:unbounded-finite-graph-family)
   anchors: []
   utility: none
   digest: One zero seed calibrates the same response on finite connected exclusion graphs. -/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! Calibration and concentration of the original response on independent configurations. -/

noncomputable section

open scoped BigOperators

namespace D5.S3.Quantum.Measurements.ConnectedExclusionCalibration

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The original configuration family contains the empty record and every singleton,
and every one of its records is independent in the same exclusion graph. -/
def IsRecordFamily (G : SimpleGraph V) (S : Finset (Finset V)) : Prop :=
  ∅ ∈ S ∧ (∀ k : V, {k} ∈ S) ∧ ∀ t ∈ S, G.IsIndepSet (t : Set V)

/-- The bit marginal of the original response, with no replacement of outcome names. -/
def marginal (S : Finset (Finset V)) (T : S → S → ℝ) (k : V) (s : S) : ℝ :=
  ∑ t : S, if k ∈ t.val then T t s else 0

/-- Nonnegative normalized columns, the original same-bit marginal law, and
one-sided support compatibility. -/
structure ResponseLaws (S : Finset (Finset V)) (T : S → S → ℝ)
    (a b : V → ℝ) : Prop where
  nonneg : ∀ t s, 0 ≤ T t s
  normalized : ∀ s, ∑ t : S, T t s = 1
  binary : ∀ k s, marginal S T k s = if k ∈ s.val then b k else a k
  compatible : ∀ k, a k = 0 → b k = 1

private theorem marginal_nonneg (S : Finset (Finset V)) (T : S → S → ℝ)
    (a b : V → ℝ) (hT : ResponseLaws S T a b) (k : V) (s : S) :
    0 ≤ marginal S T k s := by
  apply Finset.sum_nonneg
  intro t _
  split_ifs
  · exact hT.nonneg t s
  · exact le_rfl

private theorem atom_le_marginal (S : Finset (Finset V)) (T : S → S → ℝ)
    (a b : V → ℝ) (hT : ResponseLaws S T a b) (k : V) (t s : S)
    (ht : k ∈ t.val) : T t s ≤ marginal S T k s := by
  have h := Finset.single_le_sum
    (s := Finset.univ) (f := fun u : S => if k ∈ u.val then T u s else 0)
    (fun u _ => by
      split_ifs
      · exact hT.nonneg u s
      · exact le_rfl)
    (Finset.mem_univ t)
  simpa only [marginal, ite_eq_left ht] using h

private theorem atom_le_complement (S : Finset (Finset V)) (T : S → S → ℝ)
    (a b : V → ℝ) (hT : ResponseLaws S T a b) (k : V) (t s : S)
    (ht : k ∉ t.val) : T t s ≤ 1 - marginal S T k s := by
  have h := Finset.single_le_sum
    (s := Finset.univ) (f := fun u : S => if k ∉ u.val then T u s else 0)
    (fun u _ => by
      by_cases hu : k ∉ u.val
      · simpa only [ite_eq_left hu] using hT.nonneg u s
      · simp only [ite_eq_right hu, le_refl])
    (Finset.mem_univ t)
  simp only [ite_eq_left ht] at h
  have hsum : (∑ u : S, if k ∉ u.val then T u s else 0) + marginal S T k s = 1 := by
    rw [marginal, ← Finset.sum_add_distrib]
    convert hT.normalized s using 1
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : k ∈ u.val <;> simp [hu]
  linarith

private theorem adjacent_marginals_le_one (G : SimpleGraph V) (S : Finset (Finset V))
    (hS : IsRecordFamily G S) (T : S → S → ℝ) (a b : V → ℝ)
    (hT : ResponseLaws S T a b) {i j : V} (hij : G.Adj i j) (s : S) :
    marginal S T i s + marginal S T j s ≤ 1 := by
  unfold marginal
  rw [← Finset.sum_add_distrib, ← hT.normalized s]
  apply Finset.sum_le_sum
  intro t _
  by_cases hi : i ∈ t.val
  · have hj : j ∉ t.val := by
      intro hj
      exact (G.isIndepSet_iff.mp (hS.2.2 t.val t.property) hi hj hij.ne) hij
    simp [hi, hj]
  · by_cases hj : j ∈ t.val
    · simp [hi, hj]
    · simpa [hi, hj] using hT.nonneg t s

private theorem edge_propagates_zero (G : SimpleGraph V) (S : Finset (Finset V))
    (hS : IsRecordFamily G S) (T : S → S → ℝ) (a b : V → ℝ)
    (hT : ResponseLaws S T a b) {i j : V} (hij : G.Adj i j) (hi : a i = 0) :
    a j = 0 := by
  let source : S := ⟨{i}, hS.2.1 i⟩
  let empty : S := ⟨∅, hS.1⟩
  have hbi := hT.compatible i hi
  have hmi : marginal S T i source = 1 := by
    simpa [source, hbi] using hT.binary i source
  have hmj : marginal S T j source = a j := by
    simpa [source, Ne.symm hij.ne] using hT.binary j source
  have hmempty : marginal S T j empty = a j := by
    simpa [empty] using hT.binary j empty
  have hnonneg := marginal_nonneg S T a b hT j empty
  have hbound := adjacent_marginals_le_one G S hS T a b hT hij source
  rw [hmi, hmj] at hbound
  rw [hmempty] at hnonneg
  linarith

/-- Every positive transition preserves all original bits. The seed propagates
through singleton source columns before concentration is extracted. -/
private theorem propagated_support_rigidity (G : SimpleGraph V)
    (S : Finset (Finset V)) (hS : IsRecordFamily G S) (T : S → S → ℝ)
    (a b : V → ℝ) (hT : ResponseLaws S T a b) (hG : G.Connected)
    (hseed : ∃ k, a k = 0) :
    (∀ k, a k = 0 ∧ b k = 1) ∧
      ∀ t s, 0 < T t s → ∀ k, k ∈ t.val ↔ k ∈ s.val := by
  obtain ⟨seed, hseed⟩ := hseed
  have along_walk : ∀ {i j : V}, G.Walk i j → a i = 0 → a j = 0 := by
    intro i j p
    induction p with
    | nil => exact id
    | cons hij p ih =>
      intro hi
      exact ih (edge_propagates_zero G S hS T a b hT hij hi)
  have hcal : ∀ k, a k = 0 ∧ b k = 1 := by
    intro k
    have hk := (hG seed k).elim (fun p => along_walk p hseed)
    exact ⟨hk, hT.compatible k hk⟩
  refine ⟨hcal, ?_⟩
  intro t s hpos k
  constructor
  · intro ht
    by_contra hs
    have hm : marginal S T k s = 0 := by
      simpa [hs, (hcal k).1] using hT.binary k s
    have hb := atom_le_marginal S T a b hT k t s ht
    linarith
  · intro hs
    by_contra ht
    have hm : marginal S T k s = 1 := by
      simpa [hs, (hcal k).2] using hT.binary k s
    have hb := atom_le_complement S T a b hT k t s ht
    linarith

/-- Whole original R5-002 Theorem 5.1: one internal zero seed calibrates every
vertex and makes the same normalized response the identity on its original names. -/
theorem connected_response_calibration (G : SimpleGraph V)
    (S : Finset (Finset V)) (hS : IsRecordFamily G S) (T : S → S → ℝ)
    (a b : V → ℝ) (hT : ResponseLaws S T a b) (hG : G.Connected)
    (hseed : ∃ k, a k = 0) :
    (∀ k, a k = 0 ∧ b k = 1) ∧
      ∀ t s, T t s = if t = s then 1 else 0 := by
  classical
  obtain ⟨hcal, hrigid⟩ := propagated_support_rigidity G S hS T a b hT hG hseed
  have hwrong : ∀ t s : S, t ≠ s → T t s = 0 := by
    intro t s hne
    apply le_antisymm _ (hT.nonneg t s)
    by_contra hle
    have hbits := hrigid t s (lt_of_not_ge hle)
    apply hne
    apply Subtype.ext
    exact Finset.ext (fun k => hbits k)
  refine ⟨hcal, ?_⟩
  intro t s
  by_cases hts : t = s
  · subst t
    rw [ite_eq_left rfl]
    have hsum : (∑ t : S, T t s) = T s s := by
      apply Finset.sum_eq_single s
      · intro t _ hne
        exact hwrong t s hne
      · simp
    linarith [hT.normalized s]
  · rw [ite_eq_right hts]
    exact hwrong t s hts

#print axioms connected_response_calibration

end D5.S3.Quantum.Measurements.ConnectedExclusionCalibration
