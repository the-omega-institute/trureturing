/- GID: D5/S3/Quantum/Fibers/BipartiteBlockade/JointDiagonalCoordinates
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/BipartiteBlockade/JointDiagonalCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Independent blocking coordinates admit arbitrary signed diagonal perturbations with zero trace and unchanged single-site means. -/

import D5.S3.Quantum.Fibers.BipartiteBlockade.GeneralCommutator
import D5.S3.Quantum.Fibers.BipartiteBlockade.NeighborhoodIndependence

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators Classical

namespace D5.S3.Quantum.Fibers.BipartiteBlockade.JointDiagonalCoordinates

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual diagonal blocking moment on a prescribed independent vertex set. -/
def blockingMoment (G : SimpleGraph V) (N : Finset V)
    (δ : Configuration G → ℝ) : ℝ :=
  ∑ S, δ S * (if Disjoint N S.val then 1 else 0)

private def momentMatrix (G : SimpleGraph V) (F : Finset (Finset V)) :
    Matrix (Option (V ⊕ F)) (Configuration G) ℝ :=
  fun i S => match i with
    | none => 1
    | some (.inl v) => if v ∈ S.val then 1 else 0
    | some (.inr N) => if Disjoint N.val S.val then 1 else 0

private theorem moment_rows_independent (G : SimpleGraph V) (F : Finset (Finset V))
    (independent : ∀ N ∈ F, ∀ u ∈ N, ∀ v ∈ N, ¬G.Adj u v)
    (large : ∀ N ∈ F, 2 ≤ N.card) :
    LinearIndependent ℝ (momentMatrix G F).row := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have heval (S : Configuration G) :
      c none + (∑ v, c (some (.inl v)) * (if v ∈ S.val then 1 else 0)) +
        ∑ N : F, c (some (.inr N)) * (if Disjoint N.val S.val then 1 else 0) = 0 := by
    have h := congrFun hc S
    simpa [momentMatrix, Matrix.row, Fintype.sum_option, Fintype.sum_sum_type,
      Pi.smul_apply, smul_eq_mul, add_assoc] using h
  let coefficient : Finset V → ℝ := fun N =>
    if h : N ∈ F then c (some (.inr ⟨N, h⟩)) else 0
  have hcoefficient (N : F) : coefficient N.val = c (some (.inr N)) := by
    simp [coefficient]
  have hsum (S : Finset V) :
      (∑ N ∈ F, coefficient N * (if Disjoint N S then 1 else 0)) =
        ∑ N : F, c (some (.inr N)) * (if Disjoint N.val S then 1 else 0) := by
    rw [← Finset.sum_coe_sort]
    apply Fintype.sum_congr
    intro N
    rw [hcoefficient]
  have hocc (S : Finset V) :
      (∑ v, c (some (.inl v)) * (if v ∈ S then 1 else 0)) =
        ∑ v ∈ S, c (some (.inl v)) := by
    simp only [mul_ite, mul_one, mul_zero]
    exact Finset.sum_ite_mem_eq S (fun v => c (some (.inl v)))
  have hz := NeighborhoodIndependence.blocking_independent_mod_singletons G F
    independent large coefficient (-c none) (fun v => -c (some (.inl v))) (by
      intro S hind
      rw [hsum]
      have h := heval ⟨S, hind⟩
      rw [hocc] at h
      simp only [Finset.sum_neg_distrib]
      linarith)
  have hblockzero : ∀ N : F, c (some (.inr N)) = 0 := by
    intro N
    rw [← hcoefficient]
    exact hz N.val N.property
  have hsimple (S : Configuration G) :
      c none + ∑ v, c (some (.inl v)) * (if v ∈ S.val then 1 else 0) = 0 := by
    simpa only [hblockzero, zero_mul, Finset.sum_const_zero, add_zero] using heval S
  let vacuum : Configuration G := ⟨∅, by simp⟩
  have hconstant : c none = 0 := by simpa [vacuum] using hsimple vacuum
  have hsingle : ∀ v, c (some (.inl v)) = 0 := by
    intro v
    let singleton : Configuration G := ⟨{v}, by simp⟩
    simpa [hconstant, singleton] using hsimple singleton
  intro i
  rcases i with _ | (v | N)
  · exact hconstant
  · exact hsingle v
  · exact hblockzero N

/-- All blocking coordinates from distinct independent sets of size at least two
can be changed independently by a signed diagonal perturbation, without changing
trace or any single-site mean. -/
theorem arbitrary_diagonal_blocking_coordinates
    (G : SimpleGraph V) (F : Finset (Finset V))
    (independent : ∀ N ∈ F, ∀ u ∈ N, ∀ v ∈ N, ¬G.Adj u v)
    (large : ∀ N ∈ F, 2 ≤ N.card) (x : F → ℝ) :
    ∃ δ : Configuration G → ℝ,
      (∑ S, δ S) = 0 ∧
      (∀ v, (∑ S, δ S * (if v ∈ S.val then 1 else 0)) = 0) ∧
      ∀ N : F, blockingMoment G N.val δ = x N := by
  let target : Option (V ⊕ F) → ℝ := fun i => match i with
    | none => 0
    | some (.inl _) => 0
    | some (.inr N) => x N
  obtain ⟨δ, hδ⟩ := (moment_rows_independent G F independent large).mulVec_surjective target
  refine ⟨δ, ?_, ?_, ?_⟩
  · have h := congrFun hδ none
    simpa [momentMatrix, Matrix.mulVec, dotProduct, target] using h
  · intro v
    have h := congrFun hδ (some (.inl v))
    simpa [momentMatrix, Matrix.mulVec, dotProduct, target, mul_comm] using h
  · intro N
    have h := congrFun hδ (some (.inr N))
    simpa [momentMatrix, Matrix.mulVec, dotProduct, target, blockingMoment, mul_comm] using h

/-- Zero-trace, fixed-single-site signed diagonal directions. -/
def fixedMeanDirections (G : SimpleGraph V) : Submodule ℝ (Configuration G → ℝ) where
  carrier := {δ | (∑ S, δ S) = 0 ∧
    ∀ v, (∑ S, δ S * (if v ∈ S.val then 1 else 0)) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    constructor
    · simpa [Finset.sum_add_distrib] using congrArg₂ (· + ·) ha.1 hb.1
    · intro v
      change (∑ S, (a S + b S) * (if v ∈ S.val then 1 else 0)) = 0
      rw [show (∑ S, (a S + b S) * (if v ∈ S.val then 1 else 0)) =
        (∑ S, a S * (if v ∈ S.val then 1 else 0)) +
        ∑ S, b S * (if v ∈ S.val then 1 else 0) by
          simp only [add_mul, Finset.sum_add_distrib], ha.2 v, hb.2 v, add_zero]
  smul_mem' := by
    intro r δ hδ
    constructor
    · simp [← Finset.mul_sum, hδ.1]
    · intro v
      change (∑ S, (r * δ S) * (if v ∈ S.val then 1 else 0)) = 0
      simp only [mul_assoc, ← Finset.mul_sum, hδ.2 v, mul_zero]

/-- The coordinate map evaluates actual signed diagonal measures. -/
def blockingMap (G : SimpleGraph V) (F : Finset (Finset V)) :
    (Configuration G → ℝ) →ₗ[ℝ] (F → ℝ) where
  toFun δ N := blockingMoment G N.val δ
  map_add' := by
    intro a b
    ext N
    change (∑ S, (a S + b S) * (if Disjoint N.val S.val then 1 else 0)) = _
    simp only [add_mul, Finset.sum_add_distrib]
    rfl
  map_smul' := by
    intro r δ
    ext N
    change (∑ S, (r * δ S) * (if Disjoint N.val S.val then 1 else 0)) = _
    simp only [mul_assoc, ← Finset.mul_sum]
    rfl

/-- A prescribed linear compatibility equation on blocking coordinates. -/
def compatibility (F : Finset (Finset V)) (weight : F → ℝ) : (F → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ N, weight N * x N
  map_add' := by intro a b; simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by intro r x; simp [mul_left_comm, ← Finset.mul_sum]

/-- Blocking coordinates attained by fixed-mean signed diagonals satisfying the
specified compatibility equation. -/
def attainableResidual (G : SimpleGraph V) (F : Finset (Finset V))
    (weight : F → ℝ) : Submodule ℝ (F → ℝ) :=
  (fixedMeanDirections G ⊓
    LinearMap.ker ((compatibility F weight).comp (blockingMap G F))).map (blockingMap G F)

private theorem residual_eq_ker (G : SimpleGraph V) (F : Finset (Finset V))
    (independent : ∀ N ∈ F, ∀ u ∈ N, ∀ v ∈ N, ¬G.Adj u v)
    (large : ∀ N ∈ F, 2 ≤ N.card) (weight : F → ℝ) :
    attainableResidual G F weight = LinearMap.ker (compatibility F weight) := by
  ext x
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    exact hδ.2
  · intro hx
    obtain ⟨δ, ht, hm, hb⟩ := arbitrary_diagonal_blocking_coordinates G F independent large x
    have heq : blockingMap G F δ = x := funext hb
    refine ⟨δ, ⟨⟨ht, hm⟩, ?_⟩, heq⟩
    change compatibility F weight (blockingMap G F δ) = 0
    rw [heq]
    exact hx

/-- For a nonzero compatibility functional, the actual signed-diagonal
blocking residual has affine-direction dimension exactly one less than the
number of independent nonlinear blocking coordinates. -/
theorem residual_dimension_exact
    (G : SimpleGraph V) (F : Finset (Finset V))
    (independent : ∀ N ∈ F, ∀ u ∈ N, ∀ v ∈ N, ¬G.Adj u v)
    (large : ∀ N ∈ F, 2 ≤ N.card) (weight : F → ℝ)
    (nonzero : ∃ N, weight N ≠ 0) :
    Module.finrank ℝ (attainableResidual G F weight) = F.card - 1 := by
  rw [residual_eq_ker G F independent large weight]
  have hne : compatibility F weight ≠ 0 := by
    obtain ⟨N, hN⟩ := nonzero
    intro hz
    have h := congrArg (fun f : (F → ℝ) →ₗ[ℝ] ℝ => f (Pi.single N 1)) hz
    apply hN
    change (∑ K : F, weight K * (Pi.single N (1 : ℝ) : F → ℝ) K) = 0 at h
    have hsingle : (∑ K : F, weight K * (Pi.single N (1 : ℝ) : F → ℝ) K) = weight N := by
      rw [Fintype.sum_eq_single N]
      · simp only [Pi.single_eq_same, mul_one]
      · intro K hK
        rw [Pi.single_eq_of_ne hK, mul_zero]
    exact hsingle.symm.trans h
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hne
  simp only [Module.finrank_pi, Module.finrank_self, mul_one, Fintype.card_coe] at hdim
  omega

/-- info: 'D5.S3.Quantum.Fibers.BipartiteBlockade.JointDiagonalCoordinates.arbitrary_diagonal_blocking_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms arbitrary_diagonal_blocking_coordinates
/-- info: 'D5.S3.Quantum.Fibers.BipartiteBlockade.JointDiagonalCoordinates.residual_dimension_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms residual_dimension_exact

end D5.S3.Quantum.Fibers.BipartiteBlockade.JointDiagonalCoordinates
