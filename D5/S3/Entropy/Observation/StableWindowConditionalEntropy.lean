/- GID: D5/S3/Entropy/Observation/StableWindowConditionalEntropy
   generality: G
   mirror-B: D5/B/S3/Entropy/Observation/StableWindowConditionalEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Stable kernels give zero next-readout entropy, with a full-support converse. -/

import D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability

/- Library-search audit trail (2026-08-24):
   * The exact repository primitives `futureReadoutWord`, `nextReadoutJointLaw`,
     `conditionalEntropy`, and `pushforward` are imported rather than redeclared.
   * Exact public hits `conditional_entropy_eq_zero_of_point_mass_on_support` and
     `point_mass_on_support_of_conditional_entropy_eq_zero` are applied below.
   * The same imported module has a private fixed-depth graph equivalence, so it
     cannot be referenced by a deposit module; its public result identifies only
     the infima of the stable-depth and entropy-zero sets.
   * Searches in pinned Mathlib and across the entropy, observer, and concept-dynamics
     families found no public fixed-depth theorem with both directions. Pinned Mathlib
     has no matching finite real-valued conditional-entropy API.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Entropy.Observation.StableWindowConditionalEntropy

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.ConditionalEntropyEquality
open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability

private theorem graph_joint_marginal {X A B : Type*}
    [Fintype X] [Fintype B]
    (mass : X -> Real) (key : X -> A) (value : X -> B) :
    marginal (pushforward (fun x => (key x, value x)) mass) =
      pushforward key mass := by
  classical
  funext a
  simp only [marginal, pushforward]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hkey : key x = a
  · simp [hkey]
  · simp [hkey]

private theorem pushforward_apply_pos {X Z : Type*} [Fintype X]
    (mass : X -> Real) (map : X -> Z) (positive : forall x, 0 < mass x)
    (x : X) :
    0 < pushforward map mass (map x) := by
  classical
  simp only [pushforward]
  let term : X -> Real := fun x' => if map x' = map x then mass x' else 0
  change 0 < ∑ x', term x'
  have hx : term x = mass x := by simp [term]
  have hle : term x <= ∑ x', term x' := by
    simpa using
      (Finset.single_le_sum
        (s := Finset.univ)
        (f := term)
        (fun x' _ => by
          by_cases h : map x' = map x <;> simp [term, h, (positive x').le])
        (Finset.mem_univ x))
  rw [hx] at hle
  exact lt_of_lt_of_le (positive x) hle

private theorem graph_entropy_zero_of_fiber_constant {X A B : Type*}
    [Fintype X] [Fintype A] [Fintype B]
    (mass : X -> Real) (key : X -> A) (value : X -> B)
    (constant : forall x x', key x = key x' -> value x = value x') :
    conditionalEntropy (pushforward (fun x => (key x, value x)) mass) = 0 := by
  classical
  let joint : A × B -> Real := pushforward (fun x => (key x, value x)) mass
  apply conditional_entropy_eq_zero_of_point_mass_on_support joint
  intro a hmarginal
  have hexists : exists x, key x = a := by
    by_contra hnone
    push Not at hnone
    apply hmarginal
    rw [graph_joint_marginal mass key value]
    simp only [pushforward]
    apply Finset.sum_eq_zero
    intro x _
    simp [hnone x]
  obtain ⟨x0, hx0⟩ := hexists
  refine ⟨value x0, ?_⟩
  funext b
  rw [conditional]
  by_cases hb : b = value x0
  · subst b
    have hcell : joint (a, value x0) = marginal joint a := by
      rw [graph_joint_marginal mass key value]
      simp only [joint, pushforward]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : key x = a
      · have hvalue : value x = value x0 :=
          constant x x0 (hx.trans hx0.symm)
        simp [hx, hvalue]
      · simp [hx]
    simp [hcell, hmarginal]
  · have hcell : joint (a, b) = 0 := by
      simp only [joint, pushforward]
      apply Finset.sum_eq_zero
      intro x _
      by_cases hx : key x = a
      · have hvalue : value x = value x0 :=
          constant x x0 (hx.trans hx0.symm)
        simp [hx, hvalue, Ne.symm hb]
      · simp [hx]
    simp [hcell, hb]

private theorem fiber_constant_of_graph_entropy_zero {X A B : Type*}
    [Fintype X] [Fintype A] [Fintype B]
    (mass : X -> Real) (key : X -> A) (value : X -> B)
    (positive : forall x, 0 < mass x)
    (entropyZero :
      conditionalEntropy (pushforward (fun x => (key x, value x)) mass) = 0) :
    forall x x', key x = key x' -> value x = value x' := by
  classical
  let joint : A × B -> Real := pushforward (fun x => (key x, value x)) mass
  have jointNonnegative : forall z, 0 <= joint z := by
    intro z
    simp only [joint, pushforward]
    exact Finset.sum_nonneg fun x _ => by
      by_cases h : (key x, value x) = z <;> simp [h, (positive x).le]
  have pointMass :=
    point_mass_on_support_of_conditional_entropy_eq_zero
      joint jointNonnegative entropyZero
  intro x x' hkey
  have marginalNonzero : marginal joint (key x) ≠ 0 := by
    rw [graph_joint_marginal mass key value]
    exact (pushforward_apply_pos mass key positive x).ne'
  obtain ⟨b, hb⟩ := pointMass (key x) marginalNonzero
  have conditionalXNonzero : conditional joint (key x) (value x) ≠ 0 := by
    rw [conditional]
    exact div_ne_zero
      (pushforward_apply_pos mass (fun y => (key y, value y)) positive x).ne'
      marginalNonzero
  have conditionalX'Nonzero : conditional joint (key x) (value x') ≠ 0 := by
    rw [conditional]
    have hcell : 0 < joint (key x, value x') := by
      change 0 < pushforward (fun y => (key y, value y)) mass (key x, value x')
      simpa [hkey] using
        pushforward_apply_pos mass (fun y => (key y, value y)) positive x'
    exact div_ne_zero hcell.ne' marginalNonzero
  have hx : value x = b := by
    by_contra hne
    have h := congrFun hb (value x)
    rw [if_neg hne] at h
    exact conditionalXNonzero h
  have hx' : value x' = b := by
    by_contra hne
    have h := congrFun hb (value x')
    rw [if_neg hne] at h
    exact conditionalX'Nonzero h
  exact hx.trans hx'.symm

private theorem kernel_eq_next_of_next_readout_constant {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) (depth : Nat)
    (constant : forall y y',
      futureReadoutWord update readout depth y =
          futureReadoutWord update readout depth y' ->
        readout ((update^[depth + 1]) y) =
          readout ((update^[depth + 1]) y')) :
    Setoid.ker (futureReadoutWord update readout depth) =
      Setoid.ker (futureReadoutWord update readout (depth + 1)) := by
  apply Setoid.ext
  intro y y'
  constructor
  · intro hword
    funext k
    by_cases hk : k.val < depth + 1
    · let j : Fin (depth + 1) := ⟨k.val, hk⟩
      simpa [j, futureReadoutWord] using congrFun hword j
    · have hkValue : k.val = depth + 1 := by omega
      simpa [futureReadoutWord, hkValue] using constant y y' hword
  · intro hword
    funext k
    simpa [futureReadoutWord] using congrFun hword k.castSucc

/-- Stability of the depth-`n` observation kernel makes the next observation
deterministic given the observed word for every initial distribution. Conversely,
one full-support initial distribution with zero conditional entropy forces the two
consecutive observation kernels to be equal. -/
theorem stable_window_conditional_entropy {Y O : Type*}
    [Fintype Y] [Fintype O]
    (update : Y -> Y) (readout : Y -> O) (depth : Nat) :
    (Setoid.ker (futureReadoutWord update readout depth) =
        Setoid.ker (futureReadoutWord update readout (depth + 1)) ->
      forall initial : Y -> Real,
        ((forall y, 0 <= initial y) ∧ ∑ y, initial y = 1) ->
        conditionalEntropy (nextReadoutJointLaw update readout initial depth) = 0) ∧
    (forall initial : Y -> Real,
      ((forall y, 0 < initial y) ∧ ∑ y, initial y = 1) ->
      conditionalEntropy (nextReadoutJointLaw update readout initial depth) = 0 ->
      Setoid.ker (futureReadoutWord update readout depth) =
        Setoid.ker (futureReadoutWord update readout (depth + 1))) := by
  constructor
  · intro stable initial _initialLaw
    have constant : forall y y',
        futureReadoutWord update readout depth y =
            futureReadoutWord update readout depth y' ->
          readout ((update^[depth + 1]) y) =
            readout ((update^[depth + 1]) y') := by
      intro y y' hword
      have hnext :
          futureReadoutWord update readout (depth + 1) y =
            futureReadoutWord update readout (depth + 1) y' := by
        change Setoid.ker (futureReadoutWord update readout (depth + 1)) y y'
        rw [← stable]
        exact hword
      simpa [futureReadoutWord] using congrFun hnext (Fin.last (depth + 1))
    exact graph_entropy_zero_of_fiber_constant initial
      (futureReadoutWord update readout depth)
      (fun y => readout ((update^[depth + 1]) y)) constant
  · intro initial initialLaw entropyZero
    have constant := fiber_constant_of_graph_entropy_zero initial
      (futureReadoutWord update readout depth)
      (fun y => readout ((update^[depth + 1]) y)) initialLaw.1 entropyZero
    exact kernel_eq_next_of_next_readout_constant update readout depth constant

#print axioms stable_window_conditional_entropy

end D5.S3.Entropy.Observation.StableWindowConditionalEntropy
