/- GID: D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Joint faithfulness is equivalent to point separation and diagonal kernel intersection. -/

import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.TFAE

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'joint_faithfulness_tfae' D5 Golden/Frozen/accepted` found no
     existing declaration.
   * Structural repository searches found `ConceptKernelOrderDuality` for one
     readout's kernel order and `QuotientInvariantCoordinate` for one invariant
     on a quotient; neither covers a family, its kernel intersection, or the
     required constant-family counterexample. `CommutingProjectionFourSector`
     supplies the repository's direct `List.TFAE` proof pattern.
   * Pinned Mathlib searches found `funext_iff`, `Set.iInter_setOf`,
     `Setoid.injective_iff_ker_bot`, and `Function.Injective.comp`, but no theorem
     combining the three conditions here. The proof uses function and set
     extensionality together with indexed-intersection membership.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

universe u v w

/-- The single dependent readout assembled from an indexed concept family. -/
def jointReadout {I : Type u} {X : Type v} {V : I -> Type w}
    (q : forall i, X -> V i) : X -> forall i, V i :=
  fun x i => q i x

/-- The kernel of one member of a concept family, represented on pairs of states. -/
def conceptKernel {I : Type u} {X : Type v} {V : I -> Type w}
    (q : forall i, X -> V i) (i : I) : Set (X × X) :=
  {pair | q i pair.1 = q i pair.2}

/-- The states left indistinguishable by every member of a concept family. -/
def jointKernel {I : Type u} {X : Type v} {V : I -> Type w}
    (q : forall i, X -> V i) : Set (X × X) :=
  ⋂ i, conceptKernel q i

/-- The equality relation on a state space, represented as its diagonal set. -/
def diagonal (X : Type v) : Set (X × X) :=
  {pair | pair.1 = pair.2}

/-- A concept family is jointly faithful exactly when it separates every pair of
states, equivalently when the intersection of its kernels is the equality diagonal. -/
theorem joint_faithfulness_tfae {I : Type u} {X : Type v} {V : I -> Type w}
    (q : forall i, X -> V i) :
    List.TFAE
      [Function.Injective (jointReadout q),
        forall x y, (forall i, q i x = q i y) -> x = y,
        jointKernel q = diagonal X] := by
  tfae_have 1 → 2 := by
    intro injective x y indistinguishable
    apply injective
    funext i
    exact indistinguishable i
  tfae_have 2 → 1 := by
    intro separates x y hxy
    apply separates x y
    intro i
    exact congrFun hxy i
  tfae_have 2 → 3 := by
    intro separates
    ext pair
    simp only [jointKernel, conceptKernel, diagonal, Set.mem_iInter,
      Set.mem_setOf_eq]
    constructor
    · exact separates pair.1 pair.2
    · intro hpair i
      rw [hpair]
  tfae_have 3 → 2 := by
    intro hKernel x y indistinguishable
    have hPair : (x, y) ∈ jointKernel q := by
      apply Set.mem_iInter.2
      intro i
      exact indistinguishable i
    rw [hKernel] at hPair
    exact hPair
  tfae_finish

/-- A constant concept family on `Bool` witnesses that joint faithfulness is a
substantive condition rather than an unconditional logical law. -/
theorem constant_concept_family_not_jointly_faithful :
    ∃ q : forall _ : Unit, Bool -> Unit,
      (∃ x y, x ≠ y ∧ forall i, q i x = q i y) ∧
        ¬Function.Injective (jointReadout q) ∧
        ¬(forall x y, (forall i, q i x = q i y) -> x = y) ∧
        jointKernel q ≠ diagonal Bool := by
  let q : forall _ : Unit, Bool -> Unit := fun _ _ => ()
  have indistinguishable : forall i, q i false = q i true := by
    intro i
    rfl
  have distinct : false ≠ true := Bool.false_ne_true
  refine ⟨q, ⟨false, true, distinct, indistinguishable⟩, ?_, ?_, ?_⟩
  · intro injective
    apply distinct
    apply injective
    funext i
    exact indistinguishable i
  · intro separates
    exact distinct (separates false true indistinguishable)
  · intro hKernel
    have hPair : (false, true) ∈ jointKernel q := by
      apply Set.mem_iInter.2
      intro i
      exact indistinguishable i
    rw [hKernel] at hPair
    exact distinct hPair

example :
    List.TFAE
      [Function.Injective
          (jointReadout (fun _ : Unit => (id : Bool -> Bool))),
        forall x y : Bool, (forall _ : Unit, x = y) -> x = y,
        jointKernel (fun _ : Unit => (id : Bool -> Bool)) = diagonal Bool] := by
  simpa using
    (joint_faithfulness_tfae (fun _ : Unit => (id : Bool -> Bool)))

#print axioms joint_faithfulness_tfae

end D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
