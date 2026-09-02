/- GID: D5/S3/ConceptDynamics/TwoBitJointCommonKnowledgeSeparation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/TwoBitJointCommonKnowledgeSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Two coordinate observers pool all knowledge but share only constants. -/

import D5.S3.ConceptDynamics.Refinement.ConceptKernelOrderDuality

/- Library-search audit trail (2026-09-02):
   * Repository searches for two-bit pooled versus common knowledge, coordinate
     kernels, common coarsenings, and class-constant observable algebras found
     no theorem proving this concrete four-state separation.
   * `concept_kernel_order_duality` is the generalized repository owner: joint
     readouts intersect kernels, while common coarsening takes the equivalence
     closure of their union. It is applied directly below.
   * `finite_partition_algebra_order_reversal` was inspected and is the exact
     general owner for reverse inclusion of finite class-constant algebras, but
     it does not identify the two endpoint algebras in this example.
   * Pinned Mathlib supplies the `Setoid` complete lattice, `Setoid.ker_mk_eq`,
     and `Setoid.sup_eq_eqvGen`; no exact concrete theorem was found.
   * The digestion receipt and digest indexes, generalized owners, spelling
     variants, and every in-flight `origin/lane/math/*` branch were checked.
     None contains this two-bit theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.TwoBitJointCommonKnowledgeSeparation

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Refinement.ConceptKernelOrderDuality

/-- On the four-state Boolean square, pooling the two coordinate readouts has
equality kernel and therefore exposes every Boolean-valued event. Their common
coarsening has the universal kernel and therefore exposes only constants. -/
theorem two_bit_joint_common_knowledge_separation :
    let X := Bool × Bool
    let first : Concept X Bool := Prod.fst
    let second : Concept X Bool := Prod.snd
    let pooledKernel := Setoid.ker (conceptJoin first second)
    let commonKernel := Setoid.ker (commonCoarsening first second)
    pooledKernel = ⊥ ∧
      commonKernel = ⊤ ∧
      ({f : X → Bool | ∀ ⦃x y⦄, pooledKernel x y → f x = f y} : Set (X → Bool)) =
        Set.univ ∧
      ({f : X → Bool | ∀ ⦃x y⦄, commonKernel x y → f x = f y} :
          Set (X → Bool)) =
        Set.range (fun constant : Bool => fun _ : X => constant) := by
  dsimp only
  have pooledFormula :
      Setoid.ker (conceptJoin (Prod.fst : Bool × Bool → Bool) Prod.snd) =
        Setoid.ker (Prod.fst : Bool × Bool → Bool) ⊓
          Setoid.ker (Prod.snd : Bool × Bool → Bool) :=
    (concept_kernel_order_duality (Bool × Bool)).2.2.1 Prod.fst Prod.snd
  have pooledBottom :
      Setoid.ker (conceptJoin (Prod.fst : Bool × Bool → Bool) Prod.snd) = ⊥ := by
    rw [pooledFormula]
    apply Setoid.ext
    intro x y
    simp only [Setoid.inf_iff_and, Setoid.ker_def]
    exact Prod.ext_iff.symm
  have commonFormula :
      Setoid.ker
          (commonCoarsening (Prod.fst : Bool × Bool → Bool) Prod.snd) =
        Relation.EqvGen.setoid
          (fun x y => Setoid.ker (Prod.fst : Bool × Bool → Bool) x y ∨
            Setoid.ker (Prod.snd : Bool × Bool → Bool) x y) :=
    (concept_kernel_order_duality (Bool × Bool)).2.2.2 Prod.fst Prod.snd
  have commonSup :
      Setoid.ker
          (commonCoarsening (Prod.fst : Bool × Bool → Bool) Prod.snd) =
        Setoid.ker (Prod.fst : Bool × Bool → Bool) ⊔
          Setoid.ker (Prod.snd : Bool × Bool → Bool) :=
    commonFormula.trans
      (Setoid.sup_eq_eqvGen (Setoid.ker (Prod.fst : Bool × Bool → Bool))
        (Setoid.ker (Prod.snd : Bool × Bool → Bool))).symm
  have commonTop :
      Setoid.ker
          (commonCoarsening (Prod.fst : Bool × Bool → Bool) Prod.snd) = ⊤ := by
    rw [commonSup]
    apply top_unique
    intro x y _
    have firstStep :
        Setoid.ker (Prod.fst : Bool × Bool → Bool) x (x.1, y.2) := rfl
    have secondStep :
        Setoid.ker (Prod.snd : Bool × Bool → Bool) (x.1, y.2) y := rfl
    exact (Setoid.ker (Prod.fst : Bool × Bool → Bool) ⊔
        Setoid.ker (Prod.snd : Bool × Bool → Bool)).trans'
      ((show Setoid.ker (Prod.fst : Bool × Bool → Bool) ≤
        Setoid.ker Prod.fst ⊔ Setoid.ker Prod.snd from le_sup_left) firstStep)
      ((show Setoid.ker (Prod.snd : Bool × Bool → Bool) ≤
        Setoid.ker Prod.fst ⊔ Setoid.ker Prod.snd from le_sup_right) secondStep)
  refine ⟨pooledBottom, commonTop, ?_, ?_⟩
  · rw [pooledBottom]
    ext f
    constructor
    · intro _
      exact Set.mem_univ f
    · intro _ x y hxy
      change x = y at hxy
      exact congrArg f hxy
  · rw [commonTop]
    ext f
    constructor
    · intro constantOnClasses
      refine ⟨f (false, false), ?_⟩
      funext x
      exact constantOnClasses
        (show (⊤ : Setoid (Bool × Bool)) (false, false) x from trivial)
    · rintro ⟨constant, rfl⟩ x y _
      rfl

#print axioms two_bit_joint_common_knowledge_separation

end D5.S3.ConceptDynamics.TwoBitJointCommonKnowledgeSeparation
