/- GID: D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/CIRPT/PrimitiveKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Four decidable primitive roles expose equivalent relations and canonical Boolean readouts. -/

import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-09-04):
   * Repository searches for `PrimitiveAxis`, `DecidableKernel`, and the four
     constructor names found no existing declarations under `D5`.
   * The imported faithfulness module is the canonical owner of
     `conceptKernel`; its dependent-family signature is reused below with a
     singleton index rather than replaced by a second kernel definition.
   * Pinned Mathlib exact hits `Setoid.ker`, `Setoid.ker_def`,
     `Equivalence.comap`, and `decide_eq_decide`. They provide the equality
     kernels and Boolean reflection steps; no four-axis packaging theorem was
     found in Mathlib or the repository. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.CIRPT

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

universe u v w

/-- The four semantic roles whose observable content is represented by a kernel. -/
inductive PrimitiveAxis
  | cut
  | flow
  | admit
  | anchor
  deriving DecidableEq, Repr

/-- An equivalence relation together with a decision procedure for every pair. -/
structure DecidableKernel (X : Type u) where
  relation : X -> X -> Prop
  equivalence : Equivalence relation
  decidableRelation : DecidableRel relation

instance {X : Type u} (kernel : DecidableKernel X) : DecidableRel kernel.relation :=
  kernel.decidableRelation

/-- The kernel of a classifying readout. -/
def cutKernel {X : Type u} {B : Type v} [DecidableEq B]
    (q : X -> B) : DecidableKernel X where
  relation x y := q x = q y
  equivalence := eq_equivalence.comap q
  decidableRelation := fun _ _ => inferInstance

/-- The complete-output kernel of a one-step flow. -/
def flowKernel {X : Type u} {Y : Type v} [DecidableEq Y]
    (flow : X -> Y) : DecidableKernel X :=
  cutKernel flow

/-- The kernel that remembers only whether two states share an admission truth value. -/
def admitKernel {X : Type u} (admit : X -> Prop) [DecidablePred admit] :
    DecidableKernel X where
  relation x y := admit x <-> admit y
  equivalence := by
    refine ⟨fun _ => Iff.rfl, ?_, ?_⟩
    · intro x y hxy
      exact hxy.symm
    · intro x y z hxy hyz
      exact hxy.trans hyz
  decidableRelation := fun x y => inferInstance

/-- The kernel of the pointed predicate that tests equality with one anchor. -/
def anchorKernel {X : Type u} [DecidableEq X] (a : X) : DecidableKernel X where
  relation x y := (x = a) <-> (y = a)
  equivalence := by
    refine ⟨fun _ => Iff.rfl, ?_, ?_⟩
    · intro x y hxy
      exact hxy.symm
    · intro x y z hxy hyz
      exact hxy.trans hyz
  decidableRelation := fun x y => inferInstance

/-- CUT reflection: related states have exactly equal readout values. -/
@[simp] theorem cutKernel_relation_iff {X : Type u} {B : Type v} [DecidableEq B]
    (q : X -> B) (x y : X) :
    (cutKernel q).relation x y <-> q x = q y :=
  Iff.rfl

/-- FLOW reflection: related states have exactly equal flow outputs. -/
@[simp] theorem flowKernel_relation_iff {X : Type u} {Y : Type v} [DecidableEq Y]
    (flow : X -> Y) (x y : X) :
    (flowKernel flow).relation x y <-> flow x = flow y :=
  Iff.rfl

/-- ADMIT reflection: related states have the same admission truth value. -/
@[simp] theorem admitKernel_relation_iff {X : Type u} (admit : X -> Prop)
    [DecidablePred admit] (x y : X) :
    (admitKernel admit).relation x y <-> (admit x <-> admit y) :=
  Iff.rfl

/-- ANCHOR reflection: related states agree on equality with the anchor. -/
@[simp] theorem anchorKernel_relation_iff {X : Type u} [DecidableEq X]
    (a x y : X) :
    (anchorKernel a).relation x y <-> ((x = a) <-> (y = a)) :=
  Iff.rfl

/-- CIRPT-IE-001: all four primitive constructors produce equivalence relations. -/
theorem primitive_kernel_equivalence
    {X : Type u} {B : Type v} {Y : Type w}
    [DecidableEq B] [DecidableEq Y] [DecidableEq X]
    (q : X -> B) (flow : X -> Y) (admit : X -> Prop)
    [DecidablePred admit] (a : X) :
    Equivalence (cutKernel q).relation /\
      Equivalence (flowKernel flow).relation /\
      Equivalence (admitKernel admit).relation /\
      Equivalence (anchorKernel a).relation :=
  ⟨(cutKernel q).equivalence, (flowKernel flow).equivalence,
    (admitKernel admit).equivalence, (anchorKernel a).equivalence⟩

/-- A CUT relation is the canonical repository concept kernel for a singleton family. -/
theorem cutKernel_relation_eq_conceptKernel
    {X : Type u} {B : Type v} [DecidableEq B] (q : X -> B) :
    {pair : X × X | (cutKernel q).relation pair.1 pair.2} =
      conceptKernel (fun _ : Unit => q) () := by
  rfl

/-- The Boolean characteristic readout has exactly the ADMIT kernel. -/
theorem admitKernel_relation_iff_bool_readout
    {X : Type u} (admit : X -> Prop) [DecidablePred admit] (x y : X) :
    (admitKernel admit).relation x y <->
      Setoid.ker (fun state => decide (admit state)) x y := by
  change (admit x <-> admit y) <-> decide (admit x) = decide (admit y)
  exact decide_eq_decide.symm

/-- The Boolean pointed-equality readout has exactly the ANCHOR kernel. -/
theorem anchorKernel_relation_iff_bool_readout
    {X : Type u} [DecidableEq X] (a x y : X) :
    (anchorKernel a).relation x y <->
      Setoid.ker (fun state => decide (state = a)) x y := by
  change ((x = a) <-> (y = a)) <-> decide (x = a) = decide (y = a)
  exact decide_eq_decide.symm

end D5.S3.ConceptDynamics.CIRPT
