/- GID: D5/S3/ConceptDynamics/CIRPT/InformationEscape/PrimitiveBundle
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/CIRPT/InformationEscape/PrimitiveBundle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite primitive bundles compute their canonical joint kernel. -/

import D5.S3.ConceptDynamics.CIRPT.InformationEscape.QuotientCutNormalForm
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Fold

/- Library-search audit trail (2026-09-04):
   * Repository searches for `PrimitiveAtom`, `PrimitiveBundle`, `agreesB`,
     and the requested invariance theorem found no existing declarations.
   * The imported faithfulness owner supplies canonical dependent
     `jointKernel`; the imported quotient normal form supplies each atom's
     dependent quotient CUT. Both are reused in the bridge below.
   * The repository theorem `SensorFamilyKernelIntersection.
     joint_readout_kernel_eq_iInter` confirms the arbitrary-family set-kernel
     pattern. Pinned Mathlib supplies `Set.mem_iInter`, `List.all_eq_true`, and
     `Bool.eq_iff_iff`, but this pin has no `Finset.all`; the finite Boolean fold
     therefore uses the commutative `Finset.fold` characterization. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.CIRPT.InformationEscape

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

universe u v w

/-- One role-labelled primitive kernel on a common state space. -/
structure PrimitiveAtom (X : Type u) where
  axis : PrimitiveAxis
  kernel : DecidableKernel X

/-- A finite indexed family of primitive kernels on a common state space. -/
structure PrimitiveBundle (X : Type u) where
  Index : Type v
  indexFintype : Fintype Index
  indexDecidableEq : DecidableEq Index
  atom : Index -> PrimitiveAtom X

namespace PrimitiveBundle

/-- Two states agree for a bundle when every atom relates them. -/
def agrees {X : Type u} (b : PrimitiveBundle X) (x y : X) : Prop :=
  forall i, (b.atom i).kernel.relation x y

/-- Executable finite reflection of bundle agreement. -/
def agreesB {X : Type u} (b : PrimitiveBundle X) (x y : X) : Bool :=
  let _ := b.indexFintype
  let _ := b.indexDecidableEq
  Finset.fold (fun left right => left && right) true
    (fun i => decide ((b.atom i).kernel.relation x y)) Finset.univ

/-- The finite Boolean agreement test reflects propositional bundle agreement. -/
theorem agreesB_eq_true_iff {X : Type u} (b : PrimitiveBundle X) (x y : X) :
    b.agreesB x y = true <-> b.agrees x y := by
  let _ := b.indexFintype
  let _ := b.indexDecidableEq
  unfold agreesB agrees
  have foldCharacterization :=
    Finset.fold_op_rel_iff_and
      (op := fun left right : Bool => left && right)
      (r := fun _ actual : Bool => actual = true)
      (b := true)
      (f := fun i => decide ((b.atom i).kernel.relation x y))
      (s := Finset.univ) (c := true) (by
        intro expected left right
        simp)
  simpa using foldCharacterization

/-- Agreement inherited from a family of kernels is itself an equivalence relation. -/
theorem agrees_equivalence {X : Type u} (b : PrimitiveBundle X) :
    Equivalence b.agrees := by
  refine ⟨?_, ?_, ?_⟩
  · intro x i
    exact (b.atom i).kernel.equivalence.refl x
  · intro x y hxy i
    exact (b.atom i).kernel.equivalence.symm (hxy i)
  · intro x y z hxy hyz i
    exact (b.atom i).kernel.equivalence.trans (hxy i) (hyz i)

/-- The joint agreement relation, packaged as one decidable kernel. -/
def toKernel {X : Type u} (b : PrimitiveBundle X) : DecidableKernel X where
  relation := b.agrees
  equivalence := agrees_equivalence b
  decidableRelation := fun x y =>
    decidable_of_iff' (b.agreesB x y = true) (agreesB_eq_true_iff b x y).symm

/-- A bundle is nonempty exactly when its index type is inhabited. -/
def Nonempty {X : Type u} (b : PrimitiveBundle X) : Prop :=
  _root_.Nonempty b.Index

instance instDecidableNonempty {X : Type u} (b : PrimitiveBundle X) :
    Decidable b.Nonempty := by
  letI := b.indexFintype
  letI := b.indexDecidableEq
  apply decidable_of_iff' ((Finset.univ : Finset b.Index).Nonempty)
  constructor
  · rintro ⟨i⟩
    exact ⟨i, Finset.mem_univ i⟩
  · rintro ⟨i, _⟩
    exact ⟨i⟩

/-- CIRPT-IE-003: bundle agreement is the intersection of all atom kernels. -/
theorem primitive_bundle_joint_kernel {X : Type u} (b : PrimitiveBundle X) :
    {pair : X × X | b.agrees pair.1 pair.2} =
      ⋂ i, {pair : X × X | (b.atom i).kernel.relation pair.1 pair.2} := by
  ext pair
  simp only [Set.mem_ofPred_eq, Set.mem_iInter, agrees]

/-- Bundle agreement is membership in the canonical joint kernel of atom quotient CUTs. -/
theorem bundle_agrees_iff_jointKernel_quotientCuts
    {X : Type u} (b : PrimitiveBundle X) (x y : X) :
    b.agrees x y <->
      (x, y) ∈ jointKernel (fun i => (b.atom i).kernel.quotientCut) := by
  constructor
  · intro hagrees
    apply Set.mem_iInter.2
    intro i
    change (b.atom i).kernel.quotientCut x = (b.atom i).kernel.quotientCut y
    exact (quotient_cut_kernel_normal_form (b.atom i).kernel x y).1 (hagrees i)
  · intro hjoint i
    have hi := Set.mem_iInter.1 hjoint i
    change (b.atom i).kernel.quotientCut x =
      (b.atom i).kernel.quotientCut y at hi
    exact (quotient_cut_kernel_normal_form (b.atom i).kernel x y).2 hi

/-- CIRPT-IE-016: equal joint relations force equal logical and Boolean agreement. -/
theorem primitive_bundle_kernel_invariance
    {X : Type u} (first : PrimitiveBundle.{u, v} X)
    (second : PrimitiveBundle.{u, w} X)
    (sameKernel : forall x y,
      first.toKernel.relation x y <-> second.toKernel.relation x y) :
    (forall x y, first.agrees x y <-> second.agrees x y) /\
      (forall x y, first.agreesB x y = second.agreesB x y) := by
  have sameAgreement : forall x y, first.agrees x y <-> second.agrees x y := by
    intro x y
    exact sameKernel x y
  refine ⟨sameAgreement, ?_⟩
  intro x y
  apply Bool.eq_iff_iff.mpr
  rw [agreesB_eq_true_iff, agreesB_eq_true_iff]
  exact sameAgreement x y

end PrimitiveBundle

/-- A readout with its output type and decidable output equality packed together. -/
structure PackedObserver (X : Type u) where
  Output : Type v
  outputDecidableEq : DecidableEq Output
  observe : X -> Output

namespace PackedObserver

/-- Turn a packed readout into a role-labelled CUT atom. -/
def toPrimitiveAtom {X : Type u} (axis : PrimitiveAxis) (obs : PackedObserver X) :
    PrimitiveAtom X := by
  let _ := obs.outputDecidableEq
  exact ⟨axis, cutKernel obs.observe⟩

/-- A packed observer atom relates exactly the states with equal observations. -/
theorem toPrimitiveAtom_relation_iff {X : Type u} (axis : PrimitiveAxis)
    (obs : PackedObserver X) (x y : X) :
    ((toPrimitiveAtom axis obs).kernel.relation x y <->
      obs.observe x = obs.observe y) := by
  let _ := obs.outputDecidableEq
  exact cutKernel_relation_iff obs.observe x y

end PackedObserver

end D5.S3.ConceptDynamics.CIRPT.InformationEscape
