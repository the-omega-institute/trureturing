/- GID: D5/S3/ConceptDynamics/CIRPT/SemanticIntegrity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/CIRPT/SemanticIntegrity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Constant readouts, full-domain admission, and erased anchors preserve semantics. -/

import D5.S3.ConceptDynamics.CIRPT.RoleSignature

/- Library-search audit trail (2026-09-04):
   * Repository searches for constant and universal kernels, full-domain
     admission, certificate anchors, atom insertion, and unchanged
     off-diagonal domains found no existing declaration with this API.
   * Exact frozen hits `admitKernel_relation_iff_bool_readout`,
     `anchorKernel_relation_iff_bool_readout`, and
     `PackedObserver.toPrimitiveAtom_relation_iff` are applied below rather
     than reproved. Exact hit `offDiagonalPairs` is reused from its canonical
     owner `RoleSignature`.
   * Pinned Mathlib searches for constant `Setoid.ker` and universal-kernel
     lemmas found no matching packaged result. Standard `funext`, `propext`,
     and proof irrelevance suffice for the two kernel equalities. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.CIRPT

universe u v w

/-- A finite bundle whose atoms are CUTs of constant readouts. -/
def constantCutBundle {X : Type u} {I : Type v} {B : Type w}
    [Fintype I] [DecidableEq I] [DecidableEq B]
    (value : I -> B) : PrimitiveBundle X where
  Index := I
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  atom i :=
    { axis := .cut
      kernel := cutKernel (fun _ : X => value i) }

/-- CIRPT-IE-021: a constant truth readout has the universal kernel. -/
theorem closed_truth_readout_has_universal_kernel
    {X : Type u} {B : Type v} [DecidableEq B] (constant : B) (x y : X) :
    (cutKernel (fun _ : X => constant)).relation x y := by
  rfl

/-- A bundle made entirely from constant CUTs agrees on every pair. -/
theorem constant_cut_bundle_has_universal_agreement
    {X : Type u} {I : Type v} {B : Type w}
    [Fintype I] [DecidableEq I] [DecidableEq B]
    (value : I -> B) (x y : X) :
    (constantCutBundle (X := X) value).agrees x y := by
  intro i
  exact closed_truth_readout_has_universal_kernel (value i) x y

/-- Insert one atom without changing the carrier or the old atom indices. -/
def bundleWithAtom {X : Type u} (bundle : PrimitiveBundle.{u, v} X)
    (extra : PrimitiveAtom X) : PrimitiveBundle.{u, v} X := by
  let _ := bundle.indexFintype
  let _ := bundle.indexDecidableEq
  exact
    { Index := Option bundle.Index
      indexFintype := inferInstance
      indexDecidableEq := inferInstance
      atom
        | none => extra
        | some i => bundle.atom i }

private theorem DecidableKernel.eq_of_relation_eq
    {X : Type u} (first second : DecidableKernel X)
    (relationEq : first.relation = second.relation) : first = second := by
  cases first with
  | mk firstRelation firstEquivalence firstDecision =>
    cases second with
    | mk secondRelation secondEquivalence secondDecision =>
      simp only at relationEq
      subst secondRelation
      have equivalenceEq : firstEquivalence = secondEquivalence :=
        Subsingleton.elim _ _
      subst secondEquivalence
      have decisionEq : firstDecision = secondDecision := Subsingleton.elim _ _
      subst secondDecision
      rfl

/-- CIRPT-IE-020: ADMIT is exactly the CUT of its Boolean code. -/
theorem full_domain_admit_encoding
    {X : Type u} (admit : X -> Prop) [DecidablePred admit] :
    admitKernel admit = cutKernel (fun x => decide (admit x)) := by
  apply DecidableKernel.eq_of_relation_eq
  funext x y
  apply propext
  exact admitKernel_relation_iff_bool_readout admit x y

/-- Adding an ADMIT atom cannot create a newly agreeing pair. -/
theorem adding_admit_atom_cannot_increase_agreement
    {X : Type u} (bundle : PrimitiveBundle.{u, v} X)
    (admit : X -> Prop) [DecidablePred admit] (x y : X) :
    (bundleWithAtom bundle { axis := .admit, kernel := admitKernel admit }).agrees x y ->
      bundle.agrees x y := by
  intro extended i
  exact extended (some i)

/-- ADMIT changes agreement only; its insertion leaves the full finite
off-diagonal carrier domain untouched. -/
theorem admit_atom_preserves_offDiagonalPairs
    {X : Type u} [Fintype X] [DecidableEq X]
    (bundle : PrimitiveBundle.{u, v} X)
    (admit : X -> Prop) [DecidablePred admit] :
    offDiagonalPairs X = offDiagonalPairs X /\
      forall pair, pair ∈ offDiagonalPairs X ->
        (bundleWithAtom bundle { axis := .admit, kernel := admitKernel admit }).agrees
            pair.1 pair.2 ->
          bundle.agrees pair.1 pair.2 := by
  refine ⟨rfl, ?_⟩
  intro pair _ extended
  exact adding_admit_atom_cannot_increase_agreement bundle admit pair.1 pair.2 extended

/-- CIRPT-IE-019: an object anchor is only the Boolean equality readout at
the anchored object; no certificate is retained in its kernel. -/
theorem certificate_anchor_erasure
    {X : Type u} [DecidableEq X] (anchor : X) :
    (anchorKernel anchor).relation =
      Setoid.ker (fun state => decide (state = anchor)) := by
  funext x y
  apply propext
  exact anchorKernel_relation_iff_bool_readout anchor x y

/-- A packed observer constant on the carrier contributes a universal kernel,
including when its readout was obtained from proof data. -/
theorem constant_packed_observer_has_universal_kernel
    {X : Type u} (axis : PrimitiveAxis) (observer : PackedObserver X)
    (constant : observer.Output)
    (isConstant : forall x, observer.observe x = constant) (x y : X) :
    ((observer.toPrimitiveAtom axis).kernel.relation x y) := by
  apply (observer.toPrimitiveAtom_relation_iff axis x y).2
  exact (isConstant x).trans (isConstant y).symm

/-- Engine bridge: inserting an atom with a universal kernel does not change
bundle agreement. -/
theorem universal_kernel_atom_does_not_change_agrees
    {X : Type u} (bundle : PrimitiveBundle.{u, v} X)
    (atom : PrimitiveAtom X)
    (universal : forall x y, atom.kernel.relation x y) (x y : X) :
    (bundleWithAtom bundle atom).agrees x y <-> bundle.agrees x y := by
  constructor
  · intro extended i
    exact extended (some i)
  · intro original index
    cases index with
    | none => exact universal x y
    | some i => exact original i

private def constantProofObserver : PackedObserver (Bool × Bool) where
  Output := Bool
  outputDecidableEq := inferInstance
  observe := fun _ => true

example : (cutKernel (fun _ : Bool => true)).relation false true := by decide

example :
    (constantCutBundle (X := Bool × Bool) (fun bit : Bool => bit)).agrees
      (false, false) (true, true) := by decide

example :
    (admitKernel (fun state : Bool × Bool => state.1 = true)).relation
      (false, false) (false, true) := by decide

example :
    not ((anchorKernel true).relation false true) := by decide

example :
    ((constantProofObserver.toPrimitiveAtom .anchor).kernel.relation
      (false, false) (true, true)) := by decide

end D5.S3.ConceptDynamics.CIRPT
