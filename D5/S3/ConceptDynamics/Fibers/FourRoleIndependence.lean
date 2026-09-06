/- GID: D5/S3/ConceptDynamics/Fibers/FourRoleIndependence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Fibers/FourRoleIndependence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Cut, flow, admissibility, and anchor are independent Boolean model coordinates. -/

import Mathlib.Data.Bool.Basic

/- Library-search audit trail (2026-09-04):
   * Exact-name and theorem-body searches for four-role independence, cut/flow/admit/anchor,
     and Boolean coordinate countermodels found no D5 theorem with the four requested rows.
     `ObserverConceptReadoutCorrespondence` is adjacent: it shows that a joint-readout kernel
     forgets admissibility, anchor, and coordinate decomposition, but it does not establish
     independent variation of CUT and FLOW or the four same-three/different-one models here.
   * Symbol and synonym searches covered `admissible`, `anchorAdmissible`, `readout`, `flow`,
     `kernel`, `fiber`, `independent`, and `non-determination`, including snake_case and camelCase.
   * Backfill residual and absorbed indexes contain this atom only as open, with no coverage GID;
     the digest and raw Lean declaration indexes contain no equivalent theorem.
   * Generalized searches for product-coordinate separation and observational forgetting found
     only the adjacent quotient theorem above, whose conclusion neither implies nor is implied
     by all four coordinate countermodels without new constructions.
   * The in-flight module and branch logs contain no candidate for this theorem, and the proposed
     module path is absent from `origin/dev`.
   * Pinned Mathlib provides Bool computation and function congruence, but no domain-specific
     four-role theorem. The proof therefore gives all four finite models explicitly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Fibers.FourRoleIndependence

/-- On the two-state Boolean carrier, each of CUT, FLOW, ADMIT, and ANCHOR can
vary while the other three coordinates are held fixed. In the admissibility row
both predicates accept the shared anchor; in the anchor row the shared predicate
accepts both anchors. -/
theorem four_role_independence :
    (exists cutFirst cutSecond flow : Bool -> Bool,
      exists admit : Bool -> Prop,
      exists anchor : Bool,
        cutFirst ≠ cutSecond /\ admit anchor) /\
    (exists cut flowFirst flowSecond : Bool -> Bool,
      exists admit : Bool -> Prop,
      exists anchor : Bool,
        flowFirst ≠ flowSecond /\ admit anchor) /\
    (exists cut flow : Bool -> Bool,
      exists admitFirst admitSecond : Bool -> Prop,
      exists anchor : Bool,
        admitFirst ≠ admitSecond /\ admitFirst anchor /\ admitSecond anchor) /\
    (exists cut flow : Bool -> Bool,
      exists admit : Bool -> Prop,
      exists anchorFirst anchorSecond : Bool,
        anchorFirst ≠ anchorSecond /\ admit anchorFirst /\ admit anchorSecond) := by
  constructor
  · refine ⟨id, (fun _ => false), id, (fun _ => True), false, ?_, True.intro⟩
    intro sameCut
    have impossible := congrFun sameCut true
    simp at impossible
  constructor
  · refine ⟨id, id, Bool.not, (fun _ => True), false, ?_, True.intro⟩
    intro sameFlow
    have impossible := congrFun sameFlow false
    simp at impossible
  constructor
  · refine ⟨id, id, (fun _ => True), (fun state => state = false), false, ?_,
      True.intro, rfl⟩
    intro sameAdmit
    have impossible := congrFun sameAdmit true
    simp at impossible
  · exact ⟨id, id, (fun _ => True), false, true, Bool.false_ne_true,
      True.intro, True.intro⟩

#print axioms four_role_independence

end D5.S3.ConceptDynamics.Fibers.FourRoleIndependence
