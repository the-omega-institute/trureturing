/- GID: D5/S3/ConceptDynamics/Sufficiency/PredictiveCompletionMonotone
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Sufficiency/PredictiveCompletionMonotone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Completion preserves refinement for empty, singleton, constant, identity, zero-step. -/

import D5.S3.ConceptDynamics.Sufficiency.MinimalPredictiveCompletionQuotient

/- Library-search audit trail (2026-08-25): `rg -n 'congruenceKernel' D5` found
   the private kernel monotonicity proof and its public branch in
   `congruence_kernel_laws`; quotient equality uses the pinned `Quotient.exact`
   and `Quotient.sound`. No prior predictive-completion monotonicity theorem was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Sufficiency.PredictiveCompletionMonotone

open Set
open D5.S3.ConceptDynamics.Sufficiency.MinimalPredictiveCompletionQuotient
open D5.S3.Observer.Separation.CongruenceKernel

/-- Refining the readout cannot make predictive completion less informative. -/
theorem predictive_completion_monotone {X O P : Type*}
    (F : X -> X) (q : X -> O) (r : X -> P)
    (hrefine : ∀ x y, r x = r y -> q x = q y) :
    ∀ x y, predictiveProjection F r x = predictiveProjection F r y ->
      predictiveProjection F q x = predictiveProjection F q y := by
  intro x y hxy
  have hreadout : readoutRelation r ⊆ readoutRelation q := by
    intro pair hpair
    exact hrefine pair.1 pair.2 hpair
  have hkernel : congruenceKernel F (readoutRelation r) ⊆
      congruenceKernel F (readoutRelation q) := by
    exact (congruence_kernel_laws F (readoutRelation q)
      (readout_relation_equivalence q)).2.2.2.1 _ hreadout
  have hkernelR : (x, y) ∈ congruenceKernel F (readoutRelation r) := by
    exact Quotient.exact hxy
  apply Quotient.sound
  exact hkernel hkernelR
#print axioms predictive_completion_monotone

/-- The refinement premise is necessary: a coarse constant readout need not
    determine a finer identity readout on a two-state system. -/
theorem refinement_hypothesis_is_necessary :
    ¬ (∀ x y : Bool,
      predictiveProjection (id : Bool -> Bool) (fun _ : Bool => Unit.unit) x =
          predictiveProjection (id : Bool -> Bool) (fun _ : Bool => Unit.unit) y ->
        predictiveProjection (id : Bool -> Bool) (fun b : Bool => b) x =
          predictiveProjection (id : Bool -> Bool) (fun b : Bool => b) y) := by
  intro h
  have hconstant :
      predictiveProjection (id : Bool -> Bool) (fun _ : Bool => Unit.unit) true =
        predictiveProjection (id : Bool -> Bool) (fun _ : Bool => Unit.unit) false := by
    apply Quotient.sound
    intro _
    rfl
  have hidentity := h true false hconstant
  have hkernel :
      (true, false) ∈ congruenceKernel (id : Bool -> Bool)
        (readoutRelation (fun b : Bool => b)) :=
    Quotient.exact hidentity
  have hreadout : (true : Bool) = false := by
    simpa [congruenceKernel, readoutRelation] using hkernel 0
  exact Bool.noConfusion hreadout
#print axioms refinement_hypothesis_is_necessary

example :
    ∀ x y : Empty,
      predictiveProjection (id : Empty -> Empty) (@Empty.elim Unit) x =
          predictiveProjection (id : Empty -> Empty) (@Empty.elim Unit) y ->
        predictiveProjection (id : Empty -> Empty) (@Empty.elim Unit) x =
          predictiveProjection (id : Empty -> Empty) (@Empty.elim Unit) y := by
  exact predictive_completion_monotone id (@Empty.elim Unit) (@Empty.elim Unit)
    (by intro x; exact Empty.elim x)

example :
    ∀ x y : PUnit,
      predictiveProjection id (fun _ : PUnit => true) x =
          predictiveProjection id (fun _ : PUnit => true) y ->
        predictiveProjection id (fun _ : PUnit => false) x =
          predictiveProjection id (fun _ : PUnit => false) y := by
  exact predictive_completion_monotone id (fun _ : PUnit => false)
    (fun _ : PUnit => true) (by intro x y _; rfl)

example :
    ∀ x y : Bool,
      predictiveProjection (fun _ : Bool => false) (fun b : Bool => b) x =
          predictiveProjection (fun _ : Bool => false) (fun b : Bool => b) y ->
        predictiveProjection (fun _ : Bool => false) (fun _ : Bool => Unit.unit) x =
          predictiveProjection (fun _ : Bool => false) (fun _ : Bool => Unit.unit) y := by
  exact predictive_completion_monotone (fun _ : Bool => false)
    (fun _ : Bool => Unit.unit) (fun b : Bool => b) (by intro x y _; rfl)

example {X O : Type*} (q : X -> O) (x y : X)
    (h : (x, y) ∈ congruenceKernel (id : X -> X) (readoutRelation q)) :
    q x = q y := by
  simpa [congruenceKernel, readoutRelation] using h 0

end D5.S3.ConceptDynamics.Sufficiency.PredictiveCompletionMonotone
