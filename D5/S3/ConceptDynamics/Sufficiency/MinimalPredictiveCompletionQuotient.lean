/- GID: D5/S3/ConceptDynamics/Sufficiency/MinimalPredictiveCompletionQuotient
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Sufficiency/MinimalPredictiveCompletionQuotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The quotient by the maximal forward congruence inside the readout kernel preserves the current readout, carries the update, and is coarsest because its projection factors through every quotient by a forward congruence inside that kernel; in the convention Refines coarse fine, the canonical projection is refined by every admissible quotient projection, and empty states, singleton outputs, identity updates, and constant readouts require no extra assumptions. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import D5.S3.Observer.Separation.CongruenceKernel
import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-24):
   * `rg -n -F 'minimal_predictive_completion_quotient' D5` returned no prior hit;
     the same fixed-string search in `Golden/Frozen/accepted` also returned no hit.
   * The four baseline modules in `ConceptDynamics/Sufficiency` were read by
     digest; none states that the congruence-kernel quotient is the coarsest
     admissible quotient.
   * Repository quotient searches found the public adjacent theorem
     `ControlQuotientUniversalMinimality.control_quotient_universal_minimality`;
     it concerns complete profiles for a monoid action, not this arbitrary unary
     update and its maximal forward congruence, so it is not an exact cover.
   * `PredictionCompletion` already defines the full-itinerary quotient, while
     `minimal_deterministic_completion` proves a stronger unique factor only for
     finite state types and surjective implementations. Neither states this
     unrestricted quotient consequence of `congruence_kernel_laws`.
   * The proof applies `Setoid.ker.iseqv`, `Quotient.lift`, `Quotient.map`, and the
     congruence, containment, and maximality branches of `congruence_kernel_laws`;
     it does not reprove any branch of that upstream theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Sufficiency.MinimalPredictiveCompletionQuotient

open Set
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.Observer.Separation.CongruenceKernel

/-- The kernel relation of the current readout. -/
def readoutRelation {X O : Type*} (q : X -> O) : StateRelation X :=
  {pair | q pair.1 = q pair.2}

/-- The readout kernel is an equivalence relation, including on empty state types. -/
theorem readout_relation_equivalence {X O : Type*} (q : X -> O) :
    Equivalence (fun x y => (x, y) ∈ readoutRelation q) := by
  exact (Setoid.ker q).iseqv

/-- The setoid whose relation is the maximal forward congruence in the readout kernel. -/
def predictiveSetoid {X O : Type*} (F : X -> X) (q : X -> O) : Setoid X where
  r x y := (x, y) ∈ congruenceKernel F (readoutRelation q)
  iseqv :=
    (congruence_kernel_laws F (readoutRelation q)
      (readout_relation_equivalence q)).1

/-- The minimal predictive completion `X / K_infinity`. -/
abbrev PredictiveQuotient {X O : Type*} (F : X -> X) (q : X -> O) :=
  Quotient (predictiveSetoid F q)

/-- The canonical projection from states to the minimal predictive completion. -/
def predictiveProjection {X O : Type*} (F : X -> X) (q : X -> O) :
    X -> PredictiveQuotient F q :=
  Quotient.mk _

/-- A setoid viewed as its binary state relation. -/
def setoidRelation {X : Type*} (S : Setoid X) : StateRelation X :=
  {pair | S.r pair.1 pair.2}

/-- The predictive quotient preserves the readout and carries the dynamics. Moreover,
its projection factors through every quotient by a forward congruence inside the
readout kernel, which is the quotient-language form of coarseness. -/
theorem minimal_predictive_completion_quotient {X O : Type*} (F : X -> X) (q : X -> O) :
    ∃ (qbar : PredictiveQuotient F q -> O)
      (Fbar : PredictiveQuotient F q -> PredictiveQuotient F q),
      q = qbar ∘ predictiveProjection F q ∧
      predictiveProjection F q ∘ F = Fbar ∘ predictiveProjection F q ∧
      ∀ S : Setoid X,
        TauCongruence F (setoidRelation S) ->
        setoidRelation S ⊆ readoutRelation q ->
        Refines (predictiveProjection F q) (Quotient.mk S) := by
  have laws :=
    congruence_kernel_laws F (readoutRelation q)
      (readout_relation_equivalence q)
  have congruence : TauCongruence F (congruenceKernel F (readoutRelation q)) :=
    laws.2.1
  have insideReadout : congruenceKernel F (readoutRelation q) ⊆ readoutRelation q :=
    laws.2.2.1
  have maximal : ∀ S : StateRelation X,
      TauCongruence F S -> S ⊆ readoutRelation q ->
        S ⊆ congruenceKernel F (readoutRelation q) :=
    laws.2.2.2.2.2.1
  let qbar : PredictiveQuotient F q -> O :=
    Quotient.lift q (by
      intro x y hxy
      exact insideReadout hxy)
  let Fbar : PredictiveQuotient F q -> PredictiveQuotient F q :=
    Quotient.map F (by
      intro x y hxy
      exact congruence hxy)
  refine ⟨qbar, Fbar, ?_, ?_, ?_⟩
  · funext x
    rfl
  · funext x
    rfl
  · intro S hcongruence hreadout
    let factor : Quotient S -> PredictiveQuotient F q :=
      Quotient.map id (by
        intro x y hxy
        exact maximal (setoidRelation S) hcongruence hreadout hxy)
    refine ⟨factor, ?_⟩
    funext x
    rfl

example :
    ∃ qbar : PredictiveQuotient id (fun b : Bool => b) -> Bool,
      (fun b : Bool => b) = qbar ∘ predictiveProjection id (fun b : Bool => b) := by
  obtain ⟨qbar, _Fbar, hreadout, _hdynamics, _hcoarsest⟩ :=
    minimal_predictive_completion_quotient id (fun b : Bool => b)
  exact ⟨qbar, hreadout⟩

example :
    ∃ qbar :
      PredictiveQuotient (id : Empty -> Empty) (@Empty.elim Unit) -> Unit,
      (@Empty.elim Unit) =
        qbar ∘ predictiveProjection id (@Empty.elim Unit) := by
  obtain ⟨qbar, _Fbar, hreadout, _hdynamics, _hcoarsest⟩ :=
    minimal_predictive_completion_quotient
      (id : Empty -> Empty) (@Empty.elim Unit)
  exact ⟨qbar, hreadout⟩

#print axioms minimal_predictive_completion_quotient

end D5.S3.ConceptDynamics.Sufficiency.MinimalPredictiveCompletionQuotient
