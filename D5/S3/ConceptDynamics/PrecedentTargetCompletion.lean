/- GID: D5/S3/ConceptDynamics/PrecedentTargetCompletion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/PrecedentTargetCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Target completion preserves cases without an independent permitted reason. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import Mathlib.Data.Set.Function

/- Library-search audit trail (2026-08-21):
   * Exact repository hit `concept_join_universal` supplies the canonical target
     factor through the product readout and is applied directly below.
   * Pinned Mathlib provides `Set.EqOn` in `Data.Set.Operations`; it is used for
     the source's old-case restriction. Its composition lemmas are adjacent but
     do not package the target-completion and independent-doctrine clauses.
   * `Function.factorsThrough_iff` is an adjacent factorization criterion, but
     the family's canonical `Refines` relation already owns that semantics.
   * Searches of D5, the active branch, and `origin/dev` for target completion,
     noncircular distinction, and the atom ID found no complete theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.PrecedentTargetCompletion

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- Completing an old fact readout with the new decision itself always yields a
formal decision rule compatible with every preserved old case. This formal
completion does not imply that a target-independent permitted fact readout
supplies a noncircular decision rule. -/
theorem target_completion_formal_distinction_not_noncircular :
    (∀ {X OldFact Verdict : Type*} (oldCases : Set X)
        (oldFact : Concept X OldFact) (oldDecision newDecision : X → Verdict),
      Set.EqOn newDecision oldDecision oldCases →
        ∃ decide : OldFact × Verdict → Verdict,
          newDecision = decide ∘ conceptJoin oldFact newDecision ∧
          Set.EqOn (decide ∘ conceptJoin oldFact newDecision)
            oldDecision oldCases) ∧
      ∃ doctrine : Set (Concept Bool Bool),
        (fun _ : Bool => false) ∈ doctrine ∧
        (∀ fact ∈ doctrine, fact false = fact true) ∧
        Set.EqOn (id : Bool → Bool) (fun _ : Bool => false) {false} ∧
        (∃ decide : Bool × Bool → Bool,
          (id : Bool → Bool) =
            decide ∘ conceptJoin (fun _ : Bool => false) id ∧
          Set.EqOn
            (decide ∘ conceptJoin (fun _ : Bool => false) id)
            (fun _ : Bool => false) {false}) ∧
        (¬∃ fact : Concept Bool Bool,
          fact ∈ doctrine ∧
            Refines (id : Bool → Bool)
              (conceptJoin (fun _ : Bool => false) fact)) ∧
        ¬((Set.EqOn (id : Bool → Bool) (fun _ : Bool => false) {false} ∧
            ∃ decide : Bool × Bool → Bool,
              (id : Bool → Bool) =
                decide ∘ conceptJoin (fun _ : Bool => false) id ∧
              Set.EqOn
                (decide ∘ conceptJoin (fun _ : Bool => false) id)
                (fun _ : Bool => false) {false}) →
          ∃ fact : Concept Bool Bool,
            fact ∈ doctrine ∧
              Refines (id : Bool → Bool)
                (conceptJoin (fun _ : Bool => false) fact)) := by
  constructor
  · intro X OldFact Verdict oldCases oldFact oldDecision newDecision hpreserved
    rcases (concept_join_universal oldFact newDecision newDecision).2.1 with
      ⟨decide, hdecide⟩
    refine ⟨decide, hdecide, ?_⟩
    intro state hstate
    calc
      (decide ∘ conceptJoin oldFact newDecision) state = newDecision state := by
        exact (congrFun hdecide state).symm
      _ = oldDecision state := hpreserved hstate
  · let doctrine : Set (Concept Bool Bool) :=
      {fact | fact false = fact true}
    have hpreserved :
        Set.EqOn (id : Bool → Bool) (fun _ : Bool => false) {false} := by
      intro state hstate
      simp only [Set.mem_singleton_iff] at hstate
      subst state
      rfl
    have hformal :
        ∃ decide : Bool × Bool → Bool,
          (id : Bool → Bool) =
            decide ∘ conceptJoin (fun _ : Bool => false) id ∧
          Set.EqOn
            (decide ∘ conceptJoin (fun _ : Bool => false) id)
            (fun _ : Bool => false) {false} := by
      rcases (concept_join_universal
        (fun _ : Bool => false) id id).2.1 with ⟨decide, hdecide⟩
      refine ⟨decide, hdecide, ?_⟩
      intro state hstate
      calc
        (decide ∘ conceptJoin (fun _ : Bool => false) id) state =
            (id : Bool → Bool) state := by
          exact (congrFun hdecide state).symm
        _ = (fun _ : Bool => false) state := hpreserved hstate
    have hnoLegal :
        ¬∃ fact : Concept Bool Bool,
          fact ∈ doctrine ∧
            Refines (id : Bool → Bool)
              (conceptJoin (fun _ : Bool => false) fact) := by
      rintro ⟨fact, hfact, decide, hdecide⟩
      have hconstant : fact false = fact true := hfact
      have hjoin :
          conceptJoin (fun _ : Bool => false) fact false =
            conceptJoin (fun _ : Bool => false) fact true := by
        change (false, fact false) = (false, fact true)
        exact Prod.ext rfl hconstant
      have hfalse := congrFun hdecide false
      have htrue := congrFun hdecide true
      unfold Function.comp at hfalse htrue
      apply Bool.false_ne_true
      calc
        false = decide (conceptJoin (fun _ : Bool => false) fact false) := by
          simpa only [id_eq] using hfalse
        _ = decide (conceptJoin (fun _ : Bool => false) fact true) :=
          congrArg decide hjoin
        _ = true := by
          simpa only [id_eq] using htrue.symm
    refine ⟨doctrine, ?_, ?_, hpreserved, hformal, hnoLegal, ?_⟩
    · rfl
    · intro fact hfact
      exact hfact
    · intro himplication
      exact hnoLegal (himplication ⟨hpreserved, hformal⟩)

/-- The concrete case domain used by the countermodel is inhabited. -/
example : Bool := false

/-- The preservation premise used by the countermodel is satisfiable. -/
example : Set.EqOn (id : Bool → Bool) (fun _ : Bool => false) {false} := by
  intro state hstate
  simp only [Set.mem_singleton_iff] at hstate
  subst state
  rfl

#print axioms target_completion_formal_distinction_not_noncircular

end D5.S3.ConceptDynamics.PrecedentTargetCompletion
