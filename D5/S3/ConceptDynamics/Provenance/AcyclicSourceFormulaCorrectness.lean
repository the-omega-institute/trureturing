/- GID: D5/S3/ConceptDynamics/Provenance/AcyclicSourceFormulaCorrectness
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Provenance/AcyclicSourceFormulaCorrectness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Acyclic source formulas hold exactly when a source-supported proof exists. -/

import D5.S3.ConceptDynamics.Provenance.FiniteProofGraphSourceSemantics

/- Library-search audit trail (2026-08-26):
   * The frozen `FiniteAcyclicProofGraph` rank certificate is imported and
     extended rather than copied into a sibling carrier.
   * Body-shape searches for source-labelled finite alternative-rule graphs,
     recursive source formulas, and supported derivations found no repository
     primitive; the only adjacent hit was the frozen edge/rank graph.
   * Pinned Mathlib contains undirected `SimpleGraph.IsAcyclic` and generic
     well-founded recursion, but no source-formula correctness theorem for
     conjunction within rules and disjunction across alternative rules. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Provenance.AcyclicSourceFormulaCorrectness

open D5.S3.ConceptDynamics.Provenance.FiniteProofGraphSourceSemantics

/-- A source proof graph adds direct source labels and finitely many alternative
rules to the canonical finite acyclic edge/rank carrier. Every premise of a
rule is an incoming edge, so the inherited rank orders all dependencies. -/
structure SourceProofGraph (Source : Type*) (n : Nat)
    extends FiniteAcyclicProofGraph n where
  sourceAt : Fin n -> Option Source
  rules : (conclusion : Fin n) ->
    Finset (Finset {premise : Fin n // edge premise conclusion})

/-- The monotone Boolean source formula: a conclusion is available directly
from an enabled source, or through one alternative rule whose conjunctive list
of premises all have true source formulas. -/
def sourceFormulaHolds {Source : Type*} [DecidableEq Source] {n : Nat}
    (graph : SourceProofGraph Source n) (available : Finset Source)
    (conclusion : Fin n) : Prop :=
  (exists source, graph.sourceAt conclusion = some source /\ source ∈ available) \/
    exists premises, premises ∈ graph.rules conclusion /\
      forall premise, premise ∈ premises ->
        sourceFormulaHolds graph available premise.1
termination_by graph.rank conclusion
decreasing_by
  exact graph.edge_increases premise.2

/-- An independent source-supported proof object. The `rule` constructor chooses
one alternative rule and requires a proof of every conjunctive premise. -/
inductive ValidSourceProof {Source : Type*} [DecidableEq Source] {n : Nat}
    (graph : SourceProofGraph Source n) (available : Finset Source) :
    Fin n -> Prop
  | source {conclusion source} :
      graph.sourceAt conclusion = some source ->
      source ∈ available ->
      ValidSourceProof graph available conclusion
  | rule {conclusion}
      (premises : Finset {premise : Fin n // graph.edge premise conclusion}) :
      premises ∈ graph.rules conclusion ->
      (forall premise, premise ∈ premises ->
        ValidSourceProof graph available premise.1) ->
      ValidSourceProof graph available conclusion

/-- On every finite acyclic rule graph and every available source set, the
recursive provenance formula is true exactly when there is a valid proof using
only those sources. -/
theorem source_formula_iff_valid_source_proof
    {Source : Type*} [DecidableEq Source] {n : Nat}
    (graph : SourceProofGraph Source n) (available : Finset Source)
    (conclusion : Fin n) :
    sourceFormulaHolds graph available conclusion <->
      ValidSourceProof graph available conclusion := by
  apply (InvImage.wf (fun vertex : Fin n => graph.rank vertex)
    Nat.lt_wfRel.wf).induction conclusion
  intro conclusion inductionHypothesis
  rw [sourceFormulaHolds]
  constructor
  · rintro (⟨source, hsource, havailable⟩ | ⟨premises, hrule, hpremises⟩)
    · exact ValidSourceProof.source hsource havailable
    · exact ValidSourceProof.rule premises hrule (fun premise hpremise =>
        (inductionHypothesis premise.1
          (graph.edge_increases premise.2)).mp
          (hpremises premise hpremise))
  · intro proof
    cases proof with
    | source hsource havailable =>
        exact Or.inl ⟨_, hsource, havailable⟩
    | rule premises hrule hpremises =>
        exact Or.inr ⟨premises, hrule, fun premise hpremise =>
          (inductionHypothesis premise.1
            (graph.edge_increases premise.2)).mpr
            (hpremises premise hpremise)⟩

#print axioms source_formula_iff_valid_source_proof

end D5.S3.ConceptDynamics.Provenance.AcyclicSourceFormulaCorrectness
