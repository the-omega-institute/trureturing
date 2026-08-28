/- GID: D5/S3/ConceptDynamics/DefinitionEscapeSemantics/SemanticStrictSubsetWitness
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeSemantics/SemanticStrictSubsetWitness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Semantic strict expansion exposes a witness in the new-domain difference. -/

/- Library-search audit trail (2026-08-29):
   * Exact repository search
     `git grep -n -E 'semantic_strict_subset_has_new_only_witness|
     SemanticStrictSubset|SemanticNewOnly|TransportSemanticFrame' origin/dev --
     'D5/**/*.lean' 'Blueprint/**/*.scribe.cs'`
     returned no declaration or theorem hit.
   * Statement-shape search
     `rg -n -i 'strict.*subset.*(witness|difference)|subset.*new.*domain|
     new.*domain.*witness|transport.*semantic.*frame' D5 Blueprint
     --glob '*.lean' --glob '*.md' --glob '*.scribe.cs'`
     found only unrelated set strictness in `CountermodelRepairUnderdetermination`.
   * Pinned-Mathlib search
     `rg -n 'theorem ssubset_iff_exists|ssubset_iff_exists|And\.right|and_imp|
     right.*and' .lake/packages/mathlib/Mathlib .lake/packages/mathlib/Mathlib.lean
     --glob '*.lean'`
     found `Set.ssubset_iff_exists` and generic uses of conjunction projection.
     The set theorem does not apply to an arbitrary `inDomain` relation; the proof
     below uses the strict-expansion definition's second conjunct directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.Semantics

universe u v

/-- A transport interpretation with a partial prediction run. Failure and
refutation both consume the concrete result produced by that run. -/
structure TransportSemanticFrame
    (TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u)
    (PredictionResult : Type v) where
  claimAddress : Claim -> ContentAddress
  claimScope : Claim -> Domain
  claimVersion : Claim -> Version
  receiptMatches :
    TruthReceipt -> ContentAddress -> Domain -> Version -> Prop
  claimOn : Claim -> Domain -> Prop
  inDomain : NewEvidence -> Domain -> Prop
  run : NewDomainPrediction -> NewEvidence -> Option PredictionResult
  fails :
    NewDomainPrediction -> NewEvidence -> PredictionResult -> Prop
  refutes :
    NewDomainPrediction -> NewEvidence -> PredictionResult -> Claim -> Prop

/-- The directed new-domain difference: evidence belongs to the reported
domain but not to the original domain. -/
def SemanticNewOnly
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    {PredictionResult : Type v}
    (S :
      TransportSemanticFrame TruthReceipt NewDomainPrediction Claim
        ContentAddress Domain Version NewEvidence PredictionResult)
    (z : NewEvidence)
    (J J' : Domain) : Prop :=
  S.inDomain z J' ∧ ¬ S.inDomain z J

/-- Semantic strict expansion preserves old-domain membership and contains a
concrete point in the directed new-domain difference. -/
def SemanticStrictSubset
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    {PredictionResult : Type v}
    (S :
      TransportSemanticFrame TruthReceipt NewDomainPrediction Claim
        ContentAddress Domain Version NewEvidence PredictionResult)
    (J J' : Domain) : Prop :=
  (∀ z, S.inDomain z J -> S.inDomain z J') ∧
    ∃ z, SemanticNewOnly S z J J'

/-- Every semantic strict expansion supplies a point in its directed
new-domain difference. -/
theorem semantic_strict_subset_has_new_only_witness
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    {PredictionResult : Type v}
    (S :
      TransportSemanticFrame TruthReceipt NewDomainPrediction Claim
        ContentAddress Domain Version NewEvidence PredictionResult)
    (J J' : Domain)
    (strictExpansion : SemanticStrictSubset S J J') :
    ∃ z, SemanticNewOnly S z J J' :=
  strictExpansion.2

#print axioms semantic_strict_subset_has_new_only_witness

/- Equality-based Boolean membership gives an inhabited domain and a concrete
strict expansion from the empty semantic domain to the singleton `true`. -/
private def booleanTransportFrame :
    TransportSemanticFrame Unit Unit Unit Unit Bool Unit Bool Bool where
  claimAddress := fun _ => ()
  claimScope := fun _ => false
  claimVersion := fun _ => ()
  receiptMatches := fun _ _ _ _ => True
  claimOn := fun _ _ => True
  inDomain := fun z domain => domain = true ∧ z = true
  run := fun _ z => some z
  fails := fun _ _ _ => False
  refutes := fun _ _ _ _ => False

example : Bool := false

example : SemanticStrictSubset booleanTransportFrame false true := by
  simp [SemanticStrictSubset, SemanticNewOnly, booleanTransportFrame]

example : ¬ ∃ z, SemanticNewOnly booleanTransportFrame z false false := by
  simp [SemanticNewOnly, booleanTransportFrame]

example : ∃ z, SemanticNewOnly booleanTransportFrame z false true := by
  exact semantic_strict_subset_has_new_only_witness
    booleanTransportFrame false true (by
      simp [SemanticStrictSubset, SemanticNewOnly, booleanTransportFrame])

end D5.S3.ConceptDynamics.DefinitionEscape.Semantics
