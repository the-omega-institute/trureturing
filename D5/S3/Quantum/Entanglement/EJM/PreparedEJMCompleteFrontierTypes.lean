/- GID: D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierTypes
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierTypes
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.original_score_lower_bound; instance=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.accepted_original_root
   digest: Original cut rows, exact lookup, executable metadata and canonical responses have separate roles. -/

/- Prepared source only; no Lean invocation or acceptance claim.
The data are untrusted until the explicit kernel goals in the generated
consumer modules pass. No native subtree size is a theorem premise. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierDataTypes
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAdaptiveResponseBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open FiniteSymmetryBoundReplay (Partial Event Compatible)
open EJMOriginalReplayAssembly (prefixCache prefixPartial coordinate)
open EJMCacheState (Cache step lower)
open EJMPartialBoundData (scale)
open EJMCertificateData (F1 F2)
open EJMInflationScore (score)

/-- Count the literal original nodes, with all four edges and their occurrence
multiplicity. It is independent of score/cache acceptance, so shared shape may
share this count, but never an actual-context replay receipt. -/
def subtreeContexts : Nat → Fin EJMOriginalGlobalDAGData.Size → Nat
  | 0, _ => 0
  | fuel + 1, index =>
      match EJMOriginalGlobalDAGData.nodes (fuel + 1) index with
      | .bound | .symmetry _ => 1
      | .split _ children =>
          1 + subtreeContexts fuel (children 0) + subtreeContexts fuel (children 1) +
            subtreeContexts fuel (children 2) + subtreeContexts fuel (children 3)

/-- Every stored field that can affect selection is checked. In particular,
the stored subtree size is compared against the original executable DAG; a
producer's `size ≤ 4096` assertion does not stand in for this equality. -/
def metadata (cut : CutRow) : Bool :=
  if hindex : cut.index < EJMOriginalGlobalDAGData.Size then
    decide (cut.reserved = 0 ∧ cut.depth ≤ 20 ∧ cut.code < 4 ^ cut.depth ∧
      cut.kind < 3 ∧ cut.kind = EJMOriginalGlobalDAGData.word cut.index % 4 ∧
      cut.domain = 4 ^ (20 - cut.depth) ∧ 0 < cut.subtreeContexts ∧
      cut.subtreeContexts ≤ 4096 ∧
      cut.subtreeContexts = subtreeContexts (21 - cut.depth) ⟨cut.index, hindex⟩)
  else false

/-- A raw symmetry suffix supplies rank descent, not a local score bound.
This response depends on the actual prefix, and therefore transports through
the decoder's partial equality without equating associated caches. -/
def CanonicalResponse (cut : CutRow) : Prop :=
  ∀ e : Event (Fin 20) (Fin 4), Compatible (prefixPartial cut.depth cut.code) e →
    score F1 F2 e < scale →
      ∃ e', score F1 F2 e' < scale ∧ FiniteLexSymmetry.rank e' < FiniteLexSymmetry.rank e

theorem response_of_raw (cut : CutRow) (within : cut.depth ≤ 20)
    (hindex : cut.index < EJMOriginalGlobalDAGData.Size)
    (accepted : EJMOriginalReplayAssembly.Accepted cut.depth cut.code ⟨cut.index, hindex⟩) :
    CanonicalResponse cut := by
  intro e hp hbad
  exact PreparedEJMAdaptiveResponseBridge.accepted_suffix_bad_event_response
    cut.depth cut.code ⟨cut.index, hindex⟩ within accepted e hp hbad

theorem response_of_semantic (cut : CutRow)
    (semantic : ∀ e : Event (Fin 20) (Fin 4),
      Compatible (prefixPartial cut.depth cut.code) e → scale ≤ score F1 F2 e) :
    CanonicalResponse cut := by
  intro e hp hbad
  exact False.elim ((not_lt_of_ge (semantic e hp)) hbad)

/-- The concrete all-cut theorem must fill every leaf with an actual proof.
This proposition never treats native metadata or a root-acceptance assumption
as a substitute for a missing cut receipt. -/
def CutTable.Responses : CutTable → Prop
  | .empty => True
  | .leaf cut => CanonicalResponse cut
  | .branch _ _ left right => left.Responses ∧ right.Responses

theorem lookup_response (table : CutTable) : table.Responses →
    ∀ (depth code : Nat) (cut : CutRow), table.lookup depth code = some cut →
      CanonicalResponse cut := by
  induction table with
  | empty =>
      intro ready depth code cut chosen
      cases chosen
  | leaf row =>
      intro ready depth code cut chosen
      simp only [CutTable.lookup] at chosen
      split_ifs at chosen with same
      · have equality : row = cut := Option.some.inj chosen
        subst cut
        exact ready
  | branch pivotDepth pivotCode left right ihLeft ihRight =>
      intro ready depth code cut chosen
      simp only [CutTable.lookup] at chosen
      split_ifs at chosen with earlier
      · exact ihLeft ready.1 depth code cut chosen
      · exact ihRight ready.2 depth code cut chosen

#print axioms response_of_raw
#print axioms lookup_response
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
