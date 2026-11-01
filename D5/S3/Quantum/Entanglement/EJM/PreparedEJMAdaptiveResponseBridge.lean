/- GID: D5/S3/Quantum/Entanglement/EJM/PreparedEJMAdaptiveResponseBridge
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/PreparedEJMAdaptiveResponseBridge
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: none
   digest: Canonical prefix validity preserves all original cache associations. -/

/- Prepared source only, uncompiled. The same adaptive checker is reused.
Canonical raw suffix acceptance provides rank descent for an actual partial;
no equality of arbitrary associated caches is asserted or needed. -/
import D5.S0.Certificates.PreparedFiniteAdaptiveFrontierResponse
import D5.S3.Quantum.Entanglement.EJM.Frontier.EJMOriginalAdaptiveFrontierBridge
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalPrefixAssociation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMAdaptiveResponseBridge
open D5.S0.Certificates
open FiniteSymmetryBoundReplay (Partial Event Compatible)
open EJMOriginalReplayAssembly (prefixCache prefixPartial)
open EJMCacheState (Cache step lower)
open EJMCacheSoundness (initial)
open EJMPartialBoundData (scale)
open EJMCertificateData (F1 F2)
open EJMInflationScore (score)
open EJMOriginalCachedGlobalReplay (Valid valid_lower_le_score step_valid initial_valid)

theorem canonical_valid (depth code : Nat) (within : depth ≤ 20) :
    Valid (21 - depth) (prefixCache depth code) (prefixPartial depth code) := by
  constructor
  · constructor
    · omega
    · intro g future
      apply EJMOriginalPrefixAssociation.prefixPartial_future_none depth code within g
      omega
  · exact EJMOriginalPrefixAssociation.prefix_associated depth code within

/-- Only canonical replay is checked. Its response depends on the compatible
partial assignment, so it can later be transported without a cache equality. -/
theorem accepted_suffix_bad_event_response (depth code : Nat)
    (index : Fin EJMOriginalGlobalDAGData.Size) (within : depth ≤ 20)
    (accepted : EJMOriginalReplayAssembly.Accepted depth code index)
    (e : Event (Fin 20) (Fin 4)) (hp : Compatible (prefixPartial depth code) e)
    (hbad : score F1 F2 e < scale) :
    ∃ e', score F1 F2 e' < scale ∧ FiniteLexSymmetry.rank e' < FiniteLexSymmetry.rank e := by
  exact FiniteCachedSymmetryDAGReplay.checked_forces_smaller_bad_event
    (score F1 F2) FiniteLexSymmetry.rank EJMGlobalScoreSymmetry.act
    EJMOriginalGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates scale
    Valid valid_lower_le_score step_valid EJMGlobalScoreSymmetry.actual_score_invariant
    EJMGlobalScoreSymmetry.dominates_rank_lt (21 - depth) index
    (prefixCache depth code) (prefixPartial depth code) accepted
    (canonical_valid depth code within) e hp hbad


#print axioms accepted_suffix_bad_event_response
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMAdaptiveResponseBridge
