/- Prepared small actual consumer, uncompiled. Reuses the canonical complete
3269-context receipt at (depth=13, code=4, index=674). This is one real cut;
it does not supply coverage or responses for the other 52,866 cuts. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAdaptiveResponseBridge
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMOriginalAnchor3269Modular128Root

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor3269Response
open D5.S0.Certificates
open FiniteSymmetryBoundReplay (Partial Event Compatible)
open EJMOriginalReplayAssembly (prefixCache prefixPartial)
open EJMCacheState (Cache step lower)
open EJMPartialBoundData (scale)
open EJMCertificateData (F1 F2)
open EJMInflationScore (score)
open EJMOriginalCachedGlobalReplay (Valid valid_lower_le_score step_valid)

theorem actual_anchor_response (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 13 4) e) (hbad : score F1 F2 e < scale) :
    ∃ e', score F1 F2 e' < scale ∧ FiniteLexSymmetry.rank e' < FiniteLexSymmetry.rank e := by
  exact PreparedEJMAdaptiveResponseBridge.accepted_suffix_bad_event_response
    13 4 ⟨674, by decide⟩ (by decide)
    PreparedEJMOriginalAnchor3269Modular128.accepted_actual_context e hp hbad

/-- This small executable selector marks just the actual anchor. It ignores
the cache and requires exact partial equality, rather than raw replay there. -/
def anchorFrontier (fuel : Nat) (index : Fin EJMOriginalGlobalDAGData.Size)
    (_cache : Cache) (p : Partial (Fin 20) (Fin 4)) : Bool :=
  decide (fuel = 8 ∧ index.val = 674 ∧ p = prefixPartial 13 4)

theorem anchor_frontier_responses (fuel : Nat) (index : Fin EJMOriginalGlobalDAGData.Size)
    (cache : Cache) (p : Partial (Fin 20) (Fin 4)) (_valid : Valid fuel cache p)
    (marked : anchorFrontier fuel index cache p = true) (e : Event (Fin 20) (Fin 4))
    (hp : Compatible p e) (hbad : score F1 F2 e < scale) :
    ∃ e', score F1 F2 e' < scale ∧ FiniteLexSymmetry.rank e' < FiniteLexSymmetry.rank e := by
  have actual : fuel = 8 ∧ index.val = 674 ∧ p = prefixPartial 13 4 :=
    of_decide_eq_true marked
  exact actual_anchor_response e (by simpa only [actual.2.2] using hp) hbad

theorem accepted_actual_anchor :
    TransientEJMOriginalAdaptiveFrontierBridge.Accepted anchorFrontier 13 4
      ⟨674, by decide⟩ := by
  have marked : anchorFrontier 8 ⟨674, by decide⟩
      (prefixCache 13 4) (prefixPartial 13 4) = true := by
    exact decide_eq_true ⟨rfl, rfl, rfl⟩
  unfold TransientEJMOriginalAdaptiveFrontierBridge.Accepted
  simp only [FiniteAdaptiveSemanticFrontierReplay.check, marked, ite_true]

/-- Actual kernel receipt -> response frontier -> generic adaptive descent.
This concrete consumer exercises the new generic theorem at a genuine cut. -/
theorem actual_anchor_response_via_generic (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 13 4) e) (hbad : score F1 F2 e < scale) :
    ∃ e', score F1 F2 e' < scale ∧ FiniteLexSymmetry.rank e' < FiniteLexSymmetry.rank e := by
  exact PreparedFiniteAdaptiveFrontierResponse.checked_forces_smaller_bad_event
    (score F1 F2) FiniteLexSymmetry.rank EJMGlobalScoreSymmetry.act
    EJMOriginalGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates scale
    Valid valid_lower_le_score step_valid EJMGlobalScoreSymmetry.actual_score_invariant
    EJMGlobalScoreSymmetry.dominates_rank_lt anchorFrontier anchor_frontier_responses
    8 ⟨674, by decide⟩ (prefixCache 13 4) (prefixPartial 13 4)
    accepted_actual_anchor (PreparedEJMAdaptiveResponseBridge.canonical_valid 13 4 (by decide))
    e hp hbad

#print axioms actual_anchor_response
#print axioms actual_anchor_response_via_generic
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor3269Response
