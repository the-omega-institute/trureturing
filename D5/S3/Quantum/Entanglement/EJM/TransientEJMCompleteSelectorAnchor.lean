/- Uncompiled exact checks for the full-table selector at the already
accepted original cut (depth 13, code 4, node 674). These checks retain the
complete table and original subtree metadata. They provide no responses at
the other cuts and do not prove the original global score bound.
Keep these bind-only applications transient.
-/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor3269Response

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMCompleteSelectorAnchor

open D5.S0.Certificates
open FiniteSymmetryBoundReplay (Partial Event Compatible)
open EJMOriginalReplayAssembly (prefixCache prefixPartial)
open EJMCacheState (Cache)
open EJMOriginalCachedGlobalReplay (Valid)
open EJMInflationScore (score)
open EJMCertificateData (F1 F2)
open EJMPartialBoundData (scale)
open PreparedEJMCompleteFrontier

set_option trace.profiler true in
example : selected 8 ⟨674, by decide⟩ (prefixPartial 13 4) =
    some ⟨13, 2, 0, 674, 4, 3269, 16384⟩ := by
  decide +kernel

-- Marking is acceptance of the adaptive check at this cut. Its semantic
-- response is supplied separately by the actual canonical raw receipt.
example : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 4 ⟨674, by decide⟩ := by
  apply accepted_of_selected 13 4 ⟨674, by decide⟩
    ⟨13, 2, 0, 674, 4, 3269, 16384⟩ (by decide)
  decide +kernel

-- An arbitrary associated cache is allowed: only partial equality is
-- transported, using the full selector's actual selected_spec theorem.
example (fuel : Nat) (index : Fin EJMOriginalGlobalDAGData.Size)
    (cache : Cache) (p : Partial (Fin 20) (Fin 4))
    (valid : Valid fuel cache p)
    (chosen : selected fuel index p = some ⟨13, 2, 0, 674, 4, 3269, 16384⟩)
    (e : Event (Fin 20) (Fin 4)) (compatible : Compatible p e)
    (bad : score F1 F2 e < scale) :
    ∃ e', score F1 F2 e' < scale ∧ FiniteLexSymmetry.rank e' < FiniteLexSymmetry.rank e := by
  obtain ⟨partialEq, _⟩ := selected_spec fuel index cache p
    ⟨13, 2, 0, 674, 4, 3269, 16384⟩ valid chosen
  apply PreparedEJMAnchor3269Response.actual_anchor_response e
  · simpa only [← partialEq] using compatible
  · exact bad

#print axioms PreparedEJMCompleteFrontier.selected_spec
#print axioms PreparedEJMAnchor3269Response.actual_anchor_response

end D5.S3.Quantum.Entanglement.EJM.TransientEJMCompleteSelectorAnchor
