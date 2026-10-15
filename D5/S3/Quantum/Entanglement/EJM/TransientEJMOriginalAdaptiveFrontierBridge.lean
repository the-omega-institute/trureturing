/- Prepared transient adaptive-frontier integration; uncompiled.
The original twenty coordinates, four outcomes, F1/F2, scale 6987435, DAG,
initial cache and all thirty-two cached states are preserved. Each early cut
needs a semantic bound or complete raw acceptance for its exact valid context.
No selector, complete 52,867-cut receipt family or complete adaptive root
acceptance is asserted. Native cut counts do not prove any theorem premise.
This transient integration is the intended consumer of the generic checker,
not a separately delivered canonical bind-only wrapper. Its source-owned Reg
audit and binding remain unfinished under
https://github.com/the-omega-institute/trureturing/issues/16309. -/

import D5.S0.Certificates.FiniteAdaptiveSemanticFrontierReplay
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMOriginalAdaptiveFrontierBridge
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S0.Certificates.FiniteAdaptiveSemanticFrontierReplay (check checked_split)
open D5.S0.Certificates
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState (Cache step lower)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheSoundness (initial)
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalCachedGlobalReplay
  (Valid valid_lower_le_score step_valid initial_valid)
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
  (coordinate prefixCache prefixPartial)
open D5.S3.Quantum.Entanglement.EJMInflationScore (score)

/-- Adaptive acceptance retains the original depth, complete base-four prefix,
remaining fuel, node index, cache and partial assignment of this occurrence. -/
def Accepted
    (frontier : ℕ → Fin EJMOriginalGlobalDAGData.Size → Cache →
      Partial (Fin 20) (Fin 4) → Bool)
    (depth code : ℕ) (index : Fin EJMOriginalGlobalDAGData.Size) : Prop :=
  check EJMOriginalGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
    scale frontier (21 - depth) index (prefixCache depth code) (prefixPartial depth code) = true

/-- Every interior node uses its literal original split and all four actual
children. An early marked cut is handled by its own exact-context receipt. -/
theorem assemble
    (frontier : ℕ → Fin EJMOriginalGlobalDAGData.Size → Cache →
      Partial (Fin 20) (Fin 4) → Bool)
    (depth code : ℕ) (index : Fin EJMOriginalGlobalDAGData.Size)
    (within : depth < 20) (children : Fin 4 → Fin EJMOriginalGlobalDAGData.Size)
    (unmarked : frontier (21 - depth) index
      (prefixCache depth code) (prefixPartial depth code) = false)
    (node : EJMOriginalGlobalDAGData.nodes (21 - depth) index =
      .split (coordinate depth) children)
    (branches : ∀ a : Fin 4,
      Accepted frontier (depth + 1) (4 * code + a.val) (children a)) :
    Accepted frontier depth code index := by
  have fuel : 21 - depth = (21 - (depth + 1)) + 1 := by omega
  have positive : 0 < 21 - (depth + 1) := by omega
  unfold Accepted
  rw [fuel]
  apply checked_split EJMOriginalGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale frontier (21 - (depth + 1)) index
    (prefixCache depth code) (prefixPartial depth code) (coordinate depth) children
    (by simpa only [← fuel] using unmarked)
    (by simpa only [← fuel] using node) positive
  intro a
  have codeDiv : (4 * code + a.val) / 4 = code := by omega
  have codeMod : (4 * code + a.val) % 4 = a.val := by omega
  simpa only [Accepted, prefixCache, prefixPartial, codeDiv, codeMod, Fin.eta]
    using branches a

/-- Complete adaptive coverage and all marked-context receipts imply the
same original global bound. Semantic leaves need not pass the raw checker;
raw leaves reuse its already proved rank response inside the generic proof. -/
theorem original_adaptive_score_lower_bound
    (frontier : ℕ → Fin EJMOriginalGlobalDAGData.Size → Cache →
      Partial (Fin 20) (Fin 4) → Bool)
    (frontierReceipts : ∀ fuel index cache p, Valid fuel cache p →
      frontier fuel index cache p = true →
      (∀ e, Compatible p e → scale ≤ score F1 F2 e) ∨
        D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check
          EJMOriginalGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
          scale fuel index cache p = true)
    (accepted : check EJMOriginalGlobalDAGData.nodes step lower
      EJMGlobalScoreSymmetry.dominates scale frontier 21
      EJMOriginalGlobalDAGData.root initial (fun _ => none) = true) :
    ∀ e : Event (Fin 20) (Fin 4), scale ≤ score F1 F2 e := by
  exact D5.S0.Certificates.FiniteAdaptiveSemanticFrontierReplay.checked_global_lower_bound
    (score F1 F2) FiniteLexSymmetry.rank EJMGlobalScoreSymmetry.act
    EJMOriginalGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates scale
    Valid valid_lower_le_score step_valid EJMGlobalScoreSymmetry.actual_score_invariant
    EJMGlobalScoreSymmetry.dominates_rank_lt frontier frontierReceipts
    21 EJMOriginalGlobalDAGData.root initial initial_valid accepted

#print axioms assemble
#print axioms original_adaptive_score_lower_bound
end D5.S3.Quantum.Entanglement.EJM.TransientEJMOriginalAdaptiveFrontierBridge
