/- Uncompiled source-only candidate at 660d442642223072d56979f1ce6b501a79e449be.
No Lean execution, acceptance, adoption, or performance result is claimed. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.SharedPrefixRaw029.Context
open EJMCacheState (Cache step)
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)

/-- Consume the proved complete parent Cache and one proved complete edge.
No acceptance, association, hash equality, or row-index-only claim is a premise. -/
theorem cache_snoc_exact {depth code : ℕ} (a : Fin 4) {parent child : Cache}
    (parentExact : parent = prefixCache depth code)
    (edgeExact : child = step parent (coordinate depth) a) :
    child = prefixCache (depth + 1) (4 * code + a.val) := by
  have codeDiv : (4 * code + a.val) / 4 = code := by omega
  have codeMod : (4 * code + a.val) % 4 = a.val := by omega
  simpa only [prefixCache, codeDiv, codeMod, Fin.eta] using
    edgeExact.trans (congrArg (fun current : Cache => step current (coordinate depth) a)
      parentExact)

/-- The same composition preserves the entire 20-coordinate partial function.
Depth, including every leading zero outcome, remains part of the recurrence. -/
theorem partial_snoc_exact {depth code : ℕ} (a : Fin 4)
    {parent child : Partial (Fin 20) (Fin 4)}
    (parentExact : parent = prefixPartial depth code)
    (edgeExact : child = Function.update parent (coordinate depth) (some a)) :
    child = prefixPartial (depth + 1) (4 * code + a.val) := by
  have codeDiv : (4 * code + a.val) / 4 = code := by omega
  have codeMod : (4 * code + a.val) % 4 = a.val := by omega
  simpa only [prefixPartial, codeDiv, codeMod, Fin.eta] using
    edgeExact.trans (congrArg
      (fun current : Partial (Fin 20) (Fin 4) =>
        Function.update current (coordinate depth) (some a)) parentExact)

#print axioms cache_snoc_exact
#print axioms partial_snoc_exact
end D5.S3.Quantum.Entanglement.EJM.SharedPrefixRaw029.Context
