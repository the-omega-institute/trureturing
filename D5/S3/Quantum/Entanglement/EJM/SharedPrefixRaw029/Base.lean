/- Uncompiled complete Raw029 shared-prefix source-only prototype.
Reference H3: 660d442642223072d56979f1ce6b501a79e449be.
Native cache literals are proposals. Every complete edge equality and original
memo suffix is a fresh kernel obligation. No acceptance, adoption or speedup
is claimed. Only the 128 original Raw029 cuts are represented. -/
import D5.S3.Quantum.Entanglement.EJM.SharedPrefixRaw029.Context

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.SharedPrefixRaw029.Prefixes
open EJMCacheState (Cache step)
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)

/-- Depth zero is the actual original initial cache. -/
def cache_00_0 : Cache := EJMCacheSoundness.initial

theorem cache_exact_00_0 : cache_00_0 = prefixCache 0 0 := rfl

/-- The complete initial partial assignment is empty at all twenty coordinates. -/
def partial_00_0 : Partial (Fin 20) (Fin 4) := fun _ => none

theorem partial_exact_00_0 : partial_00_0 = prefixPartial 0 0 := rfl

#print axioms cache_exact_00_0
#print axioms partial_exact_00_0

end D5.S3.Quantum.Entanglement.EJM.SharedPrefixRaw029.Prefixes
