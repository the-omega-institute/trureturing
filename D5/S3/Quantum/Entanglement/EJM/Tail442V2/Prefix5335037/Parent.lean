/- GID: D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/Parent
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/Parent
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/Raw002Tail442/Assembly.raw_cut_00337; premises=D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/Parent.parent_exact
   digest: The entire literal parent cache is identified with the actual original prefixCache at depth eighteen and prefix 5335037 through all thirty-two placements. -/

/- Source-only complete Tail442 checkpoint candidate. Kernel acceptance pending. -/
import D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037.Literals

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037
open EJMCacheState (Cache triangleStep singletonStep step lower)
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
open EJMPartialBoundData (scale)
open Tail442V2.Helper
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
private theorem parent_fields :
    checkFullCache parentCache (prefixCache 18 5335037) = true := by
  decide +kernel

theorem parent_exact : parentCache = prefixCache 18 5335037 :=
  cache_eq_of_checked _ _ parent_fields

#print axioms parent_exact

end D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037
