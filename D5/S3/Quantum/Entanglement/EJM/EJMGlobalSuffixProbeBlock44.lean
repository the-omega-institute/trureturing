/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock44
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock44
   mirror-E: none(waiver:actual-global-cover-kernel-probe)
   anchors: []
   utility: none
   digest: Exact full subtree leaf receipts and every four-child split are assembled without changing their actual contexts. -/

/- Same complete existing-cover suffix. This is computational staging of the
original actual cache/partial expressions and all four branches. Native input
is untrusted. Only canonical kernel compilation earns each receipt. These
receipts close this exact suffix, not the complete global refutation. -/

import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock44
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

theorem receipt6 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 6 ⟨6, by decide⟩ cache6 partial6 = true := by
  decide +kernel

theorem receipt4 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 7 ⟨4, by decide⟩ cache4 partial4 = true := by
  decide +kernel

theorem receipt2 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 8 ⟨2, by decide⟩ cache2 partial2 = true := by
  decide +kernel

theorem receipt1 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 8 ⟨1, by decide⟩ cache1 partial1 = true := by
  decide +kernel


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock44
