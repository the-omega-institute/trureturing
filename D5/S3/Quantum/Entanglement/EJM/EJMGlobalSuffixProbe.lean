/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbe
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbe
   mirror-E: none(waiver:actual-global-cover-kernel-probe)
   anchors: []
   utility: none
   digest: An existing complete eight-coordinate suffix is replayed with its exact original prefix cache and partial event. -/

/- WIP timing probe for the complete EJM refutation, not an independent
delivery or global acceptance. The native extraction observed 2,497 contexts,
624 four-way splits, 903 bound leaves and 970 symmetry leaves. None of those
counts or native checks is a mathematical premise. The proof below must be
compiled by the real kernel before its bounded suffix receipt is earned. -/

import D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalDAGData
import D5.S3.Quantum.Entanglement.EJM.EJMCacheState

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbe
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState

def pilotPrefix : Fin 12 → Fin 4 := ![0,0,0,0,0,1,1,1,2,1,1,1]

/-- This is the actual cache obtained by the original twelve global updates.
It does not substitute a native row index, a hash or a guessed row literal. -/
def pilotCache : Cache :=
  (List.finRange 12).foldl
    (fun cache i => step cache ⟨i.val, by have h := i.isLt; omega⟩ (pilotPrefix i))
    initial

def pilotPartial : Partial (Fin 20) (Fin 4) := fun g =>
  if h : g.val < 12 then some (pilotPrefix ⟨g.val, h⟩) else none

/-- The entire existing suffix checks every branch in its own actual state.
This concrete receipt remains unverified until canonical make lean exits zero. -/
set_option trace.profiler true in
private theorem pilot_suffix :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 9 ⟨161540, by decide⟩ pilotCache pilotPartial = true := by
  decide +kernel

#print axioms pilot_suffix

end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbe
