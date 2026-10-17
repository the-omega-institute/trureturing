/- Prepared/uncompiled exact same 201-context original suffix as the accepted
numeric, full-field materialization and list probes. This changes only cache
representation and consumes its generic simulation bridge. Every four-way
branch, original lower and actual symmetry cut remains. Neither complete root
acceptance nor a speedup is asserted by this prepared source. -/
import D5.S3.Quantum.Entanglement.EJM.EJMVectorCachePilot
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalGlobalDAGData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMOriginalVectorCostPilot
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState (Cache)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)
open D5.S3.Quantum.Entanglement.EJM.EJMVectorCachePilot

private def actualInitial : Cache :=
  ⟨fun _ => ⟨(41293, (0, 0)), EJMTriangleCacheData.mirror 41293⟩,
   fun _ => ⟨(8688, (0, 0)), EJMSingletonCacheData.mirror 8688⟩⟩

private def prefixOutcomes : Fin 15 → Fin 4 := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def prefixCoordinate (i : Fin 15) : Fin 20 :=
  ⟨i.val, by have h := i.isLt; omega⟩

private def originalCache : Cache :=
  (List.finRange 15).foldl
    (fun s i => EJMCacheState.step s (prefixCoordinate i) (prefixOutcomes i)) actualInitial
private def vectorCache : VectorCache :=
  (List.finRange 15).foldl
    (fun s i => step s (prefixCoordinate i) (prefixOutcomes i)) (pack actualInitial)
private def partialEvent : Partial (Fin 20) (Fin 4) := fun g =>
  if h : g.val < 15 then some (prefixOutcomes ⟨g.val, h⟩) else none

private theorem prefix_view : view vectorCache = originalCache := by
  change view ((List.finRange 15).foldl
    (fun s i => step s (prefixCoordinate i) (prefixOutcomes i)) (pack actualInitial)) = _
  rw [view_foldl, view_pack]
  rfl

set_option trace.profiler true in
private theorem suffix_vector_accepted :
    check EJMOriginalGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 6 ⟨55, by decide⟩ vectorCache partialEvent = true := by
  decide +kernel

/-- This result concludes the unchanged original checker at its exact full
prefix state. Its proof consumes both the numeric receipt and the generic
representation simulation; no per-shape acceptance is transferred. -/
private theorem exact_original_context :
    check EJMOriginalGlobalDAGData.nodes EJMCacheState.step EJMCacheState.lower
      EJMGlobalScoreSymmetry.dominates scale 6 ⟨55, by decide⟩ originalCache partialEvent = true := by
  rw [← prefix_view]
  rw [← check_view EJMOriginalGlobalDAGData.nodes step EJMCacheState.step
    lower EJMCacheState.lower view view_step lower_view]
  exact suffix_vector_accepted

#print axioms exact_original_context
end D5.S3.Quantum.Entanglement.EJM.TransientEJMOriginalVectorCostPilot
