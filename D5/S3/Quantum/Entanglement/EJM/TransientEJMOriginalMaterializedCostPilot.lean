/- Prepared cost comparison, not yet kernel checked. The complete
literal cache must first equal the actual fifteen-step prefix. Both the cache
equality and the unchanged original 201-context suffix require Lean receipts.
This sample asserts no complete global lower bound or locality exclusion. -/
import D5.S3.Quantum.Entanglement.EJM.EJMCacheState
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalGlobalDAGData
import D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
import D5.S3.Quantum.Entanglement.EJM.EJMCacheMaterialization

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMOriginalMaterializedCostPilot
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
private def actualInitial : Cache :=
  ⟨fun _ => ⟨(41293, (0, 0)), EJMTriangleCacheData.mirror 41293⟩,
   fun _ => ⟨(8688, (0, 0)), EJMSingletonCacheData.mirror 8688⟩⟩
open D5.S3.Quantum.Entanglement.EJM.EJMCacheMaterialization (checkSame checked_same)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

private def prefixOutcomes : Fin 15 → Fin 4 := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

def computedCache : Cache :=
  (List.finRange 15).foldl
    (fun cache i => step cache ⟨i.val, by have h := i.isLt; omega⟩ (prefixOutcomes i))
    actualInitial

def partialEvent : Partial (Fin 20) (Fin 4) := fun g =>
  if h : g.val < 15 then some (prefixOutcomes ⟨g.val, h⟩) else none

/-- Every state and row payload is literal; no mirror lookup is left here. -/
def literalCache : Cache := ⟨![
    ⟨(27123, (0, 0)), ⟨1887500, (-6757394161834680), 0x3211000000, 0x19dbc008ede00076f0003b76019db9808edcc0076e6003b6f019da8008ed400076a0003b43⟩⟩,
    ⟨(15215, (6, 0)), ⟨1575000, (-6757394161834680), 0x2111000000, 0x49890024848012024009011ee01890000848000024000011ee⟩⟩,
    ⟨(27123, (6, 0)), ⟨1887500, (-6757394161834680), 0x3211000000, 0x19dbc008ede00076f0003b76019db9808edcc0076e6003b6f019da8008ed400076a0003b43⟩⟩,
    ⟨(15215, (6, 0)), ⟨1575000, (-6757394161834680), 0x2111000000, 0x49890024848012024009011ee01890000848000024000011ee⟩⟩,
    ⟨(27123, (0, 0)), ⟨1887500, (-6757394161834680), 0x3211000000, 0x19dbc008ede00076f0003b76019db9808edcc0076e6003b6f019da8008ed400076a0003b43⟩⟩,
    ⟨(15215, (6, 0)), ⟨1575000, (-6757394161834680), 0x2111000000, 0x49890024848012024009011ee01890000848000024000011ee⟩⟩,
    ⟨(27123, (6, 0)), ⟨1887500, (-6757394161834680), 0x3211000000, 0x19dbc008ede00076f0003b76019db9808edcc0076e6003b6f019da8008ed400076a0003b43⟩⟩,
    ⟨(15215, (0, 0)), ⟨1575000, (-6757394161834680), 0x2111000000, 0x49890024848012024009011ee01890000848000024000011ee⟩⟩,
    ⟨(15215, (0, 0)), ⟨1575000, (-6757394161834680), 0x2111000000, 0x49890024848012024009011ee01890000848000024000011ee⟩⟩,
    ⟨(31075, (0, 0)), ⟨1575020, (-6757394161834680), 0x3222111100, 0x1ac46009623000b11800588a01ac1c80960e400b07200582601a1b50090da80086d4003b6f⟩⟩,
    ⟨(15215, (0, 0)), ⟨1575000, (-6757394161834680), 0x2111000000, 0x49890024848012024009011ee01890000848000024000011ee⟩⟩,
    ⟨(31075, (0, 0)), ⟨1575020, (-6757394161834680), 0x3222111100, 0x1ac46009623000b11800588a01ac1c80960e400b07200582601a1b50090da80086d4003b6f⟩⟩,
    ⟨(34797, (0, 0)), ⟨1562524, (-3842827060476495), 0x3222222210, 0x1b44c009a26000d1300068964cb10626188312cc41890588a04b0a1821850c0cc286005826⟩⟩,
    ⟨(26774, (6, 0)), ⟨24, (-333398033381595), 0x2222222210, 0x4c9c3a260e1d12c70e8903267049c3a020e1d00c70e8003267⟩⟩,
    ⟨(34797, (6, 0)), ⟨1562524, (-3842827060476495), 0x3222222210, 0x1b44c009a26000d1300068964cb10626188312cc41890588a04b0a1821850c0cc286005826⟩⟩,
    ⟨(26774, (0, 0)), ⟨24, (-333398033381595), 0x2222222210, 0x4c9c3a260e1d12c70e8903267049c3a020e1d00c70e8003267⟩⟩],
  ![
    ⟨(6162, (0, 0)), ⟨77500, (342684662906040), 0x332100000, 0x1874d8083a6c001d36000e970187468083a34001d1a000e7a01873800839c0001ce0000e3b⟩⟩,
    ⟨(3643, (0, 0)), ⟨75000, (342684662906040), 0x221000000, 0x49825e24812f12009789004b001825e00812f00009780004b0⟩⟩,
    ⟨(3643, (0, 0)), ⟨75000, (342684662906040), 0x221000000, 0x49825e24812f12009789004b001825e00812f00009780004b0⟩⟩,
    ⟨(6162, (0, 0)), ⟨77500, (342684662906040), 0x332100000, 0x1874d8083a6c001d36000e970187468083a34001d1a000e7a01873800839c0001ce0000e3b⟩⟩,
    ⟨(6162, (0, 0)), ⟨77500, (342684662906040), 0x332100000, 0x1874d8083a6c001d36000e970187468083a34001d1a000e7a01873800839c0001ce0000e3b⟩⟩,
    ⟨(3643, (0, 0)), ⟨75000, (342684662906040), 0x221000000, 0x49825e24812f12009789004b001825e00812f00009780004b0⟩⟩,
    ⟨(6162, (0, 0)), ⟨77500, (342684662906040), 0x332100000, 0x1874d8083a6c001d36000e970187468083a34001d1a000e7a01873800839c0001ce0000e3b⟩⟩,
    ⟨(3643, (0, 0)), ⟨75000, (342684662906040), 0x221000000, 0x49825e24812f12009789004b001825e00812f00009780004b0⟩⟩,
    ⟨(3643, (0, 0)), ⟨75000, (342684662906040), 0x221000000, 0x49825e24812f12009789004b001825e00812f00009780004b0⟩⟩,
    ⟨(3643, (0, 0)), ⟨75000, (342684662906040), 0x221000000, 0x49825e24812f12009789004b001825e00812f00009780004b0⟩⟩,
    ⟨(3643, (0, 0)), ⟨75000, (342684662906040), 0x221000000, 0x49825e24812f12009789004b001825e00812f00009780004b0⟩⟩,
    ⟨(7163, (0, 0)), ⟨75004, (-1147801330716495), 0x332111110, 0x498aeba48575d202bae9015cb018aeb808575c002bae0015cb0489d50204ea80c2754000e3b⟩⟩,
    ⟨(5579, (0, 0)), ⟨62504, (-594470238080355), 0x221111110, 0x1867280833940019ca000ce10485850202c280c16140004b0⟩⟩,
    ⟨(3297, (0, 0)), ⟨4, (-114228225626970), 0x111111110, 0x481d80200ec00c0760000000⟩⟩,
    ⟨(5579, (0, 0)), ⟨62504, (-594470238080355), 0x221111110, 0x1867280833940019ca000ce10485850202c280c16140004b0⟩⟩,
    ⟨(3297, (0, 0)), ⟨4, (-114228225626970), 0x111111110, 0x481d80200ec00c0760000000⟩⟩]⟩

set_option trace.profiler true in
private theorem full_fields : checkSame literalCache computedCache = true := by
  decide +kernel

/-- Full equality includes all thirty-two states and every future row field. -/
theorem literal_cache_exact : literalCache = computedCache :=
  checked_same _ _ full_fields

set_option trace.profiler true in
theorem literal_suffix :
    check EJMOriginalGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 6 ⟨55, by decide⟩ literalCache partialEvent = true := by
  decide +kernel

/-- The result returns to the actual original initial cache and all fifteen updates. -/
theorem actual_original_context :
    check EJMOriginalGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 6 ⟨55, by decide⟩ computedCache partialEvent = true := by
  simpa only [literal_cache_exact] using literal_suffix

#print axioms literal_cache_exact
#print axioms literal_suffix
#print axioms actual_original_context
end D5.S3.Quantum.Entanglement.EJM.TransientEJMOriginalMaterializedCostPilot
