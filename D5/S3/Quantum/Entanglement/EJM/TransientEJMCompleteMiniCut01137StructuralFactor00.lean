/- Source-only alternative for the unchanged factor 0 of original cut 1137.
Depth 13, code 17589, index 43927; the original Fin20/Fin4 score is retained.
The saved starting row is checked once. Existing step-validity theorems then
transport its association through the four actual local updates. This source
has no kernel receipt or measured performance result yet. -/
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMCompleteMiniCut01137StructuralFactor00
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial Compatible)
open TransientEJMAnchor13674Common
open EJMOriginalReplayAssembly (prefixPartial)
open EJMCacheState (CachedLocal triangleStep)
open EJMCacheSoundness (TriangleValid triangle_step_valid triangle_valid_lower)
open EJMPartialBoundTransport (trianglePartialAct)
open EJMInflationScore (lhsTriangle triangleBlock)
open EJMCertificateData (F1)

abbrev Assignment := Fin 20 → Fin 4

private def partial0 : Partial (Fin 10) (Fin 4) :=
  prefixPartial 13 17589 ∘ lhsTriangle 0
private def partial1 (x14 : Fin 4) : Partial (Fin 10) (Fin 4) :=
  Function.update partial0 4 (some x14)
private def partial2 (x14 x15 : Fin 4) : Partial (Fin 10) (Fin 4) :=
  Function.update (partial1 x14) 7 (some x15)
private def partial3 (x14 x15 x18 : Fin 4) : Partial (Fin 10) (Fin 4) :=
  Function.update (partial2 x14 x15) 5 (some x18)
private def partial4 (x14 x15 x18 x19 : Fin 4) : Partial (Fin 10) (Fin 4) :=
  Function.update (partial3 x14 x15 x18) 8 (some x19)

private def cache0 : CachedLocal 41294 := mkTriangle (35438, (6, 1))
private def cache1 (x14 : Fin 4) : CachedLocal 41294 :=
  triangleStep cache0 4 x14
private def cache2 (x14 x15 : Fin 4) : CachedLocal 41294 :=
  triangleStep (cache1 x14) 7 x15
private def cache3 (x14 x15 x18 : Fin 4) : CachedLocal 41294 :=
  triangleStep (cache2 x14 x15) 5 x18
private def cache4 (x14 x15 x18 x19 : Fin 4) : CachedLocal 41294 :=
  triangleStep (cache3 x14 x15 x18) 8 x19

set_option trace.profiler true in
private theorem initial_assignment :
    EJMTriangleCacheData.assignment 35438 = trianglePartialAct (6, 1) partial0 := by
  decide +kernel

private theorem initial_valid : TriangleValid cache0 partial0 :=
  triangle_from_assignment (35438, (6, 1)) partial0 initial_assignment

private theorem unknown0 : partial0 4 = none := by decide +kernel
private theorem unknown1 (x14 : Fin 4) : partial1 x14 7 = none := by
  simpa only [partial1, Function.update_of_ne (by decide : (7 : Fin 10) ≠ 4)] using
    (by decide +kernel : partial0 7 = none)
private theorem unknown2 (x14 x15 : Fin 4) : partial2 x14 x15 5 = none := by
  simpa only [partial2, Function.update_of_ne (by decide : (5 : Fin 10) ≠ 7),
    partial1, Function.update_of_ne (by decide : (5 : Fin 10) ≠ 4)] using
    (by decide +kernel : partial0 5 = none)
private theorem unknown3 (x14 x15 x18 : Fin 4) :
    partial3 x14 x15 x18 8 = none := by
  simpa only [partial3, Function.update_of_ne (by decide : (8 : Fin 10) ≠ 5),
    partial2, Function.update_of_ne (by decide : (8 : Fin 10) ≠ 7),
    partial1, Function.update_of_ne (by decide : (8 : Fin 10) ≠ 4)] using
    (by decide +kernel : partial0 8 = none)

private theorem cache1_valid (x14 : Fin 4) : TriangleValid (cache1 x14) (partial1 x14) :=
  triangle_step_valid cache0 partial0 initial_valid 4 x14 unknown0
private theorem cache2_valid (x14 x15 : Fin 4) :
    TriangleValid (cache2 x14 x15) (partial2 x14 x15) :=
  triangle_step_valid (cache1 x14) (partial1 x14) (cache1_valid x14) 7 x15 (unknown1 x14)
private theorem cache3_valid (x14 x15 x18 : Fin 4) :
    TriangleValid (cache3 x14 x15 x18) (partial3 x14 x15 x18) :=
  triangle_step_valid (cache2 x14 x15) (partial2 x14 x15)
    (cache2_valid x14 x15) 5 x18 (unknown2 x14 x15)
private theorem cache4_valid (x14 x15 x18 x19 : Fin 4) :
    TriangleValid (cache4 x14 x15 x18 x19) (partial4 x14 x15 x18 x19) :=
  triangle_step_valid (cache3 x14 x15 x18) (partial3 x14 x15 x18)
    (cache3_valid x14 x15 x18) 8 x19 (unknown3 x14 x15 x18)

private def completedPartial (x14 x15 x18 x19 : Fin 4) : Partial (Fin 20) (Fin 4) :=
  Function.update (Function.update (Function.update (Function.update
    (prefixPartial 13 17589) 14 (some x14)) 15 (some x15)) 18 (some x18)) 19 (some x19)

private theorem incidence14 : EJMLocalCacheData.triangleIncidence 14 0 = some 4 := by
  decide +kernel
private theorem incidence15 : EJMLocalCacheData.triangleIncidence 15 0 = some 7 := by
  decide +kernel
private theorem incidence18 : EJMLocalCacheData.triangleIncidence 18 0 = some 5 := by
  decide +kernel
private theorem incidence19 : EJMLocalCacheData.triangleIncidence 19 0 = some 8 := by
  decide +kernel

private theorem completed_projection (x14 x15 x18 x19 : Fin 4) :
    completedPartial x14 x15 x18 x19 ∘ lhsTriangle 0 = partial4 x14 x15 x18 x19 := by
  simp only [completedPartial, partial4, partial3, partial2, partial1, partial0,
    EJMCacheLaws.triangle_projection_update, incidence14, incidence15, incidence18, incidence19]

/-- The exact symbolic local fold used by the original prepared factor.
Its expression is preserved independently of the alternative association proof. -/
def table (x14 x15 x18 x19 : Fin 4) : ℤ :=
  (mkTriangle (triangleStep (triangleStep (triangleStep (triangleStep
    (mkTriangle (35438, (6, 1))) 4 x14) 7 x15) 5 x18) 8 x19).state).row.lower

private theorem table_eq (x14 x15 x18 x19 : Fin 4) :
    table x14 x15 x18 x19 = (cache4 x14 x15 x18 x19).row.lower := by
  rfl

def lowerAt (e : Assignment) : ℤ := table (e 14) (e 15) (e 18) (e 19)

theorem bound (e : Assignment) (hp : Compatible (prefixPartial 13 17589) e) :
    lowerAt e ≤ triangleBlock F1 0 e := by
  have compatible : Compatible (completedPartial (e 14) (e 15) (e 18) (e 19)) e := by
    unfold completedPartial
    exact compatible_fill _ _ (compatible_fill _ _ (compatible_fill _ _
      (compatible_fill _ _ hp 14) 15) 18) 19
  have projected := compatible_project (completedPartial (e 14) (e 15) (e 18) (e 19)) e
    (lhsTriangle 0) compatible
  rw [completed_projection] at projected
  rw [lowerAt, table_eq]
  exact triangle_valid_lower (cache4 (e 14) (e 15) (e 18) (e 19)) _ _
    (cache4_valid (e 14) (e 15) (e 18) (e 19)) projected

#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.TransientEJMCompleteMiniCut01137StructuralFactor00
