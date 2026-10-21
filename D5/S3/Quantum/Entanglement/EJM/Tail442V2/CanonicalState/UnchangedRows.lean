/- GID: D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/UnchangedRows
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/UnchangedRows
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/Raw002Tail442/Assembly.raw_cut_00337; premises=D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/UnchangedRows.unchanged_triangle_02,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/UnchangedRows.unchanged_triangle_03,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/UnchangedRows.unchanged_triangle_06,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/UnchangedRows.unchanged_triangle_07,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/UnchangedRows.unchanged_triangle_10,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/UnchangedRows.unchanged_triangle_11,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/UnchangedRows.unchanged_triangle_12,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/UnchangedRows.unchanged_triangle_13,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/UnchangedRows.unchanged_singleton_00,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/UnchangedRows.unchanged_singleton_03,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/UnchangedRows.unchanged_singleton_04,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/UnchangedRows.unchanged_singleton_06,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/UnchangedRows.unchanged_singleton_08,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/UnchangedRows.unchanged_singleton_10,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/UnchangedRows.unchanged_singleton_12,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/UnchangedRows.unchanged_singleton_13,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/UnchangedRows.unchanged_singleton_15
   digest: Seventeen complete CachedLocal equalities retain every State index and MirrorRow field at unchanged original placements for every one of four outcomes. -/

/- Source-only candidate. Not deployed, elaborated or kernel accepted.
   Each receipt proves equality of the entire CachedLocal, including its
   complete state and all four MirrorRow fields, for every outcome a.
   Matrix's existing projection laws explicitly peel each vector constructor.
   Downstream branches can consume these opaque receipts without reproving
   their literal parent/child equality through FullLocalFields.
   Speed and heartbeat improvement remain unmeasured. -/
import D5.S3.Quantum.Entanglement.EJM.Tail442V2.CanonicalState.Literals

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.Tail442V2.CanonicalState.UnchangedRows

open Tail442V2.CanonicalStateConcrete

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem unchanged_triangle_02 (a : Fin 4) :
    parentCache.triangle ⟨2, by decide⟩ =
      (nextCache a).triangle ⟨2, by decide⟩ := by
  fin_cases a <;>
    simp only [parentCache, nextCache, childCache0, childCache1, childCache2,
      childCache3, Matrix.cons_val_zero', Matrix.cons_val_succ']

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem unchanged_triangle_03 (a : Fin 4) :
    parentCache.triangle ⟨3, by decide⟩ =
      (nextCache a).triangle ⟨3, by decide⟩ := by
  fin_cases a <;>
    simp only [parentCache, nextCache, childCache0, childCache1, childCache2,
      childCache3, Matrix.cons_val_zero', Matrix.cons_val_succ']

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem unchanged_triangle_06 (a : Fin 4) :
    parentCache.triangle ⟨6, by decide⟩ =
      (nextCache a).triangle ⟨6, by decide⟩ := by
  fin_cases a <;>
    simp only [parentCache, nextCache, childCache0, childCache1, childCache2,
      childCache3, Matrix.cons_val_zero', Matrix.cons_val_succ']

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem unchanged_triangle_07 (a : Fin 4) :
    parentCache.triangle ⟨7, by decide⟩ =
      (nextCache a).triangle ⟨7, by decide⟩ := by
  fin_cases a <;>
    simp only [parentCache, nextCache, childCache0, childCache1, childCache2,
      childCache3, Matrix.cons_val_zero', Matrix.cons_val_succ']

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem unchanged_triangle_10 (a : Fin 4) :
    parentCache.triangle ⟨10, by decide⟩ =
      (nextCache a).triangle ⟨10, by decide⟩ := by
  fin_cases a <;>
    simp only [parentCache, nextCache, childCache0, childCache1, childCache2,
      childCache3, Matrix.cons_val_zero', Matrix.cons_val_succ']

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem unchanged_triangle_11 (a : Fin 4) :
    parentCache.triangle ⟨11, by decide⟩ =
      (nextCache a).triangle ⟨11, by decide⟩ := by
  fin_cases a <;>
    simp only [parentCache, nextCache, childCache0, childCache1, childCache2,
      childCache3, Matrix.cons_val_zero', Matrix.cons_val_succ']

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem unchanged_triangle_12 (a : Fin 4) :
    parentCache.triangle ⟨12, by decide⟩ =
      (nextCache a).triangle ⟨12, by decide⟩ := by
  fin_cases a <;>
    simp only [parentCache, nextCache, childCache0, childCache1, childCache2,
      childCache3, Matrix.cons_val_zero', Matrix.cons_val_succ']

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem unchanged_triangle_13 (a : Fin 4) :
    parentCache.triangle ⟨13, by decide⟩ =
      (nextCache a).triangle ⟨13, by decide⟩ := by
  fin_cases a <;>
    simp only [parentCache, nextCache, childCache0, childCache1, childCache2,
      childCache3, Matrix.cons_val_zero', Matrix.cons_val_succ']

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem unchanged_singleton_00 (a : Fin 4) :
    parentCache.singleton ⟨0, by decide⟩ =
      (nextCache a).singleton ⟨0, by decide⟩ := by
  fin_cases a <;>
    simp only [parentCache, nextCache, childCache0, childCache1, childCache2,
      childCache3, Matrix.cons_val_zero', Matrix.cons_val_succ']

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem unchanged_singleton_03 (a : Fin 4) :
    parentCache.singleton ⟨3, by decide⟩ =
      (nextCache a).singleton ⟨3, by decide⟩ := by
  fin_cases a <;>
    simp only [parentCache, nextCache, childCache0, childCache1, childCache2,
      childCache3, Matrix.cons_val_zero', Matrix.cons_val_succ']

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem unchanged_singleton_04 (a : Fin 4) :
    parentCache.singleton ⟨4, by decide⟩ =
      (nextCache a).singleton ⟨4, by decide⟩ := by
  fin_cases a <;>
    simp only [parentCache, nextCache, childCache0, childCache1, childCache2,
      childCache3, Matrix.cons_val_zero', Matrix.cons_val_succ']

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem unchanged_singleton_06 (a : Fin 4) :
    parentCache.singleton ⟨6, by decide⟩ =
      (nextCache a).singleton ⟨6, by decide⟩ := by
  fin_cases a <;>
    simp only [parentCache, nextCache, childCache0, childCache1, childCache2,
      childCache3, Matrix.cons_val_zero', Matrix.cons_val_succ']

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem unchanged_singleton_08 (a : Fin 4) :
    parentCache.singleton ⟨8, by decide⟩ =
      (nextCache a).singleton ⟨8, by decide⟩ := by
  fin_cases a <;>
    simp only [parentCache, nextCache, childCache0, childCache1, childCache2,
      childCache3, Matrix.cons_val_zero', Matrix.cons_val_succ']

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem unchanged_singleton_10 (a : Fin 4) :
    parentCache.singleton ⟨10, by decide⟩ =
      (nextCache a).singleton ⟨10, by decide⟩ := by
  fin_cases a <;>
    simp only [parentCache, nextCache, childCache0, childCache1, childCache2,
      childCache3, Matrix.cons_val_zero', Matrix.cons_val_succ']

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem unchanged_singleton_12 (a : Fin 4) :
    parentCache.singleton ⟨12, by decide⟩ =
      (nextCache a).singleton ⟨12, by decide⟩ := by
  fin_cases a <;>
    simp only [parentCache, nextCache, childCache0, childCache1, childCache2,
      childCache3, Matrix.cons_val_zero', Matrix.cons_val_succ']

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem unchanged_singleton_13 (a : Fin 4) :
    parentCache.singleton ⟨13, by decide⟩ =
      (nextCache a).singleton ⟨13, by decide⟩ := by
  fin_cases a <;>
    simp only [parentCache, nextCache, childCache0, childCache1, childCache2,
      childCache3, Matrix.cons_val_zero', Matrix.cons_val_succ']

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem unchanged_singleton_15 (a : Fin 4) :
    parentCache.singleton ⟨15, by decide⟩ =
      (nextCache a).singleton ⟨15, by decide⟩ := by
  fin_cases a <;>
    simp only [parentCache, nextCache, childCache0, childCache1, childCache2,
      childCache3, Matrix.cons_val_zero', Matrix.cons_val_succ']

#print axioms unchanged_triangle_02
#print axioms unchanged_triangle_03
#print axioms unchanged_triangle_06
#print axioms unchanged_triangle_07
#print axioms unchanged_triangle_10
#print axioms unchanged_triangle_11
#print axioms unchanged_triangle_12
#print axioms unchanged_triangle_13
#print axioms unchanged_singleton_00
#print axioms unchanged_singleton_03
#print axioms unchanged_singleton_04
#print axioms unchanged_singleton_06
#print axioms unchanged_singleton_08
#print axioms unchanged_singleton_10
#print axioms unchanged_singleton_12
#print axioms unchanged_singleton_13
#print axioms unchanged_singleton_15

end D5.S3.Quantum.Entanglement.EJM.Tail442V2.CanonicalState.UnchangedRows
