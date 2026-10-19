/- GID: D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/Branch0
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/Branch0
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/Raw002Tail442/Assembly.raw_cut_00337; premises=D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/Branch0.branch0_step,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/Branch0.branch0_bound
   digest: All thirty-two complete placement obligations and the exact literal lower total support this prefix's original outcome-0 step and bound. -/

/- Source-only complete Tail442 checkpoint candidate. Kernel acceptance pending. -/
import D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037.Locals
import D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037.UnchangedRows
import D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037.LowerBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037
open EJMCacheState (Cache triangleStep singletonStep step lower)
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
open EJMPartialBoundData (scale)
open Tail442V2.Helper
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)

private theorem branch0_triangle_00 : FullLocalFields (triangleStep (parentCache.triangle ⟨0, by decide⟩) ⟨5, by decide⟩ ⟨0, by decide⟩) ((nextCache ⟨0, by decide⟩).triangle ⟨0, by decide⟩) :=
  fields_of_cachedLocal_eq _ _ (local_triangle_000_exact)

private theorem branch0_triangle_01 : FullLocalFields (triangleStep (parentCache.triangle ⟨1, by decide⟩) ⟨5, by decide⟩ ⟨0, by decide⟩) ((nextCache ⟨0, by decide⟩).triangle ⟨1, by decide⟩) :=
  fields_of_cachedLocal_eq _ _ (local_triangle_001_exact)

set_option maxHeartbeats 100000000 in
private theorem branch0_triangle_02 : FullLocalFields (parentCache.triangle ⟨2, by decide⟩) ((nextCache ⟨0, by decide⟩).triangle ⟨2, by decide⟩) :=
  fields_of_cachedLocal_eq _ _
    (D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037.unchanged_triangle_02 ⟨0, by decide⟩)

set_option maxHeartbeats 100000000 in
private theorem branch0_triangle_03 : FullLocalFields (parentCache.triangle ⟨3, by decide⟩) ((nextCache ⟨0, by decide⟩).triangle ⟨3, by decide⟩) :=
  fields_of_cachedLocal_eq _ _
    (D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037.unchanged_triangle_03 ⟨0, by decide⟩)

private theorem branch0_triangle_04 : FullLocalFields (triangleStep (parentCache.triangle ⟨4, by decide⟩) ⟨5, by decide⟩ ⟨0, by decide⟩) ((nextCache ⟨0, by decide⟩).triangle ⟨4, by decide⟩) :=
  fields_of_cachedLocal_eq _ _ (local_triangle_002_exact)

private theorem branch0_triangle_05 : FullLocalFields (triangleStep (parentCache.triangle ⟨5, by decide⟩) ⟨5, by decide⟩ ⟨0, by decide⟩) ((nextCache ⟨0, by decide⟩).triangle ⟨5, by decide⟩) :=
  fields_of_cachedLocal_eq _ _ (local_triangle_003_exact)

set_option maxHeartbeats 100000000 in
private theorem branch0_triangle_06 : FullLocalFields (parentCache.triangle ⟨6, by decide⟩) ((nextCache ⟨0, by decide⟩).triangle ⟨6, by decide⟩) :=
  fields_of_cachedLocal_eq _ _
    (D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037.unchanged_triangle_06 ⟨0, by decide⟩)

set_option maxHeartbeats 100000000 in
private theorem branch0_triangle_07 : FullLocalFields (parentCache.triangle ⟨7, by decide⟩) ((nextCache ⟨0, by decide⟩).triangle ⟨7, by decide⟩) :=
  fields_of_cachedLocal_eq _ _
    (D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037.unchanged_triangle_07 ⟨0, by decide⟩)

private theorem branch0_triangle_08 : FullLocalFields (triangleStep (parentCache.triangle ⟨8, by decide⟩) ⟨5, by decide⟩ ⟨0, by decide⟩) ((nextCache ⟨0, by decide⟩).triangle ⟨8, by decide⟩) :=
  fields_of_cachedLocal_eq _ _ (local_triangle_004_exact)

private theorem branch0_triangle_09 : FullLocalFields (triangleStep (parentCache.triangle ⟨9, by decide⟩) ⟨5, by decide⟩ ⟨0, by decide⟩) ((nextCache ⟨0, by decide⟩).triangle ⟨9, by decide⟩) :=
  fields_of_cachedLocal_eq _ _ (local_triangle_005_exact)

set_option maxHeartbeats 100000000 in
private theorem branch0_triangle_10 : FullLocalFields (parentCache.triangle ⟨10, by decide⟩) ((nextCache ⟨0, by decide⟩).triangle ⟨10, by decide⟩) :=
  fields_of_cachedLocal_eq _ _
    (D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037.unchanged_triangle_10 ⟨0, by decide⟩)

set_option maxHeartbeats 100000000 in
private theorem branch0_triangle_11 : FullLocalFields (parentCache.triangle ⟨11, by decide⟩) ((nextCache ⟨0, by decide⟩).triangle ⟨11, by decide⟩) :=
  fields_of_cachedLocal_eq _ _
    (D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037.unchanged_triangle_11 ⟨0, by decide⟩)

set_option maxHeartbeats 100000000 in
private theorem branch0_triangle_12 : FullLocalFields (parentCache.triangle ⟨12, by decide⟩) ((nextCache ⟨0, by decide⟩).triangle ⟨12, by decide⟩) :=
  fields_of_cachedLocal_eq _ _
    (D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037.unchanged_triangle_12 ⟨0, by decide⟩)

set_option maxHeartbeats 100000000 in
private theorem branch0_triangle_13 : FullLocalFields (parentCache.triangle ⟨13, by decide⟩) ((nextCache ⟨0, by decide⟩).triangle ⟨13, by decide⟩) :=
  fields_of_cachedLocal_eq _ _
    (D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037.unchanged_triangle_13 ⟨0, by decide⟩)

private theorem branch0_triangle_14 : FullLocalFields (triangleStep (parentCache.triangle ⟨14, by decide⟩) ⟨1, by decide⟩ ⟨0, by decide⟩) ((nextCache ⟨0, by decide⟩).triangle ⟨14, by decide⟩) :=
  fields_of_cachedLocal_eq _ _ (local_triangle_006_exact)

private theorem branch0_triangle_15 : FullLocalFields (triangleStep (parentCache.triangle ⟨15, by decide⟩) ⟨0, by decide⟩ ⟨0, by decide⟩) ((nextCache ⟨0, by decide⟩).triangle ⟨15, by decide⟩) :=
  fields_of_cachedLocal_eq _ _ (local_triangle_007_exact)

set_option maxHeartbeats 100000000 in
private theorem branch0_singleton_00 : FullLocalFields (parentCache.singleton ⟨0, by decide⟩) ((nextCache ⟨0, by decide⟩).singleton ⟨0, by decide⟩) :=
  fields_of_cachedLocal_eq _ _
    (D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037.unchanged_singleton_00 ⟨0, by decide⟩)

private theorem branch0_singleton_01 : FullLocalFields (singletonStep (parentCache.singleton ⟨1, by decide⟩) ⟨6, by decide⟩ ⟨0, by decide⟩) ((nextCache ⟨0, by decide⟩).singleton ⟨1, by decide⟩) :=
  fields_of_cachedLocal_eq _ _ (local_singleton_000_exact)

private theorem branch0_singleton_02 : FullLocalFields (singletonStep (parentCache.singleton ⟨2, by decide⟩) ⟨6, by decide⟩ ⟨0, by decide⟩) ((nextCache ⟨0, by decide⟩).singleton ⟨2, by decide⟩) :=
  fields_of_cachedLocal_eq _ _ (local_singleton_000_exact)

set_option maxHeartbeats 100000000 in
private theorem branch0_singleton_03 : FullLocalFields (parentCache.singleton ⟨3, by decide⟩) ((nextCache ⟨0, by decide⟩).singleton ⟨3, by decide⟩) :=
  fields_of_cachedLocal_eq _ _
    (D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037.unchanged_singleton_03 ⟨0, by decide⟩)

set_option maxHeartbeats 100000000 in
private theorem branch0_singleton_04 : FullLocalFields (parentCache.singleton ⟨4, by decide⟩) ((nextCache ⟨0, by decide⟩).singleton ⟨4, by decide⟩) :=
  fields_of_cachedLocal_eq _ _
    (D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037.unchanged_singleton_04 ⟨0, by decide⟩)

private theorem branch0_singleton_05 : FullLocalFields (singletonStep (parentCache.singleton ⟨5, by decide⟩) ⟨6, by decide⟩ ⟨0, by decide⟩) ((nextCache ⟨0, by decide⟩).singleton ⟨5, by decide⟩) :=
  fields_of_cachedLocal_eq _ _ (local_singleton_001_exact)

set_option maxHeartbeats 100000000 in
private theorem branch0_singleton_06 : FullLocalFields (parentCache.singleton ⟨6, by decide⟩) ((nextCache ⟨0, by decide⟩).singleton ⟨6, by decide⟩) :=
  fields_of_cachedLocal_eq _ _
    (D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037.unchanged_singleton_06 ⟨0, by decide⟩)

private theorem branch0_singleton_07 : FullLocalFields (singletonStep (parentCache.singleton ⟨7, by decide⟩) ⟨6, by decide⟩ ⟨0, by decide⟩) ((nextCache ⟨0, by decide⟩).singleton ⟨7, by decide⟩) :=
  fields_of_cachedLocal_eq _ _ (local_singleton_002_exact)

set_option maxHeartbeats 100000000 in
private theorem branch0_singleton_08 : FullLocalFields (parentCache.singleton ⟨8, by decide⟩) ((nextCache ⟨0, by decide⟩).singleton ⟨8, by decide⟩) :=
  fields_of_cachedLocal_eq _ _
    (D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037.unchanged_singleton_08 ⟨0, by decide⟩)

private theorem branch0_singleton_09 : FullLocalFields (singletonStep (parentCache.singleton ⟨9, by decide⟩) ⟨6, by decide⟩ ⟨0, by decide⟩) ((nextCache ⟨0, by decide⟩).singleton ⟨9, by decide⟩) :=
  fields_of_cachedLocal_eq _ _ (local_singleton_003_exact)

set_option maxHeartbeats 100000000 in
private theorem branch0_singleton_10 : FullLocalFields (parentCache.singleton ⟨10, by decide⟩) ((nextCache ⟨0, by decide⟩).singleton ⟨10, by decide⟩) :=
  fields_of_cachedLocal_eq _ _
    (D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037.unchanged_singleton_10 ⟨0, by decide⟩)

private theorem branch0_singleton_11 : FullLocalFields (singletonStep (parentCache.singleton ⟨11, by decide⟩) ⟨6, by decide⟩ ⟨0, by decide⟩) ((nextCache ⟨0, by decide⟩).singleton ⟨11, by decide⟩) :=
  fields_of_cachedLocal_eq _ _ (local_singleton_003_exact)

set_option maxHeartbeats 100000000 in
private theorem branch0_singleton_12 : FullLocalFields (parentCache.singleton ⟨12, by decide⟩) ((nextCache ⟨0, by decide⟩).singleton ⟨12, by decide⟩) :=
  fields_of_cachedLocal_eq _ _
    (D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037.unchanged_singleton_12 ⟨0, by decide⟩)

set_option maxHeartbeats 100000000 in
private theorem branch0_singleton_13 : FullLocalFields (parentCache.singleton ⟨13, by decide⟩) ((nextCache ⟨0, by decide⟩).singleton ⟨13, by decide⟩) :=
  fields_of_cachedLocal_eq _ _
    (D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037.unchanged_singleton_13 ⟨0, by decide⟩)

private theorem branch0_singleton_14 : FullLocalFields (singletonStep (parentCache.singleton ⟨14, by decide⟩) ⟨0, by decide⟩ ⟨0, by decide⟩) ((nextCache ⟨0, by decide⟩).singleton ⟨14, by decide⟩) :=
  fields_of_cachedLocal_eq _ _ (local_singleton_004_exact)

set_option maxHeartbeats 100000000 in
private theorem branch0_singleton_15 : FullLocalFields (parentCache.singleton ⟨15, by decide⟩) ((nextCache ⟨0, by decide⟩).singleton ⟨15, by decide⟩) :=
  fields_of_cachedLocal_eq _ _
    (D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037.unchanged_singleton_15 ⟨0, by decide⟩)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem branch0_step :
    step parentCache (coordinate 18) ⟨0, by decide⟩ = nextCache ⟨0, by decide⟩ := by
  apply step_at18_eq_of_local_fields
  · intro k
    fin_cases k
    · exact branch0_triangle_00
    · exact branch0_triangle_01
    · exact branch0_triangle_02
    · exact branch0_triangle_03
    · exact branch0_triangle_04
    · exact branch0_triangle_05
    · exact branch0_triangle_06
    · exact branch0_triangle_07
    · exact branch0_triangle_08
    · exact branch0_triangle_09
    · exact branch0_triangle_10
    · exact branch0_triangle_11
    · exact branch0_triangle_12
    · exact branch0_triangle_13
    · exact branch0_triangle_14
    · exact branch0_triangle_15
  · intro k
    fin_cases k
    · exact branch0_singleton_00
    · exact branch0_singleton_01
    · exact branch0_singleton_02
    · exact branch0_singleton_03
    · exact branch0_singleton_04
    · exact branch0_singleton_05
    · exact branch0_singleton_06
    · exact branch0_singleton_07
    · exact branch0_singleton_08
    · exact branch0_singleton_09
    · exact branch0_singleton_10
    · exact branch0_singleton_11
    · exact branch0_singleton_12
    · exact branch0_singleton_13
    · exact branch0_singleton_14
    · exact branch0_singleton_15

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem branch0_bound : scale ≤ lower (nextCache ⟨0, by decide⟩) := by
  simp only [nextCache, Matrix.cons_val_zero', Matrix.cons_val_succ']
  rw [D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037.child0_lower_exact]
  change (6987435 : ℤ) ≤ 20686156202449920
  decide +kernel

#print axioms branch0_step
#print axioms branch0_bound

end D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037
