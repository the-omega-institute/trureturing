/- Temporary same-certificate probe: it checks eight literal actual prefix
subtrees per local block. It is not the full simulation certificate, a final
original-score theorem, or an independently deliverable numeric instance. -/
import D5.S3.Quantum.Entanglement.EJM.EJMMDDData
import D5.S3.Quantum.Entanglement.EJM.EJMCacheState
import D5.S3.Quantum.Entanglement.EJM.EJMMDDPrefixSimulation
import D5.S3.Quantum.Entanglement.EJM.EJMMDDCacheBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
set_option Elab.async false

namespace D5.S3.Quantum.Entanglement.EJM.EJMMDDNumericProbe
open D5.S0.Certificates.FiniteMDDCacheSimulation
open D5.S3.Quantum.Entanglement.EJM.EJMMDDData
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMMDDPrefixSimulation
open D5.S3.Quantum.Entanglement.EJM.EJMMDDCacheBridge

set_option trace.profiler true in
private theorem triangle_ordering_probe : ∀ j : Fin 8,
    checkOrderedAt triangleNodes triangleLevel
      ⟨4582 + j.val, by have h := j.isLt; change 4582 + j.val < 76663; omega⟩ = true := by
  decide +kernel
#print axioms triangle_ordering_probe

set_option trace.profiler true in
private theorem singleton_ordering_probe : ∀ j : Fin 8,
    checkOrderedAt singletonNodes singletonLevel
      ⟨1192 + j.val, by have h := j.isLt; change 1192 + j.val < 19951; omega⟩ = true := by
  decide +kernel
#print axioms singleton_ordering_probe

set_option trace.profiler true in
private theorem triangle_indexed_prefixes : ∀ j : Fin 8,
    trianglePrefixCheck ⟨j.val, by have h := j.isLt; change j.val < 65536; omega⟩ = true := by
  decide +kernel
#print axioms triangle_indexed_prefixes

set_option trace.profiler true in
private theorem singleton_indexed_prefixes : ∀ j : Fin 8,
    singletonPrefixCheck ⟨j.val, by have h := j.isLt; change j.val < 16384; omega⟩ = true := by
  decide +kernel
#print axioms singleton_indexed_prefixes

set_option trace.profiler true in
private theorem triangle_prefix_0 :
    checkSimulation triangleNodes triangleStep (fun current => current.row.lower)
      3 ⟨60055, by decide⟩ (triangleStep (triangleStep (triangleStep (triangleStep (triangleStep (triangleStep (triangleStep (triangleStep (initial.triangle 0) 9 0) 8 0) 7 0) 6 0) 5 0) 4 0) 3 0) 2 0) = true := by
  decide +kernel
#print axioms triangle_prefix_0

set_option trace.profiler true in
private theorem triangle_prefix_1 :
    checkSimulation triangleNodes triangleStep (fun current => current.row.lower)
      3 ⟨59340, by decide⟩ (triangleStep (triangleStep (triangleStep (triangleStep (triangleStep (triangleStep (triangleStep (triangleStep (initial.triangle 0) 9 0) 8 0) 7 0) 6 0) 5 0) 4 0) 3 0) 2 1) = true := by
  decide +kernel
#print axioms triangle_prefix_1

set_option trace.profiler true in
private theorem triangle_prefix_2 :
    checkSimulation triangleNodes triangleStep (fun current => current.row.lower)
      3 ⟨59341, by decide⟩ (triangleStep (triangleStep (triangleStep (triangleStep (triangleStep (triangleStep (triangleStep (triangleStep (initial.triangle 0) 9 0) 8 0) 7 0) 6 0) 5 0) 4 0) 3 0) 2 2) = true := by
  decide +kernel
#print axioms triangle_prefix_2

set_option trace.profiler true in
private theorem triangle_prefix_3 :
    checkSimulation triangleNodes triangleStep (fun current => current.row.lower)
      3 ⟨59342, by decide⟩ (triangleStep (triangleStep (triangleStep (triangleStep (triangleStep (triangleStep (triangleStep (triangleStep (initial.triangle 0) 9 0) 8 0) 7 0) 6 0) 5 0) 4 0) 3 0) 2 3) = true := by
  decide +kernel
#print axioms triangle_prefix_3

set_option trace.profiler true in
private theorem triangle_prefix_4 :
    checkSimulation triangleNodes triangleStep (fun current => current.row.lower)
      3 ⟨59154, by decide⟩ (triangleStep (triangleStep (triangleStep (triangleStep (triangleStep (triangleStep (triangleStep (triangleStep (initial.triangle 0) 9 0) 8 0) 7 0) 6 0) 5 0) 4 0) 3 1) 2 0) = true := by
  decide +kernel
#print axioms triangle_prefix_4

set_option trace.profiler true in
private theorem triangle_prefix_5 :
    checkSimulation triangleNodes triangleStep (fun current => current.row.lower)
      3 ⟨61098, by decide⟩ (triangleStep (triangleStep (triangleStep (triangleStep (triangleStep (triangleStep (triangleStep (triangleStep (initial.triangle 0) 9 0) 8 0) 7 0) 6 0) 5 0) 4 0) 3 1) 2 1) = true := by
  decide +kernel
#print axioms triangle_prefix_5

set_option trace.profiler true in
private theorem triangle_prefix_6 :
    checkSimulation triangleNodes triangleStep (fun current => current.row.lower)
      3 ⟨63579, by decide⟩ (triangleStep (triangleStep (triangleStep (triangleStep (triangleStep (triangleStep (triangleStep (triangleStep (initial.triangle 0) 9 0) 8 0) 7 0) 6 0) 5 0) 4 0) 3 1) 2 2) = true := by
  decide +kernel
#print axioms triangle_prefix_6

set_option trace.profiler true in
private theorem triangle_prefix_7 :
    checkSimulation triangleNodes triangleStep (fun current => current.row.lower)
      3 ⟨63580, by decide⟩ (triangleStep (triangleStep (triangleStep (triangleStep (triangleStep (triangleStep (triangleStep (triangleStep (initial.triangle 0) 9 0) 8 0) 7 0) 6 0) 5 0) 4 0) 3 1) 2 3) = true := by
  decide +kernel
#print axioms triangle_prefix_7

set_option trace.profiler true in
private theorem singleton_prefix_0 :
    checkSimulation singletonNodes singletonStep (fun current => current.row.lower)
      3 ⟨12551, by decide⟩ (singletonStep (singletonStep (singletonStep (singletonStep (singletonStep (singletonStep (singletonStep (initial.singleton 0) 8 0) 7 0) 6 0) 5 0) 4 0) 3 0) 2 0) = true := by
  decide +kernel
#print axioms singleton_prefix_0

set_option trace.profiler true in
private theorem singleton_prefix_1 :
    checkSimulation singletonNodes singletonStep (fun current => current.row.lower)
      3 ⟨15014, by decide⟩ (singletonStep (singletonStep (singletonStep (singletonStep (singletonStep (singletonStep (singletonStep (initial.singleton 0) 8 0) 7 0) 6 0) 5 0) 4 0) 3 0) 2 1) = true := by
  decide +kernel
#print axioms singleton_prefix_1

set_option trace.profiler true in
private theorem singleton_prefix_2 :
    checkSimulation singletonNodes singletonStep (fun current => current.row.lower)
      3 ⟨15017, by decide⟩ (singletonStep (singletonStep (singletonStep (singletonStep (singletonStep (singletonStep (singletonStep (initial.singleton 0) 8 0) 7 0) 6 0) 5 0) 4 0) 3 0) 2 2) = true := by
  decide +kernel
#print axioms singleton_prefix_2

set_option trace.profiler true in
private theorem singleton_prefix_3 :
    checkSimulation singletonNodes singletonStep (fun current => current.row.lower)
      3 ⟨15020, by decide⟩ (singletonStep (singletonStep (singletonStep (singletonStep (singletonStep (singletonStep (singletonStep (initial.singleton 0) 8 0) 7 0) 6 0) 5 0) 4 0) 3 0) 2 3) = true := by
  decide +kernel
#print axioms singleton_prefix_3

set_option trace.profiler true in
private theorem singleton_prefix_4 :
    checkSimulation singletonNodes singletonStep (fun current => current.row.lower)
      3 ⟨15012, by decide⟩ (singletonStep (singletonStep (singletonStep (singletonStep (singletonStep (singletonStep (singletonStep (initial.singleton 0) 8 0) 7 0) 6 0) 5 0) 4 0) 3 1) 2 0) = true := by
  decide +kernel
#print axioms singleton_prefix_4

set_option trace.profiler true in
private theorem singleton_prefix_5 :
    checkSimulation singletonNodes singletonStep (fun current => current.row.lower)
      3 ⟨15488, by decide⟩ (singletonStep (singletonStep (singletonStep (singletonStep (singletonStep (singletonStep (singletonStep (initial.singleton 0) 8 0) 7 0) 6 0) 5 0) 4 0) 3 1) 2 1) = true := by
  decide +kernel
#print axioms singleton_prefix_5

set_option trace.profiler true in
private theorem singleton_prefix_6 :
    checkSimulation singletonNodes singletonStep (fun current => current.row.lower)
      3 ⟨15473, by decide⟩ (singletonStep (singletonStep (singletonStep (singletonStep (singletonStep (singletonStep (singletonStep (initial.singleton 0) 8 0) 7 0) 6 0) 5 0) 4 0) 3 1) 2 2) = true := by
  decide +kernel
#print axioms singleton_prefix_6

set_option trace.profiler true in
private theorem singleton_prefix_7 :
    checkSimulation singletonNodes singletonStep (fun current => current.row.lower)
      3 ⟨15477, by decide⟩ (singletonStep (singletonStep (singletonStep (singletonStep (singletonStep (singletonStep (singletonStep (initial.singleton 0) 8 0) 7 0) 6 0) 5 0) 4 0) 3 1) 2 3) = true := by
  decide +kernel
#print axioms singleton_prefix_7

end D5.S3.Quantum.Entanglement.EJM.EJMMDDNumericProbe
