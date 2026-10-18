/- GID: D5/S3/Quantum/Entanglement/EJM/CacheReceipts/Triangle/Mirror10
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/CacheReceipts/Triangle/Mirror10
   mirror-E: none(waiver:actual-exact-certificate-cache)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/EJMTriangleCacheReceipts.mirror_accepted; premises=D5/S3/Quantum/Entanglement/EJM/CacheReceipts/Triangle/Mirror10.accepted
   digest: Exact original triangle mirror kernel receipts for row interval [40960, 41294). -/

/- Prepared source; this layout has not been compiled. The unchanged finite
kernel reductions are consumed by the original complete receipt root in the
same delivery. All original rows and transition value branches are retained.
Escape registration remains unfinished under issues #16309 and #15859;
no declared_validated audit status is asserted. -/

import D5.S3.Quantum.Entanglement.EJM.EJMTriangleCacheData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
-- Complete each original kernel receipt before beginning the next block.
set_option Elab.async false

namespace D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Mirror10
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport
open D5.S3.Quantum.Entanglement.EJM.EJMTriangleCacheData

set_option maxHeartbeats 100000000 in
-- Exhaust the unchanged finite row block with kernel reduction.
set_option trace.profiler true in
private theorem mirror_40960 : ∀ k : Fin 128,
    checkMirrorFields ⟨40960 + k.val, by have h := k.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Exhaust the unchanged finite row block with kernel reduction.
set_option trace.profiler true in
private theorem mirror_41088 : ∀ k : Fin 128,
    checkMirrorFields ⟨41088 + k.val, by have h := k.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Exhaust the unchanged finite row block with kernel reduction.
set_option trace.profiler true in
private theorem mirror_41216 : ∀ k : Fin 78,
    checkMirrorFields ⟨41216 + k.val, by have h := k.isLt; omega⟩ = true := by
  decide +kernel

-- Combine every original chunk in this exact interval.
set_option maxHeartbeats 10000000 in
theorem accepted (j : Fin 41294) (lower : 40960 ≤ j.val)
    (upper : j.val < 41294) : checkMirrorFields j = true := by
  by_cases h0 : j.val < 41088
  · let k : Fin 128 := ⟨j.val - 40960, by have h := j.isLt; omega⟩
    have he : (⟨40960 + k.val, by dsimp [k]; have h := k.isLt; omega⟩ : Fin 41294) = j := by
      apply Fin.ext
      dsimp [k]
      omega
    simpa only [he] using mirror_40960 k
  by_cases h1 : j.val < 41216
  · let k : Fin 128 := ⟨j.val - 41088, by have h := j.isLt; omega⟩
    have he : (⟨41088 + k.val, by dsimp [k]; have h := k.isLt; omega⟩ : Fin 41294) = j := by
      apply Fin.ext
      dsimp [k]
      omega
    simpa only [he] using mirror_41088 k
  let k : Fin 78 := ⟨j.val - 41216, by have h := j.isLt; omega⟩
  have he : (⟨41216 + k.val, by dsimp [k]; have h := k.isLt; omega⟩ : Fin 41294) = j := by
    apply Fin.ext
    dsimp [k]
    omega
  simpa only [he] using mirror_41216 k

end D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle.Mirror10
