/- GID: D5/S3/Quantum/Entanglement/EJM/CacheReceipts/Singleton/Mirror02
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/CacheReceipts/Singleton/Mirror02
   mirror-E: none(waiver:actual-exact-certificate-cache)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/EJMSingletonCacheReceipts.mirror_accepted; premises=D5/S3/Quantum/Entanglement/EJM/CacheReceipts/Singleton/Mirror02.accepted
   digest: Exact original singleton mirror kernel receipts for row interval [8192, 8689). -/

/- Prepared source; this layout has not been compiled. The unchanged finite
kernel reductions are consumed by the original complete receipt root in the
same delivery. All original rows and transition value branches are retained.
Escape registration remains unfinished under issues #16309 and #15859;
no declared_validated audit status is asserted. -/

import D5.S3.Quantum.Entanglement.EJM.EJMSingletonCacheData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
-- Complete each original kernel receipt before beginning the next block.
set_option Elab.async false

namespace D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Singleton.Mirror02
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport
open D5.S3.Quantum.Entanglement.EJM.EJMSingletonCacheData

set_option maxHeartbeats 100000000 in
-- Exhaust the unchanged finite row block with kernel reduction.
set_option trace.profiler true in
private theorem mirror_8192 : ∀ k : Fin 128,
    checkMirrorFields ⟨8192 + k.val, by have h := k.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Exhaust the unchanged finite row block with kernel reduction.
set_option trace.profiler true in
private theorem mirror_8320 : ∀ k : Fin 128,
    checkMirrorFields ⟨8320 + k.val, by have h := k.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Exhaust the unchanged finite row block with kernel reduction.
set_option trace.profiler true in
private theorem mirror_8448 : ∀ k : Fin 128,
    checkMirrorFields ⟨8448 + k.val, by have h := k.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Exhaust the unchanged finite row block with kernel reduction.
set_option trace.profiler true in
private theorem mirror_8576 : ∀ k : Fin 113,
    checkMirrorFields ⟨8576 + k.val, by have h := k.isLt; omega⟩ = true := by
  decide +kernel

-- Combine every original chunk in this exact interval.
set_option maxHeartbeats 10000000 in
theorem accepted (j : Fin 8689) (lower : 8192 ≤ j.val)
    (upper : j.val < 8689) : checkMirrorFields j = true := by
  by_cases h0 : j.val < 8320
  · let k : Fin 128 := ⟨j.val - 8192, by have h := j.isLt; omega⟩
    have he : (⟨8192 + k.val, by dsimp [k]; have h := k.isLt; omega⟩ : Fin 8689) = j := by
      apply Fin.ext
      dsimp [k]
      omega
    simpa only [he] using mirror_8192 k
  by_cases h1 : j.val < 8448
  · let k : Fin 128 := ⟨j.val - 8320, by have h := j.isLt; omega⟩
    have he : (⟨8320 + k.val, by dsimp [k]; have h := k.isLt; omega⟩ : Fin 8689) = j := by
      apply Fin.ext
      dsimp [k]
      omega
    simpa only [he] using mirror_8320 k
  by_cases h2 : j.val < 8576
  · let k : Fin 128 := ⟨j.val - 8448, by have h := j.isLt; omega⟩
    have he : (⟨8448 + k.val, by dsimp [k]; have h := k.isLt; omega⟩ : Fin 8689) = j := by
      apply Fin.ext
      dsimp [k]
      omega
    simpa only [he] using mirror_8448 k
  let k : Fin 113 := ⟨j.val - 8576, by have h := j.isLt; omega⟩
  have he : (⟨8576 + k.val, by dsimp [k]; have h := k.isLt; omega⟩ : Fin 8689) = j := by
    apply Fin.ext
    dsimp [k]
    omega
  simpa only [he] using mirror_8576 k

end D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Singleton.Mirror02
