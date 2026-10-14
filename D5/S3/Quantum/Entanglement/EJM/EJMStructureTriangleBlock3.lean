/- GID: D5/S3/Quantum/Entanglement/EJM/EJMStructureTriangleBlock3
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMStructureTriangleBlock3
   mirror-E: none(waiver:actual-exact-certificate-premise)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.associated_lower_le_score; premises=D5/S3/Quantum/Entanglement/EJM/EJMStructureTriangleBlock3.accepted
   digest: Exact structural checks for actual triangle row interval [24576, 32768). -/

/- These are the same original checkStructure obligations, split at existing
1024-row boundaries so interruption preserves completed kernel modules.
All literal assignments, actions, child indices and lower bounds remain.
No independent finite-instance result or global acceptance is asserted.
The complete EJMStructureCertificates receipt consumes this entire interval.
Source-bound registration remains unfinished under issue #16309. -/

import D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option linter.style.longLine false
namespace D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock3
open D5.S0.Certificates.FinitePartialBoundDAG
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport
set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem triangle_chunk_24576 : ∀ j : Fin 1024,
    checkStructure trianglePartialAct triangleRows
      ⟨24576 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem triangle_chunk_25600 : ∀ j : Fin 1024,
    checkStructure trianglePartialAct triangleRows
      ⟨25600 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem triangle_chunk_26624 : ∀ j : Fin 1024,
    checkStructure trianglePartialAct triangleRows
      ⟨26624 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem triangle_chunk_27648 : ∀ j : Fin 1024,
    checkStructure trianglePartialAct triangleRows
      ⟨27648 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem triangle_chunk_28672 : ∀ j : Fin 1024,
    checkStructure trianglePartialAct triangleRows
      ⟨28672 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem triangle_chunk_29696 : ∀ j : Fin 1024,
    checkStructure trianglePartialAct triangleRows
      ⟨29696 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem triangle_chunk_30720 : ∀ j : Fin 1024,
    checkStructure trianglePartialAct triangleRows
      ⟨30720 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem triangle_chunk_31744 : ∀ j : Fin 1024,
    checkStructure trianglePartialAct triangleRows
      ⟨31744 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

/-- Every actual row in this whole interval passes the original structural check. -/
theorem accepted (j : Fin 8192) :
    checkStructure trianglePartialAct triangleRows
      ⟨24576 + j.val, by have h := j.isLt; omega⟩ = true := by
  by_cases h0 : j.val < 1024
  ·
    let k : Fin 1024 := ⟨j.val - 0, by have h := j.isLt; omega⟩
    have he : (⟨24576 + k.val, by have h := k.isLt; omega⟩ : Fin 41294) =
        ⟨24576 + j.val, by have h := j.isLt; omega⟩ := by
      apply Fin.ext
      dsimp [k] <;> omega
    simpa only [he] using triangle_chunk_24576 k
  by_cases h1 : j.val < 2048
  ·
    let k : Fin 1024 := ⟨j.val - 1024, by have h := j.isLt; omega⟩
    have he : (⟨25600 + k.val, by have h := k.isLt; omega⟩ : Fin 41294) =
        ⟨24576 + j.val, by have h := j.isLt; omega⟩ := by
      apply Fin.ext
      dsimp [k] <;> omega
    simpa only [he] using triangle_chunk_25600 k
  by_cases h2 : j.val < 3072
  ·
    let k : Fin 1024 := ⟨j.val - 2048, by have h := j.isLt; omega⟩
    have he : (⟨26624 + k.val, by have h := k.isLt; omega⟩ : Fin 41294) =
        ⟨24576 + j.val, by have h := j.isLt; omega⟩ := by
      apply Fin.ext
      dsimp [k] <;> omega
    simpa only [he] using triangle_chunk_26624 k
  by_cases h3 : j.val < 4096
  ·
    let k : Fin 1024 := ⟨j.val - 3072, by have h := j.isLt; omega⟩
    have he : (⟨27648 + k.val, by have h := k.isLt; omega⟩ : Fin 41294) =
        ⟨24576 + j.val, by have h := j.isLt; omega⟩ := by
      apply Fin.ext
      dsimp [k] <;> omega
    simpa only [he] using triangle_chunk_27648 k
  by_cases h4 : j.val < 5120
  ·
    let k : Fin 1024 := ⟨j.val - 4096, by have h := j.isLt; omega⟩
    have he : (⟨28672 + k.val, by have h := k.isLt; omega⟩ : Fin 41294) =
        ⟨24576 + j.val, by have h := j.isLt; omega⟩ := by
      apply Fin.ext
      dsimp [k] <;> omega
    simpa only [he] using triangle_chunk_28672 k
  by_cases h5 : j.val < 6144
  ·
    let k : Fin 1024 := ⟨j.val - 5120, by have h := j.isLt; omega⟩
    have he : (⟨29696 + k.val, by have h := k.isLt; omega⟩ : Fin 41294) =
        ⟨24576 + j.val, by have h := j.isLt; omega⟩ := by
      apply Fin.ext
      dsimp [k] <;> omega
    simpa only [he] using triangle_chunk_29696 k
  by_cases h6 : j.val < 7168
  ·
    let k : Fin 1024 := ⟨j.val - 6144, by have h := j.isLt; omega⟩
    have he : (⟨30720 + k.val, by have h := k.isLt; omega⟩ : Fin 41294) =
        ⟨24576 + j.val, by have h := j.isLt; omega⟩ := by
      apply Fin.ext
      dsimp [k] <;> omega
    simpa only [he] using triangle_chunk_30720 k
  let k : Fin 1024 := ⟨j.val - 7168, by have h := j.isLt; omega⟩
  have he : (⟨31744 + k.val, by have h := k.isLt; omega⟩ : Fin 41294) =
      ⟨24576 + j.val, by have h := j.isLt; omega⟩ := by
    apply Fin.ext
    dsimp [k] <;> omega
  simpa only [he] using triangle_chunk_31744 k

#print axioms accepted
end D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock3
