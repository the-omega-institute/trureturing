/- GID: D5/S3/Quantum/Entanglement/EJM/EJMStructureTriangleBlock2
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMStructureTriangleBlock2
   mirror-E: none(waiver:actual-exact-certificate-premise)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.associated_lower_le_score; premises=D5/S3/Quantum/Entanglement/EJM/EJMStructureTriangleBlock2.accepted
   digest: Exact structural checks for actual triangle row interval [16384, 24576). -/

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
namespace D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock2
open D5.S0.Certificates.FinitePartialBoundDAG
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport
set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem triangle_chunk_16384 : ∀ j : Fin 1024,
    checkStructure trianglePartialAct triangleRows
      ⟨16384 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem triangle_chunk_17408 : ∀ j : Fin 1024,
    checkStructure trianglePartialAct triangleRows
      ⟨17408 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem triangle_chunk_18432 : ∀ j : Fin 1024,
    checkStructure trianglePartialAct triangleRows
      ⟨18432 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem triangle_chunk_19456 : ∀ j : Fin 1024,
    checkStructure trianglePartialAct triangleRows
      ⟨19456 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem triangle_chunk_20480 : ∀ j : Fin 1024,
    checkStructure trianglePartialAct triangleRows
      ⟨20480 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem triangle_chunk_21504 : ∀ j : Fin 1024,
    checkStructure trianglePartialAct triangleRows
      ⟨21504 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem triangle_chunk_22528 : ∀ j : Fin 1024,
    checkStructure trianglePartialAct triangleRows
      ⟨22528 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem triangle_chunk_23552 : ∀ j : Fin 1024,
    checkStructure trianglePartialAct triangleRows
      ⟨23552 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

/-- Every actual row in this whole interval passes the original structural check. -/
theorem accepted (j : Fin 8192) :
    checkStructure trianglePartialAct triangleRows
      ⟨16384 + j.val, by have h := j.isLt; omega⟩ = true := by
  by_cases h0 : j.val < 1024
  ·
    let k : Fin 1024 := ⟨j.val - 0, by have h := j.isLt; omega⟩
    have he : (⟨16384 + k.val, by have h := k.isLt; omega⟩ : Fin 41294) =
        ⟨16384 + j.val, by have h := j.isLt; omega⟩ := by
      apply Fin.ext
      dsimp [k] <;> omega
    simpa only [he] using triangle_chunk_16384 k
  by_cases h1 : j.val < 2048
  ·
    let k : Fin 1024 := ⟨j.val - 1024, by have h := j.isLt; omega⟩
    have he : (⟨17408 + k.val, by have h := k.isLt; omega⟩ : Fin 41294) =
        ⟨16384 + j.val, by have h := j.isLt; omega⟩ := by
      apply Fin.ext
      dsimp [k] <;> omega
    simpa only [he] using triangle_chunk_17408 k
  by_cases h2 : j.val < 3072
  ·
    let k : Fin 1024 := ⟨j.val - 2048, by have h := j.isLt; omega⟩
    have he : (⟨18432 + k.val, by have h := k.isLt; omega⟩ : Fin 41294) =
        ⟨16384 + j.val, by have h := j.isLt; omega⟩ := by
      apply Fin.ext
      dsimp [k] <;> omega
    simpa only [he] using triangle_chunk_18432 k
  by_cases h3 : j.val < 4096
  ·
    let k : Fin 1024 := ⟨j.val - 3072, by have h := j.isLt; omega⟩
    have he : (⟨19456 + k.val, by have h := k.isLt; omega⟩ : Fin 41294) =
        ⟨16384 + j.val, by have h := j.isLt; omega⟩ := by
      apply Fin.ext
      dsimp [k] <;> omega
    simpa only [he] using triangle_chunk_19456 k
  by_cases h4 : j.val < 5120
  ·
    let k : Fin 1024 := ⟨j.val - 4096, by have h := j.isLt; omega⟩
    have he : (⟨20480 + k.val, by have h := k.isLt; omega⟩ : Fin 41294) =
        ⟨16384 + j.val, by have h := j.isLt; omega⟩ := by
      apply Fin.ext
      dsimp [k] <;> omega
    simpa only [he] using triangle_chunk_20480 k
  by_cases h5 : j.val < 6144
  ·
    let k : Fin 1024 := ⟨j.val - 5120, by have h := j.isLt; omega⟩
    have he : (⟨21504 + k.val, by have h := k.isLt; omega⟩ : Fin 41294) =
        ⟨16384 + j.val, by have h := j.isLt; omega⟩ := by
      apply Fin.ext
      dsimp [k] <;> omega
    simpa only [he] using triangle_chunk_21504 k
  by_cases h6 : j.val < 7168
  ·
    let k : Fin 1024 := ⟨j.val - 6144, by have h := j.isLt; omega⟩
    have he : (⟨22528 + k.val, by have h := k.isLt; omega⟩ : Fin 41294) =
        ⟨16384 + j.val, by have h := j.isLt; omega⟩ := by
      apply Fin.ext
      dsimp [k] <;> omega
    simpa only [he] using triangle_chunk_22528 k
  let k : Fin 1024 := ⟨j.val - 7168, by have h := j.isLt; omega⟩
  have he : (⟨23552 + k.val, by have h := k.isLt; omega⟩ : Fin 41294) =
      ⟨16384 + j.val, by have h := j.isLt; omega⟩ := by
    apply Fin.ext
    dsimp [k] <;> omega
  simpa only [he] using triangle_chunk_23552 k

#print axioms accepted
end D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock2
