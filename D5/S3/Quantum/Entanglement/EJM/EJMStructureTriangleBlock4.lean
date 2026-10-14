/- GID: D5/S3/Quantum/Entanglement/EJM/EJMStructureTriangleBlock4
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMStructureTriangleBlock4
   mirror-E: none(waiver:actual-exact-certificate-premise)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.associated_lower_le_score; premises=D5/S3/Quantum/Entanglement/EJM/EJMStructureTriangleBlock4.accepted
   digest: Exact structural checks for actual triangle row interval [32768, 40960). -/

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
namespace D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock4
open D5.S0.Certificates.FinitePartialBoundDAG
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport
set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem triangle_chunk_32768 : ∀ j : Fin 1024,
    checkStructure trianglePartialAct triangleRows
      ⟨32768 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem triangle_chunk_33792 : ∀ j : Fin 1024,
    checkStructure trianglePartialAct triangleRows
      ⟨33792 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem triangle_chunk_34816 : ∀ j : Fin 1024,
    checkStructure trianglePartialAct triangleRows
      ⟨34816 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem triangle_chunk_35840 : ∀ j : Fin 1024,
    checkStructure trianglePartialAct triangleRows
      ⟨35840 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem triangle_chunk_36864 : ∀ j : Fin 1024,
    checkStructure trianglePartialAct triangleRows
      ⟨36864 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem triangle_chunk_37888 : ∀ j : Fin 1024,
    checkStructure trianglePartialAct triangleRows
      ⟨37888 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem triangle_chunk_38912 : ∀ j : Fin 1024,
    checkStructure trianglePartialAct triangleRows
      ⟨38912 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem triangle_chunk_39936 : ∀ j : Fin 1024,
    checkStructure trianglePartialAct triangleRows
      ⟨39936 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

/-- Every actual row in this whole interval passes the original structural check. -/
theorem accepted (j : Fin 8192) :
    checkStructure trianglePartialAct triangleRows
      ⟨32768 + j.val, by have h := j.isLt; omega⟩ = true := by
  by_cases h0 : j.val < 1024
  ·
    let k : Fin 1024 := ⟨j.val - 0, by have h := j.isLt; omega⟩
    have he : (⟨32768 + k.val, by have h := k.isLt; omega⟩ : Fin 41294) =
        ⟨32768 + j.val, by have h := j.isLt; omega⟩ := by
      apply Fin.ext
      dsimp [k] <;> omega
    simpa only [he] using triangle_chunk_32768 k
  by_cases h1 : j.val < 2048
  ·
    let k : Fin 1024 := ⟨j.val - 1024, by have h := j.isLt; omega⟩
    have he : (⟨33792 + k.val, by have h := k.isLt; omega⟩ : Fin 41294) =
        ⟨32768 + j.val, by have h := j.isLt; omega⟩ := by
      apply Fin.ext
      dsimp [k] <;> omega
    simpa only [he] using triangle_chunk_33792 k
  by_cases h2 : j.val < 3072
  ·
    let k : Fin 1024 := ⟨j.val - 2048, by have h := j.isLt; omega⟩
    have he : (⟨34816 + k.val, by have h := k.isLt; omega⟩ : Fin 41294) =
        ⟨32768 + j.val, by have h := j.isLt; omega⟩ := by
      apply Fin.ext
      dsimp [k] <;> omega
    simpa only [he] using triangle_chunk_34816 k
  by_cases h3 : j.val < 4096
  ·
    let k : Fin 1024 := ⟨j.val - 3072, by have h := j.isLt; omega⟩
    have he : (⟨35840 + k.val, by have h := k.isLt; omega⟩ : Fin 41294) =
        ⟨32768 + j.val, by have h := j.isLt; omega⟩ := by
      apply Fin.ext
      dsimp [k] <;> omega
    simpa only [he] using triangle_chunk_35840 k
  by_cases h4 : j.val < 5120
  ·
    let k : Fin 1024 := ⟨j.val - 4096, by have h := j.isLt; omega⟩
    have he : (⟨36864 + k.val, by have h := k.isLt; omega⟩ : Fin 41294) =
        ⟨32768 + j.val, by have h := j.isLt; omega⟩ := by
      apply Fin.ext
      dsimp [k] <;> omega
    simpa only [he] using triangle_chunk_36864 k
  by_cases h5 : j.val < 6144
  ·
    let k : Fin 1024 := ⟨j.val - 5120, by have h := j.isLt; omega⟩
    have he : (⟨37888 + k.val, by have h := k.isLt; omega⟩ : Fin 41294) =
        ⟨32768 + j.val, by have h := j.isLt; omega⟩ := by
      apply Fin.ext
      dsimp [k] <;> omega
    simpa only [he] using triangle_chunk_37888 k
  by_cases h6 : j.val < 7168
  ·
    let k : Fin 1024 := ⟨j.val - 6144, by have h := j.isLt; omega⟩
    have he : (⟨38912 + k.val, by have h := k.isLt; omega⟩ : Fin 41294) =
        ⟨32768 + j.val, by have h := j.isLt; omega⟩ := by
      apply Fin.ext
      dsimp [k] <;> omega
    simpa only [he] using triangle_chunk_38912 k
  let k : Fin 1024 := ⟨j.val - 7168, by have h := j.isLt; omega⟩
  have he : (⟨39936 + k.val, by have h := k.isLt; omega⟩ : Fin 41294) =
      ⟨32768 + j.val, by have h := j.isLt; omega⟩ := by
    apply Fin.ext
    dsimp [k] <;> omega
  simpa only [he] using triangle_chunk_39936 k

#print axioms accepted
end D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock4
