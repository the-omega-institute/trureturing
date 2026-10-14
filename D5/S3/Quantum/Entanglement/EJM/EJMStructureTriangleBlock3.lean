/- GID: D5/S3/Quantum/Entanglement/EJM/EJMStructureTriangleBlock3
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMStructureTriangleBlock3
   mirror-E: none(waiver:actual-exact-certificate-premise)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.associated_lower_le_score; premises=D5/S3/Quantum/Entanglement/EJM/EJMStructureTriangleBlock3.accepted
   digest: Exact structural checks for actual triangle row interval [12288, 16384). -/

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
private theorem triangle_chunk_12288 : ∀ j : Fin 1024,
    checkStructure trianglePartialAct triangleRows
      ⟨12288 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem triangle_chunk_13312 : ∀ j : Fin 1024,
    checkStructure trianglePartialAct triangleRows
      ⟨13312 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem triangle_chunk_14336 : ∀ j : Fin 1024,
    checkStructure trianglePartialAct triangleRows
      ⟨14336 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem triangle_chunk_15360 : ∀ j : Fin 1024,
    checkStructure trianglePartialAct triangleRows
      ⟨15360 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

/-- Every actual row in this whole interval passes the original structural check. -/
theorem accepted (j : Fin 4096) :
    checkStructure trianglePartialAct triangleRows
      ⟨12288 + j.val, by have h := j.isLt; omega⟩ = true := by
  by_cases h0 : j.val < 1024
  ·
    let k : Fin 1024 := ⟨j.val - 0, by have h := j.isLt; omega⟩
    have he : (⟨12288 + k.val, by have h := k.isLt; omega⟩ : Fin 41294) =
        ⟨12288 + j.val, by have h := j.isLt; omega⟩ := by
      apply Fin.ext
      dsimp [k] <;> omega
    simpa only [he] using triangle_chunk_12288 k
  by_cases h1 : j.val < 2048
  ·
    let k : Fin 1024 := ⟨j.val - 1024, by have h := j.isLt; omega⟩
    have he : (⟨13312 + k.val, by have h := k.isLt; omega⟩ : Fin 41294) =
        ⟨12288 + j.val, by have h := j.isLt; omega⟩ := by
      apply Fin.ext
      dsimp [k] <;> omega
    simpa only [he] using triangle_chunk_13312 k
  by_cases h2 : j.val < 3072
  ·
    let k : Fin 1024 := ⟨j.val - 2048, by have h := j.isLt; omega⟩
    have he : (⟨14336 + k.val, by have h := k.isLt; omega⟩ : Fin 41294) =
        ⟨12288 + j.val, by have h := j.isLt; omega⟩ := by
      apply Fin.ext
      dsimp [k] <;> omega
    simpa only [he] using triangle_chunk_14336 k
  let k : Fin 1024 := ⟨j.val - 3072, by have h := j.isLt; omega⟩
  have he : (⟨15360 + k.val, by have h := k.isLt; omega⟩ : Fin 41294) =
      ⟨12288 + j.val, by have h := j.isLt; omega⟩ := by
    apply Fin.ext
    dsimp [k] <;> omega
  simpa only [he] using triangle_chunk_15360 k

#print axioms accepted
end D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock3
