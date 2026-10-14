/- GID: D5/S3/Quantum/Entanglement/EJM/EJMStructureSingletonBlock0
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMStructureSingletonBlock0
   mirror-E: none(waiver:actual-exact-certificate-premise)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.associated_lower_le_score; premises=D5/S3/Quantum/Entanglement/EJM/EJMStructureSingletonBlock0.accepted
   digest: Exact structural checks for actual singleton row interval [0, 8192). -/

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
namespace D5.S3.Quantum.Entanglement.EJM.EJMStructureSingletonBlock0
open D5.S0.Certificates.FinitePartialBoundDAG
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport
set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem singleton_chunk_0 : ∀ j : Fin 1024,
    checkStructure singletonPartialAct singletonRows
      ⟨0 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem singleton_chunk_1024 : ∀ j : Fin 1024,
    checkStructure singletonPartialAct singletonRows
      ⟨1024 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem singleton_chunk_2048 : ∀ j : Fin 1024,
    checkStructure singletonPartialAct singletonRows
      ⟨2048 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem singleton_chunk_3072 : ∀ j : Fin 1024,
    checkStructure singletonPartialAct singletonRows
      ⟨3072 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem singleton_chunk_4096 : ∀ j : Fin 1024,
    checkStructure singletonPartialAct singletonRows
      ⟨4096 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem singleton_chunk_5120 : ∀ j : Fin 1024,
    checkStructure singletonPartialAct singletonRows
      ⟨5120 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem singleton_chunk_6144 : ∀ j : Fin 1024,
    checkStructure singletonPartialAct singletonRows
      ⟨6144 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- Full literal row transport requires bounded kernel reduction.
private theorem singleton_chunk_7168 : ∀ j : Fin 1024,
    checkStructure singletonPartialAct singletonRows
      ⟨7168 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

/-- Every actual row in this whole interval passes the original structural check. -/
theorem accepted (j : Fin 8192) :
    checkStructure singletonPartialAct singletonRows
      ⟨0 + j.val, by have h := j.isLt; omega⟩ = true := by
  by_cases h0 : j.val < 1024
  ·
    let k : Fin 1024 := ⟨j.val - 0, by have h := j.isLt; omega⟩
    have he : (⟨0 + k.val, by have h := k.isLt; omega⟩ : Fin 8689) =
        ⟨0 + j.val, by have h := j.isLt; omega⟩ := by
      apply Fin.ext
      dsimp [k] <;> omega
    simpa only [he] using singleton_chunk_0 k
  by_cases h1 : j.val < 2048
  ·
    let k : Fin 1024 := ⟨j.val - 1024, by have h := j.isLt; omega⟩
    have he : (⟨1024 + k.val, by have h := k.isLt; omega⟩ : Fin 8689) =
        ⟨0 + j.val, by have h := j.isLt; omega⟩ := by
      apply Fin.ext
      dsimp [k] <;> omega
    simpa only [he] using singleton_chunk_1024 k
  by_cases h2 : j.val < 3072
  ·
    let k : Fin 1024 := ⟨j.val - 2048, by have h := j.isLt; omega⟩
    have he : (⟨2048 + k.val, by have h := k.isLt; omega⟩ : Fin 8689) =
        ⟨0 + j.val, by have h := j.isLt; omega⟩ := by
      apply Fin.ext
      dsimp [k] <;> omega
    simpa only [he] using singleton_chunk_2048 k
  by_cases h3 : j.val < 4096
  ·
    let k : Fin 1024 := ⟨j.val - 3072, by have h := j.isLt; omega⟩
    have he : (⟨3072 + k.val, by have h := k.isLt; omega⟩ : Fin 8689) =
        ⟨0 + j.val, by have h := j.isLt; omega⟩ := by
      apply Fin.ext
      dsimp [k] <;> omega
    simpa only [he] using singleton_chunk_3072 k
  by_cases h4 : j.val < 5120
  ·
    let k : Fin 1024 := ⟨j.val - 4096, by have h := j.isLt; omega⟩
    have he : (⟨4096 + k.val, by have h := k.isLt; omega⟩ : Fin 8689) =
        ⟨0 + j.val, by have h := j.isLt; omega⟩ := by
      apply Fin.ext
      dsimp [k] <;> omega
    simpa only [he] using singleton_chunk_4096 k
  by_cases h5 : j.val < 6144
  ·
    let k : Fin 1024 := ⟨j.val - 5120, by have h := j.isLt; omega⟩
    have he : (⟨5120 + k.val, by have h := k.isLt; omega⟩ : Fin 8689) =
        ⟨0 + j.val, by have h := j.isLt; omega⟩ := by
      apply Fin.ext
      dsimp [k] <;> omega
    simpa only [he] using singleton_chunk_5120 k
  by_cases h6 : j.val < 7168
  ·
    let k : Fin 1024 := ⟨j.val - 6144, by have h := j.isLt; omega⟩
    have he : (⟨6144 + k.val, by have h := k.isLt; omega⟩ : Fin 8689) =
        ⟨0 + j.val, by have h := j.isLt; omega⟩ := by
      apply Fin.ext
      dsimp [k] <;> omega
    simpa only [he] using singleton_chunk_6144 k
  let k : Fin 1024 := ⟨j.val - 7168, by have h := j.isLt; omega⟩
  have he : (⟨7168 + k.val, by have h := k.isLt; omega⟩ : Fin 8689) =
      ⟨0 + j.val, by have h := j.isLt; omega⟩ := by
    apply Fin.ext
    dsimp [k] <;> omega
  simpa only [he] using singleton_chunk_7168 k

#print axioms accepted
end D5.S3.Quantum.Entanglement.EJM.EJMStructureSingletonBlock0
