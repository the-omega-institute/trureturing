/- GID: D5/S3/Quantum/Entanglement/EJM/EJMSingletonCacheReceipts
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMSingletonCacheReceipts
   mirror-E: none(waiver:actual-exact-certificate-cache)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/EJMExactCertificate.result; premises=D5/S3/Quantum/Entanglement/EJM/EJMSingletonCacheReceipts.mirror_accepted,D5/S3/Quantum/Entanglement/EJM/EJMSingletonCacheReceipts.transitions_accepted
   digest: Full finite-domain kernel receipts bind every local mirror and unknown-coordinate transition to the original rows. -/

/- Prepared source: not yet compiled. Part of the same complete actual EJM
certificate, not a standalone conditional or numerical delivery. All literal
mirrors, actions and transition receipts require kernel acceptance before use.
The original score, scale, all actual assignments and four value branches are
preserved. Producer checks below are not mathematical premises. -/

import D5.S3.Quantum.Entanglement.EJM.EJMSingletonCacheData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.Quantum.Entanglement.EJM.EJMSingletonCacheReceipts
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport
open D5.S3.Quantum.Entanglement.EJM.EJMSingletonCacheData

set_option maxHeartbeats 100000000 in
-- The explicit finite kernel domain needs this budget; producer checks are not premises.
set_option trace.profiler true in
private theorem mirror_0 : ∀ k : Fin 2048,
    checkMirror ⟨0 + k.val, by have h := k.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- The explicit finite kernel domain needs this budget; producer checks are not premises.
set_option trace.profiler true in
private theorem mirror_2048 : ∀ k : Fin 2048,
    checkMirror ⟨2048 + k.val, by have h := k.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- The explicit finite kernel domain needs this budget; producer checks are not premises.
set_option trace.profiler true in
private theorem mirror_4096 : ∀ k : Fin 2048,
    checkMirror ⟨4096 + k.val, by have h := k.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- The explicit finite kernel domain needs this budget; producer checks are not premises.
set_option trace.profiler true in
private theorem mirror_6144 : ∀ k : Fin 2048,
    checkMirror ⟨6144 + k.val, by have h := k.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- The explicit finite kernel domain needs this budget; producer checks are not premises.
set_option trace.profiler true in
private theorem mirror_8192 : ∀ k : Fin 497,
    checkMirror ⟨8192 + k.val, by have h := k.isLt; omega⟩ = true := by
  decide +kernel

theorem mirror_accepted (j : Fin 8689) : checkMirror j = true := by
  by_cases h0 : j.val < 2048
  ·
    let k : Fin 2048 := ⟨j.val - 0, by have h := j.isLt; omega⟩
    have he : (⟨0 + k.val, by dsimp [k]; have h := k.isLt; omega⟩ : Fin 8689) = j := by
      apply Fin.ext
      dsimp [k]
      omega
    simpa only [he] using mirror_0 k
  by_cases h1 : j.val < 4096
  ·
    let k : Fin 2048 := ⟨j.val - 2048, by have h := j.isLt; omega⟩
    have he : (⟨2048 + k.val, by dsimp [k]; have h := k.isLt; omega⟩ : Fin 8689) = j := by
      apply Fin.ext
      dsimp [k]
      omega
    simpa only [he] using mirror_2048 k
  by_cases h2 : j.val < 6144
  ·
    let k : Fin 2048 := ⟨j.val - 4096, by have h := j.isLt; omega⟩
    have he : (⟨4096 + k.val, by dsimp [k]; have h := k.isLt; omega⟩ : Fin 8689) = j := by
      apply Fin.ext
      dsimp [k]
      omega
    simpa only [he] using mirror_4096 k
  by_cases h3 : j.val < 8192
  ·
    let k : Fin 2048 := ⟨j.val - 6144, by have h := j.isLt; omega⟩
    have he : (⟨6144 + k.val, by dsimp [k]; have h := k.isLt; omega⟩ : Fin 8689) = j := by
      apply Fin.ext
      dsimp [k]
      omega
    simpa only [he] using mirror_6144 k
  let k : Fin 497 := ⟨j.val - 8192, by have h := j.isLt; omega⟩
  have he : (⟨8192 + k.val, by dsimp [k]; have h := k.isLt; omega⟩ : Fin 8689) = j := by
    apply Fin.ext
    dsimp [k]
    omega
  simpa only [he] using mirror_8192 k

set_option maxHeartbeats 100000000 in
-- The explicit finite kernel domain needs this budget; producer checks are not premises.
set_option trace.profiler true in
private theorem transitions_0 : ∀ k : Fin 2048,
    checkTransitions ⟨0 + k.val, by have h := k.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- The explicit finite kernel domain needs this budget; producer checks are not premises.
set_option trace.profiler true in
private theorem transitions_2048 : ∀ k : Fin 2048,
    checkTransitions ⟨2048 + k.val, by have h := k.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- The explicit finite kernel domain needs this budget; producer checks are not premises.
set_option trace.profiler true in
private theorem transitions_4096 : ∀ k : Fin 2048,
    checkTransitions ⟨4096 + k.val, by have h := k.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- The explicit finite kernel domain needs this budget; producer checks are not premises.
set_option trace.profiler true in
private theorem transitions_6144 : ∀ k : Fin 2048,
    checkTransitions ⟨6144 + k.val, by have h := k.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- The explicit finite kernel domain needs this budget; producer checks are not premises.
set_option trace.profiler true in
private theorem transitions_8192 : ∀ k : Fin 497,
    checkTransitions ⟨8192 + k.val, by have h := k.isLt; omega⟩ = true := by
  decide +kernel

theorem transitions_accepted (j : Fin 8689) : checkTransitions j = true := by
  by_cases h0 : j.val < 2048
  ·
    let k : Fin 2048 := ⟨j.val - 0, by have h := j.isLt; omega⟩
    have he : (⟨0 + k.val, by dsimp [k]; have h := k.isLt; omega⟩ : Fin 8689) = j := by
      apply Fin.ext
      dsimp [k]
      omega
    simpa only [he] using transitions_0 k
  by_cases h1 : j.val < 4096
  ·
    let k : Fin 2048 := ⟨j.val - 2048, by have h := j.isLt; omega⟩
    have he : (⟨2048 + k.val, by dsimp [k]; have h := k.isLt; omega⟩ : Fin 8689) = j := by
      apply Fin.ext
      dsimp [k]
      omega
    simpa only [he] using transitions_2048 k
  by_cases h2 : j.val < 6144
  ·
    let k : Fin 2048 := ⟨j.val - 4096, by have h := j.isLt; omega⟩
    have he : (⟨4096 + k.val, by dsimp [k]; have h := k.isLt; omega⟩ : Fin 8689) = j := by
      apply Fin.ext
      dsimp [k]
      omega
    simpa only [he] using transitions_4096 k
  by_cases h3 : j.val < 8192
  ·
    let k : Fin 2048 := ⟨j.val - 6144, by have h := j.isLt; omega⟩
    have he : (⟨6144 + k.val, by dsimp [k]; have h := k.isLt; omega⟩ : Fin 8689) = j := by
      apply Fin.ext
      dsimp [k]
      omega
    simpa only [he] using transitions_6144 k
  let k : Fin 497 := ⟨j.val - 8192, by have h := j.isLt; omega⟩
  have he : (⟨8192 + k.val, by dsimp [k]; have h := k.isLt; omega⟩ : Fin 8689) = j := by
    apply Fin.ext
    dsimp [k]
    omega
  simpa only [he] using transitions_8192 k

theorem assignment_eq (j : Fin 8689) :
    assignment j = (singletonRows j).assignment :=
  (of_decide_eq_true (mirror_accepted j)).1

theorem lower_eq (j : Fin 8689) : lower j = (singletonRows j).lower :=
  (of_decide_eq_true (mirror_accepted j)).2

/-- This consequence uses the original row assignments on both sides. -/
theorem transition_accepted (j : Fin 8689) (i : Fin 9) (a : Fin 4)
    (unknown : (singletonRows j).assignment i = none) :
    D5.S0.Certificates.FiniteLocalRowCache.checkTransition singletonPartialAct
      singletonRows transition j i a = true := by
  have hu : assignment j i = none := by rw [assignment_eq, unknown]
  have h := of_decide_eq_true (transitions_accepted j) i hu a
  rw [assignment_eq, assignment_eq] at h
  exact decide_eq_true h

#print axioms assignment_eq
#print axioms lower_eq
#print axioms transition_accepted

end D5.S3.Quantum.Entanglement.EJM.EJMSingletonCacheReceipts
