/- GID: D5/S3/Quantum/Entanglement/EJM/EJMTerminalCertificates
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMTerminalCertificates
   mirror-E: none(waiver:actual-exact-certificate-premise)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/EJMExactCertificate.result; premises=D5/S3/Quantum/Entanglement/EJM/EJMTerminalCertificates.triangle_terminals,D5/S3/Quantum/Entanglement/EJM/EJMTerminalCertificates.triangle_tags,D5/S3/Quantum/Entanglement/EJM/EJMTerminalCertificates.singleton_terminals,D5/S3/Quantum/Entanglement/EJM/EJMTerminalCertificates.singleton_tags
   digest: Actual terminal events, contraction witnesses and scaled integer comparisons pass their checks. -/

/-
admission_basis: escape-witness
This is part of the same actual-certificate delivery as the substantive
recursive checker soundness and final locality refutation, not an
independent numerical-instance or first-freeze deliverable. Numerical
normalization and consumed binding helpers supply no separate escape.
Public targets: triangle_terminals, singleton_terminals,
triangle_tags, singleton_tags. Every private chunk and public check receipt
has proof_shape: bind-only. The checks cover all 4588 triangle terminals,
1192 singleton terminals, and the terminal-tag check on all 41294 and 8689
local rows. They inspect actual complete events, exact local coordinate and
outcome transport, and the stored inequality in its required lower-bound
direction. The checks do not assume stored contraction values are correct:
EJMTerminalBoundSoundness separately consumes the actual contraction receipts.
All four public checks are live premises of local acceptance and the final
refutation, not independently delivered finite positive instances.
The concrete numeric premises listed in the utility header must be
kernel-checked in this delivery, with the same original functions,
finite domains, partial rows and inequality direction. Pending sources
or external producer validations do not fulfill those premises.
Four-slot registration remains unfinished under issue #16309. The
specific public targets below lack a compiled original-source
realization bridge, enrolled readout and variation/sensitivity evidence;
this is a missing-registration statement, not a template-support claim.
-/

import D5.S3.Quantum.Entanglement.EJM.EJMTerminalBoundData
set_option maxRecDepth 1000000
-- Kernel-check each complete block before beginning the next one.
set_option Elab.async false
namespace D5.S3.Quantum.Entanglement.EJM.EJMTerminalCertificates
open D5.S3.Quantum.Entanglement.EJM.EJMTerminalBoundData
set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_0 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨0 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_128 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨128 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_256 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨256 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_384 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨384 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_512 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨512 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_640 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨640 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_768 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨768 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_896 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨896 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_1024 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨1024 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_1152 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨1152 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_1280 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨1280 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_1408 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨1408 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_1536 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨1536 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_1664 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨1664 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_1792 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨1792 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_1920 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨1920 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_2048 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨2048 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_2176 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨2176 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_2304 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨2304 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_2432 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨2432 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_2560 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨2560 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_2688 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨2688 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_2816 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨2816 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_2944 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨2944 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_3072 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨3072 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_3200 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨3200 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_3328 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨3328 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_3456 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨3456 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_3584 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨3584 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_3712 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨3712 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_3840 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨3840 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_3968 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨3968 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_4096 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨4096 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_4224 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨4224 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_4352 : ∀ j : Fin 128,
    triangleTerminalCheck ⟨4352 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem triangle_chunk_4480 : ∀ j : Fin 108,
    triangleTerminalCheck ⟨4480 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

theorem triangle_terminals (i : Fin 4588) : triangleTerminalCheck i = true := by
  by_cases h0 : i.val < 128
  ·
    let j : Fin 128 := ⟨i.val - 0, by have h := i.isLt; omega⟩
    have he : (⟨0 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_0 j
  by_cases h1 : i.val < 256
  ·
    let j : Fin 128 := ⟨i.val - 128, by have h := i.isLt; omega⟩
    have he : (⟨128 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_128 j
  by_cases h2 : i.val < 384
  ·
    let j : Fin 128 := ⟨i.val - 256, by have h := i.isLt; omega⟩
    have he : (⟨256 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_256 j
  by_cases h3 : i.val < 512
  ·
    let j : Fin 128 := ⟨i.val - 384, by have h := i.isLt; omega⟩
    have he : (⟨384 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_384 j
  by_cases h4 : i.val < 640
  ·
    let j : Fin 128 := ⟨i.val - 512, by have h := i.isLt; omega⟩
    have he : (⟨512 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_512 j
  by_cases h5 : i.val < 768
  ·
    let j : Fin 128 := ⟨i.val - 640, by have h := i.isLt; omega⟩
    have he : (⟨640 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_640 j
  by_cases h6 : i.val < 896
  ·
    let j : Fin 128 := ⟨i.val - 768, by have h := i.isLt; omega⟩
    have he : (⟨768 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_768 j
  by_cases h7 : i.val < 1024
  ·
    let j : Fin 128 := ⟨i.val - 896, by have h := i.isLt; omega⟩
    have he : (⟨896 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_896 j
  by_cases h8 : i.val < 1152
  ·
    let j : Fin 128 := ⟨i.val - 1024, by have h := i.isLt; omega⟩
    have he : (⟨1024 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_1024 j
  by_cases h9 : i.val < 1280
  ·
    let j : Fin 128 := ⟨i.val - 1152, by have h := i.isLt; omega⟩
    have he : (⟨1152 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_1152 j
  by_cases h10 : i.val < 1408
  ·
    let j : Fin 128 := ⟨i.val - 1280, by have h := i.isLt; omega⟩
    have he : (⟨1280 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_1280 j
  by_cases h11 : i.val < 1536
  ·
    let j : Fin 128 := ⟨i.val - 1408, by have h := i.isLt; omega⟩
    have he : (⟨1408 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_1408 j
  by_cases h12 : i.val < 1664
  ·
    let j : Fin 128 := ⟨i.val - 1536, by have h := i.isLt; omega⟩
    have he : (⟨1536 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_1536 j
  by_cases h13 : i.val < 1792
  ·
    let j : Fin 128 := ⟨i.val - 1664, by have h := i.isLt; omega⟩
    have he : (⟨1664 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_1664 j
  by_cases h14 : i.val < 1920
  ·
    let j : Fin 128 := ⟨i.val - 1792, by have h := i.isLt; omega⟩
    have he : (⟨1792 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_1792 j
  by_cases h15 : i.val < 2048
  ·
    let j : Fin 128 := ⟨i.val - 1920, by have h := i.isLt; omega⟩
    have he : (⟨1920 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_1920 j
  by_cases h16 : i.val < 2176
  ·
    let j : Fin 128 := ⟨i.val - 2048, by have h := i.isLt; omega⟩
    have he : (⟨2048 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_2048 j
  by_cases h17 : i.val < 2304
  ·
    let j : Fin 128 := ⟨i.val - 2176, by have h := i.isLt; omega⟩
    have he : (⟨2176 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_2176 j
  by_cases h18 : i.val < 2432
  ·
    let j : Fin 128 := ⟨i.val - 2304, by have h := i.isLt; omega⟩
    have he : (⟨2304 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_2304 j
  by_cases h19 : i.val < 2560
  ·
    let j : Fin 128 := ⟨i.val - 2432, by have h := i.isLt; omega⟩
    have he : (⟨2432 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_2432 j
  by_cases h20 : i.val < 2688
  ·
    let j : Fin 128 := ⟨i.val - 2560, by have h := i.isLt; omega⟩
    have he : (⟨2560 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_2560 j
  by_cases h21 : i.val < 2816
  ·
    let j : Fin 128 := ⟨i.val - 2688, by have h := i.isLt; omega⟩
    have he : (⟨2688 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_2688 j
  by_cases h22 : i.val < 2944
  ·
    let j : Fin 128 := ⟨i.val - 2816, by have h := i.isLt; omega⟩
    have he : (⟨2816 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_2816 j
  by_cases h23 : i.val < 3072
  ·
    let j : Fin 128 := ⟨i.val - 2944, by have h := i.isLt; omega⟩
    have he : (⟨2944 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_2944 j
  by_cases h24 : i.val < 3200
  ·
    let j : Fin 128 := ⟨i.val - 3072, by have h := i.isLt; omega⟩
    have he : (⟨3072 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_3072 j
  by_cases h25 : i.val < 3328
  ·
    let j : Fin 128 := ⟨i.val - 3200, by have h := i.isLt; omega⟩
    have he : (⟨3200 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_3200 j
  by_cases h26 : i.val < 3456
  ·
    let j : Fin 128 := ⟨i.val - 3328, by have h := i.isLt; omega⟩
    have he : (⟨3328 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_3328 j
  by_cases h27 : i.val < 3584
  ·
    let j : Fin 128 := ⟨i.val - 3456, by have h := i.isLt; omega⟩
    have he : (⟨3456 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_3456 j
  by_cases h28 : i.val < 3712
  ·
    let j : Fin 128 := ⟨i.val - 3584, by have h := i.isLt; omega⟩
    have he : (⟨3584 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_3584 j
  by_cases h29 : i.val < 3840
  ·
    let j : Fin 128 := ⟨i.val - 3712, by have h := i.isLt; omega⟩
    have he : (⟨3712 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_3712 j
  by_cases h30 : i.val < 3968
  ·
    let j : Fin 128 := ⟨i.val - 3840, by have h := i.isLt; omega⟩
    have he : (⟨3840 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_3840 j
  by_cases h31 : i.val < 4096
  ·
    let j : Fin 128 := ⟨i.val - 3968, by have h := i.isLt; omega⟩
    have he : (⟨3968 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_3968 j
  by_cases h32 : i.val < 4224
  ·
    let j : Fin 128 := ⟨i.val - 4096, by have h := i.isLt; omega⟩
    have he : (⟨4096 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_4096 j
  by_cases h33 : i.val < 4352
  ·
    let j : Fin 128 := ⟨i.val - 4224, by have h := i.isLt; omega⟩
    have he : (⟨4224 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_4224 j
  by_cases h34 : i.val < 4480
  ·
    let j : Fin 128 := ⟨i.val - 4352, by have h := i.isLt; omega⟩
    have he : (⟨4352 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using triangle_chunk_4352 j
  let j : Fin 108 := ⟨i.val - 4480, by have h := i.isLt; omega⟩
  have he : (⟨4480 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 4588) = i := by
    apply Fin.ext
    dsimp [j]
    omega
  simpa only [he] using triangle_chunk_4480 j

#print axioms triangle_terminals

set_option maxHeartbeats 100000000 in
private theorem singleton_chunk_0 : ∀ j : Fin 128,
    singletonTerminalCheck ⟨0 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem singleton_chunk_128 : ∀ j : Fin 128,
    singletonTerminalCheck ⟨128 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem singleton_chunk_256 : ∀ j : Fin 128,
    singletonTerminalCheck ⟨256 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem singleton_chunk_384 : ∀ j : Fin 128,
    singletonTerminalCheck ⟨384 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem singleton_chunk_512 : ∀ j : Fin 128,
    singletonTerminalCheck ⟨512 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem singleton_chunk_640 : ∀ j : Fin 128,
    singletonTerminalCheck ⟨640 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem singleton_chunk_768 : ∀ j : Fin 128,
    singletonTerminalCheck ⟨768 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem singleton_chunk_896 : ∀ j : Fin 128,
    singletonTerminalCheck ⟨896 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem singleton_chunk_1024 : ∀ j : Fin 128,
    singletonTerminalCheck ⟨1024 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
private theorem singleton_chunk_1152 : ∀ j : Fin 40,
    singletonTerminalCheck ⟨1152 + j.val, by have h := j.isLt; omega⟩ = true := by
  decide +kernel

theorem singleton_terminals (i : Fin 1192) : singletonTerminalCheck i = true := by
  by_cases h0 : i.val < 128
  ·
    let j : Fin 128 := ⟨i.val - 0, by have h := i.isLt; omega⟩
    have he : (⟨0 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 1192) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using singleton_chunk_0 j
  by_cases h1 : i.val < 256
  ·
    let j : Fin 128 := ⟨i.val - 128, by have h := i.isLt; omega⟩
    have he : (⟨128 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 1192) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using singleton_chunk_128 j
  by_cases h2 : i.val < 384
  ·
    let j : Fin 128 := ⟨i.val - 256, by have h := i.isLt; omega⟩
    have he : (⟨256 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 1192) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using singleton_chunk_256 j
  by_cases h3 : i.val < 512
  ·
    let j : Fin 128 := ⟨i.val - 384, by have h := i.isLt; omega⟩
    have he : (⟨384 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 1192) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using singleton_chunk_384 j
  by_cases h4 : i.val < 640
  ·
    let j : Fin 128 := ⟨i.val - 512, by have h := i.isLt; omega⟩
    have he : (⟨512 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 1192) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using singleton_chunk_512 j
  by_cases h5 : i.val < 768
  ·
    let j : Fin 128 := ⟨i.val - 640, by have h := i.isLt; omega⟩
    have he : (⟨640 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 1192) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using singleton_chunk_640 j
  by_cases h6 : i.val < 896
  ·
    let j : Fin 128 := ⟨i.val - 768, by have h := i.isLt; omega⟩
    have he : (⟨768 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 1192) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using singleton_chunk_768 j
  by_cases h7 : i.val < 1024
  ·
    let j : Fin 128 := ⟨i.val - 896, by have h := i.isLt; omega⟩
    have he : (⟨896 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 1192) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using singleton_chunk_896 j
  by_cases h8 : i.val < 1152
  ·
    let j : Fin 128 := ⟨i.val - 1024, by have h := i.isLt; omega⟩
    have he : (⟨1024 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 1192) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [he] using singleton_chunk_1024 j
  let j : Fin 40 := ⟨i.val - 1152, by have h := i.isLt; omega⟩
  have he : (⟨1152 + j.val, by dsimp [j]; have h := j.isLt; omega⟩ : Fin 1192) = i := by
    apply Fin.ext
    dsimp [j]
    omega
  simpa only [he] using singleton_chunk_1152 j

#print axioms singleton_terminals

set_option maxHeartbeats 100000000 in
theorem triangle_tags : ∀ j : Fin 41294, triangleTerminalTagCheck j = true := by
  decide +kernel

#print axioms triangle_tags

set_option maxHeartbeats 100000000 in
theorem singleton_tags : ∀ j : Fin 8689, singletonTerminalTagCheck j = true := by
  decide +kernel

#print axioms singleton_tags

end D5.S3.Quantum.Entanglement.EJM.EJMTerminalCertificates
