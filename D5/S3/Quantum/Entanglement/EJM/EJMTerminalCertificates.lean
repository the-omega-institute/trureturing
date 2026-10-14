/- GID: D5/S3/Quantum/Entanglement/EJM/EJMTerminalCertificates
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMTerminalCertificates
   mirror-E: none(waiver:actual-exact-certificate-premise)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.associated_lower_le_score; premises=D5/S3/Quantum/Entanglement/EJM/EJMTerminalCertificates.triangle_terminals,D5/S3/Quantum/Entanglement/EJM/EJMTerminalCertificates.triangle_tags,D5/S3/Quantum/Entanglement/EJM/EJMTerminalCertificates.singleton_terminals,D5/S3/Quantum/Entanglement/EJM/EJMTerminalCertificates.singleton_tags
   digest: Actual terminal events, contraction witnesses and scaled integer comparisons pass their checks. -/

/-
admission_basis: escape-witness
This delivery supplies the complete actual numerical premises for local
row and cache soundness. The consumed receipts are not independent
positive finite-instance results. Numerical
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

/- The complete tag domains are checked in 128-row kernel blocks.
The previous whole-domain tag reductions were the only unbounded finite
receipts in this source. The prior resource cancellation did not identify
a failed mathematical proposition. This revised source still awaits its
actual kernel build; no new acceptance is asserted here. -/

set_option maxHeartbeats 100000000
set_option linter.style.longLine false

private theorem triangle_chunk_0 : ∀ j : Fin 128, triangleTerminalCheck ⟨0 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_128 : ∀ j : Fin 128, triangleTerminalCheck ⟨128 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_256 : ∀ j : Fin 128, triangleTerminalCheck ⟨256 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_384 : ∀ j : Fin 128, triangleTerminalCheck ⟨384 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_512 : ∀ j : Fin 128, triangleTerminalCheck ⟨512 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_640 : ∀ j : Fin 128, triangleTerminalCheck ⟨640 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_768 : ∀ j : Fin 128, triangleTerminalCheck ⟨768 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_896 : ∀ j : Fin 128, triangleTerminalCheck ⟨896 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_1024 : ∀ j : Fin 128, triangleTerminalCheck ⟨1024 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_1152 : ∀ j : Fin 128, triangleTerminalCheck ⟨1152 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_1280 : ∀ j : Fin 128, triangleTerminalCheck ⟨1280 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_1408 : ∀ j : Fin 128, triangleTerminalCheck ⟨1408 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_1536 : ∀ j : Fin 128, triangleTerminalCheck ⟨1536 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_1664 : ∀ j : Fin 128, triangleTerminalCheck ⟨1664 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_1792 : ∀ j : Fin 128, triangleTerminalCheck ⟨1792 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_1920 : ∀ j : Fin 128, triangleTerminalCheck ⟨1920 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_2048 : ∀ j : Fin 128, triangleTerminalCheck ⟨2048 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_2176 : ∀ j : Fin 128, triangleTerminalCheck ⟨2176 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_2304 : ∀ j : Fin 128, triangleTerminalCheck ⟨2304 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_2432 : ∀ j : Fin 128, triangleTerminalCheck ⟨2432 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_2560 : ∀ j : Fin 128, triangleTerminalCheck ⟨2560 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_2688 : ∀ j : Fin 128, triangleTerminalCheck ⟨2688 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_2816 : ∀ j : Fin 128, triangleTerminalCheck ⟨2816 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_2944 : ∀ j : Fin 128, triangleTerminalCheck ⟨2944 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_3072 : ∀ j : Fin 128, triangleTerminalCheck ⟨3072 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_3200 : ∀ j : Fin 128, triangleTerminalCheck ⟨3200 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_3328 : ∀ j : Fin 128, triangleTerminalCheck ⟨3328 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_3456 : ∀ j : Fin 128, triangleTerminalCheck ⟨3456 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_3584 : ∀ j : Fin 128, triangleTerminalCheck ⟨3584 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_3712 : ∀ j : Fin 128, triangleTerminalCheck ⟨3712 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_3840 : ∀ j : Fin 128, triangleTerminalCheck ⟨3840 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_3968 : ∀ j : Fin 128, triangleTerminalCheck ⟨3968 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_4096 : ∀ j : Fin 128, triangleTerminalCheck ⟨4096 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_4224 : ∀ j : Fin 128, triangleTerminalCheck ⟨4224 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_4352 : ∀ j : Fin 128, triangleTerminalCheck ⟨4352 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_chunk_4480 : ∀ j : Fin 108, triangleTerminalCheck ⟨4480 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_chunk_0 : ∀ j : Fin 128, singletonTerminalCheck ⟨0 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_chunk_128 : ∀ j : Fin 128, singletonTerminalCheck ⟨128 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_chunk_256 : ∀ j : Fin 128, singletonTerminalCheck ⟨256 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_chunk_384 : ∀ j : Fin 128, singletonTerminalCheck ⟨384 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_chunk_512 : ∀ j : Fin 128, singletonTerminalCheck ⟨512 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_chunk_640 : ∀ j : Fin 128, singletonTerminalCheck ⟨640 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_chunk_768 : ∀ j : Fin 128, singletonTerminalCheck ⟨768 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_chunk_896 : ∀ j : Fin 128, singletonTerminalCheck ⟨896 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_chunk_1024 : ∀ j : Fin 128, singletonTerminalCheck ⟨1024 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_chunk_1152 : ∀ j : Fin 40, singletonTerminalCheck ⟨1152 + j.val, by have h := j.isLt; omega⟩ = true := by decide +kernel

private def triangleTerminalChunkLength (b : Fin 36) : ℕ :=
  min 128 (4588 - 128 * b.val)

private def triangleTerminalChunkIndex (b : Fin 36)
    (k : Fin (triangleTerminalChunkLength b)) : Fin 4588 :=
  ⟨128 * b.val + k.val, by
    have hb := b.isLt
    have hk := k.isLt
    dsimp [triangleTerminalChunkLength] at hk
    omega⟩

private theorem triangleTerminalBlocks : ∀ b : Fin 36,
    ∀ k : Fin (triangleTerminalChunkLength b), triangleTerminalCheck (triangleTerminalChunkIndex b k) = true :=
  Fin.cases triangle_chunk_0 (Fin.cases triangle_chunk_128 (Fin.cases triangle_chunk_256 (Fin.cases triangle_chunk_384 (Fin.cases triangle_chunk_512 (Fin.cases triangle_chunk_640 (Fin.cases triangle_chunk_768 (Fin.cases triangle_chunk_896 (Fin.cases triangle_chunk_1024 (Fin.cases triangle_chunk_1152 (Fin.cases triangle_chunk_1280 (Fin.cases triangle_chunk_1408 (Fin.cases triangle_chunk_1536 (Fin.cases triangle_chunk_1664 (Fin.cases triangle_chunk_1792 (Fin.cases triangle_chunk_1920 (
  Fin.cases triangle_chunk_2048 (Fin.cases triangle_chunk_2176 (Fin.cases triangle_chunk_2304 (Fin.cases triangle_chunk_2432 (Fin.cases triangle_chunk_2560 (Fin.cases triangle_chunk_2688 (Fin.cases triangle_chunk_2816 (Fin.cases triangle_chunk_2944 (Fin.cases triangle_chunk_3072 (Fin.cases triangle_chunk_3200 (Fin.cases triangle_chunk_3328 (Fin.cases triangle_chunk_3456 (Fin.cases triangle_chunk_3584 (Fin.cases triangle_chunk_3712 (Fin.cases triangle_chunk_3840 (Fin.cases triangle_chunk_3968 (
  Fin.cases triangle_chunk_4096 (Fin.cases triangle_chunk_4224 (Fin.cases triangle_chunk_4352 (Fin.cases triangle_chunk_4480 (
  (fun b : Fin 0 => Fin.elim0 b)))))))))))))))))))))))))))))))))))))

theorem triangle_terminals (i : Fin 4588) : triangleTerminalCheck i = true := by
  let b : Fin 36 := ⟨i.val / 128, by have hi := i.isLt; omega⟩
  let k : Fin (triangleTerminalChunkLength b) := ⟨i.val % 128, by
    have hi := i.isLt
    dsimp [triangleTerminalChunkLength, b]
    omega⟩
  have he : triangleTerminalChunkIndex b k = i := by
    apply Fin.ext
    dsimp [triangleTerminalChunkIndex, b, k]
    omega
  simpa only [he] using triangleTerminalBlocks b k

#print axioms triangle_terminals

private def singletonTerminalChunkLength (b : Fin 10) : ℕ :=
  min 128 (1192 - 128 * b.val)

private def singletonTerminalChunkIndex (b : Fin 10)
    (k : Fin (singletonTerminalChunkLength b)) : Fin 1192 :=
  ⟨128 * b.val + k.val, by
    have hb := b.isLt
    have hk := k.isLt
    dsimp [singletonTerminalChunkLength] at hk
    omega⟩

private theorem singletonTerminalBlocks : ∀ b : Fin 10,
    ∀ k : Fin (singletonTerminalChunkLength b), singletonTerminalCheck (singletonTerminalChunkIndex b k) = true :=
  Fin.cases singleton_chunk_0 (Fin.cases singleton_chunk_128 (Fin.cases singleton_chunk_256 (Fin.cases singleton_chunk_384 (Fin.cases singleton_chunk_512 (Fin.cases singleton_chunk_640 (Fin.cases singleton_chunk_768 (Fin.cases singleton_chunk_896 (Fin.cases singleton_chunk_1024 (Fin.cases singleton_chunk_1152 (
  (fun b : Fin 0 => Fin.elim0 b)))))))))))

theorem singleton_terminals (i : Fin 1192) : singletonTerminalCheck i = true := by
  let b : Fin 10 := ⟨i.val / 128, by have hi := i.isLt; omega⟩
  let k : Fin (singletonTerminalChunkLength b) := ⟨i.val % 128, by
    have hi := i.isLt
    dsimp [singletonTerminalChunkLength, b]
    omega⟩
  have he : singletonTerminalChunkIndex b k = i := by
    apply Fin.ext
    dsimp [singletonTerminalChunkIndex, b, k]
    omega
  simpa only [he] using singletonTerminalBlocks b k

#print axioms singleton_terminals

private theorem triangle_tags_chunk_0 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨0 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_128 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨128 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_256 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨256 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_384 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨384 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_512 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨512 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_640 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨640 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_768 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨768 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_896 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨896 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_1024 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨1024 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_1152 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨1152 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_1280 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨1280 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_1408 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨1408 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_1536 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨1536 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_1664 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨1664 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_1792 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨1792 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_1920 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨1920 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_2048 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨2048 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_2176 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨2176 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_2304 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨2304 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_2432 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨2432 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_2560 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨2560 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_2688 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨2688 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_2816 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨2816 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_2944 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨2944 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_3072 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨3072 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_3200 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨3200 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_3328 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨3328 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_3456 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨3456 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_3584 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨3584 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_3712 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨3712 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_3840 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨3840 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_3968 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨3968 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_4096 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨4096 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_4224 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨4224 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_4352 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨4352 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_4480 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨4480 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_4608 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨4608 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_4736 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨4736 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_4864 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨4864 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_4992 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨4992 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_5120 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨5120 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_5248 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨5248 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_5376 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨5376 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_5504 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨5504 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_5632 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨5632 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_5760 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨5760 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_5888 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨5888 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_6016 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨6016 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_6144 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨6144 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_6272 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨6272 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_6400 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨6400 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_6528 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨6528 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_6656 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨6656 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_6784 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨6784 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_6912 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨6912 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_7040 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨7040 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_7168 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨7168 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_7296 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨7296 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_7424 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨7424 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_7552 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨7552 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_7680 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨7680 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_7808 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨7808 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_7936 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨7936 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_8064 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨8064 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_8192 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨8192 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_8320 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨8320 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_8448 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨8448 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_8576 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨8576 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_8704 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨8704 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_8832 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨8832 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_8960 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨8960 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_9088 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨9088 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_9216 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨9216 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_9344 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨9344 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_9472 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨9472 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_9600 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨9600 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_9728 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨9728 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_9856 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨9856 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_9984 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨9984 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_10112 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨10112 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_10240 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨10240 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_10368 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨10368 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_10496 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨10496 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_10624 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨10624 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_10752 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨10752 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_10880 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨10880 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_11008 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨11008 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_11136 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨11136 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_11264 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨11264 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_11392 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨11392 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_11520 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨11520 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_11648 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨11648 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_11776 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨11776 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_11904 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨11904 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_12032 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨12032 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_12160 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨12160 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_12288 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨12288 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_12416 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨12416 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_12544 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨12544 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_12672 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨12672 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_12800 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨12800 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_12928 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨12928 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_13056 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨13056 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_13184 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨13184 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_13312 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨13312 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_13440 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨13440 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_13568 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨13568 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_13696 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨13696 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_13824 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨13824 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_13952 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨13952 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_14080 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨14080 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_14208 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨14208 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_14336 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨14336 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_14464 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨14464 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_14592 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨14592 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_14720 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨14720 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_14848 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨14848 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_14976 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨14976 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_15104 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨15104 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_15232 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨15232 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_15360 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨15360 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_15488 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨15488 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_15616 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨15616 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_15744 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨15744 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_15872 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨15872 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_16000 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨16000 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_16128 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨16128 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_16256 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨16256 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_16384 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨16384 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_16512 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨16512 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_16640 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨16640 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_16768 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨16768 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_16896 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨16896 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_17024 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨17024 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_17152 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨17152 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_17280 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨17280 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_17408 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨17408 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_17536 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨17536 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_17664 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨17664 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_17792 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨17792 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_17920 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨17920 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_18048 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨18048 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_18176 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨18176 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_18304 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨18304 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_18432 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨18432 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_18560 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨18560 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_18688 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨18688 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_18816 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨18816 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_18944 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨18944 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_19072 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨19072 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_19200 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨19200 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_19328 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨19328 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_19456 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨19456 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_19584 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨19584 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_19712 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨19712 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_19840 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨19840 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_19968 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨19968 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_20096 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨20096 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_20224 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨20224 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_20352 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨20352 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_20480 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨20480 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_20608 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨20608 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_20736 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨20736 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_20864 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨20864 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_20992 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨20992 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_21120 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨21120 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_21248 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨21248 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_21376 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨21376 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_21504 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨21504 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_21632 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨21632 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_21760 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨21760 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_21888 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨21888 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_22016 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨22016 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_22144 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨22144 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_22272 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨22272 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_22400 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨22400 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_22528 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨22528 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_22656 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨22656 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_22784 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨22784 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_22912 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨22912 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_23040 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨23040 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_23168 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨23168 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_23296 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨23296 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_23424 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨23424 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_23552 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨23552 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_23680 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨23680 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_23808 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨23808 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_23936 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨23936 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_24064 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨24064 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_24192 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨24192 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_24320 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨24320 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_24448 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨24448 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_24576 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨24576 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_24704 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨24704 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_24832 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨24832 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_24960 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨24960 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_25088 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨25088 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_25216 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨25216 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_25344 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨25344 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_25472 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨25472 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_25600 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨25600 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_25728 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨25728 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_25856 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨25856 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_25984 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨25984 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_26112 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨26112 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_26240 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨26240 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_26368 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨26368 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_26496 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨26496 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_26624 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨26624 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_26752 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨26752 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_26880 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨26880 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_27008 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨27008 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_27136 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨27136 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_27264 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨27264 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_27392 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨27392 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_27520 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨27520 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_27648 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨27648 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_27776 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨27776 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_27904 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨27904 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_28032 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨28032 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_28160 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨28160 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_28288 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨28288 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_28416 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨28416 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_28544 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨28544 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_28672 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨28672 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_28800 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨28800 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_28928 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨28928 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_29056 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨29056 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_29184 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨29184 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_29312 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨29312 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_29440 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨29440 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_29568 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨29568 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_29696 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨29696 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_29824 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨29824 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_29952 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨29952 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_30080 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨30080 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_30208 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨30208 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_30336 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨30336 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_30464 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨30464 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_30592 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨30592 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_30720 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨30720 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_30848 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨30848 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_30976 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨30976 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_31104 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨31104 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_31232 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨31232 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_31360 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨31360 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_31488 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨31488 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_31616 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨31616 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_31744 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨31744 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_31872 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨31872 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_32000 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨32000 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_32128 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨32128 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_32256 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨32256 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_32384 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨32384 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_32512 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨32512 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_32640 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨32640 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_32768 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨32768 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_32896 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨32896 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_33024 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨33024 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_33152 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨33152 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_33280 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨33280 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_33408 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨33408 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_33536 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨33536 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_33664 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨33664 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_33792 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨33792 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_33920 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨33920 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_34048 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨34048 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_34176 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨34176 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_34304 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨34304 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_34432 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨34432 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_34560 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨34560 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_34688 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨34688 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_34816 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨34816 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_34944 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨34944 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_35072 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨35072 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_35200 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨35200 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_35328 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨35328 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_35456 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨35456 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_35584 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨35584 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_35712 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨35712 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_35840 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨35840 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_35968 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨35968 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_36096 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨36096 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_36224 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨36224 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_36352 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨36352 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_36480 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨36480 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_36608 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨36608 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_36736 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨36736 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_36864 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨36864 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_36992 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨36992 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_37120 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨37120 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_37248 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨37248 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_37376 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨37376 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_37504 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨37504 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_37632 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨37632 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_37760 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨37760 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_37888 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨37888 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_38016 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨38016 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_38144 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨38144 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_38272 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨38272 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_38400 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨38400 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_38528 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨38528 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_38656 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨38656 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_38784 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨38784 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_38912 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨38912 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_39040 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨39040 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_39168 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨39168 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_39296 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨39296 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_39424 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨39424 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_39552 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨39552 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_39680 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨39680 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_39808 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨39808 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_39936 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨39936 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_40064 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨40064 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_40192 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨40192 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_40320 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨40320 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_40448 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨40448 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_40576 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨40576 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_40704 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨40704 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_40832 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨40832 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_40960 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨40960 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_41088 : ∀ k : Fin 128, triangleTerminalTagCheck ⟨41088 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem triangle_tags_chunk_41216 : ∀ k : Fin 78, triangleTerminalTagCheck ⟨41216 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel

private def triangleTagChunkLength (b : Fin 323) : ℕ :=
  min 128 (41294 - 128 * b.val)

private def triangleTagChunkIndex (b : Fin 323)
    (k : Fin (triangleTagChunkLength b)) : Fin 41294 :=
  ⟨128 * b.val + k.val, by
    have hb := b.isLt
    have hk := k.isLt
    dsimp [triangleTagChunkLength] at hk
    omega⟩

private theorem triangleTagBlocks : ∀ b : Fin 323,
    ∀ k : Fin (triangleTagChunkLength b), triangleTerminalTagCheck (triangleTagChunkIndex b k) = true :=
  Fin.cases triangle_tags_chunk_0 (Fin.cases triangle_tags_chunk_128 (Fin.cases triangle_tags_chunk_256 (Fin.cases triangle_tags_chunk_384 (Fin.cases triangle_tags_chunk_512 (Fin.cases triangle_tags_chunk_640 (Fin.cases triangle_tags_chunk_768 (Fin.cases triangle_tags_chunk_896 (Fin.cases triangle_tags_chunk_1024 (Fin.cases triangle_tags_chunk_1152 (Fin.cases triangle_tags_chunk_1280 (Fin.cases triangle_tags_chunk_1408 (Fin.cases triangle_tags_chunk_1536 (Fin.cases triangle_tags_chunk_1664 (Fin.cases triangle_tags_chunk_1792 (Fin.cases triangle_tags_chunk_1920 (
  Fin.cases triangle_tags_chunk_2048 (Fin.cases triangle_tags_chunk_2176 (Fin.cases triangle_tags_chunk_2304 (Fin.cases triangle_tags_chunk_2432 (Fin.cases triangle_tags_chunk_2560 (Fin.cases triangle_tags_chunk_2688 (Fin.cases triangle_tags_chunk_2816 (Fin.cases triangle_tags_chunk_2944 (Fin.cases triangle_tags_chunk_3072 (Fin.cases triangle_tags_chunk_3200 (Fin.cases triangle_tags_chunk_3328 (Fin.cases triangle_tags_chunk_3456 (Fin.cases triangle_tags_chunk_3584 (Fin.cases triangle_tags_chunk_3712 (Fin.cases triangle_tags_chunk_3840 (Fin.cases triangle_tags_chunk_3968 (
  Fin.cases triangle_tags_chunk_4096 (Fin.cases triangle_tags_chunk_4224 (Fin.cases triangle_tags_chunk_4352 (Fin.cases triangle_tags_chunk_4480 (Fin.cases triangle_tags_chunk_4608 (Fin.cases triangle_tags_chunk_4736 (Fin.cases triangle_tags_chunk_4864 (Fin.cases triangle_tags_chunk_4992 (Fin.cases triangle_tags_chunk_5120 (Fin.cases triangle_tags_chunk_5248 (Fin.cases triangle_tags_chunk_5376 (Fin.cases triangle_tags_chunk_5504 (Fin.cases triangle_tags_chunk_5632 (Fin.cases triangle_tags_chunk_5760 (Fin.cases triangle_tags_chunk_5888 (Fin.cases triangle_tags_chunk_6016 (
  Fin.cases triangle_tags_chunk_6144 (Fin.cases triangle_tags_chunk_6272 (Fin.cases triangle_tags_chunk_6400 (Fin.cases triangle_tags_chunk_6528 (Fin.cases triangle_tags_chunk_6656 (Fin.cases triangle_tags_chunk_6784 (Fin.cases triangle_tags_chunk_6912 (Fin.cases triangle_tags_chunk_7040 (Fin.cases triangle_tags_chunk_7168 (Fin.cases triangle_tags_chunk_7296 (Fin.cases triangle_tags_chunk_7424 (Fin.cases triangle_tags_chunk_7552 (Fin.cases triangle_tags_chunk_7680 (Fin.cases triangle_tags_chunk_7808 (Fin.cases triangle_tags_chunk_7936 (Fin.cases triangle_tags_chunk_8064 (
  Fin.cases triangle_tags_chunk_8192 (Fin.cases triangle_tags_chunk_8320 (Fin.cases triangle_tags_chunk_8448 (Fin.cases triangle_tags_chunk_8576 (Fin.cases triangle_tags_chunk_8704 (Fin.cases triangle_tags_chunk_8832 (Fin.cases triangle_tags_chunk_8960 (Fin.cases triangle_tags_chunk_9088 (Fin.cases triangle_tags_chunk_9216 (Fin.cases triangle_tags_chunk_9344 (Fin.cases triangle_tags_chunk_9472 (Fin.cases triangle_tags_chunk_9600 (Fin.cases triangle_tags_chunk_9728 (Fin.cases triangle_tags_chunk_9856 (Fin.cases triangle_tags_chunk_9984 (Fin.cases triangle_tags_chunk_10112 (
  Fin.cases triangle_tags_chunk_10240 (Fin.cases triangle_tags_chunk_10368 (Fin.cases triangle_tags_chunk_10496 (Fin.cases triangle_tags_chunk_10624 (Fin.cases triangle_tags_chunk_10752 (Fin.cases triangle_tags_chunk_10880 (Fin.cases triangle_tags_chunk_11008 (Fin.cases triangle_tags_chunk_11136 (Fin.cases triangle_tags_chunk_11264 (Fin.cases triangle_tags_chunk_11392 (Fin.cases triangle_tags_chunk_11520 (Fin.cases triangle_tags_chunk_11648 (Fin.cases triangle_tags_chunk_11776 (Fin.cases triangle_tags_chunk_11904 (Fin.cases triangle_tags_chunk_12032 (Fin.cases triangle_tags_chunk_12160 (
  Fin.cases triangle_tags_chunk_12288 (Fin.cases triangle_tags_chunk_12416 (Fin.cases triangle_tags_chunk_12544 (Fin.cases triangle_tags_chunk_12672 (Fin.cases triangle_tags_chunk_12800 (Fin.cases triangle_tags_chunk_12928 (Fin.cases triangle_tags_chunk_13056 (Fin.cases triangle_tags_chunk_13184 (Fin.cases triangle_tags_chunk_13312 (Fin.cases triangle_tags_chunk_13440 (Fin.cases triangle_tags_chunk_13568 (Fin.cases triangle_tags_chunk_13696 (Fin.cases triangle_tags_chunk_13824 (Fin.cases triangle_tags_chunk_13952 (Fin.cases triangle_tags_chunk_14080 (Fin.cases triangle_tags_chunk_14208 (
  Fin.cases triangle_tags_chunk_14336 (Fin.cases triangle_tags_chunk_14464 (Fin.cases triangle_tags_chunk_14592 (Fin.cases triangle_tags_chunk_14720 (Fin.cases triangle_tags_chunk_14848 (Fin.cases triangle_tags_chunk_14976 (Fin.cases triangle_tags_chunk_15104 (Fin.cases triangle_tags_chunk_15232 (Fin.cases triangle_tags_chunk_15360 (Fin.cases triangle_tags_chunk_15488 (Fin.cases triangle_tags_chunk_15616 (Fin.cases triangle_tags_chunk_15744 (Fin.cases triangle_tags_chunk_15872 (Fin.cases triangle_tags_chunk_16000 (Fin.cases triangle_tags_chunk_16128 (Fin.cases triangle_tags_chunk_16256 (
  Fin.cases triangle_tags_chunk_16384 (Fin.cases triangle_tags_chunk_16512 (Fin.cases triangle_tags_chunk_16640 (Fin.cases triangle_tags_chunk_16768 (Fin.cases triangle_tags_chunk_16896 (Fin.cases triangle_tags_chunk_17024 (Fin.cases triangle_tags_chunk_17152 (Fin.cases triangle_tags_chunk_17280 (Fin.cases triangle_tags_chunk_17408 (Fin.cases triangle_tags_chunk_17536 (Fin.cases triangle_tags_chunk_17664 (Fin.cases triangle_tags_chunk_17792 (Fin.cases triangle_tags_chunk_17920 (Fin.cases triangle_tags_chunk_18048 (Fin.cases triangle_tags_chunk_18176 (Fin.cases triangle_tags_chunk_18304 (
  Fin.cases triangle_tags_chunk_18432 (Fin.cases triangle_tags_chunk_18560 (Fin.cases triangle_tags_chunk_18688 (Fin.cases triangle_tags_chunk_18816 (Fin.cases triangle_tags_chunk_18944 (Fin.cases triangle_tags_chunk_19072 (Fin.cases triangle_tags_chunk_19200 (Fin.cases triangle_tags_chunk_19328 (Fin.cases triangle_tags_chunk_19456 (Fin.cases triangle_tags_chunk_19584 (Fin.cases triangle_tags_chunk_19712 (Fin.cases triangle_tags_chunk_19840 (Fin.cases triangle_tags_chunk_19968 (Fin.cases triangle_tags_chunk_20096 (Fin.cases triangle_tags_chunk_20224 (Fin.cases triangle_tags_chunk_20352 (
  Fin.cases triangle_tags_chunk_20480 (Fin.cases triangle_tags_chunk_20608 (Fin.cases triangle_tags_chunk_20736 (Fin.cases triangle_tags_chunk_20864 (Fin.cases triangle_tags_chunk_20992 (Fin.cases triangle_tags_chunk_21120 (Fin.cases triangle_tags_chunk_21248 (Fin.cases triangle_tags_chunk_21376 (Fin.cases triangle_tags_chunk_21504 (Fin.cases triangle_tags_chunk_21632 (Fin.cases triangle_tags_chunk_21760 (Fin.cases triangle_tags_chunk_21888 (Fin.cases triangle_tags_chunk_22016 (Fin.cases triangle_tags_chunk_22144 (Fin.cases triangle_tags_chunk_22272 (Fin.cases triangle_tags_chunk_22400 (
  Fin.cases triangle_tags_chunk_22528 (Fin.cases triangle_tags_chunk_22656 (Fin.cases triangle_tags_chunk_22784 (Fin.cases triangle_tags_chunk_22912 (Fin.cases triangle_tags_chunk_23040 (Fin.cases triangle_tags_chunk_23168 (Fin.cases triangle_tags_chunk_23296 (Fin.cases triangle_tags_chunk_23424 (Fin.cases triangle_tags_chunk_23552 (Fin.cases triangle_tags_chunk_23680 (Fin.cases triangle_tags_chunk_23808 (Fin.cases triangle_tags_chunk_23936 (Fin.cases triangle_tags_chunk_24064 (Fin.cases triangle_tags_chunk_24192 (Fin.cases triangle_tags_chunk_24320 (Fin.cases triangle_tags_chunk_24448 (
  Fin.cases triangle_tags_chunk_24576 (Fin.cases triangle_tags_chunk_24704 (Fin.cases triangle_tags_chunk_24832 (Fin.cases triangle_tags_chunk_24960 (Fin.cases triangle_tags_chunk_25088 (Fin.cases triangle_tags_chunk_25216 (Fin.cases triangle_tags_chunk_25344 (Fin.cases triangle_tags_chunk_25472 (Fin.cases triangle_tags_chunk_25600 (Fin.cases triangle_tags_chunk_25728 (Fin.cases triangle_tags_chunk_25856 (Fin.cases triangle_tags_chunk_25984 (Fin.cases triangle_tags_chunk_26112 (Fin.cases triangle_tags_chunk_26240 (Fin.cases triangle_tags_chunk_26368 (Fin.cases triangle_tags_chunk_26496 (
  Fin.cases triangle_tags_chunk_26624 (Fin.cases triangle_tags_chunk_26752 (Fin.cases triangle_tags_chunk_26880 (Fin.cases triangle_tags_chunk_27008 (Fin.cases triangle_tags_chunk_27136 (Fin.cases triangle_tags_chunk_27264 (Fin.cases triangle_tags_chunk_27392 (Fin.cases triangle_tags_chunk_27520 (Fin.cases triangle_tags_chunk_27648 (Fin.cases triangle_tags_chunk_27776 (Fin.cases triangle_tags_chunk_27904 (Fin.cases triangle_tags_chunk_28032 (Fin.cases triangle_tags_chunk_28160 (Fin.cases triangle_tags_chunk_28288 (Fin.cases triangle_tags_chunk_28416 (Fin.cases triangle_tags_chunk_28544 (
  Fin.cases triangle_tags_chunk_28672 (Fin.cases triangle_tags_chunk_28800 (Fin.cases triangle_tags_chunk_28928 (Fin.cases triangle_tags_chunk_29056 (Fin.cases triangle_tags_chunk_29184 (Fin.cases triangle_tags_chunk_29312 (Fin.cases triangle_tags_chunk_29440 (Fin.cases triangle_tags_chunk_29568 (Fin.cases triangle_tags_chunk_29696 (Fin.cases triangle_tags_chunk_29824 (Fin.cases triangle_tags_chunk_29952 (Fin.cases triangle_tags_chunk_30080 (Fin.cases triangle_tags_chunk_30208 (Fin.cases triangle_tags_chunk_30336 (Fin.cases triangle_tags_chunk_30464 (Fin.cases triangle_tags_chunk_30592 (
  Fin.cases triangle_tags_chunk_30720 (Fin.cases triangle_tags_chunk_30848 (Fin.cases triangle_tags_chunk_30976 (Fin.cases triangle_tags_chunk_31104 (Fin.cases triangle_tags_chunk_31232 (Fin.cases triangle_tags_chunk_31360 (Fin.cases triangle_tags_chunk_31488 (Fin.cases triangle_tags_chunk_31616 (Fin.cases triangle_tags_chunk_31744 (Fin.cases triangle_tags_chunk_31872 (Fin.cases triangle_tags_chunk_32000 (Fin.cases triangle_tags_chunk_32128 (Fin.cases triangle_tags_chunk_32256 (Fin.cases triangle_tags_chunk_32384 (Fin.cases triangle_tags_chunk_32512 (Fin.cases triangle_tags_chunk_32640 (
  Fin.cases triangle_tags_chunk_32768 (Fin.cases triangle_tags_chunk_32896 (Fin.cases triangle_tags_chunk_33024 (Fin.cases triangle_tags_chunk_33152 (Fin.cases triangle_tags_chunk_33280 (Fin.cases triangle_tags_chunk_33408 (Fin.cases triangle_tags_chunk_33536 (Fin.cases triangle_tags_chunk_33664 (Fin.cases triangle_tags_chunk_33792 (Fin.cases triangle_tags_chunk_33920 (Fin.cases triangle_tags_chunk_34048 (Fin.cases triangle_tags_chunk_34176 (Fin.cases triangle_tags_chunk_34304 (Fin.cases triangle_tags_chunk_34432 (Fin.cases triangle_tags_chunk_34560 (Fin.cases triangle_tags_chunk_34688 (
  Fin.cases triangle_tags_chunk_34816 (Fin.cases triangle_tags_chunk_34944 (Fin.cases triangle_tags_chunk_35072 (Fin.cases triangle_tags_chunk_35200 (Fin.cases triangle_tags_chunk_35328 (Fin.cases triangle_tags_chunk_35456 (Fin.cases triangle_tags_chunk_35584 (Fin.cases triangle_tags_chunk_35712 (Fin.cases triangle_tags_chunk_35840 (Fin.cases triangle_tags_chunk_35968 (Fin.cases triangle_tags_chunk_36096 (Fin.cases triangle_tags_chunk_36224 (Fin.cases triangle_tags_chunk_36352 (Fin.cases triangle_tags_chunk_36480 (Fin.cases triangle_tags_chunk_36608 (Fin.cases triangle_tags_chunk_36736 (
  Fin.cases triangle_tags_chunk_36864 (Fin.cases triangle_tags_chunk_36992 (Fin.cases triangle_tags_chunk_37120 (Fin.cases triangle_tags_chunk_37248 (Fin.cases triangle_tags_chunk_37376 (Fin.cases triangle_tags_chunk_37504 (Fin.cases triangle_tags_chunk_37632 (Fin.cases triangle_tags_chunk_37760 (Fin.cases triangle_tags_chunk_37888 (Fin.cases triangle_tags_chunk_38016 (Fin.cases triangle_tags_chunk_38144 (Fin.cases triangle_tags_chunk_38272 (Fin.cases triangle_tags_chunk_38400 (Fin.cases triangle_tags_chunk_38528 (Fin.cases triangle_tags_chunk_38656 (Fin.cases triangle_tags_chunk_38784 (
  Fin.cases triangle_tags_chunk_38912 (Fin.cases triangle_tags_chunk_39040 (Fin.cases triangle_tags_chunk_39168 (Fin.cases triangle_tags_chunk_39296 (Fin.cases triangle_tags_chunk_39424 (Fin.cases triangle_tags_chunk_39552 (Fin.cases triangle_tags_chunk_39680 (Fin.cases triangle_tags_chunk_39808 (Fin.cases triangle_tags_chunk_39936 (Fin.cases triangle_tags_chunk_40064 (Fin.cases triangle_tags_chunk_40192 (Fin.cases triangle_tags_chunk_40320 (Fin.cases triangle_tags_chunk_40448 (Fin.cases triangle_tags_chunk_40576 (Fin.cases triangle_tags_chunk_40704 (Fin.cases triangle_tags_chunk_40832 (
  Fin.cases triangle_tags_chunk_40960 (Fin.cases triangle_tags_chunk_41088 (Fin.cases triangle_tags_chunk_41216 (
  (fun b : Fin 0 => Fin.elim0 b))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem triangle_tags (i : Fin 41294) : triangleTerminalTagCheck i = true := by
  let b : Fin 323 := ⟨i.val / 128, by have hi := i.isLt; omega⟩
  let k : Fin (triangleTagChunkLength b) := ⟨i.val % 128, by
    have hi := i.isLt
    dsimp [triangleTagChunkLength, b]
    omega⟩
  have he : triangleTagChunkIndex b k = i := by
    apply Fin.ext
    dsimp [triangleTagChunkIndex, b, k]
    omega
  simpa only [he] using triangleTagBlocks b k

#print axioms triangle_tags

private theorem singleton_tags_chunk_0 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨0 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_128 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨128 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_256 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨256 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_384 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨384 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_512 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨512 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_640 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨640 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_768 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨768 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_896 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨896 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_1024 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨1024 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_1152 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨1152 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_1280 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨1280 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_1408 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨1408 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_1536 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨1536 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_1664 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨1664 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_1792 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨1792 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_1920 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨1920 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_2048 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨2048 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_2176 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨2176 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_2304 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨2304 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_2432 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨2432 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_2560 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨2560 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_2688 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨2688 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_2816 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨2816 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_2944 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨2944 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_3072 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨3072 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_3200 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨3200 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_3328 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨3328 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_3456 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨3456 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_3584 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨3584 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_3712 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨3712 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_3840 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨3840 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_3968 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨3968 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_4096 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨4096 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_4224 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨4224 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_4352 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨4352 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_4480 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨4480 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_4608 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨4608 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_4736 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨4736 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_4864 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨4864 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_4992 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨4992 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_5120 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨5120 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_5248 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨5248 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_5376 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨5376 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_5504 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨5504 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_5632 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨5632 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_5760 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨5760 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_5888 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨5888 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_6016 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨6016 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_6144 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨6144 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_6272 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨6272 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_6400 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨6400 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_6528 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨6528 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_6656 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨6656 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_6784 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨6784 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_6912 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨6912 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_7040 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨7040 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_7168 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨7168 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_7296 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨7296 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_7424 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨7424 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_7552 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨7552 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_7680 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨7680 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_7808 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨7808 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_7936 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨7936 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_8064 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨8064 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_8192 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨8192 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_8320 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨8320 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_8448 : ∀ k : Fin 128, singletonTerminalTagCheck ⟨8448 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel
private theorem singleton_tags_chunk_8576 : ∀ k : Fin 113, singletonTerminalTagCheck ⟨8576 + k.val, by have h := k.isLt; omega⟩ = true := by decide +kernel

private def singletonTagChunkLength (b : Fin 68) : ℕ :=
  min 128 (8689 - 128 * b.val)

private def singletonTagChunkIndex (b : Fin 68)
    (k : Fin (singletonTagChunkLength b)) : Fin 8689 :=
  ⟨128 * b.val + k.val, by
    have hb := b.isLt
    have hk := k.isLt
    dsimp [singletonTagChunkLength] at hk
    omega⟩

private theorem singletonTagBlocks : ∀ b : Fin 68,
    ∀ k : Fin (singletonTagChunkLength b), singletonTerminalTagCheck (singletonTagChunkIndex b k) = true :=
  Fin.cases singleton_tags_chunk_0 (Fin.cases singleton_tags_chunk_128 (Fin.cases singleton_tags_chunk_256 (Fin.cases singleton_tags_chunk_384 (Fin.cases singleton_tags_chunk_512 (Fin.cases singleton_tags_chunk_640 (Fin.cases singleton_tags_chunk_768 (Fin.cases singleton_tags_chunk_896 (Fin.cases singleton_tags_chunk_1024 (Fin.cases singleton_tags_chunk_1152 (Fin.cases singleton_tags_chunk_1280 (Fin.cases singleton_tags_chunk_1408 (Fin.cases singleton_tags_chunk_1536 (Fin.cases singleton_tags_chunk_1664 (Fin.cases singleton_tags_chunk_1792 (Fin.cases singleton_tags_chunk_1920 (
  Fin.cases singleton_tags_chunk_2048 (Fin.cases singleton_tags_chunk_2176 (Fin.cases singleton_tags_chunk_2304 (Fin.cases singleton_tags_chunk_2432 (Fin.cases singleton_tags_chunk_2560 (Fin.cases singleton_tags_chunk_2688 (Fin.cases singleton_tags_chunk_2816 (Fin.cases singleton_tags_chunk_2944 (Fin.cases singleton_tags_chunk_3072 (Fin.cases singleton_tags_chunk_3200 (Fin.cases singleton_tags_chunk_3328 (Fin.cases singleton_tags_chunk_3456 (Fin.cases singleton_tags_chunk_3584 (Fin.cases singleton_tags_chunk_3712 (Fin.cases singleton_tags_chunk_3840 (Fin.cases singleton_tags_chunk_3968 (
  Fin.cases singleton_tags_chunk_4096 (Fin.cases singleton_tags_chunk_4224 (Fin.cases singleton_tags_chunk_4352 (Fin.cases singleton_tags_chunk_4480 (Fin.cases singleton_tags_chunk_4608 (Fin.cases singleton_tags_chunk_4736 (Fin.cases singleton_tags_chunk_4864 (Fin.cases singleton_tags_chunk_4992 (Fin.cases singleton_tags_chunk_5120 (Fin.cases singleton_tags_chunk_5248 (Fin.cases singleton_tags_chunk_5376 (Fin.cases singleton_tags_chunk_5504 (Fin.cases singleton_tags_chunk_5632 (Fin.cases singleton_tags_chunk_5760 (Fin.cases singleton_tags_chunk_5888 (Fin.cases singleton_tags_chunk_6016 (
  Fin.cases singleton_tags_chunk_6144 (Fin.cases singleton_tags_chunk_6272 (Fin.cases singleton_tags_chunk_6400 (Fin.cases singleton_tags_chunk_6528 (Fin.cases singleton_tags_chunk_6656 (Fin.cases singleton_tags_chunk_6784 (Fin.cases singleton_tags_chunk_6912 (Fin.cases singleton_tags_chunk_7040 (Fin.cases singleton_tags_chunk_7168 (Fin.cases singleton_tags_chunk_7296 (Fin.cases singleton_tags_chunk_7424 (Fin.cases singleton_tags_chunk_7552 (Fin.cases singleton_tags_chunk_7680 (Fin.cases singleton_tags_chunk_7808 (Fin.cases singleton_tags_chunk_7936 (Fin.cases singleton_tags_chunk_8064 (
  Fin.cases singleton_tags_chunk_8192 (Fin.cases singleton_tags_chunk_8320 (Fin.cases singleton_tags_chunk_8448 (Fin.cases singleton_tags_chunk_8576 (
  (fun b : Fin 0 => Fin.elim0 b)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem singleton_tags (i : Fin 8689) : singletonTerminalTagCheck i = true := by
  let b : Fin 68 := ⟨i.val / 128, by have hi := i.isLt; omega⟩
  let k : Fin (singletonTagChunkLength b) := ⟨i.val % 128, by
    have hi := i.isLt
    dsimp [singletonTagChunkLength, b]
    omega⟩
  have he : singletonTagChunkIndex b k = i := by
    apply Fin.ext
    dsimp [singletonTagChunkIndex, b, k]
    omega
  simpa only [he] using singletonTagBlocks b k

#print axioms singleton_tags

end D5.S3.Quantum.Entanglement.EJM.EJMTerminalCertificates
