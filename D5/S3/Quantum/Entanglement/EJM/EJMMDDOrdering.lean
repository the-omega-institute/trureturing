/- GID: D5/S3/Quantum/Entanglement/EJM/EJMMDDOrdering
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMMDDOrdering
   mirror-E: none(waiver:actual-value-diagram-certificate)
   anchors: []
   utility: none
   digest: Complete per-node ordering receipts check the literal reverse-coordinate EJM diagrams. -/

/- WIP for the same full EJM certificate. Every private numeric receipt still
requires an actual kernel build; source emission asserts no acceptance.
These shape obligations retain all literal children but do not replace the
separate complete simulation of actual cache rows and earned actions. -/

import D5.S3.Quantum.Entanglement.EJM.EJMMDDData
import D5.S3.Quantum.Entanglement.EJM.EJMMDDCacheBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000
set_option Elab.async false
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMMDDOrdering
open D5.S3.Quantum.Entanglement.EJM.EJMMDDData
open D5.S3.Quantum.Entanglement.EJM.EJMMDDCacheBridge

private theorem triangle_chunk_0 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨0 + j.val, by have h := j.isLt; change 0 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_128 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨128 + j.val, by have h := j.isLt; change 128 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_256 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨256 + j.val, by have h := j.isLt; change 256 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_384 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨384 + j.val, by have h := j.isLt; change 384 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_512 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨512 + j.val, by have h := j.isLt; change 512 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_640 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨640 + j.val, by have h := j.isLt; change 640 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_768 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨768 + j.val, by have h := j.isLt; change 768 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_896 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨896 + j.val, by have h := j.isLt; change 896 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_1024 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨1024 + j.val, by have h := j.isLt; change 1024 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_1152 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨1152 + j.val, by have h := j.isLt; change 1152 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_1280 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨1280 + j.val, by have h := j.isLt; change 1280 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_1408 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨1408 + j.val, by have h := j.isLt; change 1408 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_1536 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨1536 + j.val, by have h := j.isLt; change 1536 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_1664 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨1664 + j.val, by have h := j.isLt; change 1664 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_1792 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨1792 + j.val, by have h := j.isLt; change 1792 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_1920 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨1920 + j.val, by have h := j.isLt; change 1920 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_2048 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨2048 + j.val, by have h := j.isLt; change 2048 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_2176 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨2176 + j.val, by have h := j.isLt; change 2176 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_2304 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨2304 + j.val, by have h := j.isLt; change 2304 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_2432 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨2432 + j.val, by have h := j.isLt; change 2432 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_2560 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨2560 + j.val, by have h := j.isLt; change 2560 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_2688 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨2688 + j.val, by have h := j.isLt; change 2688 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_2816 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨2816 + j.val, by have h := j.isLt; change 2816 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_2944 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨2944 + j.val, by have h := j.isLt; change 2944 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_3072 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨3072 + j.val, by have h := j.isLt; change 3072 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_3200 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨3200 + j.val, by have h := j.isLt; change 3200 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_3328 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨3328 + j.val, by have h := j.isLt; change 3328 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_3456 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨3456 + j.val, by have h := j.isLt; change 3456 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_3584 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨3584 + j.val, by have h := j.isLt; change 3584 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_3712 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨3712 + j.val, by have h := j.isLt; change 3712 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_3840 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨3840 + j.val, by have h := j.isLt; change 3840 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_3968 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨3968 + j.val, by have h := j.isLt; change 3968 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_4096 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨4096 + j.val, by have h := j.isLt; change 4096 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_4224 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨4224 + j.val, by have h := j.isLt; change 4224 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_4352 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨4352 + j.val, by have h := j.isLt; change 4352 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_4480 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨4480 + j.val, by have h := j.isLt; change 4480 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_4608 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨4608 + j.val, by have h := j.isLt; change 4608 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_4736 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨4736 + j.val, by have h := j.isLt; change 4736 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_4864 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨4864 + j.val, by have h := j.isLt; change 4864 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_4992 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨4992 + j.val, by have h := j.isLt; change 4992 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_5120 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨5120 + j.val, by have h := j.isLt; change 5120 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_5248 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨5248 + j.val, by have h := j.isLt; change 5248 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_5376 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨5376 + j.val, by have h := j.isLt; change 5376 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_5504 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨5504 + j.val, by have h := j.isLt; change 5504 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_5632 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨5632 + j.val, by have h := j.isLt; change 5632 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_5760 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨5760 + j.val, by have h := j.isLt; change 5760 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_5888 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨5888 + j.val, by have h := j.isLt; change 5888 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_6016 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨6016 + j.val, by have h := j.isLt; change 6016 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_6144 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨6144 + j.val, by have h := j.isLt; change 6144 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_6272 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨6272 + j.val, by have h := j.isLt; change 6272 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_6400 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨6400 + j.val, by have h := j.isLt; change 6400 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_6528 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨6528 + j.val, by have h := j.isLt; change 6528 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_6656 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨6656 + j.val, by have h := j.isLt; change 6656 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_6784 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨6784 + j.val, by have h := j.isLt; change 6784 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_6912 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨6912 + j.val, by have h := j.isLt; change 6912 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_7040 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨7040 + j.val, by have h := j.isLt; change 7040 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_7168 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨7168 + j.val, by have h := j.isLt; change 7168 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_7296 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨7296 + j.val, by have h := j.isLt; change 7296 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_7424 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨7424 + j.val, by have h := j.isLt; change 7424 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_7552 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨7552 + j.val, by have h := j.isLt; change 7552 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_7680 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨7680 + j.val, by have h := j.isLt; change 7680 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_7808 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨7808 + j.val, by have h := j.isLt; change 7808 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_7936 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨7936 + j.val, by have h := j.isLt; change 7936 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_8064 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨8064 + j.val, by have h := j.isLt; change 8064 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_8192 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨8192 + j.val, by have h := j.isLt; change 8192 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_8320 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨8320 + j.val, by have h := j.isLt; change 8320 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_8448 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨8448 + j.val, by have h := j.isLt; change 8448 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_8576 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨8576 + j.val, by have h := j.isLt; change 8576 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_8704 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨8704 + j.val, by have h := j.isLt; change 8704 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_8832 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨8832 + j.val, by have h := j.isLt; change 8832 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_8960 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨8960 + j.val, by have h := j.isLt; change 8960 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_9088 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨9088 + j.val, by have h := j.isLt; change 9088 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_9216 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨9216 + j.val, by have h := j.isLt; change 9216 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_9344 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨9344 + j.val, by have h := j.isLt; change 9344 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_9472 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨9472 + j.val, by have h := j.isLt; change 9472 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_9600 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨9600 + j.val, by have h := j.isLt; change 9600 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_9728 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨9728 + j.val, by have h := j.isLt; change 9728 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_9856 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨9856 + j.val, by have h := j.isLt; change 9856 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_9984 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨9984 + j.val, by have h := j.isLt; change 9984 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_10112 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨10112 + j.val, by have h := j.isLt; change 10112 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_10240 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨10240 + j.val, by have h := j.isLt; change 10240 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_10368 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨10368 + j.val, by have h := j.isLt; change 10368 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_10496 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨10496 + j.val, by have h := j.isLt; change 10496 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_10624 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨10624 + j.val, by have h := j.isLt; change 10624 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_10752 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨10752 + j.val, by have h := j.isLt; change 10752 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_10880 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨10880 + j.val, by have h := j.isLt; change 10880 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_11008 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨11008 + j.val, by have h := j.isLt; change 11008 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_11136 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨11136 + j.val, by have h := j.isLt; change 11136 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_11264 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨11264 + j.val, by have h := j.isLt; change 11264 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_11392 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨11392 + j.val, by have h := j.isLt; change 11392 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_11520 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨11520 + j.val, by have h := j.isLt; change 11520 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_11648 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨11648 + j.val, by have h := j.isLt; change 11648 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_11776 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨11776 + j.val, by have h := j.isLt; change 11776 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_11904 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨11904 + j.val, by have h := j.isLt; change 11904 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_12032 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨12032 + j.val, by have h := j.isLt; change 12032 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_12160 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨12160 + j.val, by have h := j.isLt; change 12160 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_12288 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨12288 + j.val, by have h := j.isLt; change 12288 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_12416 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨12416 + j.val, by have h := j.isLt; change 12416 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_12544 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨12544 + j.val, by have h := j.isLt; change 12544 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_12672 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨12672 + j.val, by have h := j.isLt; change 12672 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_12800 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨12800 + j.val, by have h := j.isLt; change 12800 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_12928 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨12928 + j.val, by have h := j.isLt; change 12928 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_13056 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨13056 + j.val, by have h := j.isLt; change 13056 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_13184 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨13184 + j.val, by have h := j.isLt; change 13184 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_13312 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨13312 + j.val, by have h := j.isLt; change 13312 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_13440 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨13440 + j.val, by have h := j.isLt; change 13440 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_13568 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨13568 + j.val, by have h := j.isLt; change 13568 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_13696 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨13696 + j.val, by have h := j.isLt; change 13696 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_13824 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨13824 + j.val, by have h := j.isLt; change 13824 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_13952 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨13952 + j.val, by have h := j.isLt; change 13952 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_14080 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨14080 + j.val, by have h := j.isLt; change 14080 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_14208 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨14208 + j.val, by have h := j.isLt; change 14208 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_14336 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨14336 + j.val, by have h := j.isLt; change 14336 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_14464 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨14464 + j.val, by have h := j.isLt; change 14464 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_14592 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨14592 + j.val, by have h := j.isLt; change 14592 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_14720 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨14720 + j.val, by have h := j.isLt; change 14720 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_14848 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨14848 + j.val, by have h := j.isLt; change 14848 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_14976 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨14976 + j.val, by have h := j.isLt; change 14976 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_15104 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨15104 + j.val, by have h := j.isLt; change 15104 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_15232 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨15232 + j.val, by have h := j.isLt; change 15232 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_15360 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨15360 + j.val, by have h := j.isLt; change 15360 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_15488 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨15488 + j.val, by have h := j.isLt; change 15488 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_15616 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨15616 + j.val, by have h := j.isLt; change 15616 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_15744 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨15744 + j.val, by have h := j.isLt; change 15744 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_15872 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨15872 + j.val, by have h := j.isLt; change 15872 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_16000 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨16000 + j.val, by have h := j.isLt; change 16000 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_16128 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨16128 + j.val, by have h := j.isLt; change 16128 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_16256 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨16256 + j.val, by have h := j.isLt; change 16256 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_16384 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨16384 + j.val, by have h := j.isLt; change 16384 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_16512 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨16512 + j.val, by have h := j.isLt; change 16512 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_16640 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨16640 + j.val, by have h := j.isLt; change 16640 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_16768 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨16768 + j.val, by have h := j.isLt; change 16768 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_16896 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨16896 + j.val, by have h := j.isLt; change 16896 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_17024 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨17024 + j.val, by have h := j.isLt; change 17024 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_17152 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨17152 + j.val, by have h := j.isLt; change 17152 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_17280 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨17280 + j.val, by have h := j.isLt; change 17280 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_17408 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨17408 + j.val, by have h := j.isLt; change 17408 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_17536 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨17536 + j.val, by have h := j.isLt; change 17536 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_17664 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨17664 + j.val, by have h := j.isLt; change 17664 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_17792 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨17792 + j.val, by have h := j.isLt; change 17792 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_17920 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨17920 + j.val, by have h := j.isLt; change 17920 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_18048 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨18048 + j.val, by have h := j.isLt; change 18048 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_18176 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨18176 + j.val, by have h := j.isLt; change 18176 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_18304 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨18304 + j.val, by have h := j.isLt; change 18304 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_18432 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨18432 + j.val, by have h := j.isLt; change 18432 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_18560 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨18560 + j.val, by have h := j.isLt; change 18560 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_18688 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨18688 + j.val, by have h := j.isLt; change 18688 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_18816 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨18816 + j.val, by have h := j.isLt; change 18816 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_18944 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨18944 + j.val, by have h := j.isLt; change 18944 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_19072 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨19072 + j.val, by have h := j.isLt; change 19072 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_19200 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨19200 + j.val, by have h := j.isLt; change 19200 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_19328 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨19328 + j.val, by have h := j.isLt; change 19328 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_19456 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨19456 + j.val, by have h := j.isLt; change 19456 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_19584 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨19584 + j.val, by have h := j.isLt; change 19584 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_19712 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨19712 + j.val, by have h := j.isLt; change 19712 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_19840 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨19840 + j.val, by have h := j.isLt; change 19840 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_19968 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨19968 + j.val, by have h := j.isLt; change 19968 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_20096 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨20096 + j.val, by have h := j.isLt; change 20096 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_20224 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨20224 + j.val, by have h := j.isLt; change 20224 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_20352 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨20352 + j.val, by have h := j.isLt; change 20352 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_20480 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨20480 + j.val, by have h := j.isLt; change 20480 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_20608 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨20608 + j.val, by have h := j.isLt; change 20608 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_20736 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨20736 + j.val, by have h := j.isLt; change 20736 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_20864 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨20864 + j.val, by have h := j.isLt; change 20864 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_20992 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨20992 + j.val, by have h := j.isLt; change 20992 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_21120 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨21120 + j.val, by have h := j.isLt; change 21120 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_21248 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨21248 + j.val, by have h := j.isLt; change 21248 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_21376 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨21376 + j.val, by have h := j.isLt; change 21376 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_21504 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨21504 + j.val, by have h := j.isLt; change 21504 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_21632 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨21632 + j.val, by have h := j.isLt; change 21632 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_21760 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨21760 + j.val, by have h := j.isLt; change 21760 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_21888 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨21888 + j.val, by have h := j.isLt; change 21888 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_22016 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨22016 + j.val, by have h := j.isLt; change 22016 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_22144 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨22144 + j.val, by have h := j.isLt; change 22144 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_22272 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨22272 + j.val, by have h := j.isLt; change 22272 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_22400 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨22400 + j.val, by have h := j.isLt; change 22400 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_22528 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨22528 + j.val, by have h := j.isLt; change 22528 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_22656 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨22656 + j.val, by have h := j.isLt; change 22656 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_22784 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨22784 + j.val, by have h := j.isLt; change 22784 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_22912 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨22912 + j.val, by have h := j.isLt; change 22912 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_23040 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨23040 + j.val, by have h := j.isLt; change 23040 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_23168 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨23168 + j.val, by have h := j.isLt; change 23168 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_23296 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨23296 + j.val, by have h := j.isLt; change 23296 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_23424 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨23424 + j.val, by have h := j.isLt; change 23424 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_23552 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨23552 + j.val, by have h := j.isLt; change 23552 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_23680 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨23680 + j.val, by have h := j.isLt; change 23680 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_23808 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨23808 + j.val, by have h := j.isLt; change 23808 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_23936 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨23936 + j.val, by have h := j.isLt; change 23936 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_24064 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨24064 + j.val, by have h := j.isLt; change 24064 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_24192 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨24192 + j.val, by have h := j.isLt; change 24192 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_24320 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨24320 + j.val, by have h := j.isLt; change 24320 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_24448 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨24448 + j.val, by have h := j.isLt; change 24448 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_24576 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨24576 + j.val, by have h := j.isLt; change 24576 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_24704 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨24704 + j.val, by have h := j.isLt; change 24704 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_24832 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨24832 + j.val, by have h := j.isLt; change 24832 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_24960 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨24960 + j.val, by have h := j.isLt; change 24960 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_25088 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨25088 + j.val, by have h := j.isLt; change 25088 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_25216 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨25216 + j.val, by have h := j.isLt; change 25216 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_25344 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨25344 + j.val, by have h := j.isLt; change 25344 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_25472 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨25472 + j.val, by have h := j.isLt; change 25472 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_25600 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨25600 + j.val, by have h := j.isLt; change 25600 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_25728 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨25728 + j.val, by have h := j.isLt; change 25728 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_25856 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨25856 + j.val, by have h := j.isLt; change 25856 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_25984 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨25984 + j.val, by have h := j.isLt; change 25984 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_26112 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨26112 + j.val, by have h := j.isLt; change 26112 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_26240 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨26240 + j.val, by have h := j.isLt; change 26240 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_26368 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨26368 + j.val, by have h := j.isLt; change 26368 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_26496 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨26496 + j.val, by have h := j.isLt; change 26496 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_26624 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨26624 + j.val, by have h := j.isLt; change 26624 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_26752 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨26752 + j.val, by have h := j.isLt; change 26752 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_26880 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨26880 + j.val, by have h := j.isLt; change 26880 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_27008 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨27008 + j.val, by have h := j.isLt; change 27008 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_27136 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨27136 + j.val, by have h := j.isLt; change 27136 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_27264 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨27264 + j.val, by have h := j.isLt; change 27264 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_27392 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨27392 + j.val, by have h := j.isLt; change 27392 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_27520 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨27520 + j.val, by have h := j.isLt; change 27520 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_27648 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨27648 + j.val, by have h := j.isLt; change 27648 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_27776 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨27776 + j.val, by have h := j.isLt; change 27776 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_27904 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨27904 + j.val, by have h := j.isLt; change 27904 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_28032 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨28032 + j.val, by have h := j.isLt; change 28032 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_28160 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨28160 + j.val, by have h := j.isLt; change 28160 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_28288 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨28288 + j.val, by have h := j.isLt; change 28288 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_28416 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨28416 + j.val, by have h := j.isLt; change 28416 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_28544 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨28544 + j.val, by have h := j.isLt; change 28544 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_28672 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨28672 + j.val, by have h := j.isLt; change 28672 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_28800 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨28800 + j.val, by have h := j.isLt; change 28800 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_28928 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨28928 + j.val, by have h := j.isLt; change 28928 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_29056 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨29056 + j.val, by have h := j.isLt; change 29056 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_29184 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨29184 + j.val, by have h := j.isLt; change 29184 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_29312 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨29312 + j.val, by have h := j.isLt; change 29312 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_29440 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨29440 + j.val, by have h := j.isLt; change 29440 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_29568 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨29568 + j.val, by have h := j.isLt; change 29568 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_29696 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨29696 + j.val, by have h := j.isLt; change 29696 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_29824 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨29824 + j.val, by have h := j.isLt; change 29824 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_29952 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨29952 + j.val, by have h := j.isLt; change 29952 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_30080 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨30080 + j.val, by have h := j.isLt; change 30080 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_30208 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨30208 + j.val, by have h := j.isLt; change 30208 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_30336 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨30336 + j.val, by have h := j.isLt; change 30336 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_30464 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨30464 + j.val, by have h := j.isLt; change 30464 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_30592 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨30592 + j.val, by have h := j.isLt; change 30592 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_30720 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨30720 + j.val, by have h := j.isLt; change 30720 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_30848 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨30848 + j.val, by have h := j.isLt; change 30848 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_30976 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨30976 + j.val, by have h := j.isLt; change 30976 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_31104 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨31104 + j.val, by have h := j.isLt; change 31104 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_31232 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨31232 + j.val, by have h := j.isLt; change 31232 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_31360 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨31360 + j.val, by have h := j.isLt; change 31360 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_31488 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨31488 + j.val, by have h := j.isLt; change 31488 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_31616 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨31616 + j.val, by have h := j.isLt; change 31616 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_31744 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨31744 + j.val, by have h := j.isLt; change 31744 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_31872 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨31872 + j.val, by have h := j.isLt; change 31872 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_32000 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨32000 + j.val, by have h := j.isLt; change 32000 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_32128 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨32128 + j.val, by have h := j.isLt; change 32128 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_32256 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨32256 + j.val, by have h := j.isLt; change 32256 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_32384 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨32384 + j.val, by have h := j.isLt; change 32384 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_32512 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨32512 + j.val, by have h := j.isLt; change 32512 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_32640 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨32640 + j.val, by have h := j.isLt; change 32640 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_32768 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨32768 + j.val, by have h := j.isLt; change 32768 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_32896 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨32896 + j.val, by have h := j.isLt; change 32896 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_33024 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨33024 + j.val, by have h := j.isLt; change 33024 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_33152 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨33152 + j.val, by have h := j.isLt; change 33152 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_33280 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨33280 + j.val, by have h := j.isLt; change 33280 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_33408 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨33408 + j.val, by have h := j.isLt; change 33408 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_33536 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨33536 + j.val, by have h := j.isLt; change 33536 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_33664 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨33664 + j.val, by have h := j.isLt; change 33664 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_33792 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨33792 + j.val, by have h := j.isLt; change 33792 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_33920 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨33920 + j.val, by have h := j.isLt; change 33920 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_34048 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨34048 + j.val, by have h := j.isLt; change 34048 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_34176 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨34176 + j.val, by have h := j.isLt; change 34176 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_34304 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨34304 + j.val, by have h := j.isLt; change 34304 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_34432 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨34432 + j.val, by have h := j.isLt; change 34432 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_34560 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨34560 + j.val, by have h := j.isLt; change 34560 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_34688 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨34688 + j.val, by have h := j.isLt; change 34688 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_34816 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨34816 + j.val, by have h := j.isLt; change 34816 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_34944 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨34944 + j.val, by have h := j.isLt; change 34944 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_35072 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨35072 + j.val, by have h := j.isLt; change 35072 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_35200 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨35200 + j.val, by have h := j.isLt; change 35200 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_35328 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨35328 + j.val, by have h := j.isLt; change 35328 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_35456 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨35456 + j.val, by have h := j.isLt; change 35456 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_35584 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨35584 + j.val, by have h := j.isLt; change 35584 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_35712 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨35712 + j.val, by have h := j.isLt; change 35712 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_35840 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨35840 + j.val, by have h := j.isLt; change 35840 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_35968 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨35968 + j.val, by have h := j.isLt; change 35968 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_36096 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨36096 + j.val, by have h := j.isLt; change 36096 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_36224 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨36224 + j.val, by have h := j.isLt; change 36224 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_36352 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨36352 + j.val, by have h := j.isLt; change 36352 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_36480 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨36480 + j.val, by have h := j.isLt; change 36480 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_36608 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨36608 + j.val, by have h := j.isLt; change 36608 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_36736 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨36736 + j.val, by have h := j.isLt; change 36736 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_36864 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨36864 + j.val, by have h := j.isLt; change 36864 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_36992 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨36992 + j.val, by have h := j.isLt; change 36992 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_37120 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨37120 + j.val, by have h := j.isLt; change 37120 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_37248 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨37248 + j.val, by have h := j.isLt; change 37248 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_37376 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨37376 + j.val, by have h := j.isLt; change 37376 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_37504 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨37504 + j.val, by have h := j.isLt; change 37504 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_37632 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨37632 + j.val, by have h := j.isLt; change 37632 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_37760 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨37760 + j.val, by have h := j.isLt; change 37760 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_37888 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨37888 + j.val, by have h := j.isLt; change 37888 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_38016 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨38016 + j.val, by have h := j.isLt; change 38016 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_38144 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨38144 + j.val, by have h := j.isLt; change 38144 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_38272 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨38272 + j.val, by have h := j.isLt; change 38272 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_38400 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨38400 + j.val, by have h := j.isLt; change 38400 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_38528 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨38528 + j.val, by have h := j.isLt; change 38528 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_38656 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨38656 + j.val, by have h := j.isLt; change 38656 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_38784 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨38784 + j.val, by have h := j.isLt; change 38784 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_38912 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨38912 + j.val, by have h := j.isLt; change 38912 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_39040 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨39040 + j.val, by have h := j.isLt; change 39040 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_39168 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨39168 + j.val, by have h := j.isLt; change 39168 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_39296 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨39296 + j.val, by have h := j.isLt; change 39296 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_39424 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨39424 + j.val, by have h := j.isLt; change 39424 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_39552 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨39552 + j.val, by have h := j.isLt; change 39552 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_39680 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨39680 + j.val, by have h := j.isLt; change 39680 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_39808 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨39808 + j.val, by have h := j.isLt; change 39808 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_39936 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨39936 + j.val, by have h := j.isLt; change 39936 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_40064 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨40064 + j.val, by have h := j.isLt; change 40064 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_40192 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨40192 + j.val, by have h := j.isLt; change 40192 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_40320 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨40320 + j.val, by have h := j.isLt; change 40320 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_40448 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨40448 + j.val, by have h := j.isLt; change 40448 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_40576 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨40576 + j.val, by have h := j.isLt; change 40576 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_40704 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨40704 + j.val, by have h := j.isLt; change 40704 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_40832 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨40832 + j.val, by have h := j.isLt; change 40832 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_40960 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨40960 + j.val, by have h := j.isLt; change 40960 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_41088 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨41088 + j.val, by have h := j.isLt; change 41088 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_41216 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨41216 + j.val, by have h := j.isLt; change 41216 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_41344 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨41344 + j.val, by have h := j.isLt; change 41344 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_41472 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨41472 + j.val, by have h := j.isLt; change 41472 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_41600 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨41600 + j.val, by have h := j.isLt; change 41600 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_41728 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨41728 + j.val, by have h := j.isLt; change 41728 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_41856 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨41856 + j.val, by have h := j.isLt; change 41856 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_41984 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨41984 + j.val, by have h := j.isLt; change 41984 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_42112 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨42112 + j.val, by have h := j.isLt; change 42112 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_42240 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨42240 + j.val, by have h := j.isLt; change 42240 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_42368 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨42368 + j.val, by have h := j.isLt; change 42368 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_42496 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨42496 + j.val, by have h := j.isLt; change 42496 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_42624 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨42624 + j.val, by have h := j.isLt; change 42624 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_42752 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨42752 + j.val, by have h := j.isLt; change 42752 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_42880 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨42880 + j.val, by have h := j.isLt; change 42880 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_43008 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨43008 + j.val, by have h := j.isLt; change 43008 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_43136 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨43136 + j.val, by have h := j.isLt; change 43136 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_43264 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨43264 + j.val, by have h := j.isLt; change 43264 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_43392 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨43392 + j.val, by have h := j.isLt; change 43392 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_43520 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨43520 + j.val, by have h := j.isLt; change 43520 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_43648 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨43648 + j.val, by have h := j.isLt; change 43648 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_43776 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨43776 + j.val, by have h := j.isLt; change 43776 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_43904 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨43904 + j.val, by have h := j.isLt; change 43904 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_44032 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨44032 + j.val, by have h := j.isLt; change 44032 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_44160 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨44160 + j.val, by have h := j.isLt; change 44160 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_44288 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨44288 + j.val, by have h := j.isLt; change 44288 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_44416 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨44416 + j.val, by have h := j.isLt; change 44416 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_44544 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨44544 + j.val, by have h := j.isLt; change 44544 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_44672 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨44672 + j.val, by have h := j.isLt; change 44672 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_44800 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨44800 + j.val, by have h := j.isLt; change 44800 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_44928 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨44928 + j.val, by have h := j.isLt; change 44928 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_45056 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨45056 + j.val, by have h := j.isLt; change 45056 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_45184 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨45184 + j.val, by have h := j.isLt; change 45184 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_45312 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨45312 + j.val, by have h := j.isLt; change 45312 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_45440 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨45440 + j.val, by have h := j.isLt; change 45440 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_45568 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨45568 + j.val, by have h := j.isLt; change 45568 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_45696 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨45696 + j.val, by have h := j.isLt; change 45696 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_45824 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨45824 + j.val, by have h := j.isLt; change 45824 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_45952 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨45952 + j.val, by have h := j.isLt; change 45952 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_46080 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨46080 + j.val, by have h := j.isLt; change 46080 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_46208 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨46208 + j.val, by have h := j.isLt; change 46208 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_46336 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨46336 + j.val, by have h := j.isLt; change 46336 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_46464 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨46464 + j.val, by have h := j.isLt; change 46464 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_46592 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨46592 + j.val, by have h := j.isLt; change 46592 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_46720 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨46720 + j.val, by have h := j.isLt; change 46720 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_46848 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨46848 + j.val, by have h := j.isLt; change 46848 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_46976 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨46976 + j.val, by have h := j.isLt; change 46976 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_47104 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨47104 + j.val, by have h := j.isLt; change 47104 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_47232 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨47232 + j.val, by have h := j.isLt; change 47232 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_47360 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨47360 + j.val, by have h := j.isLt; change 47360 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_47488 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨47488 + j.val, by have h := j.isLt; change 47488 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_47616 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨47616 + j.val, by have h := j.isLt; change 47616 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_47744 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨47744 + j.val, by have h := j.isLt; change 47744 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_47872 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨47872 + j.val, by have h := j.isLt; change 47872 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_48000 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨48000 + j.val, by have h := j.isLt; change 48000 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_48128 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨48128 + j.val, by have h := j.isLt; change 48128 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_48256 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨48256 + j.val, by have h := j.isLt; change 48256 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_48384 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨48384 + j.val, by have h := j.isLt; change 48384 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_48512 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨48512 + j.val, by have h := j.isLt; change 48512 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_48640 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨48640 + j.val, by have h := j.isLt; change 48640 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_48768 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨48768 + j.val, by have h := j.isLt; change 48768 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_48896 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨48896 + j.val, by have h := j.isLt; change 48896 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_49024 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨49024 + j.val, by have h := j.isLt; change 49024 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_49152 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨49152 + j.val, by have h := j.isLt; change 49152 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_49280 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨49280 + j.val, by have h := j.isLt; change 49280 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_49408 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨49408 + j.val, by have h := j.isLt; change 49408 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_49536 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨49536 + j.val, by have h := j.isLt; change 49536 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_49664 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨49664 + j.val, by have h := j.isLt; change 49664 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_49792 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨49792 + j.val, by have h := j.isLt; change 49792 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_49920 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨49920 + j.val, by have h := j.isLt; change 49920 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_50048 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨50048 + j.val, by have h := j.isLt; change 50048 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_50176 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨50176 + j.val, by have h := j.isLt; change 50176 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_50304 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨50304 + j.val, by have h := j.isLt; change 50304 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_50432 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨50432 + j.val, by have h := j.isLt; change 50432 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_50560 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨50560 + j.val, by have h := j.isLt; change 50560 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_50688 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨50688 + j.val, by have h := j.isLt; change 50688 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_50816 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨50816 + j.val, by have h := j.isLt; change 50816 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_50944 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨50944 + j.val, by have h := j.isLt; change 50944 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_51072 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨51072 + j.val, by have h := j.isLt; change 51072 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_51200 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨51200 + j.val, by have h := j.isLt; change 51200 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_51328 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨51328 + j.val, by have h := j.isLt; change 51328 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_51456 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨51456 + j.val, by have h := j.isLt; change 51456 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_51584 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨51584 + j.val, by have h := j.isLt; change 51584 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_51712 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨51712 + j.val, by have h := j.isLt; change 51712 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_51840 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨51840 + j.val, by have h := j.isLt; change 51840 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_51968 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨51968 + j.val, by have h := j.isLt; change 51968 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_52096 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨52096 + j.val, by have h := j.isLt; change 52096 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_52224 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨52224 + j.val, by have h := j.isLt; change 52224 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_52352 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨52352 + j.val, by have h := j.isLt; change 52352 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_52480 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨52480 + j.val, by have h := j.isLt; change 52480 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_52608 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨52608 + j.val, by have h := j.isLt; change 52608 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_52736 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨52736 + j.val, by have h := j.isLt; change 52736 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_52864 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨52864 + j.val, by have h := j.isLt; change 52864 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_52992 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨52992 + j.val, by have h := j.isLt; change 52992 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_53120 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨53120 + j.val, by have h := j.isLt; change 53120 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_53248 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨53248 + j.val, by have h := j.isLt; change 53248 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_53376 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨53376 + j.val, by have h := j.isLt; change 53376 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_53504 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨53504 + j.val, by have h := j.isLt; change 53504 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_53632 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨53632 + j.val, by have h := j.isLt; change 53632 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_53760 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨53760 + j.val, by have h := j.isLt; change 53760 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_53888 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨53888 + j.val, by have h := j.isLt; change 53888 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_54016 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨54016 + j.val, by have h := j.isLt; change 54016 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_54144 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨54144 + j.val, by have h := j.isLt; change 54144 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_54272 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨54272 + j.val, by have h := j.isLt; change 54272 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_54400 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨54400 + j.val, by have h := j.isLt; change 54400 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_54528 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨54528 + j.val, by have h := j.isLt; change 54528 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_54656 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨54656 + j.val, by have h := j.isLt; change 54656 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_54784 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨54784 + j.val, by have h := j.isLt; change 54784 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_54912 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨54912 + j.val, by have h := j.isLt; change 54912 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_55040 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨55040 + j.val, by have h := j.isLt; change 55040 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_55168 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨55168 + j.val, by have h := j.isLt; change 55168 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_55296 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨55296 + j.val, by have h := j.isLt; change 55296 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_55424 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨55424 + j.val, by have h := j.isLt; change 55424 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_55552 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨55552 + j.val, by have h := j.isLt; change 55552 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_55680 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨55680 + j.val, by have h := j.isLt; change 55680 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_55808 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨55808 + j.val, by have h := j.isLt; change 55808 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_55936 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨55936 + j.val, by have h := j.isLt; change 55936 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_56064 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨56064 + j.val, by have h := j.isLt; change 56064 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_56192 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨56192 + j.val, by have h := j.isLt; change 56192 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_56320 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨56320 + j.val, by have h := j.isLt; change 56320 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_56448 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨56448 + j.val, by have h := j.isLt; change 56448 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_56576 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨56576 + j.val, by have h := j.isLt; change 56576 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_56704 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨56704 + j.val, by have h := j.isLt; change 56704 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_56832 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨56832 + j.val, by have h := j.isLt; change 56832 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_56960 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨56960 + j.val, by have h := j.isLt; change 56960 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_57088 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨57088 + j.val, by have h := j.isLt; change 57088 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_57216 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨57216 + j.val, by have h := j.isLt; change 57216 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_57344 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨57344 + j.val, by have h := j.isLt; change 57344 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_57472 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨57472 + j.val, by have h := j.isLt; change 57472 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_57600 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨57600 + j.val, by have h := j.isLt; change 57600 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_57728 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨57728 + j.val, by have h := j.isLt; change 57728 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_57856 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨57856 + j.val, by have h := j.isLt; change 57856 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_57984 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨57984 + j.val, by have h := j.isLt; change 57984 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_58112 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨58112 + j.val, by have h := j.isLt; change 58112 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_58240 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨58240 + j.val, by have h := j.isLt; change 58240 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_58368 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨58368 + j.val, by have h := j.isLt; change 58368 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_58496 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨58496 + j.val, by have h := j.isLt; change 58496 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_58624 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨58624 + j.val, by have h := j.isLt; change 58624 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_58752 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨58752 + j.val, by have h := j.isLt; change 58752 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_58880 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨58880 + j.val, by have h := j.isLt; change 58880 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_59008 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨59008 + j.val, by have h := j.isLt; change 59008 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_59136 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨59136 + j.val, by have h := j.isLt; change 59136 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_59264 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨59264 + j.val, by have h := j.isLt; change 59264 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_59392 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨59392 + j.val, by have h := j.isLt; change 59392 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_59520 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨59520 + j.val, by have h := j.isLt; change 59520 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_59648 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨59648 + j.val, by have h := j.isLt; change 59648 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_59776 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨59776 + j.val, by have h := j.isLt; change 59776 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_59904 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨59904 + j.val, by have h := j.isLt; change 59904 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_60032 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨60032 + j.val, by have h := j.isLt; change 60032 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_60160 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨60160 + j.val, by have h := j.isLt; change 60160 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_60288 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨60288 + j.val, by have h := j.isLt; change 60288 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_60416 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨60416 + j.val, by have h := j.isLt; change 60416 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_60544 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨60544 + j.val, by have h := j.isLt; change 60544 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_60672 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨60672 + j.val, by have h := j.isLt; change 60672 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_60800 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨60800 + j.val, by have h := j.isLt; change 60800 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_60928 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨60928 + j.val, by have h := j.isLt; change 60928 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_61056 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨61056 + j.val, by have h := j.isLt; change 61056 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_61184 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨61184 + j.val, by have h := j.isLt; change 61184 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_61312 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨61312 + j.val, by have h := j.isLt; change 61312 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_61440 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨61440 + j.val, by have h := j.isLt; change 61440 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_61568 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨61568 + j.val, by have h := j.isLt; change 61568 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_61696 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨61696 + j.val, by have h := j.isLt; change 61696 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_61824 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨61824 + j.val, by have h := j.isLt; change 61824 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_61952 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨61952 + j.val, by have h := j.isLt; change 61952 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_62080 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨62080 + j.val, by have h := j.isLt; change 62080 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_62208 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨62208 + j.val, by have h := j.isLt; change 62208 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_62336 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨62336 + j.val, by have h := j.isLt; change 62336 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_62464 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨62464 + j.val, by have h := j.isLt; change 62464 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_62592 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨62592 + j.val, by have h := j.isLt; change 62592 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_62720 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨62720 + j.val, by have h := j.isLt; change 62720 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_62848 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨62848 + j.val, by have h := j.isLt; change 62848 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_62976 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨62976 + j.val, by have h := j.isLt; change 62976 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_63104 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨63104 + j.val, by have h := j.isLt; change 63104 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_63232 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨63232 + j.val, by have h := j.isLt; change 63232 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_63360 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨63360 + j.val, by have h := j.isLt; change 63360 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_63488 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨63488 + j.val, by have h := j.isLt; change 63488 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_63616 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨63616 + j.val, by have h := j.isLt; change 63616 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_63744 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨63744 + j.val, by have h := j.isLt; change 63744 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_63872 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨63872 + j.val, by have h := j.isLt; change 63872 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_64000 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨64000 + j.val, by have h := j.isLt; change 64000 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_64128 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨64128 + j.val, by have h := j.isLt; change 64128 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_64256 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨64256 + j.val, by have h := j.isLt; change 64256 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_64384 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨64384 + j.val, by have h := j.isLt; change 64384 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_64512 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨64512 + j.val, by have h := j.isLt; change 64512 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_64640 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨64640 + j.val, by have h := j.isLt; change 64640 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_64768 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨64768 + j.val, by have h := j.isLt; change 64768 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_64896 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨64896 + j.val, by have h := j.isLt; change 64896 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_65024 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨65024 + j.val, by have h := j.isLt; change 65024 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_65152 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨65152 + j.val, by have h := j.isLt; change 65152 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_65280 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨65280 + j.val, by have h := j.isLt; change 65280 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_65408 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨65408 + j.val, by have h := j.isLt; change 65408 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_65536 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨65536 + j.val, by have h := j.isLt; change 65536 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_65664 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨65664 + j.val, by have h := j.isLt; change 65664 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_65792 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨65792 + j.val, by have h := j.isLt; change 65792 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_65920 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨65920 + j.val, by have h := j.isLt; change 65920 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_66048 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨66048 + j.val, by have h := j.isLt; change 66048 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_66176 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨66176 + j.val, by have h := j.isLt; change 66176 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_66304 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨66304 + j.val, by have h := j.isLt; change 66304 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_66432 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨66432 + j.val, by have h := j.isLt; change 66432 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_66560 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨66560 + j.val, by have h := j.isLt; change 66560 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_66688 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨66688 + j.val, by have h := j.isLt; change 66688 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_66816 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨66816 + j.val, by have h := j.isLt; change 66816 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_66944 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨66944 + j.val, by have h := j.isLt; change 66944 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_67072 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨67072 + j.val, by have h := j.isLt; change 67072 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_67200 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨67200 + j.val, by have h := j.isLt; change 67200 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_67328 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨67328 + j.val, by have h := j.isLt; change 67328 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_67456 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨67456 + j.val, by have h := j.isLt; change 67456 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_67584 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨67584 + j.val, by have h := j.isLt; change 67584 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_67712 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨67712 + j.val, by have h := j.isLt; change 67712 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_67840 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨67840 + j.val, by have h := j.isLt; change 67840 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_67968 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨67968 + j.val, by have h := j.isLt; change 67968 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_68096 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨68096 + j.val, by have h := j.isLt; change 68096 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_68224 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨68224 + j.val, by have h := j.isLt; change 68224 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_68352 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨68352 + j.val, by have h := j.isLt; change 68352 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_68480 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨68480 + j.val, by have h := j.isLt; change 68480 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_68608 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨68608 + j.val, by have h := j.isLt; change 68608 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_68736 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨68736 + j.val, by have h := j.isLt; change 68736 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_68864 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨68864 + j.val, by have h := j.isLt; change 68864 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_68992 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨68992 + j.val, by have h := j.isLt; change 68992 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_69120 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨69120 + j.val, by have h := j.isLt; change 69120 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_69248 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨69248 + j.val, by have h := j.isLt; change 69248 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_69376 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨69376 + j.val, by have h := j.isLt; change 69376 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_69504 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨69504 + j.val, by have h := j.isLt; change 69504 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_69632 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨69632 + j.val, by have h := j.isLt; change 69632 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_69760 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨69760 + j.val, by have h := j.isLt; change 69760 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_69888 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨69888 + j.val, by have h := j.isLt; change 69888 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_70016 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨70016 + j.val, by have h := j.isLt; change 70016 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_70144 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨70144 + j.val, by have h := j.isLt; change 70144 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_70272 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨70272 + j.val, by have h := j.isLt; change 70272 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_70400 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨70400 + j.val, by have h := j.isLt; change 70400 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_70528 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨70528 + j.val, by have h := j.isLt; change 70528 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_70656 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨70656 + j.val, by have h := j.isLt; change 70656 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_70784 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨70784 + j.val, by have h := j.isLt; change 70784 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_70912 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨70912 + j.val, by have h := j.isLt; change 70912 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_71040 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨71040 + j.val, by have h := j.isLt; change 71040 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_71168 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨71168 + j.val, by have h := j.isLt; change 71168 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_71296 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨71296 + j.val, by have h := j.isLt; change 71296 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_71424 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨71424 + j.val, by have h := j.isLt; change 71424 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_71552 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨71552 + j.val, by have h := j.isLt; change 71552 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_71680 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨71680 + j.val, by have h := j.isLt; change 71680 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_71808 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨71808 + j.val, by have h := j.isLt; change 71808 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_71936 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨71936 + j.val, by have h := j.isLt; change 71936 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_72064 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨72064 + j.val, by have h := j.isLt; change 72064 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_72192 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨72192 + j.val, by have h := j.isLt; change 72192 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_72320 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨72320 + j.val, by have h := j.isLt; change 72320 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_72448 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨72448 + j.val, by have h := j.isLt; change 72448 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_72576 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨72576 + j.val, by have h := j.isLt; change 72576 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_72704 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨72704 + j.val, by have h := j.isLt; change 72704 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_72832 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨72832 + j.val, by have h := j.isLt; change 72832 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_72960 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨72960 + j.val, by have h := j.isLt; change 72960 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_73088 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨73088 + j.val, by have h := j.isLt; change 73088 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_73216 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨73216 + j.val, by have h := j.isLt; change 73216 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_73344 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨73344 + j.val, by have h := j.isLt; change 73344 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_73472 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨73472 + j.val, by have h := j.isLt; change 73472 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_73600 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨73600 + j.val, by have h := j.isLt; change 73600 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_73728 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨73728 + j.val, by have h := j.isLt; change 73728 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_73856 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨73856 + j.val, by have h := j.isLt; change 73856 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_73984 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨73984 + j.val, by have h := j.isLt; change 73984 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_74112 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨74112 + j.val, by have h := j.isLt; change 74112 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_74240 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨74240 + j.val, by have h := j.isLt; change 74240 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_74368 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨74368 + j.val, by have h := j.isLt; change 74368 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_74496 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨74496 + j.val, by have h := j.isLt; change 74496 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_74624 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨74624 + j.val, by have h := j.isLt; change 74624 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_74752 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨74752 + j.val, by have h := j.isLt; change 74752 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_74880 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨74880 + j.val, by have h := j.isLt; change 74880 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_75008 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨75008 + j.val, by have h := j.isLt; change 75008 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_75136 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨75136 + j.val, by have h := j.isLt; change 75136 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_75264 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨75264 + j.val, by have h := j.isLt; change 75264 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_75392 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨75392 + j.val, by have h := j.isLt; change 75392 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_75520 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨75520 + j.val, by have h := j.isLt; change 75520 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_75648 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨75648 + j.val, by have h := j.isLt; change 75648 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_75776 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨75776 + j.val, by have h := j.isLt; change 75776 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_75904 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨75904 + j.val, by have h := j.isLt; change 75904 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_76032 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨76032 + j.val, by have h := j.isLt; change 76032 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_76160 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨76160 + j.val, by have h := j.isLt; change 76160 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_76288 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨76288 + j.val, by have h := j.isLt; change 76288 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_76416 : ∀ j : Fin 128,
    checkOrderedAt triangleNodes triangleLevel
      ⟨76416 + j.val, by have h := j.isLt; change 76416 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private theorem triangle_chunk_76544 : ∀ j : Fin 119,
    checkOrderedAt triangleNodes triangleLevel
      ⟨76544 + j.val, by have h := j.isLt; change 76544 + j.val < 76663; omega⟩ = true := by
  decide +kernel

private def triangleChunkLength (b : Fin 599) : ℕ :=
  min 128 (76663 - 128 * b.val)

private def triangleChunkIndex (b : Fin 599)
    (k : Fin (triangleChunkLength b)) : Fin 76663 :=
  ⟨128 * b.val + k.val, by
    have hb := b.isLt
    have hk := k.isLt
    dsimp [triangleChunkLength] at hk
    omega⟩

private theorem triangleBlocks : ∀ b : Fin 599,
    ∀ k : Fin (triangleChunkLength b),
      checkOrderedAt triangleNodes triangleLevel (triangleChunkIndex b k) = true :=
  (Fin.cases triangle_chunk_0 (Fin.cases triangle_chunk_128 (Fin.cases triangle_chunk_256 (Fin.cases triangle_chunk_384 (Fin.cases triangle_chunk_512 (Fin.cases triangle_chunk_640 (Fin.cases triangle_chunk_768 (Fin.cases triangle_chunk_896 (Fin.cases triangle_chunk_1024 (Fin.cases triangle_chunk_1152 (Fin.cases triangle_chunk_1280 (Fin.cases triangle_chunk_1408 (Fin.cases triangle_chunk_1536 (Fin.cases triangle_chunk_1664 (Fin.cases triangle_chunk_1792 (Fin.cases triangle_chunk_1920 (Fin.cases triangle_chunk_2048 (Fin.cases triangle_chunk_2176 (Fin.cases triangle_chunk_2304 (Fin.cases triangle_chunk_2432 (Fin.cases triangle_chunk_2560 (Fin.cases triangle_chunk_2688 (Fin.cases triangle_chunk_2816 (Fin.cases triangle_chunk_2944 (Fin.cases triangle_chunk_3072 (Fin.cases triangle_chunk_3200 (Fin.cases triangle_chunk_3328 (Fin.cases triangle_chunk_3456 (Fin.cases triangle_chunk_3584 (Fin.cases triangle_chunk_3712 (Fin.cases triangle_chunk_3840 (Fin.cases triangle_chunk_3968 (Fin.cases triangle_chunk_4096 (Fin.cases triangle_chunk_4224 (Fin.cases triangle_chunk_4352 (Fin.cases triangle_chunk_4480 (Fin.cases triangle_chunk_4608 (Fin.cases triangle_chunk_4736 (Fin.cases triangle_chunk_4864 (Fin.cases triangle_chunk_4992 (Fin.cases triangle_chunk_5120 (Fin.cases triangle_chunk_5248 (Fin.cases triangle_chunk_5376 (Fin.cases triangle_chunk_5504 (Fin.cases triangle_chunk_5632 (Fin.cases triangle_chunk_5760 (Fin.cases triangle_chunk_5888 (Fin.cases triangle_chunk_6016 (Fin.cases triangle_chunk_6144 (Fin.cases triangle_chunk_6272 (Fin.cases triangle_chunk_6400 (Fin.cases triangle_chunk_6528 (Fin.cases triangle_chunk_6656 (Fin.cases triangle_chunk_6784 (Fin.cases triangle_chunk_6912 (Fin.cases triangle_chunk_7040 (Fin.cases triangle_chunk_7168 (Fin.cases triangle_chunk_7296 (Fin.cases triangle_chunk_7424 (Fin.cases triangle_chunk_7552 (Fin.cases triangle_chunk_7680 (Fin.cases triangle_chunk_7808 (Fin.cases triangle_chunk_7936 (Fin.cases triangle_chunk_8064 (Fin.cases triangle_chunk_8192 (Fin.cases triangle_chunk_8320 (Fin.cases triangle_chunk_8448 (Fin.cases triangle_chunk_8576 (Fin.cases triangle_chunk_8704 (Fin.cases triangle_chunk_8832 (Fin.cases triangle_chunk_8960 (Fin.cases triangle_chunk_9088 (Fin.cases triangle_chunk_9216 (Fin.cases triangle_chunk_9344 (Fin.cases triangle_chunk_9472 (Fin.cases triangle_chunk_9600 (Fin.cases triangle_chunk_9728 (Fin.cases triangle_chunk_9856 (Fin.cases triangle_chunk_9984 (Fin.cases triangle_chunk_10112 (Fin.cases triangle_chunk_10240 (Fin.cases triangle_chunk_10368 (Fin.cases triangle_chunk_10496 (Fin.cases triangle_chunk_10624 (Fin.cases triangle_chunk_10752 (Fin.cases triangle_chunk_10880 (Fin.cases triangle_chunk_11008 (Fin.cases triangle_chunk_11136 (Fin.cases triangle_chunk_11264 (Fin.cases triangle_chunk_11392 (Fin.cases triangle_chunk_11520 (Fin.cases triangle_chunk_11648 (Fin.cases triangle_chunk_11776 (Fin.cases triangle_chunk_11904 (Fin.cases triangle_chunk_12032 (Fin.cases triangle_chunk_12160 (Fin.cases triangle_chunk_12288 (Fin.cases triangle_chunk_12416 (Fin.cases triangle_chunk_12544 (Fin.cases triangle_chunk_12672 (Fin.cases triangle_chunk_12800 (Fin.cases triangle_chunk_12928 (Fin.cases triangle_chunk_13056 (Fin.cases triangle_chunk_13184 (Fin.cases triangle_chunk_13312 (Fin.cases triangle_chunk_13440 (Fin.cases triangle_chunk_13568 (Fin.cases triangle_chunk_13696 (Fin.cases triangle_chunk_13824 (Fin.cases triangle_chunk_13952 (Fin.cases triangle_chunk_14080 (Fin.cases triangle_chunk_14208 (Fin.cases triangle_chunk_14336 (Fin.cases triangle_chunk_14464 (Fin.cases triangle_chunk_14592 (Fin.cases triangle_chunk_14720 (Fin.cases triangle_chunk_14848 (Fin.cases triangle_chunk_14976 (Fin.cases triangle_chunk_15104 (Fin.cases triangle_chunk_15232 (Fin.cases triangle_chunk_15360 (Fin.cases triangle_chunk_15488 (Fin.cases triangle_chunk_15616 (Fin.cases triangle_chunk_15744 (Fin.cases triangle_chunk_15872 (Fin.cases triangle_chunk_16000 (Fin.cases triangle_chunk_16128 (Fin.cases triangle_chunk_16256 (Fin.cases triangle_chunk_16384 (Fin.cases triangle_chunk_16512 (Fin.cases triangle_chunk_16640 (Fin.cases triangle_chunk_16768 (Fin.cases triangle_chunk_16896 (Fin.cases triangle_chunk_17024 (Fin.cases triangle_chunk_17152 (Fin.cases triangle_chunk_17280 (Fin.cases triangle_chunk_17408 (Fin.cases triangle_chunk_17536 (Fin.cases triangle_chunk_17664 (Fin.cases triangle_chunk_17792 (Fin.cases triangle_chunk_17920 (Fin.cases triangle_chunk_18048 (Fin.cases triangle_chunk_18176 (Fin.cases triangle_chunk_18304 (Fin.cases triangle_chunk_18432 (Fin.cases triangle_chunk_18560 (Fin.cases triangle_chunk_18688 (Fin.cases triangle_chunk_18816 (Fin.cases triangle_chunk_18944 (Fin.cases triangle_chunk_19072 (Fin.cases triangle_chunk_19200 (Fin.cases triangle_chunk_19328 (Fin.cases triangle_chunk_19456 (Fin.cases triangle_chunk_19584 (Fin.cases triangle_chunk_19712 (Fin.cases triangle_chunk_19840 (Fin.cases triangle_chunk_19968 (Fin.cases triangle_chunk_20096 (Fin.cases triangle_chunk_20224 (Fin.cases triangle_chunk_20352 (Fin.cases triangle_chunk_20480 (Fin.cases triangle_chunk_20608 (Fin.cases triangle_chunk_20736 (Fin.cases triangle_chunk_20864 (Fin.cases triangle_chunk_20992 (Fin.cases triangle_chunk_21120 (Fin.cases triangle_chunk_21248 (Fin.cases triangle_chunk_21376 (Fin.cases triangle_chunk_21504 (Fin.cases triangle_chunk_21632 (Fin.cases triangle_chunk_21760 (Fin.cases triangle_chunk_21888 (Fin.cases triangle_chunk_22016 (Fin.cases triangle_chunk_22144 (Fin.cases triangle_chunk_22272 (Fin.cases triangle_chunk_22400 (Fin.cases triangle_chunk_22528 (Fin.cases triangle_chunk_22656 (Fin.cases triangle_chunk_22784 (Fin.cases triangle_chunk_22912 (Fin.cases triangle_chunk_23040 (Fin.cases triangle_chunk_23168 (Fin.cases triangle_chunk_23296 (Fin.cases triangle_chunk_23424 (Fin.cases triangle_chunk_23552 (Fin.cases triangle_chunk_23680 (Fin.cases triangle_chunk_23808 (Fin.cases triangle_chunk_23936 (Fin.cases triangle_chunk_24064 (Fin.cases triangle_chunk_24192 (Fin.cases triangle_chunk_24320 (Fin.cases triangle_chunk_24448 (Fin.cases triangle_chunk_24576 (Fin.cases triangle_chunk_24704 (Fin.cases triangle_chunk_24832 (Fin.cases triangle_chunk_24960 (Fin.cases triangle_chunk_25088 (Fin.cases triangle_chunk_25216 (Fin.cases triangle_chunk_25344 (Fin.cases triangle_chunk_25472 (Fin.cases triangle_chunk_25600 (Fin.cases triangle_chunk_25728 (Fin.cases triangle_chunk_25856 (Fin.cases triangle_chunk_25984 (Fin.cases triangle_chunk_26112 (Fin.cases triangle_chunk_26240 (Fin.cases triangle_chunk_26368 (Fin.cases triangle_chunk_26496 (Fin.cases triangle_chunk_26624 (Fin.cases triangle_chunk_26752 (Fin.cases triangle_chunk_26880 (Fin.cases triangle_chunk_27008 (Fin.cases triangle_chunk_27136 (Fin.cases triangle_chunk_27264 (Fin.cases triangle_chunk_27392 (Fin.cases triangle_chunk_27520 (Fin.cases triangle_chunk_27648 (Fin.cases triangle_chunk_27776 (Fin.cases triangle_chunk_27904 (Fin.cases triangle_chunk_28032 (Fin.cases triangle_chunk_28160 (Fin.cases triangle_chunk_28288 (Fin.cases triangle_chunk_28416 (Fin.cases triangle_chunk_28544 (Fin.cases triangle_chunk_28672 (Fin.cases triangle_chunk_28800 (Fin.cases triangle_chunk_28928 (Fin.cases triangle_chunk_29056 (Fin.cases triangle_chunk_29184 (Fin.cases triangle_chunk_29312 (Fin.cases triangle_chunk_29440 (Fin.cases triangle_chunk_29568 (Fin.cases triangle_chunk_29696 (Fin.cases triangle_chunk_29824 (Fin.cases triangle_chunk_29952 (Fin.cases triangle_chunk_30080 (Fin.cases triangle_chunk_30208 (Fin.cases triangle_chunk_30336 (Fin.cases triangle_chunk_30464 (Fin.cases triangle_chunk_30592 (Fin.cases triangle_chunk_30720 (Fin.cases triangle_chunk_30848 (Fin.cases triangle_chunk_30976 (Fin.cases triangle_chunk_31104 (Fin.cases triangle_chunk_31232 (Fin.cases triangle_chunk_31360 (Fin.cases triangle_chunk_31488 (Fin.cases triangle_chunk_31616 (Fin.cases triangle_chunk_31744 (Fin.cases triangle_chunk_31872 (Fin.cases triangle_chunk_32000 (Fin.cases triangle_chunk_32128 (Fin.cases triangle_chunk_32256 (Fin.cases triangle_chunk_32384 (Fin.cases triangle_chunk_32512 (Fin.cases triangle_chunk_32640 (Fin.cases triangle_chunk_32768 (Fin.cases triangle_chunk_32896 (Fin.cases triangle_chunk_33024 (Fin.cases triangle_chunk_33152 (Fin.cases triangle_chunk_33280 (Fin.cases triangle_chunk_33408 (Fin.cases triangle_chunk_33536 (Fin.cases triangle_chunk_33664 (Fin.cases triangle_chunk_33792 (Fin.cases triangle_chunk_33920 (Fin.cases triangle_chunk_34048 (Fin.cases triangle_chunk_34176 (Fin.cases triangle_chunk_34304 (Fin.cases triangle_chunk_34432 (Fin.cases triangle_chunk_34560 (Fin.cases triangle_chunk_34688 (Fin.cases triangle_chunk_34816 (Fin.cases triangle_chunk_34944 (Fin.cases triangle_chunk_35072 (Fin.cases triangle_chunk_35200 (Fin.cases triangle_chunk_35328 (Fin.cases triangle_chunk_35456 (Fin.cases triangle_chunk_35584 (Fin.cases triangle_chunk_35712 (Fin.cases triangle_chunk_35840 (Fin.cases triangle_chunk_35968 (Fin.cases triangle_chunk_36096 (Fin.cases triangle_chunk_36224 (Fin.cases triangle_chunk_36352 (Fin.cases triangle_chunk_36480 (Fin.cases triangle_chunk_36608 (Fin.cases triangle_chunk_36736 (Fin.cases triangle_chunk_36864 (Fin.cases triangle_chunk_36992 (Fin.cases triangle_chunk_37120 (Fin.cases triangle_chunk_37248 (Fin.cases triangle_chunk_37376 (Fin.cases triangle_chunk_37504 (Fin.cases triangle_chunk_37632 (Fin.cases triangle_chunk_37760 (Fin.cases triangle_chunk_37888 (Fin.cases triangle_chunk_38016 (Fin.cases triangle_chunk_38144 (Fin.cases triangle_chunk_38272 (Fin.cases triangle_chunk_38400 (Fin.cases triangle_chunk_38528 (Fin.cases triangle_chunk_38656 (Fin.cases triangle_chunk_38784 (Fin.cases triangle_chunk_38912 (Fin.cases triangle_chunk_39040 (Fin.cases triangle_chunk_39168 (Fin.cases triangle_chunk_39296 (Fin.cases triangle_chunk_39424 (Fin.cases triangle_chunk_39552 (Fin.cases triangle_chunk_39680 (Fin.cases triangle_chunk_39808 (Fin.cases triangle_chunk_39936 (Fin.cases triangle_chunk_40064 (Fin.cases triangle_chunk_40192 (Fin.cases triangle_chunk_40320 (Fin.cases triangle_chunk_40448 (Fin.cases triangle_chunk_40576 (Fin.cases triangle_chunk_40704 (Fin.cases triangle_chunk_40832 (Fin.cases triangle_chunk_40960 (Fin.cases triangle_chunk_41088 (Fin.cases triangle_chunk_41216 (Fin.cases triangle_chunk_41344 (Fin.cases triangle_chunk_41472 (Fin.cases triangle_chunk_41600 (Fin.cases triangle_chunk_41728 (Fin.cases triangle_chunk_41856 (Fin.cases triangle_chunk_41984 (Fin.cases triangle_chunk_42112 (Fin.cases triangle_chunk_42240 (Fin.cases triangle_chunk_42368 (Fin.cases triangle_chunk_42496 (Fin.cases triangle_chunk_42624 (Fin.cases triangle_chunk_42752 (Fin.cases triangle_chunk_42880 (Fin.cases triangle_chunk_43008 (Fin.cases triangle_chunk_43136 (Fin.cases triangle_chunk_43264 (Fin.cases triangle_chunk_43392 (Fin.cases triangle_chunk_43520 (Fin.cases triangle_chunk_43648 (Fin.cases triangle_chunk_43776 (Fin.cases triangle_chunk_43904 (Fin.cases triangle_chunk_44032 (Fin.cases triangle_chunk_44160 (Fin.cases triangle_chunk_44288 (Fin.cases triangle_chunk_44416 (Fin.cases triangle_chunk_44544 (Fin.cases triangle_chunk_44672 (Fin.cases triangle_chunk_44800 (Fin.cases triangle_chunk_44928 (Fin.cases triangle_chunk_45056 (Fin.cases triangle_chunk_45184 (Fin.cases triangle_chunk_45312 (Fin.cases triangle_chunk_45440 (Fin.cases triangle_chunk_45568 (Fin.cases triangle_chunk_45696 (Fin.cases triangle_chunk_45824 (Fin.cases triangle_chunk_45952 (Fin.cases triangle_chunk_46080 (Fin.cases triangle_chunk_46208 (Fin.cases triangle_chunk_46336 (Fin.cases triangle_chunk_46464 (Fin.cases triangle_chunk_46592 (Fin.cases triangle_chunk_46720 (Fin.cases triangle_chunk_46848 (Fin.cases triangle_chunk_46976 (Fin.cases triangle_chunk_47104 (Fin.cases triangle_chunk_47232 (Fin.cases triangle_chunk_47360 (Fin.cases triangle_chunk_47488 (Fin.cases triangle_chunk_47616 (Fin.cases triangle_chunk_47744 (Fin.cases triangle_chunk_47872 (Fin.cases triangle_chunk_48000 (Fin.cases triangle_chunk_48128 (Fin.cases triangle_chunk_48256 (Fin.cases triangle_chunk_48384 (Fin.cases triangle_chunk_48512 (Fin.cases triangle_chunk_48640 (Fin.cases triangle_chunk_48768 (Fin.cases triangle_chunk_48896 (Fin.cases triangle_chunk_49024 (Fin.cases triangle_chunk_49152 (Fin.cases triangle_chunk_49280 (Fin.cases triangle_chunk_49408 (Fin.cases triangle_chunk_49536 (Fin.cases triangle_chunk_49664 (Fin.cases triangle_chunk_49792 (Fin.cases triangle_chunk_49920 (Fin.cases triangle_chunk_50048 (Fin.cases triangle_chunk_50176 (Fin.cases triangle_chunk_50304 (Fin.cases triangle_chunk_50432 (Fin.cases triangle_chunk_50560 (Fin.cases triangle_chunk_50688 (Fin.cases triangle_chunk_50816 (Fin.cases triangle_chunk_50944 (Fin.cases triangle_chunk_51072 (Fin.cases triangle_chunk_51200 (Fin.cases triangle_chunk_51328 (Fin.cases triangle_chunk_51456 (Fin.cases triangle_chunk_51584 (Fin.cases triangle_chunk_51712 (Fin.cases triangle_chunk_51840 (Fin.cases triangle_chunk_51968 (Fin.cases triangle_chunk_52096 (Fin.cases triangle_chunk_52224 (Fin.cases triangle_chunk_52352 (Fin.cases triangle_chunk_52480 (Fin.cases triangle_chunk_52608 (Fin.cases triangle_chunk_52736 (Fin.cases triangle_chunk_52864 (Fin.cases triangle_chunk_52992 (Fin.cases triangle_chunk_53120 (Fin.cases triangle_chunk_53248 (Fin.cases triangle_chunk_53376 (Fin.cases triangle_chunk_53504 (Fin.cases triangle_chunk_53632 (Fin.cases triangle_chunk_53760 (Fin.cases triangle_chunk_53888 (Fin.cases triangle_chunk_54016 (Fin.cases triangle_chunk_54144 (Fin.cases triangle_chunk_54272 (Fin.cases triangle_chunk_54400 (Fin.cases triangle_chunk_54528 (Fin.cases triangle_chunk_54656 (Fin.cases triangle_chunk_54784 (Fin.cases triangle_chunk_54912 (Fin.cases triangle_chunk_55040 (Fin.cases triangle_chunk_55168 (Fin.cases triangle_chunk_55296 (Fin.cases triangle_chunk_55424 (Fin.cases triangle_chunk_55552 (Fin.cases triangle_chunk_55680 (Fin.cases triangle_chunk_55808 (Fin.cases triangle_chunk_55936 (Fin.cases triangle_chunk_56064 (Fin.cases triangle_chunk_56192 (Fin.cases triangle_chunk_56320 (Fin.cases triangle_chunk_56448 (Fin.cases triangle_chunk_56576 (Fin.cases triangle_chunk_56704 (Fin.cases triangle_chunk_56832 (Fin.cases triangle_chunk_56960 (Fin.cases triangle_chunk_57088 (Fin.cases triangle_chunk_57216 (Fin.cases triangle_chunk_57344 (Fin.cases triangle_chunk_57472 (Fin.cases triangle_chunk_57600 (Fin.cases triangle_chunk_57728 (Fin.cases triangle_chunk_57856 (Fin.cases triangle_chunk_57984 (Fin.cases triangle_chunk_58112 (Fin.cases triangle_chunk_58240 (Fin.cases triangle_chunk_58368 (Fin.cases triangle_chunk_58496 (Fin.cases triangle_chunk_58624 (Fin.cases triangle_chunk_58752 (Fin.cases triangle_chunk_58880 (Fin.cases triangle_chunk_59008 (Fin.cases triangle_chunk_59136 (Fin.cases triangle_chunk_59264 (Fin.cases triangle_chunk_59392 (Fin.cases triangle_chunk_59520 (Fin.cases triangle_chunk_59648 (Fin.cases triangle_chunk_59776 (Fin.cases triangle_chunk_59904 (Fin.cases triangle_chunk_60032 (Fin.cases triangle_chunk_60160 (Fin.cases triangle_chunk_60288 (Fin.cases triangle_chunk_60416 (Fin.cases triangle_chunk_60544 (Fin.cases triangle_chunk_60672 (Fin.cases triangle_chunk_60800 (Fin.cases triangle_chunk_60928 (Fin.cases triangle_chunk_61056 (Fin.cases triangle_chunk_61184 (Fin.cases triangle_chunk_61312 (Fin.cases triangle_chunk_61440 (Fin.cases triangle_chunk_61568 (Fin.cases triangle_chunk_61696 (Fin.cases triangle_chunk_61824 (Fin.cases triangle_chunk_61952 (Fin.cases triangle_chunk_62080 (Fin.cases triangle_chunk_62208 (Fin.cases triangle_chunk_62336 (Fin.cases triangle_chunk_62464 (Fin.cases triangle_chunk_62592 (Fin.cases triangle_chunk_62720 (Fin.cases triangle_chunk_62848 (Fin.cases triangle_chunk_62976 (Fin.cases triangle_chunk_63104 (Fin.cases triangle_chunk_63232 (Fin.cases triangle_chunk_63360 (Fin.cases triangle_chunk_63488 (Fin.cases triangle_chunk_63616 (Fin.cases triangle_chunk_63744 (Fin.cases triangle_chunk_63872 (Fin.cases triangle_chunk_64000 (Fin.cases triangle_chunk_64128 (Fin.cases triangle_chunk_64256 (Fin.cases triangle_chunk_64384 (Fin.cases triangle_chunk_64512 (Fin.cases triangle_chunk_64640 (Fin.cases triangle_chunk_64768 (Fin.cases triangle_chunk_64896 (Fin.cases triangle_chunk_65024 (Fin.cases triangle_chunk_65152 (Fin.cases triangle_chunk_65280 (Fin.cases triangle_chunk_65408 (Fin.cases triangle_chunk_65536 (Fin.cases triangle_chunk_65664 (Fin.cases triangle_chunk_65792 (Fin.cases triangle_chunk_65920 (Fin.cases triangle_chunk_66048 (Fin.cases triangle_chunk_66176 (Fin.cases triangle_chunk_66304 (Fin.cases triangle_chunk_66432 (Fin.cases triangle_chunk_66560 (Fin.cases triangle_chunk_66688 (Fin.cases triangle_chunk_66816 (Fin.cases triangle_chunk_66944 (Fin.cases triangle_chunk_67072 (Fin.cases triangle_chunk_67200 (Fin.cases triangle_chunk_67328 (Fin.cases triangle_chunk_67456 (Fin.cases triangle_chunk_67584 (Fin.cases triangle_chunk_67712 (Fin.cases triangle_chunk_67840 (Fin.cases triangle_chunk_67968 (Fin.cases triangle_chunk_68096 (Fin.cases triangle_chunk_68224 (Fin.cases triangle_chunk_68352 (Fin.cases triangle_chunk_68480 (Fin.cases triangle_chunk_68608 (Fin.cases triangle_chunk_68736 (Fin.cases triangle_chunk_68864 (Fin.cases triangle_chunk_68992 (Fin.cases triangle_chunk_69120 (Fin.cases triangle_chunk_69248 (Fin.cases triangle_chunk_69376 (Fin.cases triangle_chunk_69504 (Fin.cases triangle_chunk_69632 (Fin.cases triangle_chunk_69760 (Fin.cases triangle_chunk_69888 (Fin.cases triangle_chunk_70016 (Fin.cases triangle_chunk_70144 (Fin.cases triangle_chunk_70272 (Fin.cases triangle_chunk_70400 (Fin.cases triangle_chunk_70528 (Fin.cases triangle_chunk_70656 (Fin.cases triangle_chunk_70784 (Fin.cases triangle_chunk_70912 (Fin.cases triangle_chunk_71040 (Fin.cases triangle_chunk_71168 (Fin.cases triangle_chunk_71296 (Fin.cases triangle_chunk_71424 (Fin.cases triangle_chunk_71552 (Fin.cases triangle_chunk_71680 (Fin.cases triangle_chunk_71808 (Fin.cases triangle_chunk_71936 (Fin.cases triangle_chunk_72064 (Fin.cases triangle_chunk_72192 (Fin.cases triangle_chunk_72320 (Fin.cases triangle_chunk_72448 (Fin.cases triangle_chunk_72576 (Fin.cases triangle_chunk_72704 (Fin.cases triangle_chunk_72832 (Fin.cases triangle_chunk_72960 (Fin.cases triangle_chunk_73088 (Fin.cases triangle_chunk_73216 (Fin.cases triangle_chunk_73344 (Fin.cases triangle_chunk_73472 (Fin.cases triangle_chunk_73600 (Fin.cases triangle_chunk_73728 (Fin.cases triangle_chunk_73856 (Fin.cases triangle_chunk_73984 (Fin.cases triangle_chunk_74112 (Fin.cases triangle_chunk_74240 (Fin.cases triangle_chunk_74368 (Fin.cases triangle_chunk_74496 (Fin.cases triangle_chunk_74624 (Fin.cases triangle_chunk_74752 (Fin.cases triangle_chunk_74880 (Fin.cases triangle_chunk_75008 (Fin.cases triangle_chunk_75136 (Fin.cases triangle_chunk_75264 (Fin.cases triangle_chunk_75392 (Fin.cases triangle_chunk_75520 (Fin.cases triangle_chunk_75648 (Fin.cases triangle_chunk_75776 (Fin.cases triangle_chunk_75904 (Fin.cases triangle_chunk_76032 (Fin.cases triangle_chunk_76160 (Fin.cases triangle_chunk_76288 (Fin.cases triangle_chunk_76416 (Fin.cases triangle_chunk_76544 (fun b : Fin 0 => Fin.elim0 b))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem triangle_ordering (index : Fin triangleSize) :
    checkOrderedAt triangleNodes triangleLevel index = true := by
  let b : Fin 599 := ⟨index.val / 128, by have hi : index.val < 76663 := index.isLt; omega⟩
  let k : Fin (triangleChunkLength b) := ⟨index.val % 128, by
    have hi : index.val < 76663 := index.isLt
    dsimp [triangleChunkLength, b]
    omega⟩
  have same : triangleChunkIndex b k = index := by
    apply Fin.ext
    dsimp [triangleChunkIndex, b, k]
    omega
  simpa only [same] using triangleBlocks b k

def triangleDiagram : OrderedDiagram 10 triangleSize :=
  checked_ordered_diagram triangleNodes triangleLevel triangle_ordering

theorem triangle_root_level : triangleLevel triangleRoot = 0 := by
  decide +kernel

#print axioms triangle_ordering
#print axioms triangleDiagram
#print axioms triangle_root_level

private theorem singleton_chunk_0 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨0 + j.val, by have h := j.isLt; change 0 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_128 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨128 + j.val, by have h := j.isLt; change 128 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_256 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨256 + j.val, by have h := j.isLt; change 256 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_384 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨384 + j.val, by have h := j.isLt; change 384 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_512 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨512 + j.val, by have h := j.isLt; change 512 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_640 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨640 + j.val, by have h := j.isLt; change 640 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_768 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨768 + j.val, by have h := j.isLt; change 768 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_896 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨896 + j.val, by have h := j.isLt; change 896 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_1024 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨1024 + j.val, by have h := j.isLt; change 1024 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_1152 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨1152 + j.val, by have h := j.isLt; change 1152 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_1280 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨1280 + j.val, by have h := j.isLt; change 1280 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_1408 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨1408 + j.val, by have h := j.isLt; change 1408 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_1536 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨1536 + j.val, by have h := j.isLt; change 1536 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_1664 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨1664 + j.val, by have h := j.isLt; change 1664 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_1792 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨1792 + j.val, by have h := j.isLt; change 1792 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_1920 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨1920 + j.val, by have h := j.isLt; change 1920 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_2048 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨2048 + j.val, by have h := j.isLt; change 2048 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_2176 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨2176 + j.val, by have h := j.isLt; change 2176 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_2304 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨2304 + j.val, by have h := j.isLt; change 2304 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_2432 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨2432 + j.val, by have h := j.isLt; change 2432 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_2560 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨2560 + j.val, by have h := j.isLt; change 2560 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_2688 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨2688 + j.val, by have h := j.isLt; change 2688 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_2816 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨2816 + j.val, by have h := j.isLt; change 2816 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_2944 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨2944 + j.val, by have h := j.isLt; change 2944 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_3072 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨3072 + j.val, by have h := j.isLt; change 3072 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_3200 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨3200 + j.val, by have h := j.isLt; change 3200 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_3328 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨3328 + j.val, by have h := j.isLt; change 3328 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_3456 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨3456 + j.val, by have h := j.isLt; change 3456 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_3584 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨3584 + j.val, by have h := j.isLt; change 3584 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_3712 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨3712 + j.val, by have h := j.isLt; change 3712 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_3840 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨3840 + j.val, by have h := j.isLt; change 3840 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_3968 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨3968 + j.val, by have h := j.isLt; change 3968 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_4096 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨4096 + j.val, by have h := j.isLt; change 4096 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_4224 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨4224 + j.val, by have h := j.isLt; change 4224 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_4352 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨4352 + j.val, by have h := j.isLt; change 4352 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_4480 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨4480 + j.val, by have h := j.isLt; change 4480 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_4608 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨4608 + j.val, by have h := j.isLt; change 4608 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_4736 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨4736 + j.val, by have h := j.isLt; change 4736 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_4864 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨4864 + j.val, by have h := j.isLt; change 4864 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_4992 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨4992 + j.val, by have h := j.isLt; change 4992 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_5120 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨5120 + j.val, by have h := j.isLt; change 5120 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_5248 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨5248 + j.val, by have h := j.isLt; change 5248 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_5376 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨5376 + j.val, by have h := j.isLt; change 5376 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_5504 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨5504 + j.val, by have h := j.isLt; change 5504 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_5632 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨5632 + j.val, by have h := j.isLt; change 5632 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_5760 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨5760 + j.val, by have h := j.isLt; change 5760 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_5888 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨5888 + j.val, by have h := j.isLt; change 5888 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_6016 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨6016 + j.val, by have h := j.isLt; change 6016 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_6144 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨6144 + j.val, by have h := j.isLt; change 6144 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_6272 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨6272 + j.val, by have h := j.isLt; change 6272 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_6400 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨6400 + j.val, by have h := j.isLt; change 6400 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_6528 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨6528 + j.val, by have h := j.isLt; change 6528 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_6656 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨6656 + j.val, by have h := j.isLt; change 6656 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_6784 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨6784 + j.val, by have h := j.isLt; change 6784 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_6912 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨6912 + j.val, by have h := j.isLt; change 6912 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_7040 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨7040 + j.val, by have h := j.isLt; change 7040 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_7168 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨7168 + j.val, by have h := j.isLt; change 7168 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_7296 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨7296 + j.val, by have h := j.isLt; change 7296 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_7424 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨7424 + j.val, by have h := j.isLt; change 7424 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_7552 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨7552 + j.val, by have h := j.isLt; change 7552 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_7680 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨7680 + j.val, by have h := j.isLt; change 7680 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_7808 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨7808 + j.val, by have h := j.isLt; change 7808 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_7936 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨7936 + j.val, by have h := j.isLt; change 7936 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_8064 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨8064 + j.val, by have h := j.isLt; change 8064 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_8192 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨8192 + j.val, by have h := j.isLt; change 8192 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_8320 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨8320 + j.val, by have h := j.isLt; change 8320 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_8448 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨8448 + j.val, by have h := j.isLt; change 8448 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_8576 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨8576 + j.val, by have h := j.isLt; change 8576 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_8704 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨8704 + j.val, by have h := j.isLt; change 8704 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_8832 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨8832 + j.val, by have h := j.isLt; change 8832 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_8960 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨8960 + j.val, by have h := j.isLt; change 8960 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_9088 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨9088 + j.val, by have h := j.isLt; change 9088 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_9216 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨9216 + j.val, by have h := j.isLt; change 9216 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_9344 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨9344 + j.val, by have h := j.isLt; change 9344 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_9472 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨9472 + j.val, by have h := j.isLt; change 9472 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_9600 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨9600 + j.val, by have h := j.isLt; change 9600 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_9728 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨9728 + j.val, by have h := j.isLt; change 9728 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_9856 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨9856 + j.val, by have h := j.isLt; change 9856 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_9984 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨9984 + j.val, by have h := j.isLt; change 9984 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_10112 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨10112 + j.val, by have h := j.isLt; change 10112 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_10240 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨10240 + j.val, by have h := j.isLt; change 10240 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_10368 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨10368 + j.val, by have h := j.isLt; change 10368 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_10496 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨10496 + j.val, by have h := j.isLt; change 10496 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_10624 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨10624 + j.val, by have h := j.isLt; change 10624 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_10752 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨10752 + j.val, by have h := j.isLt; change 10752 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_10880 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨10880 + j.val, by have h := j.isLt; change 10880 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_11008 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨11008 + j.val, by have h := j.isLt; change 11008 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_11136 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨11136 + j.val, by have h := j.isLt; change 11136 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_11264 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨11264 + j.val, by have h := j.isLt; change 11264 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_11392 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨11392 + j.val, by have h := j.isLt; change 11392 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_11520 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨11520 + j.val, by have h := j.isLt; change 11520 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_11648 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨11648 + j.val, by have h := j.isLt; change 11648 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_11776 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨11776 + j.val, by have h := j.isLt; change 11776 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_11904 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨11904 + j.val, by have h := j.isLt; change 11904 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_12032 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨12032 + j.val, by have h := j.isLt; change 12032 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_12160 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨12160 + j.val, by have h := j.isLt; change 12160 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_12288 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨12288 + j.val, by have h := j.isLt; change 12288 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_12416 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨12416 + j.val, by have h := j.isLt; change 12416 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_12544 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨12544 + j.val, by have h := j.isLt; change 12544 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_12672 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨12672 + j.val, by have h := j.isLt; change 12672 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_12800 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨12800 + j.val, by have h := j.isLt; change 12800 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_12928 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨12928 + j.val, by have h := j.isLt; change 12928 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_13056 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨13056 + j.val, by have h := j.isLt; change 13056 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_13184 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨13184 + j.val, by have h := j.isLt; change 13184 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_13312 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨13312 + j.val, by have h := j.isLt; change 13312 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_13440 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨13440 + j.val, by have h := j.isLt; change 13440 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_13568 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨13568 + j.val, by have h := j.isLt; change 13568 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_13696 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨13696 + j.val, by have h := j.isLt; change 13696 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_13824 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨13824 + j.val, by have h := j.isLt; change 13824 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_13952 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨13952 + j.val, by have h := j.isLt; change 13952 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_14080 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨14080 + j.val, by have h := j.isLt; change 14080 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_14208 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨14208 + j.val, by have h := j.isLt; change 14208 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_14336 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨14336 + j.val, by have h := j.isLt; change 14336 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_14464 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨14464 + j.val, by have h := j.isLt; change 14464 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_14592 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨14592 + j.val, by have h := j.isLt; change 14592 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_14720 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨14720 + j.val, by have h := j.isLt; change 14720 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_14848 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨14848 + j.val, by have h := j.isLt; change 14848 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_14976 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨14976 + j.val, by have h := j.isLt; change 14976 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_15104 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨15104 + j.val, by have h := j.isLt; change 15104 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_15232 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨15232 + j.val, by have h := j.isLt; change 15232 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_15360 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨15360 + j.val, by have h := j.isLt; change 15360 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_15488 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨15488 + j.val, by have h := j.isLt; change 15488 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_15616 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨15616 + j.val, by have h := j.isLt; change 15616 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_15744 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨15744 + j.val, by have h := j.isLt; change 15744 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_15872 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨15872 + j.val, by have h := j.isLt; change 15872 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_16000 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨16000 + j.val, by have h := j.isLt; change 16000 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_16128 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨16128 + j.val, by have h := j.isLt; change 16128 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_16256 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨16256 + j.val, by have h := j.isLt; change 16256 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_16384 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨16384 + j.val, by have h := j.isLt; change 16384 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_16512 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨16512 + j.val, by have h := j.isLt; change 16512 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_16640 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨16640 + j.val, by have h := j.isLt; change 16640 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_16768 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨16768 + j.val, by have h := j.isLt; change 16768 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_16896 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨16896 + j.val, by have h := j.isLt; change 16896 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_17024 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨17024 + j.val, by have h := j.isLt; change 17024 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_17152 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨17152 + j.val, by have h := j.isLt; change 17152 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_17280 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨17280 + j.val, by have h := j.isLt; change 17280 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_17408 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨17408 + j.val, by have h := j.isLt; change 17408 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_17536 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨17536 + j.val, by have h := j.isLt; change 17536 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_17664 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨17664 + j.val, by have h := j.isLt; change 17664 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_17792 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨17792 + j.val, by have h := j.isLt; change 17792 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_17920 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨17920 + j.val, by have h := j.isLt; change 17920 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_18048 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨18048 + j.val, by have h := j.isLt; change 18048 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_18176 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨18176 + j.val, by have h := j.isLt; change 18176 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_18304 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨18304 + j.val, by have h := j.isLt; change 18304 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_18432 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨18432 + j.val, by have h := j.isLt; change 18432 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_18560 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨18560 + j.val, by have h := j.isLt; change 18560 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_18688 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨18688 + j.val, by have h := j.isLt; change 18688 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_18816 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨18816 + j.val, by have h := j.isLt; change 18816 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_18944 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨18944 + j.val, by have h := j.isLt; change 18944 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_19072 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨19072 + j.val, by have h := j.isLt; change 19072 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_19200 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨19200 + j.val, by have h := j.isLt; change 19200 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_19328 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨19328 + j.val, by have h := j.isLt; change 19328 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_19456 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨19456 + j.val, by have h := j.isLt; change 19456 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_19584 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨19584 + j.val, by have h := j.isLt; change 19584 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_19712 : ∀ j : Fin 128,
    checkOrderedAt singletonNodes singletonLevel
      ⟨19712 + j.val, by have h := j.isLt; change 19712 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private theorem singleton_chunk_19840 : ∀ j : Fin 111,
    checkOrderedAt singletonNodes singletonLevel
      ⟨19840 + j.val, by have h := j.isLt; change 19840 + j.val < 19951; omega⟩ = true := by
  decide +kernel

private def singletonChunkLength (b : Fin 156) : ℕ :=
  min 128 (19951 - 128 * b.val)

private def singletonChunkIndex (b : Fin 156)
    (k : Fin (singletonChunkLength b)) : Fin 19951 :=
  ⟨128 * b.val + k.val, by
    have hb := b.isLt
    have hk := k.isLt
    dsimp [singletonChunkLength] at hk
    omega⟩

private theorem singletonBlocks : ∀ b : Fin 156,
    ∀ k : Fin (singletonChunkLength b),
      checkOrderedAt singletonNodes singletonLevel (singletonChunkIndex b k) = true :=
  (Fin.cases singleton_chunk_0 (Fin.cases singleton_chunk_128 (Fin.cases singleton_chunk_256 (Fin.cases singleton_chunk_384 (Fin.cases singleton_chunk_512 (Fin.cases singleton_chunk_640 (Fin.cases singleton_chunk_768 (Fin.cases singleton_chunk_896 (Fin.cases singleton_chunk_1024 (Fin.cases singleton_chunk_1152 (Fin.cases singleton_chunk_1280 (Fin.cases singleton_chunk_1408 (Fin.cases singleton_chunk_1536 (Fin.cases singleton_chunk_1664 (Fin.cases singleton_chunk_1792 (Fin.cases singleton_chunk_1920 (Fin.cases singleton_chunk_2048 (Fin.cases singleton_chunk_2176 (Fin.cases singleton_chunk_2304 (Fin.cases singleton_chunk_2432 (Fin.cases singleton_chunk_2560 (Fin.cases singleton_chunk_2688 (Fin.cases singleton_chunk_2816 (Fin.cases singleton_chunk_2944 (Fin.cases singleton_chunk_3072 (Fin.cases singleton_chunk_3200 (Fin.cases singleton_chunk_3328 (Fin.cases singleton_chunk_3456 (Fin.cases singleton_chunk_3584 (Fin.cases singleton_chunk_3712 (Fin.cases singleton_chunk_3840 (Fin.cases singleton_chunk_3968 (Fin.cases singleton_chunk_4096 (Fin.cases singleton_chunk_4224 (Fin.cases singleton_chunk_4352 (Fin.cases singleton_chunk_4480 (Fin.cases singleton_chunk_4608 (Fin.cases singleton_chunk_4736 (Fin.cases singleton_chunk_4864 (Fin.cases singleton_chunk_4992 (Fin.cases singleton_chunk_5120 (Fin.cases singleton_chunk_5248 (Fin.cases singleton_chunk_5376 (Fin.cases singleton_chunk_5504 (Fin.cases singleton_chunk_5632 (Fin.cases singleton_chunk_5760 (Fin.cases singleton_chunk_5888 (Fin.cases singleton_chunk_6016 (Fin.cases singleton_chunk_6144 (Fin.cases singleton_chunk_6272 (Fin.cases singleton_chunk_6400 (Fin.cases singleton_chunk_6528 (Fin.cases singleton_chunk_6656 (Fin.cases singleton_chunk_6784 (Fin.cases singleton_chunk_6912 (Fin.cases singleton_chunk_7040 (Fin.cases singleton_chunk_7168 (Fin.cases singleton_chunk_7296 (Fin.cases singleton_chunk_7424 (Fin.cases singleton_chunk_7552 (Fin.cases singleton_chunk_7680 (Fin.cases singleton_chunk_7808 (Fin.cases singleton_chunk_7936 (Fin.cases singleton_chunk_8064 (Fin.cases singleton_chunk_8192 (Fin.cases singleton_chunk_8320 (Fin.cases singleton_chunk_8448 (Fin.cases singleton_chunk_8576 (Fin.cases singleton_chunk_8704 (Fin.cases singleton_chunk_8832 (Fin.cases singleton_chunk_8960 (Fin.cases singleton_chunk_9088 (Fin.cases singleton_chunk_9216 (Fin.cases singleton_chunk_9344 (Fin.cases singleton_chunk_9472 (Fin.cases singleton_chunk_9600 (Fin.cases singleton_chunk_9728 (Fin.cases singleton_chunk_9856 (Fin.cases singleton_chunk_9984 (Fin.cases singleton_chunk_10112 (Fin.cases singleton_chunk_10240 (Fin.cases singleton_chunk_10368 (Fin.cases singleton_chunk_10496 (Fin.cases singleton_chunk_10624 (Fin.cases singleton_chunk_10752 (Fin.cases singleton_chunk_10880 (Fin.cases singleton_chunk_11008 (Fin.cases singleton_chunk_11136 (Fin.cases singleton_chunk_11264 (Fin.cases singleton_chunk_11392 (Fin.cases singleton_chunk_11520 (Fin.cases singleton_chunk_11648 (Fin.cases singleton_chunk_11776 (Fin.cases singleton_chunk_11904 (Fin.cases singleton_chunk_12032 (Fin.cases singleton_chunk_12160 (Fin.cases singleton_chunk_12288 (Fin.cases singleton_chunk_12416 (Fin.cases singleton_chunk_12544 (Fin.cases singleton_chunk_12672 (Fin.cases singleton_chunk_12800 (Fin.cases singleton_chunk_12928 (Fin.cases singleton_chunk_13056 (Fin.cases singleton_chunk_13184 (Fin.cases singleton_chunk_13312 (Fin.cases singleton_chunk_13440 (Fin.cases singleton_chunk_13568 (Fin.cases singleton_chunk_13696 (Fin.cases singleton_chunk_13824 (Fin.cases singleton_chunk_13952 (Fin.cases singleton_chunk_14080 (Fin.cases singleton_chunk_14208 (Fin.cases singleton_chunk_14336 (Fin.cases singleton_chunk_14464 (Fin.cases singleton_chunk_14592 (Fin.cases singleton_chunk_14720 (Fin.cases singleton_chunk_14848 (Fin.cases singleton_chunk_14976 (Fin.cases singleton_chunk_15104 (Fin.cases singleton_chunk_15232 (Fin.cases singleton_chunk_15360 (Fin.cases singleton_chunk_15488 (Fin.cases singleton_chunk_15616 (Fin.cases singleton_chunk_15744 (Fin.cases singleton_chunk_15872 (Fin.cases singleton_chunk_16000 (Fin.cases singleton_chunk_16128 (Fin.cases singleton_chunk_16256 (Fin.cases singleton_chunk_16384 (Fin.cases singleton_chunk_16512 (Fin.cases singleton_chunk_16640 (Fin.cases singleton_chunk_16768 (Fin.cases singleton_chunk_16896 (Fin.cases singleton_chunk_17024 (Fin.cases singleton_chunk_17152 (Fin.cases singleton_chunk_17280 (Fin.cases singleton_chunk_17408 (Fin.cases singleton_chunk_17536 (Fin.cases singleton_chunk_17664 (Fin.cases singleton_chunk_17792 (Fin.cases singleton_chunk_17920 (Fin.cases singleton_chunk_18048 (Fin.cases singleton_chunk_18176 (Fin.cases singleton_chunk_18304 (Fin.cases singleton_chunk_18432 (Fin.cases singleton_chunk_18560 (Fin.cases singleton_chunk_18688 (Fin.cases singleton_chunk_18816 (Fin.cases singleton_chunk_18944 (Fin.cases singleton_chunk_19072 (Fin.cases singleton_chunk_19200 (Fin.cases singleton_chunk_19328 (Fin.cases singleton_chunk_19456 (Fin.cases singleton_chunk_19584 (Fin.cases singleton_chunk_19712 (Fin.cases singleton_chunk_19840 (fun b : Fin 0 => Fin.elim0 b)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem singleton_ordering (index : Fin singletonSize) :
    checkOrderedAt singletonNodes singletonLevel index = true := by
  let b : Fin 156 := ⟨index.val / 128, by have hi : index.val < 19951 := index.isLt; omega⟩
  let k : Fin (singletonChunkLength b) := ⟨index.val % 128, by
    have hi : index.val < 19951 := index.isLt
    dsimp [singletonChunkLength, b]
    omega⟩
  have same : singletonChunkIndex b k = index := by
    apply Fin.ext
    dsimp [singletonChunkIndex, b, k]
    omega
  simpa only [same] using singletonBlocks b k

def singletonDiagram : OrderedDiagram 9 singletonSize :=
  checked_ordered_diagram singletonNodes singletonLevel singleton_ordering

theorem singleton_root_level : singletonLevel singletonRoot = 0 := by
  decide +kernel

#print axioms singleton_ordering
#print axioms singletonDiagram
#print axioms singleton_root_level

end D5.S3.Quantum.Entanglement.EJM.EJMMDDOrdering
