/- Prepared uncompiled complete finite scalar receipts.
Every actual row is compared with the original complete mirror's lower field.
The two domain totals are 41,294 and 8,689; no producer minimum is a premise. -/

import D5.S3.Quantum.Entanglement.EJM.EJMPackedLowerData
import D5.S3.Quantum.Entanglement.EJM.EJMTriangleCacheData
import D5.S3.Quantum.Entanglement.EJM.EJMSingletonCacheData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option trace.profiler true
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMPackedLowerReceipts
open EJMPackedLowerData

private theorem triangle_0 : ∀ k : Fin 128, triangleLower ⟨0 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨0 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_128 : ∀ k : Fin 128, triangleLower ⟨128 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨128 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_256 : ∀ k : Fin 128, triangleLower ⟨256 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨256 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_384 : ∀ k : Fin 128, triangleLower ⟨384 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨384 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_512 : ∀ k : Fin 128, triangleLower ⟨512 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨512 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_640 : ∀ k : Fin 128, triangleLower ⟨640 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨640 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_768 : ∀ k : Fin 128, triangleLower ⟨768 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨768 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_896 : ∀ k : Fin 128, triangleLower ⟨896 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨896 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_1024 : ∀ k : Fin 128, triangleLower ⟨1024 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨1024 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_1152 : ∀ k : Fin 128, triangleLower ⟨1152 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨1152 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_1280 : ∀ k : Fin 128, triangleLower ⟨1280 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨1280 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_1408 : ∀ k : Fin 128, triangleLower ⟨1408 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨1408 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_1536 : ∀ k : Fin 128, triangleLower ⟨1536 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨1536 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_1664 : ∀ k : Fin 128, triangleLower ⟨1664 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨1664 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_1792 : ∀ k : Fin 128, triangleLower ⟨1792 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨1792 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_1920 : ∀ k : Fin 128, triangleLower ⟨1920 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨1920 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_2048 : ∀ k : Fin 128, triangleLower ⟨2048 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨2048 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_2176 : ∀ k : Fin 128, triangleLower ⟨2176 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨2176 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_2304 : ∀ k : Fin 128, triangleLower ⟨2304 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨2304 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_2432 : ∀ k : Fin 128, triangleLower ⟨2432 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨2432 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_2560 : ∀ k : Fin 128, triangleLower ⟨2560 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨2560 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_2688 : ∀ k : Fin 128, triangleLower ⟨2688 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨2688 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_2816 : ∀ k : Fin 128, triangleLower ⟨2816 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨2816 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_2944 : ∀ k : Fin 128, triangleLower ⟨2944 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨2944 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_3072 : ∀ k : Fin 128, triangleLower ⟨3072 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨3072 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_3200 : ∀ k : Fin 128, triangleLower ⟨3200 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨3200 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_3328 : ∀ k : Fin 128, triangleLower ⟨3328 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨3328 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_3456 : ∀ k : Fin 128, triangleLower ⟨3456 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨3456 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_3584 : ∀ k : Fin 128, triangleLower ⟨3584 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨3584 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_3712 : ∀ k : Fin 128, triangleLower ⟨3712 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨3712 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_3840 : ∀ k : Fin 128, triangleLower ⟨3840 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨3840 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_3968 : ∀ k : Fin 128, triangleLower ⟨3968 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨3968 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_4096 : ∀ k : Fin 128, triangleLower ⟨4096 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨4096 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_4224 : ∀ k : Fin 128, triangleLower ⟨4224 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨4224 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_4352 : ∀ k : Fin 128, triangleLower ⟨4352 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨4352 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_4480 : ∀ k : Fin 128, triangleLower ⟨4480 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨4480 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_4608 : ∀ k : Fin 128, triangleLower ⟨4608 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨4608 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_4736 : ∀ k : Fin 128, triangleLower ⟨4736 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨4736 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_4864 : ∀ k : Fin 128, triangleLower ⟨4864 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨4864 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_4992 : ∀ k : Fin 128, triangleLower ⟨4992 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨4992 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_5120 : ∀ k : Fin 128, triangleLower ⟨5120 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨5120 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_5248 : ∀ k : Fin 128, triangleLower ⟨5248 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨5248 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_5376 : ∀ k : Fin 128, triangleLower ⟨5376 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨5376 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_5504 : ∀ k : Fin 128, triangleLower ⟨5504 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨5504 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_5632 : ∀ k : Fin 128, triangleLower ⟨5632 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨5632 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_5760 : ∀ k : Fin 128, triangleLower ⟨5760 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨5760 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_5888 : ∀ k : Fin 128, triangleLower ⟨5888 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨5888 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_6016 : ∀ k : Fin 128, triangleLower ⟨6016 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨6016 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_6144 : ∀ k : Fin 128, triangleLower ⟨6144 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨6144 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_6272 : ∀ k : Fin 128, triangleLower ⟨6272 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨6272 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_6400 : ∀ k : Fin 128, triangleLower ⟨6400 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨6400 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_6528 : ∀ k : Fin 128, triangleLower ⟨6528 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨6528 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_6656 : ∀ k : Fin 128, triangleLower ⟨6656 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨6656 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_6784 : ∀ k : Fin 128, triangleLower ⟨6784 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨6784 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_6912 : ∀ k : Fin 128, triangleLower ⟨6912 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨6912 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_7040 : ∀ k : Fin 128, triangleLower ⟨7040 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨7040 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_7168 : ∀ k : Fin 128, triangleLower ⟨7168 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨7168 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_7296 : ∀ k : Fin 128, triangleLower ⟨7296 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨7296 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_7424 : ∀ k : Fin 128, triangleLower ⟨7424 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨7424 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_7552 : ∀ k : Fin 128, triangleLower ⟨7552 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨7552 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_7680 : ∀ k : Fin 128, triangleLower ⟨7680 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨7680 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_7808 : ∀ k : Fin 128, triangleLower ⟨7808 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨7808 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_7936 : ∀ k : Fin 128, triangleLower ⟨7936 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨7936 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_8064 : ∀ k : Fin 128, triangleLower ⟨8064 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨8064 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_8192 : ∀ k : Fin 128, triangleLower ⟨8192 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨8192 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_8320 : ∀ k : Fin 128, triangleLower ⟨8320 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨8320 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_8448 : ∀ k : Fin 128, triangleLower ⟨8448 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨8448 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_8576 : ∀ k : Fin 128, triangleLower ⟨8576 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨8576 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_8704 : ∀ k : Fin 128, triangleLower ⟨8704 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨8704 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_8832 : ∀ k : Fin 128, triangleLower ⟨8832 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨8832 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_8960 : ∀ k : Fin 128, triangleLower ⟨8960 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨8960 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_9088 : ∀ k : Fin 128, triangleLower ⟨9088 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨9088 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_9216 : ∀ k : Fin 128, triangleLower ⟨9216 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨9216 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_9344 : ∀ k : Fin 128, triangleLower ⟨9344 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨9344 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_9472 : ∀ k : Fin 128, triangleLower ⟨9472 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨9472 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_9600 : ∀ k : Fin 128, triangleLower ⟨9600 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨9600 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_9728 : ∀ k : Fin 128, triangleLower ⟨9728 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨9728 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_9856 : ∀ k : Fin 128, triangleLower ⟨9856 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨9856 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_9984 : ∀ k : Fin 128, triangleLower ⟨9984 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨9984 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_10112 : ∀ k : Fin 128, triangleLower ⟨10112 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨10112 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_10240 : ∀ k : Fin 128, triangleLower ⟨10240 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨10240 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_10368 : ∀ k : Fin 128, triangleLower ⟨10368 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨10368 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_10496 : ∀ k : Fin 128, triangleLower ⟨10496 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨10496 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_10624 : ∀ k : Fin 128, triangleLower ⟨10624 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨10624 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_10752 : ∀ k : Fin 128, triangleLower ⟨10752 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨10752 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_10880 : ∀ k : Fin 128, triangleLower ⟨10880 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨10880 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_11008 : ∀ k : Fin 128, triangleLower ⟨11008 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨11008 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_11136 : ∀ k : Fin 128, triangleLower ⟨11136 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨11136 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_11264 : ∀ k : Fin 128, triangleLower ⟨11264 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨11264 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_11392 : ∀ k : Fin 128, triangleLower ⟨11392 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨11392 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_11520 : ∀ k : Fin 128, triangleLower ⟨11520 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨11520 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_11648 : ∀ k : Fin 128, triangleLower ⟨11648 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨11648 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_11776 : ∀ k : Fin 128, triangleLower ⟨11776 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨11776 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_11904 : ∀ k : Fin 128, triangleLower ⟨11904 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨11904 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_12032 : ∀ k : Fin 128, triangleLower ⟨12032 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨12032 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_12160 : ∀ k : Fin 128, triangleLower ⟨12160 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨12160 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_12288 : ∀ k : Fin 128, triangleLower ⟨12288 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨12288 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_12416 : ∀ k : Fin 128, triangleLower ⟨12416 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨12416 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_12544 : ∀ k : Fin 128, triangleLower ⟨12544 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨12544 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_12672 : ∀ k : Fin 128, triangleLower ⟨12672 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨12672 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_12800 : ∀ k : Fin 128, triangleLower ⟨12800 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨12800 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_12928 : ∀ k : Fin 128, triangleLower ⟨12928 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨12928 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_13056 : ∀ k : Fin 128, triangleLower ⟨13056 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨13056 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_13184 : ∀ k : Fin 128, triangleLower ⟨13184 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨13184 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_13312 : ∀ k : Fin 128, triangleLower ⟨13312 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨13312 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_13440 : ∀ k : Fin 128, triangleLower ⟨13440 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨13440 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_13568 : ∀ k : Fin 128, triangleLower ⟨13568 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨13568 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_13696 : ∀ k : Fin 128, triangleLower ⟨13696 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨13696 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_13824 : ∀ k : Fin 128, triangleLower ⟨13824 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨13824 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_13952 : ∀ k : Fin 128, triangleLower ⟨13952 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨13952 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_14080 : ∀ k : Fin 128, triangleLower ⟨14080 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨14080 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_14208 : ∀ k : Fin 128, triangleLower ⟨14208 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨14208 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_14336 : ∀ k : Fin 128, triangleLower ⟨14336 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨14336 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_14464 : ∀ k : Fin 128, triangleLower ⟨14464 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨14464 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_14592 : ∀ k : Fin 128, triangleLower ⟨14592 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨14592 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_14720 : ∀ k : Fin 128, triangleLower ⟨14720 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨14720 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_14848 : ∀ k : Fin 128, triangleLower ⟨14848 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨14848 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_14976 : ∀ k : Fin 128, triangleLower ⟨14976 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨14976 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_15104 : ∀ k : Fin 128, triangleLower ⟨15104 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨15104 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_15232 : ∀ k : Fin 128, triangleLower ⟨15232 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨15232 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_15360 : ∀ k : Fin 128, triangleLower ⟨15360 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨15360 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_15488 : ∀ k : Fin 128, triangleLower ⟨15488 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨15488 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_15616 : ∀ k : Fin 128, triangleLower ⟨15616 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨15616 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_15744 : ∀ k : Fin 128, triangleLower ⟨15744 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨15744 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_15872 : ∀ k : Fin 128, triangleLower ⟨15872 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨15872 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_16000 : ∀ k : Fin 128, triangleLower ⟨16000 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨16000 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_16128 : ∀ k : Fin 128, triangleLower ⟨16128 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨16128 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_16256 : ∀ k : Fin 128, triangleLower ⟨16256 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨16256 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_16384 : ∀ k : Fin 128, triangleLower ⟨16384 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨16384 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_16512 : ∀ k : Fin 128, triangleLower ⟨16512 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨16512 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_16640 : ∀ k : Fin 128, triangleLower ⟨16640 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨16640 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_16768 : ∀ k : Fin 128, triangleLower ⟨16768 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨16768 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_16896 : ∀ k : Fin 128, triangleLower ⟨16896 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨16896 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_17024 : ∀ k : Fin 128, triangleLower ⟨17024 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨17024 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_17152 : ∀ k : Fin 128, triangleLower ⟨17152 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨17152 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_17280 : ∀ k : Fin 128, triangleLower ⟨17280 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨17280 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_17408 : ∀ k : Fin 128, triangleLower ⟨17408 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨17408 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_17536 : ∀ k : Fin 128, triangleLower ⟨17536 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨17536 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_17664 : ∀ k : Fin 128, triangleLower ⟨17664 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨17664 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_17792 : ∀ k : Fin 128, triangleLower ⟨17792 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨17792 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_17920 : ∀ k : Fin 128, triangleLower ⟨17920 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨17920 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_18048 : ∀ k : Fin 128, triangleLower ⟨18048 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨18048 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_18176 : ∀ k : Fin 128, triangleLower ⟨18176 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨18176 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_18304 : ∀ k : Fin 128, triangleLower ⟨18304 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨18304 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_18432 : ∀ k : Fin 128, triangleLower ⟨18432 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨18432 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_18560 : ∀ k : Fin 128, triangleLower ⟨18560 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨18560 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_18688 : ∀ k : Fin 128, triangleLower ⟨18688 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨18688 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_18816 : ∀ k : Fin 128, triangleLower ⟨18816 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨18816 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_18944 : ∀ k : Fin 128, triangleLower ⟨18944 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨18944 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_19072 : ∀ k : Fin 128, triangleLower ⟨19072 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨19072 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_19200 : ∀ k : Fin 128, triangleLower ⟨19200 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨19200 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_19328 : ∀ k : Fin 128, triangleLower ⟨19328 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨19328 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_19456 : ∀ k : Fin 128, triangleLower ⟨19456 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨19456 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_19584 : ∀ k : Fin 128, triangleLower ⟨19584 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨19584 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_19712 : ∀ k : Fin 128, triangleLower ⟨19712 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨19712 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_19840 : ∀ k : Fin 128, triangleLower ⟨19840 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨19840 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_19968 : ∀ k : Fin 128, triangleLower ⟨19968 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨19968 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_20096 : ∀ k : Fin 128, triangleLower ⟨20096 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨20096 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_20224 : ∀ k : Fin 128, triangleLower ⟨20224 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨20224 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_20352 : ∀ k : Fin 128, triangleLower ⟨20352 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨20352 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_20480 : ∀ k : Fin 128, triangleLower ⟨20480 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨20480 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_20608 : ∀ k : Fin 128, triangleLower ⟨20608 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨20608 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_20736 : ∀ k : Fin 128, triangleLower ⟨20736 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨20736 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_20864 : ∀ k : Fin 128, triangleLower ⟨20864 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨20864 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_20992 : ∀ k : Fin 128, triangleLower ⟨20992 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨20992 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_21120 : ∀ k : Fin 128, triangleLower ⟨21120 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨21120 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_21248 : ∀ k : Fin 128, triangleLower ⟨21248 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨21248 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_21376 : ∀ k : Fin 128, triangleLower ⟨21376 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨21376 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_21504 : ∀ k : Fin 128, triangleLower ⟨21504 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨21504 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_21632 : ∀ k : Fin 128, triangleLower ⟨21632 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨21632 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_21760 : ∀ k : Fin 128, triangleLower ⟨21760 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨21760 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_21888 : ∀ k : Fin 128, triangleLower ⟨21888 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨21888 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_22016 : ∀ k : Fin 128, triangleLower ⟨22016 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨22016 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_22144 : ∀ k : Fin 128, triangleLower ⟨22144 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨22144 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_22272 : ∀ k : Fin 128, triangleLower ⟨22272 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨22272 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_22400 : ∀ k : Fin 128, triangleLower ⟨22400 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨22400 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_22528 : ∀ k : Fin 128, triangleLower ⟨22528 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨22528 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_22656 : ∀ k : Fin 128, triangleLower ⟨22656 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨22656 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_22784 : ∀ k : Fin 128, triangleLower ⟨22784 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨22784 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_22912 : ∀ k : Fin 128, triangleLower ⟨22912 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨22912 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_23040 : ∀ k : Fin 128, triangleLower ⟨23040 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨23040 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_23168 : ∀ k : Fin 128, triangleLower ⟨23168 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨23168 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_23296 : ∀ k : Fin 128, triangleLower ⟨23296 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨23296 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_23424 : ∀ k : Fin 128, triangleLower ⟨23424 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨23424 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_23552 : ∀ k : Fin 128, triangleLower ⟨23552 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨23552 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_23680 : ∀ k : Fin 128, triangleLower ⟨23680 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨23680 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_23808 : ∀ k : Fin 128, triangleLower ⟨23808 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨23808 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_23936 : ∀ k : Fin 128, triangleLower ⟨23936 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨23936 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_24064 : ∀ k : Fin 128, triangleLower ⟨24064 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨24064 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_24192 : ∀ k : Fin 128, triangleLower ⟨24192 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨24192 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_24320 : ∀ k : Fin 128, triangleLower ⟨24320 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨24320 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_24448 : ∀ k : Fin 128, triangleLower ⟨24448 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨24448 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_24576 : ∀ k : Fin 128, triangleLower ⟨24576 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨24576 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_24704 : ∀ k : Fin 128, triangleLower ⟨24704 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨24704 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_24832 : ∀ k : Fin 128, triangleLower ⟨24832 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨24832 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_24960 : ∀ k : Fin 128, triangleLower ⟨24960 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨24960 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_25088 : ∀ k : Fin 128, triangleLower ⟨25088 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨25088 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_25216 : ∀ k : Fin 128, triangleLower ⟨25216 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨25216 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_25344 : ∀ k : Fin 128, triangleLower ⟨25344 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨25344 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_25472 : ∀ k : Fin 128, triangleLower ⟨25472 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨25472 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_25600 : ∀ k : Fin 128, triangleLower ⟨25600 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨25600 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_25728 : ∀ k : Fin 128, triangleLower ⟨25728 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨25728 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_25856 : ∀ k : Fin 128, triangleLower ⟨25856 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨25856 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_25984 : ∀ k : Fin 128, triangleLower ⟨25984 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨25984 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_26112 : ∀ k : Fin 128, triangleLower ⟨26112 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨26112 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_26240 : ∀ k : Fin 128, triangleLower ⟨26240 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨26240 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_26368 : ∀ k : Fin 128, triangleLower ⟨26368 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨26368 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_26496 : ∀ k : Fin 128, triangleLower ⟨26496 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨26496 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_26624 : ∀ k : Fin 128, triangleLower ⟨26624 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨26624 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_26752 : ∀ k : Fin 128, triangleLower ⟨26752 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨26752 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_26880 : ∀ k : Fin 128, triangleLower ⟨26880 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨26880 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_27008 : ∀ k : Fin 128, triangleLower ⟨27008 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨27008 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_27136 : ∀ k : Fin 128, triangleLower ⟨27136 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨27136 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_27264 : ∀ k : Fin 128, triangleLower ⟨27264 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨27264 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_27392 : ∀ k : Fin 128, triangleLower ⟨27392 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨27392 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_27520 : ∀ k : Fin 128, triangleLower ⟨27520 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨27520 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_27648 : ∀ k : Fin 128, triangleLower ⟨27648 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨27648 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_27776 : ∀ k : Fin 128, triangleLower ⟨27776 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨27776 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_27904 : ∀ k : Fin 128, triangleLower ⟨27904 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨27904 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_28032 : ∀ k : Fin 128, triangleLower ⟨28032 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨28032 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_28160 : ∀ k : Fin 128, triangleLower ⟨28160 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨28160 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_28288 : ∀ k : Fin 128, triangleLower ⟨28288 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨28288 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_28416 : ∀ k : Fin 128, triangleLower ⟨28416 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨28416 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_28544 : ∀ k : Fin 128, triangleLower ⟨28544 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨28544 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_28672 : ∀ k : Fin 128, triangleLower ⟨28672 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨28672 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_28800 : ∀ k : Fin 128, triangleLower ⟨28800 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨28800 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_28928 : ∀ k : Fin 128, triangleLower ⟨28928 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨28928 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_29056 : ∀ k : Fin 128, triangleLower ⟨29056 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨29056 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_29184 : ∀ k : Fin 128, triangleLower ⟨29184 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨29184 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_29312 : ∀ k : Fin 128, triangleLower ⟨29312 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨29312 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_29440 : ∀ k : Fin 128, triangleLower ⟨29440 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨29440 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_29568 : ∀ k : Fin 128, triangleLower ⟨29568 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨29568 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_29696 : ∀ k : Fin 128, triangleLower ⟨29696 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨29696 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_29824 : ∀ k : Fin 128, triangleLower ⟨29824 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨29824 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_29952 : ∀ k : Fin 128, triangleLower ⟨29952 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨29952 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_30080 : ∀ k : Fin 128, triangleLower ⟨30080 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨30080 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_30208 : ∀ k : Fin 128, triangleLower ⟨30208 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨30208 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_30336 : ∀ k : Fin 128, triangleLower ⟨30336 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨30336 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_30464 : ∀ k : Fin 128, triangleLower ⟨30464 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨30464 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_30592 : ∀ k : Fin 128, triangleLower ⟨30592 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨30592 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_30720 : ∀ k : Fin 128, triangleLower ⟨30720 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨30720 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_30848 : ∀ k : Fin 128, triangleLower ⟨30848 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨30848 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_30976 : ∀ k : Fin 128, triangleLower ⟨30976 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨30976 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_31104 : ∀ k : Fin 128, triangleLower ⟨31104 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨31104 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_31232 : ∀ k : Fin 128, triangleLower ⟨31232 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨31232 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_31360 : ∀ k : Fin 128, triangleLower ⟨31360 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨31360 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_31488 : ∀ k : Fin 128, triangleLower ⟨31488 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨31488 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_31616 : ∀ k : Fin 128, triangleLower ⟨31616 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨31616 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_31744 : ∀ k : Fin 128, triangleLower ⟨31744 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨31744 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_31872 : ∀ k : Fin 128, triangleLower ⟨31872 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨31872 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_32000 : ∀ k : Fin 128, triangleLower ⟨32000 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨32000 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_32128 : ∀ k : Fin 128, triangleLower ⟨32128 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨32128 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_32256 : ∀ k : Fin 128, triangleLower ⟨32256 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨32256 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_32384 : ∀ k : Fin 128, triangleLower ⟨32384 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨32384 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_32512 : ∀ k : Fin 128, triangleLower ⟨32512 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨32512 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_32640 : ∀ k : Fin 128, triangleLower ⟨32640 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨32640 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_32768 : ∀ k : Fin 128, triangleLower ⟨32768 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨32768 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_32896 : ∀ k : Fin 128, triangleLower ⟨32896 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨32896 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_33024 : ∀ k : Fin 128, triangleLower ⟨33024 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨33024 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_33152 : ∀ k : Fin 128, triangleLower ⟨33152 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨33152 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_33280 : ∀ k : Fin 128, triangleLower ⟨33280 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨33280 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_33408 : ∀ k : Fin 128, triangleLower ⟨33408 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨33408 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_33536 : ∀ k : Fin 128, triangleLower ⟨33536 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨33536 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_33664 : ∀ k : Fin 128, triangleLower ⟨33664 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨33664 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_33792 : ∀ k : Fin 128, triangleLower ⟨33792 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨33792 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_33920 : ∀ k : Fin 128, triangleLower ⟨33920 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨33920 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_34048 : ∀ k : Fin 128, triangleLower ⟨34048 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨34048 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_34176 : ∀ k : Fin 128, triangleLower ⟨34176 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨34176 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_34304 : ∀ k : Fin 128, triangleLower ⟨34304 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨34304 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_34432 : ∀ k : Fin 128, triangleLower ⟨34432 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨34432 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_34560 : ∀ k : Fin 128, triangleLower ⟨34560 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨34560 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_34688 : ∀ k : Fin 128, triangleLower ⟨34688 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨34688 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_34816 : ∀ k : Fin 128, triangleLower ⟨34816 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨34816 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_34944 : ∀ k : Fin 128, triangleLower ⟨34944 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨34944 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_35072 : ∀ k : Fin 128, triangleLower ⟨35072 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨35072 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_35200 : ∀ k : Fin 128, triangleLower ⟨35200 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨35200 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_35328 : ∀ k : Fin 128, triangleLower ⟨35328 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨35328 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_35456 : ∀ k : Fin 128, triangleLower ⟨35456 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨35456 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_35584 : ∀ k : Fin 128, triangleLower ⟨35584 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨35584 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_35712 : ∀ k : Fin 128, triangleLower ⟨35712 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨35712 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_35840 : ∀ k : Fin 128, triangleLower ⟨35840 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨35840 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_35968 : ∀ k : Fin 128, triangleLower ⟨35968 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨35968 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_36096 : ∀ k : Fin 128, triangleLower ⟨36096 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨36096 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_36224 : ∀ k : Fin 128, triangleLower ⟨36224 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨36224 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_36352 : ∀ k : Fin 128, triangleLower ⟨36352 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨36352 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_36480 : ∀ k : Fin 128, triangleLower ⟨36480 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨36480 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_36608 : ∀ k : Fin 128, triangleLower ⟨36608 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨36608 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_36736 : ∀ k : Fin 128, triangleLower ⟨36736 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨36736 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_36864 : ∀ k : Fin 128, triangleLower ⟨36864 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨36864 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_36992 : ∀ k : Fin 128, triangleLower ⟨36992 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨36992 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_37120 : ∀ k : Fin 128, triangleLower ⟨37120 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨37120 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_37248 : ∀ k : Fin 128, triangleLower ⟨37248 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨37248 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_37376 : ∀ k : Fin 128, triangleLower ⟨37376 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨37376 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_37504 : ∀ k : Fin 128, triangleLower ⟨37504 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨37504 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_37632 : ∀ k : Fin 128, triangleLower ⟨37632 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨37632 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_37760 : ∀ k : Fin 128, triangleLower ⟨37760 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨37760 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_37888 : ∀ k : Fin 128, triangleLower ⟨37888 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨37888 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_38016 : ∀ k : Fin 128, triangleLower ⟨38016 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨38016 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_38144 : ∀ k : Fin 128, triangleLower ⟨38144 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨38144 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_38272 : ∀ k : Fin 128, triangleLower ⟨38272 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨38272 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_38400 : ∀ k : Fin 128, triangleLower ⟨38400 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨38400 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_38528 : ∀ k : Fin 128, triangleLower ⟨38528 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨38528 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_38656 : ∀ k : Fin 128, triangleLower ⟨38656 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨38656 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_38784 : ∀ k : Fin 128, triangleLower ⟨38784 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨38784 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_38912 : ∀ k : Fin 128, triangleLower ⟨38912 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨38912 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_39040 : ∀ k : Fin 128, triangleLower ⟨39040 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨39040 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_39168 : ∀ k : Fin 128, triangleLower ⟨39168 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨39168 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_39296 : ∀ k : Fin 128, triangleLower ⟨39296 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨39296 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_39424 : ∀ k : Fin 128, triangleLower ⟨39424 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨39424 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_39552 : ∀ k : Fin 128, triangleLower ⟨39552 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨39552 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_39680 : ∀ k : Fin 128, triangleLower ⟨39680 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨39680 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_39808 : ∀ k : Fin 128, triangleLower ⟨39808 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨39808 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_39936 : ∀ k : Fin 128, triangleLower ⟨39936 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨39936 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_40064 : ∀ k : Fin 128, triangleLower ⟨40064 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨40064 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_40192 : ∀ k : Fin 128, triangleLower ⟨40192 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨40192 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_40320 : ∀ k : Fin 128, triangleLower ⟨40320 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨40320 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_40448 : ∀ k : Fin 128, triangleLower ⟨40448 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨40448 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_40576 : ∀ k : Fin 128, triangleLower ⟨40576 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨40576 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_40704 : ∀ k : Fin 128, triangleLower ⟨40704 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨40704 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_40832 : ∀ k : Fin 128, triangleLower ⟨40832 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨40832 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_40960 : ∀ k : Fin 128, triangleLower ⟨40960 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨40960 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_41088 : ∀ k : Fin 128, triangleLower ⟨41088 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨41088 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem triangle_41216 : ∀ k : Fin 78, triangleLower ⟨41216 + k.val, by have hk := k.isLt; omega⟩ = (EJMTriangleCacheData.mirror ⟨41216 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel

private def triangleLength (b : Fin 323) : ℕ := min 128 (41294 - 128 * b.val)
private def triangleIndex (b : Fin 323) (k : Fin (triangleLength b)) : Fin 41294 :=
  ⟨128 * b.val + k.val, by
    have hb := b.isLt
    have hk := k.isLt
    dsimp [triangleLength] at hk
    omega⟩

private theorem triangle_blocks : ∀ b : Fin 323, ∀ k : Fin (triangleLength b),
    triangleLower (triangleIndex b k) = (EJMTriangleCacheData.mirror (triangleIndex b k)).lower :=
  Fin.cases triangle_0 (Fin.cases triangle_128 (Fin.cases triangle_256 (Fin.cases triangle_384 (Fin.cases triangle_512 (Fin.cases triangle_640 (Fin.cases triangle_768 (Fin.cases triangle_896 (Fin.cases triangle_1024 (Fin.cases triangle_1152 (Fin.cases triangle_1280 (Fin.cases triangle_1408 (Fin.cases triangle_1536 (Fin.cases triangle_1664 (Fin.cases triangle_1792 (Fin.cases triangle_1920 (
  Fin.cases triangle_2048 (Fin.cases triangle_2176 (Fin.cases triangle_2304 (Fin.cases triangle_2432 (Fin.cases triangle_2560 (Fin.cases triangle_2688 (Fin.cases triangle_2816 (Fin.cases triangle_2944 (Fin.cases triangle_3072 (Fin.cases triangle_3200 (Fin.cases triangle_3328 (Fin.cases triangle_3456 (Fin.cases triangle_3584 (Fin.cases triangle_3712 (Fin.cases triangle_3840 (Fin.cases triangle_3968 (
  Fin.cases triangle_4096 (Fin.cases triangle_4224 (Fin.cases triangle_4352 (Fin.cases triangle_4480 (Fin.cases triangle_4608 (Fin.cases triangle_4736 (Fin.cases triangle_4864 (Fin.cases triangle_4992 (Fin.cases triangle_5120 (Fin.cases triangle_5248 (Fin.cases triangle_5376 (Fin.cases triangle_5504 (Fin.cases triangle_5632 (Fin.cases triangle_5760 (Fin.cases triangle_5888 (Fin.cases triangle_6016 (
  Fin.cases triangle_6144 (Fin.cases triangle_6272 (Fin.cases triangle_6400 (Fin.cases triangle_6528 (Fin.cases triangle_6656 (Fin.cases triangle_6784 (Fin.cases triangle_6912 (Fin.cases triangle_7040 (Fin.cases triangle_7168 (Fin.cases triangle_7296 (Fin.cases triangle_7424 (Fin.cases triangle_7552 (Fin.cases triangle_7680 (Fin.cases triangle_7808 (Fin.cases triangle_7936 (Fin.cases triangle_8064 (
  Fin.cases triangle_8192 (Fin.cases triangle_8320 (Fin.cases triangle_8448 (Fin.cases triangle_8576 (Fin.cases triangle_8704 (Fin.cases triangle_8832 (Fin.cases triangle_8960 (Fin.cases triangle_9088 (Fin.cases triangle_9216 (Fin.cases triangle_9344 (Fin.cases triangle_9472 (Fin.cases triangle_9600 (Fin.cases triangle_9728 (Fin.cases triangle_9856 (Fin.cases triangle_9984 (Fin.cases triangle_10112 (
  Fin.cases triangle_10240 (Fin.cases triangle_10368 (Fin.cases triangle_10496 (Fin.cases triangle_10624 (Fin.cases triangle_10752 (Fin.cases triangle_10880 (Fin.cases triangle_11008 (Fin.cases triangle_11136 (Fin.cases triangle_11264 (Fin.cases triangle_11392 (Fin.cases triangle_11520 (Fin.cases triangle_11648 (Fin.cases triangle_11776 (Fin.cases triangle_11904 (Fin.cases triangle_12032 (Fin.cases triangle_12160 (
  Fin.cases triangle_12288 (Fin.cases triangle_12416 (Fin.cases triangle_12544 (Fin.cases triangle_12672 (Fin.cases triangle_12800 (Fin.cases triangle_12928 (Fin.cases triangle_13056 (Fin.cases triangle_13184 (Fin.cases triangle_13312 (Fin.cases triangle_13440 (Fin.cases triangle_13568 (Fin.cases triangle_13696 (Fin.cases triangle_13824 (Fin.cases triangle_13952 (Fin.cases triangle_14080 (Fin.cases triangle_14208 (
  Fin.cases triangle_14336 (Fin.cases triangle_14464 (Fin.cases triangle_14592 (Fin.cases triangle_14720 (Fin.cases triangle_14848 (Fin.cases triangle_14976 (Fin.cases triangle_15104 (Fin.cases triangle_15232 (Fin.cases triangle_15360 (Fin.cases triangle_15488 (Fin.cases triangle_15616 (Fin.cases triangle_15744 (Fin.cases triangle_15872 (Fin.cases triangle_16000 (Fin.cases triangle_16128 (Fin.cases triangle_16256 (
  Fin.cases triangle_16384 (Fin.cases triangle_16512 (Fin.cases triangle_16640 (Fin.cases triangle_16768 (Fin.cases triangle_16896 (Fin.cases triangle_17024 (Fin.cases triangle_17152 (Fin.cases triangle_17280 (Fin.cases triangle_17408 (Fin.cases triangle_17536 (Fin.cases triangle_17664 (Fin.cases triangle_17792 (Fin.cases triangle_17920 (Fin.cases triangle_18048 (Fin.cases triangle_18176 (Fin.cases triangle_18304 (
  Fin.cases triangle_18432 (Fin.cases triangle_18560 (Fin.cases triangle_18688 (Fin.cases triangle_18816 (Fin.cases triangle_18944 (Fin.cases triangle_19072 (Fin.cases triangle_19200 (Fin.cases triangle_19328 (Fin.cases triangle_19456 (Fin.cases triangle_19584 (Fin.cases triangle_19712 (Fin.cases triangle_19840 (Fin.cases triangle_19968 (Fin.cases triangle_20096 (Fin.cases triangle_20224 (Fin.cases triangle_20352 (
  Fin.cases triangle_20480 (Fin.cases triangle_20608 (Fin.cases triangle_20736 (Fin.cases triangle_20864 (Fin.cases triangle_20992 (Fin.cases triangle_21120 (Fin.cases triangle_21248 (Fin.cases triangle_21376 (Fin.cases triangle_21504 (Fin.cases triangle_21632 (Fin.cases triangle_21760 (Fin.cases triangle_21888 (Fin.cases triangle_22016 (Fin.cases triangle_22144 (Fin.cases triangle_22272 (Fin.cases triangle_22400 (
  Fin.cases triangle_22528 (Fin.cases triangle_22656 (Fin.cases triangle_22784 (Fin.cases triangle_22912 (Fin.cases triangle_23040 (Fin.cases triangle_23168 (Fin.cases triangle_23296 (Fin.cases triangle_23424 (Fin.cases triangle_23552 (Fin.cases triangle_23680 (Fin.cases triangle_23808 (Fin.cases triangle_23936 (Fin.cases triangle_24064 (Fin.cases triangle_24192 (Fin.cases triangle_24320 (Fin.cases triangle_24448 (
  Fin.cases triangle_24576 (Fin.cases triangle_24704 (Fin.cases triangle_24832 (Fin.cases triangle_24960 (Fin.cases triangle_25088 (Fin.cases triangle_25216 (Fin.cases triangle_25344 (Fin.cases triangle_25472 (Fin.cases triangle_25600 (Fin.cases triangle_25728 (Fin.cases triangle_25856 (Fin.cases triangle_25984 (Fin.cases triangle_26112 (Fin.cases triangle_26240 (Fin.cases triangle_26368 (Fin.cases triangle_26496 (
  Fin.cases triangle_26624 (Fin.cases triangle_26752 (Fin.cases triangle_26880 (Fin.cases triangle_27008 (Fin.cases triangle_27136 (Fin.cases triangle_27264 (Fin.cases triangle_27392 (Fin.cases triangle_27520 (Fin.cases triangle_27648 (Fin.cases triangle_27776 (Fin.cases triangle_27904 (Fin.cases triangle_28032 (Fin.cases triangle_28160 (Fin.cases triangle_28288 (Fin.cases triangle_28416 (Fin.cases triangle_28544 (
  Fin.cases triangle_28672 (Fin.cases triangle_28800 (Fin.cases triangle_28928 (Fin.cases triangle_29056 (Fin.cases triangle_29184 (Fin.cases triangle_29312 (Fin.cases triangle_29440 (Fin.cases triangle_29568 (Fin.cases triangle_29696 (Fin.cases triangle_29824 (Fin.cases triangle_29952 (Fin.cases triangle_30080 (Fin.cases triangle_30208 (Fin.cases triangle_30336 (Fin.cases triangle_30464 (Fin.cases triangle_30592 (
  Fin.cases triangle_30720 (Fin.cases triangle_30848 (Fin.cases triangle_30976 (Fin.cases triangle_31104 (Fin.cases triangle_31232 (Fin.cases triangle_31360 (Fin.cases triangle_31488 (Fin.cases triangle_31616 (Fin.cases triangle_31744 (Fin.cases triangle_31872 (Fin.cases triangle_32000 (Fin.cases triangle_32128 (Fin.cases triangle_32256 (Fin.cases triangle_32384 (Fin.cases triangle_32512 (Fin.cases triangle_32640 (
  Fin.cases triangle_32768 (Fin.cases triangle_32896 (Fin.cases triangle_33024 (Fin.cases triangle_33152 (Fin.cases triangle_33280 (Fin.cases triangle_33408 (Fin.cases triangle_33536 (Fin.cases triangle_33664 (Fin.cases triangle_33792 (Fin.cases triangle_33920 (Fin.cases triangle_34048 (Fin.cases triangle_34176 (Fin.cases triangle_34304 (Fin.cases triangle_34432 (Fin.cases triangle_34560 (Fin.cases triangle_34688 (
  Fin.cases triangle_34816 (Fin.cases triangle_34944 (Fin.cases triangle_35072 (Fin.cases triangle_35200 (Fin.cases triangle_35328 (Fin.cases triangle_35456 (Fin.cases triangle_35584 (Fin.cases triangle_35712 (Fin.cases triangle_35840 (Fin.cases triangle_35968 (Fin.cases triangle_36096 (Fin.cases triangle_36224 (Fin.cases triangle_36352 (Fin.cases triangle_36480 (Fin.cases triangle_36608 (Fin.cases triangle_36736 (
  Fin.cases triangle_36864 (Fin.cases triangle_36992 (Fin.cases triangle_37120 (Fin.cases triangle_37248 (Fin.cases triangle_37376 (Fin.cases triangle_37504 (Fin.cases triangle_37632 (Fin.cases triangle_37760 (Fin.cases triangle_37888 (Fin.cases triangle_38016 (Fin.cases triangle_38144 (Fin.cases triangle_38272 (Fin.cases triangle_38400 (Fin.cases triangle_38528 (Fin.cases triangle_38656 (Fin.cases triangle_38784 (
  Fin.cases triangle_38912 (Fin.cases triangle_39040 (Fin.cases triangle_39168 (Fin.cases triangle_39296 (Fin.cases triangle_39424 (Fin.cases triangle_39552 (Fin.cases triangle_39680 (Fin.cases triangle_39808 (Fin.cases triangle_39936 (Fin.cases triangle_40064 (Fin.cases triangle_40192 (Fin.cases triangle_40320 (Fin.cases triangle_40448 (Fin.cases triangle_40576 (Fin.cases triangle_40704 (Fin.cases triangle_40832 (
  Fin.cases triangle_40960 (Fin.cases triangle_41088 (Fin.cases triangle_41216 (
  (fun b : Fin 0 => Fin.elim0 b))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem triangle_eq (j : Fin 41294) :
    triangleLower j = (EJMTriangleCacheData.mirror j).lower := by
  let b : Fin 323 := ⟨j.val / 128, by have hj := j.isLt; omega⟩
  let k : Fin (triangleLength b) := ⟨j.val % 128, by
    have hj := j.isLt
    dsimp [triangleLength, b]
    omega⟩
  have he : triangleIndex b k = j := by
    apply Fin.ext
    dsimp [triangleIndex, b, k]
    omega
  simpa only [he] using triangle_blocks b k

#print axioms triangle_eq

private theorem singleton_0 : ∀ k : Fin 128, singletonLower ⟨0 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨0 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_128 : ∀ k : Fin 128, singletonLower ⟨128 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨128 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_256 : ∀ k : Fin 128, singletonLower ⟨256 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨256 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_384 : ∀ k : Fin 128, singletonLower ⟨384 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨384 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_512 : ∀ k : Fin 128, singletonLower ⟨512 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨512 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_640 : ∀ k : Fin 128, singletonLower ⟨640 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨640 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_768 : ∀ k : Fin 128, singletonLower ⟨768 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨768 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_896 : ∀ k : Fin 128, singletonLower ⟨896 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨896 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_1024 : ∀ k : Fin 128, singletonLower ⟨1024 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨1024 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_1152 : ∀ k : Fin 128, singletonLower ⟨1152 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨1152 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_1280 : ∀ k : Fin 128, singletonLower ⟨1280 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨1280 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_1408 : ∀ k : Fin 128, singletonLower ⟨1408 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨1408 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_1536 : ∀ k : Fin 128, singletonLower ⟨1536 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨1536 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_1664 : ∀ k : Fin 128, singletonLower ⟨1664 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨1664 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_1792 : ∀ k : Fin 128, singletonLower ⟨1792 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨1792 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_1920 : ∀ k : Fin 128, singletonLower ⟨1920 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨1920 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_2048 : ∀ k : Fin 128, singletonLower ⟨2048 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨2048 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_2176 : ∀ k : Fin 128, singletonLower ⟨2176 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨2176 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_2304 : ∀ k : Fin 128, singletonLower ⟨2304 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨2304 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_2432 : ∀ k : Fin 128, singletonLower ⟨2432 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨2432 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_2560 : ∀ k : Fin 128, singletonLower ⟨2560 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨2560 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_2688 : ∀ k : Fin 128, singletonLower ⟨2688 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨2688 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_2816 : ∀ k : Fin 128, singletonLower ⟨2816 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨2816 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_2944 : ∀ k : Fin 128, singletonLower ⟨2944 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨2944 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_3072 : ∀ k : Fin 128, singletonLower ⟨3072 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨3072 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_3200 : ∀ k : Fin 128, singletonLower ⟨3200 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨3200 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_3328 : ∀ k : Fin 128, singletonLower ⟨3328 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨3328 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_3456 : ∀ k : Fin 128, singletonLower ⟨3456 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨3456 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_3584 : ∀ k : Fin 128, singletonLower ⟨3584 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨3584 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_3712 : ∀ k : Fin 128, singletonLower ⟨3712 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨3712 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_3840 : ∀ k : Fin 128, singletonLower ⟨3840 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨3840 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_3968 : ∀ k : Fin 128, singletonLower ⟨3968 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨3968 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_4096 : ∀ k : Fin 128, singletonLower ⟨4096 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨4096 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_4224 : ∀ k : Fin 128, singletonLower ⟨4224 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨4224 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_4352 : ∀ k : Fin 128, singletonLower ⟨4352 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨4352 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_4480 : ∀ k : Fin 128, singletonLower ⟨4480 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨4480 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_4608 : ∀ k : Fin 128, singletonLower ⟨4608 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨4608 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_4736 : ∀ k : Fin 128, singletonLower ⟨4736 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨4736 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_4864 : ∀ k : Fin 128, singletonLower ⟨4864 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨4864 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_4992 : ∀ k : Fin 128, singletonLower ⟨4992 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨4992 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_5120 : ∀ k : Fin 128, singletonLower ⟨5120 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨5120 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_5248 : ∀ k : Fin 128, singletonLower ⟨5248 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨5248 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_5376 : ∀ k : Fin 128, singletonLower ⟨5376 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨5376 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_5504 : ∀ k : Fin 128, singletonLower ⟨5504 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨5504 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_5632 : ∀ k : Fin 128, singletonLower ⟨5632 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨5632 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_5760 : ∀ k : Fin 128, singletonLower ⟨5760 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨5760 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_5888 : ∀ k : Fin 128, singletonLower ⟨5888 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨5888 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_6016 : ∀ k : Fin 128, singletonLower ⟨6016 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨6016 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_6144 : ∀ k : Fin 128, singletonLower ⟨6144 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨6144 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_6272 : ∀ k : Fin 128, singletonLower ⟨6272 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨6272 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_6400 : ∀ k : Fin 128, singletonLower ⟨6400 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨6400 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_6528 : ∀ k : Fin 128, singletonLower ⟨6528 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨6528 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_6656 : ∀ k : Fin 128, singletonLower ⟨6656 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨6656 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_6784 : ∀ k : Fin 128, singletonLower ⟨6784 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨6784 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_6912 : ∀ k : Fin 128, singletonLower ⟨6912 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨6912 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_7040 : ∀ k : Fin 128, singletonLower ⟨7040 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨7040 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_7168 : ∀ k : Fin 128, singletonLower ⟨7168 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨7168 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_7296 : ∀ k : Fin 128, singletonLower ⟨7296 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨7296 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_7424 : ∀ k : Fin 128, singletonLower ⟨7424 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨7424 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_7552 : ∀ k : Fin 128, singletonLower ⟨7552 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨7552 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_7680 : ∀ k : Fin 128, singletonLower ⟨7680 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨7680 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_7808 : ∀ k : Fin 128, singletonLower ⟨7808 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨7808 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_7936 : ∀ k : Fin 128, singletonLower ⟨7936 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨7936 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_8064 : ∀ k : Fin 128, singletonLower ⟨8064 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨8064 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_8192 : ∀ k : Fin 128, singletonLower ⟨8192 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨8192 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_8320 : ∀ k : Fin 128, singletonLower ⟨8320 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨8320 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_8448 : ∀ k : Fin 128, singletonLower ⟨8448 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨8448 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel
private theorem singleton_8576 : ∀ k : Fin 113, singletonLower ⟨8576 + k.val, by have hk := k.isLt; omega⟩ = (EJMSingletonCacheData.mirror ⟨8576 + k.val, by have hk := k.isLt; omega⟩).lower := by decide +kernel

private def singletonLength (b : Fin 68) : ℕ := min 128 (8689 - 128 * b.val)
private def singletonIndex (b : Fin 68) (k : Fin (singletonLength b)) : Fin 8689 :=
  ⟨128 * b.val + k.val, by
    have hb := b.isLt
    have hk := k.isLt
    dsimp [singletonLength] at hk
    omega⟩

private theorem singleton_blocks : ∀ b : Fin 68, ∀ k : Fin (singletonLength b),
    singletonLower (singletonIndex b k) = (EJMSingletonCacheData.mirror (singletonIndex b k)).lower :=
  Fin.cases singleton_0 (Fin.cases singleton_128 (Fin.cases singleton_256 (Fin.cases singleton_384 (Fin.cases singleton_512 (Fin.cases singleton_640 (Fin.cases singleton_768 (Fin.cases singleton_896 (Fin.cases singleton_1024 (Fin.cases singleton_1152 (Fin.cases singleton_1280 (Fin.cases singleton_1408 (Fin.cases singleton_1536 (Fin.cases singleton_1664 (Fin.cases singleton_1792 (Fin.cases singleton_1920 (
  Fin.cases singleton_2048 (Fin.cases singleton_2176 (Fin.cases singleton_2304 (Fin.cases singleton_2432 (Fin.cases singleton_2560 (Fin.cases singleton_2688 (Fin.cases singleton_2816 (Fin.cases singleton_2944 (Fin.cases singleton_3072 (Fin.cases singleton_3200 (Fin.cases singleton_3328 (Fin.cases singleton_3456 (Fin.cases singleton_3584 (Fin.cases singleton_3712 (Fin.cases singleton_3840 (Fin.cases singleton_3968 (
  Fin.cases singleton_4096 (Fin.cases singleton_4224 (Fin.cases singleton_4352 (Fin.cases singleton_4480 (Fin.cases singleton_4608 (Fin.cases singleton_4736 (Fin.cases singleton_4864 (Fin.cases singleton_4992 (Fin.cases singleton_5120 (Fin.cases singleton_5248 (Fin.cases singleton_5376 (Fin.cases singleton_5504 (Fin.cases singleton_5632 (Fin.cases singleton_5760 (Fin.cases singleton_5888 (Fin.cases singleton_6016 (
  Fin.cases singleton_6144 (Fin.cases singleton_6272 (Fin.cases singleton_6400 (Fin.cases singleton_6528 (Fin.cases singleton_6656 (Fin.cases singleton_6784 (Fin.cases singleton_6912 (Fin.cases singleton_7040 (Fin.cases singleton_7168 (Fin.cases singleton_7296 (Fin.cases singleton_7424 (Fin.cases singleton_7552 (Fin.cases singleton_7680 (Fin.cases singleton_7808 (Fin.cases singleton_7936 (Fin.cases singleton_8064 (
  Fin.cases singleton_8192 (Fin.cases singleton_8320 (Fin.cases singleton_8448 (Fin.cases singleton_8576 (
  (fun b : Fin 0 => Fin.elim0 b)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem singleton_eq (j : Fin 8689) :
    singletonLower j = (EJMSingletonCacheData.mirror j).lower := by
  let b : Fin 68 := ⟨j.val / 128, by have hj := j.isLt; omega⟩
  let k : Fin (singletonLength b) := ⟨j.val % 128, by
    have hj := j.isLt
    dsimp [singletonLength, b]
    omega⟩
  have he : singletonIndex b k = j := by
    apply Fin.ext
    dsimp [singletonIndex, b, k]
    omega
  simpa only [he] using singleton_blocks b k

#print axioms singleton_eq

end D5.S3.Quantum.Entanglement.EJM.EJMPackedLowerReceipts
