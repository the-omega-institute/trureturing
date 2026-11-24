/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Groups/Group05
   generality: I
   mirror-B: none(waiver:finite-coverage-helper-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificates)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks05/Block0400.checked0400
   digest: Adjacent checker successes cover a complete interval of odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0400
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0401
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0402
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0403
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0404
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0405
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0406
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0407
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0408
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0409
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0410
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0411
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0412
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0413
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0414
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0415
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0416
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0417
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0418
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0419
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0420
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0421
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0422
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0423
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0424
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0425

set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-! Every slot belongs to one checked block; each branch applies its soundness theorem. -/

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

attribute [local irreducible] checkBlock checkRows checkPrime

/-- Complete prime-root coverage of this consecutive group of checked odd slots. -/
theorem group05_sound :
    ∀ (k : ℕ), k < 103340 → (3276803 + 2 * k).Prime →
      ∃ (q : ℕ), q.Prime ∧ q < 3276803 + 2 * k ∧
        orderOf (q : ZMod (3276803 + 2 * k)) = 3276803 + 2 * k - 1 := by
  intro k hk hp
  by_cases h00 : k < 4096
  · have hindex : k - 0 < 4096 := by omega
    have heq : 3276803 + 2 * (k - 0) = 3276803 + 2 * k := by omega
    have h := checkBlock_sound checked0400 (k - 0) hindex
    rw [heq] at h
    exact h hp
  by_cases h01 : k < 8192
  · have hindex : k - 4096 < 4096 := by omega
    have heq : 3284995 + 2 * (k - 4096) = 3276803 + 2 * k := by omega
    have h := checkBlock_sound checked0401 (k - 4096) hindex
    rw [heq] at h
    exact h hp
  by_cases h02 : k < 12288
  · have hindex : k - 8192 < 4096 := by omega
    have heq : 3293187 + 2 * (k - 8192) = 3276803 + 2 * k := by omega
    have h := checkBlock_sound checked0402 (k - 8192) hindex
    rw [heq] at h
    exact h hp
  by_cases h03 : k < 16384
  · have hindex : k - 12288 < 4096 := by omega
    have heq : 3301379 + 2 * (k - 12288) = 3276803 + 2 * k := by omega
    have h := checkBlock_sound checked0403 (k - 12288) hindex
    rw [heq] at h
    exact h hp
  by_cases h04 : k < 20480
  · have hindex : k - 16384 < 4096 := by omega
    have heq : 3309571 + 2 * (k - 16384) = 3276803 + 2 * k := by omega
    have h := checkBlock_sound checked0404 (k - 16384) hindex
    rw [heq] at h
    exact h hp
  by_cases h05 : k < 24576
  · have hindex : k - 20480 < 4096 := by omega
    have heq : 3317763 + 2 * (k - 20480) = 3276803 + 2 * k := by omega
    have h := checkBlock_sound checked0405 (k - 20480) hindex
    rw [heq] at h
    exact h hp
  by_cases h06 : k < 28672
  · have hindex : k - 24576 < 4096 := by omega
    have heq : 3325955 + 2 * (k - 24576) = 3276803 + 2 * k := by omega
    have h := checkBlock_sound checked0406 (k - 24576) hindex
    rw [heq] at h
    exact h hp
  by_cases h07 : k < 32768
  · have hindex : k - 28672 < 4096 := by omega
    have heq : 3334147 + 2 * (k - 28672) = 3276803 + 2 * k := by omega
    have h := checkBlock_sound checked0407 (k - 28672) hindex
    rw [heq] at h
    exact h hp
  by_cases h08 : k < 36864
  · have hindex : k - 32768 < 4096 := by omega
    have heq : 3342339 + 2 * (k - 32768) = 3276803 + 2 * k := by omega
    have h := checkBlock_sound checked0408 (k - 32768) hindex
    rw [heq] at h
    exact h hp
  by_cases h09 : k < 40960
  · have hindex : k - 36864 < 4096 := by omega
    have heq : 3350531 + 2 * (k - 36864) = 3276803 + 2 * k := by omega
    have h := checkBlock_sound checked0409 (k - 36864) hindex
    rw [heq] at h
    exact h hp
  by_cases h10 : k < 45056
  · have hindex : k - 40960 < 4096 := by omega
    have heq : 3358723 + 2 * (k - 40960) = 3276803 + 2 * k := by omega
    have h := checkBlock_sound checked0410 (k - 40960) hindex
    rw [heq] at h
    exact h hp
  by_cases h11 : k < 49152
  · have hindex : k - 45056 < 4096 := by omega
    have heq : 3366915 + 2 * (k - 45056) = 3276803 + 2 * k := by omega
    have h := checkBlock_sound checked0411 (k - 45056) hindex
    rw [heq] at h
    exact h hp
  by_cases h12 : k < 53248
  · have hindex : k - 49152 < 4096 := by omega
    have heq : 3375107 + 2 * (k - 49152) = 3276803 + 2 * k := by omega
    have h := checkBlock_sound checked0412 (k - 49152) hindex
    rw [heq] at h
    exact h hp
  by_cases h13 : k < 57344
  · have hindex : k - 53248 < 4096 := by omega
    have heq : 3383299 + 2 * (k - 53248) = 3276803 + 2 * k := by omega
    have h := checkBlock_sound checked0413 (k - 53248) hindex
    rw [heq] at h
    exact h hp
  by_cases h14 : k < 61440
  · have hindex : k - 57344 < 4096 := by omega
    have heq : 3391491 + 2 * (k - 57344) = 3276803 + 2 * k := by omega
    have h := checkBlock_sound checked0414 (k - 57344) hindex
    rw [heq] at h
    exact h hp
  by_cases h15 : k < 65536
  · have hindex : k - 61440 < 4096 := by omega
    have heq : 3399683 + 2 * (k - 61440) = 3276803 + 2 * k := by omega
    have h := checkBlock_sound checked0415 (k - 61440) hindex
    rw [heq] at h
    exact h hp
  by_cases h16 : k < 69632
  · have hindex : k - 65536 < 4096 := by omega
    have heq : 3407875 + 2 * (k - 65536) = 3276803 + 2 * k := by omega
    have h := checkBlock_sound checked0416 (k - 65536) hindex
    rw [heq] at h
    exact h hp
  by_cases h17 : k < 73728
  · have hindex : k - 69632 < 4096 := by omega
    have heq : 3416067 + 2 * (k - 69632) = 3276803 + 2 * k := by omega
    have h := checkBlock_sound checked0417 (k - 69632) hindex
    rw [heq] at h
    exact h hp
  by_cases h18 : k < 77824
  · have hindex : k - 73728 < 4096 := by omega
    have heq : 3424259 + 2 * (k - 73728) = 3276803 + 2 * k := by omega
    have h := checkBlock_sound checked0418 (k - 73728) hindex
    rw [heq] at h
    exact h hp
  by_cases h19 : k < 81920
  · have hindex : k - 77824 < 4096 := by omega
    have heq : 3432451 + 2 * (k - 77824) = 3276803 + 2 * k := by omega
    have h := checkBlock_sound checked0419 (k - 77824) hindex
    rw [heq] at h
    exact h hp
  by_cases h20 : k < 86016
  · have hindex : k - 81920 < 4096 := by omega
    have heq : 3440643 + 2 * (k - 81920) = 3276803 + 2 * k := by omega
    have h := checkBlock_sound checked0420 (k - 81920) hindex
    rw [heq] at h
    exact h hp
  by_cases h21 : k < 90112
  · have hindex : k - 86016 < 4096 := by omega
    have heq : 3448835 + 2 * (k - 86016) = 3276803 + 2 * k := by omega
    have h := checkBlock_sound checked0421 (k - 86016) hindex
    rw [heq] at h
    exact h hp
  by_cases h22 : k < 94208
  · have hindex : k - 90112 < 4096 := by omega
    have heq : 3457027 + 2 * (k - 90112) = 3276803 + 2 * k := by omega
    have h := checkBlock_sound checked0422 (k - 90112) hindex
    rw [heq] at h
    exact h hp
  by_cases h23 : k < 98304
  · have hindex : k - 94208 < 4096 := by omega
    have heq : 3465219 + 2 * (k - 94208) = 3276803 + 2 * k := by omega
    have h := checkBlock_sound checked0423 (k - 94208) hindex
    rw [heq] at h
    exact h hp
  by_cases h24 : k < 102400
  · have hindex : k - 98304 < 4096 := by omega
    have heq : 3473411 + 2 * (k - 98304) = 3276803 + 2 * k := by omega
    have h := checkBlock_sound checked0424 (k - 98304) hindex
    rw [heq] at h
    exact h hp
  have hindex : k - 102400 < 940 := by omega
  have heq : 3481603 + 2 * (k - 102400) = 3276803 + 2 * k := by omega
  have h := checkBlock_sound checked0425 (k - 102400) hindex
  rw [heq] at h
  exact h hp

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
