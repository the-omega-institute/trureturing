/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Groups/Group05
   generality: I
   mirror-B: none(waiver:finite-coverage-helper-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificates)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks05/Block0400.checked0400
   digest: Adjacent checker successes cover a complete interval of odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Checker
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

private theorem block_at {base start off count : ℕ} {rows : List Row}
    (h : checkBlock start count rows = true) (hst : start = base + 2 * off)
    {k : ℕ} (hlo : off ≤ k) (hhi : k < off + count) (hp : (base + 2 * k).Prime) :
    ∃ q, q.Prime ∧ q < base + 2 * k ∧
      orderOf (q : ZMod (base + 2 * k)) = base + 2 * k - 1 := by
  have hindex : k - off < count := by omega
  have heq : start + 2 * (k - off) = base + 2 * k := by omega
  have ht := checkBlock_sound h (k - off) hindex
  rw [heq] at ht
  exact ht hp

/-- Complete prime-root coverage of this consecutive group of checked odd slots. -/
theorem group05_sound :
    ∀ (k : ℕ), k < 103340 → (3276803 + 2 * k).Prime →
      ∃ (q : ℕ), q.Prime ∧ q < 3276803 + 2 * k ∧
        orderOf (q : ZMod (3276803 + 2 * k)) = 3276803 + 2 * k - 1 := by
  intro k hk hp
  by_cases h00 : k < 4096
  · exact block_at (base := 3276803) (off := 0) checked0400 rfl
      (Nat.zero_le k) h00 hp
  by_cases h01 : k < 8192
  · exact block_at (base := 3276803) (off := 4096) checked0401 rfl
      (Nat.le_of_not_gt h00) h01 hp
  by_cases h02 : k < 12288
  · exact block_at (base := 3276803) (off := 8192) checked0402 rfl
      (Nat.le_of_not_gt h01) h02 hp
  by_cases h03 : k < 16384
  · exact block_at (base := 3276803) (off := 12288) checked0403 rfl
      (Nat.le_of_not_gt h02) h03 hp
  by_cases h04 : k < 20480
  · exact block_at (base := 3276803) (off := 16384) checked0404 rfl
      (Nat.le_of_not_gt h03) h04 hp
  by_cases h05 : k < 24576
  · exact block_at (base := 3276803) (off := 20480) checked0405 rfl
      (Nat.le_of_not_gt h04) h05 hp
  by_cases h06 : k < 28672
  · exact block_at (base := 3276803) (off := 24576) checked0406 rfl
      (Nat.le_of_not_gt h05) h06 hp
  by_cases h07 : k < 32768
  · exact block_at (base := 3276803) (off := 28672) checked0407 rfl
      (Nat.le_of_not_gt h06) h07 hp
  by_cases h08 : k < 36864
  · exact block_at (base := 3276803) (off := 32768) checked0408 rfl
      (Nat.le_of_not_gt h07) h08 hp
  by_cases h09 : k < 40960
  · exact block_at (base := 3276803) (off := 36864) checked0409 rfl
      (Nat.le_of_not_gt h08) h09 hp
  by_cases h10 : k < 45056
  · exact block_at (base := 3276803) (off := 40960) checked0410 rfl
      (Nat.le_of_not_gt h09) h10 hp
  by_cases h11 : k < 49152
  · exact block_at (base := 3276803) (off := 45056) checked0411 rfl
      (Nat.le_of_not_gt h10) h11 hp
  by_cases h12 : k < 53248
  · exact block_at (base := 3276803) (off := 49152) checked0412 rfl
      (Nat.le_of_not_gt h11) h12 hp
  by_cases h13 : k < 57344
  · exact block_at (base := 3276803) (off := 53248) checked0413 rfl
      (Nat.le_of_not_gt h12) h13 hp
  by_cases h14 : k < 61440
  · exact block_at (base := 3276803) (off := 57344) checked0414 rfl
      (Nat.le_of_not_gt h13) h14 hp
  by_cases h15 : k < 65536
  · exact block_at (base := 3276803) (off := 61440) checked0415 rfl
      (Nat.le_of_not_gt h14) h15 hp
  by_cases h16 : k < 69632
  · exact block_at (base := 3276803) (off := 65536) checked0416 rfl
      (Nat.le_of_not_gt h15) h16 hp
  by_cases h17 : k < 73728
  · exact block_at (base := 3276803) (off := 69632) checked0417 rfl
      (Nat.le_of_not_gt h16) h17 hp
  by_cases h18 : k < 77824
  · exact block_at (base := 3276803) (off := 73728) checked0418 rfl
      (Nat.le_of_not_gt h17) h18 hp
  by_cases h19 : k < 81920
  · exact block_at (base := 3276803) (off := 77824) checked0419 rfl
      (Nat.le_of_not_gt h18) h19 hp
  by_cases h20 : k < 86016
  · exact block_at (base := 3276803) (off := 81920) checked0420 rfl
      (Nat.le_of_not_gt h19) h20 hp
  by_cases h21 : k < 90112
  · exact block_at (base := 3276803) (off := 86016) checked0421 rfl
      (Nat.le_of_not_gt h20) h21 hp
  by_cases h22 : k < 94208
  · exact block_at (base := 3276803) (off := 90112) checked0422 rfl
      (Nat.le_of_not_gt h21) h22 hp
  by_cases h23 : k < 98304
  · exact block_at (base := 3276803) (off := 94208) checked0423 rfl
      (Nat.le_of_not_gt h22) h23 hp
  by_cases h24 : k < 102400
  · exact block_at (base := 3276803) (off := 98304) checked0424 rfl
      (Nat.le_of_not_gt h23) h24 hp
  exact block_at (base := 3276803) (off := 102400) checked0425 rfl
      (Nat.le_of_not_gt h24) hk hp

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
