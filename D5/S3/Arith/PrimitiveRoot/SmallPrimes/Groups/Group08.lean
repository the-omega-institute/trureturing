/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Groups/Group08
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks07/Block0586.checked0586
   digest: Adjacent checker successes cover extended consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Checker
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks07.Block0586
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks07.Block0587
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks07.Block0588
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks07.Block0589
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks07.Block0590
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks07.Block0591
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks07.Block0592
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks07.Block0593
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks07.Block0594
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks07.Block0595
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks07.Block0596
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks07.Block0597
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks07.Block0598
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks07.Block0599
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks07.Block0600
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks07.Block0601
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks07.Block0602
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks07.Block0603
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks07.Block0604
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks07.Block0605
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks07.Block0606
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks07.Block0607
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks07.Block0608
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks07.Block0609
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks07.Block0610
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks07.Block0611

set_option maxRecDepth 10000
set_option maxHeartbeats 0

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

/-- Every prime slot in this complete consecutive group has a smaller prime root. -/
theorem group08_sound :
    ∀ (k : ℕ), k < 102899 → (4794203 + 2 * k).Prime →
      ∃ (q : ℕ), q.Prime ∧ q < 4794203 + 2 * k ∧
        orderOf (q : ZMod (4794203 + 2 * k)) = 4794203 + 2 * k - 1 := by
  intro k hk hp
  by_cases h00 : k < 4096
  · exact block_at (base := 4794203) (off := 0) checked0586 rfl
      (Nat.zero_le k) h00 hp
  by_cases h01 : k < 8192
  · exact block_at (base := 4794203) (off := 4096) checked0587 rfl
      (Nat.le_of_not_gt h00) h01 hp
  by_cases h02 : k < 12288
  · exact block_at (base := 4794203) (off := 8192) checked0588 rfl
      (Nat.le_of_not_gt h01) h02 hp
  by_cases h03 : k < 16384
  · exact block_at (base := 4794203) (off := 12288) checked0589 rfl
      (Nat.le_of_not_gt h02) h03 hp
  by_cases h04 : k < 20480
  · exact block_at (base := 4794203) (off := 16384) checked0590 rfl
      (Nat.le_of_not_gt h03) h04 hp
  by_cases h05 : k < 24576
  · exact block_at (base := 4794203) (off := 20480) checked0591 rfl
      (Nat.le_of_not_gt h04) h05 hp
  by_cases h06 : k < 28672
  · exact block_at (base := 4794203) (off := 24576) checked0592 rfl
      (Nat.le_of_not_gt h05) h06 hp
  by_cases h07 : k < 32768
  · exact block_at (base := 4794203) (off := 28672) checked0593 rfl
      (Nat.le_of_not_gt h06) h07 hp
  by_cases h08 : k < 36864
  · exact block_at (base := 4794203) (off := 32768) checked0594 rfl
      (Nat.le_of_not_gt h07) h08 hp
  by_cases h09 : k < 40960
  · exact block_at (base := 4794203) (off := 36864) checked0595 rfl
      (Nat.le_of_not_gt h08) h09 hp
  by_cases h10 : k < 45056
  · exact block_at (base := 4794203) (off := 40960) checked0596 rfl
      (Nat.le_of_not_gt h09) h10 hp
  by_cases h11 : k < 49152
  · exact block_at (base := 4794203) (off := 45056) checked0597 rfl
      (Nat.le_of_not_gt h10) h11 hp
  by_cases h12 : k < 53248
  · exact block_at (base := 4794203) (off := 49152) checked0598 rfl
      (Nat.le_of_not_gt h11) h12 hp
  by_cases h13 : k < 57344
  · exact block_at (base := 4794203) (off := 53248) checked0599 rfl
      (Nat.le_of_not_gt h12) h13 hp
  by_cases h14 : k < 61440
  · exact block_at (base := 4794203) (off := 57344) checked0600 rfl
      (Nat.le_of_not_gt h13) h14 hp
  by_cases h15 : k < 65536
  · exact block_at (base := 4794203) (off := 61440) checked0601 rfl
      (Nat.le_of_not_gt h14) h15 hp
  by_cases h16 : k < 69632
  · exact block_at (base := 4794203) (off := 65536) checked0602 rfl
      (Nat.le_of_not_gt h15) h16 hp
  by_cases h17 : k < 73728
  · exact block_at (base := 4794203) (off := 69632) checked0603 rfl
      (Nat.le_of_not_gt h16) h17 hp
  by_cases h18 : k < 77824
  · exact block_at (base := 4794203) (off := 73728) checked0604 rfl
      (Nat.le_of_not_gt h17) h18 hp
  by_cases h19 : k < 81920
  · exact block_at (base := 4794203) (off := 77824) checked0605 rfl
      (Nat.le_of_not_gt h18) h19 hp
  by_cases h20 : k < 86016
  · exact block_at (base := 4794203) (off := 81920) checked0606 rfl
      (Nat.le_of_not_gt h19) h20 hp
  by_cases h21 : k < 90112
  · exact block_at (base := 4794203) (off := 86016) checked0607 rfl
      (Nat.le_of_not_gt h20) h21 hp
  by_cases h22 : k < 94208
  · exact block_at (base := 4794203) (off := 90112) checked0608 rfl
      (Nat.le_of_not_gt h21) h22 hp
  by_cases h23 : k < 98304
  · exact block_at (base := 4794203) (off := 94208) checked0609 rfl
      (Nat.le_of_not_gt h22) h23 hp
  by_cases h24 : k < 102400
  · exact block_at (base := 4794203) (off := 98304) checked0610 rfl
      (Nat.le_of_not_gt h23) h24 hp
  exact block_at (base := 4794203) (off := 102400) checked0611 rfl
      (Nat.le_of_not_gt h24) hk hp

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
