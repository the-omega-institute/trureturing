/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Groups/Group08
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks07/Block0586.checked0586
   digest: Adjacent checker successes cover extended consecutive odd slots. -/

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

/-- Every prime slot in this complete consecutive group has a smaller prime root. -/
theorem group08_sound :
    ∀ (k : ℕ), k < 102899 → (4794203 + 2 * k).Prime →
      ∃ (q : ℕ), q.Prime ∧ q < 4794203 + 2 * k ∧
        orderOf (q : ZMod (4794203 + 2 * k)) = 4794203 + 2 * k - 1 := by
  intro k hk hp
  by_cases h00 : k < 4096
  · have hindex : k - 0 < 4096 := by omega
    have heq : 4794203 + 2 * (k - 0) = 4794203 + 2 * k := by omega
    have h := checkBlock_sound checked0586 (k - 0) hindex
    rw [heq] at h
    exact h hp
  by_cases h01 : k < 8192
  · have hindex : k - 4096 < 4096 := by omega
    have heq : 4802395 + 2 * (k - 4096) = 4794203 + 2 * k := by omega
    have h := checkBlock_sound checked0587 (k - 4096) hindex
    rw [heq] at h
    exact h hp
  by_cases h02 : k < 12288
  · have hindex : k - 8192 < 4096 := by omega
    have heq : 4810587 + 2 * (k - 8192) = 4794203 + 2 * k := by omega
    have h := checkBlock_sound checked0588 (k - 8192) hindex
    rw [heq] at h
    exact h hp
  by_cases h03 : k < 16384
  · have hindex : k - 12288 < 4096 := by omega
    have heq : 4818779 + 2 * (k - 12288) = 4794203 + 2 * k := by omega
    have h := checkBlock_sound checked0589 (k - 12288) hindex
    rw [heq] at h
    exact h hp
  by_cases h04 : k < 20480
  · have hindex : k - 16384 < 4096 := by omega
    have heq : 4826971 + 2 * (k - 16384) = 4794203 + 2 * k := by omega
    have h := checkBlock_sound checked0590 (k - 16384) hindex
    rw [heq] at h
    exact h hp
  by_cases h05 : k < 24576
  · have hindex : k - 20480 < 4096 := by omega
    have heq : 4835163 + 2 * (k - 20480) = 4794203 + 2 * k := by omega
    have h := checkBlock_sound checked0591 (k - 20480) hindex
    rw [heq] at h
    exact h hp
  by_cases h06 : k < 28672
  · have hindex : k - 24576 < 4096 := by omega
    have heq : 4843355 + 2 * (k - 24576) = 4794203 + 2 * k := by omega
    have h := checkBlock_sound checked0592 (k - 24576) hindex
    rw [heq] at h
    exact h hp
  by_cases h07 : k < 32768
  · have hindex : k - 28672 < 4096 := by omega
    have heq : 4851547 + 2 * (k - 28672) = 4794203 + 2 * k := by omega
    have h := checkBlock_sound checked0593 (k - 28672) hindex
    rw [heq] at h
    exact h hp
  by_cases h08 : k < 36864
  · have hindex : k - 32768 < 4096 := by omega
    have heq : 4859739 + 2 * (k - 32768) = 4794203 + 2 * k := by omega
    have h := checkBlock_sound checked0594 (k - 32768) hindex
    rw [heq] at h
    exact h hp
  by_cases h09 : k < 40960
  · have hindex : k - 36864 < 4096 := by omega
    have heq : 4867931 + 2 * (k - 36864) = 4794203 + 2 * k := by omega
    have h := checkBlock_sound checked0595 (k - 36864) hindex
    rw [heq] at h
    exact h hp
  by_cases h10 : k < 45056
  · have hindex : k - 40960 < 4096 := by omega
    have heq : 4876123 + 2 * (k - 40960) = 4794203 + 2 * k := by omega
    have h := checkBlock_sound checked0596 (k - 40960) hindex
    rw [heq] at h
    exact h hp
  by_cases h11 : k < 49152
  · have hindex : k - 45056 < 4096 := by omega
    have heq : 4884315 + 2 * (k - 45056) = 4794203 + 2 * k := by omega
    have h := checkBlock_sound checked0597 (k - 45056) hindex
    rw [heq] at h
    exact h hp
  by_cases h12 : k < 53248
  · have hindex : k - 49152 < 4096 := by omega
    have heq : 4892507 + 2 * (k - 49152) = 4794203 + 2 * k := by omega
    have h := checkBlock_sound checked0598 (k - 49152) hindex
    rw [heq] at h
    exact h hp
  by_cases h13 : k < 57344
  · have hindex : k - 53248 < 4096 := by omega
    have heq : 4900699 + 2 * (k - 53248) = 4794203 + 2 * k := by omega
    have h := checkBlock_sound checked0599 (k - 53248) hindex
    rw [heq] at h
    exact h hp
  by_cases h14 : k < 61440
  · have hindex : k - 57344 < 4096 := by omega
    have heq : 4908891 + 2 * (k - 57344) = 4794203 + 2 * k := by omega
    have h := checkBlock_sound checked0600 (k - 57344) hindex
    rw [heq] at h
    exact h hp
  by_cases h15 : k < 65536
  · have hindex : k - 61440 < 4096 := by omega
    have heq : 4917083 + 2 * (k - 61440) = 4794203 + 2 * k := by omega
    have h := checkBlock_sound checked0601 (k - 61440) hindex
    rw [heq] at h
    exact h hp
  by_cases h16 : k < 69632
  · have hindex : k - 65536 < 4096 := by omega
    have heq : 4925275 + 2 * (k - 65536) = 4794203 + 2 * k := by omega
    have h := checkBlock_sound checked0602 (k - 65536) hindex
    rw [heq] at h
    exact h hp
  by_cases h17 : k < 73728
  · have hindex : k - 69632 < 4096 := by omega
    have heq : 4933467 + 2 * (k - 69632) = 4794203 + 2 * k := by omega
    have h := checkBlock_sound checked0603 (k - 69632) hindex
    rw [heq] at h
    exact h hp
  by_cases h18 : k < 77824
  · have hindex : k - 73728 < 4096 := by omega
    have heq : 4941659 + 2 * (k - 73728) = 4794203 + 2 * k := by omega
    have h := checkBlock_sound checked0604 (k - 73728) hindex
    rw [heq] at h
    exact h hp
  by_cases h19 : k < 81920
  · have hindex : k - 77824 < 4096 := by omega
    have heq : 4949851 + 2 * (k - 77824) = 4794203 + 2 * k := by omega
    have h := checkBlock_sound checked0605 (k - 77824) hindex
    rw [heq] at h
    exact h hp
  by_cases h20 : k < 86016
  · have hindex : k - 81920 < 4096 := by omega
    have heq : 4958043 + 2 * (k - 81920) = 4794203 + 2 * k := by omega
    have h := checkBlock_sound checked0606 (k - 81920) hindex
    rw [heq] at h
    exact h hp
  by_cases h21 : k < 90112
  · have hindex : k - 86016 < 4096 := by omega
    have heq : 4966235 + 2 * (k - 86016) = 4794203 + 2 * k := by omega
    have h := checkBlock_sound checked0607 (k - 86016) hindex
    rw [heq] at h
    exact h hp
  by_cases h22 : k < 94208
  · have hindex : k - 90112 < 4096 := by omega
    have heq : 4974427 + 2 * (k - 90112) = 4794203 + 2 * k := by omega
    have h := checkBlock_sound checked0608 (k - 90112) hindex
    rw [heq] at h
    exact h hp
  by_cases h23 : k < 98304
  · have hindex : k - 94208 < 4096 := by omega
    have heq : 4982619 + 2 * (k - 94208) = 4794203 + 2 * k := by omega
    have h := checkBlock_sound checked0609 (k - 94208) hindex
    rw [heq] at h
    exact h hp
  by_cases h24 : k < 102400
  · have hindex : k - 98304 < 4096 := by omega
    have heq : 4990811 + 2 * (k - 98304) = 4794203 + 2 * k := by omega
    have h := checkBlock_sound checked0610 (k - 98304) hindex
    rw [heq] at h
    exact h hp
  have hindex : k - 102400 < 499 := by omega
  have heq : 4999003 + 2 * (k - 102400) = 4794203 + 2 * k := by omega
  have h := checkBlock_sound checked0611 (k - 102400) hindex
  rw [heq] at h
  exact h hp

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
