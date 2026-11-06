/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTail/LargeWindows
   generality: I
   mirror-B: none(waiver:private-implementation-owned-by-endpoint)
   mirror-E: none(waiver:private-implementation-owned-by-endpoint)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Universal positive-coefficient identities for the original paired seam windows. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.Algebra

/-! Exact equal-tail polynomial windows. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail
open private A B L K SU SV SW scaledGates from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.Algebra

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem large_windows (x p s : ℤ) (hx : 4≤x) (hp : x≤p) (hs : 1≤s) :
    ∀ i : Fin 12, 0≤scaledGates x p s 0 (4*p-4) x (2*x) 0 i := by
  let uX := x-4
  have huX : 0≤uX := by dsimp [uX]; omega
  let uP := p-x
  have huP : 0≤uP := by dsimp [uP]; omega
  let uR := s-1
  have huR : 0≤uR := by dsimp [uR]; omega
  intro i
  fin_cases i
  · have expansion : scaledGates x p s 0 (4*p-4) x (2*x) 0 0 =
      8 * uX^6 * uR + 8 * uX^6 + 24 * uX^5 * uP * uR
      + 24 * uX^5 * uP + 184 * uX^5 * uR + 184 * uX^5
      + 24 * uX^4 * uP^2 * uR + 24 * uX^4 * uP^2 + 456 * uX^4 * uP * uR
      + 456 * uX^4 * uP + 1776 * uX^4 * uR + 1776 * uX^4
      + 8 * uX^3 * uP^3 * uR + 8 * uX^3 * uP^3 + 360 * uX^3 * uP^2 * uR
      + 360 * uX^3 * uP^2 + 3488 * uX^3 * uP * uR + 3488 * uX^3 * uP
      + 9208 * uX^3 * uR + 9208 * uX^3 + 88 * uX^2 * uP^3 * uR
      + 88 * uX^2 * uP^3 + 2032 * uX^2 * uP^2 * uR + 2032 * uX^2 * uP^2
      + 13424 * uX^2 * uP * uR + 13424 * uX^2 * uP + 27056 * uX^2 * uR
      + 27056 * uX^2 + 320 * uX * uP^3 * uR + 320 * uX * uP^3
      + 5112 * uX * uP^2 * uR + 5112 * uX * uP^2 + 26000 * uX * uP * uR
      + 26000 * uX * uP + 42744 * uX * uR + 42744 * uX
      + 384 * uP^3 * uR + 384 * uP^3 + 4832 * uP^2 * uR
      + 4832 * uP^2 + 20280 * uP * uR + 20280 * uP
      + 28384 * uR + 28392 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uX,uP,uR]
      ring
    change 0≤scaledGates x p s 0 (4*p-4) x (2*x) 0 0
    rw [expansion]
    positivity
  · have expansion : scaledGates x p s 0 (4*p-4) x (2*x) 0 1 =
      8 * uX^5 * uR + 8 * uX^5 + 24 * uX^4 * uP * uR
      + 24 * uX^4 * uP + 152 * uX^4 * uR + 152 * uX^4
      + 24 * uX^3 * uP^2 * uR + 24 * uX^3 * uP^2 + 368 * uX^3 * uP * uR
      + 368 * uX^3 * uP + 1160 * uX^3 * uR + 1160 * uX^3
      + 8 * uX^2 * uP^3 * uR + 8 * uX^2 * uP^3 + 280 * uX^2 * uP^2 * uR
      + 280 * uX^2 * uP^2 + 2128 * uX^2 * uP * uR + 2128 * uX^2 * uP
      + 4440 * uX^2 * uR + 4440 * uX^2 + 64 * uX * uP^3 * uR
      + 64 * uX * uP^3 + 1096 * uX * uP^2 * uR + 1096 * uX * uP^2
      + 5496 * uX * uP * uR + 5496 * uX * uP + 8520 * uX * uR
      + 8520 * uX + 128 * uP^3 * uR + 128 * uP^3
      + 1440 * uP^2 * uR + 1440 * uP^2 + 5352 * uP * uR
      + 5352 * uP + 6560 * uR + 6552 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uX,uP,uR]
      ring
    change 0≤scaledGates x p s 0 (4*p-4) x (2*x) 0 1
    rw [expansion]
    positivity
  · have expansion : scaledGates x p s 0 (4*p-4) x (2*x) 0 2 =
      4 * uX^5 * uR + 4 * uX^5 + 8 * uX^4 * uP * uR
      + 8 * uX^4 * uP + 72 * uX^4 * uR + 74 * uX^4
      + 4 * uX^3 * uP^2 * uR + 4 * uX^3 * uP^2 + 112 * uX^3 * uP * uR
      + 114 * uX^3 * uP + 524 * uX^3 * uR + 558 * uX^3
      + 40 * uX^2 * uP^2 * uR + 40 * uX^2 * uP^2 + 588 * uX^2 * uP * uR
      + 614 * uX^2 * uP + 1928 * uX^2 * uR + 2144 * uX^2
      + 128 * uX * uP^2 * uR + 128 * uX * uP^2 + 1368 * uX * uP * uR
      + 1480 * uX * uP + 3580 * uX * uR + 4198 * uX
      + 128 * uP^2 * uR + 128 * uP^2 + 1184 * uP * uR
      + 1344 * uP + 2664 * uR + 3352 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uX,uP,uR]
      ring
    change 0≤scaledGates x p s 0 (4*p-4) x (2*x) 0 2
    rw [expansion]
    positivity
  · have expansion : scaledGates x p s 0 (4*p-4) x (2*x) 0 3 =
      4 * uX^5 * uR + 4 * uX^5 + 8 * uX^4 * uP * uR
      + 8 * uX^4 * uP + 88 * uX^4 * uR + 86 * uX^4
      + 4 * uX^3 * uP^2 * uR + 4 * uX^3 * uP^2 + 144 * uX^3 * uP * uR
      + 142 * uX^3 * uP + 764 * uX^3 * uR + 730 * uX^3
      + 56 * uX^2 * uP^2 * uR + 56 * uX^2 * uP^2 + 956 * uX^2 * uP * uR
      + 930 * uX^2 * uP + 3288 * uX^2 * uR + 3072 * uX^2
      + 256 * uX * uP^2 * uR + 256 * uX * uP^2 + 2792 * uX * uP * uR
      + 2680 * uX * uP + 7044 * uX * uR + 6430 * uX
      + 384 * uP^2 * uR + 384 * uP^2 + 3040 * uP * uR
      + 2880 * uP + 6040 * uR + 5368 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uX,uP,uR]
      ring
    change 0≤scaledGates x p s 0 (4*p-4) x (2*x) 0 3
    rw [expansion]
    positivity
  · have expansion : scaledGates x p s 0 (4*p-4) x (2*x) 0 4 =
      4 * uX^5 * uR + 4 * uX^5 + 8 * uX^4 * uP * uR
      + 8 * uX^4 * uP + 72 * uX^4 * uR + 74 * uX^4
      + 4 * uX^3 * uP^2 * uR + 4 * uX^3 * uP^2 + 112 * uX^3 * uP * uR
      + 114 * uX^3 * uP + 508 * uX^3 * uR + 550 * uX^3
      + 40 * uX^2 * uP^2 * uR + 40 * uX^2 * uP^2 + 572 * uX^2 * uP * uR
      + 606 * uX^2 * uP + 1736 * uX^2 * uR + 2056 * uX^2
      + 128 * uX * uP^2 * uR + 128 * uX * uP^2 + 1240 * uX * uP * uR
      + 1424 * uX * uP + 2812 * uX * uR + 3870 * uX
      + 128 * uP^2 * uR + 128 * uP^2 + 928 * uP * uR
      + 1248 * uP + 1640 * uR + 2936 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uX,uP,uR]
      ring
    change 0≤scaledGates x p s 0 (4*p-4) x (2*x) 0 4
    rw [expansion]
    positivity
  · have expansion : scaledGates x p s 0 (4*p-4) x (2*x) 0 5 =
      4 * uX^5 * uR + 4 * uX^5 + 8 * uX^4 * uP * uR
      + 8 * uX^4 * uP + 88 * uX^4 * uR + 86 * uX^4
      + 4 * uX^3 * uP^2 * uR + 4 * uX^3 * uP^2 + 144 * uX^3 * uP * uR
      + 142 * uX^3 * uP + 772 * uX^3 * uR + 734 * uX^3
      + 56 * uX^2 * uP^2 * uR + 56 * uX^2 * uP^2 + 964 * uX^2 * uP * uR
      + 934 * uX^2 * uP + 3384 * uX^2 * uR + 3116 * uX^2
      + 256 * uX * uP^2 * uR + 256 * uX * uP^2 + 2856 * uX * uP * uR
      + 2708 * uX * uP + 7428 * uX * uR + 6594 * uX
      + 384 * uP^2 * uR + 384 * uP^2 + 3168 * uP * uR
      + 2928 * uP + 6552 * uR + 5576 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uX,uP,uR]
      ring
    change 0≤scaledGates x p s 0 (4*p-4) x (2*x) 0 5
    rw [expansion]
    positivity
  · have expansion : scaledGates x p s 0 (4*p-4) x (2*x) 0 6 =
      16 * uX^6 * uR + 16 * uX^6 + 48 * uX^5 * uP * uR
      + 48 * uX^5 * uP + 368 * uX^5 * uR + 368 * uX^5
      + 48 * uX^4 * uP^2 * uR + 48 * uX^4 * uP^2 + 912 * uX^4 * uP * uR
      + 912 * uX^4 * uP + 3536 * uX^4 * uR + 3536 * uX^4
      + 16 * uX^3 * uP^3 * uR + 16 * uX^3 * uP^3 + 720 * uX^3 * uP^2 * uR
      + 720 * uX^3 * uP^2 + 6944 * uX^3 * uP * uR + 6944 * uX^3 * uP
      + 18168 * uX^3 * uR + 18168 * uX^3 + 176 * uX^2 * uP^3 * uR
      + 176 * uX^2 * uP^3 + 4048 * uX^2 * uP^2 * uR + 4048 * uX^2 * uP^2
      + 26480 * uX^2 * uP * uR + 26480 * uX^2 * uP + 52656 * uX^2 * uR
      + 52656 * uX^2 + 640 * uX * uP^3 * uR + 640 * uX * uP^3
      + 10104 * uX * uP^2 * uR + 10104 * uX * uP^2 + 50576 * uX * uP * uR
      + 50576 * uX * uP + 81656 * uX * uR + 81656 * uX
      + 768 * uP^3 * uR + 768 * uP^3 + 9440 * uP^2 * uR
      + 9440 * uP^2 + 38712 * uP * uR + 38712 * uP
      + 52960 * uR + 52968 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uX,uP,uR]
      ring
    change 0≤scaledGates x p s 0 (4*p-4) x (2*x) 0 6
    rw [expansion]
    positivity
  · have expansion : scaledGates x p s 0 (4*p-4) x (2*x) 0 7 =
      16 * uX^5 * uR + 16 * uX^5 + 48 * uX^4 * uP * uR
      + 48 * uX^4 * uP + 312 * uX^4 * uR + 312 * uX^4
      + 48 * uX^3 * uP^2 * uR + 48 * uX^3 * uP^2 + 752 * uX^3 * uP * uR
      + 752 * uX^3 * uP + 2440 * uX^3 * uR + 2440 * uX^3
      + 16 * uX^2 * uP^3 * uR + 16 * uX^2 * uP^3 + 568 * uX^2 * uP^2 * uR
      + 568 * uX^2 * uP^2 + 4432 * uX^2 * uP * uR + 4432 * uX^2 * uP
      + 9560 * uX^2 * uR + 9560 * uX^2 + 128 * uX * uP^3 * uR
      + 128 * uX * uP^3 + 2248 * uX * uP^2 * uR + 2248 * uX * uP^2
      + 11640 * uX * uP * uR + 11640 * uX * uP + 18760 * uX * uR
      + 18760 * uX + 256 * uP^3 * uR + 256 * uP^3
      + 2976 * uP^2 * uR + 2976 * uP^2 + 11496 * uP * uR
      + 11496 * uP + 14752 * uR + 14744 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uX,uP,uR]
      ring
    change 0≤scaledGates x p s 0 (4*p-4) x (2*x) 0 7
    rw [expansion]
    positivity
  · have expansion : scaledGates x p s 0 (4*p-4) x (2*x) 0 8 =
      8 * uX^5 * uR + 8 * uX^5 + 16 * uX^4 * uP * uR
      + 16 * uX^4 * uP + 144 * uX^4 * uR + 148 * uX^4
      + 8 * uX^3 * uP^2 * uR + 8 * uX^3 * uP^2 + 224 * uX^3 * uP * uR
      + 228 * uX^3 * uP + 1052 * uX^3 * uR + 1120 * uX^3
      + 80 * uX^2 * uP^2 * uR + 80 * uX^2 * uP^2 + 1180 * uX^2 * uP * uR
      + 1232 * uX^2 * uP + 3912 * uX^2 * uR + 4344 * uX^2
      + 256 * uX * uP^2 * uR + 256 * uX * uP^2 + 2776 * uX * uP * uR
      + 3000 * uX * uP + 7420 * uX * uR + 8654 * uX
      + 256 * uP^2 * uR + 256 * uP^2 + 2464 * uP * uR
      + 2784 * uP + 5736 * uR + 7104 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uX,uP,uR]
      ring
    change 0≤scaledGates x p s 0 (4*p-4) x (2*x) 0 8
    rw [expansion]
    positivity
  · have expansion : scaledGates x p s 0 (4*p-4) x (2*x) 0 9 =
      16 * uX^4 * uR + 12 * uX^4 + 32 * uX^3 * uP * uR
      + 28 * uX^3 * uP + 236 * uX^3 * uR + 168 * uX^3
      + 16 * uX^2 * uP^2 * uR + 16 * uX^2 * uP^2 + 364 * uX^2 * uP * uR
      + 312 * uX^2 * uP + 1304 * uX^2 * uR + 872 * uX^2
      + 128 * uX * uP^2 * uR + 128 * uX * uP^2 + 1384 * uX * uP * uR
      + 1160 * uX * uP + 3204 * uX * uR + 1974 * uX
      + 256 * uP^2 * uR + 256 * uP^2 + 1760 * uP * uR
      + 1440 * uP + 2968 * uR + 1616 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uX,uP,uR]
      ring
    change 0≤scaledGates x p s 0 (4*p-4) x (2*x) 0 9
    rw [expansion]
    positivity
  · have expansion : scaledGates x p s 0 (4*p-4) x (2*x) 0 10 =
      8 * uX^5 * uR + 8 * uX^5 + 16 * uX^4 * uP * uR
      + 16 * uX^4 * uP + 144 * uX^4 * uR + 148 * uX^4
      + 8 * uX^3 * uP^2 * uR + 8 * uX^3 * uP^2 + 224 * uX^3 * uP * uR
      + 228 * uX^3 * uP + 1020 * uX^3 * uR + 1104 * uX^3
      + 80 * uX^2 * uP^2 * uR + 80 * uX^2 * uP^2 + 1148 * uX^2 * uP * uR
      + 1216 * uX^2 * uP + 3528 * uX^2 * uR + 4168 * uX^2
      + 256 * uX * uP^2 * uR + 256 * uX * uP^2 + 2520 * uX * uP * uR
      + 2888 * uX * uP + 5884 * uX * uR + 7998 * uX
      + 256 * uP^2 * uR + 256 * uP^2 + 1952 * uP * uR
      + 2592 * uP + 3688 * uR + 6264 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uX,uP,uR]
      ring
    change 0≤scaledGates x p s 0 (4*p-4) x (2*x) 0 10
    rw [expansion]
    positivity
  · have expansion : scaledGates x p s 0 (4*p-4) x (2*x) 0 11 =
      8 * uX^5 * uR + 8 * uX^5 + 16 * uX^4 * uP * uR
      + 16 * uX^4 * uP + 176 * uX^4 * uR + 172 * uX^4
      + 8 * uX^3 * uP^2 * uR + 8 * uX^3 * uP^2 + 288 * uX^3 * uP * uR
      + 284 * uX^3 * uP + 1540 * uX^3 * uR + 1464 * uX^3
      + 112 * uX^2 * uP^2 * uR + 112 * uX^2 * uP^2 + 1924 * uX^2 * uP * uR
      + 1864 * uX^2 * uP + 6712 * uX^2 * uR + 6176 * uX^2
      + 512 * uX * uP^2 * uR + 512 * uX * uP^2 + 5672 * uX * uP * uR
      + 5376 * uX * uP + 14596 * uX * uR + 12930 * uX
      + 768 * uP^2 * uR + 768 * uP^2 + 6240 * uP * uR
      + 5760 * uP + 12696 * uR + 10760 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uX,uP,uR]
      ring
    change 0≤scaledGates x p s 0 (4*p-4) x (2*x) 0 11
    rw [expansion]
    positivity

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail
