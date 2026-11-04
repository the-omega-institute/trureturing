/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTail/SmallLessWindows
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
private theorem small_l_less_windows (ell p s : ℤ) (he : 1≤ell) (hp : 2*ell≤p) (hs : 1≤s) :
    ∀ i : Fin 12, 0≤scaledGates (4*p*ell) p s ell (8*p*(ell+1)-8) (4*p*ell+4*ell) (8*p*ell+8*ell) 1 i := by
  let uT := ell-1
  have huT : 0≤uT := by dsimp [uT]; omega
  let uP := p-2*ell
  have huP : 0≤uP := by dsimp [uP]; omega
  let uR := s-1
  have huR : 0≤uR := by dsimp [uR]; omega
  intro i
  fin_cases i
  · have expansion : scaledGates (4*p*ell) p s ell (8*p*(ell+1)-8) (4*p*ell+4*ell) (8*p*ell+8*ell) 1 0 =
      8192 * uT^8 * uR + 8192 * uT^8 + 20480 * uT^7 * uP * uR
      + 20480 * uT^7 * uP + 61440 * uT^7 * uR + 61440 * uT^7
      + 20480 * uT^6 * uP^2 * uR + 20480 * uT^6 * uP^2 + 131072 * uT^6 * uP * uR
      + 131072 * uT^6 * uP + 206848 * uT^6 * uR + 206848 * uT^6
      + 10240 * uT^5 * uP^3 * uR + 10240 * uT^5 * uP^3 + 108544 * uT^5 * uP^2 * uR
      + 108544 * uT^5 * uP^2 + 368640 * uT^5 * uP * uR + 368640 * uT^5 * uP
      + 409088 * uT^5 * uR + 409088 * uT^5 + 2560 * uT^4 * uP^4 * uR
      + 2560 * uT^4 * uP^4 + 43008 * uT^4 * uP^3 * uR + 43008 * uT^4 * uP^3
      + 244736 * uT^4 * uP^2 * uR + 244736 * uT^4 * uP^2 + 593152 * uT^4 * uP * uR
      + 593152 * uT^4 * uP + 519424 * uT^4 * uR + 519424 * uT^4
      + 256 * uT^3 * uP^5 * uR + 256 * uT^3 * uP^5 + 7936 * uT^3 * uP^4 * uR
      + 7936 * uT^3 * uP^4 + 72704 * uT^3 * uP^3 * uR + 72704 * uT^3 * uP^3
      + 302720 * uT^3 * uP^2 * uR + 302720 * uT^3 * uP^2 + 590336 * uT^3 * uP * uR
      + 590336 * uT^3 * uP + 432512 * uT^3 * uR + 432512 * uT^3
      + 512 * uT^2 * uP^5 * uR + 512 * uT^2 * uP^5 + 8832 * uT^2 * uP^4 * uR
      + 8832 * uT^2 * uP^4 + 62400 * uT^2 * uP^3 * uR + 62400 * uT^2 * uP^3
      + 217664 * uT^2 * uP^2 * uR + 217664 * uT^2 * uP^2 + 362880 * uT^2 * uP * uR
      + 362880 * uT^2 * uP + 229984 * uT^2 * uR + 229984 * uT^2
      + 256 * uT * uP^5 * uR + 256 * uT * uP^5 + 4096 * uT * uP^4 * uR
      + 4096 * uT * uP^4 + 27456 * uT * uP^3 * uR + 27456 * uT * uP^3
      + 86368 * uT * uP^2 * uR + 86368 * uT * uP^2 + 127216 * uT * uP * uR
      + 127216 * uT * uP + 71200 * uT * uR + 71208 * uT
      + 640 * uP^4 * uR + 640 * uP^4 + 4992 * uP^3 * uR
      + 4992 * uP^3 + 14752 * uP^2 * uR + 14752 * uP^2
      + 19552 * uP * uR + 19552 * uP + 9800 * uR
      + 9816 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uT,uP,uR]
      ring
    change 0≤scaledGates (4*p*ell) p s ell (8*p*(ell+1)-8) (4*p*ell+4*ell) (8*p*ell+8*ell) 1 0
    rw [expansion]
    positivity
  · have expansion : scaledGates (4*p*ell) p s ell (8*p*(ell+1)-8) (4*p*ell+4*ell) (8*p*ell+8*ell) 1 1 =
      32768 * uT^9 * uR + 32768 * uT^9 + 98304 * uT^8 * uP * uR
      + 98304 * uT^8 * uP + 286720 * uT^8 * uR + 286720 * uT^8
      + 122880 * uT^7 * uP^2 * uR + 122880 * uT^7 * uP^2 + 765952 * uT^7 * uP * uR
      + 765952 * uT^7 * uP + 1118208 * uT^7 * uR + 1118208 * uT^7
      + 81920 * uT^6 * uP^3 * uR + 81920 * uT^6 * uP^3 + 839680 * uT^6 * uP^2 * uR
      + 839680 * uT^6 * uP^2 + 2621440 * uT^6 * uP * uR + 2621440 * uT^6 * uP
      + 2547712 * uT^6 * uR + 2547712 * uT^6 + 30720 * uT^5 * uP^4 * uR
      + 30720 * uT^5 * uP^4 + 481280 * uT^5 * uP^3 * uR + 481280 * uT^5 * uP^3
      + 2471936 * uT^5 * uP^2 * uR + 2471936 * uT^5 * uP^2 + 5140480 * uT^5 * uP * uR
      + 5140480 * uT^5 * uP + 3731968 * uT^5 * uR + 3731968 * uT^5
      + 6144 * uT^4 * uP^5 * uR + 6144 * uT^4 * uP^5 + 151040 * uT^4 * uP^4 * uR
      + 151040 * uT^4 * uP^4 + 1185792 * uT^4 * uP^3 * uR + 1185792 * uT^4 * uP^3
      + 4059136 * uT^4 * uP^2 * uR + 4059136 * uT^4 * uP^2 + 6308608 * uT^4 * uP * uR
      + 6308608 * uT^4 * uP + 3640064 * uT^4 * uR + 3640064 * uT^4
      + 512 * uT^3 * uP^6 * uR + 512 * uT^3 * uP^6 + 24320 * uT^3 * uP^5 * uR
      + 24320 * uT^3 * uP^5 + 299264 * uT^3 * uP^4 * uR + 299264 * uT^3 * uP^4
      + 1566720 * uT^3 * uP^3 * uR + 1566720 * uT^3 * uP^3 + 4010368 * uT^3 * uP^2 * uR
      + 4010368 * uT^3 * uP^2 + 4955648 * uT^3 * uP * uR + 4955648 * uT^3 * uP
      + 2361088 * uT^3 * uR + 2361088 * uT^3 + 1536 * uT^2 * uP^6 * uR
      + 1536 * uT^2 * uP^6 + 36352 * uT^2 * uP^5 * uR + 36352 * uT^2 * uP^5
      + 298496 * uT^2 * uP^4 * uR + 298496 * uT^2 * uP^4 + 1169472 * uT^2 * uP^3 * uR
      + 1169472 * uT^2 * uP^3 + 2381248 * uT^2 * uP^2 * uR + 2381248 * uT^2 * uP^2
      + 2430720 * uT^2 * uP * uR + 2430720 * uT^2 * uP + 980768 * uT^2 * uR
      + 980768 * uT^2 + 1536 * uT * uP^6 * uR + 1536 * uT * uP^6
      + 24320 * uT * uP^5 * uR + 24320 * uT * uP^5 + 149760 * uT * uP^4 * uR
      + 149760 * uT * uP^4 + 467136 * uT * uP^3 * uR + 467136 * uT * uP^3
      + 786112 * uT * uP^2 * uR + 786112 * uT * uP^2 + 679952 * uT * uP * uR
      + 679952 * uT * uP + 236384 * uT * uR + 236376 * uT
      + 512 * uP^6 * uR + 512 * uP^6 + 6144 * uP^5 * uR
      + 6144 * uP^5 + 30208 * uP^4 * uR + 30208 * uP^4
      + 77952 * uP^3 * uR + 77952 * uP^3 + 111232 * uP^2 * uR
      + 111232 * uP^2 + 82976 * uP * uR + 82976 * uP
      + 25144 * uR + 25128 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uT,uP,uR]
      ring
    change 0≤scaledGates (4*p*ell) p s ell (8*p*(ell+1)-8) (4*p*ell+4*ell) (8*p*ell+8*ell) 1 1
    rw [expansion]
    positivity
  · have expansion : scaledGates (4*p*ell) p s ell (8*p*(ell+1)-8) (4*p*ell+4*ell) (8*p*ell+8*ell) 1 2 =
      8192 * uT^8 * uR + 8192 * uT^8 + 20480 * uT^7 * uP * uR
      + 20480 * uT^7 * uP + 61440 * uT^7 * uR + 63488 * uT^7
      + 20480 * uT^6 * uP^2 * uR + 20480 * uT^6 * uP^2 + 135168 * uT^6 * uP * uR
      + 139264 * uT^6 * uP + 198656 * uT^6 * uR + 214016 * uT^6
      + 10240 * uT^5 * uP^3 * uR + 10240 * uT^5 * uP^3 + 116736 * uT^5 * uP^2 * uR
      + 119808 * uT^5 * uP^2 + 376832 * uT^5 * uP * uR + 402944 * uT^5 * uP
      + 361984 * uT^5 * uR + 411392 * uT^5 + 2560 * uT^4 * uP^4 * uR
      + 2560 * uT^4 * uP^4 + 49152 * uT^4 * uP^3 * uR + 50176 * uT^4 * uP^3
      + 273408 * uT^4 * uP^2 * uR + 289536 * uT^4 * uP^2 + 575744 * uT^4 * uP * uR
      + 645248 * uT^4 * uP + 406784 * uT^4 * uR + 495232 * uT^4
      + 256 * uT^3 * uP^5 * uR + 256 * uT^3 * uP^5 + 9984 * uT^3 * uP^4 * uR
      + 10112 * uT^3 * uP^4 + 93184 * uT^3 * uP^3 * uR + 97408 * uT^3 * uP^3
      + 337024 * uT^3 * uP^2 * uR + 371008 * uT^3 * uP^2 + 520960 * uT^3 * uP * uR
      + 619904 * uT^3 * uP + 288640 * uT^3 * uR + 383872 * uT^3
      + 768 * uT^2 * uP^5 * uR + 768 * uT^2 * uP^5 + 14464 * uT^2 * uP^4 * uR
      + 14848 * uT^2 * uP^4 + 87232 * uT^2 * uP^3 * uR + 93792 * uT^2 * uP^3
      + 230720 * uT^2 * uP^2 * uR + 266656 * uT^2 * uP^2 + 279168 * uT^2 * uP * uR
      + 358656 * uT^2 * uP + 126048 * uT^2 * uR + 187824 * uT^2
      + 768 * uT * uP^5 * uR + 768 * uT * uP^5 + 9216 * uT * uP^4 * uR
      + 9600 * uT * uP^4 + 40320 * uT * uP^3 * uR + 44864 * uT * uP^3
      + 83168 * uT * uP^2 * uR + 102240 * uT * uP^2 + 81904 * uT * uP * uR
      + 116120 * uT * uP + 30768 * uT * uR + 53208 * uT
      + 256 * uP^5 * uR + 256 * uP^5 + 2176 * uP^4 * uR
      + 2304 * uP^4 + 7360 * uP^3 * uR + 8544 * uP^3
      + 12320 * uP^2 * uR + 16384 * uP^2 + 10096 * uP * uR
      + 16280 * uP + 3144 * uR + 6696 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uT,uP,uR]
      ring
    change 0≤scaledGates (4*p*ell) p s ell (8*p*(ell+1)-8) (4*p*ell+4*ell) (8*p*ell+8*ell) 1 2
    rw [expansion]
    positivity
  · have expansion : scaledGates (4*p*ell) p s ell (8*p*(ell+1)-8) (4*p*ell+4*ell) (8*p*ell+8*ell) 1 3 =
      8192 * uT^8 * uR + 8192 * uT^8 + 20480 * uT^7 * uP * uR
      + 20480 * uT^7 * uP + 69632 * uT^7 * uR + 67584 * uT^7
      + 20480 * uT^6 * uP^2 * uR + 20480 * uT^6 * uP^2 + 151552 * uT^6 * uP * uR
      + 147456 * uT^6 * uP + 260096 * uT^6 * uR + 244736 * uT^6
      + 10240 * uT^5 * uP^3 * uR + 10240 * uT^5 * uP^3 + 129024 * uT^5 * uP^2 * uR
      + 125952 * uT^5 * uP^2 + 483328 * uT^5 * uP * uR + 457216 * uT^5 * uP
      + 556544 * uT^5 * uR + 507136 * uT^5 + 2560 * uT^4 * uP^4 * uR
      + 2560 * uT^4 * uP^4 + 53248 * uT^4 * uP^3 * uR + 52224 * uT^4 * uP^3
      + 340992 * uT^4 * uP^2 * uR + 324864 * uT^4 * uP^2 + 859392 * uT^4 * uP * uR
      + 789888 * uT^4 * uP + 745216 * uT^4 * uR + 656768 * uT^4
      + 256 * uT^3 * uP^5 * uR + 256 * uT^3 * uP^5 + 10496 * uT^3 * uP^4 * uR
      + 10368 * uT^3 * uP^4 + 111616 * uT^3 * uP^3 * uR + 107392 * uT^3 * uP^3
      + 482944 * uT^3 * uP^2 * uR + 448960 * uT^3 * uP^2 + 918784 * uT^3 * uP * uR
      + 819840 * uT^3 * uP + 639104 * uT^3 * uR + 543872 * uT^3
      + 768 * uT^2 * uP^5 * uR + 768 * uT^2 * uP^5 + 16256 * uT^2 * uP^4 * uR
      + 15872 * uT^2 * uP^4 + 117696 * uT^2 * uP^3 * uR + 111136 * uT^2 * uP^3
      + 385984 * uT^2 * uP^2 * uR + 350048 * uT^2 * uP^2 + 590208 * uT^2 * uP * uR
      + 510720 * uT^2 * uP + 342944 * uT^2 * uR + 281200 * uT^2
      + 768 * uT * uP^5 * uR + 768 * uT * uP^5 + 11264 * uT * uP^4 * uR
      + 10880 * uT * uP^4 + 62336 * uT * uP^3 * uR + 57792 * uT * uP^3
      + 164896 * uT * uP^2 * uR + 145824 * uT * uP^2 + 210960 * uT * uP * uR
      + 176760 * uT * uP + 105424 * uT * uR + 83048 * uT
      + 256 * uP^5 * uR + 256 * uP^5 + 2944 * uP^4 * uR
      + 2816 * uP^4 + 13248 * uP^3 * uR + 12064 * uP^3
      + 29408 * uP^2 * uR + 25344 * uP^2 + 32400 * uP * uR
      + 26232 * uP + 14264 * uR + 10744 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uT,uP,uR]
      ring
    change 0≤scaledGates (4*p*ell) p s ell (8*p*(ell+1)-8) (4*p*ell+4*ell) (8*p*ell+8*ell) 1 3
    rw [expansion]
    positivity
  · have expansion : scaledGates (4*p*ell) p s ell (8*p*(ell+1)-8) (4*p*ell+4*ell) (8*p*ell+8*ell) 1 4 =
      8192 * uT^8 * uR + 8192 * uT^8 + 20480 * uT^7 * uP * uR
      + 20480 * uT^7 * uP + 61440 * uT^7 * uR + 63488 * uT^7
      + 20480 * uT^6 * uP^2 * uR + 20480 * uT^6 * uP^2 + 135168 * uT^6 * uP * uR
      + 139264 * uT^6 * uP + 198656 * uT^6 * uR + 214016 * uT^6
      + 10240 * uT^5 * uP^3 * uR + 10240 * uT^5 * uP^3 + 116736 * uT^5 * uP^2 * uR
      + 119808 * uT^5 * uP^2 + 376832 * uT^5 * uP * uR + 402944 * uT^5 * uP
      + 359936 * uT^5 * uR + 410368 * uT^5 + 2560 * uT^4 * uP^4 * uR
      + 2560 * uT^4 * uP^4 + 49152 * uT^4 * uP^3 * uR + 50176 * uT^4 * uP^3
      + 273408 * uT^4 * uP^2 * uR + 289536 * uT^4 * uP^2 + 572672 * uT^4 * uP * uR
      + 643712 * uT^4 * uP + 396544 * uT^4 * uR + 490112 * uT^4
      + 256 * uT^3 * uP^5 * uR + 256 * uT^3 * uP^5 + 9984 * uT^3 * uP^4 * uR
      + 10112 * uT^3 * uP^4 + 93184 * uT^3 * uP^3 * uR + 97408 * uT^3 * uP^3
      + 335488 * uT^3 * uP^2 * uR + 370240 * uT^3 * uP^2 + 508672 * uT^3 * uP * uR
      + 613760 * uT^3 * uP + 268160 * uT^3 * uR + 373760 * uT^3
      + 768 * uT^2 * uP^5 * uR + 768 * uT^2 * uP^5 + 14464 * uT^2 * uP^4 * uR
      + 14848 * uT^2 * uP^4 + 86976 * uT^2 * uP^3 * uR + 93664 * uT^2 * uP^3
      + 226112 * uT^2 * uP^2 * uR + 264352 * uT^2 * uP^2 + 260736 * uT^2 * uP * uR
      + 349568 * uT^2 * uP + 105568 * uT^2 * uR + 177904 * uT^2
      + 768 * uT * uP^5 * uR + 768 * uT * uP^5 + 9216 * uT * uP^4 * uR
      + 9600 * uT * uP^4 + 39808 * uT * uP^3 * uR + 44608 * uT * uP^3
      + 78560 * uT * uP^2 * uR + 99968 * uT * uP^2 + 69616 * uT * uP * uR
      + 110200 * uT * uP + 20528 * uT * uR + 48344 * uT
      + 256 * uP^5 * uR + 256 * uP^5 + 2176 * uP^4 * uR
      + 2304 * uP^4 + 7104 * uP^3 * uR + 8416 * uP^3
      + 10784 * uP^2 * uR + 15648 * uP^2 + 7024 * uP * uR
      + 14840 * uP + 1096 * uR + 5736 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uT,uP,uR]
      ring
    change 0≤scaledGates (4*p*ell) p s ell (8*p*(ell+1)-8) (4*p*ell+4*ell) (8*p*ell+8*ell) 1 4
    rw [expansion]
    positivity
  · have expansion : scaledGates (4*p*ell) p s ell (8*p*(ell+1)-8) (4*p*ell+4*ell) (8*p*ell+8*ell) 1 5 =
      8192 * uT^8 * uR + 8192 * uT^8 + 20480 * uT^7 * uP * uR
      + 20480 * uT^7 * uP + 69632 * uT^7 * uR + 67584 * uT^7
      + 20480 * uT^6 * uP^2 * uR + 20480 * uT^6 * uP^2 + 151552 * uT^6 * uP * uR
      + 147456 * uT^6 * uP + 260096 * uT^6 * uR + 244736 * uT^6
      + 10240 * uT^5 * uP^3 * uR + 10240 * uT^5 * uP^3 + 129024 * uT^5 * uP^2 * uR
      + 125952 * uT^5 * uP^2 + 483328 * uT^5 * uP * uR + 457216 * uT^5 * uP
      + 557568 * uT^5 * uR + 507648 * uT^5 + 2560 * uT^4 * uP^4 * uR
      + 2560 * uT^4 * uP^4 + 53248 * uT^4 * uP^3 * uR + 52224 * uT^4 * uP^3
      + 340992 * uT^4 * uP^2 * uR + 324864 * uT^4 * uP^2 + 860928 * uT^4 * uP * uR
      + 790656 * uT^4 * uP + 750336 * uT^4 * uR + 659328 * uT^4
      + 256 * uT^3 * uP^5 * uR + 256 * uT^3 * uP^5 + 10496 * uT^3 * uP^4 * uR
      + 10368 * uT^3 * uP^4 + 111616 * uT^3 * uP^3 * uR + 107392 * uT^3 * uP^3
      + 483712 * uT^3 * uP^2 * uR + 449344 * uT^3 * uP^2 + 924928 * uT^3 * uP * uR
      + 822912 * uT^3 * uP + 649344 * uT^3 * uR + 548928 * uT^3
      + 768 * uT^2 * uP^5 * uR + 768 * uT^2 * uP^5 + 16256 * uT^2 * uP^4 * uR
      + 15872 * uT^2 * uP^4 + 117824 * uT^2 * uP^3 * uR + 111200 * uT^2 * uP^3
      + 388288 * uT^2 * uP^2 * uR + 351200 * uT^2 * uP^2 + 599424 * uT^2 * uP * uR
      + 515264 * uT^2 * uP + 353184 * uT^2 * uR + 286160 * uT^2
      + 768 * uT * uP^5 * uR + 768 * uT * uP^5 + 11264 * uT * uP^4 * uR
      + 10880 * uT * uP^4 + 62592 * uT * uP^3 * uR + 57920 * uT * uP^3
      + 167200 * uT * uP^2 * uR + 146960 * uT * uP^2 + 217104 * uT * uP * uR
      + 179720 * uT * uP + 110544 * uT * uR + 85480 * uT
      + 256 * uP^5 * uR + 256 * uP^5 + 2944 * uP^4 * uR
      + 2816 * uP^4 + 13376 * uP^3 * uR + 12128 * uP^3
      + 30176 * uP^2 * uR + 25712 * uP^2 + 33936 * uP * uR
      + 26952 * uP + 15288 * uR + 11224 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uT,uP,uR]
      ring
    change 0≤scaledGates (4*p*ell) p s ell (8*p*(ell+1)-8) (4*p*ell+4*ell) (8*p*ell+8*ell) 1 5
    rw [expansion]
    positivity
  · have expansion : scaledGates (4*p*ell) p s ell (8*p*(ell+1)-8) (4*p*ell+4*ell) (8*p*ell+8*ell) 1 6 =
      49152 * uT^8 * uR + 49152 * uT^8 + 122880 * uT^7 * uP * uR
      + 122880 * uT^7 * uP + 380928 * uT^7 * uR + 380928 * uT^7
      + 122880 * uT^6 * uP^2 * uR + 122880 * uT^6 * uP^2 + 827392 * uT^6 * uP * uR
      + 827392 * uT^6 * uP + 1298432 * uT^6 * uR + 1298432 * uT^6
      + 61440 * uT^5 * uP^3 * uR + 61440 * uT^5 * uP^3 + 702464 * uT^5 * uP^2 * uR
      + 702464 * uT^5 * uP^2 + 2400256 * uT^5 * uP * uR + 2400256 * uT^5 * uP
      + 2545152 * uT^5 * uR + 2545152 * uT^5 + 15360 * uT^4 * uP^4 * uR
      + 15360 * uT^4 * uP^4 + 288768 * uT^4 * uP^3 * uR + 288768 * uT^4 * uP^3
      + 1681408 * uT^4 * uP^2 * uR + 1681408 * uT^4 * uP^2 + 3893504 * uT^4 * uP * uR
      + 3893504 * uT^4 * uP + 3140864 * uT^4 * uR + 3140864 * uT^4
      + 1536 * uT^3 * uP^5 * uR + 1536 * uT^3 * uP^5 + 56576 * uT^3 * uP^4 * uR
      + 56576 * uT^3 * uP^4 + 544768 * uT^3 * uP^3 * uR + 544768 * uT^3 * uP^3
      + 2159744 * uT^3 * uP^2 * uR + 2159744 * uT^3 * uP^2 + 3817984 * uT^3 * uP * uR
      + 3817984 * uT^3 * uP + 2500992 * uT^3 * uR + 2500992 * uT^3
      + 4096 * uT^2 * uP^5 * uR + 4096 * uT^2 * uP^5 + 78080 * uT^2 * uP^4 * uR
      + 78080 * uT^2 * uP^4 + 516288 * uT^2 * uP^3 * uR + 516288 * uT^2 * uP^3
      + 1571904 * uT^2 * uP^2 * uR + 1571904 * uT^2 * uP^2 + 2265472 * uT^2 * uP * uR
      + 2265472 * uT^2 * uP + 1256032 * uT^2 * uR + 1256096 * uT^2
      + 3584 * uT * uP^5 * uR + 3584 * uT * uP^5 + 47872 * uT * uP^4 * uR
      + 47872 * uT * uP^4 + 246080 * uT * uP^3 * uR + 246080 * uT * uP^3
      + 615264 * uT * uP^2 * uR + 615264 * uT * uP^2 + 753904 * uT * uP * uR
      + 753936 * uT * uP + 364064 * uT * uR + 364200 * uT
      + 1024 * uP^5 * uR + 1024 * uP^5 + 11008 * uP^4 * uR
      + 11008 * uP^4 + 47232 * uP^3 * uR + 47232 * uP^3
      + 101280 * uP^2 * uR + 101280 * uP^2 + 108640 * uP * uR
      + 108672 * uP + 46664 * uR + 46752 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uT,uP,uR]
      ring
    change 0≤scaledGates (4*p*ell) p s ell (8*p*(ell+1)-8) (4*p*ell+4*ell) (8*p*ell+8*ell) 1 6
    rw [expansion]
    positivity
  · have expansion : scaledGates (4*p*ell) p s ell (8*p*(ell+1)-8) (4*p*ell+4*ell) (8*p*ell+8*ell) 1 7 =
      65536 * uT^9 * uR + 65536 * uT^9 + 196608 * uT^8 * uP * uR
      + 196608 * uT^8 * uP + 540672 * uT^8 * uR + 540672 * uT^8
      + 245760 * uT^7 * uP^2 * uR + 245760 * uT^7 * uP^2 + 1449984 * uT^7 * uP * uR
      + 1449984 * uT^7 * uP + 1978368 * uT^7 * uR + 1978368 * uT^7
      + 163840 * uT^6 * uP^3 * uR + 163840 * uT^6 * uP^3 + 1597440 * uT^6 * uP^2 * uR
      + 1597440 * uT^6 * uP^2 + 4677632 * uT^6 * uP * uR + 4677632 * uT^6 * uP
      + 4208640 * uT^6 * uR + 4208640 * uT^6 + 61440 * uT^5 * uP^4 * uR
      + 61440 * uT^5 * uP^4 + 921600 * uT^5 * uP^3 * uR + 921600 * uT^5 * uP^3
      + 4458496 * uT^5 * uP^2 * uR + 4458496 * uT^5 * uP^2 + 8613888 * uT^5 * uP * uR
      + 8613888 * uT^5 * uP + 5724672 * uT^5 * uR + 5724672 * uT^5
      + 12288 * uT^4 * uP^5 * uR + 12288 * uT^4 * uP^5 + 291840 * uT^4 * uP^4 * uR
      + 291840 * uT^4 * uP^4 + 2168832 * uT^4 * uP^3 * uR + 2168832 * uT^4 * uP^3
      + 6923264 * uT^4 * uP^2 * uR + 6923264 * uT^4 * uP^2 + 9889536 * uT^4 * uP * uR
      + 9889536 * uT^4 * uP + 5147392 * uT^4 * uR + 5147392 * uT^4
      + 1024 * uT^3 * uP^6 * uR + 1024 * uT^3 * uP^6 + 47616 * uT^3 * uP^5 * uR
      + 47616 * uT^3 * uP^5 + 557824 * uT^3 * uP^4 * uR + 557824 * uT^3 * uP^4
      + 2733056 * uT^3 * uP^3 * uR + 2733056 * uT^3 * uP^3 + 6454144 * uT^3 * uP^2 * uR
      + 6454144 * uT^3 * uP^2 + 7233024 * uT^3 * uP * uR + 7233024 * uT^3 * uP
      + 3045120 * uT^3 * uR + 3045120 * uT^3 + 3072 * uT^2 * uP^6 * uR
      + 3072 * uT^2 * uP^6 + 69632 * uT^2 * uP^5 * uR + 69632 * uT^2 * uP^5
      + 536448 * uT^2 * uP^4 * uR + 536448 * uT^2 * uP^4 + 1944384 * uT^2 * uP^3 * uR
      + 1944384 * uT^2 * uP^3 + 3607488 * uT^2 * uP^2 * uR + 3607488 * uT^2 * uP^2
      + 3280640 * uT^2 * uP * uR + 3280640 * uT^2 * uP + 1134368 * uT^2 * uR
      + 1134304 * uT^2 + 3072 * uT * uP^6 * uR + 3072 * uT * uP^6
      + 45568 * uT * uP^5 * uR + 45568 * uT * uP^5 + 259584 * uT * uP^4 * uR
      + 259584 * uT * uP^4 + 740032 * uT * uP^3 * uR + 740032 * uT * uP^3
      + 1117376 * uT * uP^2 * uR + 1117376 * uT * uP^2 + 839696 * uT * uP * uR
      + 839664 * uT * uP + 238432 * uT * uR + 238296 * uT
      + 1024 * uP^6 * uR + 1024 * uP^6 + 11264 * uP^5 * uR
      + 11264 * uP^5 + 50560 * uP^4 * uR + 50560 * uP^4
      + 117632 * uP^3 * uR + 117632 * uP^3 + 147584 * uP^2 * uR
      + 147584 * uP^2 + 92192 * uP * uR + 92160 * uP
      + 21048 * uR + 20960 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uT,uP,uR]
      ring
    change 0≤scaledGates (4*p*ell) p s ell (8*p*(ell+1)-8) (4*p*ell+4*ell) (8*p*ell+8*ell) 1 7
    rw [expansion]
    positivity
  · have expansion : scaledGates (4*p*ell) p s ell (8*p*(ell+1)-8) (4*p*ell+4*ell) (8*p*ell+8*ell) 1 8 =
      16384 * uT^8 * uR + 16384 * uT^8 + 40960 * uT^7 * uP * uR
      + 40960 * uT^7 * uP + 122880 * uT^7 * uR + 126976 * uT^7
      + 40960 * uT^6 * uP^2 * uR + 40960 * uT^6 * uP^2 + 270336 * uT^6 * uP * uR
      + 278528 * uT^6 * uP + 397312 * uT^6 * uR + 428032 * uT^6
      + 20480 * uT^5 * uP^3 * uR + 20480 * uT^5 * uP^3 + 233472 * uT^5 * uP^2 * uR
      + 239616 * uT^5 * uP^2 + 753664 * uT^5 * uP * uR + 805888 * uT^5 * uP
      + 724480 * uT^5 * uR + 823296 * uT^5 + 5120 * uT^4 * uP^4 * uR
      + 5120 * uT^4 * uP^4 + 98304 * uT^4 * uP^3 * uR + 100352 * uT^4 * uP^3
      + 546816 * uT^4 * uP^2 * uR + 579072 * uT^4 * uP^2 + 1152256 * uT^4 * uP * uR
      + 1291264 * uT^4 * uP + 816384 * uT^4 * uR + 993280 * uT^4
      + 512 * uT^3 * uP^5 * uR + 512 * uT^3 * uP^5 + 19968 * uT^3 * uP^4 * uR
      + 20224 * uT^3 * uP^4 + 186368 * uT^3 * uP^3 * uR + 194816 * uT^3 * uP^3
      + 674432 * uT^3 * uP^2 * uR + 742400 * uT^3 * uP^2 + 1045248 * uT^3 * uP * uR
      + 1243136 * uT^3 * uP + 583552 * uT^3 * uR + 774016 * uT^3
      + 1536 * uT^2 * uP^5 * uR + 1536 * uT^2 * uP^5 + 28928 * uT^2 * uP^4 * uR
      + 29696 * uT^2 * uP^4 + 174528 * uT^2 * uP^3 * uR + 187648 * uT^2 * uP^3
      + 462656 * uT^2 * uP^2 * uR + 534528 * uT^2 * uP^2 + 563840 * uT^2 * uP * uR
      + 722816 * uT^2 * uP + 259168 * uT^2 * uR + 382704 * uT^2
      + 1536 * uT * uP^5 * uR + 1536 * uT * uP^5 + 18432 * uT * uP^4 * uR
      + 19200 * uT * uP^4 + 80768 * uT * uP^3 * uR + 89856 * uT * uP^3
      + 167648 * uT * uP^2 * uR + 205792 * uT * uP^2 + 167920 * uT * uP * uR
      + 236344 * uT * uP + 65584 * uT * uR + 110424 * uT
      + 512 * uP^5 * uR + 512 * uP^5 + 4352 * uP^4 * uR
      + 4608 * uP^4 + 14784 * uP^3 * uR + 17152 * uP^3
      + 25120 * uP^2 * uR + 33248 * uP^2 + 21360 * uP * uR
      + 33720 * uP + 7240 * uR + 14320 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uT,uP,uR]
      ring
    change 0≤scaledGates (4*p*ell) p s ell (8*p*(ell+1)-8) (4*p*ell+4*ell) (8*p*ell+8*ell) 1 8
    rw [expansion]
    positivity
  · have expansion : scaledGates (4*p*ell) p s ell (8*p*(ell+1)-8) (4*p*ell+4*ell) (8*p*ell+8*ell) 1 9 =
      8192 * uT^7 * uR + 4096 * uT^7 + 16384 * uT^6 * uP * uR
      + 8192 * uT^6 * uP + 61440 * uT^6 * uR + 30720 * uT^6
      + 12288 * uT^5 * uP^2 * uR + 6144 * uT^5 * uP^2 + 106496 * uT^5 * uP * uR
      + 54272 * uT^5 * uP + 194048 * uT^5 * uR + 95232 * uT^5
      + 4096 * uT^4 * uP^3 * uR + 2048 * uT^4 * uP^3 + 67584 * uT^4 * uP^2 * uR
      + 35328 * uT^4 * uP^2 + 282880 * uT^4 * uP * uR + 143872 * uT^4 * uP
      + 335616 * uT^4 * uR + 158720 * uT^4 + 512 * uT^3 * uP^4 * uR
      + 256 * uT^3 * uP^4 + 18432 * uT^3 * uP^3 * uR + 9984 * uT^3 * uP^3
      + 145536 * uT^3 * uP^2 * uR + 77568 * uT^3 * uP^2 + 394496 * uT^3 * uP * uR
      + 196608 * uT^3 * uP + 344192 * uT^3 * uR + 153728 * uT^3
      + 1792 * uT^2 * uP^4 * uR + 1024 * uT^2 * uP^4 + 30400 * uT^2 * uP^3 * uR
      + 17280 * uT^2 * uP^3 + 154048 * uT^2 * uP^2 * uR + 82176 * uT^2 * uP^2
      + 305536 * uT^2 * uP * uR + 146560 * uT^2 * uP + 209824 * uT^2 * uR
      + 86320 * uT^2 + 2048 * uT * uP^4 * uR + 1280 * uT * uP^4
      + 21888 * uT * uP^3 * uR + 12800 * uT * uP^3 + 80416 * uT * uP^2 * uR
      + 42272 * uT * uP^2 + 124944 * uT * uP * uR + 56536 * uT * uP
      + 70608 * uT * uR + 25832 * uT + 768 * uP^4 * uR
      + 512 * uP^4 + 5824 * uP^3 * uR + 3456 * uP^3
      + 16608 * uP^2 * uR + 8480 * uP^2 + 21136 * uP * uR
      + 8792 * uP + 10168 * uR + 3120 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uT,uP,uR]
      ring
    change 0≤scaledGates (4*p*ell) p s ell (8*p*(ell+1)-8) (4*p*ell+4*ell) (8*p*ell+8*ell) 1 9
    rw [expansion]
    positivity
  · have expansion : scaledGates (4*p*ell) p s ell (8*p*(ell+1)-8) (4*p*ell+4*ell) (8*p*ell+8*ell) 1 10 =
      16384 * uT^8 * uR + 16384 * uT^8 + 40960 * uT^7 * uP * uR
      + 40960 * uT^7 * uP + 122880 * uT^7 * uR + 126976 * uT^7
      + 40960 * uT^6 * uP^2 * uR + 40960 * uT^6 * uP^2 + 270336 * uT^6 * uP * uR
      + 278528 * uT^6 * uP + 397312 * uT^6 * uR + 428032 * uT^6
      + 20480 * uT^5 * uP^3 * uR + 20480 * uT^5 * uP^3 + 233472 * uT^5 * uP^2 * uR
      + 239616 * uT^5 * uP^2 + 753664 * uT^5 * uP * uR + 805888 * uT^5 * uP
      + 720384 * uT^5 * uR + 821248 * uT^5 + 5120 * uT^4 * uP^4 * uR
      + 5120 * uT^4 * uP^4 + 98304 * uT^4 * uP^3 * uR + 100352 * uT^4 * uP^3
      + 546816 * uT^4 * uP^2 * uR + 579072 * uT^4 * uP^2 + 1146112 * uT^4 * uP * uR
      + 1288192 * uT^4 * uP + 795904 * uT^4 * uR + 983040 * uT^4
      + 512 * uT^3 * uP^5 * uR + 512 * uT^3 * uP^5 + 19968 * uT^3 * uP^4 * uR
      + 20224 * uT^3 * uP^4 + 186368 * uT^3 * uP^3 * uR + 194816 * uT^3 * uP^3
      + 671360 * uT^3 * uP^2 * uR + 740864 * uT^3 * uP^2 + 1020672 * uT^3 * uP * uR
      + 1230848 * uT^3 * uP + 542592 * uT^3 * uR + 753792 * uT^3
      + 1536 * uT^2 * uP^5 * uR + 1536 * uT^2 * uP^5 + 28928 * uT^2 * uP^4 * uR
      + 29696 * uT^2 * uP^4 + 174016 * uT^2 * uP^3 * uR + 187392 * uT^2 * uP^3
      + 453440 * uT^2 * uP^2 * uR + 529920 * uT^2 * uP^2 + 526976 * uT^2 * uP * uR
      + 704640 * uT^2 * uP + 218208 * uT^2 * uR + 362864 * uT^2
      + 1536 * uT * uP^5 * uR + 1536 * uT * uP^5 + 18432 * uT * uP^4 * uR
      + 19200 * uT * uP^4 + 79744 * uT * uP^3 * uR + 89344 * uT * uP^3
      + 158432 * uT * uP^2 * uR + 201248 * uT * uP^2 + 143344 * uT * uP * uR
      + 224504 * uT * uP + 45104 * uT * uR + 100696 * uT
      + 512 * uP^5 * uR + 512 * uP^5 + 4352 * uP^4 * uR
      + 4608 * uP^4 + 14272 * uP^3 * uR + 16896 * uP^3
      + 22048 * uP^2 * uR + 31776 * uP^2 + 15216 * uP * uR
      + 30840 * uP + 3144 * uR + 12392 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uT,uP,uR]
      ring
    change 0≤scaledGates (4*p*ell) p s ell (8*p*(ell+1)-8) (4*p*ell+4*ell) (8*p*ell+8*ell) 1 10
    rw [expansion]
    positivity
  · have expansion : scaledGates (4*p*ell) p s ell (8*p*(ell+1)-8) (4*p*ell+4*ell) (8*p*ell+8*ell) 1 11 =
      16384 * uT^8 * uR + 16384 * uT^8 + 40960 * uT^7 * uP * uR
      + 40960 * uT^7 * uP + 139264 * uT^7 * uR + 135168 * uT^7
      + 40960 * uT^6 * uP^2 * uR + 40960 * uT^6 * uP^2 + 303104 * uT^6 * uP * uR
      + 294912 * uT^6 * uP + 520192 * uT^6 * uR + 489472 * uT^6
      + 20480 * uT^5 * uP^3 * uR + 20480 * uT^5 * uP^3 + 258048 * uT^5 * uP^2 * uR
      + 251904 * uT^5 * uP^2 + 966656 * uT^5 * uP * uR + 914432 * uT^5 * uP
      + 1114624 * uT^5 * uR + 1014784 * uT^5 + 5120 * uT^4 * uP^4 * uR
      + 5120 * uT^4 * uP^4 + 106496 * uT^4 * uP^3 * uR + 104448 * uT^4 * uP^3
      + 681984 * uT^4 * uP^2 * uR + 649728 * uT^4 * uP^2 + 1721088 * uT^4 * uP * uR
      + 1580544 * uT^4 * uP + 1497856 * uT^4 * uR + 1315840 * uT^4
      + 512 * uT^3 * uP^5 * uR + 512 * uT^3 * uP^5 + 20992 * uT^3 * uP^4 * uR
      + 20736 * uT^3 * uP^4 + 223232 * uT^3 * uP^3 * uR + 214784 * uT^3 * uP^3
      + 967040 * uT^3 * uP^2 * uR + 898304 * uT^3 * uP^2 + 1846528 * uT^3 * uP * uR
      + 1642496 * uT^3 * uP + 1292416 * uT^3 * uR + 1091584 * uT^3
      + 1536 * uT^2 * uP^5 * uR + 1536 * uT^2 * uP^5 + 32512 * uT^2 * uP^4 * uR
      + 31744 * uT^2 * uP^4 + 235584 * uT^2 * uP^3 * uR + 222336 * uT^2 * uP^3
      + 775360 * uT^2 * uP^2 * uR + 701184 * uT^2 * uP^2 + 1193344 * uT^2 * uP * uR
      + 1025024 * uT^2 * uP + 699296 * uT^2 * uR + 565264 * uT^2
      + 1536 * uT * uP^5 * uR + 1536 * uT * uP^5 + 22528 * uT * uP^4 * uR
      + 21760 * uT * uP^4 + 125056 * uT * uP^3 * uR + 115712 * uT * uP^3
      + 333088 * uT * uP^2 * uR + 292608 * uT * uP^2 + 430096 * uT * uP * uR
      + 355336 * uT * uP + 217040 * uT * uR + 166952 * uT
      + 512 * uP^5 * uR + 512 * uP^5 + 5888 * uP^4 * uR
      + 5632 * uP^4 + 26688 * uP^3 * uR + 24192 * uP^3
      + 59872 * uP^2 * uR + 50944 * uP^2 + 66704 * uP * uR
      + 52744 * uP + 29624 * uR + 21528 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uT,uP,uR]
      ring
    change 0≤scaledGates (4*p*ell) p s ell (8*p*(ell+1)-8) (4*p*ell+4*ell) (8*p*ell+8*ell) 1 11
    rw [expansion]
    positivity

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail
