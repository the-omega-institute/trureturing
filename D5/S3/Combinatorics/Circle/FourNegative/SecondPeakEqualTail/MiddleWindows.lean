/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTail/MiddleWindows
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
private theorem middle_windows (p s : ℤ) (hp : 4≤p) (hs : 1≤s) :
    ∀ i : Fin 12, 0≤scaledGates (2*p) p s 0 (8*p-8) (2*p+4) (4*p+8) 1 i := by
  let uP := p-4
  have huP : 0≤uP := by dsimp [uP]; omega
  let uR := s-1
  have huR : 0≤uR := by dsimp [uR]; omega
  intro i
  fin_cases i
  · have expansion : scaledGates (2*p) p s 0 (8*p-8) (2*p+4) (4*p+8) 1 0 =
      96 * uP^4 * uR + 96 * uP^4 + 1504 * uP^3 * uR
      + 1504 * uP^3 + 8880 * uP^2 * uR + 8880 * uP^2
      + 23408 * uP * uR + 23408 * uP + 23240 * uR
      + 23248 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uP,uR]
      ring
    change 0≤scaledGates (2*p) p s 0 (8*p-8) (2*p+4) (4*p+8) 1 0
    rw [expansion]
    positivity
  · have expansion : scaledGates (2*p) p s 0 (8*p-8) (2*p+4) (4*p+8) 1 1 =
      64 * uP^6 * uR + 64 * uP^6 + 1536 * uP^5 * uR
      + 1536 * uP^5 + 15296 * uP^4 * uR + 15296 * uP^4
      + 80928 * uP^3 * uR + 80928 * uP^3 + 239968 * uP^2 * uR
      + 239968 * uP^2 + 378128 * uP * uR + 378128 * uP
      + 247352 * uR + 247344 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uP,uR]
      ring
    change 0≤scaledGates (2*p) p s 0 (8*p-8) (2*p+4) (4*p+8) 1 1
    rw [expansion]
    positivity
  · have expansion : scaledGates (2*p) p s 0 (8*p-8) (2*p+4) (4*p+8) 1 2 =
      32 * uP^5 * uR + 32 * uP^5 + 544 * uP^4 * uR
      + 560 * uP^4 + 3632 * uP^3 * uR + 3928 * uP^3
      + 11792 * uP^2 * uR + 13824 * uP^2 + 18296 * uP * uR
      + 24460 * uP + 10440 * uR + 17448 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uP,uR]
      ring
    change 0≤scaledGates (2*p) p s 0 (8*p-8) (2*p+4) (4*p+8) 1 2
    rw [expansion]
    positivity
  · have expansion : scaledGates (2*p) p s 0 (8*p-8) (2*p+4) (4*p+8) 1 3 =
      32 * uP^5 * uR + 32 * uP^5 + 736 * uP^4 * uR
      + 720 * uP^4 + 6640 * uP^3 * uR + 6344 * uP^3
      + 29552 * uP^2 * uR + 27520 * uP^2 + 65160 * uP * uR
      + 59004 * uP + 57144 * uR + 50168 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uP,uR]
      ring
    change 0≤scaledGates (2*p) p s 0 (8*p-8) (2*p+4) (4*p+8) 1 3
    rw [expansion]
    positivity
  · have expansion : scaledGates (2*p) p s 0 (8*p-8) (2*p+4) (4*p+8) 1 4 =
      32 * uP^5 * uR + 32 * uP^5 + 544 * uP^4 * uR
      + 560 * uP^4 + 3568 * uP^3 * uR + 3896 * uP^3
      + 11024 * uP^2 * uR + 13456 * uP^2 + 15224 * uP * uR
      + 23036 * uP + 6344 * uR + 15592 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uP,uR]
      ring
    change 0≤scaledGates (2*p) p s 0 (8*p-8) (2*p+4) (4*p+8) 1 4
    rw [expansion]
    positivity
  · have expansion : scaledGates (2*p) p s 0 (8*p-8) (2*p+4) (4*p+8) 1 5 =
      32 * uP^5 * uR + 32 * uP^5 + 736 * uP^4 * uR
      + 720 * uP^4 + 6672 * uP^3 * uR + 6360 * uP^3
      + 29936 * uP^2 * uR + 27704 * uP^2 + 66696 * uP * uR
      + 59716 * uP + 59192 * uR + 51096 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uP,uR]
      ring
    change 0≤scaledGates (2*p) p s 0 (8*p-8) (2*p+4) (4*p+8) 1 5
    rw [expansion]
    positivity
  · have expansion : scaledGates (2*p) p s 0 (8*p-8) (2*p+4) (4*p+8) 1 6 =
      128 * uP^5 * uR + 128 * uP^5 + 2688 * uP^4 * uR
      + 2688 * uP^4 + 22560 * uP^3 * uR + 22560 * uP^3
      + 94640 * uP^2 * uR + 94640 * uP^2 + 198512 * uP * uR
      + 198528 * uP + 166600 * uR + 166680 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uP,uR]
      ring
    change 0≤scaledGates (2*p) p s 0 (8*p-8) (2*p+4) (4*p+8) 1 6
    rw [expansion]
    positivity
  · have expansion : scaledGates (2*p) p s 0 (8*p-8) (2*p+4) (4*p+8) 1 7 =
      128 * uP^6 * uR + 128 * uP^6 + 2944 * uP^5 * uR
      + 2944 * uP^5 + 28064 * uP^4 * uR + 28064 * uP^4
      + 141792 * uP^3 * uR + 141792 * uP^3 + 399968 * uP^2 * uR
      + 399968 * uP^2 + 596240 * uP * uR + 596224 * uP
      + 366136 * uR + 366056 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uP,uR]
      ring
    change 0≤scaledGates (2*p) p s 0 (8*p-8) (2*p+4) (4*p+8) 1 7
    rw [expansion]
    positivity
  · have expansion : scaledGates (2*p) p s 0 (8*p-8) (2*p+4) (4*p+8) 1 8 =
      64 * uP^5 * uR + 64 * uP^5 + 1088 * uP^4 * uR
      + 1120 * uP^4 + 7280 * uP^3 * uR + 7872 * uP^3
      + 23824 * uP^2 * uR + 27888 * uP^2 + 37752 * uP * uR
      + 50076 * uP + 22728 * uR + 36720 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uP,uR]
      ring
    change 0≤scaledGates (2*p) p s 0 (8*p-8) (2*p+4) (4*p+8) 1 8
    rw [expansion]
    positivity
  · have expansion : scaledGates (2*p) p s 0 (8*p-8) (2*p+4) (4*p+8) 1 9 =
      192 * uP^4 * uR + 160 * uP^4 + 2992 * uP^3 * uR
      + 2400 * uP^3 + 17520 * uP^2 * uR + 13456 * uP^2
      + 45704 * uP * uR + 33388 * uP + 44856 * uR
      + 30896 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uP,uR]
      ring
    change 0≤scaledGates (2*p) p s 0 (8*p-8) (2*p+4) (4*p+8) 1 9
    rw [expansion]
    positivity
  · have expansion : scaledGates (2*p) p s 0 (8*p-8) (2*p+4) (4*p+8) 1 10 =
      64 * uP^5 * uR + 64 * uP^5 + 1088 * uP^4 * uR
      + 1120 * uP^4 + 7152 * uP^3 * uR + 7808 * uP^3
      + 22288 * uP^2 * uR + 27152 * uP^2 + 31608 * uP * uR
      + 47228 * uP + 14536 * uR + 33000 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uP,uR]
      ring
    change 0≤scaledGates (2*p) p s 0 (8*p-8) (2*p+4) (4*p+8) 1 10
    rw [expansion]
    positivity
  · have expansion : scaledGates (2*p) p s 0 (8*p-8) (2*p+4) (4*p+8) 1 11 =
      64 * uP^5 * uR + 64 * uP^5 + 1472 * uP^4 * uR
      + 1440 * uP^4 + 13328 * uP^3 * uR + 12704 * uP^3
      + 59632 * uP^2 * uR + 55168 * uP^2 + 132232 * uP * uR
      + 118276 * uP + 116536 * uR + 100376 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uP,uR]
      ring
    change 0≤scaledGates (2*p) p s 0 (8*p-8) (2*p+4) (4*p+8) 1 11
    rw [expansion]
    positivity

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail
