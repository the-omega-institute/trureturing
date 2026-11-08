/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTail/SpecialWindows
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
private theorem special_high_windows (s : ℤ) (hs : 2≤s) :
    ∀ i : Fin 12, 0≤scaledGates 4 2 s 0 8 4 8 1 i := by
  let uR := s-2
  have huR : 0≤uR := by dsimp [uR]; omega
  intro i
  fin_cases i
  · have expansion : scaledGates 4 2 s 0 8 4 8 1 0 =
      1448 * uR + 2904 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uR]
      ring
    change 0≤scaledGates 4 2 s 0 8 4 8 1 0
    rw [expansion]
    positivity
  · have expansion : scaledGates 4 2 s 0 8 4 8 1 1 =
      3224 * uR + 6440 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uR]
      ring
    change 0≤scaledGates 4 2 s 0 8 4 8 1 1
    rw [expansion]
    positivity
  · have expansion : scaledGates 4 2 s 0 8 4 8 1 2 =
      808 * uR + 1984 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uR]
      ring
    change 0≤scaledGates 4 2 s 0 8 4 8 1 2
    rw [expansion]
    positivity
  · have expansion : scaledGates 4 2 s 0 8 4 8 1 3 =
      1496 * uR + 2640 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uR]
      ring
    change 0≤scaledGates 4 2 s 0 8 4 8 1 3
    rw [expansion]
    positivity
  · have expansion : scaledGates 4 2 s 0 8 4 8 1 4 =
      296 * uR + 1248 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uR]
      ring
    change 0≤scaledGates 4 2 s 0 8 4 8 1 4
    rw [expansion]
    positivity
  · have expansion : scaledGates 4 2 s 0 8 4 8 1 5 =
      1752 * uR + 3008 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uR]
      ring
    change 0≤scaledGates 4 2 s 0 8 4 8 1 5
    rw [expansion]
    positivity
  · have expansion : scaledGates 4 2 s 0 8 4 8 1 6 =
      6568 * uR + 13184 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uR]
      ring
    change 0≤scaledGates 4 2 s 0 8 4 8 1 6
    rw [expansion]
    positivity
  · have expansion : scaledGates 4 2 s 0 8 4 8 1 7 =
      2200 * uR + 4352 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uR]
      ring
    change 0≤scaledGates 4 2 s 0 8 4 8 1 7
    rw [expansion]
    positivity
  · have expansion : scaledGates 4 2 s 0 8 4 8 1 8 =
      1832 * uR + 4392 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uR]
      ring
    change 0≤scaledGates 4 2 s 0 8 4 8 1 8
    rw [expansion]
    positivity
  · have expansion : scaledGates 4 2 s 0 8 4 8 1 9 =
      472 * uR + 232 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uR]
      ring
    change 0≤scaledGates 4 2 s 0 8 4 8 1 9
    rw [expansion]
    positivity
  · have expansion : scaledGates 4 2 s 0 8 4 8 1 10 =
      808 * uR + 2912 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uR]
      ring
    change 0≤scaledGates 4 2 s 0 8 4 8 1 10
    rw [expansion]
    positivity
  · have expansion : scaledGates 4 2 s 0 8 4 8 1 11 =
      3288 * uR + 5600 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uR]
      ring
    change 0≤scaledGates 4 2 s 0 8 4 8 1 11
    rw [expansion]
    positivity

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail
