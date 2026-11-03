/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakAdjacentTail/PlusThreeAtFour
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakAdjacentTail/PlusThreeAtFour
   mirror-E: none(waiver:adjacent-tail-physical-source)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Exact polynomial inequalities for adjacent-tail mask selection. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.Algebra
import Batteries.Tactic.OpenPrivate

set_option maxErrors 1
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.PlusThree
open private A B L K SU SV SW E F Common Residual StocksAndResidual HighResidual Windows ceilDiv residueRepresentative chooseM3 chooseV2 chooseM2
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.Algebra

private theorem small_a4_cmod0 (T : ℚ)
    (hT : 0 ≤ T) :
    Residual (16) ((256 + (17 * T))) (8) (1) ((106 + (8 * T))) := by
  try dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- m_lower
    have identity : (((106 + (8 * T))) : ℚ) = ((8 * T) + 106) := by ring
    have scaling : ((1) * ((106 + (8 * T))) : ℚ) = ((106 + (8 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((8 * T) + 106) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (106 + (8 * T)) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (106 + (8 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- m_stock
    have identity : (((917 + (60 * T))) : ℚ) = ((60 * T) + 917) := by ring
    have scaling : ((1) * ((917 + (60 * T))) : ℚ) = ((917 + (60 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((60 * T) + 917) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (917 + (60 * T)) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (917 + (60 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- ceil_lower
    have identity : (((829035 + (3604 * (T ^ 2)) + (109326 * T))) : ℚ) = ((3604 * (T ^ 2)) + (109326 * T) + 829035) := by ring
    have scaling : ((1) * ((15361 + ((-16) * ((256 + (17 * T)) ^ 3)) + (504 * ((256 + (17 * T)) ^ 2)) + (1020 * T) + ((106 + (8 * T)) * (257 + (17 * T) + (34 * ((256 + (17 * T)) ^ 2)))))) : ℚ) = ((829035 + (3604 * (T ^ 2)) + (109326 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((3604 * (T ^ 2)) + (109326 * T) + 829035) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (15361 + ((-16) * ((256 + (17 * T)) ^ 3)) + (504 * ((256 + (17 * T)) ^ 2)) + (1020 * T) + ((106 + (8 * T)) * (257 + (17 * T) + (34 * ((256 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (15361 + ((-16) * ((256 + (17 * T)) ^ 3)) + (504 * ((256 + (17 * T)) ^ 2)) + (1020 * T) + ((106 + (8 * T)) * (257 + (17 * T) + (34 * ((256 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- ceil_upper
    have identity : (((1399445 + (6222 * (T ^ 2)) + (186627 * T))) : ℚ) = ((6222 * (T ^ 2)) + (186627 * T) + 1399445) := by ring
    have scaling : ((1) * (((-15105) + ((-1003) * T) + ((-470) * ((256 + (17 * T)) ^ 2)) + (16 * ((256 + (17 * T)) ^ 3)) + ((-1) * (106 + (8 * T)) * (257 + (17 * T) + (34 * ((256 + (17 * T)) ^ 2)))))) : ℚ) = ((1399445 + (6222 * (T ^ 2)) + (186627 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((6222 * (T ^ 2)) + (186627 * T) + 1399445) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-15105) + ((-1003) * T) + ((-470) * ((256 + (17 * T)) ^ 2)) + (16 * ((256 + (17 * T)) ^ 3)) + ((-1) * (106 + (8 * T)) * (257 + (17 * T) + (34 * ((256 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ ((-15105) + ((-1003) * T) + ((-470) * ((256 + (17 * T)) ^ 2)) + (16 * ((256 + (17 * T)) ^ 3)) + ((-1) * (106 + (8 * T)) * (257 + (17 * T) + (34 * ((256 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- second_old_upper
    have identity : (((6763322 + (29784 * (T ^ 2)) + (897636 * T))) : ℚ) = ((29784 * (T ^ 2)) + (897636 * T) + 6763322) := by ring
    have scaling : ((1) * ((2062 + ((-880) * ((256 + (17 * T)) ^ 2)) + (32 * ((256 + (17 * T)) ^ 3)) + (136 * T) + ((-2) * (106 + (8 * T)) * (257 + (17 * T) + (34 * ((256 + (17 * T)) ^ 2)))))) : ℚ) = ((6763322 + (29784 * (T ^ 2)) + (897636 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((29784 * (T ^ 2)) + (897636 * T) + 6763322) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (2062 + ((-880) * ((256 + (17 * T)) ^ 2)) + (32 * ((256 + (17 * T)) ^ 3)) + (136 * T) + ((-2) * (106 + (8 * T)) * (257 + (17 * T) + (34 * ((256 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (2062 + ((-880) * ((256 + (17 * T)) ^ 2)) + (32 * ((256 + (17 * T)) ^ 3)) + (136 * T) + ((-2) * (106 + (8 * T)) * (257 + (17 * T) + (34 * ((256 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- second_new_lower
    have identity : (((2157163 + (9384 * (T ^ 2)) + (284562 * T))) : ℚ) = ((9384 * (T ^ 2)) + (284562 * T) + 2157163) := by ring
    have scaling : ((1) * ((32769 + ((-32) * ((256 + (17 * T)) ^ 3)) + (1016 * ((256 + (17 * T)) ^ 2)) + (2176 * T) + ((106 + (8 * T)) * (257 + (17 * T) + (68 * ((256 + (17 * T)) ^ 2)))))) : ℚ) = ((2157163 + (9384 * (T ^ 2)) + (284562 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((9384 * (T ^ 2)) + (284562 * T) + 2157163) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (32769 + ((-32) * ((256 + (17 * T)) ^ 3)) + (1016 * ((256 + (17 * T)) ^ 2)) + (2176 * T) + ((106 + (8 * T)) * (257 + (17 * T) + (68 * ((256 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (32769 + ((-32) * ((256 + (17 * T)) ^ 3)) + (1016 * ((256 + (17 * T)) ^ 2)) + (2176 * T) + ((106 + (8 * T)) * (257 + (17 * T) + (68 * ((256 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- second_new_upper
    have identity : (((4107066 + (18224 * (T ^ 2)) + (547164 * T))) : ℚ) = ((18224 * (T ^ 2)) + (547164 * T) + 4107066) := by ring
    have scaling : ((1) * (((-32754) + ((-2176) * T) + ((-1904) * ((256 + (17 * T)) ^ 2)) + (64 * ((256 + (17 * T)) ^ 3)) + ((-2) * (106 + (8 * T)) * (257 + (17 * T) + (68 * ((256 + (17 * T)) ^ 2)))))) : ℚ) = ((4107066 + (18224 * (T ^ 2)) + (547164 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((18224 * (T ^ 2)) + (547164 * T) + 4107066) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-32754) + ((-2176) * T) + ((-1904) * ((256 + (17 * T)) ^ 2)) + (64 * ((256 + (17 * T)) ^ 3)) + ((-2) * (106 + (8 * T)) * (257 + (17 * T) + (68 * ((256 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ ((-32754) + ((-2176) * T) + ((-1904) * ((256 + (17 * T)) ^ 2)) + (64 * ((256 + (17 * T)) ^ 3)) + ((-2) * (106 + (8 * T)) * (257 + (17 * T) + (68 * ((256 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- third_old_upper
    have identity : (((206275070 + (78608 * (T ^ 3)) + (3277260 * (T ^ 2)) + (45223842 * T))) : ℚ) = ((78608 * (T ^ 3)) + (3277260 * (T ^ 2)) + (45223842 * T) + 206275070) := by ring
    have scaling : ((1) * (((-32258) + ((-2142) * T) + ((-948) * ((256 + (17 * T)) ^ 2)) + (16 * ((256 + (17 * T)) ^ 3)))) : ℚ) = ((206275070 + (78608 * (T ^ 3)) + (3277260 * (T ^ 2)) + (45223842 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((78608 * (T ^ 3)) + (3277260 * (T ^ 2)) + (45223842 * T) + 206275070) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-32258) + ((-2142) * T) + ((-948) * ((256 + (17 * T)) ^ 2)) + (16 * ((256 + (17 * T)) ^ 3))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ ((-32258) + ((-2142) * T) + ((-948) * ((256 + (17 * T)) ^ 2)) + (16 * ((256 + (17 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- third_new_upper
    have identity : (((412023294 + (157216 * (T ^ 3)) + (6552208 * (T ^ 2)) + (90377882 * T))) : ℚ) = ((157216 * (T ^ 3)) + (6552208 * (T ^ 2)) + (90377882 * T) + 412023294) := by ring
    have scaling : ((1) * (((-67074) + ((-4454) * T) + ((-1904) * ((256 + (17 * T)) ^ 2)) + (32 * ((256 + (17 * T)) ^ 3)))) : ℚ) = ((412023294 + (157216 * (T ^ 3)) + (6552208 * (T ^ 2)) + (90377882 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((157216 * (T ^ 3)) + (6552208 * (T ^ 2)) + (90377882 * T) + 412023294) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-67074) + ((-4454) * T) + ((-1904) * ((256 + (17 * T)) ^ 2)) + (32 * ((256 + (17 * T)) ^ 3))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ ((-67074) + ((-4454) * T) + ((-1904) * ((256 + (17 * T)) ^ 2)) + (32 * ((256 + (17 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring

private theorem small_a4_cmod1 (T : ℚ)
    (hT : 0 ≤ T) :
    Residual (16) ((512 + (17 * T))) (8) (0) ((234 + (8 * T))) := by
  try dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- m_lower
    have identity : (((234 + (8 * T))) : ℚ) = ((8 * T) + 234) := by ring
    have scaling : ((1) * ((234 + (8 * T))) : ℚ) = ((234 + (8 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((8 * T) + 234) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (234 + (8 * T)) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (234 + (8 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- m_stock
    have identity : (((1813 + (60 * T))) : ℚ) = ((60 * T) + 1813) := by ring
    have scaling : ((1) * ((1813 + (60 * T))) : ℚ) = ((1813 + (60 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((60 * T) + 1813) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (1813 + (60 * T)) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (1813 + (60 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- ceil_lower
    have identity : (((3279082 + (3604 * (T ^ 2)) + (217420 * T))) : ℚ) = ((3604 * (T ^ 2)) + (217420 * T) + 3279082) := by ring
    have scaling : ((1) * ((13312 + ((-16) * ((512 + (17 * T)) ^ 3)) + (248 * ((512 + (17 * T)) ^ 2)) + (442 * T) + ((234 + (8 * T)) * (513 + (17 * T) + (34 * ((512 + (17 * T)) ^ 2)))))) : ℚ) = ((3279082 + (3604 * (T ^ 2)) + (217420 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((3604 * (T ^ 2)) + (217420 * T) + 3279082) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (13312 + ((-16) * ((512 + (17 * T)) ^ 3)) + (248 * ((512 + (17 * T)) ^ 2)) + (442 * T) + ((234 + (8 * T)) * (513 + (17 * T) + (34 * ((512 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (13312 + ((-16) * ((512 + (17 * T)) ^ 3)) + (248 * ((512 + (17 * T)) ^ 2)) + (442 * T) + ((234 + (8 * T)) * (513 + (17 * T) + (34 * ((512 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- ceil_upper
    have identity : (((5634326 + (6222 * (T ^ 2)) + (374469 * T))) : ℚ) = ((6222 * (T ^ 2)) + (374469 * T) + 5634326) := by ring
    have scaling : ((1) * (((-12800) + ((-425) * T) + ((-214) * ((512 + (17 * T)) ^ 2)) + (16 * ((512 + (17 * T)) ^ 3)) + ((-1) * (234 + (8 * T)) * (513 + (17 * T) + (34 * ((512 + (17 * T)) ^ 2)))))) : ℚ) = ((5634326 + (6222 * (T ^ 2)) + (374469 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((6222 * (T ^ 2)) + (374469 * T) + 5634326) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-12800) + ((-425) * T) + ((-214) * ((512 + (17 * T)) ^ 2)) + (16 * ((512 + (17 * T)) ^ 3)) + ((-1) * (234 + (8 * T)) * (513 + (17 * T) + (34 * ((512 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ ((-12800) + ((-425) * T) + ((-214) * ((512 + (17 * T)) ^ 2)) + (16 * ((512 + (17 * T)) ^ 3)) + ((-1) * (234 + (8 * T)) * (513 + (17 * T) + (34 * ((512 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- second_old_upper
    have identity : (((27061820 + (29784 * (T ^ 2)) + (1795560 * T))) : ℚ) = ((29784 * (T ^ 2)) + (1795560 * T) + 27061820) := by ring
    have scaling : ((1) * ((38928 + ((-368) * ((512 + (17 * T)) ^ 2)) + (32 * ((512 + (17 * T)) ^ 3)) + (1292 * T) + ((-2) * (234 + (8 * T)) * (513 + (17 * T) + (34 * ((512 + (17 * T)) ^ 2)))))) : ℚ) = ((27061820 + (29784 * (T ^ 2)) + (1795560 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((29784 * (T ^ 2)) + (1795560 * T) + 27061820) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (38928 + ((-368) * ((512 + (17 * T)) ^ 2)) + (32 * ((512 + (17 * T)) ^ 3)) + (1292 * T) + ((-2) * (234 + (8 * T)) * (513 + (17 * T) + (34 * ((512 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (38928 + ((-368) * ((512 + (17 * T)) ^ 2)) + (32 * ((512 + (17 * T)) ^ 3)) + (1292 * T) + ((-2) * (234 + (8 * T)) * (513 + (17 * T) + (34 * ((512 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- second_new_lower
    have identity : (((8539370 + (9384 * (T ^ 2)) + (566158 * T))) : ℚ) = ((9384 * (T ^ 2)) + (566158 * T) + 8539370) := by ring
    have scaling : ((1) * ((30720 + ((-32) * ((512 + (17 * T)) ^ 3)) + (504 * ((512 + (17 * T)) ^ 2)) + (1020 * T) + ((234 + (8 * T)) * (513 + (17 * T) + (68 * ((512 + (17 * T)) ^ 2)))))) : ℚ) = ((8539370 + (9384 * (T ^ 2)) + (566158 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((9384 * (T ^ 2)) + (566158 * T) + 8539370) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (30720 + ((-32) * ((512 + (17 * T)) ^ 3)) + (504 * ((512 + (17 * T)) ^ 2)) + (1020 * T) + ((234 + (8 * T)) * (513 + (17 * T) + (68 * ((512 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (30720 + ((-32) * ((512 + (17 * T)) ^ 3)) + (504 * ((512 + (17 * T)) ^ 2)) + (1020 * T) + ((234 + (8 * T)) * (513 + (17 * T) + (68 * ((512 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- second_new_upper
    have identity : (((16541244 + (18224 * (T ^ 2)) + (1098084 * T))) : ℚ) = ((18224 * (T ^ 2)) + (1098084 * T) + 16541244) := by ring
    have scaling : ((1) * ((4112 + ((-880) * ((512 + (17 * T)) ^ 2)) + (64 * ((512 + (17 * T)) ^ 3)) + (136 * T) + ((-2) * (234 + (8 * T)) * (513 + (17 * T) + (68 * ((512 + (17 * T)) ^ 2)))))) : ℚ) = ((16541244 + (18224 * (T ^ 2)) + (1098084 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((18224 * (T ^ 2)) + (1098084 * T) + 16541244) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (4112 + ((-880) * ((512 + (17 * T)) ^ 2)) + (64 * ((512 + (17 * T)) ^ 3)) + (136 * T) + ((-2) * (234 + (8 * T)) * (513 + (17 * T) + (68 * ((512 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (4112 + ((-880) * ((512 + (17 * T)) ^ 2)) + (64 * ((512 + (17 * T)) ^ 3)) + (136 * T) + ((-2) * (234 + (8 * T)) * (513 + (17 * T) + (68 * ((512 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- third_old_upper
    have identity : (((2033159168 + (78608 * (T ^ 3)) + (6976460 * (T ^ 2)) + (206318630 * T))) : ℚ) = ((78608 * (T ^ 3)) + (6976460 * (T ^ 2)) + (206318630 * T) + 2033159168) := by ring
    have scaling : ((1) * (((-29696) + ((-986) * T) + ((-436) * ((512 + (17 * T)) ^ 2)) + (16 * ((512 + (17 * T)) ^ 3)))) : ℚ) = ((2033159168 + (78608 * (T ^ 3)) + (6976460 * (T ^ 2)) + (206318630 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((78608 * (T ^ 3)) + (6976460 * (T ^ 2)) + (206318630 * T) + 2033159168) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-29696) + ((-986) * T) + ((-436) * ((512 + (17 * T)) ^ 2)) + (16 * ((512 + (17 * T)) ^ 3))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ ((-29696) + ((-986) * T) + ((-436) * ((512 + (17 * T)) ^ 2)) + (16 * ((512 + (17 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- third_new_upper
    have identity : (((4064216064 + (157216 * (T ^ 3)) + (13950608 * (T ^ 2)) + (412497826 * T))) : ℚ) = ((157216 * (T ^ 3)) + (13950608 * (T ^ 2)) + (412497826 * T) + 4064216064) := by ring
    have scaling : ((1) * (((-64512) + ((-2142) * T) + ((-880) * ((512 + (17 * T)) ^ 2)) + (32 * ((512 + (17 * T)) ^ 3)))) : ℚ) = ((4064216064 + (157216 * (T ^ 3)) + (13950608 * (T ^ 2)) + (412497826 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((157216 * (T ^ 3)) + (13950608 * (T ^ 2)) + (412497826 * T) + 4064216064) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-64512) + ((-2142) * T) + ((-880) * ((512 + (17 * T)) ^ 2)) + (32 * ((512 + (17 * T)) ^ 3))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ ((-64512) + ((-2142) * T) + ((-880) * ((512 + (17 * T)) ^ 2)) + (32 * ((512 + (17 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring

private theorem small_a4_cmod2 (T : ℚ)
    (hT : 0 ≤ T) :
    Residual (16) ((1024 + (17 * T))) (8) (0) ((475 + (8 * T))) := by
  try dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- m_lower
    have identity : (((475 + (8 * T))) : ℚ) = ((8 * T) + 475) := by ring
    have scaling : ((1) * ((475 + (8 * T))) : ℚ) = ((475 + (8 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((8 * T) + 475) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (475 + (8 * T)) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (475 + (8 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- m_stock
    have identity : (((3620 + (60 * T))) : ℚ) = ((60 * T) + 3620) := by ring
    have scaling : ((1) * ((3620 + (60 * T))) : ℚ) = ((3620 + (60 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((60 * T) + 3620) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (3620 + (60 * T)) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (3620 + (60 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- ceil_lower
    have identity : (((15193563 + (4182 * (T ^ 2)) + (504141 * T))) : ℚ) = ((4182 * (T ^ 2)) + (504141 * T) + 15193563) := by ring
    have scaling : ((1) * ((26624 + ((-16) * ((1024 + (17 * T)) ^ 3)) + (248 * ((1024 + (17 * T)) ^ 2)) + (442 * T) + ((475 + (8 * T)) * (1025 + (17 * T) + (34 * ((1024 + (17 * T)) ^ 2)))))) : ℚ) = ((15193563 + (4182 * (T ^ 2)) + (504141 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((4182 * (T ^ 2)) + (504141 * T) + 15193563) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (26624 + ((-16) * ((1024 + (17 * T)) ^ 3)) + (248 * ((1024 + (17 * T)) ^ 2)) + (442 * T) + ((475 + (8 * T)) * (1025 + (17 * T) + (34 * ((1024 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (26624 + ((-16) * ((1024 + (17 * T)) ^ 3)) + (248 * ((1024 + (17 * T)) ^ 2)) + (442 * T) + ((475 + (8 * T)) * (1025 + (17 * T) + (34 * ((1024 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- ceil_upper
    have identity : (((20459045 + (5644 * (T ^ 2)) + (679620 * T))) : ℚ) = ((5644 * (T ^ 2)) + (679620 * T) + 20459045) := by ring
    have scaling : ((1) * (((-25600) + ((-425) * T) + ((-214) * ((1024 + (17 * T)) ^ 2)) + (16 * ((1024 + (17 * T)) ^ 3)) + ((-1) * (475 + (8 * T)) * (1025 + (17 * T) + (34 * ((1024 + (17 * T)) ^ 2)))))) : ℚ) = ((20459045 + (5644 * (T ^ 2)) + (679620 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((5644 * (T ^ 2)) + (679620 * T) + 20459045) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-25600) + ((-425) * T) + ((-214) * ((1024 + (17 * T)) ^ 2)) + (16 * ((1024 + (17 * T)) ^ 3)) + ((-1) * (475 + (8 * T)) * (1025 + (17 * T) + (34 * ((1024 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ ((-25600) + ((-425) * T) + ((-214) * ((1024 + (17 * T)) ^ 2)) + (16 * ((1024 + (17 * T)) ^ 3)) + ((-1) * (475 + (8 * T)) * (1025 + (17 * T) + (34 * ((1024 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- second_old_upper
    have identity : (((103961690 + (28628 * (T ^ 2)) + (3450342 * T))) : ℚ) = ((28628 * (T ^ 2)) + (3450342 * T) + 103961690) := by ring
    have scaling : ((1) * ((77840 + ((-368) * ((1024 + (17 * T)) ^ 2)) + (32 * ((1024 + (17 * T)) ^ 3)) + (1292 * T) + ((-2) * (475 + (8 * T)) * (1025 + (17 * T) + (34 * ((1024 + (17 * T)) ^ 2)))))) : ℚ) = ((103961690 + (28628 * (T ^ 2)) + (3450342 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((28628 * (T ^ 2)) + (3450342 * T) + 103961690) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (77840 + ((-368) * ((1024 + (17 * T)) ^ 2)) + (32 * ((1024 + (17 * T)) ^ 3)) + (1292 * T) + ((-2) * (475 + (8 * T)) * (1025 + (17 * T) + (34 * ((1024 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (77840 + ((-368) * ((1024 + (17 * T)) ^ 2)) + (32 * ((1024 + (17 * T)) ^ 3)) + (1292 * T) + ((-2) * (475 + (8 * T)) * (1025 + (17 * T) + (34 * ((1024 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- second_new_lower
    have identity : (((38297051 + (10540 * (T ^ 2)) + (1270671 * T))) : ℚ) = ((10540 * (T ^ 2)) + (1270671 * T) + 38297051) := by ring
    have scaling : ((1) * ((61440 + ((-32) * ((1024 + (17 * T)) ^ 3)) + (504 * ((1024 + (17 * T)) ^ 2)) + (1020 * T) + ((475 + (8 * T)) * (1025 + (17 * T) + (68 * ((1024 + (17 * T)) ^ 2)))))) : ℚ) = ((38297051 + (10540 * (T ^ 2)) + (1270671 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((10540 * (T ^ 2)) + (1270671 * T) + 38297051) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (61440 + ((-32) * ((1024 + (17 * T)) ^ 3)) + (504 * ((1024 + (17 * T)) ^ 2)) + (1020 * T) + ((475 + (8 * T)) * (1025 + (17 * T) + (68 * ((1024 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (61440 + ((-32) * ((1024 + (17 * T)) ^ 3)) + (504 * ((1024 + (17 * T)) ^ 2)) + (1020 * T) + ((475 + (8 * T)) * (1025 + (17 * T) + (68 * ((1024 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- second_new_upper
    have identity : (((57754714 + (15912 * (T ^ 2)) + (1917282 * T))) : ℚ) = ((15912 * (T ^ 2)) + (1917282 * T) + 57754714) := by ring
    have scaling : ((1) * ((8208 + ((-880) * ((1024 + (17 * T)) ^ 2)) + (64 * ((1024 + (17 * T)) ^ 3)) + (136 * T) + ((-2) * (475 + (8 * T)) * (1025 + (17 * T) + (68 * ((1024 + (17 * T)) ^ 2)))))) : ℚ) = ((57754714 + (15912 * (T ^ 2)) + (1917282 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((15912 * (T ^ 2)) + (1917282 * T) + 57754714) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (8208 + ((-880) * ((1024 + (17 * T)) ^ 2)) + (64 * ((1024 + (17 * T)) ^ 3)) + (136 * T) + ((-2) * (475 + (8 * T)) * (1025 + (17 * T) + (68 * ((1024 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (8208 + ((-880) * ((1024 + (17 * T)) ^ 2)) + (64 * ((1024 + (17 * T)) ^ 3)) + (136 * T) + ((-2) * (475 + (8 * T)) * (1025 + (17 * T) + (68 * ((1024 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- third_old_upper
    have identity : (((16722630656 + (78608 * (T ^ 3)) + (14078924 * (T ^ 2)) + (840457254 * T))) : ℚ) = ((78608 * (T ^ 3)) + (14078924 * (T ^ 2)) + (840457254 * T) + 16722630656) := by ring
    have scaling : ((1) * (((-59392) + ((-986) * T) + ((-436) * ((1024 + (17 * T)) ^ 2)) + (16 * ((1024 + (17 * T)) ^ 3)))) : ℚ) = ((16722630656 + (78608 * (T ^ 3)) + (14078924 * (T ^ 2)) + (840457254 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((78608 * (T ^ 3)) + (14078924 * (T ^ 2)) + (840457254 * T) + 16722630656) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-59392) + ((-986) * T) + ((-436) * ((1024 + (17 * T)) ^ 2)) + (16 * ((1024 + (17 * T)) ^ 3))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ ((-59392) + ((-986) * T) + ((-436) * ((1024 + (17 * T)) ^ 2)) + (16 * ((1024 + (17 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- third_new_upper
    have identity : (((33436862464 + (157216 * (T ^ 3)) + (28155536 * (T ^ 2)) + (1680635810 * T))) : ℚ) = ((157216 * (T ^ 3)) + (28155536 * (T ^ 2)) + (1680635810 * T) + 33436862464) := by ring
    have scaling : ((1) * (((-129024) + ((-2142) * T) + ((-880) * ((1024 + (17 * T)) ^ 2)) + (32 * ((1024 + (17 * T)) ^ 3)))) : ℚ) = ((33436862464 + (157216 * (T ^ 3)) + (28155536 * (T ^ 2)) + (1680635810 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((157216 * (T ^ 3)) + (28155536 * (T ^ 2)) + (1680635810 * T) + 33436862464) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-129024) + ((-2142) * T) + ((-880) * ((1024 + (17 * T)) ^ 2)) + (32 * ((1024 + (17 * T)) ^ 3))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ ((-129024) + ((-2142) * T) + ((-880) * ((1024 + (17 * T)) ^ 2)) + (32 * ((1024 + (17 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring

private theorem small_a4_cmod3 (T : ℚ)
    (hT : 0 ≤ T) :
    Residual (16) ((2048 + (17 * T))) (8) (0) ((957 + (8 * T))) := by
  try dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- m_lower
    have identity : (((957 + (8 * T))) : ℚ) = ((8 * T) + 957) := by ring
    have scaling : ((1) * ((957 + (8 * T))) : ℚ) = ((957 + (8 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((8 * T) + 957) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (957 + (8 * T)) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (957 + (8 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- m_stock
    have identity : (((7234 + (60 * T))) : ℚ) = ((60 * T) + 7234) := by ring
    have scaling : ((1) * ((7234 + (60 * T))) : ℚ) = ((7234 + (60 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((60 * T) + 7234) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (7234 + (60 * T)) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (7234 + (60 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- ceil_lower
    have identity : (((77511613 + (5338 * (T ^ 2)) + (1286479 * T))) : ℚ) = ((5338 * (T ^ 2)) + (1286479 * T) + 77511613) := by ring
    have scaling : ((1) * ((53248 + ((-16) * ((2048 + (17 * T)) ^ 3)) + (248 * ((2048 + (17 * T)) ^ 2)) + (442 * T) + ((957 + (8 * T)) * (2049 + (17 * T) + (34 * ((2048 + (17 * T)) ^ 2)))))) : ℚ) = ((77511613 + (5338 * (T ^ 2)) + (1286479 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((5338 * (T ^ 2)) + (1286479 * T) + 77511613) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (53248 + ((-16) * ((2048 + (17 * T)) ^ 3)) + (248 * ((2048 + (17 * T)) ^ 2)) + (442 * T) + ((957 + (8 * T)) * (2049 + (17 * T) + (34 * ((2048 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (53248 + ((-16) * ((2048 + (17 * T)) ^ 3)) + (248 * ((2048 + (17 * T)) ^ 2)) + (442 * T) + ((957 + (8 * T)) * (2049 + (17 * T) + (34 * ((2048 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- ceil_upper
    have identity : (((65096771 + (4488 * (T ^ 2)) + (1081026 * T))) : ℚ) = ((4488 * (T ^ 2)) + (1081026 * T) + 65096771) := by ring
    have scaling : ((1) * (((-51200) + ((-425) * T) + ((-214) * ((2048 + (17 * T)) ^ 2)) + (16 * ((2048 + (17 * T)) ^ 3)) + ((-1) * (957 + (8 * T)) * (2049 + (17 * T) + (34 * ((2048 + (17 * T)) ^ 2)))))) : ℚ) = ((65096771 + (4488 * (T ^ 2)) + (1081026 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((4488 * (T ^ 2)) + (1081026 * T) + 65096771) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-51200) + ((-425) * T) + ((-214) * ((2048 + (17 * T)) ^ 2)) + (16 * ((2048 + (17 * T)) ^ 3)) + ((-1) * (957 + (8 * T)) * (2049 + (17 * T) + (34 * ((2048 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ ((-51200) + ((-425) * T) + ((-214) * ((2048 + (17 * T)) ^ 2)) + (16 * ((2048 + (17 * T)) ^ 3)) + ((-1) * (957 + (8 * T)) * (2049 + (17 * T) + (34 * ((2048 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- second_old_upper
    have identity : (((382109846 + (26316 * (T ^ 2)) + (6342114 * T))) : ℚ) = ((26316 * (T ^ 2)) + (6342114 * T) + 382109846) := by ring
    have scaling : ((1) * ((155664 + ((-368) * ((2048 + (17 * T)) ^ 2)) + (32 * ((2048 + (17 * T)) ^ 3)) + (1292 * T) + ((-2) * (957 + (8 * T)) * (2049 + (17 * T) + (34 * ((2048 + (17 * T)) ^ 2)))))) : ℚ) = ((382109846 + (26316 * (T ^ 2)) + (6342114 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((26316 * (T ^ 2)) + (6342114 * T) + 382109846) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (155664 + ((-368) * ((2048 + (17 * T)) ^ 2)) + (32 * ((2048 + (17 * T)) ^ 3)) + (1292 * T) + ((-2) * (957 + (8 * T)) * (2049 + (17 * T) + (34 * ((2048 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (155664 + ((-368) * ((2048 + (17 * T)) ^ 2)) + (32 * ((2048 + (17 * T)) ^ 3)) + (1292 * T) + ((-2) * (957 + (8 * T)) * (2049 + (17 * T) + (34 * ((2048 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- second_new_lower
    have identity : (((186633149 + (12852 * (T ^ 2)) + (3097489 * T))) : ℚ) = ((12852 * (T ^ 2)) + (3097489 * T) + 186633149) := by ring
    have scaling : ((1) * ((122880 + ((-32) * ((2048 + (17 * T)) ^ 3)) + (504 * ((2048 + (17 * T)) ^ 2)) + (1020 * T) + ((957 + (8 * T)) * (2049 + (17 * T) + (68 * ((2048 + (17 * T)) ^ 2)))))) : ℚ) = ((186633149 + (12852 * (T ^ 2)) + (3097489 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((12852 * (T ^ 2)) + (3097489 * T) + 186633149) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (122880 + ((-32) * ((2048 + (17 * T)) ^ 3)) + (504 * ((2048 + (17 * T)) ^ 2)) + (1020 * T) + ((957 + (8 * T)) * (2049 + (17 * T) + (68 * ((2048 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (122880 + ((-32) * ((2048 + (17 * T)) ^ 3)) + (504 * ((2048 + (17 * T)) ^ 2)) + (1020 * T) + ((957 + (8 * T)) * (2049 + (17 * T) + (68 * ((2048 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- second_new_upper
    have identity : (((163866774 + (11288 * (T ^ 2)) + (2720094 * T))) : ℚ) = ((11288 * (T ^ 2)) + (2720094 * T) + 163866774) := by ring
    have scaling : ((1) * ((16400 + ((-880) * ((2048 + (17 * T)) ^ 2)) + (64 * ((2048 + (17 * T)) ^ 3)) + (136 * T) + ((-2) * (957 + (8 * T)) * (2049 + (17 * T) + (68 * ((2048 + (17 * T)) ^ 2)))))) : ℚ) = ((163866774 + (11288 * (T ^ 2)) + (2720094 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((11288 * (T ^ 2)) + (2720094 * T) + 163866774) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (16400 + ((-880) * ((2048 + (17 * T)) ^ 2)) + (64 * ((2048 + (17 * T)) ^ 3)) + (136 * T) + ((-2) * (957 + (8 * T)) * (2049 + (17 * T) + (68 * ((2048 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (16400 + ((-880) * ((2048 + (17 * T)) ^ 2)) + (64 * ((2048 + (17 * T)) ^ 3)) + (136 * T) + ((-2) * (957 + (8 * T)) * (2049 + (17 * T) + (68 * ((2048 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- third_old_upper
    have identity : (((135610118144 + (78608 * (T ^ 3)) + (28283852 * (T ^ 2)) + (3392191526 * T))) : ℚ) = ((78608 * (T ^ 3)) + (28283852 * (T ^ 2)) + (3392191526 * T) + 135610118144) := by ring
    have scaling : ((1) * (((-118784) + ((-986) * T) + ((-436) * ((2048 + (17 * T)) ^ 2)) + (16 * ((2048 + (17 * T)) ^ 3)))) : ℚ) = ((135610118144 + (78608 * (T ^ 3)) + (28283852 * (T ^ 2)) + (3392191526 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((78608 * (T ^ 3)) + (28283852 * (T ^ 2)) + (3392191526 * T) + 135610118144) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-118784) + ((-986) * T) + ((-436) * ((2048 + (17 * T)) ^ 2)) + (16 * ((2048 + (17 * T)) ^ 3))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ ((-118784) + ((-986) * T) + ((-436) * ((2048 + (17 * T)) ^ 2)) + (16 * ((2048 + (17 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- third_new_upper
    have identity : (((271186661376 + (157216 * (T ^ 3)) + (56565392 * (T ^ 2)) + (6783825826 * T))) : ℚ) = ((157216 * (T ^ 3)) + (56565392 * (T ^ 2)) + (6783825826 * T) + 271186661376) := by ring
    have scaling : ((1) * (((-258048) + ((-2142) * T) + ((-880) * ((2048 + (17 * T)) ^ 2)) + (32 * ((2048 + (17 * T)) ^ 3)))) : ℚ) = ((271186661376 + (157216 * (T ^ 3)) + (56565392 * (T ^ 2)) + (6783825826 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((157216 * (T ^ 3)) + (56565392 * (T ^ 2)) + (6783825826 * T) + 271186661376) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-258048) + ((-2142) * T) + ((-880) * ((2048 + (17 * T)) ^ 2)) + (32 * ((2048 + (17 * T)) ^ 3))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ ((-258048) + ((-2142) * T) + ((-880) * ((2048 + (17 * T)) ^ 2)) + (32 * ((2048 + (17 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring

private theorem small_a4_cmod4 (T : ℚ)
    (hT : 0 ≤ T) :
    Residual (16) ((4096 + (17 * T))) (8) (0) ((1921 + (8 * T))) := by
  try dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- m_lower
    have identity : (((1921 + (8 * T))) : ℚ) = ((8 * T) + 1921) := by ring
    have scaling : ((1) * ((1921 + (8 * T))) : ℚ) = ((1921 + (8 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((8 * T) + 1921) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (1921 + (8 * T)) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (1921 + (8 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- m_stock
    have identity : (((14462 + (60 * T))) : ℚ) = ((60 * T) + 14462) := by ring
    have scaling : ((1) * ((14462 + (60 * T))) : ℚ) = ((14462 + (60 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((60 * T) + 14462) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (14462 + (60 * T)) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (14462 + (60 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- ceil_lower
    have identity : (((444184449 + (7650 * (T ^ 2)) + (3686739 * T))) : ℚ) = ((7650 * (T ^ 2)) + (3686739 * T) + 444184449) := by ring
    have scaling : ((1) * ((106496 + ((-16) * ((4096 + (17 * T)) ^ 3)) + (248 * ((4096 + (17 * T)) ^ 2)) + (442 * T) + ((1921 + (8 * T)) * (4097 + (17 * T) + (34 * ((4096 + (17 * T)) ^ 2)))))) : ℚ) = ((444184449 + (7650 * (T ^ 2)) + (3686739 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((7650 * (T ^ 2)) + (3686739 * T) + 444184449) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (106496 + ((-16) * ((4096 + (17 * T)) ^ 3)) + (248 * ((4096 + (17 * T)) ^ 2)) + (442 * T) + ((1921 + (8 * T)) * (4097 + (17 * T) + (34 * ((4096 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (106496 + ((-16) * ((4096 + (17 * T)) ^ 3)) + (248 * ((4096 + (17 * T)) ^ 2)) + (442 * T) + ((1921 + (8 * T)) * (4097 + (17 * T) + (34 * ((4096 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- ceil_upper
    have identity : (((126244991 + (2176 * (T ^ 2)) + (1048254 * T))) : ℚ) = ((2176 * (T ^ 2)) + (1048254 * T) + 126244991) := by ring
    have scaling : ((1) * (((-102400) + ((-425) * T) + ((-214) * ((4096 + (17 * T)) ^ 2)) + (16 * ((4096 + (17 * T)) ^ 3)) + ((-1) * (1921 + (8 * T)) * (4097 + (17 * T) + (34 * ((4096 + (17 * T)) ^ 2)))))) : ℚ) = ((126244991 + (2176 * (T ^ 2)) + (1048254 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((2176 * (T ^ 2)) + (1048254 * T) + 126244991) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-102400) + ((-425) * T) + ((-214) * ((4096 + (17 * T)) ^ 2)) + (16 * ((4096 + (17 * T)) ^ 3)) + ((-1) * (1921 + (8 * T)) * (4097 + (17 * T) + (34 * ((4096 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ ((-102400) + ((-425) * T) + ((-214) * ((4096 + (17 * T)) ^ 2)) + (16 * ((4096 + (17 * T)) ^ 3)) + ((-1) * (1921 + (8 * T)) * (4097 + (17 * T) + (34 * ((4096 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- second_old_upper
    have identity : (((1259639054 + (21692 * (T ^ 2)) + (10454490 * T))) : ℚ) = ((21692 * (T ^ 2)) + (10454490 * T) + 1259639054) := by ring
    have scaling : ((1) * ((311312 + ((-368) * ((4096 + (17 * T)) ^ 2)) + (32 * ((4096 + (17 * T)) ^ 3)) + (1292 * T) + ((-2) * (1921 + (8 * T)) * (4097 + (17 * T) + (34 * ((4096 + (17 * T)) ^ 2)))))) : ℚ) = ((1259639054 + (21692 * (T ^ 2)) + (10454490 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((21692 * (T ^ 2)) + (10454490 * T) + 1259639054) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (311312 + ((-368) * ((4096 + (17 * T)) ^ 2)) + (32 * ((4096 + (17 * T)) ^ 3)) + (1292 * T) + ((-2) * (1921 + (8 * T)) * (4097 + (17 * T) + (34 * ((4096 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (311312 + ((-368) * ((4096 + (17 * T)) ^ 2)) + (32 * ((4096 + (17 * T)) ^ 3)) + (1292 * T) + ((-2) * (1921 + (8 * T)) * (4097 + (17 * T) + (34 * ((4096 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- second_new_lower
    have identity : (((1014749057 + (17476 * (T ^ 2)) + (8422293 * T))) : ℚ) = ((17476 * (T ^ 2)) + (8422293 * T) + 1014749057) := by ring
    have scaling : ((1) * ((245760 + ((-32) * ((4096 + (17 * T)) ^ 3)) + (504 * ((4096 + (17 * T)) ^ 2)) + (1020 * T) + ((1921 + (8 * T)) * (4097 + (17 * T) + (68 * ((4096 + (17 * T)) ^ 2)))))) : ℚ) = ((1014749057 + (17476 * (T ^ 2)) + (8422293 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((17476 * (T ^ 2)) + (8422293 * T) + 1014749057) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (245760 + ((-32) * ((4096 + (17 * T)) ^ 3)) + (504 * ((4096 + (17 * T)) ^ 2)) + (1020 * T) + ((1921 + (8 * T)) * (4097 + (17 * T) + (68 * ((4096 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (245760 + ((-32) * ((4096 + (17 * T)) ^ 3)) + (504 * ((4096 + (17 * T)) ^ 2)) + (1020 * T) + ((1921 + (8 * T)) * (4097 + (17 * T) + (68 * ((4096 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- second_new_upper
    have identity : (((118509838 + (2040 * (T ^ 2)) + (983382 * T))) : ℚ) = ((2040 * (T ^ 2)) + (983382 * T) + 118509838) := by ring
    have scaling : ((1) * ((32784 + ((-880) * ((4096 + (17 * T)) ^ 2)) + (64 * ((4096 + (17 * T)) ^ 3)) + (136 * T) + ((-2) * (1921 + (8 * T)) * (4097 + (17 * T) + (68 * ((4096 + (17 * T)) ^ 2)))))) : ℚ) = ((118509838 + (2040 * (T ^ 2)) + (983382 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((2040 * (T ^ 2)) + (983382 * T) + 118509838) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (32784 + ((-880) * ((4096 + (17 * T)) ^ 2)) + (64 * ((4096 + (17 * T)) ^ 3)) + (136 * T) + ((-2) * (1921 + (8 * T)) * (4097 + (17 * T) + (68 * ((4096 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (32784 + ((-880) * ((4096 + (17 * T)) ^ 2)) + (64 * ((4096 + (17 * T)) ^ 3)) + (136 * T) + ((-2) * (1921 + (8 * T)) * (4097 + (17 * T) + (68 * ((4096 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- third_old_upper
    have identity : (((1092196524032 + (78608 * (T ^ 3)) + (56693708 * (T ^ 2)) + (13629488166 * T))) : ℚ) = ((78608 * (T ^ 3)) + (56693708 * (T ^ 2)) + (13629488166 * T) + 1092196524032) := by ring
    have scaling : ((1) * (((-237568) + ((-986) * T) + ((-436) * ((4096 + (17 * T)) ^ 2)) + (16 * ((4096 + (17 * T)) ^ 3)))) : ℚ) = ((1092196524032 + (78608 * (T ^ 3)) + (56693708 * (T ^ 2)) + (13629488166 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((78608 * (T ^ 3)) + (56693708 * (T ^ 2)) + (13629488166 * T) + 1092196524032) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-237568) + ((-986) * T) + ((-436) * ((4096 + (17 * T)) ^ 2)) + (16 * ((4096 + (17 * T)) ^ 3))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ ((-237568) + ((-986) * T) + ((-436) * ((4096 + (17 * T)) ^ 2)) + (16 * ((4096 + (17 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- third_new_upper
    have identity : (((2184258789376 + (157216 * (T ^ 3)) + (113385104 * (T ^ 2)) + (27257862050 * T))) : ℚ) = ((157216 * (T ^ 3)) + (113385104 * (T ^ 2)) + (27257862050 * T) + 2184258789376) := by ring
    have scaling : ((1) * (((-516096) + ((-2142) * T) + ((-880) * ((4096 + (17 * T)) ^ 2)) + (32 * ((4096 + (17 * T)) ^ 3)))) : ℚ) = ((2184258789376 + (157216 * (T ^ 3)) + (113385104 * (T ^ 2)) + (27257862050 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((157216 * (T ^ 3)) + (113385104 * (T ^ 2)) + (27257862050 * T) + 2184258789376) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-516096) + ((-2142) * T) + ((-880) * ((4096 + (17 * T)) ^ 2)) + (32 * ((4096 + (17 * T)) ^ 3))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ ((-516096) + ((-2142) * T) + ((-880) * ((4096 + (17 * T)) ^ 2)) + (32 * ((4096 + (17 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring

private theorem small_a4_cmod5 (T : ℚ)
    (hT : 0 ≤ T) :
    Residual (16) ((32 + (17 * T))) (8) (0) ((8 + (8 * T))) := by
  try dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- m_lower
    have identity : (((8 + (8 * T))) : ℚ) = ((8 * T) + 8) := by ring
    have scaling : ((1) * ((8 + (8 * T))) : ℚ) = ((8 + (8 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((8 * T) + 8) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (8 + (8 * T)) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (8 + (8 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- m_stock
    have identity : (((119 + (60 * T))) : ℚ) = ((60 * T) + 119) := by ring
    have scaling : ((1) * ((119 + (60 * T))) : ℚ) = ((119 + (60 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((60 * T) + 119) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (119 + (60 * T)) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (119 + (60 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- ceil_lower
    have identity : (((9288 + (2448 * (T ^ 2)) + (9546 * T))) : ℚ) = ((2448 * (T ^ 2)) + (9546 * T) + 9288) := by ring
    have scaling : ((1) * ((832 + ((-16) * ((32 + (17 * T)) ^ 3)) + (248 * ((32 + (17 * T)) ^ 2)) + (442 * T) + ((8 + (8 * T)) * (33 + (17 * T) + (34 * ((32 + (17 * T)) ^ 2)))))) : ℚ) = ((9288 + (2448 * (T ^ 2)) + (9546 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((2448 * (T ^ 2)) + (9546 * T) + 9288) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (832 + ((-16) * ((32 + (17 * T)) ^ 3)) + (248 * ((32 + (17 * T)) ^ 2)) + (442 * T) + ((8 + (8 * T)) * (33 + (17 * T) + (34 * ((32 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (832 + ((-16) * ((32 + (17 * T)) ^ 3)) + (248 * ((32 + (17 * T)) ^ 2)) + (442 * T) + ((8 + (8 * T)) * (33 + (17 * T) + (34 * ((32 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- ceil_upper
    have identity : (((25560 + (7378 * (T ^ 2)) + (27463 * T))) : ℚ) = ((7378 * (T ^ 2)) + (27463 * T) + 25560) := by ring
    have scaling : ((1) * (((-800) + ((-425) * T) + ((-214) * ((32 + (17 * T)) ^ 2)) + (16 * ((32 + (17 * T)) ^ 3)) + ((-1) * (8 + (8 * T)) * (33 + (17 * T) + (34 * ((32 + (17 * T)) ^ 2)))))) : ℚ) = ((25560 + (7378 * (T ^ 2)) + (27463 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((7378 * (T ^ 2)) + (27463 * T) + 25560) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-800) + ((-425) * T) + ((-214) * ((32 + (17 * T)) ^ 2)) + (16 * ((32 + (17 * T)) ^ 3)) + ((-1) * (8 + (8 * T)) * (33 + (17 * T) + (34 * ((32 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ ((-800) + ((-425) * T) + ((-214) * ((32 + (17 * T)) ^ 2)) + (16 * ((32 + (17 * T)) ^ 3)) + ((-1) * (8 + (8 * T)) * (33 + (17 * T) + (34 * ((32 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- second_old_upper
    have identity : (((116608 + (32096 * (T ^ 2)) + (122348 * T))) : ℚ) = ((32096 * (T ^ 2)) + (122348 * T) + 116608) := by ring
    have scaling : ((1) * ((2448 + ((-368) * ((32 + (17 * T)) ^ 2)) + (32 * ((32 + (17 * T)) ^ 3)) + (1292 * T) + ((-2) * (8 + (8 * T)) * (33 + (17 * T) + (34 * ((32 + (17 * T)) ^ 2)))))) : ℚ) = ((116608 + (32096 * (T ^ 2)) + (122348 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((32096 * (T ^ 2)) + (122348 * T) + 116608) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (2448 + ((-368) * ((32 + (17 * T)) ^ 2)) + (32 * ((32 + (17 * T)) ^ 3)) + (1292 * T) + ((-2) * (8 + (8 * T)) * (33 + (17 * T) + (34 * ((32 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (2448 + ((-368) * ((32 + (17 * T)) ^ 2)) + (32 * ((32 + (17 * T)) ^ 3)) + (1292 * T) + ((-2) * (8 + (8 * T)) * (33 + (17 * T) + (34 * ((32 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- second_new_lower
    have identity : (((26760 + (7072 * (T ^ 2)) + (27532 * T))) : ℚ) = ((7072 * (T ^ 2)) + (27532 * T) + 26760) := by ring
    have scaling : ((1) * ((1920 + ((-32) * ((32 + (17 * T)) ^ 3)) + (504 * ((32 + (17 * T)) ^ 2)) + (1020 * T) + ((8 + (8 * T)) * (33 + (17 * T) + (68 * ((32 + (17 * T)) ^ 2)))))) : ℚ) = ((26760 + (7072 * (T ^ 2)) + (27532 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((7072 * (T ^ 2)) + (27532 * T) + 26760) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (1920 + ((-32) * ((32 + (17 * T)) ^ 3)) + (504 * ((32 + (17 * T)) ^ 2)) + (1020 * T) + ((8 + (8 * T)) * (33 + (17 * T) + (68 * ((32 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (1920 + ((-32) * ((32 + (17 * T)) ^ 3)) + (504 * ((32 + (17 * T)) ^ 2)) + (1020 * T) + ((8 + (8 * T)) * (33 + (17 * T) + (68 * ((32 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- second_new_upper
    have identity : (((81664 + (22848 * (T ^ 2)) + (86376 * T))) : ℚ) = ((22848 * (T ^ 2)) + (86376 * T) + 81664) := by ring
    have scaling : ((1) * ((272 + ((-880) * ((32 + (17 * T)) ^ 2)) + (64 * ((32 + (17 * T)) ^ 3)) + (136 * T) + ((-2) * (8 + (8 * T)) * (33 + (17 * T) + (68 * ((32 + (17 * T)) ^ 2)))))) : ℚ) = ((81664 + (22848 * (T ^ 2)) + (86376 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((22848 * (T ^ 2)) + (86376 * T) + 81664) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (272 + ((-880) * ((32 + (17 * T)) ^ 2)) + (64 * ((32 + (17 * T)) ^ 3)) + (136 * T) + ((-2) * (8 + (8 * T)) * (33 + (17 * T) + (68 * ((32 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (272 + ((-880) * ((32 + (17 * T)) ^ 2)) + (64 * ((32 + (17 * T)) ^ 3)) + (136 * T) + ((-2) * (8 + (8 * T)) * (33 + (17 * T) + (68 * ((32 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- third_old_upper
    have identity : (((75968 + (78608 * (T ^ 3)) + (317900 * (T ^ 2)) + (360230 * T))) : ℚ) = ((78608 * (T ^ 3)) + (317900 * (T ^ 2)) + (360230 * T) + 75968) := by ring
    have scaling : ((1) * (((-1856) + ((-986) * T) + ((-436) * ((32 + (17 * T)) ^ 2)) + (16 * ((32 + (17 * T)) ^ 3)))) : ℚ) = ((75968 + (78608 * (T ^ 3)) + (317900 * (T ^ 2)) + (360230 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((78608 * (T ^ 3)) + (317900 * (T ^ 2)) + (360230 * T) + 75968) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-1856) + ((-986) * T) + ((-436) * ((32 + (17 * T)) ^ 2)) + (16 * ((32 + (17 * T)) ^ 3))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ ((-1856) + ((-986) * T) + ((-436) * ((32 + (17 * T)) ^ 2)) + (16 * ((32 + (17 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- third_new_upper
    have identity : (((143424 + (157216 * (T ^ 3)) + (633488 * (T ^ 2)) + (711586 * T))) : ℚ) = ((157216 * (T ^ 3)) + (633488 * (T ^ 2)) + (711586 * T) + 143424) := by ring
    have scaling : ((1) * (((-4032) + ((-2142) * T) + ((-880) * ((32 + (17 * T)) ^ 2)) + (32 * ((32 + (17 * T)) ^ 3)))) : ℚ) = ((143424 + (157216 * (T ^ 3)) + (633488 * (T ^ 2)) + (711586 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((157216 * (T ^ 3)) + (633488 * (T ^ 2)) + (711586 * T) + 143424) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-4032) + ((-2142) * T) + ((-880) * ((32 + (17 * T)) ^ 2)) + (32 * ((32 + (17 * T)) ^ 3))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ ((-4032) + ((-2142) * T) + ((-880) * ((32 + (17 * T)) ^ 2)) + (32 * ((32 + (17 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring

private theorem small_a4_cmod6 (T : ℚ)
    (hT : 0 ≤ T) :
    Residual (16) ((64 + (17 * T))) (8) (0) ((23 + (8 * T))) := by
  try dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- m_lower
    have identity : (((23 + (8 * T))) : ℚ) = ((8 * T) + 23) := by ring
    have scaling : ((1) * ((23 + (8 * T))) : ℚ) = ((23 + (8 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((8 * T) + 23) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (23 + (8 * T)) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (23 + (8 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- m_stock
    have identity : (((232 + (60 * T))) : ℚ) = ((60 * T) + 232) := by ring
    have scaling : ((1) * ((232 + (60 * T))) : ℚ) = ((232 + (60 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((60 * T) + 232) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (232 + (60 * T)) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (232 + (60 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- ceil_lower
    have identity : (((27735 + (1870 * (T ^ 2)) + (14409 * T))) : ℚ) = ((1870 * (T ^ 2)) + (14409 * T) + 27735) := by ring
    have scaling : ((1) * ((1664 + ((-16) * ((64 + (17 * T)) ^ 3)) + (248 * ((64 + (17 * T)) ^ 2)) + (442 * T) + ((23 + (8 * T)) * (65 + (17 * T) + (34 * ((64 + (17 * T)) ^ 2)))))) : ℚ) = ((27735 + (1870 * (T ^ 2)) + (14409 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((1870 * (T ^ 2)) + (14409 * T) + 27735) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (1664 + ((-16) * ((64 + (17 * T)) ^ 3)) + (248 * ((64 + (17 * T)) ^ 2)) + (442 * T) + ((23 + (8 * T)) * (65 + (17 * T) + (34 * ((64 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (1664 + ((-16) * ((64 + (17 * T)) ^ 3)) + (248 * ((64 + (17 * T)) ^ 2)) + (442 * T) + ((23 + (8 * T)) * (65 + (17 * T) + (34 * ((64 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- ceil_upper
    have identity : (((111593 + (7956 * (T ^ 2)) + (59592 * T))) : ℚ) = ((7956 * (T ^ 2)) + (59592 * T) + 111593) := by ring
    have scaling : ((1) * (((-1600) + ((-425) * T) + ((-214) * ((64 + (17 * T)) ^ 2)) + (16 * ((64 + (17 * T)) ^ 3)) + ((-1) * (23 + (8 * T)) * (65 + (17 * T) + (34 * ((64 + (17 * T)) ^ 2)))))) : ℚ) = ((111593 + (7956 * (T ^ 2)) + (59592 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((7956 * (T ^ 2)) + (59592 * T) + 111593) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-1600) + ((-425) * T) + ((-214) * ((64 + (17 * T)) ^ 2)) + (16 * ((64 + (17 * T)) ^ 3)) + ((-1) * (23 + (8 * T)) * (65 + (17 * T) + (34 * ((64 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ ((-1600) + ((-425) * T) + ((-214) * ((64 + (17 * T)) ^ 2)) + (16 * ((64 + (17 * T)) ^ 3)) + ((-1) * (23 + (8 * T)) * (65 + (17 * T) + (34 * ((64 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- second_old_upper
    have identity : (((477026 + (33252 * (T ^ 2)) + (251886 * T))) : ℚ) = ((33252 * (T ^ 2)) + (251886 * T) + 477026) := by ring
    have scaling : ((1) * ((4880 + ((-368) * ((64 + (17 * T)) ^ 2)) + (32 * ((64 + (17 * T)) ^ 3)) + (1292 * T) + ((-2) * (23 + (8 * T)) * (65 + (17 * T) + (34 * ((64 + (17 * T)) ^ 2)))))) : ℚ) = ((477026 + (33252 * (T ^ 2)) + (251886 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((33252 * (T ^ 2)) + (251886 * T) + 477026) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (4880 + ((-368) * ((64 + (17 * T)) ^ 2)) + (32 * ((64 + (17 * T)) ^ 3)) + (1292 * T) + ((-2) * (23 + (8 * T)) * (65 + (17 * T) + (34 * ((64 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (4880 + ((-368) * ((64 + (17 * T)) ^ 2)) + (32 * ((64 + (17 * T)) ^ 3)) + (1292 * T) + ((-2) * (23 + (8 * T)) * (65 + (17 * T) + (34 * ((64 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- second_new_lower
    have identity : (((87255 + (5916 * (T ^ 2)) + (45451 * T))) : ℚ) = ((5916 * (T ^ 2)) + (45451 * T) + 87255) := by ring
    have scaling : ((1) * ((3840 + ((-32) * ((64 + (17 * T)) ^ 3)) + (504 * ((64 + (17 * T)) ^ 2)) + (1020 * T) + ((23 + (8 * T)) * (65 + (17 * T) + (68 * ((64 + (17 * T)) ^ 2)))))) : ℚ) = ((87255 + (5916 * (T ^ 2)) + (45451 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((5916 * (T ^ 2)) + (45451 * T) + 87255) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (3840 + ((-32) * ((64 + (17 * T)) ^ 3)) + (504 * ((64 + (17 * T)) ^ 2)) + (1020 * T) + ((23 + (8 * T)) * (65 + (17 * T) + (68 * ((64 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (3840 + ((-32) * ((64 + (17 * T)) ^ 3)) + (504 * ((64 + (17 * T)) ^ 2)) + (1020 * T) + ((23 + (8 * T)) * (65 + (17 * T) + (68 * ((64 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- second_new_upper
    have identity : (((357986 + (25160 * (T ^ 2)) + (189802 * T))) : ℚ) = ((25160 * (T ^ 2)) + (189802 * T) + 357986) := by ring
    have scaling : ((1) * ((528 + ((-880) * ((64 + (17 * T)) ^ 2)) + (64 * ((64 + (17 * T)) ^ 3)) + (136 * T) + ((-2) * (23 + (8 * T)) * (65 + (17 * T) + (68 * ((64 + (17 * T)) ^ 2)))))) : ℚ) = ((357986 + (25160 * (T ^ 2)) + (189802 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((25160 * (T ^ 2)) + (189802 * T) + 357986) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (528 + ((-880) * ((64 + (17 * T)) ^ 2)) + (64 * ((64 + (17 * T)) ^ 3)) + (136 * T) + ((-2) * (23 + (8 * T)) * (65 + (17 * T) + (68 * ((64 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (528 + ((-880) * ((64 + (17 * T)) ^ 2)) + (64 * ((64 + (17 * T)) ^ 3)) + (136 * T) + ((-2) * (23 + (8 * T)) * (65 + (17 * T) + (68 * ((64 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- third_old_upper
    have identity : (((2404736 + (78608 * (T ^ 3)) + (761804 * (T ^ 2)) + (2392614 * T))) : ℚ) = ((78608 * (T ^ 3)) + (761804 * (T ^ 2)) + (2392614 * T) + 2404736) := by ring
    have scaling : ((1) * (((-3712) + ((-986) * T) + ((-436) * ((64 + (17 * T)) ^ 2)) + (16 * ((64 + (17 * T)) ^ 3)))) : ℚ) = ((2404736 + (78608 * (T ^ 3)) + (761804 * (T ^ 2)) + (2392614 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((78608 * (T ^ 3)) + (761804 * (T ^ 2)) + (2392614 * T) + 2404736) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-3712) + ((-986) * T) + ((-436) * ((64 + (17 * T)) ^ 2)) + (16 * ((64 + (17 * T)) ^ 3))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ ((-3712) + ((-986) * T) + ((-436) * ((64 + (17 * T)) ^ 2)) + (16 * ((64 + (17 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- third_new_upper
    have identity : (((4776064 + (157216 * (T ^ 3)) + (1521296 * (T ^ 2)) + (4767650 * T))) : ℚ) = ((157216 * (T ^ 3)) + (1521296 * (T ^ 2)) + (4767650 * T) + 4776064) := by ring
    have scaling : ((1) * (((-8064) + ((-2142) * T) + ((-880) * ((64 + (17 * T)) ^ 2)) + (32 * ((64 + (17 * T)) ^ 3)))) : ℚ) = ((4776064 + (157216 * (T ^ 3)) + (1521296 * (T ^ 2)) + (4767650 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((157216 * (T ^ 3)) + (1521296 * (T ^ 2)) + (4767650 * T) + 4776064) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-8064) + ((-2142) * T) + ((-880) * ((64 + (17 * T)) ^ 2)) + (32 * ((64 + (17 * T)) ^ 3))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ ((-8064) + ((-2142) * T) + ((-880) * ((64 + (17 * T)) ^ 2)) + (32 * ((64 + (17 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring

private theorem small_a4_cmod7 (T : ℚ)
    (hT : 0 ≤ T) :
    Residual (16) ((128 + (17 * T))) (8) (0) ((53 + (8 * T))) := by
  try dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- m_lower
    have identity : (((53 + (8 * T))) : ℚ) = ((8 * T) + 53) := by ring
    have scaling : ((1) * ((53 + (8 * T))) : ℚ) = ((53 + (8 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((8 * T) + 53) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (53 + (8 * T)) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (53 + (8 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- m_stock
    have identity : (((458 + (60 * T))) : ℚ) = ((60 * T) + 458) := by ring
    have scaling : ((1) * ((458 + (60 * T))) : ℚ) = ((458 + (60 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((60 * T) + 458) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (458 + (60 * T)) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (458 + (60 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- ceil_lower
    have identity : (((42933 + (714 * (T ^ 2)) + (11079 * T))) : ℚ) = ((714 * (T ^ 2)) + (11079 * T) + 42933) := by ring
    have scaling : ((1) * ((3328 + ((-16) * ((128 + (17 * T)) ^ 3)) + (248 * ((128 + (17 * T)) ^ 2)) + (442 * T) + ((53 + (8 * T)) * (129 + (17 * T) + (34 * ((128 + (17 * T)) ^ 2)))))) : ℚ) = ((42933 + (714 * (T ^ 2)) + (11079 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((714 * (T ^ 2)) + (11079 * T) + 42933) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (3328 + ((-16) * ((128 + (17 * T)) ^ 3)) + (248 * ((128 + (17 * T)) ^ 2)) + (442 * T) + ((53 + (8 * T)) * (129 + (17 * T) + (34 * ((128 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (3328 + ((-16) * ((128 + (17 * T)) ^ 3)) + (248 * ((128 + (17 * T)) ^ 2)) + (442 * T) + ((53 + (8 * T)) * (129 + (17 * T) + (34 * ((128 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- ceil_upper
    have identity : (((514251 + (9112 * (T ^ 2)) + (136906 * T))) : ℚ) = ((9112 * (T ^ 2)) + (136906 * T) + 514251) := by ring
    have scaling : ((1) * (((-3200) + ((-425) * T) + ((-214) * ((128 + (17 * T)) ^ 2)) + (16 * ((128 + (17 * T)) ^ 3)) + ((-1) * (53 + (8 * T)) * (129 + (17 * T) + (34 * ((128 + (17 * T)) ^ 2)))))) : ℚ) = ((514251 + (9112 * (T ^ 2)) + (136906 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((9112 * (T ^ 2)) + (136906 * T) + 514251) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-3200) + ((-425) * T) + ((-214) * ((128 + (17 * T)) ^ 2)) + (16 * ((128 + (17 * T)) ^ 3)) + ((-1) * (53 + (8 * T)) * (129 + (17 * T) + (34 * ((128 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ ((-3200) + ((-425) * T) + ((-214) * ((128 + (17 * T)) ^ 2)) + (16 * ((128 + (17 * T)) ^ 3)) + ((-1) * (53 + (8 * T)) * (129 + (17 * T) + (34 * ((128 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- second_old_upper
    have identity : (((2027686 + (35564 * (T ^ 2)) + (537074 * T))) : ℚ) = ((35564 * (T ^ 2)) + (537074 * T) + 2027686) := by ring
    have scaling : ((1) * ((9744 + ((-368) * ((128 + (17 * T)) ^ 2)) + (32 * ((128 + (17 * T)) ^ 3)) + (1292 * T) + ((-2) * (53 + (8 * T)) * (129 + (17 * T) + (34 * ((128 + (17 * T)) ^ 2)))))) : ℚ) = ((2027686 + (35564 * (T ^ 2)) + (537074 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((35564 * (T ^ 2)) + (537074 * T) + 2027686) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (9744 + ((-368) * ((128 + (17 * T)) ^ 2)) + (32 * ((128 + (17 * T)) ^ 3)) + (1292 * T) + ((-2) * (53 + (8 * T)) * (129 + (17 * T) + (34 * ((128 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (9744 + ((-368) * ((128 + (17 * T)) ^ 2)) + (32 * ((128 + (17 * T)) ^ 3)) + (1292 * T) + ((-2) * (53 + (8 * T)) * (129 + (17 * T) + (34 * ((128 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- second_new_lower
    have identity : (((211125 + (3604 * (T ^ 2)) + (55177 * T))) : ℚ) = ((3604 * (T ^ 2)) + (55177 * T) + 211125) := by ring
    have scaling : ((1) * ((7680 + ((-32) * ((128 + (17 * T)) ^ 3)) + (504 * ((128 + (17 * T)) ^ 2)) + (1020 * T) + ((53 + (8 * T)) * (129 + (17 * T) + (68 * ((128 + (17 * T)) ^ 2)))))) : ℚ) = ((211125 + (3604 * (T ^ 2)) + (55177 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((3604 * (T ^ 2)) + (55177 * T) + 211125) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (7680 + ((-32) * ((128 + (17 * T)) ^ 3)) + (504 * ((128 + (17 * T)) ^ 2)) + (1020 * T) + ((53 + (8 * T)) * (129 + (17 * T) + (68 * ((128 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (7680 + ((-32) * ((128 + (17 * T)) ^ 3)) + (504 * ((128 + (17 * T)) ^ 2)) + (1020 * T) + ((53 + (8 * T)) * (129 + (17 * T) + (68 * ((128 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- second_new_upper
    have identity : (((1691302 + (29784 * (T ^ 2)) + (448878 * T))) : ℚ) = ((29784 * (T ^ 2)) + (448878 * T) + 1691302) := by ring
    have scaling : ((1) * ((1040 + ((-880) * ((128 + (17 * T)) ^ 2)) + (64 * ((128 + (17 * T)) ^ 3)) + (136 * T) + ((-2) * (53 + (8 * T)) * (129 + (17 * T) + (68 * ((128 + (17 * T)) ^ 2)))))) : ℚ) = ((1691302 + (29784 * (T ^ 2)) + (448878 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((29784 * (T ^ 2)) + (448878 * T) + 1691302) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (1040 + ((-880) * ((128 + (17 * T)) ^ 2)) + (64 * ((128 + (17 * T)) ^ 3)) + (136 * T) + ((-2) * (53 + (8 * T)) * (129 + (17 * T) + (68 * ((128 + (17 * T)) ^ 2))))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ (1040 + ((-880) * ((128 + (17 * T)) ^ 2)) + (64 * ((128 + (17 * T)) ^ 3)) + (136 * T) + ((-2) * (53 + (8 * T)) * (129 + (17 * T) + (68 * ((128 + (17 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- third_old_upper
    have identity : (((26403584 + (78608 * (T ^ 3)) + (1649612 * (T ^ 2)) + (11470886 * T))) : ℚ) = ((78608 * (T ^ 3)) + (1649612 * (T ^ 2)) + (11470886 * T) + 26403584) := by ring
    have scaling : ((1) * (((-7424) + ((-986) * T) + ((-436) * ((128 + (17 * T)) ^ 2)) + (16 * ((128 + (17 * T)) ^ 3)))) : ℚ) = ((26403584 + (78608 * (T ^ 3)) + (1649612 * (T ^ 2)) + (11470886 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((78608 * (T ^ 3)) + (1649612 * (T ^ 2)) + (11470886 * T) + 26403584) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-7424) + ((-986) * T) + ((-436) * ((128 + (17 * T)) ^ 2)) + (16 * ((128 + (17 * T)) ^ 3))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ ((-7424) + ((-986) * T) + ((-436) * ((128 + (17 * T)) ^ 2)) + (16 * ((128 + (17 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring
  · -- third_new_upper
    have identity : (((52674816 + (157216 * (T ^ 3)) + (3296912 * (T ^ 2)) + (22906786 * T))) : ℚ) = ((157216 * (T ^ 3)) + (3296912 * (T ^ 2)) + (22906786 * T) + 52674816) := by ring
    have scaling : ((1) * (((-16128) + ((-2142) * T) + ((-880) * ((128 + (17 * T)) ^ 2)) + (32 * ((128 + (17 * T)) ^ 3)))) : ℚ) = ((52674816 + (157216 * (T ^ 3)) + (3296912 * (T ^ 2)) + (22906786 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((157216 * (T ^ 3)) + (3296912 * (T ^ 2)) + (22906786 * T) + 52674816) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-16128) + ((-2142) * T) + ((-880) * ((128 + (17 * T)) ^ 2)) + (32 * ((128 + (17 * T)) ^ 3))) := by rw [scaling,identity] <;> exact positive
    have side : (0 : ℚ) ≤ ((-16128) + ((-2142) * T) + ((-880) * ((128 + (17 * T)) ^ 2)) + (32 * ((128 + (17 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> (try dsimp [A,B,L,K,SU,SV,SW,E,F]) <;> field_simp <;> ring

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.PlusThree
