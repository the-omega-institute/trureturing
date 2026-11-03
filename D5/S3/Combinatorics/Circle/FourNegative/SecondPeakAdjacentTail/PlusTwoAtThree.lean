/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakAdjacentTail/PlusTwoAtThree
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakAdjacentTail/PlusTwoAtThree
   mirror-E: none(waiver:adjacent-tail-physical-source)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Exact polynomial inequalities for adjacent-tail mask selection. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.Algebra
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.PlusTwo
open private A B L K SU SV SW E F Common Residual StocksAndResidual HighResidual Windows ceilDiv residueRepresentative chooseM3 chooseV2 chooseM2
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.Algebra

private theorem small_a3_cmod0 (T : ℚ)
    (hT : 0 ≤ T) :
    StocksAndResidual (8) ((64 + (9 * T))) (4) (2) ((18 + (4 * T))) := by
  try dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- v_lower
    have identity : ((4) : ℚ) = (4) := by ring
    have scaling : ((2) * (2) : ℚ) = (4) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ (4) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * 2 := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ 2 := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- v_stock
    have identity : (((58 + (9 * T))) : ℚ) = ((9 * T) + 58) := by ring
    have scaling : ((2) * ((29 + ((9 / 2) * T))) : ℚ) = ((58 + (9 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((9 * T) + 58) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (29 + ((9 / 2) * T)) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (29 + ((9 / 2) * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_lower
    have identity : (((36 + (8 * T))) : ℚ) = ((8 * T) + 36) := by ring
    have scaling : ((2) * ((18 + (4 * T))) : ℚ) = ((36 + (8 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((8 * T) + 36) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (18 + (4 * T)) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (18 + (4 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_stock
    have identity : (((218 + (28 * T))) : ℚ) = ((28 * T) + 218) := by ring
    have scaling : ((2) * ((109 + (14 * T))) : ℚ) = ((218 + (28 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((28 * T) + 218) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (109 + (14 * T)) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (109 + (14 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_lower
    have identity : (((8744 + (72 * (T ^ 2)) + (1744 * T))) : ℚ) = ((72 * (T ^ 2)) + (1744 * T) + 8744) := by ring
    have scaling : ((2) * ((3202 + ((-8) * ((64 + (9 * T)) ^ 3)) + (188 * ((64 + (9 * T)) ^ 2)) + (450 * T) + ((18 + (4 * T)) * (65 + (9 * T) + (18 * ((64 + (9 * T)) ^ 2)))))) : ℚ) = ((8744 + (72 * (T ^ 2)) + (1744 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((72 * (T ^ 2)) + (1744 * T) + 8744) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (3202 + ((-8) * ((64 + (9 * T)) ^ 3)) + (188 * ((64 + (9 * T)) ^ 2)) + (450 * T) + ((18 + (4 * T)) * (65 + (9 * T) + (18 * ((64 + (9 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (3202 + ((-8) * ((64 + (9 * T)) ^ 3)) + (188 * ((64 + (9 * T)) ^ 2)) + (450 * T) + ((18 + (4 * T)) * (65 + (9 * T) + (18 * ((64 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_upper
    have identity : (((138840 + (2844 * (T ^ 2)) + (39746 * T))) : ℚ) = ((2844 * (T ^ 2)) + (39746 * T) + 138840) := by ring
    have scaling : ((2) * (((-3138) + ((-441) * T) + ((-170) * ((64 + (9 * T)) ^ 2)) + (8 * ((64 + (9 * T)) ^ 3)) + ((-1) * (18 + (4 * T)) * (65 + (9 * T) + (18 * ((64 + (9 * T)) ^ 2)))))) : ℚ) = ((138840 + (2844 * (T ^ 2)) + (39746 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((2844 * (T ^ 2)) + (39746 * T) + 138840) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-3138) + ((-441) * T) + ((-170) * ((64 + (9 * T)) ^ 2)) + (8 * ((64 + (9 * T)) ^ 3)) + ((-1) * (18 + (4 * T)) * (65 + (9 * T) + (18 * ((64 + (9 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-3138) + ((-441) * T) + ((-170) * ((64 + (9 * T)) ^ 2)) + (8 * ((64 + (9 * T)) ^ 3)) + ((-1) * (18 + (4 * T)) * (65 + (9 * T) + (18 * ((64 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_old_upper
    have identity : (((248768 + (5040 * (T ^ 2)) + (70816 * T))) : ℚ) = ((5040 * (T ^ 2)) + (70816 * T) + 248768) := by ring
    have scaling : ((2) * (((-4348) + ((-612) * T) + ((-344) * ((64 + (9 * T)) ^ 2)) + (16 * ((64 + (9 * T)) ^ 3)) + ((-2) * (18 + (4 * T)) * (65 + (9 * T) + (18 * ((64 + (9 * T)) ^ 2)))))) : ℚ) = ((248768 + (5040 * (T ^ 2)) + (70816 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((5040 * (T ^ 2)) + (70816 * T) + 248768) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-4348) + ((-612) * T) + ((-344) * ((64 + (9 * T)) ^ 2)) + (16 * ((64 + (9 * T)) ^ 3)) + ((-2) * (18 + (4 * T)) * (65 + (9 * T) + (18 * ((64 + (9 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-4348) + ((-612) * T) + ((-344) * ((64 + (9 * T)) ^ 2)) + (16 * ((64 + (9 * T)) ^ 3)) + ((-2) * (18 + (4 * T)) * (65 + (9 * T) + (18 * ((64 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_lower
    have identity : (((48424 + (720 * (T ^ 2)) + (11932 * T))) : ℚ) = ((720 * (T ^ 2)) + (11932 * T) + 48424) := by ring
    have scaling : ((2) * ((6658 + ((-16) * ((64 + (9 * T)) ^ 3)) + (380 * ((64 + (9 * T)) ^ 2)) + (936 * T) + ((18 + (4 * T)) * (65 + (9 * T) + (36 * ((64 + (9 * T)) ^ 2)))))) : ℚ) = ((48424 + (720 * (T ^ 2)) + (11932 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((720 * (T ^ 2)) + (11932 * T) + 48424) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (6658 + ((-16) * ((64 + (9 * T)) ^ 3)) + (380 * ((64 + (9 * T)) ^ 2)) + (936 * T) + ((18 + (4 * T)) * (65 + (9 * T) + (36 * ((64 + (9 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (6658 + ((-16) * ((64 + (9 * T)) ^ 3)) + (380 * ((64 + (9 * T)) ^ 2)) + (936 * T) + ((18 + (4 * T)) * (65 + (9 * T) + (36 * ((64 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_upper
    have identity : (((169408 + (3744 * (T ^ 2)) + (50440 * T))) : ℚ) = ((3744 * (T ^ 2)) + (50440 * T) + 169408) := by ring
    have scaling : ((2) * (((-11260) + ((-1584) * T) + ((-728) * ((64 + (9 * T)) ^ 2)) + (32 * ((64 + (9 * T)) ^ 3)) + ((-2) * (18 + (4 * T)) * (65 + (9 * T) + (36 * ((64 + (9 * T)) ^ 2)))))) : ℚ) = ((169408 + (3744 * (T ^ 2)) + (50440 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((3744 * (T ^ 2)) + (50440 * T) + 169408) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-11260) + ((-1584) * T) + ((-728) * ((64 + (9 * T)) ^ 2)) + (32 * ((64 + (9 * T)) ^ 3)) + ((-2) * (18 + (4 * T)) * (65 + (9 * T) + (36 * ((64 + (9 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-11260) + ((-1584) * T) + ((-728) * ((64 + (9 * T)) ^ 2)) + (32 * ((64 + (9 * T)) ^ 3)) + ((-2) * (18 + (4 * T)) * (65 + (9 * T) + (36 * ((64 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_old_upper
    have identity : (((1363192 + (11664 * (T ^ 3)) + (193104 * (T ^ 2)) + (975060 * T))) : ℚ) = ((11664 * (T ^ 3)) + (193104 * (T ^ 2)) + (975060 * T) + 1363192) := by ring
    have scaling : ((2) * (((-6532) + ((-918) * T) + ((-344) * ((64 + (9 * T)) ^ 2)) + (8 * ((64 + (9 * T)) ^ 3)))) : ℚ) = ((1363192 + (11664 * (T ^ 3)) + (193104 * (T ^ 2)) + (975060 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((11664 * (T ^ 3)) + (193104 * (T ^ 2)) + (975060 * T) + 1363192) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-6532) + ((-918) * T) + ((-344) * ((64 + (9 * T)) ^ 2)) + (8 * ((64 + (9 * T)) ^ 3))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-6532) + ((-918) * T) + ((-344) * ((64 + (9 * T)) ^ 2)) + (8 * ((64 + (9 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_new_upper
    have identity : (((2692856 + (23328 * (T ^ 3)) + (385560 * (T ^ 2)) + (1940796 * T))) : ℚ) = ((23328 * (T ^ 3)) + (385560 * (T ^ 2)) + (1940796 * T) + 2692856) := by ring
    have scaling : ((2) * (((-13444) + ((-1890) * T) + ((-692) * ((64 + (9 * T)) ^ 2)) + (16 * ((64 + (9 * T)) ^ 3)))) : ℚ) = ((2692856 + (23328 * (T ^ 3)) + (385560 * (T ^ 2)) + (1940796 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((23328 * (T ^ 3)) + (385560 * (T ^ 2)) + (1940796 * T) + 2692856) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-13444) + ((-1890) * T) + ((-692) * ((64 + (9 * T)) ^ 2)) + (16 * ((64 + (9 * T)) ^ 3))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-13444) + ((-1890) * T) + ((-692) * ((64 + (9 * T)) ^ 2)) + (16 * ((64 + (9 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring

private theorem small_a3_cmod1 (T : ℚ)
    (hT : 0 ≤ T) :
    StocksAndResidual (8) ((128 + (9 * T))) (4) (1) ((50 + (4 * T))) := by
  try dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- v_lower
    have identity : ((2) : ℚ) = (2) := by ring
    have scaling : ((2) * (1) : ℚ) = (2) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ (2) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * 1 := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ 1 := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- v_stock
    have identity : (((124 + (9 * T))) : ℚ) = ((9 * T) + 124) := by ring
    have scaling : ((2) * ((62 + ((9 / 2) * T))) : ℚ) = ((124 + (9 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((9 * T) + 124) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (62 + ((9 / 2) * T)) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (62 + ((9 / 2) * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_lower
    have identity : (((100 + (8 * T))) : ℚ) = ((8 * T) + 100) := by ring
    have scaling : ((2) * ((50 + (4 * T))) : ℚ) = ((100 + (8 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((8 * T) + 100) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (50 + (4 * T)) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (50 + (4 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_stock
    have identity : (((410 + (28 * T))) : ℚ) = ((28 * T) + 410) := by ring
    have scaling : ((2) * ((205 + (14 * T))) : ℚ) = ((410 + (28 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((28 * T) + 410) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (205 + (14 * T)) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (205 + (14 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_lower
    have identity : (((21094 + (72 * (T ^ 2)) + (2508 * T))) : ℚ) = ((72 * (T ^ 2)) + (2508 * T) + 21094) := by ring
    have scaling : ((2) * ((4097 + ((-8) * ((128 + (9 * T)) ^ 3)) + (124 * ((128 + (9 * T)) ^ 2)) + (288 * T) + ((50 + (4 * T)) * (129 + (9 * T) + (18 * ((128 + (9 * T)) ^ 2)))))) : ℚ) = ((21094 + (72 * (T ^ 2)) + (2508 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((72 * (T ^ 2)) + (2508 * T) + 21094) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (4097 + ((-8) * ((128 + (9 * T)) ^ 3)) + (124 * ((128 + (9 * T)) ^ 2)) + (288 * T) + ((50 + (4 * T)) * (129 + (9 * T) + (18 * ((128 + (9 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (4097 + ((-8) * ((128 + (9 * T)) ^ 3)) + (124 * ((128 + (9 * T)) ^ 2)) + (288 * T) + ((50 + (4 * T)) * (129 + (9 * T) + (18 * ((128 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_upper
    have identity : (((568986 + (2844 * (T ^ 2)) + (80454 * T))) : ℚ) = ((2844 * (T ^ 2)) + (80454 * T) + 568986) := by ring
    have scaling : ((2) * (((-3969) + ((-279) * T) + ((-106) * ((128 + (9 * T)) ^ 2)) + (8 * ((128 + (9 * T)) ^ 3)) + ((-1) * (50 + (4 * T)) * (129 + (9 * T) + (18 * ((128 + (9 * T)) ^ 2)))))) : ℚ) = ((568986 + (2844 * (T ^ 2)) + (80454 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((2844 * (T ^ 2)) + (80454 * T) + 568986) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-3969) + ((-279) * T) + ((-106) * ((128 + (9 * T)) ^ 2)) + (8 * ((128 + (9 * T)) ^ 3)) + ((-1) * (50 + (4 * T)) * (129 + (9 * T) + (18 * ((128 + (9 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-3969) + ((-279) * T) + ((-106) * ((128 + (9 * T)) ^ 2)) + (8 * ((128 + (9 * T)) ^ 3)) + ((-1) * (50 + (4 * T)) * (129 + (9 * T) + (18 * ((128 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_old_upper
    have identity : (((1014596 + (5040 * (T ^ 2)) + (143016 * T))) : ℚ) = ((5040 * (T ^ 2)) + (143016 * T) + 1014596) := by ring
    have scaling : ((2) * (((-4090) + ((-288) * T) + ((-216) * ((128 + (9 * T)) ^ 2)) + (16 * ((128 + (9 * T)) ^ 3)) + ((-2) * (50 + (4 * T)) * (129 + (9 * T) + (18 * ((128 + (9 * T)) ^ 2)))))) : ℚ) = ((1014596 + (5040 * (T ^ 2)) + (143016 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((5040 * (T ^ 2)) + (143016 * T) + 1014596) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-4090) + ((-288) * T) + ((-216) * ((128 + (9 * T)) ^ 2)) + (16 * ((128 + (9 * T)) ^ 3)) + ((-2) * (50 + (4 * T)) * (129 + (9 * T) + (18 * ((128 + (9 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-4090) + ((-288) * T) + ((-216) * ((128 + (9 * T)) ^ 2)) + (16 * ((128 + (9 * T)) ^ 3)) + ((-2) * (50 + (4 * T)) * (129 + (9 * T) + (18 * ((128 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_lower
    have identity : (((161382 + (720 * (T ^ 2)) + (21588 * T))) : ℚ) = ((720 * (T ^ 2)) + (21588 * T) + 161382) := by ring
    have scaling : ((2) * ((8705 + ((-16) * ((128 + (9 * T)) ^ 3)) + (252 * ((128 + (9 * T)) ^ 2)) + (612 * T) + ((50 + (4 * T)) * (129 + (9 * T) + (36 * ((128 + (9 * T)) ^ 2)))))) : ℚ) = ((161382 + (720 * (T ^ 2)) + (21588 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((720 * (T ^ 2)) + (21588 * T) + 161382) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (8705 + ((-16) * ((128 + (9 * T)) ^ 3)) + (252 * ((128 + (9 * T)) ^ 2)) + (612 * T) + ((50 + (4 * T)) * (129 + (9 * T) + (36 * ((128 + (9 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (8705 + ((-16) * ((128 + (9 * T)) ^ 3)) + (252 * ((128 + (9 * T)) ^ 2)) + (612 * T) + ((50 + (4 * T)) * (129 + (9 * T) + (36 * ((128 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_upper
    have identity : (((734020 + (3744 * (T ^ 2)) + (104856 * T))) : ℚ) = ((3744 * (T ^ 2)) + (104856 * T) + 734020) := by ring
    have scaling : ((2) * (((-13306) + ((-936) * T) + ((-472) * ((128 + (9 * T)) ^ 2)) + (32 * ((128 + (9 * T)) ^ 3)) + ((-2) * (50 + (4 * T)) * (129 + (9 * T) + (36 * ((128 + (9 * T)) ^ 2)))))) : ℚ) = ((734020 + (3744 * (T ^ 2)) + (104856 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((3744 * (T ^ 2)) + (104856 * T) + 734020) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-13306) + ((-936) * T) + ((-472) * ((128 + (9 * T)) ^ 2)) + (32 * ((128 + (9 * T)) ^ 3)) + ((-2) * (50 + (4 * T)) * (129 + (9 * T) + (36 * ((128 + (9 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-13306) + ((-936) * T) + ((-472) * ((128 + (9 * T)) ^ 2)) + (32 * ((128 + (9 * T)) ^ 3)) + ((-2) * (50 + (4 * T)) * (129 + (9 * T) + (36 * ((128 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_old_upper
    have identity : (((26459644 + (11664 * (T ^ 3)) + (462672 * (T ^ 2)) + (6081372 * T))) : ℚ) = ((11664 * (T ^ 3)) + (462672 * (T ^ 2)) + (6081372 * T) + 26459644) := by ring
    have scaling : ((2) * (((-8450) + ((-594) * T) + ((-216) * ((128 + (9 * T)) ^ 2)) + (8 * ((128 + (9 * T)) ^ 3)))) : ℚ) = ((26459644 + (11664 * (T ^ 3)) + (462672 * (T ^ 2)) + (6081372 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((11664 * (T ^ 3)) + (462672 * (T ^ 2)) + (6081372 * T) + 26459644) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-8450) + ((-594) * T) + ((-216) * ((128 + (9 * T)) ^ 2)) + (8 * ((128 + (9 * T)) ^ 3))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-8450) + ((-594) * T) + ((-216) * ((128 + (9 * T)) ^ 2)) + (8 * ((128 + (9 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_new_upper
    have identity : (((52786684 + (23328 * (T ^ 3)) + (924696 * (T ^ 2)) + (12144204 * T))) : ℚ) = ((23328 * (T ^ 3)) + (924696 * (T ^ 2)) + (12144204 * T) + 52786684) := by ring
    have scaling : ((2) * (((-17666) + ((-1242) * T) + ((-436) * ((128 + (9 * T)) ^ 2)) + (16 * ((128 + (9 * T)) ^ 3)))) : ℚ) = ((52786684 + (23328 * (T ^ 3)) + (924696 * (T ^ 2)) + (12144204 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((23328 * (T ^ 3)) + (924696 * (T ^ 2)) + (12144204 * T) + 52786684) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-17666) + ((-1242) * T) + ((-436) * ((128 + (9 * T)) ^ 2)) + (16 * ((128 + (9 * T)) ^ 3))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-17666) + ((-1242) * T) + ((-436) * ((128 + (9 * T)) ^ 2)) + (16 * ((128 + (9 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring

private theorem small_a3_cmod2 (T : ℚ)
    (hT : 0 ≤ T) :
    StocksAndResidual (8) ((256 + (9 * T))) (4) (1) ((107 + (4 * T))) := by
  try dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- v_lower
    have identity : ((2) : ℚ) = (2) := by ring
    have scaling : ((2) * (1) : ℚ) = (2) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ (2) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * 1 := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ 1 := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- v_stock
    have identity : (((252 + (9 * T))) : ℚ) = ((9 * T) + 252) := by ring
    have scaling : ((2) * ((126 + ((9 / 2) * T))) : ℚ) = ((252 + (9 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((9 * T) + 252) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (126 + ((9 / 2) * T)) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (126 + ((9 / 2) * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_lower
    have identity : (((214 + (8 * T))) : ℚ) = ((8 * T) + 214) := by ring
    have scaling : ((2) * ((107 + (4 * T))) : ℚ) = ((214 + (8 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((8 * T) + 214) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (107 + (4 * T)) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (107 + (4 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_stock
    have identity : (((808 + (28 * T))) : ℚ) = ((28 * T) + 808) := by ring
    have scaling : ((2) * ((404 + (14 * T))) : ℚ) = ((808 + (28 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((28 * T) + 808) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (404 + (14 * T)) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (404 + (14 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_lower
    have identity : (((333528 + (396 * (T ^ 2)) + (22990 * T))) : ℚ) = ((396 * (T ^ 2)) + (22990 * T) + 333528) := by ring
    have scaling : ((2) * ((8193 + ((-8) * ((256 + (9 * T)) ^ 3)) + (124 * ((256 + (9 * T)) ^ 2)) + (288 * T) + ((107 + (4 * T)) * (257 + (9 * T) + (18 * ((256 + (9 * T)) ^ 2)))))) : ℚ) = ((333528 + (396 * (T ^ 2)) + (22990 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((396 * (T ^ 2)) + (22990 * T) + 333528) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (8193 + ((-8) * ((256 + (9 * T)) ^ 3)) + (124 * ((256 + (9 * T)) ^ 2)) + (288 * T) + ((107 + (4 * T)) * (257 + (9 * T) + (18 * ((256 + (9 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (8193 + ((-8) * ((256 + (9 * T)) ^ 3)) + (124 * ((256 + (9 * T)) ^ 2)) + (288 * T) + ((107 + (4 * T)) * (257 + (9 * T) + (18 * ((256 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_upper
    have identity : (((2026280 + (2520 * (T ^ 2)) + (142916 * T))) : ℚ) = ((2520 * (T ^ 2)) + (142916 * T) + 2026280) := by ring
    have scaling : ((2) * (((-7937) + ((-279) * T) + ((-106) * ((256 + (9 * T)) ^ 2)) + (8 * ((256 + (9 * T)) ^ 3)) + ((-1) * (107 + (4 * T)) * (257 + (9 * T) + (18 * ((256 + (9 * T)) ^ 2)))))) : ℚ) = ((2026280 + (2520 * (T ^ 2)) + (142916 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((2520 * (T ^ 2)) + (142916 * T) + 2026280) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-7937) + ((-279) * T) + ((-106) * ((256 + (9 * T)) ^ 2)) + (8 * ((256 + (9 * T)) ^ 3)) + ((-1) * (107 + (4 * T)) * (257 + (9 * T) + (18 * ((256 + (9 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-7937) + ((-279) * T) + ((-106) * ((256 + (9 * T)) ^ 2)) + (8 * ((256 + (9 * T)) ^ 3)) + ((-1) * (107 + (4 * T)) * (257 + (9 * T) + (18 * ((256 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_old_upper
    have identity : (((3543648 + (4392 * (T ^ 2)) + (249508 * T))) : ℚ) = ((4392 * (T ^ 2)) + (249508 * T) + 3543648) := by ring
    have scaling : ((2) * (((-8186) + ((-288) * T) + ((-216) * ((256 + (9 * T)) ^ 2)) + (16 * ((256 + (9 * T)) ^ 3)) + ((-2) * (107 + (4 * T)) * (257 + (9 * T) + (18 * ((256 + (9 * T)) ^ 2)))))) : ℚ) = ((3543648 + (4392 * (T ^ 2)) + (249508 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((4392 * (T ^ 2)) + (249508 * T) + 3543648) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-8186) + ((-288) * T) + ((-216) * ((256 + (9 * T)) ^ 2)) + (16 * ((256 + (9 * T)) ^ 3)) + ((-2) * (107 + (4 * T)) * (257 + (9 * T) + (18 * ((256 + (9 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-8186) + ((-288) * T) + ((-216) * ((256 + (9 * T)) ^ 2)) + (16 * ((256 + (9 * T)) ^ 3)) + ((-2) * (107 + (4 * T)) * (257 + (9 * T) + (18 * ((256 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_lower
    have identity : (((1138392 + (1368 * (T ^ 2)) + (78934 * T))) : ℚ) = ((1368 * (T ^ 2)) + (78934 * T) + 1138392) := by ring
    have scaling : ((2) * ((17409 + ((-16) * ((256 + (9 * T)) ^ 3)) + (252 * ((256 + (9 * T)) ^ 2)) + (612 * T) + ((107 + (4 * T)) * (257 + (9 * T) + (36 * ((256 + (9 * T)) ^ 2)))))) : ℚ) = ((1138392 + (1368 * (T ^ 2)) + (78934 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((1368 * (T ^ 2)) + (78934 * T) + 1138392) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (17409 + ((-16) * ((256 + (9 * T)) ^ 3)) + (252 * ((256 + (9 * T)) ^ 2)) + (612 * T) + ((107 + (4 * T)) * (257 + (9 * T) + (36 * ((256 + (9 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (17409 + ((-16) * ((256 + (9 * T)) ^ 3)) + (252 * ((256 + (9 * T)) ^ 2)) + (612 * T) + ((107 + (4 * T)) * (257 + (9 * T) + (36 * ((256 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_upper
    have identity : (((1933920 + (2448 * (T ^ 2)) + (137620 * T))) : ℚ) = ((2448 * (T ^ 2)) + (137620 * T) + 1933920) := by ring
    have scaling : ((2) * (((-26618) + ((-936) * T) + ((-472) * ((256 + (9 * T)) ^ 2)) + (32 * ((256 + (9 * T)) ^ 3)) + ((-2) * (107 + (4 * T)) * (257 + (9 * T) + (36 * ((256 + (9 * T)) ^ 2)))))) : ℚ) = ((1933920 + (2448 * (T ^ 2)) + (137620 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((2448 * (T ^ 2)) + (137620 * T) + 1933920) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-26618) + ((-936) * T) + ((-472) * ((256 + (9 * T)) ^ 2)) + (32 * ((256 + (9 * T)) ^ 3)) + ((-2) * (107 + (4 * T)) * (257 + (9 * T) + (36 * ((256 + (9 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-26618) + ((-936) * T) + ((-472) * ((256 + (9 * T)) ^ 2)) + (32 * ((256 + (9 * T)) ^ 3)) + ((-2) * (107 + (4 * T)) * (257 + (9 * T) + (36 * ((256 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_old_upper
    have identity : (((240090108 + (11664 * (T ^ 3)) + (960336 * (T ^ 2)) + (26319708 * T))) : ℚ) = ((11664 * (T ^ 3)) + (960336 * (T ^ 2)) + (26319708 * T) + 240090108) := by ring
    have scaling : ((2) * (((-16898) + ((-594) * T) + ((-216) * ((256 + (9 * T)) ^ 2)) + (8 * ((256 + (9 * T)) ^ 3)))) : ℚ) = ((240090108 + (11664 * (T ^ 3)) + (960336 * (T ^ 2)) + (26319708 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((11664 * (T ^ 3)) + (960336 * (T ^ 2)) + (26319708 * T) + 240090108) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-16898) + ((-594) * T) + ((-216) * ((256 + (9 * T)) ^ 2)) + (8 * ((256 + (9 * T)) ^ 3))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-16898) + ((-594) * T) + ((-216) * ((256 + (9 * T)) ^ 2)) + (8 * ((256 + (9 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_new_upper
    have identity : (((479652860 + (23328 * (T ^ 3)) + (1920024 * (T ^ 2)) + (52602444 * T))) : ℚ) = ((23328 * (T ^ 3)) + (1920024 * (T ^ 2)) + (52602444 * T) + 479652860) := by ring
    have scaling : ((2) * (((-35330) + ((-1242) * T) + ((-436) * ((256 + (9 * T)) ^ 2)) + (16 * ((256 + (9 * T)) ^ 3)))) : ℚ) = ((479652860 + (23328 * (T ^ 3)) + (1920024 * (T ^ 2)) + (52602444 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((23328 * (T ^ 3)) + (1920024 * (T ^ 2)) + (52602444 * T) + 479652860) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-35330) + ((-1242) * T) + ((-436) * ((256 + (9 * T)) ^ 2)) + (16 * ((256 + (9 * T)) ^ 3))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-35330) + ((-1242) * T) + ((-436) * ((256 + (9 * T)) ^ 2)) + (16 * ((256 + (9 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring

private theorem small_a3_cmod3 (T : ℚ)
    (hT : 0 ≤ T) :
    StocksAndResidual (8) ((512 + (9 * T))) (4) (4) ((210 + (4 * T))) := by
  try dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- v_lower
    have identity : ((8) : ℚ) = (8) := by ring
    have scaling : ((2) * (4) : ℚ) = (8) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ (8) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * 4 := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ 4 := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- v_stock
    have identity : (((502 + (9 * T))) : ℚ) = ((9 * T) + 502) := by ring
    have scaling : ((2) * ((251 + ((9 / 2) * T))) : ℚ) = ((502 + (9 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((9 * T) + 502) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (251 + ((9 / 2) * T)) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (251 + ((9 / 2) * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_lower
    have identity : (((420 + (8 * T))) : ℚ) = ((8 * T) + 420) := by ring
    have scaling : ((2) * ((210 + (4 * T))) : ℚ) = ((420 + (8 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((8 * T) + 420) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (210 + (4 * T)) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (210 + (4 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_stock
    have identity : (((1626 + (28 * T))) : ℚ) = ((28 * T) + 1626) := by ring
    have scaling : ((2) * ((813 + (14 * T))) : ℚ) = ((1626 + (28 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((28 * T) + 1626) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (813 + (14 * T)) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (813 + (14 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_lower
    have identity : (((303532 + (72 * (T ^ 2)) + (9432 * T))) : ℚ) = ((72 * (T ^ 2)) + (9432 * T) + 303532) := by ring
    have scaling : ((2) * ((44036 + ((-8) * ((512 + (9 * T)) ^ 3)) + (316 * ((512 + (9 * T)) ^ 2)) + (774 * T) + ((210 + (4 * T)) * (513 + (9 * T) + (18 * ((512 + (9 * T)) ^ 2)))))) : ℚ) = ((303532 + (72 * (T ^ 2)) + (9432 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((72 * (T ^ 2)) + (9432 * T) + 303532) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (44036 + ((-8) * ((512 + (9 * T)) ^ 3)) + (316 * ((512 + (9 * T)) ^ 2)) + (774 * T) + ((210 + (4 * T)) * (513 + (9 * T) + (18 * ((512 + (9 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (44036 + ((-8) * ((512 + (9 * T)) ^ 3)) + (316 * ((512 + (9 * T)) ^ 2)) + (774 * T) + ((210 + (4 * T)) * (513 + (9 * T) + (18 * ((512 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_upper
    have identity : (((9134676 + (2844 * (T ^ 2)) + (322362 * T))) : ℚ) = ((2844 * (T ^ 2)) + (322362 * T) + 9134676) := by ring
    have scaling : ((2) * (((-43524) + ((-765) * T) + ((-298) * ((512 + (9 * T)) ^ 2)) + (8 * ((512 + (9 * T)) ^ 3)) + ((-1) * (210 + (4 * T)) * (513 + (9 * T) + (18 * ((512 + (9 * T)) ^ 2)))))) : ℚ) = ((9134676 + (2844 * (T ^ 2)) + (322362 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((2844 * (T ^ 2)) + (322362 * T) + 9134676) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-43524) + ((-765) * T) + ((-298) * ((512 + (9 * T)) ^ 2)) + (8 * ((512 + (9 * T)) ^ 3)) + ((-1) * (210 + (4 * T)) * (513 + (9 * T) + (18 * ((512 + (9 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-43524) + ((-765) * T) + ((-298) * ((512 + (9 * T)) ^ 2)) + (8 * ((512 + (9 * T)) ^ 3)) + ((-1) * (210 + (4 * T)) * (513 + (9 * T) + (18 * ((512 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_old_upper
    have identity : (((16202936 + (5040 * (T ^ 2)) + (571536 * T))) : ℚ) = ((5040 * (T ^ 2)) + (571536 * T) + 16202936) := by ring
    have scaling : ((2) * (((-71680) + ((-1260) * T) + ((-600) * ((512 + (9 * T)) ^ 2)) + (16 * ((512 + (9 * T)) ^ 3)) + ((-2) * (210 + (4 * T)) * (513 + (9 * T) + (18 * ((512 + (9 * T)) ^ 2)))))) : ℚ) = ((16202936 + (5040 * (T ^ 2)) + (571536 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((5040 * (T ^ 2)) + (571536 * T) + 16202936) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-71680) + ((-1260) * T) + ((-600) * ((512 + (9 * T)) ^ 2)) + (16 * ((512 + (9 * T)) ^ 3)) + ((-2) * (210 + (4 * T)) * (513 + (9 * T) + (18 * ((512 + (9 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-71680) + ((-1260) * T) + ((-600) * ((512 + (9 * T)) ^ 2)) + (16 * ((512 + (9 * T)) ^ 3)) + ((-2) * (210 + (4 * T)) * (513 + (9 * T) + (18 * ((512 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_lower
    have identity : (((2492844 + (720 * (T ^ 2)) + (84780 * T))) : ℚ) = ((720 * (T ^ 2)) + (84780 * T) + 2492844) := by ring
    have scaling : ((2) * ((90116 + ((-16) * ((512 + (9 * T)) ^ 3)) + (636 * ((512 + (9 * T)) ^ 2)) + (1584 * T) + ((210 + (4 * T)) * (513 + (9 * T) + (36 * ((512 + (9 * T)) ^ 2)))))) : ℚ) = ((2492844 + (720 * (T ^ 2)) + (84780 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((720 * (T ^ 2)) + (84780 * T) + 2492844) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (90116 + ((-16) * ((512 + (9 * T)) ^ 3)) + (636 * ((512 + (9 * T)) ^ 2)) + (1584 * T) + ((210 + (4 * T)) * (513 + (9 * T) + (36 * ((512 + (9 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (90116 + ((-16) * ((512 + (9 * T)) ^ 3)) + (636 * ((512 + (9 * T)) ^ 2)) + (1584 * T) + ((210 + (4 * T)) * (513 + (9 * T) + (36 * ((512 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_upper
    have identity : (((11824312 + (3744 * (T ^ 2)) + (420840 * T))) : ℚ) = ((3744 * (T ^ 2)) + (420840 * T) + 11824312) := by ring
    have scaling : ((2) * (((-163840) + ((-2880) * T) + ((-1240) * ((512 + (9 * T)) ^ 2)) + (32 * ((512 + (9 * T)) ^ 3)) + ((-2) * (210 + (4 * T)) * (513 + (9 * T) + (36 * ((512 + (9 * T)) ^ 2)))))) : ℚ) = ((11824312 + (3744 * (T ^ 2)) + (420840 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((3744 * (T ^ 2)) + (420840 * T) + 11824312) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-163840) + ((-2880) * T) + ((-1240) * ((512 + (9 * T)) ^ 2)) + (32 * ((512 + (9 * T)) ^ 3)) + ((-2) * (210 + (4 * T)) * (513 + (9 * T) + (36 * ((512 + (9 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-163840) + ((-2880) * T) + ((-1240) * ((512 + (9 * T)) ^ 2)) + (32 * ((512 + (9 * T)) ^ 3)) + ((-2) * (210 + (4 * T)) * (513 + (9 * T) + (36 * ((512 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_old_upper
    have identity : (((1832732656 + (11664 * (T ^ 3)) + (1893456 * (T ^ 2)) + (102183876 * T))) : ℚ) = ((11664 * (T ^ 3)) + (1893456 * (T ^ 2)) + (102183876 * T) + 1832732656) := by ring
    have scaling : ((2) * (((-89096) + ((-1566) * T) + ((-600) * ((512 + (9 * T)) ^ 2)) + (8 * ((512 + (9 * T)) ^ 3)))) : ℚ) = ((1832732656 + (11664 * (T ^ 3)) + (1893456 * (T ^ 2)) + (102183876 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((11664 * (T ^ 3)) + (1893456 * (T ^ 2)) + (102183876 * T) + 1832732656) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-89096) + ((-1566) * T) + ((-600) * ((512 + (9 * T)) ^ 2)) + (8 * ((512 + (9 * T)) ^ 3))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-89096) + ((-1566) * T) + ((-600) * ((512 + (9 * T)) ^ 2)) + (8 * ((512 + (9 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_new_upper
    have identity : (((3663362032 + (23328 * (T ^ 3)) + (3786264 * (T ^ 2)) + (204293916 * T))) : ℚ) = ((23328 * (T ^ 3)) + (3786264 * (T ^ 2)) + (204293916 * T) + 3663362032) := by ring
    have scaling : ((2) * (((-181256) + ((-3186) * T) + ((-1204) * ((512 + (9 * T)) ^ 2)) + (16 * ((512 + (9 * T)) ^ 3)))) : ℚ) = ((3663362032 + (23328 * (T ^ 3)) + (3786264 * (T ^ 2)) + (204293916 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((23328 * (T ^ 3)) + (3786264 * (T ^ 2)) + (204293916 * T) + 3663362032) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-181256) + ((-3186) * T) + ((-1204) * ((512 + (9 * T)) ^ 2)) + (16 * ((512 + (9 * T)) ^ 3))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-181256) + ((-3186) * T) + ((-1204) * ((512 + (9 * T)) ^ 2)) + (16 * ((512 + (9 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring

private theorem small_a3_cmod4 (T : ℚ)
    (hT : 0 ≤ T) :
    StocksAndResidual (8) ((16 + (9 * T))) (4) (0) ((4 + (4 * T))) := by
  try dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- v_lower
    have identity : ((0) : ℚ) = (0) := by ring
    have scaling : ((2) * (0) : ℚ) = (0) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ (0) := by norm_num
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * 0 := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ 0 := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- v_stock
    have identity : (((14 + (9 * T))) : ℚ) = ((9 * T) + 14) := by ring
    have scaling : ((2) * ((7 + ((9 / 2) * T))) : ℚ) = ((14 + (9 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((9 * T) + 14) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (7 + ((9 / 2) * T)) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (7 + ((9 / 2) * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_lower
    have identity : (((8 + (8 * T))) : ℚ) = ((8 * T) + 8) := by ring
    have scaling : ((2) * ((4 + (4 * T))) : ℚ) = ((8 + (8 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((8 * T) + 8) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (4 + (4 * T)) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (4 + (4 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_stock
    have identity : (((54 + (28 * T))) : ℚ) = ((28 * T) + 54) := by ring
    have scaling : ((2) * ((27 + (14 * T))) : ℚ) = ((54 + (28 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((28 * T) + 54) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (27 + (14 * T)) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (27 + (14 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_lower
    have identity : (((2632 + (720 * (T ^ 2)) + (2764 * T))) : ℚ) = ((720 * (T ^ 2)) + (2764 * T) + 2632) := by ring
    have scaling : ((2) * ((224 + ((-8) * ((16 + (9 * T)) ^ 3)) + (60 * ((16 + (9 * T)) ^ 2)) + (126 * T) + ((4 + (4 * T)) * (17 + (9 * T) + (18 * ((16 + (9 * T)) ^ 2)))))) : ℚ) = ((2632 + (720 * (T ^ 2)) + (2764 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((720 * (T ^ 2)) + (2764 * T) + 2632) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (224 + ((-8) * ((16 + (9 * T)) ^ 3)) + (60 * ((16 + (9 * T)) ^ 2)) + (126 * T) + ((4 + (4 * T)) * (17 + (9 * T) + (18 * ((16 + (9 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (224 + ((-8) * ((16 + (9 * T)) ^ 3)) + (60 * ((16 + (9 * T)) ^ 2)) + (126 * T) + ((4 + (4 * T)) * (17 + (9 * T) + (18 * ((16 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_upper
    have identity : (((6616 + (2196 * (T ^ 2)) + (7622 * T))) : ℚ) = ((2196 * (T ^ 2)) + (7622 * T) + 6616) := by ring
    have scaling : ((2) * (((-208) + ((-117) * T) + ((-42) * ((16 + (9 * T)) ^ 2)) + (8 * ((16 + (9 * T)) ^ 3)) + ((-1) * (4 + (4 * T)) * (17 + (9 * T) + (18 * ((16 + (9 * T)) ^ 2)))))) : ℚ) = ((6616 + (2196 * (T ^ 2)) + (7622 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((2196 * (T ^ 2)) + (7622 * T) + 6616) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-208) + ((-117) * T) + ((-42) * ((16 + (9 * T)) ^ 2)) + (8 * ((16 + (9 * T)) ^ 3)) + ((-1) * (4 + (4 * T)) * (17 + (9 * T) + (18 * ((16 + (9 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-208) + ((-117) * T) + ((-42) * ((16 + (9 * T)) ^ 2)) + (8 * ((16 + (9 * T)) ^ 3)) + ((-1) * (4 + (4 * T)) * (17 + (9 * T) + (18 * ((16 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_old_upper
    have identity : (((12160 + (3744 * (T ^ 2)) + (13480 * T))) : ℚ) = ((3744 * (T ^ 2)) + (13480 * T) + 12160) := by ring
    have scaling : ((2) * ((72 + ((-88) * ((16 + (9 * T)) ^ 2)) + (16 * ((16 + (9 * T)) ^ 3)) + (36 * T) + ((-2) * (4 + (4 * T)) * (17 + (9 * T) + (18 * ((16 + (9 * T)) ^ 2)))))) : ℚ) = ((12160 + (3744 * (T ^ 2)) + (13480 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((3744 * (T ^ 2)) + (13480 * T) + 12160) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (72 + ((-88) * ((16 + (9 * T)) ^ 2)) + (16 * ((16 + (9 * T)) ^ 3)) + (36 * T) + ((-2) * (4 + (4 * T)) * (17 + (9 * T) + (18 * ((16 + (9 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (72 + ((-88) * ((16 + (9 * T)) ^ 2)) + (16 * ((16 + (9 * T)) ^ 3)) + (36 * T) + ((-2) * (4 + (4 * T)) * (17 + (9 * T) + (18 * ((16 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_lower
    have identity : (((7304 + (2016 * (T ^ 2)) + (7696 * T))) : ℚ) = ((2016 * (T ^ 2)) + (7696 * T) + 7304) := by ring
    have scaling : ((2) * ((512 + ((-16) * ((16 + (9 * T)) ^ 3)) + (124 * ((16 + (9 * T)) ^ 2)) + (288 * T) + ((4 + (4 * T)) * (17 + (9 * T) + (36 * ((16 + (9 * T)) ^ 2)))))) : ℚ) = ((7304 + (2016 * (T ^ 2)) + (7696 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((2016 * (T ^ 2)) + (7696 * T) + 7304) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (512 + ((-16) * ((16 + (9 * T)) ^ 3)) + (124 * ((16 + (9 * T)) ^ 2)) + (288 * T) + ((4 + (4 * T)) * (17 + (9 * T) + (36 * ((16 + (9 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (512 + ((-16) * ((16 + (9 * T)) ^ 3)) + (124 * ((16 + (9 * T)) ^ 2)) + (288 * T) + ((4 + (4 * T)) * (17 + (9 * T) + (36 * ((16 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_upper
    have identity : (((2816 + (1152 * (T ^ 2)) + (3616 * T))) : ℚ) = ((1152 * (T ^ 2)) + (3616 * T) + 2816) := by ring
    have scaling : ((2) * (((-504) + ((-288) * T) + ((-216) * ((16 + (9 * T)) ^ 2)) + (32 * ((16 + (9 * T)) ^ 3)) + ((-2) * (4 + (4 * T)) * (17 + (9 * T) + (36 * ((16 + (9 * T)) ^ 2)))))) : ℚ) = ((2816 + (1152 * (T ^ 2)) + (3616 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((1152 * (T ^ 2)) + (3616 * T) + 2816) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-504) + ((-288) * T) + ((-216) * ((16 + (9 * T)) ^ 2)) + (32 * ((16 + (9 * T)) ^ 3)) + ((-2) * (4 + (4 * T)) * (17 + (9 * T) + (36 * ((16 + (9 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-504) + ((-288) * T) + ((-216) * ((16 + (9 * T)) ^ 2)) + (32 * ((16 + (9 * T)) ^ 3)) + ((-2) * (4 + (4 * T)) * (17 + (9 * T) + (36 * ((16 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_old_upper
    have identity : (((19520 + (11664 * (T ^ 3)) + (47952 * (T ^ 2)) + (59364 * T))) : ℚ) = ((11664 * (T ^ 3)) + (47952 * (T ^ 2)) + (59364 * T) + 19520) := by ring
    have scaling : ((2) * (((-480) + ((-270) * T) + ((-88) * ((16 + (9 * T)) ^ 2)) + (8 * ((16 + (9 * T)) ^ 3)))) : ℚ) = ((19520 + (11664 * (T ^ 3)) + (47952 * (T ^ 2)) + (59364 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((11664 * (T ^ 3)) + (47952 * (T ^ 2)) + (59364 * T) + 19520) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-480) + ((-270) * T) + ((-88) * ((16 + (9 * T)) ^ 2)) + (8 * ((16 + (9 * T)) ^ 3))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-480) + ((-270) * T) + ((-88) * ((16 + (9 * T)) ^ 2)) + (8 * ((16 + (9 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_new_upper
    have identity : (((36800 + (23328 * (T ^ 3)) + (95256 * (T ^ 2)) + (116316 * T))) : ℚ) = ((23328 * (T ^ 3)) + (95256 * (T ^ 2)) + (116316 * T) + 36800) := by ring
    have scaling : ((2) * (((-1056) + ((-594) * T) + ((-180) * ((16 + (9 * T)) ^ 2)) + (16 * ((16 + (9 * T)) ^ 3)))) : ℚ) = ((36800 + (23328 * (T ^ 3)) + (95256 * (T ^ 2)) + (116316 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((23328 * (T ^ 3)) + (95256 * (T ^ 2)) + (116316 * T) + 36800) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-1056) + ((-594) * T) + ((-180) * ((16 + (9 * T)) ^ 2)) + (16 * ((16 + (9 * T)) ^ 3))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-1056) + ((-594) * T) + ((-180) * ((16 + (9 * T)) ^ 2)) + (16 * ((16 + (9 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring

private theorem small_a3_cmod5 (T : ℚ)
    (hT : 0 ≤ T) :
    StocksAndResidual (8) ((32 + (9 * T))) (4) (0) ((11 + (4 * T))) := by
  try dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- v_lower
    have identity : ((0) : ℚ) = (0) := by ring
    have scaling : ((2) * (0) : ℚ) = (0) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ (0) := by norm_num
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * 0 := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ 0 := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- v_stock
    have identity : (((30 + (9 * T))) : ℚ) = ((9 * T) + 30) := by ring
    have scaling : ((2) * ((15 + ((9 / 2) * T))) : ℚ) = ((30 + (9 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((9 * T) + 30) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (15 + ((9 / 2) * T)) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (15 + ((9 / 2) * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_lower
    have identity : (((22 + (8 * T))) : ℚ) = ((8 * T) + 22) := by ring
    have scaling : ((2) * ((11 + (4 * T))) : ℚ) = ((22 + (8 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((8 * T) + 22) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (11 + (4 * T)) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (11 + (4 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_stock
    have identity : (((104 + (28 * T))) : ℚ) = ((28 * T) + 104) := by ring
    have scaling : ((2) * ((52 + (14 * T))) : ℚ) = ((104 + (28 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((28 * T) + 104) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (52 + (14 * T)) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (52 + (14 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_lower
    have identity : (((5718 + (396 * (T ^ 2)) + (3018 * T))) : ℚ) = ((396 * (T ^ 2)) + (3018 * T) + 5718) := by ring
    have scaling : ((2) * ((448 + ((-8) * ((32 + (9 * T)) ^ 3)) + (60 * ((32 + (9 * T)) ^ 2)) + (126 * T) + ((11 + (4 * T)) * (33 + (9 * T) + (18 * ((32 + (9 * T)) ^ 2)))))) : ℚ) = ((5718 + (396 * (T ^ 2)) + (3018 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((396 * (T ^ 2)) + (3018 * T) + 5718) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (448 + ((-8) * ((32 + (9 * T)) ^ 3)) + (60 * ((32 + (9 * T)) ^ 2)) + (126 * T) + ((11 + (4 * T)) * (33 + (9 * T) + (18 * ((32 + (9 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (448 + ((-8) * ((32 + (9 * T)) ^ 3)) + (60 * ((32 + (9 * T)) ^ 2)) + (126 * T) + ((11 + (4 * T)) * (33 + (9 * T) + (18 * ((32 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_upper
    have identity : (((31210 + (2520 * (T ^ 2)) + (17736 * T))) : ℚ) = ((2520 * (T ^ 2)) + (17736 * T) + 31210) := by ring
    have scaling : ((2) * (((-416) + ((-117) * T) + ((-42) * ((32 + (9 * T)) ^ 2)) + (8 * ((32 + (9 * T)) ^ 3)) + ((-1) * (11 + (4 * T)) * (33 + (9 * T) + (18 * ((32 + (9 * T)) ^ 2)))))) : ℚ) = ((31210 + (2520 * (T ^ 2)) + (17736 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((2520 * (T ^ 2)) + (17736 * T) + 31210) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-416) + ((-117) * T) + ((-42) * ((32 + (9 * T)) ^ 2)) + (8 * ((32 + (9 * T)) ^ 3)) + ((-1) * (11 + (4 * T)) * (33 + (9 * T) + (18 * ((32 + (9 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-416) + ((-117) * T) + ((-42) * ((32 + (9 * T)) ^ 2)) + (8 * ((32 + (9 * T)) ^ 3)) + ((-1) * (11 + (4 * T)) * (33 + (9 * T) + (18 * ((32 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_old_upper
    have identity : (((56164 + (4392 * (T ^ 2)) + (31404 * T))) : ℚ) = ((4392 * (T ^ 2)) + (31404 * T) + 56164) := by ring
    have scaling : ((2) * ((136 + ((-88) * ((32 + (9 * T)) ^ 2)) + (16 * ((32 + (9 * T)) ^ 3)) + (36 * T) + ((-2) * (11 + (4 * T)) * (33 + (9 * T) + (18 * ((32 + (9 * T)) ^ 2)))))) : ℚ) = ((56164 + (4392 * (T ^ 2)) + (31404 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((4392 * (T ^ 2)) + (31404 * T) + 56164) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (136 + ((-88) * ((32 + (9 * T)) ^ 2)) + (16 * ((32 + (9 * T)) ^ 3)) + (36 * T) + ((-2) * (11 + (4 * T)) * (33 + (9 * T) + (18 * ((32 + (9 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (136 + ((-88) * ((32 + (9 * T)) ^ 2)) + (16 * ((32 + (9 * T)) ^ 3)) + (36 * T) + ((-2) * (11 + (4 * T)) * (33 + (9 * T) + (18 * ((32 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_lower
    have identity : (((19158 + (1368 * (T ^ 2)) + (10254 * T))) : ℚ) = ((1368 * (T ^ 2)) + (10254 * T) + 19158) := by ring
    have scaling : ((2) * ((1024 + ((-16) * ((32 + (9 * T)) ^ 3)) + (124 * ((32 + (9 * T)) ^ 2)) + (288 * T) + ((11 + (4 * T)) * (33 + (9 * T) + (36 * ((32 + (9 * T)) ^ 2)))))) : ℚ) = ((19158 + (1368 * (T ^ 2)) + (10254 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((1368 * (T ^ 2)) + (10254 * T) + 19158) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (1024 + ((-16) * ((32 + (9 * T)) ^ 3)) + (124 * ((32 + (9 * T)) ^ 2)) + (288 * T) + ((11 + (4 * T)) * (33 + (9 * T) + (36 * ((32 + (9 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (1024 + ((-16) * ((32 + (9 * T)) ^ 3)) + (124 * ((32 + (9 * T)) ^ 2)) + (288 * T) + ((11 + (4 * T)) * (33 + (9 * T) + (36 * ((32 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_upper
    have identity : (((29284 + (2448 * (T ^ 2)) + (16932 * T))) : ℚ) = ((2448 * (T ^ 2)) + (16932 * T) + 29284) := by ring
    have scaling : ((2) * (((-1016) + ((-288) * T) + ((-216) * ((32 + (9 * T)) ^ 2)) + (32 * ((32 + (9 * T)) ^ 3)) + ((-2) * (11 + (4 * T)) * (33 + (9 * T) + (36 * ((32 + (9 * T)) ^ 2)))))) : ℚ) = ((29284 + (2448 * (T ^ 2)) + (16932 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((2448 * (T ^ 2)) + (16932 * T) + 29284) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-1016) + ((-288) * T) + ((-216) * ((32 + (9 * T)) ^ 2)) + (32 * ((32 + (9 * T)) ^ 3)) + ((-2) * (11 + (4 * T)) * (33 + (9 * T) + (36 * ((32 + (9 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-1016) + ((-288) * T) + ((-216) * ((32 + (9 * T)) ^ 2)) + (32 * ((32 + (9 * T)) ^ 3)) + ((-2) * (11 + (4 * T)) * (33 + (9 * T) + (36 * ((32 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_old_upper
    have identity : (((342144 + (11664 * (T ^ 3)) + (110160 * (T ^ 2)) + (340452 * T))) : ℚ) = ((11664 * (T ^ 3)) + (110160 * (T ^ 2)) + (340452 * T) + 342144) := by ring
    have scaling : ((2) * (((-960) + ((-270) * T) + ((-88) * ((32 + (9 * T)) ^ 2)) + (8 * ((32 + (9 * T)) ^ 3)))) : ℚ) = ((342144 + (11664 * (T ^ 3)) + (110160 * (T ^ 2)) + (340452 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((11664 * (T ^ 3)) + (110160 * (T ^ 2)) + (340452 * T) + 342144) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-960) + ((-270) * T) + ((-88) * ((32 + (9 * T)) ^ 2)) + (8 * ((32 + (9 * T)) ^ 3))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-960) + ((-270) * T) + ((-88) * ((32 + (9 * T)) ^ 2)) + (8 * ((32 + (9 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_new_upper
    have identity : (((675712 + (23328 * (T ^ 3)) + (219672 * (T ^ 2)) + (676188 * T))) : ℚ) = ((23328 * (T ^ 3)) + (219672 * (T ^ 2)) + (676188 * T) + 675712) := by ring
    have scaling : ((2) * (((-2112) + ((-594) * T) + ((-180) * ((32 + (9 * T)) ^ 2)) + (16 * ((32 + (9 * T)) ^ 3)))) : ℚ) = ((675712 + (23328 * (T ^ 3)) + (219672 * (T ^ 2)) + (676188 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((23328 * (T ^ 3)) + (219672 * (T ^ 2)) + (676188 * T) + 675712) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-2112) + ((-594) * T) + ((-180) * ((32 + (9 * T)) ^ 2)) + (16 * ((32 + (9 * T)) ^ 3))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-2112) + ((-594) * T) + ((-180) * ((32 + (9 * T)) ^ 2)) + (16 * ((32 + (9 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.PlusTwo
