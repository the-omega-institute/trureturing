/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakAdjacentTail/PlusTwoAtTwo
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakAdjacentTail/PlusTwoAtTwo
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

private theorem small_a2_cmod0 (T : ℚ)
    (hT : 0 ≤ T) :
    StocksAndResidual (4) ((16 + (5 * T))) (4) (0) ((10 + (4 * T))) := by
  dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- v_lower
    have identity : ((0) : ℚ) = (0) := by ring
    have scaling : ((2) * (0) : ℚ) = (0) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ (0) := by norm_num
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * 0 := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ 0 := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- v_stock
    have identity : (((14 + (5 * T))) : ℚ) = ((5 * T) + 14) := by ring
    have scaling : ((2) * ((7 + ((5 / 2) * T))) : ℚ) = ((14 + (5 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((5 * T) + 14) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (7 + ((5 / 2) * T)) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (7 + ((5 / 2) * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_lower
    have identity : (((20 + (8 * T))) : ℚ) = ((8 * T) + 20) := by ring
    have scaling : ((2) * ((10 + (4 * T))) : ℚ) = ((20 + (8 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((8 * T) + 20) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (10 + (4 * T)) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (10 + (4 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_stock
    have identity : (((42 + (12 * T))) : ℚ) = ((12 * T) + 42) := by ring
    have scaling : ((2) * ((21 + (6 * T))) : ℚ) = ((42 + (12 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((12 * T) + 42) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (21 + (6 * T)) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (21 + (6 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_lower
    have identity : (((532 + (40 * (T ^ 2)) + (296 * T))) : ℚ) = ((40 * (T ^ 2)) + (296 * T) + 532) := by ring
    have scaling : ((2) * ((96 + ((-8) * ((16 + (5 * T)) ^ 3)) + (28 * ((16 + (5 * T)) ^ 2)) + (30 * T) + ((10 + (4 * T)) * (17 + (5 * T) + (10 * ((16 + (5 * T)) ^ 2)))))) : ℚ) = ((532 + (40 * (T ^ 2)) + (296 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((40 * (T ^ 2)) + (296 * T) + 532) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (96 + ((-8) * ((16 + (5 * T)) ^ 3)) + (28 * ((16 + (5 * T)) ^ 2)) + (30 * T) + ((10 + (4 * T)) * (17 + (5 * T) + (10 * ((16 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (96 + ((-8) * ((16 + (5 * T)) ^ 3)) + (28 * ((16 + (5 * T)) ^ 2)) + (30 * T) + ((10 + (4 * T)) * (17 + (5 * T) + (10 * ((16 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_upper
    have identity : (((4620 + (460 * (T ^ 2)) + (2914 * T))) : ℚ) = ((460 * (T ^ 2)) + (2914 * T) + 4620) := by ring
    have scaling : ((2) * (((-80) + ((-25) * T) + ((-18) * ((16 + (5 * T)) ^ 2)) + (8 * ((16 + (5 * T)) ^ 3)) + ((-1) * (10 + (4 * T)) * (17 + (5 * T) + (10 * ((16 + (5 * T)) ^ 2)))))) : ℚ) = ((4620 + (460 * (T ^ 2)) + (2914 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((460 * (T ^ 2)) + (2914 * T) + 4620) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-80) + ((-25) * T) + ((-18) * ((16 + (5 * T)) ^ 2)) + (8 * ((16 + (5 * T)) ^ 3)) + ((-1) * (10 + (4 * T)) * (17 + (5 * T) + (10 * ((16 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-80) + ((-25) * T) + ((-18) * ((16 + (5 * T)) ^ 2)) + (8 * ((16 + (5 * T)) ^ 3)) + ((-1) * (10 + (4 * T)) * (17 + (5 * T) + (10 * ((16 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_old_upper
    have identity : (((7648 + (720 * (T ^ 2)) + (4688 * T))) : ℚ) = ((720 * (T ^ 2)) + (4688 * T) + 7648) := by ring
    have scaling : ((2) * ((68 + ((-40) * ((16 + (5 * T)) ^ 2)) + (16 * ((16 + (5 * T)) ^ 3)) + (20 * T) + ((-2) * (10 + (4 * T)) * (17 + (5 * T) + (10 * ((16 + (5 * T)) ^ 2)))))) : ℚ) = ((7648 + (720 * (T ^ 2)) + (4688 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((720 * (T ^ 2)) + (4688 * T) + 7648) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (68 + ((-40) * ((16 + (5 * T)) ^ 2)) + (16 * ((16 + (5 * T)) ^ 3)) + (20 * T) + ((-2) * (10 + (4 * T)) * (17 + (5 * T) + (10 * ((16 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (68 + ((-40) * ((16 + (5 * T)) ^ 2)) + (16 * ((16 + (5 * T)) ^ 3)) + (20 * T) + ((-2) * (10 + (4 * T)) * (17 + (5 * T) + (10 * ((16 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_lower
    have identity : (((2900 + (240 * (T ^ 2)) + (1676 * T))) : ℚ) = ((240 * (T ^ 2)) + (1676 * T) + 2900) := by ring
    have scaling : ((2) * ((256 + ((-16) * ((16 + (5 * T)) ^ 3)) + (60 * ((16 + (5 * T)) ^ 2)) + (80 * T) + ((10 + (4 * T)) * (17 + (5 * T) + (20 * ((16 + (5 * T)) ^ 2)))))) : ℚ) = ((2900 + (240 * (T ^ 2)) + (1676 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((240 * (T ^ 2)) + (1676 * T) + 2900) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (256 + ((-16) * ((16 + (5 * T)) ^ 3)) + (60 * ((16 + (5 * T)) ^ 2)) + (80 * T) + ((10 + (4 * T)) * (17 + (5 * T) + (20 * ((16 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (256 + ((-16) * ((16 + (5 * T)) ^ 3)) + (60 * ((16 + (5 * T)) ^ 2)) + (80 * T) + ((10 + (4 * T)) * (17 + (5 * T) + (20 * ((16 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_upper
    have identity : (((2912 + (320 * (T ^ 2)) + (1928 * T))) : ℚ) = ((320 * (T ^ 2)) + (1928 * T) + 2912) := by ring
    have scaling : ((2) * (((-252) + ((-104) * ((16 + (5 * T)) ^ 2)) + ((-80) * T) + (32 * ((16 + (5 * T)) ^ 3)) + ((-2) * (10 + (4 * T)) * (17 + (5 * T) + (20 * ((16 + (5 * T)) ^ 2)))))) : ℚ) = ((2912 + (320 * (T ^ 2)) + (1928 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((320 * (T ^ 2)) + (1928 * T) + 2912) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-252) + ((-104) * ((16 + (5 * T)) ^ 2)) + ((-80) * T) + (32 * ((16 + (5 * T)) ^ 3)) + ((-2) * (10 + (4 * T)) * (17 + (5 * T) + (20 * ((16 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-252) + ((-104) * ((16 + (5 * T)) ^ 2)) + ((-80) * T) + (32 * ((16 + (5 * T)) ^ 3)) + ((-2) * (10 + (4 * T)) * (17 + (5 * T) + (20 * ((16 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_old_upper
    have identity : (((44608 + (2000 * (T ^ 3)) + (17200 * (T ^ 2)) + (48500 * T))) : ℚ) = ((2000 * (T ^ 3)) + (17200 * (T ^ 2)) + (48500 * T) + 44608) := by ring
    have scaling : ((2) * (((-224) + ((-70) * T) + ((-40) * ((16 + (5 * T)) ^ 2)) + (8 * ((16 + (5 * T)) ^ 3)))) : ℚ) = ((44608 + (2000 * (T ^ 3)) + (17200 * (T ^ 2)) + (48500 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((2000 * (T ^ 3)) + (17200 * (T ^ 2)) + (48500 * T) + 44608) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-224) + ((-70) * T) + ((-40) * ((16 + (5 * T)) ^ 2)) + (8 * ((16 + (5 * T)) ^ 3))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-224) + ((-70) * T) + ((-40) * ((16 + (5 * T)) ^ 2)) + (8 * ((16 + (5 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_new_upper
    have identity : (((86976 + (4000 * (T ^ 3)) + (34200 * (T ^ 2)) + (95660 * T))) : ℚ) = ((4000 * (T ^ 3)) + (34200 * (T ^ 2)) + (95660 * T) + 86976) := by ring
    have scaling : ((2) * (((-544) + ((-170) * T) + ((-84) * ((16 + (5 * T)) ^ 2)) + (16 * ((16 + (5 * T)) ^ 3)))) : ℚ) = ((86976 + (4000 * (T ^ 3)) + (34200 * (T ^ 2)) + (95660 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((4000 * (T ^ 3)) + (34200 * (T ^ 2)) + (95660 * T) + 86976) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-544) + ((-170) * T) + ((-84) * ((16 + (5 * T)) ^ 2)) + (16 * ((16 + (5 * T)) ^ 3))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-544) + ((-170) * T) + ((-84) * ((16 + (5 * T)) ^ 2)) + (16 * ((16 + (5 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring

private theorem small_a2_cmod1 (T : ℚ)
    (hT : 0 ≤ T) :
    StocksAndResidual (4) ((512 + (5 * T))) (4) (4) ((394 + (4 * T))) := by
  dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- v_lower
    have identity : ((8) : ℚ) = (8) := by ring
    have scaling : ((2) * (4) : ℚ) = (8) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ (8) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * 4 := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ 4 := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- v_stock
    have identity : (((502 + (5 * T))) : ℚ) = ((5 * T) + 502) := by ring
    have scaling : ((2) * ((251 + ((5 / 2) * T))) : ℚ) = ((502 + (5 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((5 * T) + 502) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (251 + ((5 / 2) * T)) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (251 + ((5 / 2) * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_lower
    have identity : (((788 + (8 * T))) : ℚ) = ((8 * T) + 788) := by ring
    have scaling : ((2) * ((394 + (4 * T))) : ℚ) = ((788 + (8 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((8 * T) + 788) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (394 + (4 * T)) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (394 + (4 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_stock
    have identity : (((1258 + (12 * T))) : ℚ) = ((12 * T) + 1258) := by ring
    have scaling : ((2) * ((629 + (6 * T))) : ℚ) = ((1258 + (12 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((12 * T) + 1258) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (629 + (6 * T)) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (629 + (6 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_lower
    have identity : (((451356 + (40 * (T ^ 2)) + (8504 * T))) : ℚ) = ((40 * (T ^ 2)) + (8504 * T) + 451356) := by ring
    have scaling : ((2) * ((23556 + ((-8) * ((512 + (5 * T)) ^ 3)) + (156 * ((512 + (5 * T)) ^ 2)) + (230 * T) + ((394 + (4 * T)) * (513 + (5 * T) + (10 * ((512 + (5 * T)) ^ 2)))))) : ℚ) = ((451356 + (40 * (T ^ 2)) + (8504 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((40 * (T ^ 2)) + (8504 * T) + 451356) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (23556 + ((-8) * ((512 + (5 * T)) ^ 3)) + (156 * ((512 + (5 * T)) ^ 2)) + (230 * T) + ((394 + (4 * T)) * (513 + (5 * T) + (10 * ((512 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (23556 + ((-8) * ((512 + (5 * T)) ^ 3)) + (156 * ((512 + (5 * T)) ^ 2)) + (230 * T) + ((394 + (4 * T)) * (513 + (5 * T) + (10 * ((512 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_upper
    have identity : (((4792548 + (460 * (T ^ 2)) + (93906 * T))) : ℚ) = ((460 * (T ^ 2)) + (93906 * T) + 4792548) := by ring
    have scaling : ((2) * (((-23044) + ((-225) * T) + ((-146) * ((512 + (5 * T)) ^ 2)) + (8 * ((512 + (5 * T)) ^ 3)) + ((-1) * (394 + (4 * T)) * (513 + (5 * T) + (10 * ((512 + (5 * T)) ^ 2)))))) : ℚ) = ((4792548 + (460 * (T ^ 2)) + (93906 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((460 * (T ^ 2)) + (93906 * T) + 4792548) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-23044) + ((-225) * T) + ((-146) * ((512 + (5 * T)) ^ 2)) + (8 * ((512 + (5 * T)) ^ 3)) + ((-1) * (394 + (4 * T)) * (513 + (5 * T) + (10 * ((512 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-23044) + ((-225) * T) + ((-146) * ((512 + (5 * T)) ^ 2)) + (8 * ((512 + (5 * T)) ^ 3)) + ((-1) * (394 + (4 * T)) * (513 + (5 * T) + (10 * ((512 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_old_upper
    have identity : (((7502288 + (720 * (T ^ 2)) + (146992 * T))) : ℚ) = ((720 * (T ^ 2)) + (146992 * T) + 7502288) := by ring
    have scaling : ((2) * (((-38916) + ((-380) * T) + ((-296) * ((512 + (5 * T)) ^ 2)) + (16 * ((512 + (5 * T)) ^ 3)) + ((-2) * (394 + (4 * T)) * (513 + (5 * T) + (10 * ((512 + (5 * T)) ^ 2)))))) : ℚ) = ((7502288 + (720 * (T ^ 2)) + (146992 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((720 * (T ^ 2)) + (146992 * T) + 7502288) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-38916) + ((-380) * T) + ((-296) * ((512 + (5 * T)) ^ 2)) + (16 * ((512 + (5 * T)) ^ 3)) + ((-2) * (394 + (4 * T)) * (513 + (5 * T) + (10 * ((512 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-38916) + ((-380) * T) + ((-296) * ((512 + (5 * T)) ^ 2)) + (16 * ((512 + (5 * T)) ^ 3)) + ((-2) * (394 + (4 * T)) * (513 + (5 * T) + (10 * ((512 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_lower
    have identity : (((2599708 + (240 * (T ^ 2)) + (49964 * T))) : ℚ) = ((240 * (T ^ 2)) + (49964 * T) + 2599708) := by ring
    have scaling : ((2) * ((49156 + ((-16) * ((512 + (5 * T)) ^ 3)) + (316 * ((512 + (5 * T)) ^ 2)) + (480 * T) + ((394 + (4 * T)) * (513 + (5 * T) + (20 * ((512 + (5 * T)) ^ 2)))))) : ℚ) = ((2599708 + (240 * (T ^ 2)) + (49964 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((240 * (T ^ 2)) + (49964 * T) + 2599708) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (49156 + ((-16) * ((512 + (5 * T)) ^ 3)) + (316 * ((512 + (5 * T)) ^ 2)) + (480 * T) + ((394 + (4 * T)) * (513 + (5 * T) + (20 * ((512 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (49156 + ((-16) * ((512 + (5 * T)) ^ 3)) + (316 * ((512 + (5 * T)) ^ 2)) + (480 * T) + ((394 + (4 * T)) * (513 + (5 * T) + (20 * ((512 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_upper
    have identity : (((3205584 + (320 * (T ^ 2)) + (64072 * T))) : ℚ) = ((320 * (T ^ 2)) + (64072 * T) + 3205584) := by ring
    have scaling : ((2) * (((-90116) + ((-880) * T) + ((-616) * ((512 + (5 * T)) ^ 2)) + (32 * ((512 + (5 * T)) ^ 3)) + ((-2) * (394 + (4 * T)) * (513 + (5 * T) + (20 * ((512 + (5 * T)) ^ 2)))))) : ℚ) = ((3205584 + (320 * (T ^ 2)) + (64072 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((320 * (T ^ 2)) + (64072 * T) + 3205584) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-90116) + ((-880) * T) + ((-616) * ((512 + (5 * T)) ^ 2)) + (32 * ((512 + (5 * T)) ^ 3)) + ((-2) * (394 + (4 * T)) * (513 + (5 * T) + (20 * ((512 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-90116) + ((-880) * T) + ((-616) * ((512 + (5 * T)) ^ 2)) + (32 * ((512 + (5 * T)) ^ 3)) + ((-2) * (394 + (4 * T)) * (513 + (5 * T) + (20 * ((512 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_old_upper
    have identity : (((1992198128 + (2000 * (T ^ 3)) + (599600 * (T ^ 2)) + (59882580 * T))) : ℚ) = ((2000 * (T ^ 3)) + (599600 * (T ^ 2)) + (59882580 * T) + 1992198128) := by ring
    have scaling : ((2) * (((-48136) + ((-470) * T) + ((-296) * ((512 + (5 * T)) ^ 2)) + (8 * ((512 + (5 * T)) ^ 3)))) : ℚ) = ((1992198128 + (2000 * (T ^ 3)) + (599600 * (T ^ 2)) + (59882580 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((2000 * (T ^ 3)) + (599600 * (T ^ 2)) + (59882580 * T) + 1992198128) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-48136) + ((-470) * T) + ((-296) * ((512 + (5 * T)) ^ 2)) + (8 * ((512 + (5 * T)) ^ 3))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-48136) + ((-470) * T) + ((-296) * ((512 + (5 * T)) ^ 2)) + (8 * ((512 + (5 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_new_upper
    have identity : (((3982292976 + (4000 * (T ^ 3)) + (1199000 * (T ^ 2)) + (119724140 * T))) : ℚ) = ((4000 * (T ^ 3)) + (1199000 * (T ^ 2)) + (119724140 * T) + 3982292976) := by ring
    have scaling : ((2) * (((-99336) + ((-970) * T) + ((-596) * ((512 + (5 * T)) ^ 2)) + (16 * ((512 + (5 * T)) ^ 3)))) : ℚ) = ((3982292976 + (4000 * (T ^ 3)) + (1199000 * (T ^ 2)) + (119724140 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((4000 * (T ^ 3)) + (1199000 * (T ^ 2)) + (119724140 * T) + 3982292976) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-99336) + ((-970) * T) + ((-596) * ((512 + (5 * T)) ^ 2)) + (16 * ((512 + (5 * T)) ^ 3))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-99336) + ((-970) * T) + ((-596) * ((512 + (5 * T)) ^ 2)) + (16 * ((512 + (5 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring

private theorem small_a2_cmod2 (T : ℚ)
    (hT : 0 ≤ T) :
    StocksAndResidual (4) ((64 + (5 * T))) (4) (2) ((42 + (4 * T))) := by
  dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- v_lower
    have identity : ((4) : ℚ) = (4) := by ring
    have scaling : ((2) * (2) : ℚ) = (4) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ (4) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * 2 := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ 2 := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- v_stock
    have identity : (((58 + (5 * T))) : ℚ) = ((5 * T) + 58) := by ring
    have scaling : ((2) * ((29 + ((5 / 2) * T))) : ℚ) = ((58 + (5 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((5 * T) + 58) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (29 + ((5 / 2) * T)) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (29 + ((5 / 2) * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_lower
    have identity : (((84 + (8 * T))) : ℚ) = ((8 * T) + 84) := by ring
    have scaling : ((2) * ((42 + (4 * T))) : ℚ) = ((84 + (8 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((8 * T) + 84) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (42 + (4 * T)) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (42 + (4 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_stock
    have identity : (((170 + (12 * T))) : ℚ) = ((12 * T) + 170) := by ring
    have scaling : ((2) * ((85 + (6 * T))) : ℚ) = ((170 + (12 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((12 * T) + 170) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (85 + (6 * T)) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (85 + (6 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_lower
    have identity : (((8792 + (40 * (T ^ 2)) + (1200 * T))) : ℚ) = ((40 * (T ^ 2)) + (1200 * T) + 8792) := by ring
    have scaling : ((2) * ((1666 + ((-8) * ((64 + (5 * T)) ^ 3)) + (92 * ((64 + (5 * T)) ^ 2)) + (130 * T) + ((42 + (4 * T)) * (65 + (5 * T) + (10 * ((64 + (5 * T)) ^ 2)))))) : ℚ) = ((8792 + (40 * (T ^ 2)) + (1200 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((40 * (T ^ 2)) + (1200 * T) + 8792) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (1666 + ((-8) * ((64 + (5 * T)) ^ 3)) + (92 * ((64 + (5 * T)) ^ 2)) + (130 * T) + ((42 + (4 * T)) * (65 + (5 * T) + (10 * ((64 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (1666 + ((-8) * ((64 + (5 * T)) ^ 3)) + (92 * ((64 + (5 * T)) ^ 2)) + (130 * T) + ((42 + (4 * T)) * (65 + (5 * T) + (10 * ((64 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_upper
    have identity : (((73256 + (460 * (T ^ 2)) + (11610 * T))) : ℚ) = ((460 * (T ^ 2)) + (11610 * T) + 73256) := by ring
    have scaling : ((2) * (((-1602) + ((-125) * T) + ((-82) * ((64 + (5 * T)) ^ 2)) + (8 * ((64 + (5 * T)) ^ 3)) + ((-1) * (42 + (4 * T)) * (65 + (5 * T) + (10 * ((64 + (5 * T)) ^ 2)))))) : ℚ) = ((73256 + (460 * (T ^ 2)) + (11610 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((460 * (T ^ 2)) + (11610 * T) + 73256) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-1602) + ((-125) * T) + ((-82) * ((64 + (5 * T)) ^ 2)) + (8 * ((64 + (5 * T)) ^ 3)) + ((-1) * (42 + (4 * T)) * (65 + (5 * T) + (10 * ((64 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-1602) + ((-125) * T) + ((-82) * ((64 + (5 * T)) ^ 2)) + (8 * ((64 + (5 * T)) ^ 3)) + ((-1) * (42 + (4 * T)) * (65 + (5 * T) + (10 * ((64 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_old_upper
    have identity : (((115544 + (720 * (T ^ 2)) + (18240 * T))) : ℚ) = ((720 * (T ^ 2)) + (18240 * T) + 115544) := by ring
    have scaling : ((2) * (((-2304) + ((-180) * T) + ((-168) * ((64 + (5 * T)) ^ 2)) + (16 * ((64 + (5 * T)) ^ 3)) + ((-2) * (42 + (4 * T)) * (65 + (5 * T) + (10 * ((64 + (5 * T)) ^ 2)))))) : ℚ) = ((115544 + (720 * (T ^ 2)) + (18240 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((720 * (T ^ 2)) + (18240 * T) + 115544) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-2304) + ((-180) * T) + ((-168) * ((64 + (5 * T)) ^ 2)) + (16 * ((64 + (5 * T)) ^ 3)) + ((-2) * (42 + (4 * T)) * (65 + (5 * T) + (10 * ((64 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-2304) + ((-180) * T) + ((-168) * ((64 + (5 * T)) ^ 2)) + (16 * ((64 + (5 * T)) ^ 3)) + ((-2) * (42 + (4 * T)) * (65 + (5 * T) + (10 * ((64 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_lower
    have identity : (((45400 + (240 * (T ^ 2)) + (6620 * T))) : ℚ) = ((240 * (T ^ 2)) + (6620 * T) + 45400) := by ring
    have scaling : ((2) * ((3586 + ((-16) * ((64 + (5 * T)) ^ 3)) + (188 * ((64 + (5 * T)) ^ 2)) + (280 * T) + ((42 + (4 * T)) * (65 + (5 * T) + (20 * ((64 + (5 * T)) ^ 2)))))) : ℚ) = ((45400 + (240 * (T ^ 2)) + (6620 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((240 * (T ^ 2)) + (6620 * T) + 45400) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (3586 + ((-16) * ((64 + (5 * T)) ^ 3)) + (188 * ((64 + (5 * T)) ^ 2)) + (280 * T) + ((42 + (4 * T)) * (65 + (5 * T) + (20 * ((64 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (3586 + ((-16) * ((64 + (5 * T)) ^ 3)) + (188 * ((64 + (5 * T)) ^ 2)) + (280 * T) + ((42 + (4 * T)) * (65 + (5 * T) + (20 * ((64 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_upper
    have identity : (((42328 + (320 * (T ^ 2)) + (7400 * T))) : ℚ) = ((320 * (T ^ 2)) + (7400 * T) + 42328) := by ring
    have scaling : ((2) * (((-6144) + ((-480) * T) + ((-360) * ((64 + (5 * T)) ^ 2)) + (32 * ((64 + (5 * T)) ^ 3)) + ((-2) * (42 + (4 * T)) * (65 + (5 * T) + (20 * ((64 + (5 * T)) ^ 2)))))) : ℚ) = ((42328 + (320 * (T ^ 2)) + (7400 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((320 * (T ^ 2)) + (7400 * T) + 42328) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-6144) + ((-480) * T) + ((-360) * ((64 + (5 * T)) ^ 2)) + (32 * ((64 + (5 * T)) ^ 3)) + ((-2) * (42 + (4 * T)) * (65 + (5 * T) + (20 * ((64 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-6144) + ((-480) * T) + ((-360) * ((64 + (5 * T)) ^ 2)) + (32 * ((64 + (5 * T)) ^ 3)) + ((-2) * (42 + (4 * T)) * (65 + (5 * T) + (20 * ((64 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_old_upper
    have identity : (((2811128 + (2000 * (T ^ 3)) + (68400 * (T ^ 2)) + (767460 * T))) : ℚ) = ((2000 * (T ^ 3)) + (68400 * (T ^ 2)) + (767460 * T) + 2811128) := by ring
    have scaling : ((2) * (((-3460) + ((-270) * T) + ((-168) * ((64 + (5 * T)) ^ 2)) + (8 * ((64 + (5 * T)) ^ 3)))) : ℚ) = ((2811128 + (2000 * (T ^ 3)) + (68400 * (T ^ 2)) + (767460 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((2000 * (T ^ 3)) + (68400 * (T ^ 2)) + (767460 * T) + 2811128) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-3460) + ((-270) * T) + ((-168) * ((64 + (5 * T)) ^ 2)) + (8 * ((64 + (5 * T)) ^ 3))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-3460) + ((-270) * T) + ((-168) * ((64 + (5 * T)) ^ 2)) + (8 * ((64 + (5 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_new_upper
    have identity : (((5588728 + (4000 * (T ^ 3)) + (136600 * (T ^ 2)) + (1529740 * T))) : ℚ) = ((4000 * (T ^ 3)) + (136600 * (T ^ 2)) + (1529740 * T) + 5588728) := by ring
    have scaling : ((2) * (((-7300) + ((-570) * T) + ((-340) * ((64 + (5 * T)) ^ 2)) + (16 * ((64 + (5 * T)) ^ 3)))) : ℚ) = ((5588728 + (4000 * (T ^ 3)) + (136600 * (T ^ 2)) + (1529740 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((4000 * (T ^ 3)) + (136600 * (T ^ 2)) + (1529740 * T) + 5588728) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-7300) + ((-570) * T) + ((-340) * ((64 + (5 * T)) ^ 2)) + (16 * ((64 + (5 * T)) ^ 3))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-7300) + ((-570) * T) + ((-340) * ((64 + (5 * T)) ^ 2)) + (16 * ((64 + (5 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring

private theorem small_a2_cmod3 (T : ℚ)
    (hT : 0 ≤ T) :
    StocksAndResidual (4) ((128 + (5 * T))) (4) (3) ((90 + (4 * T))) := by
  dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- v_lower
    have identity : ((6) : ℚ) = (6) := by ring
    have scaling : ((2) * (3) : ℚ) = (6) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ (6) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * 3 := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ 3 := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- v_stock
    have identity : (((120 + (5 * T))) : ℚ) = ((5 * T) + 120) := by ring
    have scaling : ((2) * ((60 + ((5 / 2) * T))) : ℚ) = ((120 + (5 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((5 * T) + 120) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (60 + ((5 / 2) * T)) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (60 + ((5 / 2) * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_lower
    have identity : (((180 + (8 * T))) : ℚ) = ((8 * T) + 180) := by ring
    have scaling : ((2) * ((90 + (4 * T))) : ℚ) = ((180 + (8 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((8 * T) + 180) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (90 + (4 * T)) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (90 + (4 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_stock
    have identity : (((330 + (12 * T))) : ℚ) = ((12 * T) + 330) := by ring
    have scaling : ((2) * ((165 + (6 * T))) : ℚ) = ((330 + (12 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((12 * T) + 330) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (165 + (6 * T)) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (165 + (6 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_lower
    have identity : (((32442 + (40 * (T ^ 2)) + (2292 * T))) : ℚ) = ((40 * (T ^ 2)) + (2292 * T) + 32442) := by ring
    have scaling : ((2) * ((4611 + ((-8) * ((128 + (5 * T)) ^ 3)) + (124 * ((128 + (5 * T)) ^ 2)) + (180 * T) + ((90 + (4 * T)) * (129 + (5 * T) + (10 * ((128 + (5 * T)) ^ 2)))))) : ℚ) = ((32442 + (40 * (T ^ 2)) + (2292 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((40 * (T ^ 2)) + (2292 * T) + 32442) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (4611 + ((-8) * ((128 + (5 * T)) ^ 3)) + (124 * ((128 + (5 * T)) ^ 2)) + (180 * T) + ((90 + (4 * T)) * (129 + (5 * T) + (10 * ((128 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (4611 + ((-8) * ((128 + (5 * T)) ^ 3)) + (124 * ((128 + (5 * T)) ^ 2)) + (180 * T) + ((90 + (4 * T)) * (129 + (5 * T) + (10 * ((128 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_upper
    have identity : (((295494 + (460 * (T ^ 2)) + (23318 * T))) : ℚ) = ((460 * (T ^ 2)) + (23318 * T) + 295494) := by ring
    have scaling : ((2) * (((-4483) + ((-175) * T) + ((-114) * ((128 + (5 * T)) ^ 2)) + (8 * ((128 + (5 * T)) ^ 3)) + ((-1) * (90 + (4 * T)) * (129 + (5 * T) + (10 * ((128 + (5 * T)) ^ 2)))))) : ℚ) = ((295494 + (460 * (T ^ 2)) + (23318 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((460 * (T ^ 2)) + (23318 * T) + 295494) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-4483) + ((-175) * T) + ((-114) * ((128 + (5 * T)) ^ 2)) + (8 * ((128 + (5 * T)) ^ 3)) + ((-1) * (90 + (4 * T)) * (129 + (5 * T) + (10 * ((128 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-4483) + ((-175) * T) + ((-114) * ((128 + (5 * T)) ^ 2)) + (8 * ((128 + (5 * T)) ^ 3)) + ((-1) * (90 + (4 * T)) * (129 + (5 * T) + (10 * ((128 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_old_upper
    have identity : (((463508 + (720 * (T ^ 2)) + (36536 * T))) : ℚ) = ((720 * (T ^ 2)) + (36536 * T) + 463508) := by ring
    have scaling : ((2) * (((-7170) + ((-280) * T) + ((-232) * ((128 + (5 * T)) ^ 2)) + (16 * ((128 + (5 * T)) ^ 3)) + ((-2) * (90 + (4 * T)) * (129 + (5 * T) + (10 * ((128 + (5 * T)) ^ 2)))))) : ℚ) = ((463508 + (720 * (T ^ 2)) + (36536 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((720 * (T ^ 2)) + (36536 * T) + 463508) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-7170) + ((-280) * T) + ((-232) * ((128 + (5 * T)) ^ 2)) + (16 * ((128 + (5 * T)) ^ 3)) + ((-2) * (90 + (4 * T)) * (129 + (5 * T) + (10 * ((128 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-7170) + ((-280) * T) + ((-232) * ((128 + (5 * T)) ^ 2)) + (16 * ((128 + (5 * T)) ^ 3)) + ((-2) * (90 + (4 * T)) * (129 + (5 * T) + (10 * ((128 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_lower
    have identity : (((173754 + (240 * (T ^ 2)) + (12932 * T))) : ℚ) = ((240 * (T ^ 2)) + (12932 * T) + 173754) := by ring
    have scaling : ((2) * ((9731 + ((-16) * ((128 + (5 * T)) ^ 3)) + (252 * ((128 + (5 * T)) ^ 2)) + (380 * T) + ((90 + (4 * T)) * (129 + (5 * T) + (20 * ((128 + (5 * T)) ^ 2)))))) : ℚ) = ((173754 + (240 * (T ^ 2)) + (12932 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((240 * (T ^ 2)) + (12932 * T) + 173754) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * (9731 + ((-16) * ((128 + (5 * T)) ^ 3)) + (252 * ((128 + (5 * T)) ^ 2)) + (380 * T) + ((90 + (4 * T)) * (129 + (5 * T) + (20 * ((128 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (9731 + ((-16) * ((128 + (5 * T)) ^ 3)) + (252 * ((128 + (5 * T)) ^ 2)) + (380 * T) + ((90 + (4 * T)) * (129 + (5 * T) + (20 * ((128 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_upper
    have identity : (((180884 + (320 * (T ^ 2)) + (15256 * T))) : ℚ) = ((320 * (T ^ 2)) + (15256 * T) + 180884) := by ring
    have scaling : ((2) * (((-17410) + ((-680) * T) + ((-488) * ((128 + (5 * T)) ^ 2)) + (32 * ((128 + (5 * T)) ^ 3)) + ((-2) * (90 + (4 * T)) * (129 + (5 * T) + (20 * ((128 + (5 * T)) ^ 2)))))) : ℚ) = ((180884 + (320 * (T ^ 2)) + (15256 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((320 * (T ^ 2)) + (15256 * T) + 180884) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-17410) + ((-680) * T) + ((-488) * ((128 + (5 * T)) ^ 2)) + (32 * ((128 + (5 * T)) ^ 3)) + ((-2) * (90 + (4 * T)) * (129 + (5 * T) + (20 * ((128 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-17410) + ((-680) * T) + ((-488) * ((128 + (5 * T)) ^ 2)) + (32 * ((128 + (5 * T)) ^ 3)) + ((-2) * (90 + (4 * T)) * (129 + (5 * T) + (20 * ((128 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_old_upper
    have identity : (((25933300 + (2000 * (T ^ 3)) + (142000 * (T ^ 2)) + (3337500 * T))) : ℚ) = ((2000 * (T ^ 3)) + (142000 * (T ^ 2)) + (3337500 * T) + 25933300) := by ring
    have scaling : ((2) * (((-9478) + ((-370) * T) + ((-232) * ((128 + (5 * T)) ^ 2)) + (8 * ((128 + (5 * T)) ^ 3)))) : ℚ) = ((25933300 + (2000 * (T ^ 3)) + (142000 * (T ^ 2)) + (3337500 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((2000 * (T ^ 3)) + (142000 * (T ^ 2)) + (3337500 * T) + 25933300) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-9478) + ((-370) * T) + ((-232) * ((128 + (5 * T)) ^ 2)) + (8 * ((128 + (5 * T)) ^ 3))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-9478) + ((-370) * T) + ((-232) * ((128 + (5 * T)) ^ 2)) + (8 * ((128 + (5 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_new_upper
    have identity : (((51734004 + (4000 * (T ^ 3)) + (283800 * (T ^ 2)) + (6664700 * T))) : ℚ) = ((4000 * (T ^ 3)) + (283800 * (T ^ 2)) + (6664700 * T) + 51734004) := by ring
    have scaling : ((2) * (((-19718) + ((-770) * T) + ((-468) * ((128 + (5 * T)) ^ 2)) + (16 * ((128 + (5 * T)) ^ 3)))) : ℚ) = ((51734004 + (4000 * (T ^ 3)) + (283800 * (T ^ 2)) + (6664700 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((4000 * (T ^ 3)) + (283800 * (T ^ 2)) + (6664700 * T) + 51734004) := by positivity
    have scale_pos : (0 : ℚ) < 2 := by positivity
    have scaled : (0 : ℚ) ≤ 2 * ((-19718) + ((-770) * T) + ((-468) * ((128 + (5 * T)) ^ 2)) + (16 * ((128 + (5 * T)) ^ 3))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-19718) + ((-770) * T) + ((-468) * ((128 + (5 * T)) ^ 2)) + (16 * ((128 + (5 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring


end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.PlusTwo
