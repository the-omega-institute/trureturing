/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakAdjacentTail/PlusThreeAtTwo
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakAdjacentTail/PlusThreeAtTwo
   mirror-E: none(waiver:adjacent-tail-physical-source)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Exact polynomial inequalities for adjacent-tail mask selection. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.Algebra
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.PlusThree
open private A B L K SU SV SW E F Common Residual StocksAndResidual HighResidual Windows ceilDiv residueRepresentative chooseM3 chooseV2 chooseM2
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.Algebra

private theorem small_a2_cmod0 (T : ℚ)
    (hT : 0 ≤ T) :
    Residual (4) ((16 + (5 * T))) (8) (0) ((20 + (8 * T))) := by
  try dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- m_lower
    have identity : (((20 + (8 * T))) : ℚ) = ((8 * T) + 20) := by ring
    have scaling : ((1) * ((20 + (8 * T))) : ℚ) = ((20 + (8 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((8 * T) + 20) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (20 + (8 * T)) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (20 + (8 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_stock
    have identity : (((43 + (12 * T))) : ℚ) = ((12 * T) + 43) := by ring
    have scaling : ((1) * ((43 + (12 * T))) : ℚ) = ((43 + (12 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((12 * T) + 43) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (43 + (12 * T)) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (43 + (12 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_lower
    have identity : (((372 + (40 * (T ^ 2)) + (246 * T))) : ℚ) = ((40 * (T ^ 2)) + (246 * T) + 372) := by ring
    have scaling : ((1) * ((32 + ((-16) * ((16 + (5 * T)) ^ 3)) + (10 * T) + (56 * ((16 + (5 * T)) ^ 2)) + ((20 + (8 * T)) * (17 + (5 * T) + (10 * ((16 + (5 * T)) ^ 2)))))) : ℚ) = ((372 + (40 * (T ^ 2)) + (246 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((40 * (T ^ 2)) + (246 * T) + 372) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (32 + ((-16) * ((16 + (5 * T)) ^ 3)) + (10 * T) + (56 * ((16 + (5 * T)) ^ 2)) + ((20 + (8 * T)) * (17 + (5 * T) + (10 * ((16 + (5 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (32 + ((-16) * ((16 + (5 * T)) ^ 3)) + (10 * T) + (56 * ((16 + (5 * T)) ^ 2)) + ((20 + (8 * T)) * (17 + (5 * T) + (10 * ((16 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_upper
    have identity : (((2204 + (210 * (T ^ 2)) + (1359 * T))) : ℚ) = ((210 * (T ^ 2)) + (1359 * T) + 2204) := by ring
    have scaling : ((1) * (((-16) + ((-46) * ((16 + (5 * T)) ^ 2)) + ((-5) * T) + (16 * ((16 + (5 * T)) ^ 3)) + ((-1) * (20 + (8 * T)) * (17 + (5 * T) + (10 * ((16 + (5 * T)) ^ 2)))))) : ℚ) = ((2204 + (210 * (T ^ 2)) + (1359 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((210 * (T ^ 2)) + (1359 * T) + 2204) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-16) + ((-46) * ((16 + (5 * T)) ^ 2)) + ((-5) * T) + (16 * ((16 + (5 * T)) ^ 3)) + ((-1) * (20 + (8 * T)) * (17 + (5 * T) + (10 * ((16 + (5 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-16) + ((-46) * ((16 + (5 * T)) ^ 2)) + ((-5) * T) + (16 * ((16 + (5 * T)) ^ 3)) + ((-1) * (20 + (8 * T)) * (17 + (5 * T) + (10 * ((16 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_old_upper
    have identity : (((7964 + (720 * (T ^ 2)) + (4788 * T))) : ℚ) = ((720 * (T ^ 2)) + (4788 * T) + 7964) := by ring
    have scaling : ((1) * ((452 + ((-80) * ((16 + (5 * T)) ^ 2)) + (32 * ((16 + (5 * T)) ^ 3)) + (140 * T) + ((-2) * (20 + (8 * T)) * (17 + (5 * T) + (10 * ((16 + (5 * T)) ^ 2)))))) : ℚ) = ((7964 + (720 * (T ^ 2)) + (4788 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((720 * (T ^ 2)) + (4788 * T) + 7964) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (452 + ((-80) * ((16 + (5 * T)) ^ 2)) + (32 * ((16 + (5 * T)) ^ 3)) + (140 * T) + ((-2) * (20 + (8 * T)) * (17 + (5 * T) + (10 * ((16 + (5 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (452 + ((-80) * ((16 + (5 * T)) ^ 2)) + (32 * ((16 + (5 * T)) ^ 3)) + (140 * T) + ((-2) * (20 + (8 * T)) * (17 + (5 * T) + (10 * ((16 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_lower
    have identity : (((2580 + (240 * (T ^ 2)) + (1576 * T))) : ℚ) = ((240 * (T ^ 2)) + (1576 * T) + 2580) := by ring
    have scaling : ((1) * ((192 + ((-32) * ((16 + (5 * T)) ^ 3)) + (60 * T) + (120 * ((16 + (5 * T)) ^ 2)) + ((20 + (8 * T)) * (17 + (5 * T) + (20 * ((16 + (5 * T)) ^ 2)))))) : ℚ) = ((2580 + (240 * (T ^ 2)) + (1576 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((240 * (T ^ 2)) + (1576 * T) + 2580) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (192 + ((-32) * ((16 + (5 * T)) ^ 3)) + (60 * T) + (120 * ((16 + (5 * T)) ^ 2)) + ((20 + (8 * T)) * (17 + (5 * T) + (20 * ((16 + (5 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (192 + ((-32) * ((16 + (5 * T)) ^ 3)) + (60 * T) + (120 * ((16 + (5 * T)) ^ 2)) + ((20 + (8 * T)) * (17 + (5 * T) + (20 * ((16 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_upper
    have identity : (((3548 + (320 * (T ^ 2)) + (2128 * T))) : ℚ) = ((320 * (T ^ 2)) + (2128 * T) + 3548) := by ring
    have scaling : ((1) * ((132 + ((-208) * ((16 + (5 * T)) ^ 2)) + (40 * T) + (64 * ((16 + (5 * T)) ^ 3)) + ((-2) * (20 + (8 * T)) * (17 + (5 * T) + (20 * ((16 + (5 * T)) ^ 2)))))) : ℚ) = ((3548 + (320 * (T ^ 2)) + (2128 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((320 * (T ^ 2)) + (2128 * T) + 3548) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (132 + ((-208) * ((16 + (5 * T)) ^ 2)) + (40 * T) + (64 * ((16 + (5 * T)) ^ 3)) + ((-2) * (20 + (8 * T)) * (17 + (5 * T) + (20 * ((16 + (5 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (132 + ((-208) * ((16 + (5 * T)) ^ 2)) + (40 * T) + (64 * ((16 + (5 * T)) ^ 3)) + ((-2) * (20 + (8 * T)) * (17 + (5 * T) + (20 * ((16 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_old_upper
    have identity : (((39776 + (2000 * (T ^ 3)) + (16700 * (T ^ 2)) + (45390 * T))) : ℚ) = ((2000 * (T ^ 3)) + (16700 * (T ^ 2)) + (45390 * T) + 39776) := by ring
    have scaling : ((1) * (((-160) + ((-100) * ((16 + (5 * T)) ^ 2)) + ((-50) * T) + (16 * ((16 + (5 * T)) ^ 3)))) : ℚ) = ((39776 + (2000 * (T ^ 3)) + (16700 * (T ^ 2)) + (45390 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((2000 * (T ^ 3)) + (16700 * (T ^ 2)) + (45390 * T) + 39776) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-160) + ((-100) * ((16 + (5 * T)) ^ 2)) + ((-50) * T) + (16 * ((16 + (5 * T)) ^ 3))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-160) + ((-100) * ((16 + (5 * T)) ^ 2)) + ((-50) * T) + (16 * ((16 + (5 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_new_upper
    have identity : (((77344 + (4000 * (T ^ 3)) + (33200 * (T ^ 2)) + (89450 * T))) : ℚ) = ((4000 * (T ^ 3)) + (33200 * (T ^ 2)) + (89450 * T) + 77344) := by ring
    have scaling : ((1) * (((-480) + ((-208) * ((16 + (5 * T)) ^ 2)) + ((-150) * T) + (32 * ((16 + (5 * T)) ^ 3)))) : ℚ) = ((77344 + (4000 * (T ^ 3)) + (33200 * (T ^ 2)) + (89450 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((4000 * (T ^ 3)) + (33200 * (T ^ 2)) + (89450 * T) + 77344) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-480) + ((-208) * ((16 + (5 * T)) ^ 2)) + ((-150) * T) + (32 * ((16 + (5 * T)) ^ 3))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-480) + ((-208) * ((16 + (5 * T)) ^ 2)) + ((-150) * T) + (32 * ((16 + (5 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring

private theorem small_a2_cmod1 (T : ℚ)
    (hT : 0 ≤ T) :
    Residual (4) ((32 + (5 * T))) (8) (2) ((33 + (8 * T))) := by
  try dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- m_lower
    have identity : (((33 + (8 * T))) : ℚ) = ((8 * T) + 33) := by ring
    have scaling : ((1) * ((33 + (8 * T))) : ℚ) = ((33 + (8 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((8 * T) + 33) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (33 + (8 * T)) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (33 + (8 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_stock
    have identity : (((94 + (12 * T))) : ℚ) = ((12 * T) + 94) := by ring
    have scaling : ((1) * ((94 + (12 * T))) : ℚ) = ((94 + (12 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((12 * T) + 94) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (94 + (12 * T)) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (94 + (12 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_lower
    have identity : (((3843 + (90 * (T ^ 2)) + (1179 * T))) : ℚ) = ((90 * (T ^ 2)) + (1179 * T) + 3843) := by ring
    have scaling : ((1) * ((706 + ((-16) * ((32 + (5 * T)) ^ 3)) + (110 * T) + (184 * ((32 + (5 * T)) ^ 2)) + ((33 + (8 * T)) * (33 + (5 * T) + (10 * ((32 + (5 * T)) ^ 2)))))) : ℚ) = ((3843 + (90 * (T ^ 2)) + (1179 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((90 * (T ^ 2)) + (1179 * T) + 3843) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (706 + ((-16) * ((32 + (5 * T)) ^ 3)) + (110 * T) + (184 * ((32 + (5 * T)) ^ 2)) + ((33 + (8 * T)) * (33 + (5 * T) + (10 * ((32 + (5 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (706 + ((-16) * ((32 + (5 * T)) ^ 3)) + (110 * T) + (184 * ((32 + (5 * T)) ^ 2)) + ((33 + (8 * T)) * (33 + (5 * T) + (10 * ((32 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_upper
    have identity : (((6429 + (160 * (T ^ 2)) + (2026 * T))) : ℚ) = ((160 * (T ^ 2)) + (2026 * T) + 6429) := by ring
    have scaling : ((1) * (((-674) + ((-174) * ((32 + (5 * T)) ^ 2)) + ((-105) * T) + (16 * ((32 + (5 * T)) ^ 3)) + ((-1) * (33 + (8 * T)) * (33 + (5 * T) + (10 * ((32 + (5 * T)) ^ 2)))))) : ℚ) = ((6429 + (160 * (T ^ 2)) + (2026 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((160 * (T ^ 2)) + (2026 * T) + 6429) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-674) + ((-174) * ((32 + (5 * T)) ^ 2)) + ((-105) * T) + (16 * ((32 + (5 * T)) ^ 3)) + ((-1) * (33 + (8 * T)) * (33 + (5 * T) + (10 * ((32 + (5 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-674) + ((-174) * ((32 + (5 * T)) ^ 2)) + ((-105) * T) + (16 * ((32 + (5 * T)) ^ 3)) + ((-1) * (33 + (8 * T)) * (33 + (5 * T) + (10 * ((32 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_old_upper
    have identity : (((26110 + (620 * (T ^ 2)) + (8042 * T))) : ℚ) = ((620 * (T ^ 2)) + (8042 * T) + 26110) := by ring
    have scaling : ((1) * (((-384) + ((-336) * ((32 + (5 * T)) ^ 2)) + ((-60) * T) + (32 * ((32 + (5 * T)) ^ 3)) + ((-2) * (33 + (8 * T)) * (33 + (5 * T) + (10 * ((32 + (5 * T)) ^ 2)))))) : ℚ) = ((26110 + (620 * (T ^ 2)) + (8042 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((620 * (T ^ 2)) + (8042 * T) + 26110) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-384) + ((-336) * ((32 + (5 * T)) ^ 2)) + ((-60) * T) + (32 * ((32 + (5 * T)) ^ 3)) + ((-2) * (33 + (8 * T)) * (33 + (5 * T) + (10 * ((32 + (5 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-384) + ((-336) * ((32 + (5 * T)) ^ 2)) + ((-60) * T) + (32 * ((32 + (5 * T)) ^ 3)) + ((-2) * (33 + (8 * T)) * (33 + (5 * T) + (10 * ((32 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_lower
    have identity : (((15043 + (340 * (T ^ 2)) + (4529 * T))) : ℚ) = ((340 * (T ^ 2)) + (4529 * T) + 15043) := by ring
    have scaling : ((1) * ((1666 + ((-32) * ((32 + (5 * T)) ^ 3)) + (260 * T) + (376 * ((32 + (5 * T)) ^ 2)) + ((33 + (8 * T)) * (33 + (5 * T) + (20 * ((32 + (5 * T)) ^ 2)))))) : ℚ) = ((15043 + (340 * (T ^ 2)) + (4529 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((340 * (T ^ 2)) + (4529 * T) + 15043) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (1666 + ((-32) * ((32 + (5 * T)) ^ 3)) + (260 * T) + (376 * ((32 + (5 * T)) ^ 2)) + ((33 + (8 * T)) * (33 + (5 * T) + (20 * ((32 + (5 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (1666 + ((-32) * ((32 + (5 * T)) ^ 3)) + (260 * T) + (376 * ((32 + (5 * T)) ^ 2)) + ((33 + (8 * T)) * (33 + (5 * T) + (20 * ((32 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_upper
    have identity : (((3710 + (120 * (T ^ 2)) + (1342 * T))) : ℚ) = ((120 * (T ^ 2)) + (1342 * T) + 3710) := by ring
    have scaling : ((1) * (((-2304) + ((-720) * ((32 + (5 * T)) ^ 2)) + ((-360) * T) + (64 * ((32 + (5 * T)) ^ 3)) + ((-2) * (33 + (8 * T)) * (33 + (5 * T) + (20 * ((32 + (5 * T)) ^ 2)))))) : ℚ) = ((3710 + (120 * (T ^ 2)) + (1342 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((120 * (T ^ 2)) + (1342 * T) + 3710) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-2304) + ((-720) * ((32 + (5 * T)) ^ 2)) + ((-360) * T) + (64 * ((32 + (5 * T)) ^ 3)) + ((-2) * (33 + (8 * T)) * (33 + (5 * T) + (20 * ((32 + (5 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-2304) + ((-720) * ((32 + (5 * T)) ^ 2)) + ((-360) * T) + (64 * ((32 + (5 * T)) ^ 3)) + ((-2) * (33 + (8 * T)) * (33 + (5 * T) + (20 * ((32 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_old_upper
    have identity : (((158140 + (2000 * (T ^ 3)) + (29500 * (T ^ 2)) + (131590 * T))) : ℚ) = ((2000 * (T ^ 3)) + (29500 * (T ^ 2)) + (131590 * T) + 158140) := by ring
    have scaling : ((1) * (((-1604) + ((-356) * ((32 + (5 * T)) ^ 2)) + ((-250) * T) + (16 * ((32 + (5 * T)) ^ 3)))) : ℚ) = ((158140 + (2000 * (T ^ 3)) + (29500 * (T ^ 2)) + (131590 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((2000 * (T ^ 3)) + (29500 * (T ^ 2)) + (131590 * T) + 158140) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-1604) + ((-356) * ((32 + (5 * T)) ^ 2)) + ((-250) * T) + (16 * ((32 + (5 * T)) ^ 3))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-1604) + ((-356) * ((32 + (5 * T)) ^ 2)) + ((-250) * T) + (16 * ((32 + (5 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_new_upper
    have identity : (((307772 + (4000 * (T ^ 3)) + (58800 * (T ^ 2)) + (260570 * T))) : ℚ) = ((4000 * (T ^ 3)) + (58800 * (T ^ 2)) + (260570 * T) + 307772) := by ring
    have scaling : ((1) * (((-3524) + ((-720) * ((32 + (5 * T)) ^ 2)) + ((-550) * T) + (32 * ((32 + (5 * T)) ^ 3)))) : ℚ) = ((307772 + (4000 * (T ^ 3)) + (58800 * (T ^ 2)) + (260570 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((4000 * (T ^ 3)) + (58800 * (T ^ 2)) + (260570 * T) + 307772) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-3524) + ((-720) * ((32 + (5 * T)) ^ 2)) + ((-550) * T) + (32 * ((32 + (5 * T)) ^ 3))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-3524) + ((-720) * ((32 + (5 * T)) ^ 2)) + ((-550) * T) + (32 * ((32 + (5 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring

private theorem small_a2_cmod2 (T : ℚ)
    (hT : 0 ≤ T) :
    Residual (4) ((64 + (5 * T))) (8) (0) ((97 + (8 * T))) := by
  try dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- m_lower
    have identity : (((97 + (8 * T))) : ℚ) = ((8 * T) + 97) := by ring
    have scaling : ((1) * ((97 + (8 * T))) : ℚ) = ((97 + (8 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((8 * T) + 97) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (97 + (8 * T)) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (97 + (8 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_stock
    have identity : (((158 + (12 * T))) : ℚ) = ((12 * T) + 158) := by ring
    have scaling : ((1) * ((158 + (12 * T))) : ℚ) = ((158 + (12 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((12 * T) + 158) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (158 + (12 * T)) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (158 + (12 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_lower
    have identity : (((14625 + (90 * (T ^ 2)) + (2295 * T))) : ℚ) = ((90 * (T ^ 2)) + (2295 * T) + 14625) := by ring
    have scaling : ((1) * ((128 + ((-16) * ((64 + (5 * T)) ^ 3)) + (10 * T) + (56 * ((64 + (5 * T)) ^ 2)) + ((97 + (8 * T)) * (65 + (5 * T) + (10 * ((64 + (5 * T)) ^ 2)))))) : ℚ) = ((14625 + (90 * (T ^ 2)) + (2295 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((90 * (T ^ 2)) + (2295 * T) + 14625) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (128 + ((-16) * ((64 + (5 * T)) ^ 3)) + (10 * T) + (56 * ((64 + (5 * T)) ^ 2)) + ((97 + (8 * T)) * (65 + (5 * T) + (10 * ((64 + (5 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (128 + ((-16) * ((64 + (5 * T)) ^ 3)) + (10 * T) + (56 * ((64 + (5 * T)) ^ 2)) + ((97 + (8 * T)) * (65 + (5 * T) + (10 * ((64 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_upper
    have identity : (((26399 + (160 * (T ^ 2)) + (4110 * T))) : ℚ) = ((160 * (T ^ 2)) + (4110 * T) + 26399) := by ring
    have scaling : ((1) * (((-64) + ((-46) * ((64 + (5 * T)) ^ 2)) + ((-5) * T) + (16 * ((64 + (5 * T)) ^ 3)) + ((-1) * (97 + (8 * T)) * (65 + (5 * T) + (10 * ((64 + (5 * T)) ^ 2)))))) : ℚ) = ((26399 + (160 * (T ^ 2)) + (4110 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((160 * (T ^ 2)) + (4110 * T) + 26399) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-64) + ((-46) * ((64 + (5 * T)) ^ 2)) + ((-5) * T) + (16 * ((64 + (5 * T)) ^ 3)) + ((-1) * (97 + (8 * T)) * (65 + (5 * T) + (10 * ((64 + (5 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-64) + ((-46) * ((64 + (5 * T)) ^ 2)) + ((-5) * T) + (16 * ((64 + (5 * T)) ^ 3)) + ((-1) * (97 + (8 * T)) * (65 + (5 * T) + (10 * ((64 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_old_upper
    have identity : (((103874 + (620 * (T ^ 2)) + (16050 * T))) : ℚ) = ((620 * (T ^ 2)) + (16050 * T) + 103874) := by ring
    have scaling : ((1) * ((1796 + ((-80) * ((64 + (5 * T)) ^ 2)) + (32 * ((64 + (5 * T)) ^ 3)) + (140 * T) + ((-2) * (97 + (8 * T)) * (65 + (5 * T) + (10 * ((64 + (5 * T)) ^ 2)))))) : ℚ) = ((103874 + (620 * (T ^ 2)) + (16050 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((620 * (T ^ 2)) + (16050 * T) + 103874) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (1796 + ((-80) * ((64 + (5 * T)) ^ 2)) + (32 * ((64 + (5 * T)) ^ 3)) + (140 * T) + ((-2) * (97 + (8 * T)) * (65 + (5 * T) + (10 * ((64 + (5 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (1796 + ((-80) * ((64 + (5 * T)) ^ 2)) + (32 * ((64 + (5 * T)) ^ 3)) + (140 * T) + ((-2) * (97 + (8 * T)) * (65 + (5 * T) + (10 * ((64 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_lower
    have identity : (((56225 + (340 * (T ^ 2)) + (8745 * T))) : ℚ) = ((340 * (T ^ 2)) + (8745 * T) + 56225) := by ring
    have scaling : ((1) * ((768 + ((-32) * ((64 + (5 * T)) ^ 3)) + (60 * T) + (120 * ((64 + (5 * T)) ^ 2)) + ((97 + (8 * T)) * (65 + (5 * T) + (20 * ((64 + (5 * T)) ^ 2)))))) : ℚ) = ((56225 + (340 * (T ^ 2)) + (8745 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((340 * (T ^ 2)) + (8745 * T) + 56225) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (768 + ((-32) * ((64 + (5 * T)) ^ 3)) + (60 * T) + (120 * ((64 + (5 * T)) ^ 2)) + ((97 + (8 * T)) * (65 + (5 * T) + (20 * ((64 + (5 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (768 + ((-32) * ((64 + (5 * T)) ^ 3)) + (60 * T) + (120 * ((64 + (5 * T)) ^ 2)) + ((97 + (8 * T)) * (65 + (5 * T) + (20 * ((64 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_upper
    have identity : (((20674 + (120 * (T ^ 2)) + (3150 * T))) : ℚ) = ((120 * (T ^ 2)) + (3150 * T) + 20674) := by ring
    have scaling : ((1) * ((516 + ((-208) * ((64 + (5 * T)) ^ 2)) + (40 * T) + (64 * ((64 + (5 * T)) ^ 3)) + ((-2) * (97 + (8 * T)) * (65 + (5 * T) + (20 * ((64 + (5 * T)) ^ 2)))))) : ℚ) = ((20674 + (120 * (T ^ 2)) + (3150 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((120 * (T ^ 2)) + (3150 * T) + 20674) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (516 + ((-208) * ((64 + (5 * T)) ^ 2)) + (40 * T) + (64 * ((64 + (5 * T)) ^ 3)) + ((-2) * (97 + (8 * T)) * (65 + (5 * T) + (20 * ((64 + (5 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (516 + ((-208) * ((64 + (5 * T)) ^ 2)) + (40 * T) + (64 * ((64 + (5 * T)) ^ 3)) + ((-2) * (97 + (8 * T)) * (65 + (5 * T) + (20 * ((64 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_old_upper
    have identity : (((3784064 + (2000 * (T ^ 3)) + (74300 * (T ^ 2)) + (918990 * T))) : ℚ) = ((2000 * (T ^ 3)) + (74300 * (T ^ 2)) + (918990 * T) + 3784064) := by ring
    have scaling : ((1) * (((-640) + ((-100) * ((64 + (5 * T)) ^ 2)) + ((-50) * T) + (16 * ((64 + (5 * T)) ^ 3)))) : ℚ) = ((3784064 + (2000 * (T ^ 3)) + (74300 * (T ^ 2)) + (918990 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((2000 * (T ^ 3)) + (74300 * (T ^ 2)) + (918990 * T) + 3784064) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-640) + ((-100) * ((64 + (5 * T)) ^ 2)) + ((-50) * T) + (16 * ((64 + (5 * T)) ^ 3))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-640) + ((-100) * ((64 + (5 * T)) ^ 2)) + ((-50) * T) + (16 * ((64 + (5 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_new_upper
    have identity : (((7534720 + (4000 * (T ^ 3)) + (148400 * (T ^ 2)) + (1832810 * T))) : ℚ) = ((4000 * (T ^ 3)) + (148400 * (T ^ 2)) + (1832810 * T) + 7534720) := by ring
    have scaling : ((1) * (((-1920) + ((-208) * ((64 + (5 * T)) ^ 2)) + ((-150) * T) + (32 * ((64 + (5 * T)) ^ 3)))) : ℚ) = ((7534720 + (4000 * (T ^ 3)) + (148400 * (T ^ 2)) + (1832810 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((4000 * (T ^ 3)) + (148400 * (T ^ 2)) + (1832810 * T) + 7534720) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-1920) + ((-208) * ((64 + (5 * T)) ^ 2)) + ((-150) * T) + (32 * ((64 + (5 * T)) ^ 3))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-1920) + ((-208) * ((64 + (5 * T)) ^ 2)) + ((-150) * T) + (32 * ((64 + (5 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring

private theorem small_a2_cmod3 (T : ℚ)
    (hT : 0 ≤ T) :
    Residual (4) ((128 + (5 * T))) (8) (1) ((193 + (8 * T))) := by
  try dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- m_lower
    have identity : (((193 + (8 * T))) : ℚ) = ((8 * T) + 193) := by ring
    have scaling : ((1) * ((193 + (8 * T))) : ℚ) = ((193 + (8 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((8 * T) + 193) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (193 + (8 * T)) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (193 + (8 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_stock
    have identity : (((318 + (12 * T))) : ℚ) = ((12 * T) + 318) := by ring
    have scaling : ((1) * ((318 + (12 * T))) : ℚ) = ((318 + (12 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((12 * T) + 318) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (318 + (12 * T)) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (318 + (12 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_lower
    have identity : (((59202 + (90 * (T ^ 2)) + (4617 * T))) : ℚ) = ((90 * (T ^ 2)) + (4617 * T) + 59202) := by ring
    have scaling : ((1) * ((1537 + ((-16) * ((128 + (5 * T)) ^ 3)) + (60 * T) + (120 * ((128 + (5 * T)) ^ 2)) + ((193 + (8 * T)) * (129 + (5 * T) + (10 * ((128 + (5 * T)) ^ 2)))))) : ℚ) = ((59202 + (90 * (T ^ 2)) + (4617 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((90 * (T ^ 2)) + (4617 * T) + 59202) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (1537 + ((-16) * ((128 + (5 * T)) ^ 3)) + (60 * T) + (120 * ((128 + (5 * T)) ^ 2)) + ((193 + (8 * T)) * (129 + (5 * T) + (10 * ((128 + (5 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (1537 + ((-16) * ((128 + (5 * T)) ^ 3)) + (60 * T) + (120 * ((128 + (5 * T)) ^ 2)) + ((193 + (8 * T)) * (129 + (5 * T) + (10 * ((128 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_upper
    have identity : (((104766 + (160 * (T ^ 2)) + (8188 * T))) : ℚ) = ((160 * (T ^ 2)) + (8188 * T) + 104766) := by ring
    have scaling : ((1) * (((-1409) + ((-110) * ((128 + (5 * T)) ^ 2)) + ((-55) * T) + (16 * ((128 + (5 * T)) ^ 3)) + ((-1) * (193 + (8 * T)) * (129 + (5 * T) + (10 * ((128 + (5 * T)) ^ 2)))))) : ℚ) = ((104766 + (160 * (T ^ 2)) + (8188 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((160 * (T ^ 2)) + (8188 * T) + 104766) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-1409) + ((-110) * ((128 + (5 * T)) ^ 2)) + ((-55) * T) + (16 * ((128 + (5 * T)) ^ 3)) + ((-1) * (193 + (8 * T)) * (129 + (5 * T) + (10 * ((128 + (5 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-1409) + ((-110) * ((128 + (5 * T)) ^ 2)) + ((-55) * T) + (16 * ((128 + (5 * T)) ^ 3)) + ((-1) * (193 + (8 * T)) * (129 + (5 * T) + (10 * ((128 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_old_upper
    have identity : (((409984 + (620 * (T ^ 2)) + (31886 * T))) : ℚ) = ((620 * (T ^ 2)) + (31886 * T) + 409984) := by ring
    have scaling : ((1) * ((1026 + ((-208) * ((128 + (5 * T)) ^ 2)) + (32 * ((128 + (5 * T)) ^ 3)) + (40 * T) + ((-2) * (193 + (8 * T)) * (129 + (5 * T) + (10 * ((128 + (5 * T)) ^ 2)))))) : ℚ) = ((409984 + (620 * (T ^ 2)) + (31886 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((620 * (T ^ 2)) + (31886 * T) + 409984) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (1026 + ((-208) * ((128 + (5 * T)) ^ 2)) + (32 * ((128 + (5 * T)) ^ 3)) + (40 * T) + ((-2) * (193 + (8 * T)) * (129 + (5 * T) + (10 * ((128 + (5 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (1026 + ((-208) * ((128 + (5 * T)) ^ 2)) + (32 * ((128 + (5 * T)) ^ 3)) + (40 * T) + ((-2) * (193 + (8 * T)) * (129 + (5 * T) + (10 * ((128 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_lower
    have identity : (((225602 + (340 * (T ^ 2)) + (17517 * T))) : ℚ) = ((340 * (T ^ 2)) + (17517 * T) + 225602) := by ring
    have scaling : ((1) * ((4097 + ((-32) * ((128 + (5 * T)) ^ 3)) + (160 * T) + (248 * ((128 + (5 * T)) ^ 2)) + ((193 + (8 * T)) * (129 + (5 * T) + (20 * ((128 + (5 * T)) ^ 2)))))) : ℚ) = ((225602 + (340 * (T ^ 2)) + (17517 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((340 * (T ^ 2)) + (17517 * T) + 225602) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (4097 + ((-32) * ((128 + (5 * T)) ^ 3)) + (160 * T) + (248 * ((128 + (5 * T)) ^ 2)) + ((193 + (8 * T)) * (129 + (5 * T) + (20 * ((128 + (5 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ (4097 + ((-32) * ((128 + (5 * T)) ^ 3)) + (160 * T) + (248 * ((128 + (5 * T)) ^ 2)) + ((193 + (8 * T)) * (129 + (5 * T) + (20 * ((128 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_upper
    have identity : (((77184 + (120 * (T ^ 2)) + (6086 * T))) : ℚ) = ((120 * (T ^ 2)) + (6086 * T) + 77184) := by ring
    have scaling : ((1) * (((-4094) + ((-464) * ((128 + (5 * T)) ^ 2)) + ((-160) * T) + (64 * ((128 + (5 * T)) ^ 3)) + ((-2) * (193 + (8 * T)) * (129 + (5 * T) + (20 * ((128 + (5 * T)) ^ 2)))))) : ℚ) = ((77184 + (120 * (T ^ 2)) + (6086 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((120 * (T ^ 2)) + (6086 * T) + 77184) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-4094) + ((-464) * ((128 + (5 * T)) ^ 2)) + ((-160) * T) + (64 * ((128 + (5 * T)) ^ 3)) + ((-2) * (193 + (8 * T)) * (129 + (5 * T) + (20 * ((128 + (5 * T)) ^ 2))))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-4094) + ((-464) * ((128 + (5 * T)) ^ 2)) + ((-160) * T) + (64 * ((128 + (5 * T)) ^ 3)) + ((-2) * (193 + (8 * T)) * (129 + (5 * T) + (20 * ((128 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_old_upper
    have identity : (((29815038 + (2000 * (T ^ 3)) + (147900 * (T ^ 2)) + (3640170 * T))) : ℚ) = ((2000 * (T ^ 3)) + (147900 * (T ^ 2)) + (3640170 * T) + 29815038) := by ring
    have scaling : ((1) * (((-3842) + ((-228) * ((128 + (5 * T)) ^ 2)) + ((-150) * T) + (16 * ((128 + (5 * T)) ^ 3)))) : ℚ) = ((29815038 + (2000 * (T ^ 3)) + (147900 * (T ^ 2)) + (3640170 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((2000 * (T ^ 3)) + (147900 * (T ^ 2)) + (3640170 * T) + 29815038) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-3842) + ((-228) * ((128 + (5 * T)) ^ 2)) + ((-150) * T) + (16 * ((128 + (5 * T)) ^ 3))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-3842) + ((-228) * ((128 + (5 * T)) ^ 2)) + ((-150) * T) + (16 * ((128 + (5 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_new_upper
    have identity : (((59497726 + (4000 * (T ^ 3)) + (295600 * (T ^ 2)) + (7270050 * T))) : ℚ) = ((4000 * (T ^ 3)) + (295600 * (T ^ 2)) + (7270050 * T) + 59497726) := by ring
    have scaling : ((1) * (((-8962) + ((-464) * ((128 + (5 * T)) ^ 2)) + ((-350) * T) + (32 * ((128 + (5 * T)) ^ 3)))) : ℚ) = ((59497726 + (4000 * (T ^ 3)) + (295600 * (T ^ 2)) + (7270050 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((4000 * (T ^ 3)) + (295600 * (T ^ 2)) + (7270050 * T) + 59497726) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-8962) + ((-464) * ((128 + (5 * T)) ^ 2)) + ((-350) * T) + (32 * ((128 + (5 * T)) ^ 3))) := by simpa only [scaling,identity] using positive
    have side : (0 : ℚ) ≤ ((-8962) + ((-464) * ((128 + (5 * T)) ^ 2)) + ((-350) * T) + (32 * ((128 + (5 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> try dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring


end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.PlusThree
