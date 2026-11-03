import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.Algebra

/-! Exact universal polynomial certificates. Independently regenerated from the
source heads and mask formulas; no finite-grid inference. Uncompiled draft. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.HighB

theorem common (X Z Q : ℚ)
    (hX : 0 ≤ X) (hZ : 0 ≤ Z) (hQ : 0 ≤ Q) :
    Common ((4 + X)) ((8 + Z + (2 * X))) ((4 + Q)) := by
  dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- first_lower
    have identity : (((9710 + (160 * (X ^ 3)) + (160 * (Z ^ 2)) + (1880 * (X ^ 2)) + (2240 * Q) + (2500 * Z) + (7390 * X) + (40 * Q * (X ^ 3)) + (40 * Q * (Z ^ 2)) + (40 * X * (Z ^ 2)) + (160 * Z * (X ^ 2)) + (460 * Q * (X ^ 2)) + (600 * Q * Z) + (1260 * X * Z) + (1760 * Q * X) + (10 * Q * X * (Z ^ 2)) + (40 * Q * Z * (X ^ 2)) + (310 * Q * X * Z))) : ℚ) = ((40 * Q * (X ^ 3)) + (160 * (X ^ 3)) + (40 * Q * Z * (X ^ 2)) + (160 * Z * (X ^ 2)) + (460 * Q * (X ^ 2)) + (1880 * (X ^ 2)) + (10 * Q * X * (Z ^ 2)) + (40 * X * (Z ^ 2)) + (310 * Q * X * Z) + (1260 * X * Z) + (1760 * Q * X) + (7390 * X) + (40 * Q * (Z ^ 2)) + (160 * (Z ^ 2)) + (600 * Q * Z) + (2500 * Z) + (2240 * Q) + 9710) := by ring
    have scaling : ((10) * ((11 + (2 * Z) + (3 * X) + (2 * (4 + X) * (8 + Z + (2 * X))) + (((8 + Z + (2 * X)) ^ 2) * (4 + Q) * (4 + X)) + ((-1) * (4 + Q) * (4 + X) * (8 + Z + (2 * X))))) : ℚ) = ((9710 + (160 * (X ^ 3)) + (160 * (Z ^ 2)) + (1880 * (X ^ 2)) + (2240 * Q) + (2500 * Z) + (7390 * X) + (40 * Q * (X ^ 3)) + (40 * Q * (Z ^ 2)) + (40 * X * (Z ^ 2)) + (160 * Z * (X ^ 2)) + (460 * Q * (X ^ 2)) + (600 * Q * Z) + (1260 * X * Z) + (1760 * Q * X) + (10 * Q * X * (Z ^ 2)) + (40 * Q * Z * (X ^ 2)) + (310 * Q * X * Z))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((40 * Q * (X ^ 3)) + (160 * (X ^ 3)) + (40 * Q * Z * (X ^ 2)) + (160 * Z * (X ^ 2)) + (460 * Q * (X ^ 2)) + (1880 * (X ^ 2)) + (10 * Q * X * (Z ^ 2)) + (40 * X * (Z ^ 2)) + (310 * Q * X * Z) + (1260 * X * Z) + (1760 * Q * X) + (7390 * X) + (40 * Q * (Z ^ 2)) + (160 * (Z ^ 2)) + (600 * Q * Z) + (2500 * Z) + (2240 * Q) + 9710) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * (11 + (2 * Z) + (3 * X) + (2 * (4 + X) * (8 + Z + (2 * X))) + (((8 + Z + (2 * X)) ^ 2) * (4 + Q) * (4 + X)) + ((-1) * (4 + Q) * (4 + X) * (8 + Z + (2 * X)))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (11 + (2 * Z) + (3 * X) + (2 * (4 + X) * (8 + Z + (2 * X))) + (((8 + Z + (2 * X)) ^ 2) * (4 + Q) * (4 + X)) + ((-1) * (4 + Q) * (4 + X) * (8 + Z + (2 * X)))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- first_upper
    have identity : (((1840 + (120 * (X ^ 2)) + (220 * Z) + (640 * Q) + (940 * X) + (40 * Q * (X ^ 2)) + (60 * X * Z) + (80 * Q * Z) + (320 * Q * X) + (20 * Q * X * Z))) : ℚ) = ((40 * Q * (X ^ 2)) + (120 * (X ^ 2)) + (20 * Q * X * Z) + (60 * X * Z) + (320 * Q * X) + (940 * X) + (80 * Q * Z) + (220 * Z) + (640 * Q) + 1840) := by ring
    have scaling : ((10) * (((-8) + ((-2) * X) + ((-2) * Z) + ((-2) * (4 + X) * (8 + Z + (2 * X))) + (2 * (4 + Q) * (4 + X) * (8 + Z + (2 * X))))) : ℚ) = ((1840 + (120 * (X ^ 2)) + (220 * Z) + (640 * Q) + (940 * X) + (40 * Q * (X ^ 2)) + (60 * X * Z) + (80 * Q * Z) + (320 * Q * X) + (20 * Q * X * Z))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((40 * Q * (X ^ 2)) + (120 * (X ^ 2)) + (20 * Q * X * Z) + (60 * X * Z) + (320 * Q * X) + (940 * X) + (80 * Q * Z) + (220 * Z) + (640 * Q) + 1840) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * ((-8) + ((-2) * X) + ((-2) * Z) + ((-2) * (4 + X) * (8 + Z + (2 * X))) + (2 * (4 + Q) * (4 + X) * (8 + Z + (2 * X)))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-8) + ((-2) * X) + ((-2) * Z) + ((-2) * (4 + X) * (8 + Z + (2 * X))) + (2 * (4 + Q) * (4 + X) * (8 + Z + (2 * X)))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_lower
    have identity : (((14800 + (220 * (Z ^ 2)) + (240 * (X ^ 3)) + (2840 * (X ^ 2)) + (3610 * Z) + (5120 * Q) + (11220 * X) + (60 * X * (Z ^ 2)) + (80 * Q * (X ^ 3)) + (80 * Q * (Z ^ 2)) + (240 * Z * (X ^ 2)) + (960 * Q * (X ^ 2)) + (1280 * Q * Z) + (1860 * X * Z) + (3840 * Q * X) + (20 * Q * X * (Z ^ 2)) + (80 * Q * Z * (X ^ 2)) + (640 * Q * X * Z))) : ℚ) = ((80 * Q * (X ^ 3)) + (240 * (X ^ 3)) + (80 * Q * Z * (X ^ 2)) + (240 * Z * (X ^ 2)) + (960 * Q * (X ^ 2)) + (2840 * (X ^ 2)) + (20 * Q * X * (Z ^ 2)) + (60 * X * (Z ^ 2)) + (640 * Q * X * Z) + (1860 * X * Z) + (3840 * Q * X) + (11220 * X) + (80 * Q * (Z ^ 2)) + (220 * (Z ^ 2)) + (1280 * Q * Z) + (3610 * Z) + (5120 * Q) + 14800) := by ring
    have scaling : ((10) * ((8 + Z + (2 * X) + ((-2) * ((8 + Z + (2 * X)) ^ 2) * (5 + X)) + (2 * (4 + X) * (8 + Z + (2 * X))) + (2 * ((8 + Z + (2 * X)) ^ 2) * (4 + Q) * (4 + X)))) : ℚ) = ((14800 + (220 * (Z ^ 2)) + (240 * (X ^ 3)) + (2840 * (X ^ 2)) + (3610 * Z) + (5120 * Q) + (11220 * X) + (60 * X * (Z ^ 2)) + (80 * Q * (X ^ 3)) + (80 * Q * (Z ^ 2)) + (240 * Z * (X ^ 2)) + (960 * Q * (X ^ 2)) + (1280 * Q * Z) + (1860 * X * Z) + (3840 * Q * X) + (20 * Q * X * (Z ^ 2)) + (80 * Q * Z * (X ^ 2)) + (640 * Q * X * Z))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((80 * Q * (X ^ 3)) + (240 * (X ^ 3)) + (80 * Q * Z * (X ^ 2)) + (240 * Z * (X ^ 2)) + (960 * Q * (X ^ 2)) + (2840 * (X ^ 2)) + (20 * Q * X * (Z ^ 2)) + (60 * X * (Z ^ 2)) + (640 * Q * X * Z) + (1860 * X * Z) + (3840 * Q * X) + (11220 * X) + (80 * Q * (Z ^ 2)) + (220 * (Z ^ 2)) + (1280 * Q * Z) + (3610 * Z) + (5120 * Q) + 14800) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * (8 + Z + (2 * X) + ((-2) * ((8 + Z + (2 * X)) ^ 2) * (5 + X)) + (2 * (4 + X) * (8 + Z + (2 * X))) + (2 * ((8 + Z + (2 * X)) ^ 2) * (4 + Q) * (4 + X))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (8 + Z + (2 * X) + ((-2) * ((8 + Z + (2 * X)) ^ 2) * (5 + X)) + (2 * (4 + X) * (8 + Z + (2 * X))) + (2 * ((8 + Z + (2 * X)) ^ 2) * (4 + Q) * (4 + X))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_old_upper
    have identity : (((14240 + (80 * (Z ^ 3)) + (160 * (X ^ 3)) + (720 * Q) + (1520 * (Z ^ 2)) + (2160 * (X ^ 2)) + (8820 * Z) + (9640 * X) + (20 * Q * (Z ^ 3)) + (40 * Q * (X ^ 2)) + (330 * Q * (Z ^ 2)) + (340 * Q * X) + (360 * X * (Z ^ 2)) + (480 * Z * (X ^ 2)) + (1450 * Q * Z) + (4120 * X * Z) + (80 * Q * X * (Z ^ 2)) + (80 * Q * Z * (X ^ 2)) + (680 * Q * X * Z))) : ℚ) = ((160 * (X ^ 3)) + (80 * Q * Z * (X ^ 2)) + (480 * Z * (X ^ 2)) + (40 * Q * (X ^ 2)) + (2160 * (X ^ 2)) + (80 * Q * X * (Z ^ 2)) + (360 * X * (Z ^ 2)) + (680 * Q * X * Z) + (4120 * X * Z) + (340 * Q * X) + (9640 * X) + (20 * Q * (Z ^ 3)) + (80 * (Z ^ 3)) + (330 * Q * (Z ^ 2)) + (1520 * (Z ^ 2)) + (1450 * Q * Z) + (8820 * Z) + (720 * Q) + 14240) := by ring
    have scaling : ((10) * (((-16) + ((-4) * X) + ((-2) * Z) + (((8 + Z + (2 * X)) ^ 2) * (4 + Q)) + ((4 + Q) * (8 + Z + (2 * X))) + ((-4) * (4 + X) * (8 + Z + (2 * X))) + (2 * ((8 + Z + (2 * X)) ^ 3) * (4 + Q)) + (4 * ((8 + Z + (2 * X)) ^ 2) * (5 + X)) + ((-4) * ((8 + Z + (2 * X)) ^ 2) * (4 + Q) * (4 + X)))) : ℚ) = ((14240 + (80 * (Z ^ 3)) + (160 * (X ^ 3)) + (720 * Q) + (1520 * (Z ^ 2)) + (2160 * (X ^ 2)) + (8820 * Z) + (9640 * X) + (20 * Q * (Z ^ 3)) + (40 * Q * (X ^ 2)) + (330 * Q * (Z ^ 2)) + (340 * Q * X) + (360 * X * (Z ^ 2)) + (480 * Z * (X ^ 2)) + (1450 * Q * Z) + (4120 * X * Z) + (80 * Q * X * (Z ^ 2)) + (80 * Q * Z * (X ^ 2)) + (680 * Q * X * Z))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((160 * (X ^ 3)) + (80 * Q * Z * (X ^ 2)) + (480 * Z * (X ^ 2)) + (40 * Q * (X ^ 2)) + (2160 * (X ^ 2)) + (80 * Q * X * (Z ^ 2)) + (360 * X * (Z ^ 2)) + (680 * Q * X * Z) + (4120 * X * Z) + (340 * Q * X) + (9640 * X) + (20 * Q * (Z ^ 3)) + (80 * (Z ^ 3)) + (330 * Q * (Z ^ 2)) + (1520 * (Z ^ 2)) + (1450 * Q * Z) + (8820 * Z) + (720 * Q) + 14240) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * ((-16) + ((-4) * X) + ((-2) * Z) + (((8 + Z + (2 * X)) ^ 2) * (4 + Q)) + ((4 + Q) * (8 + Z + (2 * X))) + ((-4) * (4 + X) * (8 + Z + (2 * X))) + (2 * ((8 + Z + (2 * X)) ^ 3) * (4 + Q)) + (4 * ((8 + Z + (2 * X)) ^ 2) * (5 + X)) + ((-4) * ((8 + Z + (2 * X)) ^ 2) * (4 + Q) * (4 + X))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-16) + ((-4) * X) + ((-2) * Z) + (((8 + Z + (2 * X)) ^ 2) * (4 + Q)) + ((4 + Q) * (8 + Z + (2 * X))) + ((-4) * (4 + X) * (8 + Z + (2 * X))) + (2 * ((8 + Z + (2 * X)) ^ 3) * (4 + Q)) + (4 * ((8 + Z + (2 * X)) ^ 2) * (5 + X)) + ((-4) * ((8 + Z + (2 * X)) ^ 2) * (4 + Q) * (4 + X))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_new_upper
    have identity : (((25440 + (160 * (Z ^ 3)) + (320 * (X ^ 3)) + (720 * Q) + (3000 * (Z ^ 2)) + (4160 * (X ^ 2)) + (16940 * Z) + (17880 * X) + (40 * Q * (X ^ 2)) + (40 * Q * (Z ^ 3)) + (340 * Q * X) + (650 * Q * (Z ^ 2)) + (720 * X * (Z ^ 2)) + (960 * Z * (X ^ 2)) + (2730 * Q * Z) + (8080 * X * Z) + (160 * Q * X * (Z ^ 2)) + (160 * Q * Z * (X ^ 2)) + (1320 * Q * X * Z))) : ℚ) = ((320 * (X ^ 3)) + (160 * Q * Z * (X ^ 2)) + (960 * Z * (X ^ 2)) + (40 * Q * (X ^ 2)) + (4160 * (X ^ 2)) + (160 * Q * X * (Z ^ 2)) + (720 * X * (Z ^ 2)) + (1320 * Q * X * Z) + (8080 * X * Z) + (340 * Q * X) + (17880 * X) + (40 * Q * (Z ^ 3)) + (160 * (Z ^ 3)) + (650 * Q * (Z ^ 2)) + (3000 * (Z ^ 2)) + (2730 * Q * Z) + (16940 * Z) + (720 * Q) + 25440) := by ring
    have scaling : ((10) * (((-48) + ((-12) * X) + ((-6) * Z) + (((8 + Z + (2 * X)) ^ 2) * (4 + Q)) + ((4 + Q) * (8 + Z + (2 * X))) + ((-8) * (4 + X) * (8 + Z + (2 * X))) + (4 * ((8 + Z + (2 * X)) ^ 3) * (4 + Q)) + (8 * ((8 + Z + (2 * X)) ^ 2) * (5 + X)) + ((-8) * ((8 + Z + (2 * X)) ^ 2) * (4 + Q) * (4 + X)))) : ℚ) = ((25440 + (160 * (Z ^ 3)) + (320 * (X ^ 3)) + (720 * Q) + (3000 * (Z ^ 2)) + (4160 * (X ^ 2)) + (16940 * Z) + (17880 * X) + (40 * Q * (X ^ 2)) + (40 * Q * (Z ^ 3)) + (340 * Q * X) + (650 * Q * (Z ^ 2)) + (720 * X * (Z ^ 2)) + (960 * Z * (X ^ 2)) + (2730 * Q * Z) + (8080 * X * Z) + (160 * Q * X * (Z ^ 2)) + (160 * Q * Z * (X ^ 2)) + (1320 * Q * X * Z))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((320 * (X ^ 3)) + (160 * Q * Z * (X ^ 2)) + (960 * Z * (X ^ 2)) + (40 * Q * (X ^ 2)) + (4160 * (X ^ 2)) + (160 * Q * X * (Z ^ 2)) + (720 * X * (Z ^ 2)) + (1320 * Q * X * Z) + (8080 * X * Z) + (340 * Q * X) + (17880 * X) + (40 * Q * (Z ^ 3)) + (160 * (Z ^ 3)) + (650 * Q * (Z ^ 2)) + (3000 * (Z ^ 2)) + (2730 * Q * Z) + (16940 * Z) + (720 * Q) + 25440) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * ((-48) + ((-12) * X) + ((-6) * Z) + (((8 + Z + (2 * X)) ^ 2) * (4 + Q)) + ((4 + Q) * (8 + Z + (2 * X))) + ((-8) * (4 + X) * (8 + Z + (2 * X))) + (4 * ((8 + Z + (2 * X)) ^ 3) * (4 + Q)) + (8 * ((8 + Z + (2 * X)) ^ 2) * (5 + X)) + ((-8) * ((8 + Z + (2 * X)) ^ 2) * (4 + Q) * (4 + X))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-48) + ((-12) * X) + ((-6) * Z) + (((8 + Z + (2 * X)) ^ 2) * (4 + Q)) + ((4 + Q) * (8 + Z + (2 * X))) + ((-8) * (4 + X) * (8 + Z + (2 * X))) + (4 * ((8 + Z + (2 * X)) ^ 3) * (4 + Q)) + (8 * ((8 + Z + (2 * X)) ^ 2) * (5 + X)) + ((-8) * ((8 + Z + (2 * X)) ^ 2) * (4 + Q) * (4 + X))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_positive
    have identity : (((22550 + (80 * (Z ^ 3)) + (320 * (X ^ 3)) + (1640 * (Z ^ 2)) + (3960 * (X ^ 2)) + (5840 * Q) + (10820 * Z) + (16360 * X) + (20 * Q * (Z ^ 3)) + (80 * Q * (X ^ 3)) + (400 * X * (Z ^ 2)) + (410 * Q * (Z ^ 2)) + (640 * Z * (X ^ 2)) + (1000 * Q * (X ^ 2)) + (2730 * Q * Z) + (4180 * Q * X) + (5260 * X * Z) + (100 * Q * X * (Z ^ 2)) + (160 * Q * Z * (X ^ 2)) + (1320 * Q * X * Z))) : ℚ) = ((80 * Q * (X ^ 3)) + (320 * (X ^ 3)) + (160 * Q * Z * (X ^ 2)) + (640 * Z * (X ^ 2)) + (1000 * Q * (X ^ 2)) + (3960 * (X ^ 2)) + (100 * Q * X * (Z ^ 2)) + (400 * X * (Z ^ 2)) + (1320 * Q * X * Z) + (5260 * X * Z) + (4180 * Q * X) + (16360 * X) + (20 * Q * (Z ^ 3)) + (80 * (Z ^ 3)) + (410 * Q * (Z ^ 2)) + (1640 * (Z ^ 2)) + (2730 * Q * Z) + (10820 * Z) + (5840 * Q) + 22550) := by ring
    have scaling : ((10) * (((-17) + ((-4) * X) + ((-2) * Z) + (((8 + Z + (2 * X)) ^ 2) * (4 + Q)) + ((4 + Q) * (8 + Z + (2 * X))) + ((-2) * (4 + X) * (8 + Z + (2 * X))) + (2 * ((8 + Z + (2 * X)) ^ 3) * (4 + Q)) + ((-2) * ((8 + Z + (2 * X)) ^ 2) * (4 + Q) * (4 + X)))) : ℚ) = ((22550 + (80 * (Z ^ 3)) + (320 * (X ^ 3)) + (1640 * (Z ^ 2)) + (3960 * (X ^ 2)) + (5840 * Q) + (10820 * Z) + (16360 * X) + (20 * Q * (Z ^ 3)) + (80 * Q * (X ^ 3)) + (400 * X * (Z ^ 2)) + (410 * Q * (Z ^ 2)) + (640 * Z * (X ^ 2)) + (1000 * Q * (X ^ 2)) + (2730 * Q * Z) + (4180 * Q * X) + (5260 * X * Z) + (100 * Q * X * (Z ^ 2)) + (160 * Q * Z * (X ^ 2)) + (1320 * Q * X * Z))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((80 * Q * (X ^ 3)) + (320 * (X ^ 3)) + (160 * Q * Z * (X ^ 2)) + (640 * Z * (X ^ 2)) + (1000 * Q * (X ^ 2)) + (3960 * (X ^ 2)) + (100 * Q * X * (Z ^ 2)) + (400 * X * (Z ^ 2)) + (1320 * Q * X * Z) + (5260 * X * Z) + (4180 * Q * X) + (16360 * X) + (20 * Q * (Z ^ 3)) + (80 * (Z ^ 3)) + (410 * Q * (Z ^ 2)) + (1640 * (Z ^ 2)) + (2730 * Q * Z) + (10820 * Z) + (5840 * Q) + 22550) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * ((-17) + ((-4) * X) + ((-2) * Z) + (((8 + Z + (2 * X)) ^ 2) * (4 + Q)) + ((4 + Q) * (8 + Z + (2 * X))) + ((-2) * (4 + X) * (8 + Z + (2 * X))) + (2 * ((8 + Z + (2 * X)) ^ 3) * (4 + Q)) + ((-2) * ((8 + Z + (2 * X)) ^ 2) * (4 + Q) * (4 + X))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-17) + ((-4) * X) + ((-2) * Z) + (((8 + Z + (2 * X)) ^ 2) * (4 + Q)) + ((4 + Q) * (8 + Z + (2 * X))) + ((-2) * (4 + X) * (8 + Z + (2 * X))) + (2 * ((8 + Z + (2 * X)) ^ 3) * (4 + Q)) + ((-2) * ((8 + Z + (2 * X)) ^ 2) * (4 + Q) * (4 + X))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_stock
    have identity : (((74790 + (120 * (Z ^ 3)) + (320 * (X ^ 4)) + (3080 * (Z ^ 2)) + (5040 * (X ^ 3)) + (20120 * Q) + (26310 * Z) + (29640 * (X ^ 2)) + (77100 * X) + (30 * Q * (Z ^ 3)) + (40 * X * (Z ^ 3)) + (80 * Q * (X ^ 4)) + (240 * (X ^ 2) * (Z ^ 2)) + (480 * Z * (X ^ 3)) + (795 * Q * (Z ^ 2)) + (1280 * Q * (X ^ 3)) + (1740 * X * (Z ^ 2)) + (5520 * Z * (X ^ 2)) + (6955 * Q * Z) + (7660 * Q * (X ^ 2)) + (20310 * Q * X) + (20980 * X * Z) + (10 * Q * X * (Z ^ 3)) + (60 * Q * (X ^ 2) * (Z ^ 2)) + (120 * Q * Z * (X ^ 3)) + (440 * Q * X * (Z ^ 2)) + (1400 * Q * Z * (X ^ 2)) + (5420 * Q * X * Z))) : ℚ) = ((80 * Q * (X ^ 4)) + (320 * (X ^ 4)) + (120 * Q * Z * (X ^ 3)) + (480 * Z * (X ^ 3)) + (1280 * Q * (X ^ 3)) + (5040 * (X ^ 3)) + (60 * Q * (X ^ 2) * (Z ^ 2)) + (240 * (X ^ 2) * (Z ^ 2)) + (1400 * Q * Z * (X ^ 2)) + (5520 * Z * (X ^ 2)) + (7660 * Q * (X ^ 2)) + (29640 * (X ^ 2)) + (10 * Q * X * (Z ^ 3)) + (40 * X * (Z ^ 3)) + (440 * Q * X * (Z ^ 2)) + (1740 * X * (Z ^ 2)) + (5420 * Q * X * Z) + (20980 * X * Z) + (20310 * Q * X) + (77100 * X) + (30 * Q * (Z ^ 3)) + (120 * (Z ^ 3)) + (795 * Q * (Z ^ 2)) + (3080 * (Z ^ 2)) + (6955 * Q * Z) + (26310 * Z) + (20120 * Q) + 74790) := by ring
    have scaling : ((10) * ((16 + (2 * Z) + (4 * X) + (((-1) + ((1 / 2) * (4 + Q) * (8 + Z + (2 * X)))) * (9 + Z + (2 * X) + (2 * ((8 + Z + (2 * X)) ^ 2) * (5 + X)))) + ((-1) * ((8 + Z + (2 * X)) ^ 2) * (4 + Q)) + ((-1) * (4 + Q) * (8 + Z + (2 * X))) + ((-2) * ((8 + Z + (2 * X)) ^ 3) * (4 + Q)) + (2 * (4 + X) * (8 + Z + (2 * X))) + (2 * ((8 + Z + (2 * X)) ^ 2) * (4 + Q) * (4 + X)))) : ℚ) = ((74790 + (120 * (Z ^ 3)) + (320 * (X ^ 4)) + (3080 * (Z ^ 2)) + (5040 * (X ^ 3)) + (20120 * Q) + (26310 * Z) + (29640 * (X ^ 2)) + (77100 * X) + (30 * Q * (Z ^ 3)) + (40 * X * (Z ^ 3)) + (80 * Q * (X ^ 4)) + (240 * (X ^ 2) * (Z ^ 2)) + (480 * Z * (X ^ 3)) + (795 * Q * (Z ^ 2)) + (1280 * Q * (X ^ 3)) + (1740 * X * (Z ^ 2)) + (5520 * Z * (X ^ 2)) + (6955 * Q * Z) + (7660 * Q * (X ^ 2)) + (20310 * Q * X) + (20980 * X * Z) + (10 * Q * X * (Z ^ 3)) + (60 * Q * (X ^ 2) * (Z ^ 2)) + (120 * Q * Z * (X ^ 3)) + (440 * Q * X * (Z ^ 2)) + (1400 * Q * Z * (X ^ 2)) + (5420 * Q * X * Z))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((80 * Q * (X ^ 4)) + (320 * (X ^ 4)) + (120 * Q * Z * (X ^ 3)) + (480 * Z * (X ^ 3)) + (1280 * Q * (X ^ 3)) + (5040 * (X ^ 3)) + (60 * Q * (X ^ 2) * (Z ^ 2)) + (240 * (X ^ 2) * (Z ^ 2)) + (1400 * Q * Z * (X ^ 2)) + (5520 * Z * (X ^ 2)) + (7660 * Q * (X ^ 2)) + (29640 * (X ^ 2)) + (10 * Q * X * (Z ^ 3)) + (40 * X * (Z ^ 3)) + (440 * Q * X * (Z ^ 2)) + (1740 * X * (Z ^ 2)) + (5420 * Q * X * Z) + (20980 * X * Z) + (20310 * Q * X) + (77100 * X) + (30 * Q * (Z ^ 3)) + (120 * (Z ^ 3)) + (795 * Q * (Z ^ 2)) + (3080 * (Z ^ 2)) + (6955 * Q * Z) + (26310 * Z) + (20120 * Q) + 74790) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * (16 + (2 * Z) + (4 * X) + (((-1) + ((1 / 2) * (4 + Q) * (8 + Z + (2 * X)))) * (9 + Z + (2 * X) + (2 * ((8 + Z + (2 * X)) ^ 2) * (5 + X)))) + ((-1) * ((8 + Z + (2 * X)) ^ 2) * (4 + Q)) + ((-1) * (4 + Q) * (8 + Z + (2 * X))) + ((-2) * ((8 + Z + (2 * X)) ^ 3) * (4 + Q)) + (2 * (4 + X) * (8 + Z + (2 * X))) + (2 * ((8 + Z + (2 * X)) ^ 2) * (4 + Q) * (4 + X))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (16 + (2 * Z) + (4 * X) + (((-1) + ((1 / 2) * (4 + Q) * (8 + Z + (2 * X)))) * (9 + Z + (2 * X) + (2 * ((8 + Z + (2 * X)) ^ 2) * (5 + X)))) + ((-1) * ((8 + Z + (2 * X)) ^ 2) * (4 + Q)) + ((-1) * (4 + Q) * (8 + Z + (2 * X))) + ((-2) * ((8 + Z + (2 * X)) ^ 3) * (4 + Q)) + (2 * (4 + X) * (8 + Z + (2 * X))) + (2 * ((8 + Z + (2 * X)) ^ 2) * (4 + Q) * (4 + X))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring

theorem large_b (X Z Q : ℚ)
    (hX : 0 ≤ X) (hZ : 0 ≤ Z) (hQ : 0 ≤ Q) :
    0 ≤ ((-32) + ((-7) * X) + ((-4) * Z) + ((-8) * ((8 + Z + (2 * X)) ^ 2) * (5 + X)) + (((8 + Z + (2 * X)) ^ 2) * (4 + X) * (32 + Q)) + ((4 + X) * (32 + Q) * (8 + Z + (2 * X))) + ((-2) * (32 + Q) * (8 + Z + (2 * X)) * (9 + Z + (2 * X)))) := by
  dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  -- second_both_upper
  have identity : (((20160 + (240 * (Z ^ 2)) + (960 * (X ^ 3)) + (1440 * Q) + (4440 * Z) + (9280 * (X ^ 2)) + (26810 * X) + (20 * Q * (Z ^ 2)) + (40 * Q * (X ^ 3)) + (240 * X * (Z ^ 2)) + (340 * Q * Z) + (420 * Q * (X ^ 2)) + (960 * Z * (X ^ 2)) + (1400 * Q * X) + (5120 * X * Z) + (10 * Q * X * (Z ^ 2)) + (40 * Q * Z * (X ^ 2)) + (250 * Q * X * Z))) : ℚ) = ((40 * Q * (X ^ 3)) + (960 * (X ^ 3)) + (40 * Q * Z * (X ^ 2)) + (960 * Z * (X ^ 2)) + (420 * Q * (X ^ 2)) + (9280 * (X ^ 2)) + (10 * Q * X * (Z ^ 2)) + (240 * X * (Z ^ 2)) + (250 * Q * X * Z) + (5120 * X * Z) + (1400 * Q * X) + (26810 * X) + (20 * Q * (Z ^ 2)) + (240 * (Z ^ 2)) + (340 * Q * Z) + (4440 * Z) + (1440 * Q) + 20160) := by ring
  have scaling : ((10) * (((-32) + ((-7) * X) + ((-4) * Z) + ((-8) * ((8 + Z + (2 * X)) ^ 2) * (5 + X)) + (((8 + Z + (2 * X)) ^ 2) * (4 + X) * (32 + Q)) + ((4 + X) * (32 + Q) * (8 + Z + (2 * X))) + ((-2) * (32 + Q) * (8 + Z + (2 * X)) * (9 + Z + (2 * X))))) : ℚ) = ((20160 + (240 * (Z ^ 2)) + (960 * (X ^ 3)) + (1440 * Q) + (4440 * Z) + (9280 * (X ^ 2)) + (26810 * X) + (20 * Q * (Z ^ 2)) + (40 * Q * (X ^ 3)) + (240 * X * (Z ^ 2)) + (340 * Q * Z) + (420 * Q * (X ^ 2)) + (960 * Z * (X ^ 2)) + (1400 * Q * X) + (5120 * X * Z) + (10 * Q * X * (Z ^ 2)) + (40 * Q * Z * (X ^ 2)) + (250 * Q * X * Z))) := by
    field_simp <;> ring
  have positive : (0 : ℚ) ≤ ((40 * Q * (X ^ 3)) + (960 * (X ^ 3)) + (40 * Q * Z * (X ^ 2)) + (960 * Z * (X ^ 2)) + (420 * Q * (X ^ 2)) + (9280 * (X ^ 2)) + (10 * Q * X * (Z ^ 2)) + (240 * X * (Z ^ 2)) + (250 * Q * X * Z) + (5120 * X * Z) + (1400 * Q * X) + (26810 * X) + (20 * Q * (Z ^ 2)) + (240 * (Z ^ 2)) + (340 * Q * Z) + (4440 * Z) + (1440 * Q) + 20160) := by positivity
  have scale_pos : (0 : ℚ) < 10 := by positivity
  have scaled : (0 : ℚ) ≤ 10 * ((-32) + ((-7) * X) + ((-4) * Z) + ((-8) * ((8 + Z + (2 * X)) ^ 2) * (5 + X)) + (((8 + Z + (2 * X)) ^ 2) * (4 + X) * (32 + Q)) + ((4 + X) * (32 + Q) * (8 + Z + (2 * X))) + ((-2) * (32 + Q) * (8 + Z + (2 * X)) * (9 + Z + (2 * X)))) := by rw [scaling,identity]; exact positive
  have side : (0 : ℚ) ≤ ((-32) + ((-7) * X) + ((-4) * Z) + ((-8) * ((8 + Z + (2 * X)) ^ 2) * (5 + X)) + (((8 + Z + (2 * X)) ^ 2) * (4 + X) * (32 + Q)) + ((4 + X) * (32 + Q) * (8 + Z + (2 * X))) + ((-2) * (32 + Q) * (8 + Z + (2 * X)) * (9 + Z + (2 * X)))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
  convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring

theorem a_at_least_three (X Z Q : ℚ)
    (hX : 0 ≤ X) (hZ : 0 ≤ Z) (hQ : 0 ≤ Q) :
    0 ≤ ((-60) + ((-7) * X) + ((-4) * Z) + ((-8) * ((16 + Z + (2 * X)) ^ 2) * (9 + X)) + (((16 + Z + (2 * X)) ^ 2) * (8 + X) * (16 + Q)) + ((8 + X) * (16 + Q) * (16 + Z + (2 * X))) + ((-2) * (16 + Q) * (16 + Z + (2 * X)) * (17 + Z + (2 * X)))) := by
  dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  -- second_both_upper
  have identity : (((76200 + (240 * (Z ^ 2)) + (320 * (X ^ 3)) + (6400 * (X ^ 2)) + (8600 * Z) + (16320 * Q) + (40250 * X) + (40 * Q * (X ^ 3)) + (60 * Q * (Z ^ 2)) + (80 * X * (Z ^ 2)) + (320 * Z * (X ^ 2)) + (900 * Q * (X ^ 2)) + (1980 * Q * Z) + (3680 * X * Z) + (6680 * Q * X) + (10 * Q * X * (Z ^ 2)) + (40 * Q * Z * (X ^ 2)) + (570 * Q * X * Z))) : ℚ) = ((40 * Q * (X ^ 3)) + (320 * (X ^ 3)) + (40 * Q * Z * (X ^ 2)) + (320 * Z * (X ^ 2)) + (900 * Q * (X ^ 2)) + (6400 * (X ^ 2)) + (10 * Q * X * (Z ^ 2)) + (80 * X * (Z ^ 2)) + (570 * Q * X * Z) + (3680 * X * Z) + (6680 * Q * X) + (40250 * X) + (60 * Q * (Z ^ 2)) + (240 * (Z ^ 2)) + (1980 * Q * Z) + (8600 * Z) + (16320 * Q) + 76200) := by ring
  have scaling : ((10) * (((-60) + ((-7) * X) + ((-4) * Z) + ((-8) * ((16 + Z + (2 * X)) ^ 2) * (9 + X)) + (((16 + Z + (2 * X)) ^ 2) * (8 + X) * (16 + Q)) + ((8 + X) * (16 + Q) * (16 + Z + (2 * X))) + ((-2) * (16 + Q) * (16 + Z + (2 * X)) * (17 + Z + (2 * X))))) : ℚ) = ((76200 + (240 * (Z ^ 2)) + (320 * (X ^ 3)) + (6400 * (X ^ 2)) + (8600 * Z) + (16320 * Q) + (40250 * X) + (40 * Q * (X ^ 3)) + (60 * Q * (Z ^ 2)) + (80 * X * (Z ^ 2)) + (320 * Z * (X ^ 2)) + (900 * Q * (X ^ 2)) + (1980 * Q * Z) + (3680 * X * Z) + (6680 * Q * X) + (10 * Q * X * (Z ^ 2)) + (40 * Q * Z * (X ^ 2)) + (570 * Q * X * Z))) := by
    field_simp <;> ring
  have positive : (0 : ℚ) ≤ ((40 * Q * (X ^ 3)) + (320 * (X ^ 3)) + (40 * Q * Z * (X ^ 2)) + (320 * Z * (X ^ 2)) + (900 * Q * (X ^ 2)) + (6400 * (X ^ 2)) + (10 * Q * X * (Z ^ 2)) + (80 * X * (Z ^ 2)) + (570 * Q * X * Z) + (3680 * X * Z) + (6680 * Q * X) + (40250 * X) + (60 * Q * (Z ^ 2)) + (240 * (Z ^ 2)) + (1980 * Q * Z) + (8600 * Z) + (16320 * Q) + 76200) := by positivity
  have scale_pos : (0 : ℚ) < 10 := by positivity
  have scaled : (0 : ℚ) ≤ 10 * ((-60) + ((-7) * X) + ((-4) * Z) + ((-8) * ((16 + Z + (2 * X)) ^ 2) * (9 + X)) + (((16 + Z + (2 * X)) ^ 2) * (8 + X) * (16 + Q)) + ((8 + X) * (16 + Q) * (16 + Z + (2 * X))) + ((-2) * (16 + Q) * (16 + Z + (2 * X)) * (17 + Z + (2 * X)))) := by rw [scaling,identity]; exact positive
  have side : (0 : ℚ) ≤ ((-60) + ((-7) * X) + ((-4) * Z) + ((-8) * ((16 + Z + (2 * X)) ^ 2) * (9 + X)) + (((16 + Z + (2 * X)) ^ 2) * (8 + X) * (16 + Q)) + ((8 + X) * (16 + Q) * (16 + Z + (2 * X))) + ((-2) * (16 + Q) * (16 + Z + (2 * X)) * (17 + Z + (2 * X)))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
  convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring

theorem a_two_b_c_plus_four_r1 (T : ℚ)
    (hT : 0 ≤ T) :
    HighResidual ((16 + (5 * T))) ((40 + (16 * T))) := by
  dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- m_lower
    have identity : (((400 + (160 * T))) : ℚ) = ((160 * T) + 400) := by ring
    have scaling : ((10) * ((40 + (16 * T))) : ℚ) = ((400 + (160 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((160 * T) + 400) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * (40 + (16 * T)) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (40 + (16 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_stock
    have identity : (((870 + (240 * T))) : ℚ) = ((240 * T) + 870) := by ring
    have scaling : ((10) * ((87 + (24 * T))) : ℚ) = ((870 + (240 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((240 * T) + 870) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * (87 + (24 * T)) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (87 + (24 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_lower
    have identity : (((5840 + (800 * (T ^ 2)) + (4420 * T))) : ℚ) = ((800 * (T ^ 2)) + (4420 * T) + 5840) := by ring
    have scaling : ((10) * (((-96) + ((-32) * ((16 + (5 * T)) ^ 3)) + ((-30) * T) + (112 * ((16 + (5 * T)) ^ 2)) + ((40 + (16 * T)) * (17 + (5 * T) + (10 * ((16 + (5 * T)) ^ 2)))))) : ℚ) = ((5840 + (800 * (T ^ 2)) + (4420 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((800 * (T ^ 2)) + (4420 * T) + 5840) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * ((-96) + ((-32) * ((16 + (5 * T)) ^ 3)) + ((-30) * T) + (112 * ((16 + (5 * T)) ^ 2)) + ((40 + (16 * T)) * (17 + (5 * T) + (10 * ((16 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-96) + ((-32) * ((16 + (5 * T)) ^ 3)) + ((-30) * T) + (112 * ((16 + (5 * T)) ^ 2)) + ((40 + (16 * T)) * (17 + (5 * T) + (10 * ((16 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_upper
    have identity : (((19920 + (1700 * (T ^ 2)) + (11630 * T))) : ℚ) = ((1700 * (T ^ 2)) + (11630 * T) + 19920) := by ring
    have scaling : ((10) * ((112 + ((-102) * ((16 + (5 * T)) ^ 2)) + (32 * ((16 + (5 * T)) ^ 3)) + (35 * T) + ((-1) * (40 + (16 * T)) * (17 + (5 * T) + (10 * ((16 + (5 * T)) ^ 2)))))) : ℚ) = ((19920 + (1700 * (T ^ 2)) + (11630 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((1700 * (T ^ 2)) + (11630 * T) + 19920) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * (112 + ((-102) * ((16 + (5 * T)) ^ 2)) + (32 * ((16 + (5 * T)) ^ 3)) + (35 * T) + ((-1) * (40 + (16 * T)) * (17 + (5 * T) + (10 * ((16 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (112 + ((-102) * ((16 + (5 * T)) ^ 2)) + (32 * ((16 + (5 * T)) ^ 3)) + (35 * T) + ((-1) * (40 + (16 * T)) * (17 + (5 * T) + (10 * ((16 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_old_upper
    have identity : (((162440 + (14400 * (T ^ 2)) + (96760 * T))) : ℚ) = ((14400 * (T ^ 2)) + (96760 * T) + 162440) := by ring
    have scaling : ((10) * ((1220 + ((-160) * ((16 + (5 * T)) ^ 2)) + (64 * ((16 + (5 * T)) ^ 3)) + (380 * T) + ((-2) * (40 + (16 * T)) * (17 + (5 * T) + (10 * ((16 + (5 * T)) ^ 2)))))) : ℚ) = ((162440 + (14400 * (T ^ 2)) + (96760 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((14400 * (T ^ 2)) + (96760 * T) + 162440) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * (1220 + ((-160) * ((16 + (5 * T)) ^ 2)) + (64 * ((16 + (5 * T)) ^ 3)) + (380 * T) + ((-2) * (40 + (16 * T)) * (17 + (5 * T) + (10 * ((16 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (1220 + ((-160) * ((16 + (5 * T)) ^ 2)) + (64 * ((16 + (5 * T)) ^ 3)) + (380 * T) + ((-2) * (40 + (16 * T)) * (17 + (5 * T) + (10 * ((16 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_lower
    have identity : (((48400 + (4800 * (T ^ 2)) + (30520 * T))) : ℚ) = ((4800 * (T ^ 2)) + (30520 * T) + 48400) := by ring
    have scaling : ((10) * ((64 + ((-64) * ((16 + (5 * T)) ^ 3)) + (20 * T) + (240 * ((16 + (5 * T)) ^ 2)) + ((40 + (16 * T)) * (17 + (5 * T) + (20 * ((16 + (5 * T)) ^ 2)))))) : ℚ) = ((48400 + (4800 * (T ^ 2)) + (30520 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((4800 * (T ^ 2)) + (30520 * T) + 48400) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * (64 + ((-64) * ((16 + (5 * T)) ^ 3)) + (20 * T) + (240 * ((16 + (5 * T)) ^ 2)) + ((40 + (16 * T)) * (17 + (5 * T) + (20 * ((16 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (64 + ((-64) * ((16 + (5 * T)) ^ 3)) + (20 * T) + (240 * ((16 + (5 * T)) ^ 2)) + ((40 + (16 * T)) * (17 + (5 * T) + (20 * ((16 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_upper
    have identity : (((77320 + (6400 * (T ^ 2)) + (44560 * T))) : ℚ) = ((6400 * (T ^ 2)) + (44560 * T) + 77320) := by ring
    have scaling : ((10) * ((900 + ((-416) * ((16 + (5 * T)) ^ 2)) + (128 * ((16 + (5 * T)) ^ 3)) + (280 * T) + ((-2) * (40 + (16 * T)) * (17 + (5 * T) + (20 * ((16 + (5 * T)) ^ 2)))))) : ℚ) = ((77320 + (6400 * (T ^ 2)) + (44560 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((6400 * (T ^ 2)) + (44560 * T) + 77320) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * (900 + ((-416) * ((16 + (5 * T)) ^ 2)) + (128 * ((16 + (5 * T)) ^ 3)) + (280 * T) + ((-2) * (40 + (16 * T)) * (17 + (5 * T) + (20 * ((16 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (900 + ((-416) * ((16 + (5 * T)) ^ 2)) + (128 * ((16 + (5 * T)) ^ 3)) + (280 * T) + ((-2) * (40 + (16 * T)) * (17 + (5 * T) + (20 * ((16 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring

theorem a_two_b_c_plus_four_r2 (T : ℚ)
    (hT : 0 ≤ T) :
    HighResidual ((32 + (5 * T))) ((91 + (16 * T))) := by
  dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- m_lower
    have identity : (((910 + (160 * T))) : ℚ) = ((160 * T) + 910) := by ring
    have scaling : ((10) * ((91 + (16 * T))) : ℚ) = ((910 + (160 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((160 * T) + 910) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * (91 + (16 * T)) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (91 + (16 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_stock
    have identity : (((1640 + (240 * T))) : ℚ) = ((240 * T) + 1640) := by ring
    have scaling : ((10) * ((164 + (24 * T))) : ℚ) = ((1640 + (240 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((240 * T) + 1640) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * (164 + (24 * T)) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (164 + (24 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_lower
    have identity : (((7630 + (300 * (T ^ 2)) + (3130 * T))) : ℚ) = ((300 * (T ^ 2)) + (3130 * T) + 7630) := by ring
    have scaling : ((10) * (((-192) + ((-32) * ((32 + (5 * T)) ^ 3)) + ((-30) * T) + (112 * ((32 + (5 * T)) ^ 2)) + ((91 + (16 * T)) * (33 + (5 * T) + (10 * ((32 + (5 * T)) ^ 2)))))) : ℚ) = ((7630 + (300 * (T ^ 2)) + (3130 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((300 * (T ^ 2)) + (3130 * T) + 7630) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * ((-192) + ((-32) * ((32 + (5 * T)) ^ 3)) + ((-30) * T) + (112 * ((32 + (5 * T)) ^ 2)) + ((91 + (16 * T)) * (33 + (5 * T) + (10 * ((32 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-192) + ((-32) * ((32 + (5 * T)) ^ 3)) + ((-30) * T) + (112 * ((32 + (5 * T)) ^ 2)) + ((91 + (16 * T)) * (33 + (5 * T) + (10 * ((32 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_upper
    have identity : (((95090 + (2200 * (T ^ 2)) + (28920 * T))) : ℚ) = ((2200 * (T ^ 2)) + (28920 * T) + 95090) := by ring
    have scaling : ((10) * ((224 + ((-102) * ((32 + (5 * T)) ^ 2)) + (32 * ((32 + (5 * T)) ^ 3)) + (35 * T) + ((-1) * (91 + (16 * T)) * (33 + (5 * T) + (10 * ((32 + (5 * T)) ^ 2)))))) : ℚ) = ((95090 + (2200 * (T ^ 2)) + (28920 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((2200 * (T ^ 2)) + (28920 * T) + 95090) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * (224 + ((-102) * ((32 + (5 * T)) ^ 2)) + (32 * ((32 + (5 * T)) ^ 3)) + (35 * T) + ((-1) * (91 + (16 * T)) * (33 + (5 * T) + (10 * ((32 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (224 + ((-102) * ((32 + (5 * T)) ^ 2)) + (32 * ((32 + (5 * T)) ^ 3)) + (35 * T) + ((-1) * (91 + (16 * T)) * (33 + (5 * T) + (10 * ((32 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_old_upper
    have identity : (((660620 + (15400 * (T ^ 2)) + (201740 * T))) : ℚ) = ((15400 * (T ^ 2)) + (201740 * T) + 660620) := by ring
    have scaling : ((10) * ((2436 + ((-160) * ((32 + (5 * T)) ^ 2)) + (64 * ((32 + (5 * T)) ^ 3)) + (380 * T) + ((-2) * (91 + (16 * T)) * (33 + (5 * T) + (10 * ((32 + (5 * T)) ^ 2)))))) : ℚ) = ((660620 + (15400 * (T ^ 2)) + (201740 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((15400 * (T ^ 2)) + (201740 * T) + 660620) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * (2436 + ((-160) * ((32 + (5 * T)) ^ 2)) + (64 * ((32 + (5 * T)) ^ 3)) + (380 * T) + ((-2) * (91 + (16 * T)) * (33 + (5 * T) + (10 * ((32 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (2436 + ((-160) * ((32 + (5 * T)) ^ 2)) + (64 * ((32 + (5 * T)) ^ 3)) + (380 * T) + ((-2) * (91 + (16 * T)) * (33 + (5 * T) + (10 * ((32 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_lower
    have identity : (((154190 + (3800 * (T ^ 2)) + (48430 * T))) : ℚ) = ((3800 * (T ^ 2)) + (48430 * T) + 154190) := by ring
    have scaling : ((10) * ((128 + ((-64) * ((32 + (5 * T)) ^ 3)) + (20 * T) + (240 * ((32 + (5 * T)) ^ 2)) + ((91 + (16 * T)) * (33 + (5 * T) + (20 * ((32 + (5 * T)) ^ 2)))))) : ℚ) = ((154190 + (3800 * (T ^ 2)) + (48430 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((3800 * (T ^ 2)) + (48430 * T) + 154190) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * (128 + ((-64) * ((32 + (5 * T)) ^ 3)) + (20 * T) + (240 * ((32 + (5 * T)) ^ 2)) + ((91 + (16 * T)) * (33 + (5 * T) + (20 * ((32 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (128 + ((-64) * ((32 + (5 * T)) ^ 3)) + (20 * T) + (240 * ((32 + (5 * T)) ^ 2)) + ((91 + (16 * T)) * (33 + (5 * T) + (20 * ((32 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_upper
    have identity : (((367500 + (8400 * (T ^ 2)) + (111140 * T))) : ℚ) = ((8400 * (T ^ 2)) + (111140 * T) + 367500) := by ring
    have scaling : ((10) * ((1796 + ((-416) * ((32 + (5 * T)) ^ 2)) + (128 * ((32 + (5 * T)) ^ 3)) + (280 * T) + ((-2) * (91 + (16 * T)) * (33 + (5 * T) + (20 * ((32 + (5 * T)) ^ 2)))))) : ℚ) = ((367500 + (8400 * (T ^ 2)) + (111140 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((8400 * (T ^ 2)) + (111140 * T) + 367500) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * (1796 + ((-416) * ((32 + (5 * T)) ^ 2)) + (128 * ((32 + (5 * T)) ^ 3)) + (280 * T) + ((-2) * (91 + (16 * T)) * (33 + (5 * T) + (20 * ((32 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (1796 + ((-416) * ((32 + (5 * T)) ^ 2)) + (128 * ((32 + (5 * T)) ^ 3)) + (280 * T) + ((-2) * (91 + (16 * T)) * (33 + (5 * T) + (20 * ((32 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring

theorem a_two_b_c_plus_four_r3 (T : ℚ)
    (hT : 0 ≤ T) :
    HighResidual ((8 + (5 * T))) ((15 + (16 * T))) := by
  dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- m_lower
    have identity : (((150 + (160 * T))) : ℚ) = ((160 * T) + 150) := by ring
    have scaling : ((10) * ((15 + (16 * T))) : ℚ) = ((150 + (160 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((160 * T) + 150) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * (15 + (16 * T)) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (15 + (16 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_stock
    have identity : (((480 + (240 * T))) : ℚ) = ((240 * T) + 480) := by ring
    have scaling : ((10) * ((48 + (24 * T))) : ℚ) = ((480 + (240 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((240 * T) + 480) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * (48 + (24 * T)) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (48 + (24 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_lower
    have identity : (((4710 + (2300 * (T ^ 2)) + (6690 * T))) : ℚ) = ((2300 * (T ^ 2)) + (6690 * T) + 4710) := by ring
    have scaling : ((10) * (((-48) + ((-32) * ((8 + (5 * T)) ^ 3)) + ((-30) * T) + (112 * ((8 + (5 * T)) ^ 2)) + ((15 + (16 * T)) * (9 + (5 * T) + (10 * ((8 + (5 * T)) ^ 2)))))) : ℚ) = ((4710 + (2300 * (T ^ 2)) + (6690 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((2300 * (T ^ 2)) + (6690 * T) + 4710) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * ((-48) + ((-32) * ((8 + (5 * T)) ^ 3)) + ((-30) * T) + (112 * ((8 + (5 * T)) ^ 2)) + ((15 + (16 * T)) * (9 + (5 * T) + (10 * ((8 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-48) + ((-32) * ((8 + (5 * T)) ^ 3)) + ((-30) * T) + (112 * ((8 + (5 * T)) ^ 2)) + ((15 + (16 * T)) * (9 + (5 * T) + (10 * ((8 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_upper
    have identity : (((1770 + (200 * (T ^ 2)) + (1360 * T))) : ℚ) = ((200 * (T ^ 2)) + (1360 * T) + 1770) := by ring
    have scaling : ((10) * ((56 + ((-102) * ((8 + (5 * T)) ^ 2)) + (32 * ((8 + (5 * T)) ^ 3)) + (35 * T) + ((-1) * (15 + (16 * T)) * (9 + (5 * T) + (10 * ((8 + (5 * T)) ^ 2)))))) : ℚ) = ((1770 + (200 * (T ^ 2)) + (1360 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((200 * (T ^ 2)) + (1360 * T) + 1770) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * (56 + ((-102) * ((8 + (5 * T)) ^ 2)) + (32 * ((8 + (5 * T)) ^ 3)) + (35 * T) + ((-1) * (15 + (16 * T)) * (9 + (5 * T) + (10 * ((8 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (56 + ((-102) * ((8 + (5 * T)) ^ 2)) + (32 * ((8 + (5 * T)) ^ 3)) + (35 * T) + ((-1) * (15 + (16 * T)) * (9 + (5 * T) + (10 * ((8 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_old_upper
    have identity : (((36700 + (11400 * (T ^ 2)) + (41020 * T))) : ℚ) = ((11400 * (T ^ 2)) + (41020 * T) + 36700) := by ring
    have scaling : ((10) * ((612 + ((-160) * ((8 + (5 * T)) ^ 2)) + (64 * ((8 + (5 * T)) ^ 3)) + (380 * T) + ((-2) * (15 + (16 * T)) * (9 + (5 * T) + (10 * ((8 + (5 * T)) ^ 2)))))) : ℚ) = ((36700 + (11400 * (T ^ 2)) + (41020 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((11400 * (T ^ 2)) + (41020 * T) + 36700) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * (612 + ((-160) * ((8 + (5 * T)) ^ 2)) + (64 * ((8 + (5 * T)) ^ 3)) + (380 * T) + ((-2) * (15 + (16 * T)) * (9 + (5 * T) + (10 * ((8 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (612 + ((-160) * ((8 + (5 * T)) ^ 2)) + (64 * ((8 + (5 * T)) ^ 3)) + (380 * T) + ((-2) * (15 + (16 * T)) * (9 + (5 * T) + (10 * ((8 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_lower
    have identity : (((19590 + (7800 * (T ^ 2)) + (24790 * T))) : ℚ) = ((7800 * (T ^ 2)) + (24790 * T) + 19590) := by ring
    have scaling : ((10) * ((32 + ((-64) * ((8 + (5 * T)) ^ 3)) + (20 * T) + (240 * ((8 + (5 * T)) ^ 2)) + ((15 + (16 * T)) * (9 + (5 * T) + (20 * ((8 + (5 * T)) ^ 2)))))) : ℚ) = ((19590 + (7800 * (T ^ 2)) + (24790 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((7800 * (T ^ 2)) + (24790 * T) + 19590) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * (32 + ((-64) * ((8 + (5 * T)) ^ 3)) + (20 * T) + (240 * ((8 + (5 * T)) ^ 2)) + ((15 + (16 * T)) * (9 + (5 * T) + (20 * ((8 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (32 + ((-64) * ((8 + (5 * T)) ^ 3)) + (20 * T) + (240 * ((8 + (5 * T)) ^ 2)) + ((15 + (16 * T)) * (9 + (5 * T) + (20 * ((8 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_upper
    have identity : (((6940 + (400 * (T ^ 2)) + (4820 * T))) : ℚ) = ((400 * (T ^ 2)) + (4820 * T) + 6940) := by ring
    have scaling : ((10) * ((452 + ((-416) * ((8 + (5 * T)) ^ 2)) + (128 * ((8 + (5 * T)) ^ 3)) + (280 * T) + ((-2) * (15 + (16 * T)) * (9 + (5 * T) + (20 * ((8 + (5 * T)) ^ 2)))))) : ℚ) = ((6940 + (400 * (T ^ 2)) + (4820 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((400 * (T ^ 2)) + (4820 * T) + 6940) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * (452 + ((-416) * ((8 + (5 * T)) ^ 2)) + (128 * ((8 + (5 * T)) ^ 3)) + (280 * T) + ((-2) * (15 + (16 * T)) * (9 + (5 * T) + (20 * ((8 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (452 + ((-416) * ((8 + (5 * T)) ^ 2)) + (128 * ((8 + (5 * T)) ^ 3)) + (280 * T) + ((-2) * (15 + (16 * T)) * (9 + (5 * T) + (20 * ((8 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring

theorem a_two_b_c_plus_four_r4 (T : ℚ)
    (hT : 0 ≤ T) :
    HighResidual ((64 + (5 * T))) ((194 + (16 * T))) := by
  dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- m_lower
    have identity : (((1940 + (160 * T))) : ℚ) = ((160 * T) + 1940) := by ring
    have scaling : ((10) * ((194 + (16 * T))) : ℚ) = ((1940 + (160 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((160 * T) + 1940) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * (194 + (16 * T)) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (194 + (16 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_stock
    have identity : (((3170 + (240 * T))) : ℚ) = ((240 * T) + 3170) := by ring
    have scaling : ((10) * ((317 + (24 * T))) : ℚ) = ((3170 + (240 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((240 * T) + 3170) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * (317 + (24 * T)) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (317 + (24 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_lower
    have identity : (((286100 + (1800 * (T ^ 2)) + (45400 * T))) : ℚ) = ((1800 * (T ^ 2)) + (45400 * T) + 286100) := by ring
    have scaling : ((10) * (((-384) + ((-32) * ((64 + (5 * T)) ^ 3)) + ((-30) * T) + (112 * ((64 + (5 * T)) ^ 2)) + ((194 + (16 * T)) * (65 + (5 * T) + (10 * ((64 + (5 * T)) ^ 2)))))) : ℚ) = ((286100 + (1800 * (T ^ 2)) + (45400 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((1800 * (T ^ 2)) + (45400 * T) + 286100) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * ((-384) + ((-32) * ((64 + (5 * T)) ^ 3)) + ((-30) * T) + (112 * ((64 + (5 * T)) ^ 2)) + ((194 + (16 * T)) * (65 + (5 * T) + (10 * ((64 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-384) + ((-32) * ((64 + (5 * T)) ^ 3)) + ((-30) * T) + (112 * ((64 + (5 * T)) ^ 2)) + ((194 + (16 * T)) * (65 + (5 * T) + (10 * ((64 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_upper
    have identity : (((124140 + (700 * (T ^ 2)) + (18650 * T))) : ℚ) = ((700 * (T ^ 2)) + (18650 * T) + 124140) := by ring
    have scaling : ((10) * ((448 + ((-102) * ((64 + (5 * T)) ^ 2)) + (32 * ((64 + (5 * T)) ^ 3)) + (35 * T) + ((-1) * (194 + (16 * T)) * (65 + (5 * T) + (10 * ((64 + (5 * T)) ^ 2)))))) : ℚ) = ((124140 + (700 * (T ^ 2)) + (18650 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((700 * (T ^ 2)) + (18650 * T) + 124140) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * (448 + ((-102) * ((64 + (5 * T)) ^ 2)) + (32 * ((64 + (5 * T)) ^ 3)) + (35 * T) + ((-1) * (194 + (16 * T)) * (65 + (5 * T) + (10 * ((64 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (448 + ((-102) * ((64 + (5 * T)) ^ 2)) + (32 * ((64 + (5 * T)) ^ 3)) + (35 * T) + ((-1) * (194 + (16 * T)) * (65 + (5 * T) + (10 * ((64 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_old_upper
    have identity : (((2090240 + (12400 * (T ^ 2)) + (322000 * T))) : ℚ) = ((12400 * (T ^ 2)) + (322000 * T) + 2090240) := by ring
    have scaling : ((10) * ((4868 + ((-160) * ((64 + (5 * T)) ^ 2)) + (64 * ((64 + (5 * T)) ^ 3)) + (380 * T) + ((-2) * (194 + (16 * T)) * (65 + (5 * T) + (10 * ((64 + (5 * T)) ^ 2)))))) : ℚ) = ((2090240 + (12400 * (T ^ 2)) + (322000 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((12400 * (T ^ 2)) + (322000 * T) + 2090240) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * (4868 + ((-160) * ((64 + (5 * T)) ^ 2)) + (64 * ((64 + (5 * T)) ^ 3)) + (380 * T) + ((-2) * (194 + (16 * T)) * (65 + (5 * T) + (10 * ((64 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (4868 + ((-160) * ((64 + (5 * T)) ^ 2)) + (64 * ((64 + (5 * T)) ^ 3)) + (380 * T) + ((-2) * (194 + (16 * T)) * (65 + (5 * T) + (10 * ((64 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_lower
    have identity : (((1111700 + (6800 * (T ^ 2)) + (173900 * T))) : ℚ) = ((6800 * (T ^ 2)) + (173900 * T) + 1111700) := by ring
    have scaling : ((10) * ((256 + ((-64) * ((64 + (5 * T)) ^ 3)) + (20 * T) + (240 * ((64 + (5 * T)) ^ 2)) + ((194 + (16 * T)) * (65 + (5 * T) + (20 * ((64 + (5 * T)) ^ 2)))))) : ℚ) = ((1111700 + (6800 * (T ^ 2)) + (173900 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((6800 * (T ^ 2)) + (173900 * T) + 1111700) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * (256 + ((-64) * ((64 + (5 * T)) ^ 3)) + (20 * T) + (240 * ((64 + (5 * T)) ^ 2)) + ((194 + (16 * T)) * (65 + (5 * T) + (20 * ((64 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (256 + ((-64) * ((64 + (5 * T)) ^ 3)) + (20 * T) + (240 * ((64 + (5 * T)) ^ 2)) + ((194 + (16 * T)) * (65 + (5 * T) + (20 * ((64 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_upper
    have identity : (((439040 + (2400 * (T ^ 2)) + (65000 * T))) : ℚ) = ((2400 * (T ^ 2)) + (65000 * T) + 439040) := by ring
    have scaling : ((10) * ((3588 + ((-416) * ((64 + (5 * T)) ^ 2)) + (128 * ((64 + (5 * T)) ^ 3)) + (280 * T) + ((-2) * (194 + (16 * T)) * (65 + (5 * T) + (20 * ((64 + (5 * T)) ^ 2)))))) : ℚ) = ((439040 + (2400 * (T ^ 2)) + (65000 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((2400 * (T ^ 2)) + (65000 * T) + 439040) := by positivity
    have scale_pos : (0 : ℚ) < 10 := by positivity
    have scaled : (0 : ℚ) ≤ 10 * (3588 + ((-416) * ((64 + (5 * T)) ^ 2)) + (128 * ((64 + (5 * T)) ^ 3)) + (280 * T) + ((-2) * (194 + (16 * T)) * (65 + (5 * T) + (20 * ((64 + (5 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (3588 + ((-416) * ((64 + (5 * T)) ^ 2)) + (128 * ((64 + (5 * T)) ^ 3)) + (280 * T) + ((-2) * (194 + (16 * T)) * (65 + (5 * T) + (20 * ((64 + (5 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.HighB
