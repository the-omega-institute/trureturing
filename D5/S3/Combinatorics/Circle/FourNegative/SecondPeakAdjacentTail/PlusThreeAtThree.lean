/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakAdjacentTail/PlusThreeAtThree
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakAdjacentTail/PlusThreeAtThree
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

private theorem small_a3_cmod0 (T : ℚ)
    (hT : 0 ≤ T) :
    Residual (8) ((64 + (9 * T))) (8) (2) ((36 + (8 * T))) := by
  dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- m_lower
    have identity : (((36 + (8 * T))) : ℚ) = ((8 * T) + 36) := by ring
    have scaling : ((1) * ((36 + (8 * T))) : ℚ) = ((36 + (8 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((8 * T) + 36) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (36 + (8 * T)) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (36 + (8 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_stock
    have identity : (((219 + (28 * T))) : ℚ) = ((28 * T) + 219) := by ring
    have scaling : ((1) * ((219 + (28 * T))) : ℚ) = ((219 + (28 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((28 * T) + 219) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (219 + (28 * T)) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (219 + (28 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_lower
    have identity : (((5286 + (72 * (T ^ 2)) + (1258 * T))) : ℚ) = ((72 * (T ^ 2)) + (1258 * T) + 5286) := by ring
    have scaling : ((1) * ((2946 + ((-16) * ((64 + (9 * T)) ^ 3)) + (376 * ((64 + (9 * T)) ^ 2)) + (414 * T) + ((36 + (8 * T)) * (65 + (9 * T) + (18 * ((64 + (9 * T)) ^ 2)))))) : ℚ) = ((5286 + (72 * (T ^ 2)) + (1258 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((72 * (T ^ 2)) + (1258 * T) + 5286) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (2946 + ((-16) * ((64 + (9 * T)) ^ 3)) + (376 * ((64 + (9 * T)) ^ 2)) + (414 * T) + ((36 + (8 * T)) * (65 + (9 * T) + (18 * ((64 + (9 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (2946 + ((-16) * ((64 + (9 * T)) ^ 3)) + (376 * ((64 + (9 * T)) ^ 2)) + (414 * T) + ((36 + (8 * T)) * (65 + (9 * T) + (18 * ((64 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_upper
    have identity : (((68506 + (1386 * (T ^ 2)) + (19487 * T))) : ℚ) = ((1386 * (T ^ 2)) + (19487 * T) + 68506) := by ring
    have scaling : ((1) * (((-2882) + ((-405) * T) + ((-358) * ((64 + (9 * T)) ^ 2)) + (16 * ((64 + (9 * T)) ^ 3)) + ((-1) * (36 + (8 * T)) * (65 + (9 * T) + (18 * ((64 + (9 * T)) ^ 2)))))) : ℚ) = ((68506 + (1386 * (T ^ 2)) + (19487 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((1386 * (T ^ 2)) + (19487 * T) + 68506) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-2882) + ((-405) * T) + ((-358) * ((64 + (9 * T)) ^ 2)) + (16 * ((64 + (9 * T)) ^ 3)) + ((-1) * (36 + (8 * T)) * (65 + (9 * T) + (18 * ((64 + (9 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-2882) + ((-405) * T) + ((-358) * ((64 + (9 * T)) ^ 2)) + (16 * ((64 + (9 * T)) ^ 3)) + ((-1) * (36 + (8 * T)) * (65 + (9 * T) + (18 * ((64 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_old_upper
    have identity : (((255676 + (5040 * (T ^ 2)) + (71788 * T))) : ℚ) = ((5040 * (T ^ 2)) + (71788 * T) + 255676) := by ring
    have scaling : ((1) * (((-1788) + ((-688) * ((64 + (9 * T)) ^ 2)) + ((-252) * T) + (32 * ((64 + (9 * T)) ^ 3)) + ((-2) * (36 + (8 * T)) * (65 + (9 * T) + (18 * ((64 + (9 * T)) ^ 2)))))) : ℚ) = ((255676 + (5040 * (T ^ 2)) + (71788 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((5040 * (T ^ 2)) + (71788 * T) + 255676) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-1788) + ((-688) * ((64 + (9 * T)) ^ 2)) + ((-252) * T) + (32 * ((64 + (9 * T)) ^ 3)) + ((-2) * (36 + (8 * T)) * (65 + (9 * T) + (18 * ((64 + (9 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-1788) + ((-688) * ((64 + (9 * T)) ^ 2)) + ((-252) * T) + (32 * ((64 + (9 * T)) ^ 3)) + ((-2) * (36 + (8 * T)) * (65 + (9 * T) + (18 * ((64 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_lower
    have identity : (((41510 + (720 * (T ^ 2)) + (10960 * T))) : ℚ) = ((720 * (T ^ 2)) + (10960 * T) + 41510) := by ring
    have scaling : ((1) * ((6402 + ((-32) * ((64 + (9 * T)) ^ 3)) + (760 * ((64 + (9 * T)) ^ 2)) + (900 * T) + ((36 + (8 * T)) * (65 + (9 * T) + (36 * ((64 + (9 * T)) ^ 2)))))) : ℚ) = ((41510 + (720 * (T ^ 2)) + (10960 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((720 * (T ^ 2)) + (10960 * T) + 41510) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (6402 + ((-32) * ((64 + (9 * T)) ^ 3)) + (760 * ((64 + (9 * T)) ^ 2)) + (900 * T) + ((36 + (8 * T)) * (65 + (9 * T) + (36 * ((64 + (9 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (6402 + ((-32) * ((64 + (9 * T)) ^ 3)) + (760 * ((64 + (9 * T)) ^ 2)) + (900 * T) + ((36 + (8 * T)) * (65 + (9 * T) + (36 * ((64 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_upper
    have identity : (((183228 + (3744 * (T ^ 2)) + (52384 * T))) : ℚ) = ((3744 * (T ^ 2)) + (52384 * T) + 183228) := by ring
    have scaling : ((1) * (((-8700) + ((-1456) * ((64 + (9 * T)) ^ 2)) + ((-1224) * T) + (64 * ((64 + (9 * T)) ^ 3)) + ((-2) * (36 + (8 * T)) * (65 + (9 * T) + (36 * ((64 + (9 * T)) ^ 2)))))) : ℚ) = ((183228 + (3744 * (T ^ 2)) + (52384 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((3744 * (T ^ 2)) + (52384 * T) + 183228) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-8700) + ((-1456) * ((64 + (9 * T)) ^ 2)) + ((-1224) * T) + (64 * ((64 + (9 * T)) ^ 3)) + ((-2) * (36 + (8 * T)) * (65 + (9 * T) + (36 * ((64 + (9 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-8700) + ((-1456) * ((64 + (9 * T)) ^ 2)) + ((-1224) * T) + (64 * ((64 + (9 * T)) ^ 3)) + ((-2) * (36 + (8 * T)) * (65 + (9 * T) + (36 * ((64 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_old_upper
    have identity : (((1222524 + (11664 * (T ^ 3)) + (190188 * (T ^ 2)) + (934542 * T))) : ℚ) = ((11664 * (T ^ 3)) + (190188 * (T ^ 2)) + (934542 * T) + 1222524) := by ring
    have scaling : ((1) * (((-6276) + ((-882) * T) + ((-724) * ((64 + (9 * T)) ^ 2)) + (16 * ((64 + (9 * T)) ^ 3)))) : ℚ) = ((1222524 + (11664 * (T ^ 3)) + (190188 * (T ^ 2)) + (934542 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((11664 * (T ^ 3)) + (190188 * (T ^ 2)) + (934542 * T) + 1222524) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-6276) + ((-882) * T) + ((-724) * ((64 + (9 * T)) ^ 2)) + (16 * ((64 + (9 * T)) ^ 3))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-6276) + ((-882) * T) + ((-724) * ((64 + (9 * T)) ^ 2)) + (16 * ((64 + (9 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_new_upper
    have identity : (((2411644 + (23328 * (T ^ 3)) + (379728 * (T ^ 2)) + (1859778 * T))) : ℚ) = ((23328 * (T ^ 3)) + (379728 * (T ^ 2)) + (1859778 * T) + 2411644) := by ring
    have scaling : ((1) * (((-13188) + ((-1854) * T) + ((-1456) * ((64 + (9 * T)) ^ 2)) + (32 * ((64 + (9 * T)) ^ 3)))) : ℚ) = ((2411644 + (23328 * (T ^ 3)) + (379728 * (T ^ 2)) + (1859778 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((23328 * (T ^ 3)) + (379728 * (T ^ 2)) + (1859778 * T) + 2411644) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-13188) + ((-1854) * T) + ((-1456) * ((64 + (9 * T)) ^ 2)) + (32 * ((64 + (9 * T)) ^ 3))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-13188) + ((-1854) * T) + ((-1456) * ((64 + (9 * T)) ^ 2)) + (32 * ((64 + (9 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring

private theorem small_a3_cmod1 (T : ℚ)
    (hT : 0 ≤ T) :
    Residual (8) ((128 + (9 * T))) (8) (1) ((100 + (8 * T))) := by
  dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- m_lower
    have identity : (((100 + (8 * T))) : ℚ) = ((8 * T) + 100) := by ring
    have scaling : ((1) * ((100 + (8 * T))) : ℚ) = ((100 + (8 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((8 * T) + 100) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (100 + (8 * T)) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (100 + (8 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_stock
    have identity : (((411 + (28 * T))) : ℚ) = ((28 * T) + 411) := by ring
    have scaling : ((1) * ((411 + (28 * T))) : ℚ) = ((411 + (28 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((28 * T) + 411) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (411 + (28 * T)) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (411 + (28 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_lower
    have identity : (((16485 + (72 * (T ^ 2)) + (2184 * T))) : ℚ) = ((72 * (T ^ 2)) + (2184 * T) + 16485) := by ring
    have scaling : ((1) * ((3585 + ((-16) * ((128 + (9 * T)) ^ 3)) + (248 * ((128 + (9 * T)) ^ 2)) + (252 * T) + ((100 + (8 * T)) * (129 + (9 * T) + (18 * ((128 + (9 * T)) ^ 2)))))) : ℚ) = ((16485 + (72 * (T ^ 2)) + (2184 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((72 * (T ^ 2)) + (2184 * T) + 16485) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (3585 + ((-16) * ((128 + (9 * T)) ^ 3)) + (248 * ((128 + (9 * T)) ^ 2)) + (252 * T) + ((100 + (8 * T)) * (129 + (9 * T) + (18 * ((128 + (9 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (3585 + ((-16) * ((128 + (9 * T)) ^ 3)) + (248 * ((128 + (9 * T)) ^ 2)) + (252 * T) + ((100 + (8 * T)) * (129 + (9 * T) + (18 * ((128 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_upper
    have identity : (((278555 + (1386 * (T ^ 2)) + (39297 * T))) : ℚ) = ((1386 * (T ^ 2)) + (39297 * T) + 278555) := by ring
    have scaling : ((1) * (((-3457) + ((-243) * T) + ((-230) * ((128 + (9 * T)) ^ 2)) + (16 * ((128 + (9 * T)) ^ 3)) + ((-1) * (100 + (8 * T)) * (129 + (9 * T) + (18 * ((128 + (9 * T)) ^ 2)))))) : ℚ) = ((278555 + (1386 * (T ^ 2)) + (39297 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((1386 * (T ^ 2)) + (39297 * T) + 278555) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-3457) + ((-243) * T) + ((-230) * ((128 + (9 * T)) ^ 2)) + (16 * ((128 + (9 * T)) ^ 3)) + ((-1) * (100 + (8 * T)) * (129 + (9 * T) + (18 * ((128 + (9 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-3457) + ((-243) * T) + ((-230) * ((128 + (9 * T)) ^ 2)) + (16 * ((128 + (9 * T)) ^ 3)) + ((-1) * (100 + (8 * T)) * (129 + (9 * T) + (18 * ((128 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_old_upper
    have identity : (((1023806 + (5040 * (T ^ 2)) + (143664 * T))) : ℚ) = ((5040 * (T ^ 2)) + (143664 * T) + 1023806) := by ring
    have scaling : ((1) * ((1030 + ((-432) * ((128 + (9 * T)) ^ 2)) + (32 * ((128 + (9 * T)) ^ 3)) + (72 * T) + ((-2) * (100 + (8 * T)) * (129 + (9 * T) + (18 * ((128 + (9 * T)) ^ 2)))))) : ℚ) = ((1023806 + (5040 * (T ^ 2)) + (143664 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((5040 * (T ^ 2)) + (143664 * T) + 1023806) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (1030 + ((-432) * ((128 + (9 * T)) ^ 2)) + (32 * ((128 + (9 * T)) ^ 3)) + (72 * T) + ((-2) * (100 + (8 * T)) * (129 + (9 * T) + (18 * ((128 + (9 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (1030 + ((-432) * ((128 + (9 * T)) ^ 2)) + (32 * ((128 + (9 * T)) ^ 3)) + (72 * T) + ((-2) * (100 + (8 * T)) * (129 + (9 * T) + (18 * ((128 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_lower
    have identity : (((152165 + (720 * (T ^ 2)) + (20940 * T))) : ℚ) = ((720 * (T ^ 2)) + (20940 * T) + 152165) := by ring
    have scaling : ((1) * ((8193 + ((-32) * ((128 + (9 * T)) ^ 3)) + (504 * ((128 + (9 * T)) ^ 2)) + (576 * T) + ((100 + (8 * T)) * (129 + (9 * T) + (36 * ((128 + (9 * T)) ^ 2)))))) : ℚ) = ((152165 + (720 * (T ^ 2)) + (20940 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((720 * (T ^ 2)) + (20940 * T) + 152165) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (8193 + ((-32) * ((128 + (9 * T)) ^ 3)) + (504 * ((128 + (9 * T)) ^ 2)) + (576 * T) + ((100 + (8 * T)) * (129 + (9 * T) + (36 * ((128 + (9 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (8193 + ((-32) * ((128 + (9 * T)) ^ 3)) + (504 * ((128 + (9 * T)) ^ 2)) + (576 * T) + ((100 + (8 * T)) * (129 + (9 * T) + (36 * ((128 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_upper
    have identity : (((752446 + (3744 * (T ^ 2)) + (106152 * T))) : ℚ) = ((3744 * (T ^ 2)) + (106152 * T) + 752446) := by ring
    have scaling : ((1) * (((-8186) + ((-944) * ((128 + (9 * T)) ^ 2)) + ((-576) * T) + (64 * ((128 + (9 * T)) ^ 3)) + ((-2) * (100 + (8 * T)) * (129 + (9 * T) + (36 * ((128 + (9 * T)) ^ 2)))))) : ℚ) = ((752446 + (3744 * (T ^ 2)) + (106152 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((3744 * (T ^ 2)) + (106152 * T) + 752446) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-8186) + ((-944) * ((128 + (9 * T)) ^ 2)) + ((-576) * T) + (64 * ((128 + (9 * T)) ^ 3)) + ((-2) * (100 + (8 * T)) * (129 + (9 * T) + (36 * ((128 + (9 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-8186) + ((-944) * ((128 + (9 * T)) ^ 2)) + ((-576) * T) + (64 * ((128 + (9 * T)) ^ 3)) + ((-2) * (100 + (8 * T)) * (129 + (9 * T) + (36 * ((128 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_old_upper
    have identity : (((25878782 + (11664 * (T ^ 3)) + (459756 * (T ^ 2)) + (5999058 * T))) : ℚ) = ((11664 * (T ^ 3)) + (459756 * (T ^ 2)) + (5999058 * T) + 25878782) := by ring
    have scaling : ((1) * (((-7938) + ((-558) * T) + ((-468) * ((128 + (9 * T)) ^ 2)) + (16 * ((128 + (9 * T)) ^ 3)))) : ℚ) = ((25878782 + (11664 * (T ^ 3)) + (459756 * (T ^ 2)) + (5999058 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((11664 * (T ^ 3)) + (459756 * (T ^ 2)) + (5999058 * T) + 25878782) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-7938) + ((-558) * T) + ((-468) * ((128 + (9 * T)) ^ 2)) + (16 * ((128 + (9 * T)) ^ 3))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-7938) + ((-558) * T) + ((-468) * ((128 + (9 * T)) ^ 2)) + (16 * ((128 + (9 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_new_upper
    have identity : (((51625214 + (23328 * (T ^ 3)) + (918864 * (T ^ 2)) + (11979594 * T))) : ℚ) = ((23328 * (T ^ 3)) + (918864 * (T ^ 2)) + (11979594 * T) + 51625214) := by ring
    have scaling : ((1) * (((-17154) + ((-1206) * T) + ((-944) * ((128 + (9 * T)) ^ 2)) + (32 * ((128 + (9 * T)) ^ 3)))) : ℚ) = ((51625214 + (23328 * (T ^ 3)) + (918864 * (T ^ 2)) + (11979594 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((23328 * (T ^ 3)) + (918864 * (T ^ 2)) + (11979594 * T) + 51625214) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-17154) + ((-1206) * T) + ((-944) * ((128 + (9 * T)) ^ 2)) + (32 * ((128 + (9 * T)) ^ 3))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-17154) + ((-1206) * T) + ((-944) * ((128 + (9 * T)) ^ 2)) + (32 * ((128 + (9 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring

private theorem small_a3_cmod2 (T : ℚ)
    (hT : 0 ≤ T) :
    Residual (8) ((256 + (9 * T))) (8) (0) ((221 + (8 * T))) := by
  dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- m_lower
    have identity : (((221 + (8 * T))) : ℚ) = ((8 * T) + 221) := by ring
    have scaling : ((1) * ((221 + (8 * T))) : ℚ) = ((221 + (8 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((8 * T) + 221) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (221 + (8 * T)) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (221 + (8 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_stock
    have identity : (((802 + (28 * T))) : ℚ) = ((28 * T) + 802) := by ring
    have scaling : ((1) * ((802 + (28 * T))) : ℚ) = ((802 + (28 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((28 * T) + 802) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (802 + (28 * T)) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (802 + (28 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_lower
    have identity : (((190429 + (234 * (T ^ 2)) + (13351 * T))) : ℚ) = ((234 * (T ^ 2)) + (13351 * T) + 190429) := by ring
    have scaling : ((1) * ((2560 + ((-16) * ((256 + (9 * T)) ^ 3)) + (90 * T) + (120 * ((256 + (9 * T)) ^ 2)) + ((221 + (8 * T)) * (257 + (9 * T) + (18 * ((256 + (9 * T)) ^ 2)))))) : ℚ) = ((190429 + (234 * (T ^ 2)) + (13351 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((234 * (T ^ 2)) + (13351 * T) + 190429) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (2560 + ((-16) * ((256 + (9 * T)) ^ 3)) + (90 * T) + (120 * ((256 + (9 * T)) ^ 2)) + ((221 + (8 * T)) * (257 + (9 * T) + (18 * ((256 + (9 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (2560 + ((-16) * ((256 + (9 * T)) ^ 3)) + (90 * T) + (120 * ((256 + (9 * T)) ^ 2)) + ((221 + (8 * T)) * (257 + (9 * T) + (18 * ((256 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_upper
    have identity : (((989475 + (1224 * (T ^ 2)) + (69602 * T))) : ℚ) = ((1224 * (T ^ 2)) + (69602 * T) + 989475) := by ring
    have scaling : ((1) * (((-2304) + ((-102) * ((256 + (9 * T)) ^ 2)) + ((-81) * T) + (16 * ((256 + (9 * T)) ^ 3)) + ((-1) * (221 + (8 * T)) * (257 + (9 * T) + (18 * ((256 + (9 * T)) ^ 2)))))) : ℚ) = ((989475 + (1224 * (T ^ 2)) + (69602 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((1224 * (T ^ 2)) + (69602 * T) + 989475) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-2304) + ((-102) * ((256 + (9 * T)) ^ 2)) + ((-81) * T) + (16 * ((256 + (9 * T)) ^ 3)) + ((-1) * (221 + (8 * T)) * (257 + (9 * T) + (18 * ((256 + (9 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-2304) + ((-102) * ((256 + (9 * T)) ^ 2)) + ((-81) * T) + (16 * ((256 + (9 * T)) ^ 3)) + ((-1) * (221 + (8 * T)) * (257 + (9 * T) + (18 * ((256 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_old_upper
    have identity : (((3829838 + (4716 * (T ^ 2)) + (268786 * T))) : ℚ) = ((4716 * (T ^ 2)) + (268786 * T) + 3829838) := by ring
    have scaling : ((1) * ((11272 + ((-176) * ((256 + (9 * T)) ^ 2)) + (32 * ((256 + (9 * T)) ^ 3)) + (396 * T) + ((-2) * (221 + (8 * T)) * (257 + (9 * T) + (18 * ((256 + (9 * T)) ^ 2)))))) : ℚ) = ((3829838 + (4716 * (T ^ 2)) + (268786 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((4716 * (T ^ 2)) + (268786 * T) + 3829838) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (11272 + ((-176) * ((256 + (9 * T)) ^ 2)) + (32 * ((256 + (9 * T)) ^ 3)) + (396 * T) + ((-2) * (221 + (8 * T)) * (257 + (9 * T) + (18 * ((256 + (9 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (11272 + ((-176) * ((256 + (9 * T)) ^ 2)) + (32 * ((256 + (9 * T)) ^ 3)) + (396 * T) + ((-2) * (221 + (8 * T)) * (257 + (9 * T) + (18 * ((256 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_lower
    have identity : (((850397 + (1044 * (T ^ 2)) + (59593 * T))) : ℚ) = ((1044 * (T ^ 2)) + (59593 * T) + 850397) := by ring
    have scaling : ((1) * ((7168 + ((-32) * ((256 + (9 * T)) ^ 3)) + (248 * ((256 + (9 * T)) ^ 2)) + (252 * T) + ((221 + (8 * T)) * (257 + (9 * T) + (36 * ((256 + (9 * T)) ^ 2)))))) : ℚ) = ((850397 + (1044 * (T ^ 2)) + (59593 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((1044 * (T ^ 2)) + (59593 * T) + 850397) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (7168 + ((-32) * ((256 + (9 * T)) ^ 3)) + (248 * ((256 + (9 * T)) ^ 2)) + (252 * T) + ((221 + (8 * T)) * (257 + (9 * T) + (36 * ((256 + (9 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (7168 + ((-32) * ((256 + (9 * T)) ^ 3)) + (248 * ((256 + (9 * T)) ^ 2)) + (252 * T) + ((221 + (8 * T)) * (257 + (9 * T) + (36 * ((256 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_upper
    have identity : (((2509902 + (3096 * (T ^ 2)) + (176302 * T))) : ℚ) = ((3096 * (T ^ 2)) + (176302 * T) + 2509902) := by ring
    have scaling : ((1) * ((2056 + ((-432) * ((256 + (9 * T)) ^ 2)) + (64 * ((256 + (9 * T)) ^ 3)) + (72 * T) + ((-2) * (221 + (8 * T)) * (257 + (9 * T) + (36 * ((256 + (9 * T)) ^ 2)))))) : ℚ) = ((2509902 + (3096 * (T ^ 2)) + (176302 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((3096 * (T ^ 2)) + (176302 * T) + 2509902) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (2056 + ((-432) * ((256 + (9 * T)) ^ 2)) + (64 * ((256 + (9 * T)) ^ 3)) + (72 * T) + ((-2) * (221 + (8 * T)) * (257 + (9 * T) + (36 * ((256 + (9 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (2056 + ((-432) * ((256 + (9 * T)) ^ 2)) + (64 * ((256 + (9 * T)) ^ 3)) + (72 * T) + ((-2) * (221 + (8 * T)) * (257 + (9 * T) + (36 * ((256 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_old_upper
    have identity : (((254535168 + (11664 * (T ^ 3)) + (978156 * (T ^ 2)) + (27334422 * T))) : ℚ) = ((11664 * (T ^ 3)) + (978156 * (T ^ 2)) + (27334422 * T) + 254535168) := by ring
    have scaling : ((1) * (((-6656) + ((-234) * T) + ((-212) * ((256 + (9 * T)) ^ 2)) + (16 * ((256 + (9 * T)) ^ 3)))) : ℚ) = ((254535168 + (11664 * (T ^ 3)) + (978156 * (T ^ 2)) + (27334422 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((11664 * (T ^ 3)) + (978156 * (T ^ 2)) + (27334422 * T) + 254535168) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-6656) + ((-234) * T) + ((-212) * ((256 + (9 * T)) ^ 2)) + (16 * ((256 + (9 * T)) ^ 3))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-6656) + ((-234) * T) + ((-212) * ((256 + (9 * T)) ^ 2)) + (16 * ((256 + (9 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_new_upper
    have identity : (((508543488 + (23328 * (T ^ 3)) + (1955664 * (T ^ 2)) + (54631890 * T))) : ℚ) = ((23328 * (T ^ 3)) + (1955664 * (T ^ 2)) + (54631890 * T) + 508543488) := by ring
    have scaling : ((1) * (((-15872) + ((-558) * T) + ((-432) * ((256 + (9 * T)) ^ 2)) + (32 * ((256 + (9 * T)) ^ 3)))) : ℚ) = ((508543488 + (23328 * (T ^ 3)) + (1955664 * (T ^ 2)) + (54631890 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((23328 * (T ^ 3)) + (1955664 * (T ^ 2)) + (54631890 * T) + 508543488) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-15872) + ((-558) * T) + ((-432) * ((256 + (9 * T)) ^ 2)) + (32 * ((256 + (9 * T)) ^ 3))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-15872) + ((-558) * T) + ((-432) * ((256 + (9 * T)) ^ 2)) + (32 * ((256 + (9 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring

private theorem small_a3_cmod3 (T : ℚ)
    (hT : 0 ≤ T) :
    Residual (8) ((512 + (9 * T))) (8) (0) ((449 + (8 * T))) := by
  dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- m_lower
    have identity : (((449 + (8 * T))) : ℚ) = ((8 * T) + 449) := by ring
    have scaling : ((1) * ((449 + (8 * T))) : ℚ) = ((449 + (8 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((8 * T) + 449) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (449 + (8 * T)) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (449 + (8 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_stock
    have identity : (((1598 + (28 * T))) : ℚ) = ((28 * T) + 1598) := by ring
    have scaling : ((1) * ((1598 + (28 * T))) : ℚ) = ((1598 + (28 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((28 * T) + 1598) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (1598 + (28 * T)) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (1598 + (28 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_lower
    have identity : (((2856897 + (882 * (T ^ 2)) + (100395 * T))) : ℚ) = ((882 * (T ^ 2)) + (100395 * T) + 2856897) := by ring
    have scaling : ((1) * ((5120 + ((-16) * ((512 + (9 * T)) ^ 3)) + (90 * T) + (120 * ((512 + (9 * T)) ^ 2)) + ((449 + (8 * T)) * (513 + (9 * T) + (18 * ((512 + (9 * T)) ^ 2)))))) : ℚ) = ((2856897 + (882 * (T ^ 2)) + (100395 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((882 * (T ^ 2)) + (100395 * T) + 2856897) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (5120 + ((-16) * ((512 + (9 * T)) ^ 3)) + (90 * T) + (120 * ((512 + (9 * T)) ^ 2)) + ((449 + (8 * T)) * (513 + (9 * T) + (18 * ((512 + (9 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (5120 + ((-16) * ((512 + (9 * T)) ^ 3)) + (90 * T) + (120 * ((512 + (9 * T)) ^ 2)) + ((449 + (8 * T)) * (513 + (9 * T) + (18 * ((512 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_upper
    have identity : (((1862207 + (576 * (T ^ 2)) + (65502 * T))) : ℚ) = ((576 * (T ^ 2)) + (65502 * T) + 1862207) := by ring
    have scaling : ((1) * (((-4608) + ((-102) * ((512 + (9 * T)) ^ 2)) + ((-81) * T) + (16 * ((512 + (9 * T)) ^ 3)) + ((-1) * (449 + (8 * T)) * (513 + (9 * T) + (18 * ((512 + (9 * T)) ^ 2)))))) : ℚ) = ((1862207 + (576 * (T ^ 2)) + (65502 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((576 * (T ^ 2)) + (65502 * T) + 1862207) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-4608) + ((-102) * ((512 + (9 * T)) ^ 2)) + ((-81) * T) + (16 * ((512 + (9 * T)) ^ 3)) + ((-1) * (449 + (8 * T)) * (513 + (9 * T) + (18 * ((512 + (9 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-4608) + ((-102) * ((512 + (9 * T)) ^ 2)) + ((-81) * T) + (16 * ((512 + (9 * T)) ^ 3)) + ((-1) * (449 + (8 * T)) * (513 + (9 * T) + (18 * ((512 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_old_upper
    have identity : (((11096198 + (3420 * (T ^ 2)) + (389610 * T))) : ℚ) = ((3420 * (T ^ 2)) + (389610 * T) + 11096198) := by ring
    have scaling : ((1) * ((22536 + ((-176) * ((512 + (9 * T)) ^ 2)) + (32 * ((512 + (9 * T)) ^ 3)) + (396 * T) + ((-2) * (449 + (8 * T)) * (513 + (9 * T) + (18 * ((512 + (9 * T)) ^ 2)))))) : ℚ) = ((11096198 + (3420 * (T ^ 2)) + (389610 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((3420 * (T ^ 2)) + (389610 * T) + 11096198) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (22536 + ((-176) * ((512 + (9 * T)) ^ 2)) + (32 * ((512 + (9 * T)) ^ 3)) + (396 * T) + ((-2) * (449 + (8 * T)) * (513 + (9 * T) + (18 * ((512 + (9 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (22536 + ((-176) * ((512 + (9 * T)) ^ 2)) + (32 * ((512 + (9 * T)) ^ 3)) + (396 * T) + ((-2) * (449 + (8 * T)) * (513 + (9 * T) + (18 * ((512 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_lower
    have identity : (((7584705 + (2340 * (T ^ 2)) + (266445 * T))) : ℚ) = ((2340 * (T ^ 2)) + (266445 * T) + 7584705) := by ring
    have scaling : ((1) * ((14336 + ((-32) * ((512 + (9 * T)) ^ 3)) + (248 * ((512 + (9 * T)) ^ 2)) + (252 * T) + ((449 + (8 * T)) * (513 + (9 * T) + (36 * ((512 + (9 * T)) ^ 2)))))) : ℚ) = ((7584705 + (2340 * (T ^ 2)) + (266445 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((2340 * (T ^ 2)) + (266445 * T) + 7584705) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (14336 + ((-32) * ((512 + (9 * T)) ^ 3)) + (248 * ((512 + (9 * T)) ^ 2)) + (252 * T) + ((449 + (8 * T)) * (513 + (9 * T) + (36 * ((512 + (9 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (14336 + ((-32) * ((512 + (9 * T)) ^ 3)) + (248 * ((512 + (9 * T)) ^ 2)) + (252 * T) + ((449 + (8 * T)) * (513 + (9 * T) + (36 * ((512 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_upper
    have identity : (((1640582 + (504 * (T ^ 2)) + (57510 * T))) : ℚ) = ((504 * (T ^ 2)) + (57510 * T) + 1640582) := by ring
    have scaling : ((1) * ((4104 + ((-432) * ((512 + (9 * T)) ^ 2)) + (64 * ((512 + (9 * T)) ^ 3)) + (72 * T) + ((-2) * (449 + (8 * T)) * (513 + (9 * T) + (36 * ((512 + (9 * T)) ^ 2)))))) : ℚ) = ((1640582 + (504 * (T ^ 2)) + (57510 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((504 * (T ^ 2)) + (57510 * T) + 1640582) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (4104 + ((-432) * ((512 + (9 * T)) ^ 2)) + (64 * ((512 + (9 * T)) ^ 3)) + (72 * T) + ((-2) * (449 + (8 * T)) * (513 + (9 * T) + (36 * ((512 + (9 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (4104 + ((-432) * ((512 + (9 * T)) ^ 2)) + (64 * ((512 + (9 * T)) ^ 3)) + (72 * T) + ((-2) * (449 + (8 * T)) * (513 + (9 * T) + (36 * ((512 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_old_upper
    have identity : (((2091895808 + (11664 * (T ^ 3)) + (1973484 * (T ^ 2)) + (111292182 * T))) : ℚ) = ((11664 * (T ^ 3)) + (1973484 * (T ^ 2)) + (111292182 * T) + 2091895808) := by ring
    have scaling : ((1) * (((-13312) + ((-234) * T) + ((-212) * ((512 + (9 * T)) ^ 2)) + (16 * ((512 + (9 * T)) ^ 3)))) : ℚ) = ((2091895808 + (11664 * (T ^ 3)) + (1973484 * (T ^ 2)) + (111292182 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((11664 * (T ^ 3)) + (1973484 * (T ^ 2)) + (111292182 * T) + 2091895808) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-13312) + ((-234) * T) + ((-212) * ((512 + (9 * T)) ^ 2)) + (16 * ((512 + (9 * T)) ^ 3))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-13312) + ((-234) * T) + ((-212) * ((512 + (9 * T)) ^ 2)) + (16 * ((512 + (9 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_new_upper
    have identity : (((4181689344 + (23328 * (T ^ 3)) + (3946320 * (T ^ 2)) + (222510546 * T))) : ℚ) = ((23328 * (T ^ 3)) + (3946320 * (T ^ 2)) + (222510546 * T) + 4181689344) := by ring
    have scaling : ((1) * (((-31744) + ((-558) * T) + ((-432) * ((512 + (9 * T)) ^ 2)) + (32 * ((512 + (9 * T)) ^ 3)))) : ℚ) = ((4181689344 + (23328 * (T ^ 3)) + (3946320 * (T ^ 2)) + (222510546 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((23328 * (T ^ 3)) + (3946320 * (T ^ 2)) + (222510546 * T) + 4181689344) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-31744) + ((-558) * T) + ((-432) * ((512 + (9 * T)) ^ 2)) + (32 * ((512 + (9 * T)) ^ 3))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-31744) + ((-558) * T) + ((-432) * ((512 + (9 * T)) ^ 2)) + (32 * ((512 + (9 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring

private theorem small_a3_cmod4 (T : ℚ)
    (hT : 0 ≤ T) :
    Residual (8) ((16 + (9 * T))) (8) (0) ((8 + (8 * T))) := by
  dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- m_lower
    have identity : (((8 + (8 * T))) : ℚ) = ((8 * T) + 8) := by ring
    have scaling : ((1) * ((8 + (8 * T))) : ℚ) = ((8 + (8 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((8 * T) + 8) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (8 + (8 * T)) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (8 + (8 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_stock
    have identity : (((55 + (28 * T))) : ℚ) = ((28 * T) + 55) := by ring
    have scaling : ((1) * ((55 + (28 * T))) : ℚ) = ((55 + (28 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((28 * T) + 55) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (55 + (28 * T)) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (55 + (28 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_lower
    have identity : (((2344 + (720 * (T ^ 2)) + (2602 * T))) : ℚ) = ((720 * (T ^ 2)) + (2602 * T) + 2344) := by ring
    have scaling : ((1) * ((160 + ((-16) * ((16 + (9 * T)) ^ 3)) + (90 * T) + (120 * ((16 + (9 * T)) ^ 2)) + ((8 + (8 * T)) * (17 + (9 * T) + (18 * ((16 + (9 * T)) ^ 2)))))) : ℚ) = ((2344 + (720 * (T ^ 2)) + (2602 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((720 * (T ^ 2)) + (2602 * T) + 2344) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (160 + ((-16) * ((16 + (9 * T)) ^ 3)) + (90 * T) + (120 * ((16 + (9 * T)) ^ 2)) + ((8 + (8 * T)) * (17 + (9 * T) + (18 * ((16 + (9 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (160 + ((-16) * ((16 + (9 * T)) ^ 3)) + (90 * T) + (120 * ((16 + (9 * T)) ^ 2)) + ((8 + (8 * T)) * (17 + (9 * T) + (18 * ((16 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_upper
    have identity : (((2280 + (738 * (T ^ 2)) + (2591 * T))) : ℚ) = ((738 * (T ^ 2)) + (2591 * T) + 2280) := by ring
    have scaling : ((1) * (((-144) + ((-102) * ((16 + (9 * T)) ^ 2)) + ((-81) * T) + (16 * ((16 + (9 * T)) ^ 3)) + ((-1) * (8 + (8 * T)) * (17 + (9 * T) + (18 * ((16 + (9 * T)) ^ 2)))))) : ℚ) = ((2280 + (738 * (T ^ 2)) + (2591 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((738 * (T ^ 2)) + (2591 * T) + 2280) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-144) + ((-102) * ((16 + (9 * T)) ^ 2)) + ((-81) * T) + (16 * ((16 + (9 * T)) ^ 3)) + ((-1) * (8 + (8 * T)) * (17 + (9 * T) + (18 * ((16 + (9 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-144) + ((-102) * ((16 + (9 * T)) ^ 2)) + ((-81) * T) + (16 * ((16 + (9 * T)) ^ 3)) + ((-1) * (8 + (8 * T)) * (17 + (9 * T) + (18 * ((16 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_old_upper
    have identity : (((12728 + (3744 * (T ^ 2)) + (13804 * T))) : ℚ) = ((3744 * (T ^ 2)) + (13804 * T) + 12728) := by ring
    have scaling : ((1) * ((712 + ((-176) * ((16 + (9 * T)) ^ 2)) + (32 * ((16 + (9 * T)) ^ 3)) + (396 * T) + ((-2) * (8 + (8 * T)) * (17 + (9 * T) + (18 * ((16 + (9 * T)) ^ 2)))))) : ℚ) = ((12728 + (3744 * (T ^ 2)) + (13804 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((3744 * (T ^ 2)) + (13804 * T) + 12728) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (712 + ((-176) * ((16 + (9 * T)) ^ 2)) + (32 * ((16 + (9 * T)) ^ 3)) + (396 * T) + ((-2) * (8 + (8 * T)) * (17 + (9 * T) + (18 * ((16 + (9 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (712 + ((-176) * ((16 + (9 * T)) ^ 2)) + (32 * ((16 + (9 * T)) ^ 3)) + (396 * T) + ((-2) * (8 + (8 * T)) * (17 + (9 * T) + (18 * ((16 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_lower
    have identity : (((6728 + (2016 * (T ^ 2)) + (7372 * T))) : ℚ) = ((2016 * (T ^ 2)) + (7372 * T) + 6728) := by ring
    have scaling : ((1) * ((448 + ((-32) * ((16 + (9 * T)) ^ 3)) + (248 * ((16 + (9 * T)) ^ 2)) + (252 * T) + ((8 + (8 * T)) * (17 + (9 * T) + (36 * ((16 + (9 * T)) ^ 2)))))) : ℚ) = ((6728 + (2016 * (T ^ 2)) + (7372 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((2016 * (T ^ 2)) + (7372 * T) + 6728) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (448 + ((-32) * ((16 + (9 * T)) ^ 3)) + (248 * ((16 + (9 * T)) ^ 2)) + (252 * T) + ((8 + (8 * T)) * (17 + (9 * T) + (36 * ((16 + (9 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (448 + ((-32) * ((16 + (9 * T)) ^ 3)) + (248 * ((16 + (9 * T)) ^ 2)) + (252 * T) + ((8 + (8 * T)) * (17 + (9 * T) + (36 * ((16 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_upper
    have identity : (((3960 + (1152 * (T ^ 2)) + (4264 * T))) : ℚ) = ((1152 * (T ^ 2)) + (4264 * T) + 3960) := by ring
    have scaling : ((1) * ((136 + ((-432) * ((16 + (9 * T)) ^ 2)) + (64 * ((16 + (9 * T)) ^ 3)) + (72 * T) + ((-2) * (8 + (8 * T)) * (17 + (9 * T) + (36 * ((16 + (9 * T)) ^ 2)))))) : ℚ) = ((3960 + (1152 * (T ^ 2)) + (4264 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((1152 * (T ^ 2)) + (4264 * T) + 3960) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (136 + ((-432) * ((16 + (9 * T)) ^ 2)) + (64 * ((16 + (9 * T)) ^ 3)) + (72 * T) + ((-2) * (8 + (8 * T)) * (17 + (9 * T) + (36 * ((16 + (9 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (136 + ((-432) * ((16 + (9 * T)) ^ 2)) + (64 * ((16 + (9 * T)) ^ 3)) + (72 * T) + ((-2) * (8 + (8 * T)) * (17 + (9 * T) + (36 * ((16 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_old_upper
    have identity : (((10848 + (11664 * (T ^ 3)) + (45036 * (T ^ 2)) + (49302 * T))) : ℚ) = ((11664 * (T ^ 3)) + (45036 * (T ^ 2)) + (49302 * T) + 10848) := by ring
    have scaling : ((1) * (((-416) + ((-234) * T) + ((-212) * ((16 + (9 * T)) ^ 2)) + (16 * ((16 + (9 * T)) ^ 3)))) : ℚ) = ((10848 + (11664 * (T ^ 3)) + (45036 * (T ^ 2)) + (49302 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((11664 * (T ^ 3)) + (45036 * (T ^ 2)) + (49302 * T) + 10848) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-416) + ((-234) * T) + ((-212) * ((16 + (9 * T)) ^ 2)) + (16 * ((16 + (9 * T)) ^ 3))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-416) + ((-234) * T) + ((-212) * ((16 + (9 * T)) ^ 2)) + (16 * ((16 + (9 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_new_upper
    have identity : (((19488 + (23328 * (T ^ 3)) + (89424 * (T ^ 2)) + (96210 * T))) : ℚ) = ((23328 * (T ^ 3)) + (89424 * (T ^ 2)) + (96210 * T) + 19488) := by ring
    have scaling : ((1) * (((-992) + ((-558) * T) + ((-432) * ((16 + (9 * T)) ^ 2)) + (32 * ((16 + (9 * T)) ^ 3)))) : ℚ) = ((19488 + (23328 * (T ^ 3)) + (89424 * (T ^ 2)) + (96210 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((23328 * (T ^ 3)) + (89424 * (T ^ 2)) + (96210 * T) + 19488) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-992) + ((-558) * T) + ((-432) * ((16 + (9 * T)) ^ 2)) + (32 * ((16 + (9 * T)) ^ 3))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-992) + ((-558) * T) + ((-432) * ((16 + (9 * T)) ^ 2)) + (32 * ((16 + (9 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring

private theorem small_a3_cmod5 (T : ℚ)
    (hT : 0 ≤ T) :
    Residual (8) ((32 + (9 * T))) (8) (0) ((22 + (8 * T))) := by
  dsimp only [Common, HighResidual, StocksAndResidual, Residual]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- m_lower
    have identity : (((22 + (8 * T))) : ℚ) = ((8 * T) + 22) := by ring
    have scaling : ((1) * ((22 + (8 * T))) : ℚ) = ((22 + (8 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((8 * T) + 22) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (22 + (8 * T)) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (22 + (8 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- m_stock
    have identity : (((105 + (28 * T))) : ℚ) = ((28 * T) + 105) := by ring
    have scaling : ((1) * ((105 + (28 * T))) : ℚ) = ((105 + (28 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((28 * T) + 105) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (105 + (28 * T)) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (105 + (28 * T)) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_lower
    have identity : (((5142 + (396 * (T ^ 2)) + (2856 * T))) : ℚ) = ((396 * (T ^ 2)) + (2856 * T) + 5142) := by ring
    have scaling : ((1) * ((320 + ((-16) * ((32 + (9 * T)) ^ 3)) + (90 * T) + (120 * ((32 + (9 * T)) ^ 2)) + ((22 + (8 * T)) * (33 + (9 * T) + (18 * ((32 + (9 * T)) ^ 2)))))) : ℚ) = ((5142 + (396 * (T ^ 2)) + (2856 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((396 * (T ^ 2)) + (2856 * T) + 5142) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (320 + ((-16) * ((32 + (9 * T)) ^ 3)) + (90 * T) + (120 * ((32 + (9 * T)) ^ 2)) + ((22 + (8 * T)) * (33 + (9 * T) + (18 * ((32 + (9 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (320 + ((-16) * ((32 + (9 * T)) ^ 3)) + (90 * T) + (120 * ((32 + (9 * T)) ^ 2)) + ((22 + (8 * T)) * (33 + (9 * T) + (18 * ((32 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- ceil_upper
    have identity : (((13322 + (1062 * (T ^ 2)) + (7521 * T))) : ℚ) = ((1062 * (T ^ 2)) + (7521 * T) + 13322) := by ring
    have scaling : ((1) * (((-288) + ((-102) * ((32 + (9 * T)) ^ 2)) + ((-81) * T) + (16 * ((32 + (9 * T)) ^ 3)) + ((-1) * (22 + (8 * T)) * (33 + (9 * T) + (18 * ((32 + (9 * T)) ^ 2)))))) : ℚ) = ((13322 + (1062 * (T ^ 2)) + (7521 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((1062 * (T ^ 2)) + (7521 * T) + 13322) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-288) + ((-102) * ((32 + (9 * T)) ^ 2)) + ((-81) * T) + (16 * ((32 + (9 * T)) ^ 3)) + ((-1) * (22 + (8 * T)) * (33 + (9 * T) + (18 * ((32 + (9 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-288) + ((-102) * ((32 + (9 * T)) ^ 2)) + ((-81) * T) + (16 * ((32 + (9 * T)) ^ 3)) + ((-1) * (22 + (8 * T)) * (33 + (9 * T) + (18 * ((32 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_old_upper
    have identity : (((57308 + (4392 * (T ^ 2)) + (31728 * T))) : ℚ) = ((4392 * (T ^ 2)) + (31728 * T) + 57308) := by ring
    have scaling : ((1) * ((1416 + ((-176) * ((32 + (9 * T)) ^ 2)) + (32 * ((32 + (9 * T)) ^ 3)) + (396 * T) + ((-2) * (22 + (8 * T)) * (33 + (9 * T) + (18 * ((32 + (9 * T)) ^ 2)))))) : ℚ) = ((57308 + (4392 * (T ^ 2)) + (31728 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((4392 * (T ^ 2)) + (31728 * T) + 57308) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (1416 + ((-176) * ((32 + (9 * T)) ^ 2)) + (32 * ((32 + (9 * T)) ^ 3)) + (396 * T) + ((-2) * (22 + (8 * T)) * (33 + (9 * T) + (18 * ((32 + (9 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (1416 + ((-176) * ((32 + (9 * T)) ^ 2)) + (32 * ((32 + (9 * T)) ^ 3)) + (396 * T) + ((-2) * (22 + (8 * T)) * (33 + (9 * T) + (18 * ((32 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_lower
    have identity : (((18006 + (1368 * (T ^ 2)) + (9930 * T))) : ℚ) = ((1368 * (T ^ 2)) + (9930 * T) + 18006) := by ring
    have scaling : ((1) * ((896 + ((-32) * ((32 + (9 * T)) ^ 3)) + (248 * ((32 + (9 * T)) ^ 2)) + (252 * T) + ((22 + (8 * T)) * (33 + (9 * T) + (36 * ((32 + (9 * T)) ^ 2)))))) : ℚ) = ((18006 + (1368 * (T ^ 2)) + (9930 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((1368 * (T ^ 2)) + (9930 * T) + 18006) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (896 + ((-32) * ((32 + (9 * T)) ^ 3)) + (248 * ((32 + (9 * T)) ^ 2)) + (252 * T) + ((22 + (8 * T)) * (33 + (9 * T) + (36 * ((32 + (9 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (896 + ((-32) * ((32 + (9 * T)) ^ 3)) + (248 * ((32 + (9 * T)) ^ 2)) + (252 * T) + ((22 + (8 * T)) * (33 + (9 * T) + (36 * ((32 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- second_new_upper
    have identity : (((31580 + (2448 * (T ^ 2)) + (17580 * T))) : ℚ) = ((2448 * (T ^ 2)) + (17580 * T) + 31580) := by ring
    have scaling : ((1) * ((264 + ((-432) * ((32 + (9 * T)) ^ 2)) + (64 * ((32 + (9 * T)) ^ 3)) + (72 * T) + ((-2) * (22 + (8 * T)) * (33 + (9 * T) + (36 * ((32 + (9 * T)) ^ 2)))))) : ℚ) = ((31580 + (2448 * (T ^ 2)) + (17580 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((2448 * (T ^ 2)) + (17580 * T) + 31580) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * (264 + ((-432) * ((32 + (9 * T)) ^ 2)) + (64 * ((32 + (9 * T)) ^ 3)) + (72 * T) + ((-2) * (22 + (8 * T)) * (33 + (9 * T) + (36 * ((32 + (9 * T)) ^ 2))))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ (264 + ((-432) * ((32 + (9 * T)) ^ 2)) + (64 * ((32 + (9 * T)) ^ 3)) + (72 * T) + ((-2) * (22 + (8 * T)) * (33 + (9 * T) + (36 * ((32 + (9 * T)) ^ 2))))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_old_upper
    have identity : (((306368 + (11664 * (T ^ 3)) + (107244 * (T ^ 2)) + (320022 * T))) : ℚ) = ((11664 * (T ^ 3)) + (107244 * (T ^ 2)) + (320022 * T) + 306368) := by ring
    have scaling : ((1) * (((-832) + ((-234) * T) + ((-212) * ((32 + (9 * T)) ^ 2)) + (16 * ((32 + (9 * T)) ^ 3)))) : ℚ) = ((306368 + (11664 * (T ^ 3)) + (107244 * (T ^ 2)) + (320022 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((11664 * (T ^ 3)) + (107244 * (T ^ 2)) + (320022 * T) + 306368) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-832) + ((-234) * T) + ((-212) * ((32 + (9 * T)) ^ 2)) + (16 * ((32 + (9 * T)) ^ 3))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-832) + ((-234) * T) + ((-212) * ((32 + (9 * T)) ^ 2)) + (16 * ((32 + (9 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring
  · -- third_new_upper
    have identity : (((604224 + (23328 * (T ^ 3)) + (213840 * (T ^ 2)) + (635346 * T))) : ℚ) = ((23328 * (T ^ 3)) + (213840 * (T ^ 2)) + (635346 * T) + 604224) := by ring
    have scaling : ((1) * (((-1984) + ((-558) * T) + ((-432) * ((32 + (9 * T)) ^ 2)) + (32 * ((32 + (9 * T)) ^ 3)))) : ℚ) = ((604224 + (23328 * (T ^ 3)) + (213840 * (T ^ 2)) + (635346 * T))) := by
      field_simp <;> ring
    have positive : (0 : ℚ) ≤ ((23328 * (T ^ 3)) + (213840 * (T ^ 2)) + (635346 * T) + 604224) := by positivity
    have scale_pos : (0 : ℚ) < 1 := by positivity
    have scaled : (0 : ℚ) ≤ 1 * ((-1984) + ((-558) * T) + ((-432) * ((32 + (9 * T)) ^ 2)) + (32 * ((32 + (9 * T)) ^ 3))) := by rw [scaling,identity]; exact positive
    have side : (0 : ℚ) ≤ ((-1984) + ((-558) * T) + ((-432) * ((32 + (9 * T)) ^ 2)) + (32 * ((32 + (9 * T)) ^ 3))) := (mul_nonneg_iff_of_pos_left scale_pos).mp scaled
    convert side using 1 <;> dsimp [A,B,L,K,SU,SV,SW,E,F] <;> field_simp <;> ring


end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.PlusThree
