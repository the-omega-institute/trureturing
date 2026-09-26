/- GID: D5/S3/Arith/Lattices/GoldenCubicIndexForm
   generality: I
   mirror-B: D5/B/S3/Arith/Lattices/GoldenCubicIndexForm
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The golden cubic order has an exact integral power-basis determinant. -/

import D5.S1.Scale.GoldenCubicBlockCongruences
import Mathlib.Data.Matrix.Reflection
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Ring

namespace D5.S3.Arith.Lattices.GoldenCubicIndexForm

open scoped Matrix
open D5.S1.Scale

/-- Coordinates on the integral order with basis `(1, theta, beta)` and
`theta^3 = 9a+1`, `3 beta = 1+theta+theta^2`. -/
@[ext] structure CubicOrder (a : ℤ) where
  c0 : ℤ
  c1 : ℤ
  c2 : ℤ
  deriving DecidableEq

namespace CubicOrder

variable {a : ℤ}

instance : Zero (CubicOrder a) := ⟨⟨0, 0, 0⟩⟩
instance : One (CubicOrder a) := ⟨⟨1, 0, 0⟩⟩
instance : Add (CubicOrder a) :=
  ⟨fun x y => ⟨x.c0 + y.c0, x.c1 + y.c1, x.c2 + y.c2⟩⟩
instance : Neg (CubicOrder a) := ⟨fun x => ⟨-x.c0, -x.c1, -x.c2⟩⟩

instance : Mul (CubicOrder a) :=
  ⟨fun x y =>
    ⟨x.c0 * y.c0 - x.c1 * y.c1 + 3 * a * (x.c1 * y.c2 + x.c2 * y.c1) +
        2 * a * x.c2 * y.c2,
      x.c0 * y.c1 + x.c1 * y.c0 - x.c1 * y.c1 + a * x.c2 * y.c2,
      x.c0 * y.c2 + x.c2 * y.c0 + 3 * x.c1 * y.c1 +
        x.c1 * y.c2 + x.c2 * y.c1 + x.c2 * y.c2⟩⟩

instance addCommGroup : AddCommGroup (CubicOrder a) := by
  have hc0_add (x y : CubicOrder a) : (x + y).c0 = x.c0 + y.c0 := rfl
  have hc1_add (x y : CubicOrder a) : (x + y).c1 = x.c1 + y.c1 := rfl
  have hc2_add (x y : CubicOrder a) : (x + y).c2 = x.c2 + y.c2 := rfl
  have hc0_neg (x : CubicOrder a) : (-x).c0 = -x.c0 := rfl
  have hc1_neg (x : CubicOrder a) : (-x).c1 = -x.c1 := rfl
  have hc2_neg (x : CubicOrder a) : (-x).c2 = -x.c2 := rfl
  have hc0_zero : (0 : CubicOrder a).c0 = 0 := rfl
  have hc1_zero : (0 : CubicOrder a).c1 = 0 := rfl
  have hc2_zero : (0 : CubicOrder a).c2 = 0 := rfl
  refine
    { sub := fun x y => x + -y
      nsmul := @nsmulRec (CubicOrder a) ⟨0⟩ ⟨(· + ·)⟩
      zsmul := @zsmulRec (CubicOrder a) ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩
        (@nsmulRec (CubicOrder a) ⟨0⟩ ⟨(· + ·)⟩)
      add_assoc := ?_
      zero_add := ?_
      add_zero := ?_
      neg_add_cancel := ?_
      add_comm := ?_ } <;>
    intros <;> ext <;>
      simp [hc0_add, hc1_add, hc2_add, hc0_neg, hc1_neg, hc2_neg,
        hc0_zero, hc1_zero, hc2_zero, add_comm, add_left_comm]

instance addGroupWithOne : AddGroupWithOne (CubicOrder a) :=
  { addCommGroup with
    natCast := fun n => ⟨n, 0, 0⟩
    intCast := fun z => ⟨z, 0, 0⟩ }

instance commRing : CommRing (CubicOrder a) := by
  have hc0_mul (x y : CubicOrder a) :
      (x * y).c0 = x.c0 * y.c0 - x.c1 * y.c1 +
        3 * a * (x.c1 * y.c2 + x.c2 * y.c1) + 2 * a * x.c2 * y.c2 := rfl
  have hc1_mul (x y : CubicOrder a) :
      (x * y).c1 = x.c0 * y.c1 + x.c1 * y.c0 - x.c1 * y.c1 +
        a * x.c2 * y.c2 := rfl
  have hc2_mul (x y : CubicOrder a) :
      (x * y).c2 = x.c0 * y.c2 + x.c2 * y.c0 + 3 * x.c1 * y.c1 +
        x.c1 * y.c2 + x.c2 * y.c1 + x.c2 * y.c2 := rfl
  have hc0_add (x y : CubicOrder a) : (x + y).c0 = x.c0 + y.c0 := rfl
  have hc1_add (x y : CubicOrder a) : (x + y).c1 = x.c1 + y.c1 := rfl
  have hc2_add (x y : CubicOrder a) : (x + y).c2 = x.c2 + y.c2 := rfl
  have hc0_zero : (0 : CubicOrder a).c0 = 0 := rfl
  have hc1_zero : (0 : CubicOrder a).c1 = 0 := rfl
  have hc2_zero : (0 : CubicOrder a).c2 = 0 := rfl
  have hc0_one : (1 : CubicOrder a).c0 = 1 := rfl
  have hc1_one : (1 : CubicOrder a).c1 = 0 := rfl
  have hc2_one : (1 : CubicOrder a).c2 = 0 := rfl
  refine
    { addGroupWithOne with
      npow := @npowRec (CubicOrder a) ⟨1⟩ ⟨(· * ·)⟩
      mul_assoc := ?_
      one_mul := ?_
      mul_one := ?_
      left_distrib := ?_
      right_distrib := ?_
      zero_mul := ?_
      mul_zero := ?_
      add_comm := ?_
      mul_comm := ?_ } <;>
    intros <;> ext <;>
      simp [hc0_mul, hc1_mul, hc2_mul, hc0_add, hc1_add, hc2_add,
        hc0_zero, hc1_zero, hc2_zero, hc0_one, hc1_one, hc2_one] <;> ring

end CubicOrder

def blockB (j : ℕ) : ℤ := goldenLucas (3 ^ j) ^ 2 + 3
def blockA (j : ℕ) : ℤ := (blockB j - 1) / 9

def basisElement (a : ℤ) : Fin 3 → CubicOrder a :=
  ![⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ⟨0, 0, 1⟩]

def coordinate {a : ℤ} (i : Fin 3) (x : CubicOrder a) : ℤ :=
  ![x.c0, x.c1, x.c2] i

def multiplicationMatrix {a : ℤ} (x : CubicOrder a) :
    Matrix (Fin 3) (Fin 3) ℤ :=
  fun i k => coordinate i (x * basisElement a k)

def regularTrace {a : ℤ} (x : CubicOrder a) : ℤ :=
  Matrix.trace (multiplicationMatrix x)

def traceGram (a : ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  fun i k => regularTrace (basisElement a i * basisElement a k)

/-- Columns of the power basis `(1, alpha, alpha^2)` in `(1, theta, beta)`. -/
def indexMatrix (a r b c : ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  let alpha : CubicOrder a := ⟨r, b, c⟩
  !![1, alpha.c0, (alpha ^ 2).c0;
     0, alpha.c1, (alpha ^ 2).c1;
     0, alpha.c2, (alpha ^ 2).c2]

/-- The trace discriminant and signed power-basis determinant of the cubic
coordinate order attached to an actual golden block. -/
theorem golden_cubic_discriminant_index_form (j : ℕ) (hj : 1 ≤ j) (r b c : ℤ) :
    Matrix.det (traceGram (blockA j)) = -3 * blockB j ^ 2 ∧
      Matrix.det (indexMatrix (blockA j) r b c) =
        3 * b ^ 3 + 3 * b ^ 2 * c + b * c ^ 2 - blockA j * c ^ 3 ∧
      9 * Matrix.det (indexMatrix (blockA j) r b c) =
        (3 * b + c) ^ 3 - blockB j * c ^ 3 := by
  have hmod : ((blockB j : ℤ) : ZMod 9) = 1 := by
    simpa only [blockB] using (golden_cubic_lucas_block j hj).2.2.1
  have hdvd : (9 : ℤ) ∣ blockB j - 1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (blockB j - 1) 9).mp
    simpa only [Int.cast_sub, Int.cast_one, sub_self] using
      congrArg (fun z : ZMod 9 => z - 1) hmod
  have hB : blockB j = 9 * blockA j + 1 := by
    have h := Int.ediv_mul_cancel hdvd
    dsimp [blockA]
    omega
  have hc0 (x y : CubicOrder (blockA j)) :
      (x * y).c0 = x.c0 * y.c0 - x.c1 * y.c1 +
        3 * blockA j * (x.c1 * y.c2 + x.c2 * y.c1) +
        2 * blockA j * x.c2 * y.c2 := rfl
  have hc1 (x y : CubicOrder (blockA j)) :
      (x * y).c1 = x.c0 * y.c1 + x.c1 * y.c0 - x.c1 * y.c1 +
        blockA j * x.c2 * y.c2 := rfl
  have hc2 (x y : CubicOrder (blockA j)) :
      (x * y).c2 = x.c0 * y.c2 + x.c2 * y.c0 + 3 * x.c1 * y.c1 +
        x.c1 * y.c2 + x.c2 * y.c1 + x.c2 * y.c2 := rfl
  have htrace (x : CubicOrder (blockA j)) :
      regularTrace x = 3 * x.c0 + x.c2 := by
    simp [regularTrace, multiplicationMatrix, Matrix.trace,
      Fin.sum_univ_three, coordinate, basisElement, hc0, hc1, hc2]
    ring
  have hgram : traceGram (blockA j) =
      !![3, 0, 1; 0, 0, blockB j; 1, blockB j, 6 * blockA j + 1] := by
    ext i k
    fin_cases i <;> fin_cases k <;>
      simp [traceGram, htrace, basisElement, hc0, hc2, hB] <;> ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hgram, Matrix.det_fin_three]
    simp
    ring
  · simp [indexMatrix, Matrix.det_fin_three, pow_two, hc0, hc1, hc2]
    ring
  · rw [hB]
    simp [indexMatrix, Matrix.det_fin_three, pow_two, hc0, hc1, hc2]
    ring

end D5.S3.Arith.Lattices.GoldenCubicIndexForm
