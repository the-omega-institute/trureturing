/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryTraceRoot
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryTraceRoot
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryDiagonalGeometry

namespace NikolovSegal.UnitaryField
open Matrix
variable {F : Type*} [Field F] [Finite F]

def antiDiagonal3 : Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

def traceRoot3 (ι : F ≃+* F) (x y : F) : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, x, y; 0, 1, -ι x; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem traceRoot3_unitary (ι : F ≃+* F) (hinv : Function.Involutive ι)
    (x y : F) (hy : y + ι y = -(x * ι x)) :
    adjoint ι (traceRoot3 ι x y).val * antiDiagonal3 * (traceRoot3 ι x y).val =
      antiDiagonal3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adjoint, traceRoot3, antiDiagonal3, Matrix.mul_apply, Fin.sum_univ_three,
      map_neg, hinv x]
  linear_combination hy

/- Actual short-root coordinates in characteristic two as well as odd characteristic.
The trace selector is obtained from native separable trace surjectivity, and the
right hand side is the actual relative norm, identified above with x*iota(x). -/
theorem actual_trace_root_exists (ι : F ≃+* F)
    (hinv : Function.Involutive ι) (hne : ι ≠ RingEquiv.refl F) (x : F) :
    ∃ y : F, y + ι y = -(x * ι x) ∧
      adjoint ι (traceRoot3 ι x y).val * antiDiagonal3 * (traceRoot3 ι x y).val =
        antiDiagonal3 := by
  obtain ⟨y, hy⟩ := trace_surjective ι hinv hne (-Algebra.norm (fixedField ι) x)
  have hh : y + ι y = -(x * ι x) := by
    simpa only [Subfield.coe_neg, norm_formula ι hinv hne x] using hy
  exact ⟨y, hh, traceRoot3_unitary ι hinv x y hh⟩

end NikolovSegal.UnitaryField
