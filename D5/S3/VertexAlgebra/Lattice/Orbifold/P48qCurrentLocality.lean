import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qHeisenbergCharged
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedHeisenberg

open P48qThirdTwistedField (Cartan State)
open ThirdEigenspacePairing (p48qForm)

attribute [local instance] LieRing.ofAssociativeRing

/-- At cover exponents `m, l` the signed modes are `-m - 3, -l - 3`.
Their commutator is supported on `m + l = -6`. -/
theorem currentField_coeff_commutator (u v : Cartan) (m l : ℤ) :
    ⁅HVertexOperator.coeff (currentField u) m,
        HVertexOperator.coeff (currentField v) l⁆ =
      if m + l = -6 then
        ((((-m - 3 : ℤ) : ℂ) / 3) * p48qForm (projectAt (-m - 3) u) v) •
          (1 : Module.End ℂ State)
      else 0 := by
  have hopposite : (-m - 3) + (-l - 3) = 0 ↔ m + l = -6 := by omega
  simp only [currentField_coeff, mode_commutator, hopposite]

private theorem projectAt_period_three (u : Cartan) (k : ℤ) :
    projectAt (k + 3) u = projectAt k u := by
  rw [projectAt_eq_fourier, projectAt_eq_fourier, Int.add_emod_right]

private theorem affine_second_difference (k : ℤ) (c : ℂ) :
    (((k + 6 : ℤ) : ℂ) / 3) * c - 2 * ((((k + 3 : ℤ) : ℂ) / 3) * c) +
      ((k : ℂ) / 3) * c = 0 := by
  simp only [Int.cast_add, Int.cast_ofNat]
  ring

/-- The coefficient of `x^m y^l` in `(x^3 - y^3)^2 [currentField u (x),
currentField v (y)]` is zero as an endomorphism of the full `State`.
The three terms come from `x^6`, `-2 x^3 y^3`, and `y^6`. With `k = -m - 3`
and `j = -l - 3` their signed pairs are `(k + 6, j)`, `(k + 3, j + 3)`,
and `(k, j + 6)`. All three pairs sum to zero exactly when `m + l = 0`. -/
theorem currentField_currentField_locality (u v : Cartan) (m l : ℤ) :
    ⁅HVertexOperator.coeff (currentField u) (m - 6),
        HVertexOperator.coeff (currentField v) l⁆ -
      (2 : ℂ) • ⁅HVertexOperator.coeff (currentField u) (m - 3),
        HVertexOperator.coeff (currentField v) (l - 3)⁆ +
      ⁅HVertexOperator.coeff (currentField u) m,
        HVertexOperator.coeff (currentField v) (l - 6)⁆ = 0 := by
  have hxx : (m - 6) + l = -6 ↔ m + l = 0 := by omega
  have hxy : (m - 3) + (l - 3) = -6 ↔ m + l = 0 := by omega
  have hyy : m + (l - 6) = -6 ↔ m + l = 0 := by omega
  simp only [currentField_coeff_commutator, hxx, hxy, hyy]
  by_cases h : m + l = 0
  · simp only [if_pos h]
    let k : ℤ := -m - 3
    have hk₆ : -(m - 6) - 3 = k + 6 := by
      dsimp [k]
      omega
    have hk₃ : -(m - 3) - 3 = k + 3 := by
      dsimp [k]
      omega
    have hp₆ : projectAt (k + 6) u = projectAt k u := by
      calc
        projectAt (k + 6) u = projectAt ((k + 3) + 3) u := by
          rw [show k + 6 = (k + 3) + 3 by omega]
        _ = projectAt (k + 3) u := projectAt_period_three u (k + 3)
        _ = projectAt k u := projectAt_period_three u k
    rw [hk₆, hk₃, hp₆, projectAt_period_three u k, smul_smul, ← sub_smul, ← add_smul]
    simpa only [zero_smul] using
      congrArg (fun c : ℂ => c • (1 : Module.End ℂ State))
        (affine_second_difference k (p48qForm (projectAt k u) v))
  · simp only [if_neg h, smul_zero, sub_zero, add_zero]

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedHeisenberg

#print axioms D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedHeisenberg.currentField_currentField_locality
