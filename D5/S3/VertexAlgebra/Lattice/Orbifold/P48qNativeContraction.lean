/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeContraction
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The cubic scalar contraction and Fourier coefficients for the native P48q action. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedChargeAction
import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedScalarLocality

/-! The cubic scalar contraction and Fourier coefficients for the native P48q action. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeContraction

open LatticeGeneratingFieldLocality (Charge bilinear)
open P48qTwistedChargeAction (lattice g g_cube g_isometry)
open ThirdTwistedContraction (binomialUnit)
open PowerSeries
open scoped BigOperators

local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)

/-- The series in the scalar exponential in the native cover coordinate. -/
abbrev contractionExponent : Charge lattice → Charge lattice → PowerSeries ℂ :=
  ThirdTwistedContraction.contractionExponent lattice g ζ

/-- The complex scalar extension of the native lattice pairing. -/
abbrev complexPairing : LinearMap.BilinForm ℂ (Fin lattice.rank → ℂ) :=
  ThirdTwistedContraction.complexPairing lattice

/-- Fourier component for eigenvalue `u⁻¹` when `u ^ 3 = 1`. -/
abbrev fourierComponent : ℂ → Charge lattice → (Fin lattice.rank → ℂ) :=
  ThirdTwistedContraction.fourierComponent lattice g

@[simp] theorem constantCoeff_contractionExponent (a b : Charge lattice) :
    constantCoeff (contractionExponent a b) = 0 :=
  ThirdTwistedContraction.constantCoeff_contractionExponent lattice g ζ a b

/-- The scalar contraction for the native P48q action. -/
theorem scalar_contraction (a b : Charge lattice) :
    (exp ℂ).subst (contractionExponent a b) =
      (↑(∏ j ∈ Finset.range 3,
        binomialUnit (ζ ^ j) ^ bilinear lattice ((g^[j]) a) b) : PowerSeries ℂ) :=
  ThirdTwistedContraction.scalar_contraction lattice g ζ a b

/-- At positive frequency `n/3`, the coefficient uses the pairing of complementary
Fourier components. For `u = ζ^(n % 3)`, the second component has eigenvalue `u`. -/
theorem coeff_contractionExponent_opposite (a b : Charge lattice) {n : ℕ} (hn : n ≠ 0) :
    coeff n (contractionExponent a b) =
      -(complexPairing (fourierComponent (ζ ^ (n % 3)) a)
        (fourierComponent ((ζ ^ (n % 3)) ^ 2) b)) / ((n : ℂ) / 3) :=
  ThirdTwistedContraction.coeff_contractionExponent_opposite lattice g ζ g_cube g_isometry
    (IsPrimitiveRoot.coe_units_iff.mpr ThirdTwistedChargeCocycle.zeta_primitive).pow_eq_one a b hn

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeContraction
