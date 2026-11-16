/- GID: D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The finite pointed fusion algebra carried by the discriminant group. -/

import Mathlib.Algebra.MonoidAlgebra.Basic
import D5.S3.VertexAlgebra.Characters.LatticeDiscriminantVerlinde

/-! # The finite discriminant fusion algebra

The normalized Weil `S`-kernel gives the addition law on the finite
discriminant group.  We package that law as the genuine finite based
algebra `ℂ[Discriminant D]`; this is an algebraic consequence of the
finite Verlinde coefficients and does not assert a tensor-category or
vertex-operator-algebra construction.
-/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.LatticeDiscriminantFusionAlgebra
open LatticeGeneratingFieldLocality LatticePositiveEnergy
open D5.S3.VertexAlgebra.LatticeDiscriminantTheta
open D5.S3.VertexAlgebra.LatticeDiscriminantVerlinde

noncomputable section

variable (D : LatticeData) [hD : Fact (gramReal D).PosDef]
local instance : Fintype (Discriminant D) := Fintype.ofFinite _
local instance : DecidableEq (Discriminant D) := Classical.decEq _

/-- The finite fusion algebra attached to the discriminant group. -/
abbrev FusionAlgebra := AddMonoidAlgebra ℂ (Discriminant D)

/-- The basis element indexed by a discriminant class. -/
def basis (a : Discriminant D) : FusionAlgebra D :=
  AddMonoidAlgebra.single a 1

@[simp]
theorem basis_mul (a b : Discriminant D) :
    basis D a * basis D b = basis D (a + b) := by
  simp [basis]

@[simp]
theorem basis_zero : basis D 0 = (1 : FusionAlgebra D) := by
  simp [basis, AddMonoidAlgebra.one_def]

theorem basis_mul_comm (a b : Discriminant D) :
    basis D a * basis D b = basis D b * basis D a := by
  simp [add_comm]

theorem basis_mul_assoc (a b c : Discriminant D) :
    (basis D a * basis D b) * basis D c =
      basis D a * (basis D b * basis D c) := by
  simp [add_assoc]

/-- The structure constants of the basis multiplication are the finite
Verlinde coefficients computed from the Weil `S`-kernel. -/
theorem basis_mul_coeff_eq_fusionCoefficient (a b c : Discriminant D) :
    (basis D a * basis D b).coeff c = fusionCoefficient D a b c := by
  rw [basis_mul]
  simp [basis, Finsupp.single_apply, fusionCoefficient_eq_indicator]

/-- The augmentation sends every basis element to `1`. -/
def augmentation : FusionAlgebra D →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ (Discriminant D)
    ({ toFun := fun _ : Multiplicative (Discriminant D) => (1 : ℂ)
       map_one' := by simp
       map_mul' := by intro _ _; simp } : Multiplicative (Discriminant D) →* ℂ)

@[simp]
theorem augmentation_basis (a : Discriminant D) :
    augmentation D (basis D a) = 1 := by
  simp [augmentation, basis]

end
end D5.S3.VertexAlgebra.LatticeDiscriminantFusionAlgebra
