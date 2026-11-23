/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldFirstImaginary
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldFirstImaginary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Relative BRST multiplicity at the Leech orbifold's first imaginary momentum. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeCohomology
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldWeightTwo

/-! At plane momentum `(1, -1)`, relative ghost degree one reads out the actual
orbifold's weight-two space. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST

open ActualLeechOrbifoldCriticalMatter (hyperbolicPlane)
open ActualLeechOrbifoldMatter (mode)
open ActualLeechOrbifoldWeightTwo (weight_two_finrank)
open LatticeGeneratingFieldLocality (Charge)
open LatticePositiveEnergy (chargeEnergy)
open RelativeCohomology
  (OrbifoldWeight GradedCycles GradedCohomology GhostSpace ghostOneCohomologyEquivNonzero
    exact_of_degree_ne_one)

/-- The integer plane momentum `(1, -1)` in the ordered basis of `U`. -/
def firstImaginaryMomentum : Charge hyperbolicPlane :=
  Fin.cases 1 (fun _ => -1)

local instance (p : Charge hyperbolicPlane) : AddCommGroup (relativeShell p) :=
  Submodule.addCommGroup (relativeShell p)

local instance (g : ℤ) :
    AddCommGroup (GradedCycles planeFrame planeBasis firstImaginaryMomentum g) :=
  Submodule.addCommGroup (GradedCycles planeFrame planeBasis firstImaginaryMomentum g)

private theorem firstImaginaryMomentum_ne_zero : firstImaginaryMomentum ≠ 0 := by
  intro h
  exact Int.one_ne_zero (congrFun h (0 : Fin 2))

theorem first_imaginary_momentum_product :
    firstImaginaryMomentum (0 : Fin 2) * firstImaginaryMomentum (1 : Fin 2) = -1 := by
  change (1 : ℤ) * -1 = -1
  norm_num

theorem first_imaginary_charge_energy : chargeEnergy hyperbolicPlane firstImaginaryMomentum = -1 :=
  (plane_chargeEnergy firstImaginaryMomentum).trans first_imaginary_momentum_product

private theorem firstImaginaryWeight :
    OrbifoldWeight firstImaginaryMomentum = (mode 0).eigenspace (2 : ℂ) := by
  change (mode 0).eigenspace
    ((1 - firstImaginaryMomentum (0 : Fin 2) * firstImaginaryMomentum (1 : Fin 2) : ℤ) : ℂ) = _
  rw [← plane_chargeEnergy, first_imaginary_charge_energy]
  norm_num

/-- The actual relative degree-one quotient at `(1, -1)` is linearly
equivalent to the assembled orbifold's weight-two eigenspace. -/
def firstImaginaryGhostOneEquiv :
    GradedCohomology planeFrame planeBasis firstImaginaryMomentum 1 ≃ₗ[ℂ]
      (mode 0).eigenspace (2 : ℂ) :=
  (ghostOneCohomologyEquivNonzero firstImaginaryMomentum firstImaginaryMomentum_ne_zero).trans
    (LinearEquiv.ofEq _ _ firstImaginaryWeight)

instance firstImaginaryGhostOne_finite :
    FiniteDimensional ℂ (GradedCohomology planeFrame planeBasis firstImaginaryMomentum 1) :=
  Module.Finite.of_surjective firstImaginaryGhostOneEquiv.symm.toLinearMap
    firstImaginaryGhostOneEquiv.symm.surjective

theorem first_imaginary_ghost_one_finrank :
    Module.finrank ℂ (GradedCohomology planeFrame planeBasis firstImaginaryMomentum 1) = 196884 :=
  firstImaginaryGhostOneEquiv.finrank_eq.trans weight_two_finrank

/-- Every homogeneous cycle at this momentum outside ghost degree one has a
primitive in the same relative shell and in the preceding ghost degree. -/
theorem first_imaginary_exact_of_degree_ne_one (g : ℤ) (hg : g ≠ 1)
    (x : relativeShell firstImaginaryMomentum)
    (hx : x ∈ GhostSpace firstImaginaryMomentum g)
    (hc : relativeQ planeFrame planeBasis firstImaginaryMomentum x = 0) :
    ∃ y ∈ GhostSpace firstImaginaryMomentum (g - 1),
      relativeQ planeFrame planeBasis firstImaginaryMomentum y = x := by
  apply exact_of_degree_ne_one planeFrame planeBasis firstImaginaryMomentum _ g hg x hx hc
  rw [planeFrame_pPlus, show firstImaginaryMomentum (1 : Fin 2) = -1 from rfl]
  norm_num

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST
