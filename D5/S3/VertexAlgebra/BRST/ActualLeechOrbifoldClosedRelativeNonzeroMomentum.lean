/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldClosedRelativeNonzeroMomentum
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldClosedRelativeNonzeroMomentum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual graded closed double-relative BRST at two nonzero momenta. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldClosedRelativeBRST
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldClosedRelativeZeroMomentum

/-!
At independently specified nonzero momenta, the signed double-relative
complex has cohomology in total ghost degree two, with the native corrected
tensor representatives and the tensor of the two native chiral coefficients.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open scoped TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.ClosedRelative

open ActualLeechOrbifoldCriticalMatter (hyperbolicPlane)
open ActualLeechOrbifoldMatter (Orbifold)
open LatticeGeneratingFieldLocality (Charge)
open LatticeLightConeCoordinates (NullFrame)
open LatticeQuartetContraction (State)
open RelativeCohomology (OrbifoldWeight)

open private cycle_sub_rep from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldClosedRelativeBRST
open private gradedBoundaryMap from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldClosedRelativeZeroMomentum

local instance : AddCommGroup AssocState :=
  TensorProduct.addCommGroup (R := ℂ) (M := Orbifold) (N := State hyperbolicPlane)

local instance (p : Charge hyperbolicPlane) : AddCommGroup (relativeShell p) :=
  Submodule.addCommGroup _

local instance (p : Charge hyperbolicPlane) : AddCommGroup (OrbifoldWeight p) :=
  Submodule.addCommGroup (R := ℂ) (M := Orbifold) (OrbifoldWeight p)

local instance (p q : Charge hyperbolicPlane) : AddCommGroup (Shell p q) :=
  TensorProduct.addCommGroup (R := ℂ) (M := relativeShell p) (N := relativeShell q)

local instance (p q : Charge hyperbolicPlane) (g : ℤ) :
    AddCommGroup (GradedCycles p q g) := Submodule.addCommGroup _

variable (FL FR : NullFrame hyperbolicPlane)
variable (BL : Module.Basis (Fin 0) ℂ FL.K) (BR : Module.Basis (Fin 0) ℂ FR.K)
variable (pL pR : Charge hyperbolicPlane)
variable (hL : FL.pPlus pL ≠ 0) (hR : FR.pPlus pR ≠ 0)

/-- The actual corrected tensor inclusion takes values in the degree-two cycles. -/
def ghostTwoRepresentative : Physical pL pR →ₗ[ℂ] GradedCycles pL pR 2 :=
  (representative FL FR BL BR pL pR hL hR).codRestrict _ fun u =>
    Submodule.mem_inf.mpr ⟨representative_degree FL FR BL BR pL pR hL hR u,
      LinearMap.congr_fun (representative_chain FL FR BL BR pL pR hL hR) u⟩

/-- Read the actual tensor coefficient on the degree-two cycles. -/
def ghostTwoCoefficient : GradedCycles pL pR 2 →ₗ[ℂ] Physical pL pR :=
  (coefficient FL FR BL BR pL pR hL hR).comp (GradedCycles pL pR 2).subtype

private theorem ghostTwoCoefficient_representative (u : Physical pL pR) :
    ghostTwoCoefficient FL FR BL BR pL pR hL hR
      (ghostTwoRepresentative FL FR BL BR pL pR hL hR u) = u :=
  LinearMap.congr_fun (coefficient_representative FL FR BL BR pL pR hL hR) u

/-- The kernel of the degree-two coefficient is exactly the image of the
actual differential from total ghost degree one. -/
theorem ghostTwoBoundaries_eq_ker :
    GradedBoundaries pL pR 2 =
      LinearMap.ker (ghostTwoCoefficient FL FR BL BR pL pR hL hR) := by
  ext x
  change (∃ y : TotalGhostSpace pL pR ((2 : ℤ) - 1), gradedBoundaryMap pL pR 2 y = x) ↔
    coefficient FL FR BL BR pL pR hL hR x.val = 0
  constructor
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun (coefficient_chain FL FR BL BR pL pR hL hR) y.val
  · intro hx
    have hy : primitive FL FR BL BR pL pR hL hR x.val ∈
        TotalGhostSpace pL pR 1 :=
      primitive_degree FL FR BL BR pL pR hL hR 2 x.val x.property.1
    refine ⟨⟨primitive FL FR BL BR pL pR hL hR x.val, hy⟩, Subtype.ext ?_⟩
    change differential pL pR (primitive FL FR BL BR pL pR hL hR x.val) = x.val
    rw [cycle_sub_rep FL FR BL BR pL pR hL hR x.val x.property.2, hx, map_zero, sub_zero]

/-- In total degree two the literal graded quotient is the tensor of the
two native orbifold weight spaces. -/
def ghostTwoCohomologyEquiv : GradedCohomology pL pR 2 ≃ₗ[ℂ] Physical pL pR := by
  let f := ghostTwoCoefficient FL FR BL BR pL pR hL hR
  have hs : Function.Surjective f := fun u =>
    ⟨ghostTwoRepresentative FL FR BL BR pL pR hL hR u,
      ghostTwoCoefficient_representative FL FR BL BR pL pR hL hR u⟩
  exact ((GradedBoundaries pL pR 2).quotEquivOfEq (LinearMap.ker f)
    (ghostTwoBoundaries_eq_ker FL FR BL BR pL pR hL hR)).trans
    (f.quotKerEquivOfSurjective hs)

/-- On every actual degree-two cycle the quotient equivalence reads the tensor coefficient. -/
theorem ghostTwoCohomologyEquiv_mk (x : GradedCycles pL pR 2) :
    ghostTwoCohomologyEquiv FL FR BL BR pL pR hL hR (Submodule.Quotient.mk x) =
      coefficient FL FR BL BR pL pR hL hR x.val := rfl

/-- The inverse class is represented by the actual tensor inclusion of the two native spaces. -/
theorem ghostTwoCohomologyEquiv_symm_apply (u : Physical pL pR) :
    (ghostTwoCohomologyEquiv FL FR BL BR pL pR hL hR).symm u =
      Submodule.Quotient.mk ⟨representative FL FR BL BR pL pR hL hR u,
        Submodule.mem_inf.mpr ⟨representative_degree FL FR BL BR pL pR hL hR u,
          LinearMap.congr_fun (representative_chain FL FR BL BR pL pR hL hR) u⟩⟩ := by
  apply (ghostTwoCohomologyEquiv FL FR BL BR pL pR hL hR).injective
  rw [LinearEquiv.apply_symm_apply, ghostTwoCohomologyEquiv_mk]
  exact (LinearMap.congr_fun (coefficient_representative FL FR BL BR pL pR hL hR) u).symm

include FL FR BL BR hL hR in
/-- Every off-degree-two class is zero by an actual primitive in the preceding degree. -/
theorem gradedCohomology_vanishes (g : ℤ) (hg : g ≠ 2) :
    Subsingleton (GradedCohomology pL pR g) := by
  have hzero (z : GradedCohomology pL pR g) : z = 0 := by
    refine Submodule.Quotient.induction_on _ z (fun x => ?_)
    apply (Submodule.Quotient.mk_eq_zero (GradedBoundaries pL pR g)).mpr
    obtain ⟨y, hy, he⟩ := exact_of_degree_ne_two FL FR BL BR pL pR hL hR g hg
      x.val x.property.1 x.property.2
    exact LinearMap.mem_range.mpr ⟨⟨y, hy⟩, Subtype.ext he⟩
  exact ⟨fun z w => (hzero z).trans (hzero w).symm⟩

/-- Degree two at every pair of nonzero momenta, using an independent native
or swapped light-cone polarization for each chirality. -/
def ghostTwoCohomologyEquivNonzero (hpL : pL ≠ 0) (hpR : pR ≠ 0) :
    GradedCohomology pL pR 2 ≃ₗ[ℂ] Physical pL pR := by
  by_cases left : planeFrame.pPlus pL ≠ 0
  · by_cases right : planeFrame.pPlus pR ≠ 0
    · exact ghostTwoCohomologyEquiv planeFrame planeFrame planeBasis planeBasis pL pR left right
    · exact ghostTwoCohomologyEquiv planeFrame swappedPlaneFrame planeBasis swappedPlaneBasis
        pL pR left ((planeFrame_covers_nonzero pR hpR).resolve_left right)
  · have left' := (planeFrame_covers_nonzero pL hpL).resolve_left left
    by_cases right : planeFrame.pPlus pR ≠ 0
    · exact ghostTwoCohomologyEquiv swappedPlaneFrame planeFrame swappedPlaneBasis planeBasis
        pL pR left' right
    · exact ghostTwoCohomologyEquiv swappedPlaneFrame swappedPlaneFrame swappedPlaneBasis
        swappedPlaneBasis pL pR left' ((planeFrame_covers_nonzero pR hpR).resolve_left right)

/-- All other degrees vanish at every pair of nonzero momenta. -/
theorem gradedCohomology_vanishes_nonzero (hpL : pL ≠ 0) (hpR : pR ≠ 0)
    (g : ℤ) (hg : g ≠ 2) : Subsingleton (GradedCohomology pL pR g) := by
  rcases planeFrame_covers_nonzero pL hpL with left | left <;>
    rcases planeFrame_covers_nonzero pR hpR with right | right
  · exact gradedCohomology_vanishes planeFrame planeFrame planeBasis planeBasis pL pR left right g hg
  · exact gradedCohomology_vanishes planeFrame swappedPlaneFrame planeBasis swappedPlaneBasis
      pL pR left right g hg
  · exact gradedCohomology_vanishes swappedPlaneFrame planeFrame swappedPlaneBasis planeBasis
      pL pR left right g hg
  · exact gradedCohomology_vanishes swappedPlaneFrame swappedPlaneFrame swappedPlaneBasis
      swappedPlaneBasis pL pR left right g hg

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.ClosedRelative
