/- GID: D5/S3/Constants/IcosahedralGeometry/ProjectiveAxisDecompositionAxisClasses
   generality: I
   mirror-B: D5/B/S3/Constants/IcosahedralGeometry/ProjectiveAxisDecompositionAxisClasses
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The invariant quadratic form defines the three chart classes and five-cycle subgroups. -/

import D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecompositionMatrixAction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecomposition

/-- The explicit matrix of the invariant quadratic form from the source. -/
def formMatrix : Matrix (Fin 3) (Fin 3) F5 :=
  ![![2, 1, 1], ![1, 2, 1], ![1, 1, 2]]

def chartQuadraticForm (p : AxisChart) : F5 :=
  dotProduct (axisVector p) (formMatrix.mulVec (axisVector p))

def chartFivefoldAxes : Finset AxisChart :=
  Finset.univ.filter fun p => chartQuadraticForm p = 0

def chartThreefoldAxes : Finset AxisChart :=
  Finset.univ.filter fun p => chartQuadraticForm p = 2 ∨ chartQuadraticForm p = 3

def chartTwofoldAxes : Finset AxisChart :=
  Finset.univ.filter fun p => chartQuadraticForm p = 1 ∨ chartQuadraticForm p = 4

abbrev ChartFivefoldAxis := chartFivefoldAxes

def chartAxisOrbit (p : AxisChart) : Finset AxisChart :=
  Finset.univ.image fun g : IcosahedralGroup => g • p

set_option maxHeartbeats 4000000 in
-- This finite check enumerates the fivefold stabilizers in the 60-element group.
set_option maxRecDepth 100000 in
private theorem chartFiveCycle_mul_closed :
    ∀ p : ChartFivefoldAxis, ∀ g h : IcosahedralGroup,
      (g • p.1 = p.1 ∧ g ^ 5 = 1) → (h • p.1 = p.1 ∧ h ^ 5 = 1) →
        (g * h) • p.1 = p.1 ∧ (g * h) ^ 5 = 1 := by
  decide

set_option maxHeartbeats 4000000 in
-- This finite check enumerates inverses in the fivefold stabilizers.
set_option maxRecDepth 100000 in
private theorem chartFiveCycle_inv_closed :
    ∀ p : ChartFivefoldAxis, ∀ g : IcosahedralGroup,
      (g • p.1 = p.1 ∧ g ^ 5 = 1) → g⁻¹ • p.1 = p.1 ∧ g⁻¹ ^ 5 = 1 := by
  decide

def chartFiveCycleSubgroup (p : ChartFivefoldAxis) : Subgroup IcosahedralGroup where
  carrier := {g | g • p.1 = p.1 ∧ g ^ 5 = 1}
  one_mem' := by
    constructor
    · exact one_smul IcosahedralGroup p.1
    · exact one_pow 5
  mul_mem' := by
    intro g h hg hh
    exact chartFiveCycle_mul_closed p g h hg hh
  inv_mem' := by
    intro g hg
    exact chartFiveCycle_inv_closed p g hg

instance (p : ChartFivefoldAxis) : DecidablePred (· ∈ chartFiveCycleSubgroup p) := by
  intro g
  change Decidable (g • p.1 = p.1 ∧ g ^ 5 = 1)
  infer_instance

end D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecomposition
