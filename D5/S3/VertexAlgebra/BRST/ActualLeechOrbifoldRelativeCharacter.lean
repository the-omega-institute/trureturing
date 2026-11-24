/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeCharacter
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeCharacter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Character formulas for the nonzero relative ghost-one multiplicities. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeCohomology
import D5.S3.VertexAlgebra.Characters.ActualLeechOrbifoldMoonshineCharacter

/-! The actual relative cohomology equivalence transports the literal weight
dimension and its moonshine recursion to nonzero plane charge. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open UpperHalfPlane (qExpansion)

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeCohomology

open ActualLeechOrbifoldCriticalMatter (hyperbolicPlane)
open LatticeGeneratingFieldLocality (Charge)
open ActualLeechOrbifoldAllWeightDimension (weightMultiplicity weight_finrank)
open ActualLeechOrbifoldTraceSeries (dimension)
open ActualLeechOrbifoldMoonshineCharacter (normalizedNumerator dimension_recursion)

local notation "Δ" => ModularForm.discriminant

local instance (p : Charge hyperbolicPlane) : AddCommGroup (relativeShell p) :=
  Submodule.addCommGroup (relativeShell p)

local instance (p : Charge hyperbolicPlane) :
    AddCommGroup (GradedCycles planeFrame planeBasis p 1) :=
  Submodule.addCommGroup (GradedCycles planeFrame planeBasis p 1)

set_option maxRecDepth 4096 in
/-- At nonzero plane charge the native relative ghost-one quotient has the
orbifold multiplicity at the conformal weight selected by the charge. -/
theorem ghost_one_finrank_nonzero (p : Charge hyperbolicPlane) (hp : p ≠ 0) :
    (Module.finrank ℂ (GradedCohomology planeFrame planeBasis p 1) : ℂ) =
      weightMultiplicity (1 - p (0 : Fin 2) * p (1 : Fin 2)) := by
  rw [(ghostOneCohomologyEquivNonzero p hp).finrank_eq]
  exact weight_finrank (1 - p (0 : Fin 2) * p (1 : Fin 2))

set_option maxHeartbeats 1200000 in
/-- At nonzero plane momentum the recursion reads the coefficient with Laurent
index minus the product of the two charge coordinates. -/
theorem ghost_one_finrank_nonzero_moonshine (p : Charge hyperbolicPlane) (hp : p ≠ 0) :
    let n : ℤ := 1 - p (0 : Fin 2) * p (1 : Fin 2)
    (Module.finrank ℂ (GradedCohomology planeFrame planeBasis p 1) : ℂ) =
      if 0 ≤ n then
        (qExpansion 1 normalizedNumerator).coeff n.toNat -
          ∑ k ∈ Finset.range n.toNat,
            (dimension k : ℂ) * (qExpansion 1 Δ).coeff (n.toNat - k + 1)
      else 0 := by
  dsimp only
  rw [(ghostOneCohomologyEquivNonzero p hp).finrank_eq]
  let n : ℤ := 1 - p (0 : Fin 2) * p (1 : Fin 2)
  change (dimension n : ℂ) =
    if 0 ≤ n then
      (qExpansion 1 normalizedNumerator).coeff n.toNat -
        ∑ k ∈ Finset.range n.toNat,
          (dimension k : ℂ) * (qExpansion 1 Δ).coeff (n.toNat - k + 1)
    else 0
  by_cases hn : 0 ≤ n
  · rw [ite_eq_left hn]
    have h := dimension_recursion n.toNat
    rw [Int.toNat_of_nonneg hn] at h
    exact h
  · rw [ite_eq_right hn, ActualLeechOrbifoldMoonshineCharacter.dimension_eq_zero_of_neg n
      (lt_of_not_ge hn), Nat.cast_zero]

#print axioms ghost_one_finrank_nonzero
#print axioms ghost_one_finrank_nonzero_moonshine

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeCohomology
