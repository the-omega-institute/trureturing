/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldClosedRelativeKunneth
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldClosedRelativeKunneth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native double-relative BRST differential and Künneth cycle formula. -/

import D5.S3.HomologicalAlgebra.ParityOddKunneth
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTDescentJacobi

/-!
The two chiral factors each satisfy the original constraints `b₀ = L₀ = 0`.
The quotient is the cohomology of their tensor differential with its native
ghost-parity sign. The semirelative carrier uses difference zero modes on
the ambient closed complex and has separate comparison obligations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace D5.S3.VertexAlgebra.OriginalOrbifoldClosedRelativeKunneth

open D5.S3.HomologicalAlgebra
open OriginalOrbifoldCriticalMatter (Matter State Q)
open OriginalOrbifoldBRSTSignedLocality (parity)
open OriginalOrbifoldBRSTDescent
  (relativeStates relativeDifferential relativeDifferential_square
    relativeCycles relativeBoundaries RelativeCohomology)

open private parity_square Q_parity from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTDescent
open private relativeParity from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTDescentJacobi

noncomputable section

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

/-- Ghost parity restricted to the original relative carrier. -/
abbrev chiralParity : Module.End ℂ relativeStates := relativeParity

local notation "V" => relativeStates
local notation "d" => relativeDifferential
local notation "σ" => chiralParity

theorem relativeParity_val (x : V) : (σ x : State) = parity (x : State) := rfl

private theorem chiralParitySquare : σ * σ = 1 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change parity (parity (x : State)) = (x : State)
  exact parity_square _

/-- The restricted original charge is odd for the restricted ghost parity. -/
private theorem chiralDifferentialOdd : d * σ = -(σ * d) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change Q (parity (x : State)) = -parity (Q (x : State))
  exact Q_parity _

/-- The native chiral relative complex supplied to the shared Künneth construction. -/
def chiralComplex : ParityOddKunneth.OddDifferential V :=
  ⟨d, σ, relativeDifferential_square, chiralParitySquare, chiralDifferentialOdd⟩

abbrev ClosedRelativeState := V ⊗[ℂ] V

/-- The native double-relative charge `Q ⊗ 1 + σ ⊗ Q`. -/
abbrev closedDifferential : Module.End ℂ ClosedRelativeState :=
  ParityOddKunneth.closedDifferential chiralComplex chiralComplex

theorem closedDifferential_tmul (x y : V) :
    closedDifferential (x ⊗ₜ[ℂ] y) = d x ⊗ₜ[ℂ] y + σ x ⊗ₜ[ℂ] d y :=
  ParityOddKunneth.closedDifferential_tmul chiralComplex chiralComplex x y

abbrev ClosedRelativeCycles := ParityOddKunneth.closedCycles chiralComplex chiralComplex
abbrev closedRelativeBoundaries := ParityOddKunneth.closedBoundaries chiralComplex chiralComplex
abbrev ClosedRelativeCohomology := ParityOddKunneth.ClosedCohomology chiralComplex chiralComplex

/-- Tensoring two original chiral cycles gives a cycle of the native closed charge. -/
abbrev closedCycleTensor (x y : relativeCycles) : ClosedRelativeCycles :=
  ParityOddKunneth.cycleTensor chiralComplex chiralComplex x y

/-- Cross product from the two original chiral quotients to the original closed quotient. -/
def kunnethEquiv : (RelativeCohomology ⊗[ℂ] RelativeCohomology) ≃ₗ[ℂ] ClosedRelativeCohomology :=
  ParityOddKunneth.kunnethEquiv chiralComplex chiralComplex

/-- The cross product uses the tensor of the given representatives in the closed quotient. -/
theorem kunnethEquiv_classOf_tmul (x y : relativeCycles) :
    kunnethEquiv (relativeBoundaries.mkQ x ⊗ₜ[ℂ] relativeBoundaries.mkQ y) =
      closedRelativeBoundaries.mkQ (closedCycleTensor x y) :=
  ParityOddKunneth.kunnethEquiv_classOf_tmul chiralComplex chiralComplex x y

#print axioms relativeParity_val
#print axioms chiralComplex
#print axioms closedDifferential_tmul
#print axioms kunnethEquiv
#print axioms kunnethEquiv_classOf_tmul

end
end D5.S3.VertexAlgebra.OriginalOrbifoldClosedRelativeKunneth
