/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTPhysicalPairing
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTPhysicalPairing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Quotient.Bilinear]
   utility: none
   digest: The native inserted BPZ form descends to relative cohomology and physical degree one. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTBPZWard
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTMomentum
import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
The relative Ward identity and ghost parity descend the inserted BPZ form
through both arguments of the actual relative quotient. The restriction to
physical degree one pairs only opposite hyperbolic momenta.

Nondegeneracy requires identifying both cycle radicals with the boundary
image. For the physical restriction, both radicals are tested on
ghost-number-one cycles and compared with the boundaries of that ghost number.
Lie invariance requires the cyclic identity for the native descent bracket
against degree-one cycles with the zero mode inserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTPhysicalPairing

open D5.S3.HomologicalAlgebra.FinitePerturbation (boundaryMap)
open D5.S3.Quantum.Fermionic
open OriginalOrbifoldCriticalMatter (Matter State Q hyperbolicData matterDatum)
open OriginalOrbifoldBRSTSignedLocality (parity)
open OriginalOrbifoldBRSTDescent (relativeStates relativeDifferential relativeDifferential_square
  relativeCycles relativeBoundaries RelativeCohomology)
open OriginalOrbifoldBRSTBPZWard (betaTotal betaRelTotal betaRelTotal_ward parityRelative)
open OriginalOrbifoldBRSTPhysicalLie (DegreeOne grade)
open OriginalOrbifoldBRSTMomentum (relativeMomentum physicalMomentum mem_relativeMomentum_iff)
open OriginalOrbifoldBRSTZeroEnergy (FullLabel fullBasis)
open OriginalOrbifoldRelativeMassShell (fixedMomentum)
open OriginalOrbifoldMatterBPZ (matterBPZ_charge)
open LatticeGeneratingFieldLocality (Charge)

open private Q_parity parity_square cycle_closed from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTDescent
open private fullBasis_apply fixedMomentum_eq_span from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeMassShell

noncomputable section

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

/-- The inserted relative form vanishes on a boundary paired with a cycle. -/
theorem betaRelTotal_left_boundary (x y : relativeCycles) (hx : x ∈ relativeBoundaries) :
    betaRelTotal (x : relativeStates) (y : relativeStates) = 0 := by
  change ∃ u : relativeStates, boundaryMap relativeDifferential relativeDifferential_square u = x
    at hx
  obtain ⟨u, rfl⟩ := hx
  have hy : relativeDifferential (y : relativeStates) = 0 := LinearMap.mem_ker.mp y.property
  change betaRelTotal (relativeDifferential u) (y : relativeStates) = 0
  rw [betaRelTotal_ward, hy, map_zero]

/-- Relative parity allows the same Ward identity to annihilate a right boundary. -/
theorem betaRelTotal_right_boundary (x y : relativeCycles) (hy : y ∈ relativeBoundaries) :
    betaRelTotal (x : relativeStates) (y : relativeStates) = 0 := by
  change ∃ u : relativeStates, boundaryMap relativeDifferential relativeDifferential_square u = y
    at hy
  obtain ⟨u, rfl⟩ := hy
  have hQ : relativeDifferential (parityRelative (x : relativeStates)) = 0 := by
    apply Subtype.ext
    change Q (parity (x.1 : State)) = 0
    rw [Q_parity, cycle_closed x, map_zero, neg_zero]
  have hp : parityRelative (parityRelative (x : relativeStates)) = (x : relativeStates) :=
    Subtype.ext (parity_square (x.1 : State))
  have h := betaRelTotal_ward (parityRelative (x : relativeStates)) u
  change betaRelTotal (x : relativeStates) (relativeDifferential u) = 0
  simpa only [hQ, hp, map_zero, LinearMap.zero_apply] using h.symm

private def cycleBPZ : LinearMap.BilinForm ℂ relativeCycles :=
  betaRelTotal.compl₁₂ relativeCycles.subtype relativeCycles.subtype

/-- The inserted BPZ form on the full native relative BRST cohomology. -/
def cohomologyBPZ : LinearMap.BilinForm ℂ RelativeCohomology :=
  cycleBPZ.liftQ₂ relativeBoundaries relativeBoundaries
    (by
      intro x hx
      apply LinearMap.mem_ker.mpr
      apply LinearMap.ext
      intro y
      exact betaRelTotal_left_boundary x y hx)
    (by
      intro y hy
      apply LinearMap.mem_ker.mpr
      apply LinearMap.ext
      intro x
      exact betaRelTotal_right_boundary x y hy)

/-- Evaluate the quotient form on the original relative representatives. -/
theorem cohomologyBPZ_mk (x y : relativeCycles) :
    cohomologyBPZ (relativeBoundaries.mkQ x) (relativeBoundaries.mkQ y) =
      betaRelTotal (x : relativeStates) (y : relativeStates) := rfl

/-- The restriction of the quotient form to the native physical Lie algebra. -/
def physicalBPZ : LinearMap.BilinForm ℂ DegreeOne :=
  cohomologyBPZ.compl₁₂ (grade 1).subtype (grade 1).subtype

/-- Evaluate the physical form using any cycles representing the two degree-one classes. -/
theorem physicalBPZ_representatives (a b : DegreeOne) (x y : relativeCycles)
    (hx : relativeBoundaries.mkQ x = (a : RelativeCohomology))
    (hy : relativeBoundaries.mkQ y = (b : RelativeCohomology)) :
    physicalBPZ a b = betaRelTotal (x : relativeStates) (y : relativeStates) := by
  change cohomologyBPZ (a : RelativeCohomology) (b : RelativeCohomology) = _
  rw [← hx, ← hy, cohomologyBPZ_mk]

private theorem insertedBPZ_basis_eq_zero (i j : FullLabel) (hne : j.2.1.1 ≠ -i.2.1.1) :
    betaTotal (fullBasis i) (VirasoroBRST.ghostC matterDatum 0 (fullBasis j)) = 0 := by
  classical
  simp only [fullBasis_apply, VirasoroBRST.ghostC, BcGhostChargeTensor.C,
    BcGhostChargeTensor.liftGhost, TensorProduct.map_tmul, LinearMap.id_apply,
    betaTotal, LinearMap.BilinForm.tensorDistrib_tmul, matterBPZ_charge,
    ite_eq_right hne, smul_zero]

private theorem betaRelTotal_eq_zero_of_momentum
    {p q : Charge hyperbolicData} {x y : relativeStates} (hne : q ≠ -p)
    (hx : (x : State) ∈ fixedMomentum p) (hy : (y : State) ∈ fixedMomentum q) :
    betaRelTotal x y = 0 := by
  let B : LinearMap.BilinForm ℂ State := betaTotal.compl₂ (VirasoroBRST.ghostC matterDatum 0)
  change B (x : State) (y : State) = 0
  rw [fixedMomentum_eq_span] at hx hy
  refine (Submodule.mem_bot ℂ).mp (LinearMap.BilinMap.apply_apply_mem_of_mem_span
    (⊥ : Submodule ℂ ℂ) (fullBasis '' {i : FullLabel | i.2.1.1 = p})
    (fullBasis '' {j : FullLabel | j.2.1.1 = q}) B (by
      rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
      change i.2.1.1 = p at hi
      change j.2.1.1 = q at hj
      exact (Submodule.mem_bot ℂ).mpr
        (insertedBPZ_basis_eq_zero i j (by simpa only [hi, hj] using hne)))
    (x : State) (y : State) hx hy)

/-- Relative cohomology components are orthogonal unless their momenta are opposite. -/
theorem cohomologyBPZ_eq_zero_of_momentum
    {p q : Charge hyperbolicData} {x y : RelativeCohomology} (hne : q ≠ -p)
    (hx : x ∈ relativeMomentum p) (hy : y ∈ relativeMomentum q) :
    cohomologyBPZ x y = 0 := by
  obtain ⟨u, hu, hup⟩ := (mem_relativeMomentum_iff p x).mp hx
  obtain ⟨v, hv, hvq⟩ := (mem_relativeMomentum_iff q y).mp hy
  rw [← hu, ← hv, cohomologyBPZ_mk]
  exact betaRelTotal_eq_zero_of_momentum hne hup hvq

/-- Physical momentum components are orthogonal unless their momenta are opposite. -/
theorem physicalBPZ_eq_zero_of_momentum
    {p q : Charge hyperbolicData} {x y : DegreeOne} (hne : q ≠ -p)
    (hx : x ∈ physicalMomentum p) (hy : y ∈ physicalMomentum q) :
    physicalBPZ x y = 0 := by
  change (x : RelativeCohomology) ∈ relativeMomentum p at hx
  change (y : RelativeCohomology) ∈ relativeMomentum q at hy
  change cohomologyBPZ (x : RelativeCohomology) (y : RelativeCohomology) = 0
  exact cohomologyBPZ_eq_zero_of_momentum hne hx hy

#print axioms betaRelTotal_left_boundary
#print axioms betaRelTotal_right_boundary
#print axioms cohomologyBPZ
#print axioms cohomologyBPZ_mk
#print axioms physicalBPZ
#print axioms physicalBPZ_representatives
#print axioms cohomologyBPZ_eq_zero_of_momentum
#print axioms physicalBPZ_eq_zero_of_momentum

end
end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTPhysicalPairing
