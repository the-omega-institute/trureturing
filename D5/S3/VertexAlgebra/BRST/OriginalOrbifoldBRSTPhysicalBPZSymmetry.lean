/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTPhysicalBPZSymmetry
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTPhysicalBPZSymmetry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.BilinearForm.TensorProduct]
   utility: none
   digest: Native inserted BPZ symmetry on degree-one relative cochains and physical classes. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTBPZGhostNumber

/-! At ghost number one the phase is constant on the left ghost input. The
inserted ghost BPZ pairing on that degree is therefore a common scalar times
the symmetric native relative ghost pairing. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTPhysicalBPZSymmetry

open D5.S3.Quantum.Fermionic
open CountableOccupationFock (Fock ket)
open BcGhostCharge (charge)
open BcGhostHermitian (Homogeneous Relative relativeKet)
open OriginalOrbifoldCriticalMatter (Matter State hyperbolicData matterDatum)
open OriginalOrbifoldMatterBPZ (orbifoldBPZ fixedBPZ negativeBPZ hyperbolicBPZ matterBPZ
  fixedBPZ_symmetric negativeBPZ_symmetric)
open SourceBPZ.OriginalSourcePairing (sourcePairing_symmetric)
open OriginalOrbifoldBRSTGhostBilinear (Brel Brel_apply Brel_symm)
open OriginalOrbifoldBRSTGhostBPZ (beta betaRel betaRel_apply beta_of_homogeneous bpzPhase)
open OriginalOrbifoldBRSTDescent (relativeStates relativeCycles relativeBoundaries
  RelativeCohomology)
open OriginalOrbifoldBRSTZeroEnergy (FullLabel fullBasis)
open OriginalOrbifoldBRSTBPZWard (betaTotal betaRelTotal)
open OriginalOrbifoldBRSTPhysicalLie (DegreeOne N grade homogeneous_cycle_lift)
open OriginalOrbifoldBRSTPhysicalPairing (physicalBPZ physicalBPZ_representatives)

open private fullBasis_apply from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTZeroEnergy
open private betaTotal_tmul ket_homogeneous b_zero_of_relative from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTBPZWard
open private b_zero_iff from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeMassShell
open private mem_span_of_number from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTBPZGhostNumber

noncomputable section

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private theorem matterBPZ_symmetric : matterBPZ.IsSymm := by
  have horbifold : orbifoldBPZ.IsSymm := by
    constructor
    intro x y
    change fixedBPZ x.1 y.1 + negativeBPZ x.2 y.2 =
      fixedBPZ y.1 x.1 + negativeBPZ y.2 x.2
    rw [fixedBPZ_symmetric.eq x.1 y.1, negativeBPZ_symmetric.eq x.2 y.2]
  have hhyperbolic : hyperbolicBPZ.IsSymm := ⟨sourcePairing_symmetric hyperbolicData⟩
  exact LinearMap.BilinForm.isSymm_iff.mpr
    (LinearMap.IsSymm.tmul (LinearMap.BilinForm.isSymm_iff.mp horbifold)
      (LinearMap.BilinForm.isSymm_iff.mp hhyperbolic))

private theorem betaRel_of_number_one (x y : Relative) (hx : Homogeneous 1 (x : Fock)) :
    betaRel x y = bpzPhase 1 * Brel x y := by
  rw [betaRel_apply, Brel_apply, beta_of_homogeneous hx]

private theorem insertedGhostBPZ_symm {S T : Finset ℕ}
    (hS : charge S = 1) (hT : charge T = 1) (hSrel : 3 ∉ S) (hTrel : 3 ∉ T) :
    beta (ket S) (BcGhostFock.c 0 (ket T)) = beta (ket T) (BcGhostFock.c 0 (ket S)) := by
  let x := relativeKet S hSrel
  let y := relativeKet T hTrel
  have hx : Homogeneous 1 (x : Fock) := by
    change Homogeneous 1 (ket S)
    simpa only [hS] using ket_homogeneous S
  have hy : Homogeneous 1 (y : Fock) := by
    change Homogeneous 1 (ket T)
    simpa only [hT] using ket_homogeneous T
  change beta (x : Fock) (BcGhostFock.c 0 (y : Fock)) =
    beta (y : Fock) (BcGhostFock.c 0 (x : Fock))
  rw [← betaRel_apply x y, ← betaRel_apply y x, betaRel_of_number_one x y hx,
    betaRel_of_number_one y x hy, Brel_symm x y]

private def degreeOneRelativeLabels : Set FullLabel :=
  {i | charge i.2.2 = 1 ∧ 3 ∉ i.2.2}

private theorem mem_span_degreeOneRelativeLabels (x : relativeStates) (hx : N (x : State) = x) :
    (x : State) ∈ Submodule.span ℂ (fullBasis '' degreeOneRelativeLabels) := by
  have hnumber := fullBasis.mem_span_image.mp
    (mem_span_of_number (r := 1) (x := (x : State)) (by
      simpa only [Int.cast_one, one_smul] using hx))
  have hb := (b_zero_iff (x : State)).mp (b_zero_of_relative x)
  apply fullBasis.mem_span_image.mpr
  intro i hi
  exact ⟨hnumber hi, fun h => (Finsupp.mem_support_iff.mp hi) (hb i h)⟩

private theorem insertedBPZ_basis_symm (i j : FullLabel)
    (hi : i ∈ degreeOneRelativeLabels) (hj : j ∈ degreeOneRelativeLabels) :
    betaTotal (fullBasis i) (VirasoroBRST.ghostC matterDatum 0 (fullBasis j)) =
      betaTotal (fullBasis j) (VirasoroBRST.ghostC matterDatum 0 (fullBasis i)) := by
  simp only [fullBasis_apply, VirasoroBRST.ghostC, BcGhostChargeTensor.C,
    BcGhostChargeTensor.liftGhost, TensorProduct.map_tmul, LinearMap.id_apply, betaTotal_tmul]
  exact congrArg₂ (· * ·) (matterBPZ_symmetric.eq _ _)
    (insertedGhostBPZ_symm hi.1 hj.1 hi.2 hj.2)

/-- The native inserted relative BPZ form is symmetric on all ghost-number-one cochains. -/
theorem betaRelTotal_symmetric_of_number_one (x y : relativeStates)
    (hx : N (x : State) = x) (hy : N (y : State) = y) :
    betaRelTotal x y = betaRelTotal y x := by
  let B : LinearMap.BilinForm ℂ State := betaTotal.compl₂ (VirasoroBRST.ghostC matterDatum 0)
  have hzero : (B - B.flip) (x : State) (y : State) = 0 := by
    refine (Submodule.mem_bot ℂ).mp (LinearMap.BilinMap.apply_apply_mem_of_mem_span
      (⊥ : Submodule ℂ ℂ) (fullBasis '' degreeOneRelativeLabels)
      (fullBasis '' degreeOneRelativeLabels) (B - B.flip) ?_ (x : State) (y : State)
      (mem_span_degreeOneRelativeLabels x hx) (mem_span_degreeOneRelativeLabels y hy))
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    apply (Submodule.mem_bot ℂ).mpr
    change B (fullBasis i) (fullBasis j) - B (fullBasis j) (fullBasis i) = 0
    exact sub_eq_zero.mpr (insertedBPZ_basis_symm i j hi hj)
  change B (x : State) (y : State) = B (y : State) (x : State)
  change B (x : State) (y : State) - B (y : State) (x : State) = 0 at hzero
  exact sub_eq_zero.mp hzero

/-- The BPZ form on the native physical Lie algebra is symmetric. -/
theorem physicalBPZ_symmetric : physicalBPZ.IsSymm := by
  have lift (c : DegreeOne) : ∃ z : relativeCycles,
      relativeBoundaries.mkQ z = (c : RelativeCohomology) ∧
        N (z.1 : State) = (z.1 : State) := by
    have hc : (c : RelativeCohomology) ∈ grade 1 := c.property
    simpa only [Int.cast_one, one_smul] using homogeneous_cycle_lift 1 (c : RelativeCohomology) hc
  exact ⟨fun (a b : DegreeOne) =>
    (lift a).elim fun (x : relativeCycles) hx =>
      (lift b).elim fun (y : relativeCycles) hy =>
        calc
          physicalBPZ a b = betaRelTotal (x : relativeStates) (y : relativeStates) :=
            physicalBPZ_representatives a b x y hx.1 hy.1
          _ = betaRelTotal (y : relativeStates) (x : relativeStates) :=
            betaRelTotal_symmetric_of_number_one (x : relativeStates) (y : relativeStates)
              hx.2 hy.2
          _ = physicalBPZ b a := (physicalBPZ_representatives b a y x hy.1 hx.1).symm⟩

#print axioms betaRelTotal_symmetric_of_number_one
#print axioms physicalBPZ_symmetric

end
end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTPhysicalBPZSymmetry
