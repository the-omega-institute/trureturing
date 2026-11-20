/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTBPZGhostNumber
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTBPZGhostNumber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Basis.Basic]
   utility: none
   digest: The native relative BRST BPZ pairing and its cohomology descent have total ghost number two. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTPhysicalPairing

/-! The right `c₀` insertion raises ghost number by one. The absolute BPZ
selection rule on the ghost factor thus gives relative orthogonality at
ghost-number sums other than two, also after passing to cohomology. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTBPZGhostNumber

open D5.S3.Quantum.Fermionic
open CountableOccupationFock (ket)
open BcGhostCharge (charge)
open BcGhostHermitian (homogeneous_c_zero)
open OriginalOrbifoldCriticalMatter (Matter State matterDatum)
open OriginalOrbifoldBRSTDescent (relativeStates relativeBoundaries RelativeCohomology)
open OriginalOrbifoldBRSTZeroEnergy (FullLabel fullBasis)
open OriginalOrbifoldBRSTGhostBPZ (beta beta_charge_selection)
open OriginalOrbifoldBRSTBPZWard (betaTotal betaRelTotal)
open OriginalOrbifoldBRSTPhysicalLie (N grade homogeneous_cycle_lift)
open OriginalOrbifoldBRSTPhysicalPairing (cohomologyBPZ cohomologyBPZ_mk)

open private fullBasis_apply from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTZeroEnergy
open private betaTotal_tmul ket_homogeneous from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTBPZWard
open private number_coordinate from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTPhysicalLie

noncomputable section

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private theorem mem_span_of_number {r : ℤ} {x : State} (hx : N x = (r : ℂ) • x) :
    x ∈ Submodule.span ℂ (fullBasis '' {i : FullLabel | charge i.2.2 = r}) := by
  apply fullBasis.mem_span_image.mpr
  intro i hi
  change charge i.2.2 = r
  have hnonzero : fullBasis.repr x i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have h : fullBasis.repr (N x) i = fullBasis.repr ((r : ℂ) • x) i :=
    congrArg (fun y : State => fullBasis.repr y i) hx
  rw [number_coordinate, map_smul, Finsupp.smul_apply, smul_eq_mul] at h
  have hz : ((charge i.2.2 : ℂ) - (r : ℂ)) * fullBasis.repr x i = 0 := by
    rw [sub_mul, h, sub_self]
  exact Int.cast_injective (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hnonzero))

private theorem insertedBPZ_basis_eq_zero (i j : FullLabel)
    (hne : charge i.2.2 + charge j.2.2 ≠ 2) :
    betaTotal (fullBasis i) (VirasoroBRST.ghostC matterDatum 0 (fullBasis j)) = 0 := by
  have hghost : beta (ket i.2.2) (BcGhostFock.c 0 (ket j.2.2)) = 0 :=
    beta_charge_selection (ket_homogeneous i.2.2)
      (homogeneous_c_zero _ _ (ket_homogeneous j.2.2)) (by omega)
  simp only [fullBasis_apply, VirasoroBRST.ghostC, BcGhostChargeTensor.C,
    BcGhostChargeTensor.liftGhost, TensorProduct.map_tmul, LinearMap.id_apply,
    betaTotal_tmul, hghost, mul_zero]

/-- Native relative eigenstates are BPZ orthogonal unless their ghost numbers sum to two. -/
theorem betaRelTotal_eq_zero_of_ghost_number
    {r s : ℤ} {x y : relativeStates} (hne : r + s ≠ 2)
    (hx : N (x : State) = (r : ℂ) • (x : State))
    (hy : N (y : State) = (s : ℂ) • (y : State)) :
    betaRelTotal x y = 0 := by
  let B : LinearMap.BilinForm ℂ State := betaTotal.compl₂ (VirasoroBRST.ghostC matterDatum 0)
  change B (x : State) (y : State) = 0
  refine (Submodule.mem_bot ℂ).mp (LinearMap.BilinMap.apply_apply_mem_of_mem_span
    (⊥ : Submodule ℂ ℂ) (fullBasis '' {i : FullLabel | charge i.2.2 = r})
    (fullBasis '' {j : FullLabel | charge j.2.2 = s}) B (by
      rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
      change charge i.2.2 = r at hi
      change charge j.2.2 = s at hj
      exact (Submodule.mem_bot ℂ).mpr
        (insertedBPZ_basis_eq_zero i j (by simpa only [hi, hj] using hne)))
    (x : State) (y : State) (mem_span_of_number hx) (mem_span_of_number hy))

/-- The descended BPZ form pairs each relative cohomology grade only with its complementary
grade. In particular, the physical grade one is orthogonal in both arguments to every other
integer grade. -/
theorem cohomologyBPZ_eq_zero_of_ghost_number
    {r s : ℤ} {x y : RelativeCohomology} (hne : r + s ≠ 2)
    (hx : x ∈ grade r) (hy : y ∈ grade s) :
    cohomologyBPZ x y = 0 := by
  obtain ⟨u, hu, hun⟩ := homogeneous_cycle_lift r x hx
  obtain ⟨v, hv, hvn⟩ := homogeneous_cycle_lift s y hy
  rw [← hu, ← hv, cohomologyBPZ_mk]
  exact betaRelTotal_eq_zero_of_ghost_number hne hun hvn

#print axioms betaRelTotal_eq_zero_of_ghost_number
#print axioms cohomologyBPZ_eq_zero_of_ghost_number

end
end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTBPZGhostNumber
