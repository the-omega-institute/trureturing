/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTNoGhostPairing
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTNoGhostPairing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The native degree-one BRST pairing in transverse orbifold coordinates. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTLightConeBPZ
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTPhysicalSpectrum

/-! The finite quartet representatives preserve the transverse BPZ comparison
on the native degree-one relative quotient. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTNoGhostPairing

open OriginalOrbifoldCriticalMatter (Matter State Orbifold hyperbolicData)
open OriginalOrbifoldRelativeMassShell (relativeMassShell differential hyperbolic_chargeEnergy)
open OriginalOrbifoldRelativeQuartet (Frame UCharge orbifoldGrade inclusion groundEquiv shellH
  ghostOneCycles ghostOneBoundaries ghostOneCohomologyEquivInFrame hdelta_nilpotent exists_frame)
open OriginalOrbifoldBRSTLightConeBPZ (shellBPZ_inclusion)
open OriginalOrbifoldBRSTShellBPZ (shellBPZ)
open OriginalOrbifoldBRSTPhysicalSpectrum (ghostOneCycleToRelative
  ghostOneCohomologyEquivPhysicalMomentum ghostOneCohomologyEquivPhysicalMomentum_apply_mk)
open OriginalOrbifoldBRSTPhysicalPairing (physicalBPZ physicalBPZ_representatives)
open OriginalOrbifoldBRSTMomentum (physicalMomentum)
open OriginalOrbifoldMatterBPZ (orbifoldBPZ)
open LatticePositiveEnergy (chargeEnergy)
open LatticeRelativeMassShell (massShellCutoff)
open LatticeLightConeCoordinates (g chargeVector)
open LatticeLightConeCoordinates.NullFrame (pPlus)
open LatticeBRSTModeFiltration (degree)
open D5.S3.HomologicalAlgebra.FinitePerturbation (inversePolynomial)

open private frameBasis FrameLabel groundIndex groundTensor_repr from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeShellQuartet
open private DegreeAtLeast delta hdelta_power_degree ground_degree perturbationInput
  perturbation_D perturbation_transferred_zero correctedI_ghostOne from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeQuartet
open private shellBPZ_degree_selection_of_support from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTLightConeBPZ

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private abbrev cutoff (a : UCharge) := massShellCutoff hyperbolicData a

private abbrev seriesLength (a : UCharge) := 2 * cutoff a + 1

private theorem opposite_pPlus (F : Frame) (a : UCharge) :
    F.pPlus (-a) = -F.pPlus a := by
  simp [pPlus, chargeVector, g, mul_neg, Finset.sum_neg_distrib]

private theorem opposite_onShell (a : UCharge) (ha : chargeEnergy hyperbolicData a ≤ 1) :
    chargeEnergy hyperbolicData (-a) ≤ 1 := by
  simpa only [hyperbolic_chargeEnergy, Pi.neg_apply, neg_mul_neg] using ha

private theorem inclusion_degree (F : Frame) (a : UCharge) (ha : chargeEnergy hyperbolicData a ≤ 1)
    (u : orbifoldGrade (cutoff a)) :
    DegreeAtLeast F 0 (inclusion a ha u : State) := by
  intro i hi
  change (frameBasis F).repr (OriginalOrbifoldRelativeQuartet.groundTensor a u) i ≠ 0 at hi
  rw [groundTensor_repr] at hi
  have h : i.2 = groundIndex a := by
    by_contra h
    exact (mul_ne_zero_iff.mp hi).2 (Finsupp.single_eq_of_ne h)
  rw [h, ground_degree]

private def correctedTerm (F : Frame) (a : UCharge) (ha : chargeEnergy hyperbolicData a ≤ 1)
    (u : orbifoldGrade (cutoff a)) (r : ℕ) : relativeMassShell a :=
  ((-(shellH F a * delta F a)) ^ r) (inclusion a ha u)

private theorem correctedTerm_degree (F : Frame) (a : UCharge)
    (ha : chargeEnergy hyperbolicData a ≤ 1) (u : orbifoldGrade (cutoff a)) (r : ℕ) :
    DegreeAtLeast F r (correctedTerm F a ha u r : State) := by
  have h : DegreeAtLeast F r (((shellH F a * delta F a) ^ r) (inclusion a ha u) : State) := by
    simpa only [zero_add] using hdelta_power_degree F a 0 _ (inclusion_degree F a ha u) r
  unfold correctedTerm
  rcases Nat.even_or_odd r with hr | hr
  · rw [hr.neg_pow]
    exact h
  · rw [hr.neg_pow]
    intro i hi
    apply h i
    let z : relativeMassShell a := ((shellH F a * delta F a) ^ r) (inclusion a ha u)
    let L : relativeMassShell a →ₗ[ℂ] ℂ :=
      ((frameBasis F).coord i).comp (relativeMassShell a).subtype
    change L (-z) ≠ 0 at hi
    change L z ≠ 0
    exact fun hz => hi ((L.map_neg z).trans (by rw [hz, neg_zero]))

private theorem correctedTerm_pair_eq_zero (F : Frame) (a : UCharge)
    (ha : chargeEnergy hyperbolicData a ≤ 1) (hb : chargeEnergy hyperbolicData (-a) ≤ 1)
    (u : orbifoldGrade (cutoff a)) (v : orbifoldGrade (cutoff (-a)))
    (r s : ℕ) (h : r + s ≠ 0) :
    shellBPZ a (correctedTerm F a ha u r) (correctedTerm F (-a) hb v s) = 0 := by
  apply shellBPZ_degree_selection_of_support F a
  intro i j hi hj
  have hr := correctedTerm_degree F a ha u r i hi
  have hs := correctedTerm_degree F (-a) hb v s j hj
  omega

private theorem groundEquiv_coe (F : Frame) (a : UCharge) (hp : F.pPlus a ≠ 0)
    (ha : chargeEnergy hyperbolicData a ≤ 1) (u : orbifoldGrade (cutoff a)) :
    (groundEquiv F a hp ha u : relativeMassShell a) = inclusion a ha u := rfl

private theorem corrected_representatives (F : Frame) (a : UCharge) (hp : F.pPlus a ≠ 0)
    (ha : chargeEnergy hyperbolicData a ≤ 1) (u : orbifoldGrade (cutoff a)) :
    let C := perturbationInput F a hp ha
    let n := seriesLength a
    C.D (C.I n (groundEquiv F a hp ha u)) = 0 ∧
      C.P n (C.I n (groundEquiv F a hp ha u)) = groundEquiv F a hp ha u := by
  let C := perturbationInput F a hp ha
  let n := seriesLength a
  have hn : 1 ≤ n := by dsimp [n, seriesLength]; omega
  exact ((C.finite_perturbation n hn (hdelta_nilpotent F a)).representatives
    (perturbation_transferred_zero F a hp ha n)).1 _

private def correctedCycle (F : Frame) (a : UCharge) (hp : F.pPlus a ≠ 0)
    (ha : chargeEnergy hyperbolicData a ≤ 1) (u : orbifoldGrade (cutoff a)) : ghostOneCycles a :=
  ⟨(perturbationInput F a hp ha).I (seriesLength a) (groundEquiv F a hp ha u),
    correctedI_ghostOne F a hp ha _ _,
    LinearMap.mem_ker.mpr (by
      rw [← perturbation_D F a hp ha]
      exact (corrected_representatives F a hp ha u).1)⟩

private theorem correctedCycle_sum (F : Frame) (a : UCharge) (hp : F.pPlus a ≠ 0)
    (ha : chargeEnergy hyperbolicData a ≤ 1) (u : orbifoldGrade (cutoff a)) :
    (correctedCycle F a hp ha u : relativeMassShell a) =
      ∑ r ∈ Finset.range (seriesLength a), correctedTerm F a ha u r := by
  change inversePolynomial (shellH F a * delta F a) (seriesLength a)
    (groundEquiv F a hp ha u : relativeMassShell a) = _
  rw [groundEquiv_coe]
  simp only [inversePolynomial, LinearMap.sum_apply, correctedTerm]

private theorem correctedCycle_pair (F : Frame) (a : UCharge)
    (hp : F.pPlus a ≠ 0) (hn : F.pPlus (-a) ≠ 0)
    (ha : chargeEnergy hyperbolicData a ≤ 1) (hb : chargeEnergy hyperbolicData (-a) ≤ 1)
    (u : orbifoldGrade (cutoff a)) (v : orbifoldGrade (cutoff (-a))) :
    shellBPZ a (correctedCycle F a hp ha u) (correctedCycle F (-a) hn hb v) =
      -orbifoldBPZ (u : Orbifold) (v : Orbifold) := by
  rw [correctedCycle_sum, correctedCycle_sum]
  simp only [map_sum, LinearMap.sum_apply]
  rw [Finset.sum_eq_single 0, Finset.sum_eq_single 0]
  · simpa only [correctedTerm, pow_zero, Module.End.one_apply] using
      shellBPZ_inclusion a ha hb u v
  · intro s _ hs
    exact correctedTerm_pair_eq_zero F a ha hb u v s 0 (by simpa using hs)
  · simp [seriesLength]
  · intro r _ hr
    exact Finset.sum_eq_zero fun s _ =>
      correctedTerm_pair_eq_zero F a ha hb u v s r (by omega)
  · simp [seriesLength]

private theorem correctedCycle_mk (F : Frame) (a : UCharge) (hp : F.pPlus a ≠ 0)
    (ha : chargeEnergy hyperbolicData a ≤ 1) (u : orbifoldGrade (cutoff a)) :
    (ghostOneCohomologyEquivInFrame F a hp ha).symm u =
      (ghostOneBoundaries a).mkQ (correctedCycle F a hp ha u) := by
  apply (ghostOneCohomologyEquivInFrame F a hp ha).injective
  rw [LinearEquiv.apply_symm_apply]
  change u = (groundEquiv F a hp ha).symm
    ((perturbationInput F a hp ha).P (seriesLength a) (correctedCycle F a hp ha u))
  rw [show (perturbationInput F a hp ha).P (seriesLength a) (correctedCycle F a hp ha u) =
    groundEquiv F a hp ha u from (corrected_representatives F a hp ha u).2,
    LinearEquiv.symm_apply_apply]

/-- The degree-one physical equivalence in a specified light-cone frame. -/
def physicalMomentumEquivOrbifoldGradeInFrame (F : Frame) (a : UCharge) (hp : F.pPlus a ≠ 0)
    (ha : chargeEnergy hyperbolicData a ≤ 1) :
    physicalMomentum a ≃ₗ[ℂ] orbifoldGrade (massShellCutoff hyperbolicData a) :=
  (ghostOneCohomologyEquivPhysicalMomentum a).symm.trans
    (ghostOneCohomologyEquivInFrame F a hp ha)

/-- In a common frame the physical pairing of opposite momenta is the negative
of the original bilinear form of the transverse orbifold. -/
theorem physicalBPZ_inFrame (F : Frame) (a : UCharge)
    (hp : F.pPlus a ≠ 0) (hn : F.pPlus (-a) ≠ 0)
    (ha : chargeEnergy hyperbolicData a ≤ 1) (hb : chargeEnergy hyperbolicData (-a) ≤ 1)
    (u : orbifoldGrade (massShellCutoff hyperbolicData a))
    (v : orbifoldGrade (massShellCutoff hyperbolicData (-a))) :
    physicalBPZ ((physicalMomentumEquivOrbifoldGradeInFrame F a hp ha).symm u)
        ((physicalMomentumEquivOrbifoldGradeInFrame F (-a) hn hb).symm v) =
      -orbifoldBPZ (u : Orbifold) (v : Orbifold) := by
  let x := correctedCycle F a hp ha u
  let y := correctedCycle F (-a) hn hb v
  simp only [physicalMomentumEquivOrbifoldGradeInFrame, LinearEquiv.symm_trans_apply,
    LinearEquiv.symm_symm, correctedCycle_mk]
  refine (physicalBPZ_representatives _ _ (ghostOneCycleToRelative a x)
    (ghostOneCycleToRelative (-a) y)
    (ghostOneCohomologyEquivPhysicalMomentum_apply_mk a x).symm
    (ghostOneCohomologyEquivPhysicalMomentum_apply_mk (-a) y).symm).trans ?_
  exact correctedCycle_pair F a hp hn ha hb u v

/-- Every nonzero on-shell momentum and its opposite admit a common frame
in which the comparison holds for all transverse representatives. -/
theorem physicalBPZ_exists_common_frame (a : UCharge) (ha0 : a ≠ 0)
    (ha : chargeEnergy hyperbolicData a ≤ 1) :
    ∃ (F : Frame) (hp : F.pPlus a ≠ 0) (hn : F.pPlus (-a) ≠ 0),
      ∀ (u : orbifoldGrade (massShellCutoff hyperbolicData a))
        (v : orbifoldGrade (massShellCutoff hyperbolicData (-a))),
        physicalBPZ ((physicalMomentumEquivOrbifoldGradeInFrame F a hp ha).symm u)
            ((physicalMomentumEquivOrbifoldGradeInFrame F (-a) hn
              (opposite_onShell a ha)).symm v) =
          -orbifoldBPZ (u : Orbifold) (v : Orbifold) := by
  have hF : ∃ F : Frame, F.pPlus a ≠ 0 := exists_frame a ha0
  let F : Frame := Classical.choose hF
  have hp : F.pPlus a ≠ 0 := Classical.choose_spec hF
  have hn : F.pPlus (-a) ≠ 0 := by rwa [opposite_pPlus, neg_ne_zero]
  exact ⟨F, hp, hn, physicalBPZ_inFrame F a hp hn ha (opposite_onShell a ha)⟩

#print axioms physicalBPZ_inFrame
#print axioms physicalBPZ_exists_common_frame

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTNoGhostPairing
