/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTNoGhostContravariant
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTNoGhostContravariant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The native contravariant BRST pairing in transverse orbifold coordinates. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTNoGhostPairing
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTContravariant

/-! Charge reversal preserves light-cone degree and fixes the transverse orbifold factor. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped TensorProduct BigOperators

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTNoGhostContravariant

open OriginalOrbifoldCriticalMatter (Matter State Orbifold hyperbolicData b)
open OriginalOrbifoldBRSTZeroEnergy (orbifoldBasis totalL0)
open OriginalOrbifoldRelativeMassShell (relativeMassShell hyperbolic_chargeEnergy)
open OriginalOrbifoldRelativeQuartet (Frame UCharge transverseBasis orbifoldGrade
  groundTensor inclusion ghostOneBoundaries)
open OriginalOrbifoldBRSTChevalley
  (stateTheta stateTheta_mem_fixedMomentum stateTheta_b stateTheta_L0 chevalley)
open OriginalOrbifoldBRSTNoGhostPairing (physicalMomentumEquivOrbifoldGradeInFrame)
open OriginalOrbifoldBRSTContravariant (contravariantBPZ contravariantBPZ_apply)
open OriginalOrbifoldBRSTLightConeBPZ (shellBPZ_inclusion)
open OriginalOrbifoldBRSTShellBPZ (shellBPZ)
open OriginalOrbifoldBRSTPhysicalSpectrum (ghostOneCycleToRelative
  ghostOneCohomologyEquivPhysicalMomentum ghostOneCohomologyEquivPhysicalMomentum_apply_mk)
open OriginalOrbifoldBRSTPhysicalPairing (physicalBPZ_representatives)
open OriginalOrbifoldBRSTDescent (relativeBoundaries RelativeCohomology)
open OriginalOrbifoldMatterBPZ (orbifoldBPZ)
open LatticePositiveEnergy (chargeEnergy)
open LatticeRelativeMassShell (massShellCutoff)
open LatticeLightConeCoordinates (E lin)
open LatticeGeneratingFieldLocality (Oscillator)
open LatticeQuartetContraction (actualBasis_apply sector Exponents)
open LatticeBRSTModeFiltration (degree basis_expand)
open LatticeInvolution (sigma sigma_smul sigma_X theta thetaLinear theta_single)
open D5.S3.Quantum.Fermionic.CountableOccupationFock (ket)
open MvPolynomial

open private frameBasis frameBasis_apply FrameLabel from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeShellQuartet
open private DegreeAtLeast from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeQuartet
open private shellBPZ_degree_selection_of_support from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTLightConeBPZ
open private polynomialEquiv_symm_X from
  D5.S3.VertexAlgebra.Lattice.LatticeLightConeCoordinates
open private matterTheta cycleTheta cohomologyTheta cohomologyTheta_mk from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTChevalley
open private cutoff seriesLength opposite_onShell correctedTerm correctedTerm_degree
  correctedCycle correctedCycle_sum correctedCycle_mk from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTNoGhostPairing

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private theorem sigma_lin (r : ℕ) (z : E hyperbolicData) :
    sigma hyperbolicData (lin r z) = -lin r z := by
  classical
  change sigma hyperbolicData (∑ i, z i • X (i, r)) = -(∑ i, z i • X (i, r))
  rw [map_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  let Xir : Oscillator hyperbolicData := X (i, r)
  change sigma hyperbolicData (z i • Xir) = -(z i • Xir)
  exact (sigma_smul hyperbolicData (z i) Xir).trans (by
    rw [show sigma hyperbolicData Xir = -Xir from sigma_X hyperbolicData (i, r), smul_neg])

private theorem sigma_frameMonomial (F : Frame) (d : Exponents 0) :
    let A := (F.coordinateEquiv (transverseBasis F)).symm
    sigma hyperbolicData (A (monomial d 1)) =
      (-1 : ℂ) ^ (∑ k ∈ d.support, d k) • A (monomial d 1) := by
  classical
  let A := (F.coordinateEquiv (transverseBasis F)).symm
  have hx (k : LatticeLightConeCoordinates.NullFrame.Label 0 × ℕ) :
      sigma hyperbolicData (A (X k)) = (-1 : ℂ) • A (X k) := by
    rcases k with ⟨j, r⟩
    change sigma hyperbolicData ((LatticeLightConeCoordinates.polynomialEquiv
      (F.completeBasis (transverseBasis F))).symm (X (j, r))) = _
    rw [polynomialEquiv_symm_X, sigma_lin, neg_one_smul]
  have hxpow (k : LatticeLightConeCoordinates.NullFrame.Label 0 × ℕ) :
      sigma hyperbolicData (A (X k)) ^ d k = (-1 : ℂ) ^ d k • A (X k) ^ d k := by
    rw [hx, smul_pow]
  change sigma hyperbolicData (A (monomial d 1)) =
    (-1 : ℂ) ^ (∑ k ∈ d.support, d k) • A (monomial d 1)
  simp only [monomial_eq, C_1, one_mul, Finsupp.prod, map_prod, map_pow, hxpow,
    Finset.prod_smul, Finset.prod_pow_eq_pow_sum]

private def reflectedLabel (i : FrameLabel) : FrameLabel :=
  (i.1, (⟨-i.2.1.1, i.2.1.2⟩, i.2.2))

private theorem stateTheta_frameBasis (F : Frame) (i : FrameLabel) :
    ∃ c : ℂ, stateTheta (frameBasis F i) = c • frameBasis F (reflectedLabel i) := by
  rcases i with ⟨j, ⟨a, d⟩, S⟩
  refine ⟨(-1 : ℂ) ^ (∑ k ∈ d.support, d k), ?_⟩
  rw [frameBasis_apply, frameBasis_apply]
  simp only [reflectedLabel, actualBasis_apply, sector, TensorProduct.assoc_symm_tmul,
    stateTheta, matterTheta, TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.coe_coe]
  rw [show theta hyperbolicData _ = thetaLinear hyperbolicData _ from rfl,
    theta_single, sigma_frameMonomial, ← Finsupp.smul_single, TensorProduct.tmul_smul,
    ← TensorProduct.smul_tmul']

private theorem stateTheta_preserves_degree (F : Frame) (l : ℤ) (x : State)
    (hx : DegreeAtLeast F l x) : DegreeAtLeast F l (stateTheta x) := by
  classical
  intro j hj
  by_contra h
  apply hj
  change (frameBasis F).coord j (stateTheta x) = 0
  rw [← basis_expand (frameBasis F) x]
  simp only [map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro i hi
  obtain ⟨c, hc⟩ := stateTheta_frameBasis F i
  have hne : reflectedLabel i ≠ j := by
    intro hij
    apply h
    rw [← hij]
    exact hx i (Finsupp.mem_support_iff.mp hi)
  rw [hc, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self_apply, ite_eq_right hne,
    smul_zero, smul_zero]

private def thetaShell (a : UCharge) : relativeMassShell a →ₗ[ℂ] relativeMassShell (-a) :=
  (stateTheta.comp (relativeMassShell a).subtype).codRestrict _ (by
    intro x
    change (stateTheta (x : State) ∈ OriginalOrbifoldRelativeMassShell.fixedMomentum (-a) ∧
      b 0 (stateTheta (x : State)) = 0) ∧ totalL0 (stateTheta (x : State)) = 0
    refine ⟨⟨stateTheta_mem_fixedMomentum x.property.1.1, ?_⟩, ?_⟩
    · rw [← stateTheta_b, x.property.1.2, map_zero]
    · rw [← stateTheta_L0, x.property.2, map_zero])

private theorem cutoff_opposite (a : UCharge) : cutoff a = cutoff (-a) := by
  simp only [cutoff, massShellCutoff, hyperbolic_chargeEnergy, Pi.neg_apply, neg_mul_neg]

private theorem stateTheta_groundTensor (a : UCharge) (v : Orbifold) :
    stateTheta (groundTensor a v) = groundTensor (-a) v := by
  change stateTheta ((v ⊗ₜ[ℂ] Finsupp.single a (monomial 0 1)) ⊗ₜ[ℂ] ket {1}) = _
  simp only [stateTheta, matterTheta, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearEquiv.coe_coe]
  rw [show theta hyperbolicData _ = thetaLinear hyperbolicData _ from rfl,
    theta_single, monomial_zero', C_1, map_one]
  rfl

private theorem correctedCycle_theta_pair (F : Frame) (a : UCharge)
    (hp : F.pPlus a ≠ 0) (ha : chargeEnergy hyperbolicData a ≤ 1)
    (u v : orbifoldGrade (cutoff a)) :
    shellBPZ a (correctedCycle F a hp ha u) (thetaShell a (correctedCycle F a hp ha v)) =
      -orbifoldBPZ (u : Orbifold) (v : Orbifold) := by
  rw [correctedCycle_sum, correctedCycle_sum]
  simp only [map_sum, LinearMap.sum_apply]
  have hterm (r s : ℕ) (h : r + s ≠ 0) :
      shellBPZ a (correctedTerm F a ha u r) (thetaShell a (correctedTerm F a ha v s)) = 0 := by
    apply shellBPZ_degree_selection_of_support F a
    intro i j hi hj
    have hr := correctedTerm_degree F a ha u r i hi
    have hs := stateTheta_preserves_degree F s _
      (correctedTerm_degree F a ha v s) j hj
    omega
  rw [Finset.sum_eq_single 0, Finset.sum_eq_single 0]
  · simp only [correctedTerm, pow_zero, Module.End.one_apply]
    let v' : orbifoldGrade (cutoff (-a)) := ⟨v, cutoff_opposite a ▸ v.property⟩
    have hθ : thetaShell a (inclusion a ha v) = inclusion (-a) (opposite_onShell a ha) v' :=
      Subtype.ext (stateTheta_groundTensor a v)
    rw [hθ]
    exact shellBPZ_inclusion a ha (opposite_onShell a ha) u v'
  · intro r _ hr
    exact hterm r 0 (by simpa using hr)
  · simp [seriesLength]
  · intro s _ hs
    exact Finset.sum_eq_zero fun r _ => hterm r s (by omega)
  · simp [seriesLength]

set_option maxHeartbeats 600000 in
-- Identifying the ambient quotient representatives unfolds the momentum and grade subtypes.
/-- The original contravariant form restricts on every nonzero on-shell
physical momentum to the original transverse orbifold form in a light-cone frame. -/
theorem contravariantBPZ_inFrame (F : Frame) (a : UCharge) (hp : F.pPlus a ≠ 0)
    (ha : chargeEnergy hyperbolicData a ≤ 1) (u v : orbifoldGrade (massShellCutoff hyperbolicData a)) :
    contravariantBPZ ((physicalMomentumEquivOrbifoldGradeInFrame F a hp ha).symm u)
        ((physicalMomentumEquivOrbifoldGradeInFrame F a hp ha).symm v) =
      orbifoldBPZ (u : Orbifold) (v : Orbifold) := by
  let x := correctedCycle F a hp ha u
  let y := correctedCycle F a hp ha v
  rw [contravariantBPZ_apply]
  simp only [physicalMomentumEquivOrbifoldGradeInFrame, LinearEquiv.symm_trans_apply,
    LinearEquiv.symm_symm, correctedCycle_mk]
  rw [physicalBPZ_representatives _ _ (ghostOneCycleToRelative a x)
    (cycleTheta (ghostOneCycleToRelative a y))
    (ghostOneCohomologyEquivPhysicalMomentum_apply_mk a x).symm (by
      change relativeBoundaries.mkQ (cycleTheta (ghostOneCycleToRelative a y)) =
        cohomologyTheta
          ((ghostOneCohomologyEquivPhysicalMomentum a ((ghostOneBoundaries a).mkQ y)).1 :
            RelativeCohomology)
      exact (cohomologyTheta_mk (ghostOneCycleToRelative a y)).symm.trans
        (congrArg (fun z : RelativeCohomology => cohomologyTheta z)
          (ghostOneCohomologyEquivPhysicalMomentum_apply_mk a y).symm))]
  change -shellBPZ a (correctedCycle F a hp ha u) (thetaShell a (correctedCycle F a hp ha v)) = _
  rw [correctedCycle_theta_pair, neg_neg]

#print axioms contravariantBPZ_inFrame

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTNoGhostContravariant
