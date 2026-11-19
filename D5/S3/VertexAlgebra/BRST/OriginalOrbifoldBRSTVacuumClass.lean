/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTVacuumClass
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTVacuumClass
   mirror-E: none(waiver:algebraic-original-brst-cohomology)
   anchors: []
   utility: none
   digest: The all-state vacuum coefficient separates the original Leech orbifold BRST vacuum. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldCriticalMatter
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyNonvacuity

/-! The vacuum class of the original orbifold, hyperbolic lattice, and bc ghost complex. -/

set_option autoImplicit false

open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTVacuumClass

open OriginalOrbifoldCriticalMatter
open ActualLeechHyperbolic (leechData leech_spec)
open TwistedGround
open D5.S3.Quantum.Fermionic
open CountableOccupationFock (Fock)
open private matterVacuumCoeff matterCoeff_negative_sugawara ghostCoeff_charge ghostCoeff_c from
  D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyNonvacuity
open private epsilon_vacuum from D5.S3.Quantum.Fermionic.BcGhostVirasoro

noncomputable section

private def orbifoldCoeff : Orbifold →ₗ[ℂ] ℂ :=
  (matterVacuumCoeff leechData).comp
    ((LatticeInvolution.fixedSpace leechData).subtype.comp (LinearMap.fst ℂ _ _))

private theorem orbifoldCoeff_negative_mode (m : ℤ) (hm : m < 0) (v : Orbifold) :
    orbifoldCoeff (orbifoldMode m v) = 0 := by
  change matterVacuumCoeff leechData
    (OriginalOrbifoldConformal.L leechData leech_spec.2.1 leech_spec.2.2.1 m v).1.val = 0
  rw [OriginalOrbifoldConformal.L_fixed_apply]
  exact matterCoeff_negative_sugawara _ _ m hm v.1.val

private def matterCoeff : Matter →ₗ[ℂ] ℂ :=
  TensorProduct.lift (orbifoldCoeff.smulRight (matterVacuumCoeff hyperbolicData))

private theorem matterCoeff_tmul (v : Orbifold) (w : Hyperbolic) :
    matterCoeff (v ⊗ₜ[ℂ] w) = orbifoldCoeff v * matterVacuumCoeff hyperbolicData w := by
  rw [matterCoeff, TensorProduct.lift.tmul, LinearMap.smulRight_apply,
    LinearMap.smul_apply, smul_eq_mul]

private theorem matterCoeff_negative_mode (m : ℤ) (hm : m < 0) (x : Matter) :
    matterCoeff (mode m x) = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
      have hw : matterVacuumCoeff hyperbolicData (hyperbolicMode m w) = 0 :=
        matterCoeff_negative_sugawara hyperbolicData hyperbolicInverse m hm w
      rw [mode, LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
        map_add, matterCoeff_tmul, matterCoeff_tmul, orbifoldCoeff_negative_mode m hm,
        hw, zero_mul, mul_zero, add_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

/-- The vacuum coefficient on the entire algebraic matter-ghost state space. -/
def vacuumCoeff : State →ₗ[ℂ] ℂ :=
  TensorProduct.lift (matterCoeff.smulRight BcGhostVirasoro.epsilon)

private theorem vacuumCoeff_tmul (v : Matter) (w : Fock) :
    vacuumCoeff (v ⊗ₜ[ℂ] w) = matterCoeff v * BcGhostVirasoro.epsilon w := by
  rw [vacuumCoeff, TensorProduct.lift.tmul, LinearMap.smulRight_apply,
    LinearMap.smul_apply, smul_eq_mul]

private theorem vacuumCoeff_summand (m : ℤ) (x : State) :
    vacuumCoeff (VirasoroBRST.summand matterDatum m x) = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
      change vacuumCoeff (TensorProduct.map (mode m) (BcGhostFock.c (-m)) (v ⊗ₜ[ℂ] w)) = 0
      rw [TensorProduct.map_tmul, vacuumCoeff_tmul]
      by_cases hm : m < 0
      · rw [matterCoeff_negative_mode m hm, zero_mul]
      · rw [ghostCoeff_c (-m) (by omega), mul_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

private theorem vacuumCoeff_matter_charge (x : State) :
    vacuumCoeff (VirasoroBRST.T matterDatum x) = 0 := by
  change vacuumCoeff (∑ᶠ m : ℤ, VirasoroBRST.summand matterDatum m x) = 0
  rw [map_finsum _ (VirasoroBRST.summand_finite matterDatum x)]
  exact finsum_eq_zero_of_forall_eq_zero (fun m => vacuumCoeff_summand m x)

private theorem vacuumCoeff_ghost_charge (x : State) :
    vacuumCoeff (VirasoroBRST.ghostCharge matterDatum x) = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
      change vacuumCoeff (TensorProduct.map LinearMap.id BcGhostBRST.Qg (v ⊗ₜ[ℂ] w)) = 0
      rw [TensorProduct.map_tmul, vacuumCoeff_tmul, ghostCoeff_charge, mul_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

theorem vacuumCoeff_Q (x : State) : vacuumCoeff (Q x) = 0 := by
  change vacuumCoeff (VirasoroBRST.T matterDatum x + VirasoroBRST.ghostCharge matterDatum x) = 0
  rw [map_add, vacuumCoeff_matter_charge, vacuumCoeff_ghost_charge, add_zero]

theorem vacuumCoeff_vacuum : vacuumCoeff vacuum = 1 := by
  rw [vacuum, vacuumCoeff_tmul, matterVacuum, matterCoeff_tmul, epsilon_vacuum]
  change matterVacuumCoeff leechData (LatticeAllStateField.vacuum leechData) *
    matterVacuumCoeff hyperbolicData (LatticeAllStateField.vacuum hyperbolicData) * 1 = 1
  simp [matterVacuumCoeff, LatticeAllStateField.vacuum]

/-- The actual tensor vacuum is outside the range of the original charge. -/
theorem vacuum_not_mem_range : vacuum ∉ LinearMap.range Q := by
  rintro ⟨x, hx⟩
  have h := congrArg vacuumCoeff hx
  rw [vacuumCoeff_Q, vacuumCoeff_vacuum] at h
  exact zero_ne_one h

/-- Cycles of the original charge on the full algebraic state space. -/
abbrev cycles : Submodule ℂ State := LinearMap.ker Q

instance cycles_addCommGroup : AddCommGroup cycles :=
  Submodule.addCommGroup (R := ℂ) (M := State) cycles

private theorem range_Q_le_ker_Q : LinearMap.range Q ≤ cycles := by
  apply LinearMap.range_le_ker_iff.mpr
  change Q * Q = 0
  simpa only [pow_two] using Q_squared

/-- The range of `Q` included into its kernel by square-zero. -/
def boundaries : Submodule ℂ cycles :=
  LinearMap.range (Submodule.inclusion range_Q_le_ker_Q)

abbrev Cohomology : Type := cycles ⧸ boundaries

/-- The image of the closed tensor vacuum in the BRST quotient. -/
def vacuumClass : Cohomology := boundaries.mkQ ⟨vacuum, LinearMap.mem_ker.mpr vacuum_closed⟩

/-- The vacuum coefficient descended to the actual BRST quotient. -/
def vacuumEvaluation : Cohomology →ₗ[ℂ] ℂ :=
  boundaries.liftQ (vacuumCoeff.comp cycles.subtype) (by
    intro a ha
    change a ∈ LinearMap.range (Submodule.inclusion range_Q_le_ker_Q) at ha
    obtain ⟨b, rfl⟩ := LinearMap.mem_range.mp ha
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp b.property
    change vacuumCoeff (b : State) = 0
    rw [← hx, vacuumCoeff_Q])

theorem vacuumEvaluation_vacuumClass : vacuumEvaluation vacuumClass = 1 := by
  change vacuumCoeff vacuum = 1
  exact vacuumCoeff_vacuum

theorem vacuumClass_ne_zero : vacuumClass ≠ 0 := by
  intro h
  have he := vacuumEvaluation_vacuumClass
  rw [h, map_zero] at he
  exact zero_ne_one he

#print axioms vacuumCoeff_Q
#print axioms vacuumCoeff_vacuum
#print axioms vacuum_not_mem_range
#print axioms Cohomology
#print axioms vacuumClass
#print axioms vacuumEvaluation
#print axioms vacuumEvaluation_vacuumClass
#print axioms vacuumClass_ne_zero

end
end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTVacuumClass
