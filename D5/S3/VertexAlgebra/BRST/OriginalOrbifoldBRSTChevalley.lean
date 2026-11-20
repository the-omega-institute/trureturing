/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTChevalley
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTChevalley
   mirror-E: none(waiver:algebraic-original-orbifold-brst-chevalley)
   anchors: []
   utility: none
   digest: The native BRST Lie involution reverses hyperbolic momentum and negates the Cartan. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTCartan

/-!
The charge reversal on the hyperbolic lattice factor implements the involution
on the Monster Lie algebra described in Borcherds (1992), §6. The construction
uses the original orbifold and ghost fields and descends on the native relative
BRST quotient.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTChevalley

open D5.S3.Quantum.Fermionic
open D5.S3.HomologicalAlgebra.FinitePerturbation (boundaryMap)
open OriginalOrbifoldCriticalMatter (Matter State Orbifold hyperbolicData hyperbolicInverse
  orbifoldVertexAlgebra matterVacuum matterDatum Q b)
open OriginalOrbifoldMatterTensorField (stateField stressState)
open OriginalOrbifoldBRSTStateField (Y J OmegaTotal)
open OriginalOrbifoldBRSTZeroEnergy (totalL0)
open OriginalOrbifoldBRSTDescent (relativeStates relativeCycles relativeBoundaries
  RelativeCohomology descent cycleDescent cohomologyDescent cohomologyDescent_mk)
open OriginalOrbifoldBRSTPhysicalLie (N DegreeOne grade cohomologyNumber cycleNumber
  cohomologyNumber_mk degreeOne_bracket)
open OriginalOrbifoldBRSTMomentum (momentumCurrent momentumZeroMode physicalMomentum
  mem_fixedMomentum_iff_zero_modes mem_physicalMomentum_iff)
open OriginalOrbifoldRelativeMassShell (fixedMomentum)
open OriginalOrbifoldBRSTCartan (cartanCycle cartanCycle_coe h span_h_eq_physicalMomentum_zero)

open private theta_omega_fixed from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private opposite from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTMomentum
open private cycle_closed from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTDescent

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private def matterTheta : Module.End ℂ Matter :=
  TensorProduct.map LinearMap.id (LatticeInvolution.theta hyperbolicData).toLinearMap

/-- The original charge-reversal operator, with the orbifold and ghost factors fixed. -/
def stateTheta : Module.End ℂ State :=
  TensorProduct.map matterTheta LinearMap.id

private theorem matterTheta_square (x : Matter) : matterTheta (matterTheta x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a u =>
    simpa only [matterTheta, TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.coe_coe,
      LatticeInvolution.theta, LinearEquiv.coe_ofInvolutive] using
      congrArg (fun v => a ⊗ₜ[ℂ] v) (LatticeInvolution.theta_involutive hyperbolicData u)
  | add x y hx hy => simp only [map_add, hx, hy]

theorem stateTheta_involutive : Function.Involutive stateTheta := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul u a =>
    simp only [stateTheta, TensorProduct.map_tmul, LinearMap.id_apply, matterTheta_square]
  | add x y hx hy => simp only [map_add, hx, hy]

section MatterField

open private modeSummand_tmul from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldMatterTensorField

private theorem matterTheta_mode (s x : Matter) (n : ℤ) :
    matterTheta (((stateField s)[[n]]) x) =
      ((stateField (matterTheta s))[[n]]) (matterTheta x) := by
  induction s using TensorProduct.inductionOn with
  | tmul a u =>
    induction x using TensorProduct.inductionOn with
    | tmul v w =>
      rw [OriginalOrbifoldMatterTensorField.stateField_ncoeff_apply,
        map_finsum matterTheta (OriginalOrbifoldMatterTensorField.modeSummand_finite _ _ _),
        OriginalOrbifoldMatterTensorField.stateField_ncoeff_apply]
      apply finsum_congr
      intro k
      simp only [matterTheta, TensorProduct.map_tmul, LinearMap.id_apply,
        LinearEquiv.coe_coe, modeSummand_tmul,
        LatticeInvolution.stateField_theta]
    | add x y hx hy => simp only [map_add, hx, hy]
  | add s t hs ht => simp only [map_add, Pi.add_apply, LinearMap.add_apply, hs, ht]

end MatterField

open private modeSummand_tmul from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTStateField

/-- Every normalized mode of the original total state-field map is equivariant. -/
theorem stateTheta_mode (s x : State) (n : ℤ) :
    stateTheta (((Y s)[[n]]) x) = ((Y (stateTheta s))[[n]]) (stateTheta x) := by
  induction s using TensorProduct.inductionOn with
  | tmul u a =>
    induction x using TensorProduct.inductionOn with
    | tmul v b =>
      rw [OriginalOrbifoldBRSTStateField.Y_ncoeff_apply,
        map_finsum stateTheta (OriginalOrbifoldBRSTStateField.modeSummand_finite _ _ _),
        OriginalOrbifoldBRSTStateField.Y_ncoeff_apply]
      apply finsum_congr
      intro k
      simp only [stateTheta, TensorProduct.map_tmul, LinearMap.id_apply, modeSummand_tmul]
      exact congrArg (fun w => w ⊗ₜ[ℂ] ((BcGhostStateField.Y a)[[n - 1 - k]]) b)
        (matterTheta_mode u v k)
    | add x y hx hy => simp only [map_add, hx, hy]
  | add s t hs ht => simp only [map_add, Pi.add_apply, LinearMap.add_apply, hs, ht]

private theorem matterTheta_vacuum : matterTheta matterVacuum = matterVacuum := by
  simp only [matterTheta, matterVacuum, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearEquiv.coe_coe, LatticeInvolution.theta_vacuum]

private theorem matterTheta_stress : matterTheta stressState = stressState := by
  simp only [matterTheta, stressState, TensorProduct.map_tmul, LinearMap.id_apply, map_add,
    LinearEquiv.coe_coe, LatticeInvolution.theta_vacuum, theta_omega_fixed]

theorem stateTheta_Q (x : State) : stateTheta (Q x) = Q (stateTheta x) := by
  have hJ : stateTheta J = J := by
    simp only [J, stateTheta, map_add, TensorProduct.map_tmul, LinearMap.id_apply,
      matterTheta_vacuum, matterTheta_stress]
  simpa only [hJ, OriginalOrbifoldBRSTStateField.current_zero_mode] using stateTheta_mode J x 0

theorem stateTheta_L0 (x : State) : stateTheta (totalL0 x) = totalL0 (stateTheta x) := by
  have hOmega : stateTheta OmegaTotal = OmegaTotal := by
    simp only [OmegaTotal, stateTheta, map_add, TensorProduct.map_tmul, LinearMap.id_apply,
      matterTheta_vacuum, matterTheta_stress]
  simpa only [hOmega, ← OriginalOrbifoldBRSTStateField.conformal_modes 0]
    using stateTheta_mode OmegaTotal x (0 + 1)

private theorem stateTheta_liftGhost (T : Module.End ℂ CountableOccupationFock.Fock)
    (x : State) :
    stateTheta (BcGhostChargeTensor.liftGhost T x) =
      BcGhostChargeTensor.liftGhost T (stateTheta x) := by
  induction x using TensorProduct.inductionOn with
  | tmul u a =>
    simp only [stateTheta, BcGhostChargeTensor.liftGhost, TensorProduct.map_tmul,
      LinearMap.id_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem stateTheta_b (n : ℤ) (x : State) : stateTheta (b n x) = b n (stateTheta x) :=
  stateTheta_liftGhost _ x

theorem stateTheta_N (x : State) : stateTheta (N x) = N (stateTheta x) :=
  stateTheta_liftGhost _ x

theorem stateTheta_descent (x y : State) :
    stateTheta (descent x y) = descent (stateTheta x) (stateTheta y) := by
  change stateTheta (((Y (b (-1) x))[[0]]) y) = ((Y (b (-1) (stateTheta x)))[[0]]) (stateTheta y)
  rw [stateTheta_mode, stateTheta_b]

private theorem stateTheta_momentumCurrent (i : Fin hyperbolicData.rank) :
    stateTheta (momentumCurrent i) = -momentumCurrent i := by
  have ht := LatticeInvolution.theta_neutralField_ncoeff hyperbolicData (opposite i) (-1)
    (LatticeAllStateField.vacuum hyperbolicData)
  rw [LatticeInvolution.theta_vacuum] at ht
  simp only [stateTheta, matterTheta, momentumCurrent, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearEquiv.coe_coe, ht, TensorProduct.tmul_neg, TensorProduct.neg_tmul]

theorem stateTheta_momentumZeroMode (i : Fin hyperbolicData.rank) (x : State) :
    stateTheta (momentumZeroMode i x) = -momentumZeroMode i (stateTheta x) := by
  simpa only [momentumZeroMode, stateTheta_momentumCurrent, map_neg, Pi.neg_apply,
    LinearMap.neg_apply] using stateTheta_mode (momentumCurrent i) x 0

theorem stateTheta_mem_fixedMomentum {p : LatticeGeneratingFieldLocality.Charge hyperbolicData}
    {x : State} (hx : x ∈ fixedMomentum p) : stateTheta x ∈ fixedMomentum (-p) := by
  apply (mem_fixedMomentum_iff_zero_modes _ _).mpr
  intro i
  have hi := (mem_fixedMomentum_iff_zero_modes _ _).mp hx i
  have hneg := (stateTheta_momentumZeroMode i x).symm
  rw [hi, map_smul] at hneg
  rw [← neg_neg (momentumZeroMode i (stateTheta x)), hneg]
  simp only [Pi.neg_apply, Int.cast_neg, neg_smul]

private def relativeTheta : Module.End ℂ relativeStates :=
  stateTheta.restrict (by
    intro x hx
    change b 0 x = 0 ∧ totalL0 x = 0 at hx
    change b 0 (stateTheta x) = 0 ∧ totalL0 (stateTheta x) = 0
    rw [← stateTheta_b, ← stateTheta_L0, hx.1, hx.2, map_zero]
    exact ⟨rfl, rfl⟩)

private def cycleTheta : Module.End ℂ relativeCycles :=
  relativeTheta.restrict (by
    intro x hx
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change Q (stateTheta (x : State)) = 0
    rw [← stateTheta_Q, cycle_closed ⟨x, hx⟩, map_zero])

private def cohomologyTheta : Module.End ℂ RelativeCohomology :=
  relativeBoundaries.mapQ relativeBoundaries cycleTheta (by
    intro x hx
    change ∃ z, boundaryMap _ _ z = x at hx
    obtain ⟨z, rfl⟩ := hx
    refine ⟨relativeTheta z, Subtype.ext (Subtype.ext ?_)⟩
    exact (stateTheta_Q (z : State)).symm)

private theorem cohomologyTheta_mk (x : relativeCycles) :
    cohomologyTheta (relativeBoundaries.mkQ x) = relativeBoundaries.mkQ (cycleTheta x) := rfl

private theorem cohomologyTheta_involutive : Function.Involutive cohomologyTheta := by
  intro x
  obtain ⟨z, rfl⟩ := relativeBoundaries.mkQ_surjective x
  rw [cohomologyTheta_mk, cohomologyTheta_mk]
  exact congrArg relativeBoundaries.mkQ (Subtype.ext (Subtype.ext (stateTheta_involutive _)))

private theorem cohomologyTheta_number (x : RelativeCohomology) :
    cohomologyTheta (cohomologyNumber x) = cohomologyNumber (cohomologyTheta x) := by
  obtain ⟨z, rfl⟩ := relativeBoundaries.mkQ_surjective x
  simp only [cohomologyNumber_mk, cohomologyTheta_mk]
  exact congrArg relativeBoundaries.mkQ (Subtype.ext (Subtype.ext (stateTheta_N (z.1 : State))))

set_option maxHeartbeats 800000 in
-- The quotient identities compare both nested cycle representatives.
private theorem cohomologyTheta_descent (x y : RelativeCohomology) :
    cohomologyTheta (cohomologyDescent x y) =
      cohomologyDescent (cohomologyTheta x) (cohomologyTheta y) := by
  refine Exists.elim (relativeBoundaries.mkQ_surjective x) fun u hu => ?_
  refine Exists.elim (relativeBoundaries.mkQ_surjective y) fun v hv => ?_
  simp only [← hu, ← hv, cohomologyDescent_mk, cohomologyTheta_mk]
  apply congrArg relativeBoundaries.mkQ
  apply Subtype.ext
  apply Subtype.ext
  change stateTheta (descent (u.1 : State) (v.1 : State)) =
    descent (stateTheta (u.1 : State)) (stateTheta (v.1 : State))
  exact stateTheta_descent _ _

private def degreeOneTheta : Module.End ℂ DegreeOne :=
  cohomologyTheta.restrict (by
    intro x hx
    have hn := Module.End.mem_eigenspace_iff.mp hx
    apply Module.End.mem_eigenspace_iff.mpr
    rw [← cohomologyTheta_number, hn, map_smul])

private theorem degreeOneTheta_involutive : Function.Involutive degreeOneTheta :=
  fun x => Subtype.ext (cohomologyTheta_involutive (x : RelativeCohomology))

set_option maxHeartbeats 800000 in
-- Identifying the restricted bracket unfolds the quotient and the grade subtype.
private theorem degreeOneTheta_lie (x y : DegreeOne) :
    degreeOneTheta ⁅x, y⁆ = ⁅degreeOneTheta x, degreeOneTheta y⁆ := by
  apply Subtype.ext
  change cohomologyTheta (cohomologyDescent (x : RelativeCohomology) (y : RelativeCohomology)) =
    cohomologyDescent (cohomologyTheta (x : RelativeCohomology))
      (cohomologyTheta (y : RelativeCohomology))
  exact cohomologyTheta_descent _ _

/-- The charge-reversal Lie automorphism on the actual relative ghost-number-one algebra. -/
def chevalley : DegreeOne ≃ₗ⁅ℂ⁆ DegreeOne :=
  { LinearEquiv.ofInvolutive degreeOneTheta degreeOneTheta_involutive with
    map_lie' := fun {x y} => degreeOneTheta_lie x y }

theorem chevalley_involutive : Function.Involutive chevalley :=
  degreeOneTheta_involutive

set_option maxHeartbeats 1000000 in
-- The physical momentum criterion uses representatives through the quotient and grade subtype.
/-- The automorphism exchanges each native momentum component with its opposite. -/
theorem chevalley_mem_physicalMomentum_iff
    (p : LatticeGeneratingFieldLocality.Charge hyperbolicData) (x : DegreeOne) :
    chevalley x ∈ physicalMomentum (-p) ↔ x ∈ physicalMomentum p := by
  have reverse : ∀ (q : LatticeGeneratingFieldLocality.Charge hyperbolicData) (a : DegreeOne),
      a ∈ physicalMomentum q → chevalley a ∈ physicalMomentum (-q) := by
    intro q a ha
    obtain ⟨z, hz, hp, hn⟩ := (mem_physicalMomentum_iff q a).mp ha
    refine (mem_physicalMomentum_iff (-q) (chevalley a)).mpr ⟨cycleTheta z, ?_, ?_, ?_⟩
    · change relativeBoundaries.mkQ (cycleTheta z) = cohomologyTheta (a : RelativeCohomology)
      rw [← cohomologyTheta_mk, hz]
    · exact stateTheta_mem_fixedMomentum hp
    · change N (stateTheta (z.1 : State)) = stateTheta (z.1 : State)
      rw [← stateTheta_N, hn]
  refine ⟨fun hx => ?_, reverse p x⟩
  simpa only [chevalley_involutive x, neg_neg] using reverse (-p) (chevalley x) hx

set_option maxHeartbeats 800000 in
-- Identifying the current classes compares the cycle, quotient and grade coercions.
/-- Charge reversal negates the native current classes. -/
theorem chevalley_h (i : Fin hyperbolicData.rank) : chevalley (h i) = -h i := by
  apply Subtype.ext
  change cohomologyTheta (relativeBoundaries.mkQ (cartanCycle i)) =
    -relativeBoundaries.mkQ (cartanCycle i)
  rw [cohomologyTheta_mk, ← relativeBoundaries.mkQ.map_neg]
  apply congrArg relativeBoundaries.mkQ
  apply Subtype.ext
  apply Subtype.ext
  change stateTheta ((cartanCycle i).1 : State) = -((cartanCycle i).1 : State)
  rw [cartanCycle_coe, show stateTheta (VirasoroBRST.ghostC matterDatum 1 (momentumCurrent i)) =
      VirasoroBRST.ghostC matterDatum 1 (stateTheta (momentumCurrent i)) from
    stateTheta_liftGhost _ _, stateTheta_momentumCurrent,
    (VirasoroBRST.ghostC matterDatum 1).map_neg]

set_option maxHeartbeats 800000 in
-- Comparing the kernel with the physical momentum subspace uses the nested degree-one subtype.
/-- The involution is minus the identity on the entire momentum-zero Cartan. -/
theorem chevalley_eq_neg_of_zero_momentum (x : DegreeOne)
    (hx : x ∈ physicalMomentum (0 : LatticeGeneratingFieldLocality.Charge hyperbolicData)) :
    chevalley x = -x := by
  let e : Module.End ℂ DegreeOne := chevalley.toLinearEquiv.toLinearMap + LinearMap.id
  have hle : Submodule.span ℂ (Set.range h) ≤ LinearMap.ker e := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply LinearMap.mem_ker.mpr
    change chevalley (h i) + h i = 0
    exact eq_neg_iff_add_eq_zero.mp (chevalley_h i)
  rw [← span_h_eq_physicalMomentum_zero] at hx
  exact eq_neg_iff_add_eq_zero.mpr (LinearMap.mem_ker.mp (hle hx))

#print axioms stateTheta
#print axioms stateTheta_involutive
#print axioms stateTheta_mode
#print axioms stateTheta_Q
#print axioms stateTheta_b
#print axioms stateTheta_L0
#print axioms stateTheta_N
#print axioms stateTheta_descent
#print axioms stateTheta_momentumZeroMode
#print axioms stateTheta_mem_fixedMomentum
#print axioms cycleTheta
#print axioms cohomologyTheta
#print axioms chevalley
#print axioms chevalley_involutive
#print axioms chevalley_mem_physicalMomentum_iff
#print axioms chevalley_h
#print axioms chevalley_eq_neg_of_zero_momentum

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTChevalley
