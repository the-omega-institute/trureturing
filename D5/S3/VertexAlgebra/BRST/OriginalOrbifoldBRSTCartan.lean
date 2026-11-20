/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTCartan
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTCartan
   mirror-E: none(waiver:algebraic-original-orbifold-brst-cartan)
   anchors: []
   utility: none
   digest: The actual Cartan classes and their momentum action in the original BRST Lie algebra. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTMomentum
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeSpectrum

/-! The native hyperbolic currents acquire relative ghost number one by applying `c(1)`.
Their descent removes that ghost and acts by the native momentum zero modes. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTCartan

open D5.S3.Quantum.Fermionic
open OriginalOrbifoldCriticalMatter (Matter State Q b matterDatum hyperbolicData)
open OriginalOrbifoldBRSTZeroEnergy (totalL0)
open OriginalOrbifoldBRSTStateField (Y)
open OriginalOrbifoldBRSTDescent (relativeStates relativeCycles
  relativeBoundaries RelativeCohomology descent cycleDescent cohomologyDescent cohomologyDescent_mk)
open OriginalOrbifoldBRSTPhysicalLie (N DegreeOne degreeOne_bracket)
open OriginalOrbifoldBRSTMomentum (momentumCurrent momentumZeroMode physicalMomentum
  mem_physicalMomentum_iff mem_fixedMomentum_iff_zero_modes)
open OriginalOrbifoldRelativeMassShell (fixedMomentum relativeMassShell)
open OriginalOrbifoldRelativeNull (ShellIndex bottom middle top shellVector shellBasis
  shellBasis_coe shellCoordinates ghostNumber ghostNumber_shellVector Q_middle)
open OriginalOrbifoldRelativeQuartet (ghostOneCycles)
open LatticeGeneratingFieldLocality (Charge bilinear)
open LatticeFiniteNegativeGeneration (neutralField neutralPolynomialMode)
open LatticePositiveEnergy (chargeEnergy_zero)

open private opposite class_mem_grade_one from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTMomentum
open private shellVector_middle from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeNull
open private cycle_closed from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTDescent
open private mem_ghostOneCycles_zero_iff from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeSpectrum

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private abbrev UCharge := Charge hyperbolicData

private abbrev zeroShellBasis : Module.Basis ShellIndex ℂ (relativeMassShell (0 : UCharge)) :=
  shellBasis 0 (chargeEnergy_zero hyperbolicData)

private abbrev cartanState (i : Fin hyperbolicData.rank) : State :=
  VirasoroBRST.ghostC matterDatum 1 (momentumCurrent i)

private theorem cartanState_eq_shellVector (i : Fin hyperbolicData.rank) :
    cartanState i = shellVector 0 (middle (opposite i)) := by
  have hmode : neutralPolynomialMode hyperbolicData (opposite i) 0 (-1) =
      LinearMap.mulLeft ℂ (MvPolynomial.X (opposite i, 0)) :=
    LatticeSugawaraCurrents.neutralPolynomialMode_negative hyperbolicData (opposite i) 0 0
  simp only [cartanState, momentumCurrent, VirasoroBRST.ghostC, BcGhostChargeTensor.C,
    BcGhostChargeTensor.liftGhost, TensorProduct.map_tmul, LinearMap.id_apply,
    BcGhostFock.ghost_vacuum.2.2.1, shellVector_middle, LatticeAllStateField.vacuum,
    LatticeSugawaraCurrents.neutralField_ncoeff, LatticeSugawaraCurrents.neutralMode_single,
    hmode, LinearMap.mulLeft_apply, mul_one]

private theorem cartanState_mem_shell (i : Fin hyperbolicData.rank) :
    cartanState i ∈ relativeMassShell (0 : UCharge) := by
  rw [cartanState_eq_shellVector, ← shellBasis_coe 0 (chargeEnergy_zero hyperbolicData)]
  exact (zeroShellBasis (middle (opposite i))).property

private theorem cartanState_closed (i : Fin hyperbolicData.rank) : Q (cartanState i) = 0 := by
  rw [cartanState_eq_shellVector, Q_middle 0 (chargeEnergy_zero hyperbolicData)]
  simp [LatticeSugawaraVirasoro.chargeScalar, bilinear]

private theorem cartanState_number (i : Fin hyperbolicData.rank) :
    N (cartanState i) = cartanState i := by
  rw [cartanState_eq_shellVector]
  simpa only [show ghostNumber (middle (opposite i)) = 1 from rfl, Nat.cast_one, one_smul]
    using ghostNumber_shellVector 0 (middle (opposite i))

/-- The native current with `c(1)` is an actual relative BRST cycle. -/
def cartanCycle (i : Fin hyperbolicData.rank) : relativeCycles := by
  have hm := cartanState_mem_shell i
  change (cartanState i ∈ fixedMomentum 0 ∧ b 0 (cartanState i) = 0) ∧
    totalL0 (cartanState i) = 0 at hm
  let u : relativeStates := ⟨cartanState i, ⟨hm.1.2, hm.2⟩⟩
  exact ⟨u, LinearMap.mem_ker.mpr (Subtype.ext (cartanState_closed i))⟩

theorem cartanCycle_coe (i : Fin hyperbolicData.rank) :
    ((cartanCycle i).1 : State) = VirasoroBRST.ghostC matterDatum 1 (momentumCurrent i) := rfl

/-- The ghost-number-one relative class of the current dual to momentum coordinate `i`. -/
def h (i : Fin hyperbolicData.rank) : DegreeOne :=
  ⟨relativeBoundaries.mkQ (cartanCycle i),
    class_mem_grade_one (cartanCycle i) (cartanState_number i)⟩

/-- Each of the two current classes belongs to the native momentum-zero sector. -/
theorem h_mem_physicalMomentum_zero (i : Fin hyperbolicData.rank) :
    h i ∈ physicalMomentum (0 : UCharge) := by
  have hm := cartanState_mem_shell i
  change (cartanState i ∈ fixedMomentum 0 ∧ b 0 (cartanState i) = 0) ∧
    totalL0 (cartanState i) = 0 at hm
  exact (mem_physicalMomentum_iff 0 (h i)).mpr
    ⟨cartanCycle i, rfl, hm.1.1, cartanState_number i⟩

private theorem b_cartanState (i : Fin hyperbolicData.rank) :
    b (-1) (cartanState i) = momentumCurrent i := by
  let vacuum := CountableOccupationFock.vacuum
  have hb : BcGhostFock.b (-1) vacuum = 0 := BcGhostFock.ghost_vacuum.1 (-1) le_rfl
  have car := LinearMap.congr_fun (BcGhostFock.ghost_mixed_car (-1) 1) vacuum
  rw [ite_eq_left (by decide : (-1 : ℤ) + 1 = 0)] at car
  have hcancel : BcGhostFock.b (-1) (BcGhostFock.c 1 vacuum) = vacuum := by
    simpa only [LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply,
      hb, map_zero, add_zero] using car
  change BcGhostChargeTensor.B (-1) (BcGhostChargeTensor.C 1 (momentumCurrent i)) = _
  simp only [momentumCurrent, BcGhostChargeTensor.B, BcGhostChargeTensor.C,
    BcGhostChargeTensor.liftGhost, TensorProduct.map_tmul, LinearMap.id_apply, hcancel, vacuum]

/-- Descent by the relative cycle is the native momentum zero mode on the original states. -/
theorem descent_cartanCycle (i : Fin hyperbolicData.rank) :
    descent ((cartanCycle i).1 : State) = momentumZeroMode i := by
  rw [cartanCycle_coe]
  change (Y (b (-1) (cartanState i)))[[0]] = (Y (momentumCurrent i))[[0]]
  rw [b_cartanState]

private theorem cycleDescent_cartanCycle_eq_smul (i : Fin hyperbolicData.rank) (p : UCharge)
    (z : relativeCycles) (hp : (z.1 : State) ∈ fixedMomentum p) :
    cycleDescent (cartanCycle i) z = (p i : ℂ) • z := by
  apply Subtype.ext
  apply Subtype.ext
  change descent ((cartanCycle i).1 : State) (z.1 : State) = (p i : ℂ) • (z.1 : State)
  calc
    _ = momentumZeroMode i (z.1 : State) :=
      LinearMap.congr_fun (descent_cartanCycle i) (z.1 : State)
    _ = _ := (mem_fixedMomentum_iff_zero_modes p (z.1 : State)).mp hp i

set_option maxHeartbeats 1600000 in
-- Extracting a homogeneous representative and identifying its bracket in the quotient
-- require elaborating the nested cycle and grade subtypes.
/-- The physical Lie adjoint action reads the indicated integral momentum coordinate. -/
theorem lie_h_eq_momentum_smul (i : Fin hyperbolicData.rank) (p : UCharge) (x : DegreeOne)
    (hx : x ∈ physicalMomentum p) : ⁅h i, x⁆ = (p i : ℂ) • x := by
  let cl : relativeCycles →ₗ[ℂ] RelativeCohomology := relativeBoundaries.mkQ
  have hLift : ∃ z : relativeCycles, cl z = (x : RelativeCohomology) ∧
      (z.1 : State) ∈ fixedMomentum p ∧ N (z.1 : State) = (z.1 : State) :=
    (mem_physicalMomentum_iff p x).mp hx
  obtain ⟨z, hz, hp, _⟩ := hLift
  let adj : Module.End ℂ RelativeCohomology := cohomologyDescent (cl (cartanCycle i))
  apply Subtype.ext
  change (↑⁅h i, x⁆ : RelativeCohomology) = (p i : ℂ) • (x : RelativeCohomology)
  calc
    _ = adj (x : RelativeCohomology) := degreeOne_bracket (h i) x
    _ = adj (cl z) := congrArg adj hz.symm
    _ = cl (cycleDescent (cartanCycle i) z) := cohomologyDescent_mk (cartanCycle i) z
    _ = cl ((p i : ℂ) • z) := congrArg cl (cycleDescent_cartanCycle_eq_smul i p z hp)
    _ = (p i : ℂ) • cl z := cl.map_smul (p i : ℂ) z
    _ = _ := congrArg (fun q : RelativeCohomology => (p i : ℂ) • q) hz

set_option maxHeartbeats 800000 in
-- Transferring the null-shell basis expansion to the nested relative cycle subtype is costly.
private theorem zero_relativeCycle_combination (z : relativeCycles)
    (hp : (z.1 : State) ∈ fixedMomentum (0 : UCharge)) (hn : N (z.1 : State) = (z.1 : State)) :
    ∃ a b : ℂ, z = a • cartanCycle 0 + b • cartanCycle 1 := by
  have hr : b 0 (z.1 : State) = 0 ∧ totalL0 (z.1 : State) = 0 := z.1.property
  let w : relativeMassShell (0 : UCharge) := ⟨(z.1 : State), ⟨⟨hp, hr.1⟩, hr.2⟩⟩
  have hw : w ∈ ghostOneCycles (0 : UCharge) := by
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, LinearMap.mem_ker.mpr ?_⟩
    · apply Subtype.ext
      change N (z.1 : State) = ((1 : ℤ) : ℂ) • (z.1 : State)
      simpa only [Int.cast_one, one_smul] using hn
    · exact Subtype.ext (cycle_closed z)
  let e := shellCoordinates (0 : UCharge) (chargeEnergy_zero hyperbolicData)
  obtain ⟨hbottom, htop⟩ := (mem_ghostOneCycles_zero_iff w).mp hw
  change e w bottom = 0 at hbottom
  change e w top = 0 at htop
  refine ⟨e w (middle 1), e w (middle 0), ?_⟩
  have hrep : w = e w (middle 1) • zeroShellBasis (middle 1) +
      e w (middle 0) • zeroShellBasis (middle 0) := by
    apply e.injective
    rw [map_add, map_smul, map_smul]
    funext k
    change e w k = e w (middle 1) * zeroShellBasis.equivFun (zeroShellBasis (middle 1)) k +
      e w (middle 0) * zeroShellBasis.equivFun (zeroShellBasis (middle 0)) k
    rw [Module.Basis.equivFun_self, Module.Basis.equivFun_self]
    rcases k with (⟨⟩ | (j | ⟨⟩))
    · simp [middle, hbottom]
    · fin_cases j <;> simp [middle]
    · simp [middle, htop]
  apply Subtype.ext
  apply Subtype.ext
  change (w : State) = e w (middle 1) • cartanState 0 + e w (middle 0) • cartanState 1
  have hstate := congrArg (fun y : relativeMassShell (0 : UCharge) => (y : State)) hrep
  simpa only [Submodule.coe_add, Submodule.coe_smul, zeroShellBasis, shellBasis_coe,
    cartanState_eq_shellVector, show opposite 0 = 1 by decide, show opposite 1 = 0 by decide]
    using hstate

set_option maxHeartbeats 800000 in
-- Comparing the basis expansion in cohomology requires elaborating the quotient and grade subtype.
/-- The two ghost-one current classes span the entire native momentum-zero sector. -/
theorem span_h_eq_physicalMomentum_zero :
    Submodule.span ℂ (Set.range h) = physicalMomentum (0 : UCharge) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact h_mem_physicalMomentum_zero i
  · intro x hx
    obtain ⟨z, hz, hp, hn⟩ := (mem_physicalMomentum_iff 0 x).mp hx
    obtain ⟨a, b, hrep⟩ := zero_relativeCycle_combination z hp hn
    have hclass := congrArg relativeBoundaries.mkQ hrep
    simp only [map_add, map_smul] at hclass
    have hx' : x = a • h 0 + b • h 1 := Subtype.ext (hz.symm.trans hclass)
    rw [hx']
    exact Submodule.add_mem _
      (Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_range_self 0)))
      (Submodule.smul_mem _ b (Submodule.subset_span (Set.mem_range_self 1)))

#print axioms cartanCycle
#print axioms cartanCycle_coe
#print axioms h
#print axioms h_mem_physicalMomentum_zero
#print axioms descent_cartanCycle
#print axioms lie_h_eq_momentum_smul
#print axioms span_h_eq_physicalMomentum_zero

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTCartan
