/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTPhysicalSpectrum
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTPhysicalSpectrum
   mirror-E: none(waiver:algebraic-original-orbifold-brst-physical-spectrum)
   anchors: []
   utility: none
   digest: The fixed-momentum relative BRST quotients and the physical Lie algebra spectrum. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTMomentum
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeSpectrum

/-! The native shell includes into the ambient relative complex. Momentum and ghost-number
projections recover shell boundaries, and homogeneous cycle lifts supply all physical classes. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTPhysicalSpectrum

open OriginalOrbifoldCriticalMatter (Matter State Q b hyperbolicData)
open OriginalOrbifoldBRSTZeroEnergy (FullLabel fullBasis totalL0)
open OriginalOrbifoldBRSTDescent
  (relativeStates relativeDifferential relativeDifferential_square relativeCycles
    relativeBoundaries RelativeCohomology)
open OriginalOrbifoldBRSTPhysicalLie (N DegreeOne number_Q)
open OriginalOrbifoldBRSTMomentum (physicalMomentum mem_physicalMomentum_iff)
open OriginalOrbifoldRelativeMassShell
  (fixedMomentum relativeMassShell differential mem_relativeMassShell_iff)
open OriginalOrbifoldRelativeQuartet
  (shellNumber ghostSector ghostOneCycles ghostOneBoundaries GhostOneCohomology
    ghostOneCohomologyEquiv orbifoldGrade)
open OriginalOrbifoldRelativeSpectrum (ghostOneCohomologyEquiv_zero ghostOneCohomology_finrank)
open LatticeGeneratingFieldLocality (Charge)
open LatticePositiveEnergy (chargeEnergy)
open LatticeRelativeMassShell (massShellCutoff)
open D5.S3.HomologicalAlgebra.FinitePerturbation (boundaryMap)
open D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus (diagonal diagonal_coefficient)
open D5.S3.Quantum.Fermionic.BcGhostCharge (charge)

open private number_basis number_coordinate from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTPhysicalLie
open private momentumPart_mem momentumPart_of_mem relativePart relativePart_chain
  class_mem_grade_one from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTMomentum

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private abbrev UCharge := Charge hyperbolicData

private theorem mem_shell (a : UCharge) (x : State) :
    x ∈ relativeMassShell a ↔ x ∈ fixedMomentum a ∧ x ∈ relativeStates := by
  change (x ∈ fixedMomentum a ∧ b 0 x = 0) ∧ totalL0 x = 0 ↔
    x ∈ fixedMomentum a ∧ (b 0 x = 0 ∧ totalL0 x = 0)
  exact and_assoc

private def numberPart (p : ℤ) : Module.End ℂ State :=
  diagonal fullBasis fun (i : FullLabel) => if charge i.2.2 = p then 1 else 0

private theorem numberPart_coeff (p : ℤ) (x : State) (i : FullLabel) :
    fullBasis.repr (numberPart p x) i =
      if charge i.2.2 = p then fullBasis.repr x i else 0 := by
  rw [numberPart, diagonal_coefficient]
  split_ifs <;> simp only [one_mul, zero_mul]

private theorem numberPart_mem_shell (a : UCharge) (p : ℤ) {x : State}
    (hx : x ∈ relativeMassShell a) : numberPart p x ∈ relativeMassShell a := by
  apply (mem_relativeMassShell_iff a _).mpr
  intro i hi
  apply (mem_relativeMassShell_iff a x).mp hx i
  intro h
  apply hi
  rw [numberPart_coeff, h]
  split_ifs <;> rfl

private theorem numberPart_eigen (p : ℤ) (x : State) :
    N (numberPart p x) = (p : ℂ) • numberPart p x := by
  apply fullBasis.repr.injective
  ext i
  rw [number_coordinate, map_smul, Finsupp.smul_apply, smul_eq_mul, numberPart_coeff]
  by_cases hi : charge i.2.2 = p <;> simp only [hi, ite_true, ite_false, mul_zero]

private theorem numberPart_of_eigen (p q : ℤ) (x : State)
    (hx : N x = (q : ℂ) • x) : numberPart p x = if q = p then x else 0 := by
  apply fullBasis.repr.injective
  ext i
  have hcoeff (hi : charge i.2.2 ≠ q) : fullBasis.repr x i = 0 := by
    have h := congrArg (fun y : State => fullBasis.repr y i) hx
    change fullBasis.repr (N x) i = fullBasis.repr ((q : ℂ) • x) i at h
    rw [number_coordinate, map_smul, Finsupp.smul_apply, smul_eq_mul] at h
    have hz : ((charge i.2.2 : ℂ) - (q : ℂ)) * fullBasis.repr x i = 0 := by
      rw [sub_mul, h, sub_self]
    exact (mul_eq_zero.mp hz).resolve_left
      (sub_ne_zero.mpr fun he => hi (Int.cast_injective he))
  rw [numberPart_coeff]
  by_cases hi : charge i.2.2 = q
  · rw [hi]
    by_cases h : q = p
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h, fullBasis.repr.map_zero, Finsupp.zero_apply]
  · rw [hcoeff hi]
    have hzero : (if charge i.2.2 = p then (0 : ℂ) else 0) = 0 := by split_ifs <;> rfl
    rw [hzero]
    by_cases h : q = p
    · rw [ite_eq_left h, hcoeff hi]
    · rw [ite_eq_right h, fullBasis.repr.map_zero, Finsupp.zero_apply]

private theorem numberPart_Q : (numberPart 1).comp Q = Q.comp (numberPart 0) := by
  apply fullBasis.ext
  intro i
  have hi : N (Q (fullBasis i)) = ((charge i.2.2 + 1 : ℤ) : ℂ) • Q (fullBasis i) := by
    rw [number_Q, number_basis, map_smul, Int.cast_add, Int.cast_one, add_smul, one_smul]
  rw [LinearMap.comp_apply, LinearMap.comp_apply, numberPart_of_eigen 1 _ _ hi,
    numberPart_of_eigen 0 _ _ (number_basis i)]
  by_cases h : charge i.2.2 = 0
  · simp [h]
  · have h' : charge i.2.2 + 1 ≠ 1 := by omega
    simp [h, h']

private theorem cycle_number_one (a : UCharge) (z : ghostOneCycles a) :
    N (z.1 : State) = (z.1 : State) := by
  have he : shellNumber a z.1 = ((1 : ℤ) : ℂ) • z.1 :=
    Module.End.mem_eigenspace_iff.mp z.property.1
  have h : shellNumber a z.1 = z.1 := by simpa only [Int.cast_one, one_smul] using he
  exact congrArg (fun w : relativeMassShell a => (w : State)) h

private def shellToRelative (a : UCharge) : relativeMassShell a →ₗ[ℂ] relativeStates :=
  Submodule.inclusion fun x hx => ((mem_shell a x).mp hx).2

/-- A shell ghost-one cycle as a cycle in the ambient relative complex. -/
def ghostOneCycleToRelative (a : UCharge) : ghostOneCycles a →ₗ[ℂ] relativeCycles :=
  ((shellToRelative a).comp (ghostOneCycles a).subtype).codRestrict relativeCycles (by
    intro z
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change Q (z.1 : State) = 0
    exact congrArg (fun w : relativeMassShell a => (w : State))
      (LinearMap.mem_ker.mp z.property.2))

set_option maxHeartbeats 800000 in
-- The projected preimage passes through the relative-state and shell subtypes.
private theorem ambient_boundary_iff (a : UCharge) (z : ghostOneCycles a) :
    ghostOneCycleToRelative a z ∈ relativeBoundaries ↔ z ∈ ghostOneBoundaries a := by
  constructor
  · intro hz
    change ∃ u : relativeStates,
      boundaryMap (R := ℂ) relativeDifferential relativeDifferential_square u =
        ghostOneCycleToRelative a z at hz
    obtain ⟨u, hu⟩ := hz
    let v : relativeStates := relativePart a u
    have hv : (v : State) ∈ relativeMassShell a :=
      (mem_shell a _).mpr ⟨momentumPart_mem a _, v.property⟩
    have huz : relativeDifferential u = (ghostOneCycleToRelative a z).1 :=
      congrArg (fun w : relativeCycles => w.1) hu
    have hQv : Q (v : State) = (z.1 : State) := by
      have hc := LinearMap.congr_fun (relativePart_chain a) u
      calc
        Q (v : State) = (relativePart a (relativeDifferential u) : State) :=
          congrArg (fun w : relativeStates => (w : State)) hc.symm
        _ = (z.1 : State) := by
          rw [huz]
          exact momentumPart_of_mem ((mem_shell a _).mp z.1.property).1
    let w : relativeMassShell a := ⟨numberPart 0 (v : State), numberPart_mem_shell a 0 hv⟩
    have hw : w ∈ ghostSector a 0 := by
      apply Module.End.mem_eigenspace_iff.mpr
      apply Subtype.ext
      change N (numberPart 0 (v : State)) = ((0 : ℤ) : ℂ) • numberPart 0 (v : State)
      exact numberPart_eigen 0 (v : State)
    have hzEigen : N (z.1 : State) = ((1 : ℤ) : ℂ) • (z.1 : State) := by
      simpa only [Int.cast_one, one_smul] using cycle_number_one a z
    have hQw : Q (w : State) = (z.1 : State) := by
      calc
        Q (w : State) = numberPart 1 (Q (v : State)) :=
          (LinearMap.congr_fun numberPart_Q (v : State)).symm
        _ = (z.1 : State) := by rw [hQv, numberPart_of_eigen 1 1 _ hzEigen, ite_eq_left rfl]
    unfold ghostOneBoundaries
    exact LinearMap.mem_range.mpr ⟨⟨w, hw⟩, Subtype.ext (Subtype.ext hQw)⟩
  · intro hz
    unfold ghostOneBoundaries at hz
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hz
    have hQw : Q (w.1 : State) = (z.1 : State) :=
      congrArg (fun y : ghostOneCycles a => (y.1 : State)) hw
    change ∃ u : relativeStates,
      boundaryMap (R := ℂ) relativeDifferential relativeDifferential_square u =
        ghostOneCycleToRelative a z
    exact ⟨shellToRelative a w.1, Subtype.ext (Subtype.ext hQw)⟩

set_option maxHeartbeats 800000 in
-- The two codomain restrictions elaborate through the ambient relative quotient.
private def cycleToPhysicalMomentum (a : UCharge) : ghostOneCycles a →ₗ[ℂ] physicalMomentum a :=
  let cl : ghostOneCycles a →ₗ[ℂ] RelativeCohomology :=
    relativeBoundaries.mkQ.comp (ghostOneCycleToRelative a)
  let f : ghostOneCycles a →ₗ[ℂ] DegreeOne :=
    cl.codRestrict _ fun z => class_mem_grade_one _ (cycle_number_one a z)
  f.codRestrict _ fun z => (mem_physicalMomentum_iff a (f z)).mpr
    ⟨ghostOneCycleToRelative a z, rfl, ((mem_shell a _).mp z.1.property).1, cycle_number_one a z⟩

set_option maxHeartbeats 800000 in
-- The vanishing proof compares two nested subtypes with the ambient quotient.
private def shellToPhysicalMomentum (a : UCharge) :
    GhostOneCohomology a →ₗ[ℂ] physicalMomentum a :=
  (ghostOneBoundaries a).liftQ (cycleToPhysicalMomentum a) (by
    intro z hz
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    apply Subtype.ext
    change relativeBoundaries.mkQ (ghostOneCycleToRelative a z) = 0
    exact (Submodule.Quotient.mk_eq_zero (p := relativeBoundaries)).mpr
      ((ambient_boundary_iff a z).mpr hz))

set_option maxHeartbeats 800000 in
-- The homogeneous representative is repackaged in the nested shell and cycle carriers.
private theorem shellToPhysicalMomentum_surjective (a : UCharge) (x : physicalMomentum a) :
    ∃ q : GhostOneCohomology a, shellToPhysicalMomentum a q = x := by
  let xp : DegreeOne := x.1
  have hLift : ∃ z : relativeCycles,
      relativeBoundaries.mkQ z = (xp : RelativeCohomology) ∧
        (z.1 : State) ∈ fixedMomentum a ∧ N (z.1 : State) = (z.1 : State) :=
    (mem_physicalMomentum_iff a xp).mp x.property
  rcases hLift with ⟨z, hz, hm, hn⟩
  let w : relativeMassShell a := ⟨(z.1 : State), (mem_shell a _).mpr ⟨hm, z.1.property⟩⟩
  have hw : w ∈ ghostOneCycles a := by
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, LinearMap.mem_ker.mpr ?_⟩
    · apply Subtype.ext
      change N (z.1 : State) = ((1 : ℤ) : ℂ) • (z.1 : State)
      simpa only [Int.cast_one, one_smul] using hn
    · exact Subtype.ext (congrArg (fun y : relativeStates => (y : State))
        (LinearMap.mem_ker.mp z.property))
  let y : ghostOneCycles a := ⟨w, hw⟩
  have hy : ghostOneCycleToRelative a y = z := Subtype.ext (Subtype.ext rfl)
  refine ⟨(ghostOneBoundaries a).mkQ y, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change relativeBoundaries.mkQ (ghostOneCycleToRelative a y) = (xp : RelativeCohomology)
  exact (congrArg relativeBoundaries.mkQ hy).trans hz

set_option maxHeartbeats 800000 in
-- Quotient representatives are compared after projecting through both subtypes.
private theorem shellToPhysicalMomentum_bijective (a : UCharge) :
    Function.Bijective (shellToPhysicalMomentum a) := by
  constructor
  · apply (injective_iff_map_eq_zero (shellToPhysicalMomentum a)).mpr
    intro x
    refine Submodule.Quotient.induction_on (ghostOneBoundaries a)
      (C := fun x : GhostOneCohomology a => shellToPhysicalMomentum a x = 0 → x = 0) x ?_
    intro z hz
    have h : relativeBoundaries.mkQ (ghostOneCycleToRelative a z) = 0 :=
      congrArg (fun y : physicalMomentum a => (y.1 : RelativeCohomology)) hz
    have hb : ghostOneCycleToRelative a z ∈ relativeBoundaries :=
      (Submodule.Quotient.mk_eq_zero (p := relativeBoundaries)).mp h
    exact (Submodule.Quotient.mk_eq_zero (p := ghostOneBoundaries a)).mpr
      ((ambient_boundary_iff a z).mp hb)
  · exact shellToPhysicalMomentum_surjective a

/-- The native ghost-one quotient identifies with the degree-one physical momentum subspace. -/
def ghostOneCohomologyEquivPhysicalMomentum (a : UCharge) :
    GhostOneCohomology a ≃ₗ[ℂ] physicalMomentum a :=
  LinearEquiv.ofBijective (shellToPhysicalMomentum a) (shellToPhysicalMomentum_bijective a)

/-- The equivalence takes a shell cycle to the ambient relative class of the same cycle. -/
theorem ghostOneCohomologyEquivPhysicalMomentum_apply_mk (a : UCharge) (z : ghostOneCycles a) :
    ((ghostOneCohomologyEquivPhysicalMomentum a ((ghostOneBoundaries a).mkQ z)).1 :
      RelativeCohomology) = relativeBoundaries.mkQ (ghostOneCycleToRelative a z) := rfl

/-- At zero momentum the physical space is the pair of coordinates of the null shell. -/
def physicalMomentumEquivZero : physicalMomentum (0 : UCharge) ≃ₗ[ℂ] (Fin 2 → ℂ) :=
  (ghostOneCohomologyEquivPhysicalMomentum 0).symm.trans ghostOneCohomologyEquiv_zero

/-- At nonzero on-shell momentum the physical space is the corresponding orbifold grade. -/
def physicalMomentumEquivOrbifoldGrade (a : UCharge) (ha : a ≠ 0)
    (he : chargeEnergy hyperbolicData a ≤ 1) :
    physicalMomentum a ≃ₗ[ℂ] orbifoldGrade (massShellCutoff hyperbolicData a) :=
  (ghostOneCohomologyEquivPhysicalMomentum a).symm.trans (ghostOneCohomologyEquiv a ha he)

/-- The dimension of every momentum component of the degree-one physical Lie algebra. -/
theorem physicalMomentum_finrank (a : UCharge) :
    Module.finrank ℂ (physicalMomentum a) =
      if a = 0 then 2
      else if a 0 * a 1 ≤ 1 then Module.finrank ℂ (orbifoldGrade (1 - a 0 * a 1).toNat)
      else 0 :=
  ((ghostOneCohomologyEquivPhysicalMomentum a).finrank_eq).symm.trans
    (ghostOneCohomology_finrank a)

#print axioms ghostOneCycleToRelative
#print axioms ghostOneCohomologyEquivPhysicalMomentum
#print axioms ghostOneCohomologyEquivPhysicalMomentum_apply_mk
#print axioms physicalMomentumEquivZero
#print axioms physicalMomentumEquivOrbifoldGrade
#print axioms physicalMomentum_finrank

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTPhysicalSpectrum
