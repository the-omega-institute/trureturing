/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeQuartet
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeQuartet
   mirror-E: none(waiver:algebraic-original-orbifold-relative-quartet)
   anchors: []
   utility: none
   digest: The native quartet at fixed nonzero hyperbolic momentum in the actual Leech orbifold. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeMassShell
import D5.S3.VertexAlgebra.Lattice.LatticeRelativeBRSTGround
import D5.S3.VertexAlgebra.Lattice.LatticeRelativeBRSTCohomology
import D5.S3.VertexAlgebra.Lattice.LatticeNullFrameExistence
import D5.S3.HomologicalAlgebra.FinitePerturbationCohomology

/-! The quartet contraction and its range on the native relative mass shell. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open scoped TensorProduct

namespace D5.S3.VertexAlgebra.OriginalOrbifoldRelativeQuartet

open OriginalOrbifoldCriticalMatter
open OriginalOrbifoldBRSTZeroEnergy (OrbifoldLabel FullLabel orbifoldBasis fullBasis)
open OriginalOrbifoldRelativeMassShell
open LatticeGeneratingFieldLocality (Charge)
open LatticeLightConeCoordinates (NullFrame)
open LatticePositiveEnergy (chargeEnergy oscillatorEnergy)
open LatticeQuartetContraction (d0 d0_square)
open D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus (ac)
open LatticeQuartetContraction (h P0 ghostB0 chargeProject)
open D5.S3.Quantum.Fermionic.CountableOccupationFock (Fock ket)
open D5.S3.Quantum.Fermionic.BcGhostRelativeEnergy (level level_cast relativeEnergy)
open private orbifoldSlice orbifoldSlice_tmul orbifoldSlice_coeff fullBasis_apply from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeMassShell
open private mem_fixedMomentum_iff_chargeProject originalEnergy originalEnergy_d0
  originalEnergy_R originalEnergy_invM chargeProject_h from
  D5.S3.VertexAlgebra.Lattice.LatticeRelativeBRSTGround

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

abbrev UCharge := Charge hyperbolicData
abbrev UState := LatticeMatterGhostCoupling.State hyperbolicData
abbrev Frame := NullFrame hyperbolicData

/-- The transverse basis of the rank-two lattice is indexed by the empty type. -/
abbrev transverseBasis (F : Frame) : Module.Basis (Fin 0) ℂ F.K := F.transverseBasis

theorem exists_frame (a : UCharge) (ha : a ≠ 0) :
    ∃ F : Frame, F.pPlus a ≠ 0 :=
  LatticeNullFrameExistence.exists_nullFrame_pPlus_ne_zero hyperbolicData
    hyperbolicInverse hyperbolic_inverse_left (by decide) a ha

private abbrev uEnergy : Module.End ℂ UState := originalEnergy hyperbolicData hyperbolicInverse

private abbrev uCoeff := LatticeRelativeMassShell.coeff hyperbolicData
private abbrev ULabel := LatticeRelativeMassShell.TensorLabel hyperbolicData

private theorem uEnergy_coeff (x : UState) (i : ULabel) :
    uCoeff (uEnergy x) i =
      (LatticeRelativeMassShell.totalEnergy hyperbolicData i : ℂ) * uCoeff x i :=
  LatticeRelativeMassShell.totalL0_coeff hyperbolicData hyperbolicInverse
    hyperbolic_inverse_left hyperbolic_inverse_right x i

private theorem uEnergy_eigen_iff (n : ℕ) (x : UState) :
    uEnergy x = (-(n : ℂ)) • x ↔
      ∀ i : ULabel, uCoeff x i ≠ 0 →
        LatticeRelativeMassShell.totalEnergy hyperbolicData i = -(n : ℤ) := by
  let e := LatticeRelativeMassShell.tensorCoeffEquiv hyperbolicData
  constructor
  · intro hx i hi
    have h := congrArg (fun y => e y i) hx
    change uCoeff (uEnergy x) i = e ((-(n : ℂ)) • x) i at h
    rw [uEnergy_coeff, e.map_smul, Finsupp.smul_apply, smul_eq_mul] at h
    have hn := mul_right_cancel₀ hi h
    exact_mod_cast hn
  · intro hx
    apply e.injective
    ext i
    change uCoeff (uEnergy x) i = e ((-(n : ℂ)) • x) i
    rw [uEnergy_coeff, e.map_smul, Finsupp.smul_apply, smul_eq_mul]
    by_cases hi : uCoeff x i = 0
    · change uCoeff x i = 0 at hi
      change _ * uCoeff x i = _ * uCoeff x i
      simp [hi]
    · rw [hx i hi, Int.cast_neg, Int.cast_natCast]
      rfl

private theorem mem_shell_iff_slices (a : UCharge) (x : State) :
    x ∈ relativeMassShell a ↔ ∀ j : OrbifoldLabel,
      chargeProject a (orbifoldSlice j x) = orbifoldSlice j x ∧
      ghostB0 (orbifoldSlice j x) = 0 ∧
      uEnergy (orbifoldSlice j x) = (-(j.1 : ℂ)) • orbifoldSlice j x := by
  rw [mem_relativeMassShell_iff]
  simp only [← mem_fixedMomentum_iff_chargeProject, LatticeRelativeMassShell.mem_fixedMomentum_iff,
    show (ghostB0 : Module.End ℂ UState) =
      LatticeMatterGhostCoupling.ghostB hyperbolicData 0 from rfl,
    LatticeRelativeMassShell.ghostB_zero_iff, uEnergy_eigen_iff]
  simp only [orbifoldSlice_coeff]
  have henergy (j : OrbifoldLabel) (i : ULabel) (ha : i.1.1 = a) :
      LatticeRelativeMassShell.totalEnergy hyperbolicData i = -(j.1 : ℤ) ↔
        ((j.1 + oscillatorEnergy i.1.2 + level i.2 : ℕ) : ℤ) =
          1 - chargeEnergy hyperbolicData a := by
    simp only [LatticeRelativeMassShell.totalEnergy, LatticePositiveEnergy.energy,
      D5.S3.Quantum.Fermionic.BcGhostRelativeEnergy.relativeEnergy, Nat.cast_add, level_cast, ha]
    omega
  constructor
  · intro hx j
    refine ⟨fun i hm => ?_, fun i hb => ?_, fun i hi => ?_⟩
    · exact not_not.mp fun hi => hm (hx (j, i) hi).1
    · exact not_not.mp fun hi => (hx (j, i) hi).2.1 hb
    · have h := hx (j, i) hi
      exact (henergy j i h.1).mpr h.2.2
  · intro hx i hi
    obtain ⟨hm, hb, he⟩ := hx i.1
    have ha := not_ne_iff.mp (fun hn => hi (hm i.2 hn))
    exact ⟨ha, fun h => hi (hb i.2 h), (henergy i.1 i.2 ha).mp (he i.2 hi)⟩

private abbrev assoc := TensorProduct.assoc ℂ Orbifold Hyperbolic Fock

/-- Extend a native hyperbolic-matter–ghost operator by the identity on the orbifold. -/
def lift (A : Module.End ℂ UState) : Module.End ℂ State :=
  assoc.symm.toLinearMap.comp ((A.lTensor Orbifold).comp assoc.toLinearMap)

private theorem slice_assoc_tmul (j : OrbifoldLabel) (u : Orbifold) (v : UState) :
    orbifoldSlice j (assoc.symm (u ⊗ₜ[ℂ] v)) = orbifoldBasis.repr u j • v := by
  change TensorProduct.equivFinsuppOfBasisLeft orbifoldBasis
    (assoc (assoc.symm (u ⊗ₜ[ℂ] v))) j = _
  rw [LinearEquiv.apply_symm_apply, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]

private theorem lift_assoc_tmul (A : Module.End ℂ UState) (u : Orbifold) (v : UState) :
    lift A (assoc.symm (u ⊗ₜ[ℂ] v)) = assoc.symm (u ⊗ₜ[ℂ] A v) := by
  simp only [lift, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    LinearMap.lTensor_tmul]

private theorem slice_lift (A : Module.End ℂ UState) (j : OrbifoldLabel) (x : State) :
    orbifoldSlice j (lift A x) = A (orbifoldSlice j x) := by
  have he : ((orbifoldSlice j).comp (lift A)).comp assoc.symm.toLinearMap =
      (A.comp (orbifoldSlice j)).comp assoc.symm.toLinearMap := by
    apply TensorProduct.ext'
    intro u v
    change orbifoldSlice j (lift A (assoc.symm (u ⊗ₜ[ℂ] v))) =
      A (orbifoldSlice j (assoc.symm (u ⊗ₜ[ℂ] v)))
    rw [lift_assoc_tmul, slice_assoc_tmul, slice_assoc_tmul, map_smul]
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using
    LinearMap.congr_fun he (assoc x)

private theorem lift_mem_shell (a : UCharge) (A : Module.End ℂ UState)
    (hc : chargeProject a * A = A * chargeProject a)
    (hb : ∀ y : UState, ghostB0 y = 0 → ghostB0 (A y) = 0)
    (he : uEnergy * A = A * uEnergy) (x : State) (hx : x ∈ relativeMassShell a) :
    lift A x ∈ relativeMassShell a := by
  apply (mem_shell_iff_slices a _).mpr
  intro j
  obtain ⟨hcj, hbj, hej⟩ := (mem_shell_iff_slices a x).mp hx j
  rw [slice_lift]
  refine ⟨?_, hb _ hbj, ?_⟩
  · simpa only [Module.End.mul_apply, hcj] using
      LinearMap.congr_fun hc (orbifoldSlice j x)
  · simpa only [Module.End.mul_apply, hej, map_smul] using
      LinearMap.congr_fun he (orbifoldSlice j x)

private theorem ghost_kernel_of_ac (A : Module.End ℂ UState)
    (hb : ac ghostB0 A = 0) (y : UState) (hy : ghostB0 y = 0) :
    ghostB0 (A y) = 0 := by
  simpa only [ac, LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply,
    hy, map_zero, add_zero] using LinearMap.congr_fun hb y

def shellD0 (F : Frame) (a : UCharge) : Module.End ℂ (relativeMassShell a) :=
  (lift (d0 F a)).restrict fun x hx =>
    lift_mem_shell a _ (LatticeQuartetContraction.chargeProject_d0 F a a)
      (ghost_kernel_of_ac _ (LatticeQuartetContraction.b0_d0 F a))
      (originalEnergy_d0 F hyperbolicInverse hyperbolic_inverse_left
        hyperbolic_inverse_right a) x hx

def shellH (F : Frame) (a : UCharge) : Module.End ℂ (relativeMassShell a) :=
  (lift (h F (transverseBasis F) a)).restrict fun x hx => by
    apply lift_mem_shell a _ (chargeProject_h F (transverseBasis F) a a)
      (ghost_kernel_of_ac _ (LatticeQuartetContraction.b0_h F (transverseBasis F) a)) _ x hx
    rw [h, ← mul_assoc, originalEnergy_R F hyperbolicInverse hyperbolic_inverse_left
      hyperbolic_inverse_right a, mul_assoc,
      ← originalEnergy_invM F (transverseBasis F) hyperbolicInverse
        hyperbolic_inverse_left hyperbolic_inverse_right, mul_assoc]

private theorem slices_injective {x y : State}
    (hxy : ∀ j, orbifoldSlice j x = orbifoldSlice j y) : x = y := by
  apply fullBasis.repr.injective
  ext i
  rcases i with ⟨j, i⟩
  rw [← orbifoldSlice_coeff, ← orbifoldSlice_coeff, hxy]

set_option maxHeartbeats 2400000 in
-- The native restriction and both nested tensor instances are reduced here.
theorem shell_contraction (F : Frame) (a : UCharge) (ha : F.pPlus a ≠ 0) :
    ∀ x : relativeMassShell a,
      (shellD0 F a (shellH F a x) + shellH F a (shellD0 F a x) : State) =
        (x : State) - lift (P0 F (transverseBasis F)) x := by
  intro x
  apply slices_injective
  intro j
  change orbifoldSlice j (lift (d0 F a) (lift (h F (transverseBasis F) a) x) +
    lift (h F (transverseBasis F) a) (lift (d0 F a) x)) = _
  simp only [map_add, map_sub, slice_lift]
  simpa only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.one_apply] using
    LinearMap.congr_fun (LatticeQuartetContraction.homotopy_contraction F
      (transverseBasis F) a ha) (orbifoldSlice j x)

theorem shellH_square (F : Frame) (a : UCharge) : shellH F a * shellH F a = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  apply slices_injective
  intro j
  change orbifoldSlice j (lift (h F (transverseBasis F) a)
    (lift (h F (transverseBasis F) a) x)) = orbifoldSlice j 0
  rw [slice_lift, slice_lift, map_zero]
  exact LinearMap.congr_fun (LatticeQuartetContraction.homotopy_square F
    (transverseBasis F) a) (orbifoldSlice j x)

def shellP0 (F : Frame) (a : UCharge) (ha : F.pPlus a ≠ 0) :
    Module.End ℂ (relativeMassShell a) :=
  (lift (P0 F (transverseBasis F))).restrict fun x hx => by
    let y : relativeMassShell a := ⟨x, hx⟩
    have he := shell_contraction F a ha y
    have hp : lift (P0 F (transverseBasis F)) x =
        x - (shellD0 F a (shellH F a y) + shellH F a (shellD0 F a y) : State) := by
      rw [he]
      change _ = x - (x - _)
      abel
    rw [hp]
    exact (relativeMassShell a).sub_mem hx
      ((relativeMassShell a).add_mem (shellD0 F a (shellH F a y)).property
        (shellH F a (shellD0 F a y)).property)

open LatticeQuartetContraction (StateIndex actualBasis totalCount totalCount_zero_iff)
open LatticeRelativeShellDegreeBounds (frameEnergy coordinateSlice originalSlice
  originalSlice_coeff actualBasis_repr_eq_coordinateSlice)
open LatticeRelativeMassShell (massShellCutoff massShellCutoff_cast)
open private exists_original_coeff_of_coordinate_coeff from
  D5.S3.VertexAlgebra.Lattice.LatticeRelativeShellDegreeBounds
open private orbifold_grades_internal orbifoldGradeBasis orbifoldMode_basis from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTZeroEnergy

private abbrev UFrameLabel := StateIndex hyperbolicData 0
private abbrev FrameLabel := OrbifoldLabel × UFrameLabel

/-- The original momentum, relative occupation, and exact total excitation
on a slice expressed in null-frame oscillator coordinates. -/
private theorem slice_frame_support (F : Frame) (a : UCharge) (x : State)
    (hx : x ∈ relativeMassShell a) (j : OrbifoldLabel) (i : UFrameLabel)
    (hi : (actualBasis F (transverseBasis F)).repr (orbifoldSlice j x) i ≠ 0) :
    i.1.1 = a ∧ 3 ∉ i.2 ∧ j.1 + frameEnergy i.1.2 + level i.2 =
      massShellCutoff hyperbolicData a := by
  let B := transverseBasis F
  rw [actualBasis_repr_eq_coordinateSlice] at hi
  obtain ⟨d, hd⟩ := exists_original_coeff_of_coordinate_coeff F B
    (orbifoldSlice j x) i.1.1 i.2 i.1.2 hi
  rw [orbifoldSlice_coeff] at hd
  have hs := (mem_relativeMassShell_iff a x).mp hx
  have h := hs (j, ((i.1.1, d), i.2)) hd
  have hcut := (coefficient_support_bound a hx hd).1
  have hhom : MvPolynomial.IsWeightedHomogeneous
      (LatticeGeneratingFieldLocality.oscillatorWeight hyperbolicData)
      (originalSlice hyperbolicData i.1.1 i.2 (orbifoldSlice j x)) (oscillatorEnergy d) := by
    intro e he
    rw [originalSlice_coeff, orbifoldSlice_coeff] at he
    have hecut := (coefficient_support_bound a hx he).1
    change oscillatorEnergy e = oscillatorEnergy d
    change j.1 + oscillatorEnergy e + level i.2 = massShellCutoff hyperbolicData a at hecut
    change j.1 + oscillatorEnergy d + level i.2 = massShellCutoff hyperbolicData a at hcut
    omega
  have hframe : frameEnergy i.1.2 = oscillatorEnergy d :=
    ((F.frequency_grading B _ _).mpr hhom) hi
  exact ⟨h.1, h.2.1, by rw [hframe]; exact hcut⟩

private def frameBasis (F : Frame) : Module.Basis FrameLabel ℂ State :=
  (orbifoldBasis.tensorProduct (actualBasis F (transverseBasis F))).map assoc.symm

private theorem frameBasis_apply (F : Frame) (i : FrameLabel) :
    frameBasis F i = assoc.symm
      (orbifoldBasis i.1 ⊗ₜ[ℂ] actualBasis F (transverseBasis F) i.2) := by
  rw [frameBasis, Module.Basis.map_apply, Module.Basis.tensorProduct_apply']

set_option maxHeartbeats 1800000 in
-- Comparing the native tensor basis and slice reduces the carrier instances.
private theorem frameBasis_coeff (F : Frame) (x : State) (j : OrbifoldLabel) (i : UFrameLabel) :
    (frameBasis F).repr x (j, i) =
      (actualBasis F (transverseBasis F)).repr (orbifoldSlice j x) i := by
  have h : ((frameBasis F).coord (j, i)).comp assoc.symm.toLinearMap =
      (((actualBasis F (transverseBasis F)).coord i).comp (orbifoldSlice j)).comp
        assoc.symm.toLinearMap := by
    apply TensorProduct.ext'
    intro u v
    change (frameBasis F).repr (assoc.symm (u ⊗ₜ[ℂ] v)) (j, i) =
      (actualBasis F (transverseBasis F)).repr
        (orbifoldSlice j (assoc.symm (u ⊗ₜ[ℂ] v))) i
    rw [frameBasis, Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm,
      LinearEquiv.apply_symm_apply, Module.Basis.tensorProduct_repr_tmul_apply, slice_assoc_tmul,
      (actualBasis F (transverseBasis F)).repr.map_smul, Finsupp.smul_apply]
    exact mul_comm _ _
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    Module.Basis.coord_apply] using LinearMap.congr_fun h (assoc x)

private theorem zero_count_iff (i : UFrameLabel) :
    totalCount i = 0 ↔ i.1.2 = 0 ∧ (i.2 = {1} ∨ i.2 = {1, 3}) := by
  rw [totalCount_zero_iff]
  apply and_congr_left'
  constructor
  · intro h
    ext ⟨v, r⟩
    rw [Finsupp.zero_apply]
    rcases v with u | u | v
    · cases u
      exact (h r).1
    · cases u
      exact (h r).2
    · exact Fin.elim0 v
  · intro h
    simp [h, LatticeQuartetContraction.NoLongitudinal]

private abbrev groundIndex (a : UCharge) : UFrameLabel := (⟨a, 0⟩, {1})

private theorem groundIndex_basis (F : Frame) (a : UCharge) :
    actualBasis F (transverseBasis F) (groundIndex a) =
      Finsupp.single a (MvPolynomial.monomial 0 1) ⊗ₜ[ℂ] ket {1} := by
  rw [LatticeQuartetContraction.actualBasis_apply]
  simp only [LatticeQuartetContraction.sector, MvPolynomial.monomial_zero', map_one]

open D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus
  (projectZero diagonal_coefficient)

private theorem lift_P0_coeff (F : Frame) (x : State) (i : FrameLabel) :
    (frameBasis F).repr (lift (P0 F (transverseBasis F)) x) i =
      (if totalCount i.2 = 0 then (1 : ℂ) else 0) * (frameBasis F).repr x i := by
  classical
  rcases i with ⟨j, i⟩
  rw [frameBasis_coeff, frameBasis_coeff, slice_lift, P0, projectZero, diagonal_coefficient]

/-- The actual eigenspace of the conformal zero mode on the Golay–Leech orbifold. -/
abbrev orbifoldGrade (n : ℕ) := (orbifoldMode 0).eigenspace (n : ℂ)

private theorem ground_level : level ({1} : Finset ℕ) = 0 := by
  simp [level, relativeEnergy, D5.S3.Quantum.Fermionic.BcGhostRelativeEnergy.energy,
    D5.S3.Quantum.Fermionic.BcGhostRelativeEnergy.siteEnergy_one]

/-- The uncorrected quartet representative (u \otimes e^a \otimes c_1|0\rangle). -/
def groundTensor (a : UCharge) : Orbifold →ₗ[ℂ] State :=
  (TensorProduct.mk ℂ Matter Fock).flip (ket {1}) ∘ₗ
    (TensorProduct.mk ℂ Orbifold Hyperbolic).flip (Finsupp.single a (MvPolynomial.monomial 0 1))

private theorem groundTensor_assoc (F : Frame) (a : UCharge) (u : Orbifold) :
    groundTensor a u = assoc.symm (u ⊗ₜ[ℂ] actualBasis F (transverseBasis F) (groundIndex a)) := by
  rw [groundIndex_basis, TensorProduct.assoc_symm_tmul]
  rfl

private theorem groundTensor_repr (F : Frame) (a : UCharge) (u : Orbifold) (i : FrameLabel) :
    (frameBasis F).repr (groundTensor a u) i =
      orbifoldBasis.repr u i.1 * Finsupp.single (groundIndex a) (1 : ℂ) i.2 := by
  rcases i with ⟨j, i⟩
  rw [groundTensor_assoc F, frameBasis, Module.Basis.map_repr, LinearEquiv.trans_apply,
    LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply,
    Module.Basis.tensorProduct_repr_tmul_apply, Module.Basis.repr_self]
  exact mul_comm _ _

private theorem groundTensor_injective (F : Frame) (a : UCharge) :
    Function.Injective (groundTensor a) := by
  intro u v h
  apply orbifoldBasis.repr.injective
  ext j
  simpa only [groundTensor_repr, Finsupp.single_eq_same, mul_one] using
    congrArg (fun x => (frameBasis F).repr x (j, groundIndex a)) h

private theorem groundTensor_mem_shell (a : UCharge) (ha : chargeEnergy hyperbolicData a ≤ 1)
    (u : orbifoldGrade (massShellCutoff hyperbolicData a)) :
    groundTensor a u ∈ relativeMassShell a := by
  let n := massShellCutoff hyperbolicData a
  let B := orbifoldGradeBasis n
  change groundTensor a ((u : orbifoldGrade n) : Orbifold) ∈ relativeMassShell a
  have hexp := B.linearCombination_repr u
  rw [← hexp, Finsupp.linearCombination_apply, Finsupp.sum]
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  have he : groundTensor a (B i : Orbifold) = fullBasis (⟨n, i⟩, ((a, 0), {1})) := by
    rw [fullBasis_apply]
    have h : orbifoldBasis ⟨n, i⟩ = (B i : Orbifold) := by
      exact congrFun (orbifold_grades_internal.collectedBasis_coe orbifoldGradeBasis) ⟨n, i⟩
    rw [h]
    rfl
  rw [he, relativeMassShell_eq_span]
  apply Submodule.subset_span
  refine ⟨_, ⟨rfl, by simp, ?_⟩, rfl⟩
  have hos := (LatticePositiveEnergy.oscillatorEnergy_eq_zero_iff hyperbolicData _).mpr rfl
  change ((n + oscillatorEnergy (0 : LatticePositiveEnergy.Exponent hyperbolicData) +
    level ({1} : Finset ℕ) : ℕ) : ℤ) = 1 - chargeEnergy hyperbolicData a
  simpa [hos, ground_level] using massShellCutoff_cast hyperbolicData a ha

/-- The zero-quartet representative in the actual relative mass shell. -/
def inclusion (a : UCharge) (ha : chargeEnergy hyperbolicData a ≤ 1) :
    orbifoldGrade (massShellCutoff hyperbolicData a) →ₗ[ℂ] relativeMassShell a :=
  ((groundTensor a).comp (orbifoldGrade (massShellCutoff hyperbolicData a)).subtype).codRestrict
    _ (groundTensor_mem_shell a ha)

private theorem shellP0_fixes_inclusion (F : Frame) (a : UCharge) (hp : F.pPlus a ≠ 0)
    (ha : chargeEnergy hyperbolicData a ≤ 1)
    (u : orbifoldGrade (massShellCutoff hyperbolicData a)) :
    shellP0 F a hp (inclusion a ha u) = inclusion a ha u := by
  classical
  apply Subtype.ext
  apply (frameBasis F).repr.injective
  ext i
  change (frameBasis F).repr (lift (P0 F (transverseBasis F)) (groundTensor a u)) i =
    (frameBasis F).repr (groundTensor a u) i
  rw [lift_P0_coeff, groundTensor_repr]
  by_cases hi : i.2 = groundIndex a
  · have hzero : totalCount (groundIndex a) = 0 :=
      (zero_count_iff _).mpr ⟨rfl, Or.inl rfl⟩
    simp [hi, hzero]
  · simp [Finsupp.single_eq_of_ne hi]

private theorem shellP0_mem_target (F : Frame) (a : UCharge) (hp : F.pPlus a ≠ 0)
    (ha : chargeEnergy hyperbolicData a ≤ 1) (x : relativeMassShell a) :
    shellP0 F a hp x ∈ LinearMap.range (inclusion a ha) := by
  classical
  let y := shellP0 F a hp x
  have hs : (y : State) ∈ LinearMap.range ((relativeMassShell a).subtype.comp (inclusion a ha)) := by
    rw [← (frameBasis F).linearCombination_repr (y : State), Finsupp.linearCombination_apply,
      Finsupp.sum]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    have hc : (frameBasis F).repr (y : State) i ≠ 0 :=
      Finsupp.mem_support_iff.mp hi
    change (frameBasis F).repr (lift (P0 F (transverseBasis F)) x) i ≠ 0 at hc
    rw [lift_P0_coeff] at hc
    have hzero : totalCount i.2 = 0 := by
      by_contra hn
      simp [hn] at hc
    have hnonzero := (mul_ne_zero_iff.mp hc).2
    have hh := slice_frame_support F a x x.property i.1 i.2 (by
      rcases i with ⟨j, k⟩
      rwa [frameBasis_coeff] at hnonzero)
    obtain ⟨hexp, hghost⟩ := (zero_count_iff i.2).mp hzero
    have hg : i.2.2 = {1} := hghost.resolve_right (fun h => hh.2.1 (by simp [h]))
    have hk : i.2 = groundIndex a := Prod.ext (Sigma.ext hh.1 (heq_of_eq hexp)) hg
    have hj : i.1.1 = massShellCutoff hyperbolicData a := by
      simpa [hexp, hg, frameEnergy, ground_level] using hh.2.2
    have hm : orbifoldBasis i.1 ∈ orbifoldGrade (massShellCutoff hyperbolicData a) :=
      Module.End.mem_eigenspace_iff.mpr (by simpa only [hj] using orbifoldMode_basis i.1)
    refine ⟨⟨orbifoldBasis i.1, hm⟩, ?_⟩
    change groundTensor a (orbifoldBasis i.1) = _
    rw [frameBasis_apply, hk, groundTensor_assoc F]
  obtain ⟨u, hu⟩ := hs
  exact ⟨u, Subtype.ext hu⟩

/-- The zero-quartet range on the native shell is exactly the image of
the actual orbifold eigenspace under the ground tensor map. -/
theorem shellP0_range (F : Frame) (a : UCharge) (hp : F.pPlus a ≠ 0)
    (ha : chargeEnergy hyperbolicData a ≤ 1) :
    LinearMap.range (shellP0 F a hp) = LinearMap.range (inclusion a ha) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact shellP0_mem_target F a hp ha x
  · rintro _ ⟨u, rfl⟩
    exact ⟨inclusion a ha u, shellP0_fixes_inclusion F a hp ha u⟩

/-- The exact zero-quartet target and its native representative. -/
def groundEquiv (F : Frame) (a : UCharge) (hp : F.pPlus a ≠ 0)
    (ha : chargeEnergy hyperbolicData a ≤ 1) :
    orbifoldGrade (massShellCutoff hyperbolicData a) ≃ₗ[ℂ] LinearMap.range (shellP0 F a hp) :=
  (LinearEquiv.ofInjective (inclusion a ha)
    (fun _ _ h => Subtype.ext (groundTensor_injective F a (congrArg Subtype.val h)))).trans
      (LinearEquiv.ofEq _ _ (shellP0_range F a hp ha).symm)

theorem groundEquiv_finrank_at_minus_one (F : Frame) (a : UCharge) (hp : F.pPlus a ≠ 0)
    (ha : chargeEnergy hyperbolicData a = -1) :
    Module.finrank ℂ (LinearMap.range (shellP0 F a hp)) = 196884 := by
  have hle : chargeEnergy hyperbolicData a ≤ 1 := by omega
  rw [← (groundEquiv F a hp hle).finrank_eq]
  have he : massShellCutoff hyperbolicData a = 2 := by simp [massShellCutoff, ha]
  rw [he]
  exact TwistedGround.OriginalOrbifoldLowSpectrum.actual_leech_low_spectrum.2.2.2.2.2.1

section FullCharge
set_option synthInstance.maxHeartbeats 100000

open D5.S3.Quantum.Fermionic.BcGhostFock (c)
open LatticeQuartetContraction (tp)
open LatticeBRSTModeFiltration (degree c_shift tensor_ghost_shift h_shift)

private abbrev uSummand (m : ℤ) :=
  LatticeMatterGhostCoupling.summand hyperbolicData hyperbolicInverse m

private abbrev uCharge : Module.End ℂ UState :=
  LatticeBRST.totalCharge hyperbolicData hyperbolicInverse

/-- The (L_m^{orb}c_{-m}) contribution in the original three factors. -/
def orbifoldTerm (m : ℤ) : Module.End ℂ State :=
  assoc.symm.toLinearMap.comp
    ((TensorProduct.map (orbifoldMode m) (tp 1 (c (-m)))).comp assoc.toLinearMap)

private theorem orbifoldTerm_apply (m : ℤ) (u : Orbifold) (v : UState) :
    orbifoldTerm m (assoc.symm (u ⊗ₜ[ℂ] v)) =
      assoc.symm (orbifoldMode m u ⊗ₜ[ℂ] tp 1 (c (-m)) v) := by
  simp only [orbifoldTerm, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, TensorProduct.map_tmul]

private theorem summand_split (m : ℤ) :
    VirasoroBRST.summand matterDatum m = lift (uSummand m) + orbifoldTerm m := by
  apply TensorProduct.ext'
  intro z w
  induction z using TensorProduct.inductionOn with
  | tmul u v =>
      rw [← TensorProduct.assoc_symm_tmul, LinearMap.add_apply, lift_assoc_tmul,
        orbifoldTerm_apply, TensorProduct.assoc_symm_tmul]
      simp only [VirasoroBRST.summand, TensorProduct.map_tmul,
        LatticeMatterGhostCoupling.summand, tp, Module.End.one_apply,
        TensorProduct.assoc_symm_tmul]
      change mode m (u ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] c (-m) w =
        (u ⊗ₜ[ℂ] hyperbolicMode m v) ⊗ₜ[ℂ] c (-m) w +
          (orbifoldMode m u ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] c (-m) w
      simp only [mode, LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
        TensorProduct.add_tmul]
      exact add_comm _ _
  | add x y hx hy =>
      simpa only [TensorProduct.add_tmul, map_add] using congrArg₂ (· + ·) hx hy

private theorem ghostCharge_split :
    VirasoroBRST.ghostCharge matterDatum = lift (LatticeBRST.ghostCharge hyperbolicData) := by
  apply TensorProduct.ext'
  intro z w
  induction z using TensorProduct.inductionOn with
  | tmul u v =>
      rw [← TensorProduct.assoc_symm_tmul, lift_assoc_tmul, TensorProduct.assoc_symm_tmul]
      simp only [VirasoroBRST.ghostCharge, D5.S3.Quantum.Fermionic.BcGhostChargeTensor.liftGhost,
        LatticeBRST.ghostCharge, TensorProduct.map_tmul, LinearMap.id_apply,
        TensorProduct.assoc_symm_tmul]
  | add x y hx hy =>
      simpa only [TensorProduct.add_tmul, map_add] using congrArg₂ (· + ·) hx hy

/-- A simultaneous finite capture computes the native charge on an elementary
orbifold tensor. Every summand, including the zero mode, is retained. -/
theorem charge_finite_split (u : Orbifold) (v : UState) (s : Finset ℤ)
    (hs : Function.support (fun m => VirasoroBRST.summand matterDatum m
        (assoc.symm (u ⊗ₜ[ℂ] v))) ⊆ (s : Set ℤ))
    (hu : Function.support (fun m => uSummand m v) ⊆ (s : Set ℤ)) :
    Q (assoc.symm (u ⊗ₜ[ℂ] v)) =
      lift uCharge (assoc.symm (u ⊗ₜ[ℂ] v)) +
        ∑ m ∈ s, orbifoldTerm m (assoc.symm (u ⊗ₜ[ℂ] v)) := by
  let x := assoc.symm (u ⊗ₜ[ℂ] v)
  change VirasoroBRST.T matterDatum x + VirasoroBRST.ghostCharge matterDatum x = _
  have ht : ∑ m ∈ s, lift (uSummand m) x =
      lift (LatticeMatterGhostCoupling.T hyperbolicData hyperbolicInverse) x := by
    change _ = lift _ (assoc.symm (u ⊗ₜ[ℂ] v))
    simp only [x, lift_assoc_tmul]
    rw [LatticeMatterGhostCoupling.finite_capture hyperbolicData hyperbolicInverse v s hu,
      TensorProduct.tmul_sum]
    exact (map_sum assoc.symm.toLinearMap _ s).symm
  rw [VirasoroBRST.finite_capture _ _ _ hs, ghostCharge_split]
  simp_rw [summand_split, LinearMap.add_apply]
  rw [Finset.sum_add_distrib, ht]
  change _ + _ = lift uCharge x + _
  have hq : lift uCharge x =
      lift (LatticeMatterGhostCoupling.T hyperbolicData hyperbolicInverse) x +
        lift (LatticeBRST.ghostCharge hyperbolicData) x := by
    simp only [x, lift_assoc_tmul, LatticeBRST.totalCharge, LinearMap.add_apply,
      TensorProduct.tmul_add, assoc.symm.map_add]
  rw [hq]
  abel

private theorem orbifoldTerm_raises (F : Frame) (m : ℤ) (i j : FrameLabel)
    (hj : (frameBasis F).repr (orbifoldTerm m (frameBasis F i)) j ≠ 0) :
    degree i.2 + 1 ≤ degree j.2 := by
  rcases j with ⟨k, j⟩
  rw [frameBasis_apply, orbifoldTerm_apply, frameBasis_coeff, slice_assoc_tmul,
    (actualBasis F (transverseBasis F)).repr.map_smul, Finsupp.smul_apply] at hj
  have hshift := tensor_ghost_shift F (transverseBasis F) (c (-m)) 1 (c_shift (-m))
  exact le_of_eq (hshift i.2 j (mul_ne_zero_iff.mp hj).2).symm

open LatticeBRSTModeFiltration (basis_expand exponentDegree)
open LatticeRelativeShellDegreeBounds (abs_exponentDegree_le_frameEnergy)
open private ghost_abs_charge_sub_one_le_relativeEnergy from
  D5.S3.VertexAlgebra.Lattice.LatticeRelativeShellDegreeBounds
open D5.S3.Quantum.Fermionic.BcGhostCharge (charge)

private def DegreeAtLeast (F : Frame) (l : ℤ) (x : State) : Prop :=
  ∀ i : FrameLabel, (frameBasis F).repr x i ≠ 0 → l ≤ degree i.2

private theorem frame_support_degree_bound (F : Frame) (a : UCharge)
    (x : relativeMassShell a) (i : FrameLabel)
    (hi : (frameBasis F).repr (x : State) i ≠ 0) :
    |degree i.2| ≤ (massShellCutoff hyperbolicData a : ℤ) := by
  rcases i with ⟨j, i⟩
  rw [frameBasis_coeff] at hi
  obtain ⟨_, hb, he⟩ := slice_frame_support F a x x.property j i hi
  calc
    |degree i| = |exponentDegree i.1.2 + (charge i.2 - 1)| := by
      congr 1
      unfold degree
      ring
    _ ≤ |exponentDegree i.1.2| + |charge i.2 - 1| := abs_add_le _ _
    _ ≤ (frameEnergy i.1.2 : ℤ) + relativeEnergy i.2 :=
      add_le_add (abs_exponentDegree_le_frameEnergy _) (ghost_abs_charge_sub_one_le_relativeEnergy _ hb)
    _ ≤ (massShellCutoff hyperbolicData a : ℤ) := by
      rw [← level_cast]
      omega

set_option maxHeartbeats 2200000 in
-- The finite sums and coefficients use both associations of the native carrier.
private theorem remainder_basis_raises (F : Frame) (a : UCharge) (i j : FrameLabel)
    (hi : i.2.1.1 = a)
    (hj : (frameBasis F).repr ((Q - lift (d0 F a)) (frameBasis F i)) j ≠ 0) :
    degree i.2 + 1 ≤ degree j.2 := by
  classical
  let B := transverseBasis F
  let u := orbifoldBasis i.1
  let v := actualBasis F B i.2
  let x := frameBasis F i
  let sf := VirasoroBRST.summand_finite matterDatum x
  let su := LatticeMatterGhostCoupling.summand_finite hyperbolicData hyperbolicInverse v
  let s := sf.toFinset ∪ su.toFinset
  have h := charge_finite_split u v s
    (by
      intro m hm
      exact Finset.mem_union_left _ (sf.mem_toFinset.mpr (by simpa only [x, frameBasis_apply] using hm)))
    (fun m hm => Finset.mem_union_right _ (su.mem_toFinset.mpr hm))
  change Q (assoc.symm (u ⊗ₜ[ℂ] v)) = _ at h
  rw [← frameBasis_apply] at h
  have hs : (Q - lift (d0 F a)) x =
      lift (uCharge - d0 F a) x + ∑ m ∈ s, orbifoldTerm m x := by
    change Q x - lift (d0 F a) x = _
    rw [h]
    have hl : lift (uCharge - d0 F a) x = lift uCharge x - lift (d0 F a) x := by
      simp only [x, frameBasis_apply, lift_assoc_tmul, LinearMap.sub_apply,
        TensorProduct.tmul_sub]
      exact map_sub assoc.symm.toLinearMap _ _
    rw [hl]
    abel
  by_contra hn
  apply hj
  change (frameBasis F).coord j ((Q - lift (d0 F a)) x) = 0
  rw [hs, map_add, map_sum]
  have huca : (frameBasis F).coord j (lift (uCharge - d0 F a) x) = 0 := by
    rcases j with ⟨k, j⟩
    simp only [Module.Basis.coord_apply, x, frameBasis_apply, lift_assoc_tmul, frameBasis_coeff,
      slice_assoc_tmul]
    rw [(actualBasis F (transverseBasis F)).repr.map_smul, Finsupp.smul_apply]
    have hz : (actualBasis F B).repr ((uCharge - d0 F a) v) j = 0 := by
      by_contra hz
      exact hn (LatticeBRSTFullOriginalRaising.full_remainder_fixed_charge_basis_raises
        F B hyperbolicInverse hyperbolic_inverse_left hyperbolic_inverse_right a i.2 j hi hz)
    change orbifoldBasis.repr u k * (actualBasis F B).repr ((uCharge - d0 F a) v) j = 0
    rw [hz, mul_zero]
  rw [huca, zero_add]
  exact Finset.sum_eq_zero fun m _ => by
    by_contra hz
    exact hn (orbifoldTerm_raises F m i j hz)

private theorem operator_degree_bound (F : Frame) (A : Module.End ℂ State)
    (k l : ℤ) (x : State)
    (h : ∀ i j : FrameLabel, (frameBasis F).repr x i ≠ 0 →
      (frameBasis F).repr (A (frameBasis F i)) j ≠ 0 → l + k ≤ degree j.2) :
    DegreeAtLeast F (l + k) (A x) := by
  classical
  intro j hj
  by_contra hn
  apply hj
  change (frameBasis F).coord j (A x) = 0
  rw [← basis_expand (frameBasis F) x]
  simp only [map_sum, map_smul, Module.Basis.coord_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro i hi
  have hx := Finsupp.mem_support_iff.mp hi
  have hz : (frameBasis F).repr (A (frameBasis F i)) j = 0 := by
    by_contra hz
    exact hn (h i j hx hz)
  rw [hz, mul_zero]

private abbrev delta (F : Frame) (a : UCharge) :=
  differential a - shellD0 F a

private theorem delta_raises (F : Frame) (a : UCharge) (l : ℤ)
    (x : relativeMassShell a) (hx : DegreeAtLeast F l x) :
    DegreeAtLeast F (l + 1) (delta F a x : State) := by
  apply operator_degree_bound F (Q - lift (d0 F a)) 1 l (x : State)
  intro i j hi hj
  have hcharge := (slice_frame_support F a x x.property i.1 i.2 (by
    rcases i with ⟨k, i⟩
    rwa [frameBasis_coeff] at hi)).1
  have hstep := remainder_basis_raises F a i j hcharge hj
  have hinput := hx i hi
  omega

private theorem shellH_preserves_degree (F : Frame) (a : UCharge) (l : ℤ)
    (x : relativeMassShell a) (hx : DegreeAtLeast F l x) :
    DegreeAtLeast F l (shellH F a x : State) := by
  rw [← add_zero l]
  apply operator_degree_bound F (lift (h F (transverseBasis F) a)) 0 l (x : State)
  intro i j hi hj
  rcases j with ⟨k, j⟩
  rw [frameBasis_apply, lift_assoc_tmul, frameBasis_coeff, slice_assoc_tmul,
    (actualBasis F (transverseBasis F)).repr.map_smul, Finsupp.smul_apply] at hj
  have he := h_shift F (transverseBasis F) a i.2 j (mul_ne_zero_iff.mp hj).2
  change degree j = degree i.2 + 0 at he
  change l + 0 ≤ degree j
  simpa only [he, add_zero] using hx i hi

private theorem hdelta_power_degree (F : Frame) (a : UCharge) (l : ℤ)
    (x : relativeMassShell a) (hx : DegreeAtLeast F l x) (r : ℕ) :
    DegreeAtLeast F (l + r) (((shellH F a * delta F a) ^ r) x : State) := by
  induction r with
  | zero => simpa using hx
  | succ r ih =>
      rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      push_cast
      rw [← add_assoc]
      exact shellH_preserves_degree F a _ _
        (delta_raises F a _ _ ih)

theorem hdelta_nilpotent (F : Frame) (a : UCharge) :
    (shellH F a * delta F a) ^ (2 * massShellCutoff hyperbolicData a + 1) = 0 := by
  let N := massShellCutoff hyperbolicData a
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  let y := ((shellH F a * delta F a) ^ (2 * N + 1)) x
  change (y : State) = 0
  apply (frameBasis F).repr.injective
  rw [(frameBasis F).repr.map_zero]
  ext i
  rw [Finsupp.zero_apply]
  by_contra hn
  have h₀ : DegreeAtLeast F (-(N : ℤ)) x :=
    fun j hj => (abs_le.mp (frame_support_degree_bound F a x j hj)).1
  have h₁ := hdelta_power_degree F a _ x h₀ (2 * N + 1) i hn
  have h₂ := (abs_le.mp (frame_support_degree_bound F a y i hn)).2
  change degree i.2 ≤ (N : ℤ) at h₂
  omega

open D5.S3.HomologicalAlgebra.FinitePerturbation (Input inversePolynomial Cohomology Boundaries)

private theorem shellD0_square (F : Frame) (a : UCharge) :
    shellD0 F a * shellD0 F a = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  apply slices_injective
  intro j
  change orbifoldSlice j (lift (d0 F a) (lift (d0 F a) x)) = orbifoldSlice j 0
  rw [slice_lift, slice_lift, map_zero]
  exact LinearMap.congr_fun (d0_square F a) (orbifoldSlice j x)

private theorem shellP0_mul_zero (F : Frame) (a : UCharge) (hp : F.pPlus a ≠ 0)
    (A : Module.End ℂ UState) (S : Module.End ℂ (relativeMassShell a))
    (hc : ∀ x : relativeMassShell a, (S x : State) = lift A x)
    (hA : P0 F (transverseBasis F) * A = 0) : shellP0 F a hp * S = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  apply slices_injective
  intro j
  change orbifoldSlice j (lift (P0 F (transverseBasis F)) (S x)) = orbifoldSlice j 0
  rw [hc, slice_lift, slice_lift, map_zero]
  exact LinearMap.congr_fun hA (orbifoldSlice j x)

private theorem mul_shellP0_zero (F : Frame) (a : UCharge) (hp : F.pPlus a ≠ 0)
    (A : Module.End ℂ UState) (S : Module.End ℂ (relativeMassShell a))
    (hc : ∀ x : relativeMassShell a, (S x : State) = lift A x)
    (hA : A * P0 F (transverseBasis F) = 0) : S * shellP0 F a hp = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  apply slices_injective
  intro j
  change orbifoldSlice j (S (shellP0 F a hp x)) = orbifoldSlice j 0
  rw [hc]
  change orbifoldSlice j (lift A (lift (P0 F (transverseBasis F)) x)) = orbifoldSlice j 0
  rw [slice_lift, slice_lift, map_zero]
  exact LinearMap.congr_fun hA (orbifoldSlice j x)

private theorem differential_sq (a : UCharge) :
    differential a * differential a = 0 := by
  simpa only [pow_two] using differential_squared a

private def perturbationInput (F : Frame) (a : UCharge) (hp : F.pPlus a ≠ 0)
    (he : chargeEnergy hyperbolicData a ≤ 1) :
    Input (R := ℂ) (U := LinearMap.range (shellP0 F a hp)) (V := relativeMassShell a) where
  d0 := shellD0 F a
  h := shellH F a
  delta := delta F a
  i := (LinearMap.range (shellP0 F a hp)).subtype
  p := (shellP0 F a hp).rangeRestrict
  d0_sq := shellD0_square F a
  pi := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    change shellP0 F a hp y = (y : relativeMassShell a)
    have hy : (y : relativeMassShell a) ∈ LinearMap.range (inclusion a he) :=
      (shellP0_range F a hp he) ▸ y.property
    obtain ⟨u, hu⟩ := hy
    rw [← hu, shellP0_fixes_inclusion F a hp he]
  di := by
    have hh := mul_shellP0_zero F a hp _ (shellD0 F a) (fun _ => rfl)
      (LatticeQuartetContraction.d0_mul_P0 F (transverseBasis F) a)
    apply LinearMap.ext
    intro y
    obtain ⟨x, hx⟩ := y.property
    change shellD0 F a y = 0
    rw [← hx]
    exact LinearMap.congr_fun hh x
  pd := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun
      (shellP0_mul_zero F a hp _ (shellD0 F a) (fun _ => rfl)
        (LatticeQuartetContraction.P0_mul_d0 F (transverseBasis F) a)) x
  contraction := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact shell_contraction F a hp x
  hh := shellH_square F a
  hi := by
    have hh := mul_shellP0_zero F a hp _ (shellH F a) (fun _ => rfl)
      (LatticeQuartetContraction.h_mul_P0 F (transverseBasis F) a)
    apply LinearMap.ext
    intro y
    obtain ⟨x, hx⟩ := y.property
    change shellH F a y = 0
    rw [← hx]
    exact LinearMap.congr_fun hh x
  ph := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun
      (shellP0_mul_zero F a hp _ (shellH F a) (fun _ => rfl)
        (LatticeQuartetContraction.P0_mul_h F (transverseBasis F) a)) x
  perturbed_sq := by
    rw [add_sub_cancel]
    exact differential_sq a

private theorem ground_degree (a : UCharge) : degree (groundIndex a) = 0 := by
  norm_num [degree, exponentDegree, charge, Finset.filter_singleton]

private theorem projected_support_degree (F : Frame) (a : UCharge)
    (x : relativeMassShell a) (i : FrameLabel)
    (hc : (frameBasis F).repr (lift (P0 F (transverseBasis F)) x) i ≠ 0) :
    degree i.2 = 0 := by
  rw [lift_P0_coeff] at hc
  have hzero : totalCount i.2 = 0 := by
    by_contra hn
    simp [hn] at hc
  have hnonzero := (mul_ne_zero_iff.mp hc).2
  have hh := slice_frame_support F a x x.property i.1 i.2 (by
    rcases i with ⟨j, k⟩
    rwa [frameBasis_coeff] at hnonzero)
  obtain ⟨hexp, hghost⟩ := (zero_count_iff i.2).mp hzero
  have hg : i.2.2 = {1} := hghost.resolve_right (fun h => hh.2.1 (by simp [h]))
  have hk : i.2 = groundIndex a := Prod.ext (Sigma.ext hh.1 (heq_of_eq hexp)) hg
  rw [hk, ground_degree]

private theorem shellP0_kills_positive (F : Frame) (a : UCharge) (hp : F.pPlus a ≠ 0)
    (x : relativeMassShell a) (hx : DegreeAtLeast F 1 x) : shellP0 F a hp x = 0 := by
  apply Subtype.ext
  change (lift (P0 F (transverseBasis F)) x : State) = 0
  apply (frameBasis F).repr.injective
  rw [(frameBasis F).repr.map_zero]
  ext i
  change (frameBasis F).repr (lift (P0 F (transverseBasis F)) x) i = 0
  by_contra hc
  have hzero := projected_support_degree F a x i hc
  rw [lift_P0_coeff] at hc
  have hpos := hx i (mul_ne_zero_iff.mp hc).2
  omega

private theorem perturbation_transferred_zero (F : Frame) (a : UCharge)
    (hp : F.pPlus a ≠ 0) (he : chargeEnergy hyperbolicData a ≤ 1) (n : ℕ) :
    (perturbationInput F a hp he).transferred n = 0 := by
  classical
  let C := perturbationInput F a hp he
  apply LinearMap.ext
  intro y
  apply Subtype.ext
  change shellP0 F a hp (delta F a (C.I n y)) = 0
  apply shellP0_kills_positive
  apply (show DegreeAtLeast F 0 (C.I n y : State) →
      DegreeAtLeast F 1 (delta F a (C.I n y) : State) from by
    simpa only [zero_add] using delta_raises F a 0 (C.I n y))
  have hy : DegreeAtLeast F 0 (((y : relativeMassShell a) : State)) := by
    obtain ⟨x, hx⟩ := y.property
    rw [← hx]
    intro i hi
    exact le_of_eq (projected_support_degree F a x i hi).symm
  intro i hi
  by_contra hn
  apply hi
  let L : relativeMassShell a →ₗ[ℂ] ℂ :=
    ((frameBasis F).coord i).comp (relativeMassShell a).subtype
  change L (C.I n y) = 0
  change L (inversePolynomial (shellH F a * delta F a) n (y : relativeMassShell a)) = 0
  simp only [inversePolynomial, LinearMap.sum_apply, map_sum L]
  apply Finset.sum_eq_zero
  intro r hr
  have hz : L (((shellH F a * delta F a) ^ r) (y : relativeMassShell a)) = 0 := by
    by_contra hz
    have hbound := hdelta_power_degree F a 0 y hy r i hz
    omega
  rcases Nat.even_or_odd r with hr | hr
  · rw [hr.neg_pow]
    exact hz
  · rw [hr.neg_pow, LinearMap.neg_apply, map_neg, hz, neg_zero]

private theorem perturbation_D (F : Frame) (a : UCharge) (hp : F.pPlus a ≠ 0)
    (he : chargeEnergy hyperbolicData a ≤ 1) :
    (perturbationInput F a hp he).D = differential a := by
  change shellD0 F a + (differential a - shellD0 F a) = differential a
  abel

private def zeroCohomologyEquiv {U : Type*} [AddCommGroup U] [Module ℂ U]
    (d : Module.End ℂ U) (hsq : d * d = 0) (he : d = 0) :
    Cohomology d hsq ≃ₗ[ℂ] U := by
  subst d
  have hb : Boundaries (0 : Module.End ℂ U) hsq = ⊥ := by
    apply LinearMap.range_eq_bot.mpr
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl
  exact ((Boundaries (0 : Module.End ℂ U) hsq).quotEquivOfEqBot hb).trans
    ((LinearEquiv.ofEq _ _ (LinearMap.ker_zero : LinearMap.ker (0 : Module.End ℂ U) = ⊤)).trans
      Submodule.topEquiv)

/-- The kernel of the full original shell charge modulo its actual boundaries. -/
abbrev FullCohomology (a : UCharge) :=
  Cohomology (differential a) (differential_sq a)

/-- Finite perturbation gives a linear equivalence of the full shell quotient
with the original orbifold grade. -/
def fullCohomologyEquiv (F : Frame) (a : UCharge) (hp : F.pPlus a ≠ 0)
    (he : chargeEnergy hyperbolicData a ≤ 1) :
    FullCohomology a ≃ₗ[ℂ] orbifoldGrade (massShellCutoff hyperbolicData a) := by
  let C := perturbationInput F a hp he
  let n := 2 * massShellCutoff hyperbolicData a + 1
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hnil : (C.h * C.delta) ^ n = 0 := hdelta_nilpotent F a
  have htr := perturbation_transferred_zero F a hp he n
  let e := (C.cohomologyEquiv n hn hnil).trans
    ((zeroCohomologyEquiv _ _ htr).trans (groundEquiv F a hp he).symm)
  have transport (d : Module.End ℂ (relativeMassShell a)) (hd : d * d = 0)
      (h : d = differential a) : FullCohomology a ≃ₗ[ℂ] Cohomology d hd := by
    subst d
    exact LinearEquiv.refl ℂ (FullCohomology a)
  exact (transport C.D C.perturbed_sq (perturbation_D F a hp he)).trans e


section GhostNumber

open D5.S3.Quantum.Fermionic.BcGhostCharge (ghostNumber)
open D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus (diagonal diagonal_basis)
open private number_ket from D5.S3.Quantum.Fermionic.BcGhostCharge
open private number_ghostCharge from D5.S3.VertexAlgebra.BRST.VirasoroBRST
open private N_d0 N_h commutes_inversePolynomial from
  D5.S3.VertexAlgebra.Lattice.LatticeRelativeBRSTCohomology

private abbrev nativeNumber : Module.End ℂ State := VirasoroBRST.number (V := Matter)
private abbrev uNumber : Module.End ℂ UState :=
  D5.S3.VertexAlgebra.LatticeRelativeBRSTCohomology.Number.N hyperbolicData

private theorem nativeNumber_eq_lift : nativeNumber = lift uNumber := by
  apply TensorProduct.ext'
  intro z w
  induction z using TensorProduct.inductionOn with
  | tmul u v =>
      rw [← TensorProduct.assoc_symm_tmul, lift_assoc_tmul, TensorProduct.assoc_symm_tmul]
      simp only [uNumber, LatticeRelativeBRSTCohomology.Number.N,
        D5.S3.Quantum.Fermionic.BcGhostChargeTensor.number,
        D5.S3.Quantum.Fermionic.BcGhostChargeTensor.liftGhost,
        TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.assoc_symm_tmul]
  | add x y hx hy =>
      simpa only [TensorProduct.add_tmul, map_add] using congrArg₂ (· + ·) hx hy

private theorem nativeNumber_mem_shell (a : UCharge) (x : State) (hx : x ∈ relativeMassShell a) :
    nativeNumber x ∈ relativeMassShell a := by
  have hdiag : nativeNumber = diagonal fullBasis (fun i => (charge i.2.2 : ℂ)) := by
    apply fullBasis.ext
    intro i
    rw [diagonal_basis, fullBasis_apply]
    simp only [D5.S3.Quantum.Fermionic.BcGhostChargeTensor.liftGhost,
      TensorProduct.map_tmul, LinearMap.id_apply, number_ket, TensorProduct.tmul_smul]
  apply (mem_relativeMassShell_iff a _).mpr
  intro i hi
  rw [hdiag, diagonal_coefficient] at hi
  exact (mem_relativeMassShell_iff a x).mp hx i (mul_ne_zero_iff.mp hi).2

/-- The original occupation number restricted to the native fixed-momentum shell. -/
def shellNumber (a : UCharge) : Module.End ℂ (relativeMassShell a) :=
  nativeNumber.restrict (nativeNumber_mem_shell a)

private theorem shellNumber_Q (a : UCharge) :
    shellNumber a * differential a - differential a * shellNumber a = differential a := by
  have hQ : nativeNumber * Q - Q * nativeNumber = Q := by
    have ht := VirasoroBRST.number_T matterDatum
    have hg := number_ghostCharge matterDatum
    change nativeNumber * VirasoroBRST.T matterDatum -
      VirasoroBRST.T matterDatum * nativeNumber = VirasoroBRST.T matterDatum at ht
    change nativeNumber * VirasoroBRST.ghostCharge matterDatum -
      VirasoroBRST.ghostCharge matterDatum * nativeNumber = VirasoroBRST.ghostCharge matterDatum at hg
    change nativeNumber * (VirasoroBRST.T matterDatum + VirasoroBRST.ghostCharge matterDatum) -
      (VirasoroBRST.T matterDatum + VirasoroBRST.ghostCharge matterDatum) * nativeNumber = _
    rw [mul_add, add_mul]
    change _ = VirasoroBRST.T matterDatum + VirasoroBRST.ghostCharge matterDatum
    calc
      _ = (nativeNumber * VirasoroBRST.T matterDatum - VirasoroBRST.T matterDatum * nativeNumber) +
          (nativeNumber * VirasoroBRST.ghostCharge matterDatum -
            VirasoroBRST.ghostCharge matterDatum * nativeNumber) := by abel
      _ = _ := congrArg₂ (· + ·) ht hg
  apply LinearMap.ext
  intro x
  exact Subtype.ext (LinearMap.congr_fun hQ (x : State))

private theorem shellNumber_lift_comm (a : UCharge) (A : Module.End ℂ UState)
    (S : Module.End ℂ (relativeMassShell a))
    (hs : ∀ x : relativeMassShell a, (S x : State) = lift A x)
    (z : ℂ) (hA : uNumber * A - A * uNumber = z • A) :
    shellNumber a * S - S * shellNumber a = z • S := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  apply slices_injective
  intro j
  change orbifoldSlice j (nativeNumber (S x) - (S (shellNumber a x) : State)) =
    orbifoldSlice j (z • (S x : State))
  simp only [hs]
  change orbifoldSlice j (nativeNumber (lift A x) - lift A (nativeNumber x)) =
    orbifoldSlice j (z • lift A x)
  simp only [nativeNumber_eq_lift, map_sub, map_smul, slice_lift]
  exact LinearMap.congr_fun hA (orbifoldSlice j x)

private theorem shellNumber_delta (F : Frame) (a : UCharge) :
    shellNumber a * delta F a - delta F a * shellNumber a = delta F a := by
  have hd : shellNumber a * shellD0 F a - shellD0 F a * shellNumber a = shellD0 F a := by
    simpa only [one_smul] using shellNumber_lift_comm a (d0 F a) (shellD0 F a)
      (fun _ => rfl) 1 (by simpa only [one_smul] using N_d0 F a)
  have hQ := shellNumber_Q a
  change shellNumber a * (differential a - shellD0 F a) -
    (differential a - shellD0 F a) * shellNumber a = differential a - shellD0 F a
  linear_combination (norm := noncomm_ring) hQ - hd

private theorem shellNumber_h (F : Frame) (a : UCharge) :
    shellNumber a * shellH F a - shellH F a * shellNumber a = -shellH F a := by
  have hh : uNumber * h F (transverseBasis F) a - h F (transverseBasis F) a * uNumber =
      (-1 : ℂ) • h F (transverseBasis F) a :=
    (N_h F (transverseBasis F) a).trans
      (neg_one_smul ℂ (h F (transverseBasis F) a)).symm
  exact (shellNumber_lift_comm a _ (shellH F a) (fun _ => rfl) (-1) hh).trans
    (neg_one_smul ℂ (shellH F a))

private theorem shellNumber_K (F : Frame) (a : UCharge) (hp : F.pPlus a ≠ 0)
    (he : chargeEnergy hyperbolicData a ≤ 1) (n : ℕ) :
    shellNumber a * (perturbationInput F a hp he).K n =
      (perturbationInput F a hp he).K n * shellNumber a := by
  apply commutes_inversePolynomial
  change shellNumber a * (shellH F a * delta F a) =
    (shellH F a * delta F a) * shellNumber a
  have hd := shellNumber_delta F a
  have hh := shellNumber_h F a
  linear_combination (norm := noncomm_ring) hh * delta F a + shellH F a * hd

private theorem shellNumber_ground (F : Frame) (a : UCharge) (hp : F.pPlus a ≠ 0)
    (he : chargeEnergy hyperbolicData a ≤ 1) (u : LinearMap.range (shellP0 F a hp)) :
    shellNumber a u = (u : relativeMassShell a) := by
  have hu : (u : relativeMassShell a) ∈ LinearMap.range (inclusion a he) :=
    (shellP0_range F a hp he) ▸ u.property
  obtain ⟨v, hv⟩ := hu
  rw [← hv]
  apply Subtype.ext
  change nativeNumber (groundTensor a v) = groundTensor a v
  have hc : charge ({1} : Finset ℕ) = 1 := by norm_num [charge, Finset.filter_singleton]
  simp only [groundTensor, D5.S3.Quantum.Fermionic.BcGhostChargeTensor.liftGhost,
    LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, number_ket, hc, Int.cast_one, one_smul]

/-- Native ghost-number eigenspaces of the relative shell. -/
abbrev ghostSector (a : UCharge) (q : ℤ) := (shellNumber a).eigenspace (q : ℂ)

/-- Actual relative ghost-number-one cycles at fixed hyperbolic momentum. -/
def ghostOneCycles (a : UCharge) : Submodule ℂ (relativeMassShell a) :=
  ghostSector a 1 ⊓ LinearMap.ker (differential a)

private theorem differential_from_ghostZero (a : UCharge) (x : ghostSector a 0) :
    differential a x ∈ ghostOneCycles a := by
  have hx : shellNumber a x = 0 := by
    simpa only [Int.cast_zero, zero_smul] using Module.End.mem_eigenspace_iff.mp x.property
  have hq := LinearMap.congr_fun (shellNumber_Q a) (x : relativeMassShell a)
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
  · simpa only [LinearMap.sub_apply, Module.End.mul_apply, hx, map_zero, sub_zero,
      Int.cast_one, one_smul] using hq
  · exact LinearMap.congr_fun (differential_sq a) (x : relativeMassShell a)

/-- The genuine boundaries of ghost number one, with preimages in ghost number zero. -/
def ghostOneBoundaries (a : UCharge) : Submodule ℂ (ghostOneCycles a) :=
  LinearMap.range (((differential a).comp (ghostSector a 0).subtype).codRestrict
    (ghostOneCycles a) (differential_from_ghostZero a))

/-- Relative BRST cohomology in native ghost number one at momentum a. -/
abbrev GhostOneCohomology (a : UCharge) := ghostOneCycles a ⧸ ghostOneBoundaries a

private theorem correctedI_ghostOne (F : Frame) (a : UCharge) (hp : F.pPlus a ≠ 0)
    (he : chargeEnergy hyperbolicData a ≤ 1) (n : ℕ)
    (u : LinearMap.range (shellP0 F a hp)) :
    (perturbationInput F a hp he).I n u ∈ ghostSector a 1 := by
  let C := perturbationInput F a hp he
  apply Module.End.mem_eigenspace_iff.mpr
  change shellNumber a (C.K n u) = ((1 : ℤ) : ℂ) • C.K n u
  have h := LinearMap.congr_fun (shellNumber_K F a hp he n) (u : relativeMassShell a)
  simpa only [Module.End.mul_apply, shellNumber_ground F a hp he u, Int.cast_one, one_smul] using h

private theorem correctedH_ghostZero (F : Frame) (a : UCharge) (hp : F.pPlus a ≠ 0)
    (he : chargeEnergy hyperbolicData a ≤ 1) (n : ℕ)
    (x : relativeMassShell a) (hx : x ∈ ghostSector a 1) :
    (perturbationInput F a hp he).H n x ∈ ghostSector a 0 := by
  let C := perturbationInput F a hp he
  have hx' : shellNumber a x = x := by
    simpa only [Int.cast_one, one_smul] using Module.End.mem_eigenspace_iff.mp hx
  have h := LinearMap.congr_fun (shellNumber_h F a) x
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.neg_apply, hx'] at h
  have hz : shellNumber a (shellH F a x) = 0 := by
    rw [sub_eq_iff_eq_add, neg_add_cancel] at h
    exact h
  apply Module.End.mem_eigenspace_iff.mpr
  change shellNumber a (C.K n (shellH F a x)) = ((0 : ℤ) : ℂ) • C.K n (shellH F a x)
  have hk := LinearMap.congr_fun (shellNumber_K F a hp he n) (shellH F a x)
  simpa only [Module.End.mul_apply, hz, Int.cast_zero, zero_smul, map_zero] using hk

/-- The physical ghost-number-one quotient is linearly equivalent to the actual
orbifold conformal grade at any nonzero hyperbolic momentum on the mass shell. -/
def ghostOneCohomologyEquivInFrame (F : Frame) (a : UCharge) (hp : F.pPlus a ≠ 0)
    (he : chargeEnergy hyperbolicData a ≤ 1) :
    GhostOneCohomology a ≃ₗ[ℂ] orbifoldGrade (massShellCutoff hyperbolicData a) := by
  let C := perturbationInput F a hp he
  let n := 2 * massShellCutoff hyperbolicData a + 1
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hnil : (C.h * C.delta) ^ n = 0 := hdelta_nilpotent F a
  have hD : C.D = differential a := perturbation_D F a hp he
  have htr := perturbation_transferred_zero F a hp he n
  obtain ⟨hreps, hdecomp, hboundary⟩ := (C.finite_perturbation n hn hnil).representatives htr
  let p := (C.P n).comp (ghostOneCycles a).subtype
  have hsurj : Function.Surjective p := by
    intro u
    have hi := hreps u
    refine ⟨⟨C.I n u, correctedI_ghostOne F a hp he n u, ?_⟩, hi.2⟩
    apply LinearMap.mem_ker.mpr
    simpa only [hD] using hi.1
  have hker : ghostOneBoundaries a = LinearMap.ker p := by
    ext x
    have hx : C.D (x : relativeMassShell a) = 0 := by
      rw [hD]
      exact x.property.2
    constructor
    · rintro ⟨z, hz⟩
      apply (hboundary x hx).mp
      refine ⟨z, ?_⟩
      rw [hD]
      exact congrArg Subtype.val hz
    · intro hxp
      have hp0 : C.P n x = 0 := hxp
      refine ⟨⟨C.H n x, correctedH_ghostZero F a hp he n x x.property.1⟩, ?_⟩
      apply Subtype.ext
      change differential a (C.H n x) = (x : relativeMassShell a)
      have hh := hdecomp x hx
      simpa only [hp0, map_zero, sub_zero, hD] using hh.symm
  exact (Submodule.quotEquivOfEq _ _ hker).trans
    ((p.quotKerEquivOfSurjective hsurj).trans (groundEquiv F a hp he).symm)

end GhostNumber

/-- Existence of a frame gives the native ghost-number-one quotient at every
nonzero integral hyperbolic momentum of half-norm at most one. -/
def ghostOneCohomologyEquiv (a : UCharge) (ha : a ≠ 0)
    (he : chargeEnergy hyperbolicData a ≤ 1) :
    GhostOneCohomology a ≃ₗ[ℂ] orbifoldGrade (massShellCutoff hyperbolicData a) :=
  ghostOneCohomologyEquivInFrame (Classical.choose (exists_frame a ha)) a
    (Classical.choose_spec (exists_frame a ha)) he

theorem ghostOneCohomology_finrank_at_minus_one (a : UCharge)
    (he : chargeEnergy hyperbolicData a = -1) :
    Module.finrank ℂ (GhostOneCohomology a) = 196884 := by
  have ha : a ≠ 0 := by
    intro h
    subst a
    rw [LatticePositiveEnergy.chargeEnergy_zero] at he
    omega
  have hle : chargeEnergy hyperbolicData a ≤ 1 := by omega
  rw [(ghostOneCohomologyEquiv a ha hle).finrank_eq]
  have hcut : massShellCutoff hyperbolicData a = 2 := by simp [massShellCutoff, he]
  rw [hcut]
  exact TwistedGround.OriginalOrbifoldLowSpectrum.actual_leech_low_spectrum.2.2.2.2.2.1

theorem oneNegOne_ghostOneCohomology :
    Module.finrank ℂ (GhostOneCohomology (fun i => if i = 0 then 1 else -1)) = 196884 := by
  apply ghostOneCohomology_finrank_at_minus_one
  rw [hyperbolic_chargeEnergy]
  decide

end FullCharge

#print axioms fullCohomologyEquiv
#print axioms ghostOneCohomologyEquiv
#print axioms oneNegOne_ghostOneCohomology

#print axioms charge_finite_split
#print axioms hdelta_nilpotent

#print axioms exists_frame
#print axioms shell_contraction
#print axioms shellH_square
#print axioms shellP0_range
#print axioms groundEquiv
#print axioms groundEquiv_finrank_at_minus_one

end D5.S3.VertexAlgebra.OriginalOrbifoldRelativeQuartet
