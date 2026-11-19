/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeShellQuartet
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeShellQuartet
   mirror-E: none(waiver:algebraic-original-orbifold-relative-shell-quartet)
   anchors: []
   utility: none
   digest: Native shell quartet contraction and its orbifold ground equivalence. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeMassShell
import D5.S3.VertexAlgebra.Lattice.LatticeRelativeBRSTGround
import D5.S3.VertexAlgebra.Lattice.LatticeNullFrameExistence

/-! The quartet contraction and its range on the native relative mass shell. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

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
  simp only [← mem_fixedMomentum_iff_chargeProject,
    LatticeRelativeMassShell.mem_fixedMomentum_iff,
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
    groundTensor a u =
      assoc.symm (u ⊗ₜ[ℂ] actualBasis F (transverseBasis F) (groundIndex a)) := by
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
  have hs : (y : State) ∈
      LinearMap.range ((relativeMassShell a).subtype.comp (inclusion a ha)) := by
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

#print axioms exists_frame
#print axioms shell_contraction
#print axioms shellH_square
#print axioms shellP0_range
#print axioms groundEquiv
#print axioms groundEquiv_finrank_at_minus_one

end D5.S3.VertexAlgebra.OriginalOrbifoldRelativeQuartet
