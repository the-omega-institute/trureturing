/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeConformalSector
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeConformalSector
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The fixed lattice fields act on each native cubic conformal rotation eigenspace. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qCubicMonodromy
import D5.S3.VertexAlgebra.LatticeActualLZeroGrading
import OmegaBuild.Commands

/-! The fixed lattice states act by integral Laurent series on each rotation
eigenspace in the native cubic twisted carrier. The construction uses
homogeneous fixed states to prove rotation covariance and extends it to
arbitrary fixed states by the finite source energy decomposition. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeConformalSector

open scoped BigOperators VertexOperator
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open LatticeAllStateField (Y)
open LatticeAllStateReconstruction (mu)
open LatticeActualConformalState (omega)
open LatticeActualConformalWard (omega_ncoeff)
open LatticePositiveEnergy (actualL0_eigen_iff_grade gradeProjection gradeProjection_mem
  stateEnergies sum_gradeProjections)
open LatticeSugawaraCurrents (sugawaraMode)
open NativeStandardThirdLift (standardLift standardLift_compatible standardLift_omega)
open P48qAllJetWickField (NativeStates nativeField)
open P48qCubicMonodromy (conformalMonodromy conformalMonodromy_totalLZero_eigenvector)
open P48qNativeConformalZero (native_conformal_coeff_neg_six_eq_totalLZero)
open P48qNativeCurrentLocality (stripResidue stripResidue_coeff)
open P48qNativeGradingRotation (gradingRotation gradingRotation_nativeField_coeff)
open P48qNativeResidueIterate (TwistedBorcherdsAt)
open P48qThirdTwistedField (State)
open P48qTwistedChargeAction (lattice g g_cube g_isometry)
open P48qTwistedStateEnergy (totalLZero vacuum vacuum_ne_zero totalLZero_vacuum)
open SignedFieldResidueLocality (residueField residueCoefficient residueLeft residueRight)
open StateFieldResidueReconstruction (epsilon integerBinomial)
open private gram_det_unit from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qConformalVectorDecomposition
open private liftProject liftProject_eigen from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativePairwiseLocality
open private nativeField_twisted_borcherds_with_cutoff from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeResidueIterate

noncomputable section

local notation "σ" => standardLift lattice g g_cube g_isometry
local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)
local notation "Ω" => omega lattice (actualInverse lattice)
local notation "L" => sugawaraMode lattice (actualInverse lattice) 0
local notation "C" => HVertexOperator.coeff
local notation "τ" => (2 * (Real.pi : ℂ) * Complex.I)

/-- The source states fixed by the order-three standard lift. -/
def fixedStates : Submodule ℂ NativeStates :=
  Module.End.eigenspace (σ).toLinearMap 1

private theorem mem_fixedStates_iff (a : NativeStates) :
    a ∈ fixedStates ↔ σ a = a := by
  rw [fixedStates, Module.End.mem_eigenspace_iff, LinearEquiv.coe_toLinearMap, one_smul]

private theorem lift_fixed (a : fixedStates) : σ a.val = a.val :=
  (mem_fixedStates_iff a.val).mp a.property

private theorem lift_omega : σ Ω = Ω :=
  standardLift_omega lattice g g_cube g_isometry (actualInverse lattice)
    (actualInverse_left lattice gram_det_unit)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem lift_sourceLZero (a : NativeStates) : σ (L a) = L (σ a) := by
  have h : σ (((Y lattice Ω)[[1]]) a) = ((Y lattice (σ Ω))[[1]]) (σ a) :=
    (standardLift_compatible lattice g g_cube g_isometry).2.1 Ω 1 a
  have hmode : ((Y lattice Ω)[[1]]) = L := by
    rw [omega_ncoeff, sub_self]
  simpa only [lift_omega, hmode] using h

private def fixedProjection : Module.End ℂ NativeStates :=
  (3 : ℂ)⁻¹ • (LinearMap.id + (σ).toLinearMap + (σ).toLinearMap.comp (σ).toLinearMap)

private theorem fixedProjection_fixed (a : NativeStates) :
    σ (fixedProjection a) = fixedProjection a := by
  have he : fixedProjection a = liftProject 0 a := by
    change (3 : ℂ)⁻¹ • (a + σ a + σ (σ a)) = liftProject 0 a
    simp only [liftProject, Fin.val_zero, pow_zero, one_pow, one_smul]
  rw [he]
  simpa only [Fin.val_zero, pow_zero, one_pow, one_smul] using liftProject_eigen 0 a

private theorem fixedProjection_eq_self (a : NativeStates) (ha : σ a = a) :
    fixedProjection a = a := by
  change (3 : ℂ)⁻¹ • (a + σ a + σ (σ a)) = a
  simp only [ha]
  have hthree : a + a + a = (3 : ℂ) • a := by module
  rw [hthree, smul_smul, inv_mul_cancel₀ (by norm_num : (3 : ℂ) ≠ 0), one_smul]

set_option maxRecDepth 4096 in
private theorem sourceLZero_fixedProjection (a : NativeStates) :
    L (fixedProjection a) = fixedProjection (L a) := by
  simp only [fixedProjection, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, map_smul, map_add, ← lift_sourceLZero]

/-- Rotation commutes with every coefficient of a fixed field, including
when the source state has mixed conformal weights. -/
theorem gradingRotation_fixed_coeff (a : fixedStates) (k : ℤ) :
    gradingRotation * C (nativeField a.val) k = C (nativeField a.val) k * gradingRotation := by
  let read : NativeStates →ₗ[ℂ] Module.End ℂ State :=
    ((LinearMap.proj k).comp HVertexOperator.coeff).comp nativeField
  have hsum := congrArg fixedProjection (sum_gradeProjections lattice a.val)
  rw [map_sum, fixedProjection_eq_self a.val (lift_fixed a)] at hsum
  change gradingRotation * read a.val = read a.val * gradingRotation
  rw [← hsum]
  simp only [map_sum, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _
  let x := gradeProjection lattice h a.val
  have hx : L x = (h : ℂ) • x :=
    (actualL0_eigen_iff_grade lattice (actualInverse lattice)
      (actualInverse_left lattice gram_det_unit) (actualInverse_right lattice gram_det_unit)
      h x).mpr (gradeProjection_mem lattice h a.val)
  have hw : L (fixedProjection x) = (h : ℂ) • fixedProjection x := by
    rw [sourceLZero_fixedProjection, hx, map_smul]
  have hf : σ (fixedProjection x) = ζ ^ (0 : ℤ) • fixedProjection x := by
    simpa only [zpow_zero, one_smul] using fixedProjection_fixed x
  simpa only [read, LinearMap.comp_apply, LinearMap.proj_apply, zpow_zero, one_smul]
    using gradingRotation_nativeField_coeff (fixedProjection x) 0 hf k h hw

/-- The native eigenspace with normalized rotation eigenvalue `ζ^s`. -/
def sector (s : Fin 3) : Submodule ℂ State := gradingRotation.eigenspace (ζ ^ s.val)

private theorem nativeCoeff_mem (s : Fin 3) (a : fixedStates) (k : ℤ)
    (v : State) (hv : v ∈ sector s) : C (nativeField a.val) k v ∈ sector s := by
  rw [sector, Module.End.mem_eigenspace_iff] at hv ⊢
  have h := LinearMap.congr_fun (gradingRotation_fixed_coeff a k) v
  change gradingRotation (C (nativeField a.val) k v) =
    C (nativeField a.val) k (gradingRotation v) at h
  exact h.trans (by rw [hv, map_smul])

private def restrictedCoeff (s : Fin 3) (a : fixedStates) (k : ℤ) :
    Module.End ℂ (sector s) :=
  (C (nativeField a.val) (3 * k)).restrict (nativeCoeff_mem s a (3 * k))

private def restrictedField (s : Fin 3) (a : fixedStates) :
    VertexOperator ℂ (sector s) :=
  VertexOperator.of_coeff (restrictedCoeff s a) (by
    intro v
    let A := stripResidue 0 (nativeField a.val)
    refine ⟨((HahnModule.of ℂ).symm (A v.val)).order, ?_⟩
    intro k hk
    by_contra h
    apply hk
    apply Subtype.ext
    change C (nativeField a.val) (3 * k) v.val = 0
    simpa only [A, stripResidue_coeff, add_zero] using
      VertexOperator.coeff_eq_zero_of_lt_order A k v.val (lt_of_not_ge h))

private theorem restrictedField_coeff_val (s : Fin 3) (a : fixedStates)
    (k : ℤ) (v : sector s) :
    (C (restrictedField s a) k v).val = C (nativeField a.val) (3 * k) v.val := rfl

/-- The fixed-state field map on the sector, in the integral coordinate. -/
def fixedField (s : Fin 3) : fixedStates →ₗ[ℂ] VertexOperator ℂ (sector s) where
  toFun := restrictedField s
  map_add' a b := by
    apply HVertexOperator.coeff_inj
    funext k
    apply LinearMap.ext
    intro v
    change C (restrictedField s (a + b)) k v =
      C (restrictedField s a + restrictedField s b) k v
    simp only [map_add, Pi.add_apply, LinearMap.add_apply]
    apply Subtype.ext
    simp only [restrictedField_coeff_val, Submodule.coe_add, map_add, Pi.add_apply,
      LinearMap.add_apply]
  map_smul' c a := by
    apply HVertexOperator.coeff_inj
    funext k
    apply LinearMap.ext
    intro v
    change C (restrictedField s (c • a)) k v = C (c • restrictedField s a) k v
    simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply]
    apply Subtype.ext
    simp only [restrictedField_coeff_val, Submodule.coe_smul, map_smul, Pi.smul_apply,
      LinearMap.smul_apply]

/-- The inclusion into the native carrier intertwines every integral
coefficient with the original coefficient at the corresponding cover exponent. -/
theorem fixedField_coeff_val (s : Fin 3) (a : fixedStates) (k : ℤ) (v : sector s) :
    (C (fixedField s a) k v).val = C (nativeField a.val) (3 * k) v.val :=
  restrictedField_coeff_val s a k v

/-- The untwisted lattice vacuum in the fixed source. -/
def fixedVacuum : fixedStates :=
  ⟨(LatticeAllStateField.vacuum lattice : NativeStates),
    (mem_fixedStates_iff _).mpr (standardLift_compatible lattice g g_cube g_isometry).1⟩

/-- The vacuum acts as the identity field on every native sector. -/
theorem fixedField_vacuum_coeff (s : Fin 3) (k : ℤ) :
    C (fixedField s fixedVacuum) k = if k = 0 then 1 else 0 := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  rw [fixedField_coeff_val]
  change C (nativeField (LatticeAllStateField.vacuum lattice)) (3 * k) v.val = _
  rw [LatticeAllStateField.vacuum, P48qAllJetWickField.nativeField_ground,
    P48qTwistedGeneratorVacuum.concreteChargedField_zero_coeff]
  by_cases hk : k = 0
  · have hcover : 3 * k = 0 := by rw [hk, mul_zero]
    simp only [if_pos hcover, if_pos hk, LinearMap.id_apply, Module.End.one_apply] <;> rfl
  · have hcover : 3 * k ≠ 0 := by omega
    simp only [if_neg hcover, if_neg hk, LinearMap.zero_apply, Submodule.coe_zero]

/-- The actual source product of fixed states, closed by standard-lift covariance. -/
def fixedProduct (a b : fixedStates) (n : ℤ) : fixedStates :=
  ⟨mu lattice a.val n b.val, (mem_fixedStates_iff _).mpr (by
    simpa only [mu, lift_fixed a, lift_fixed b] using
      (standardLift_compatible lattice g g_cube g_isometry).2.1 a.val n b.val)⟩

/-- The integral mixed Borcherds identity on the sector, with the actual
fixed-state iterate. Its finite right-hand cutoff is inherited from the source. -/
theorem fixedField_borcherds (s : Fin 3) (a b : fixedStates) :
    ∃ N : ℕ, (∀ j ≥ (N : ℤ), fixedProduct a b j = 0) ∧
      ∀ (p q n : ℤ) (v : sector s),
        (∑ᶠ j : ℕ, (((-1 : ℂ) ^ j) * integerBinomial n j) •
          ((fixedField s a)[[p + n - j]]) (((fixedField s b)[[q + j]]) v)) -
          epsilon n • (∑ᶠ j : ℕ, (((-1 : ℂ) ^ j) * integerBinomial n j) •
            ((fixedField s b)[[q + n - j]]) (((fixedField s a)[[p + j]]) v)) =
          ∑ j ∈ Finset.range ((N : ℤ) - n).toNat,
            Ring.choose (p : ℂ) j •
              ((fixedField s (fixedProduct a b (n + j)))[[p + q - j]]) v := by
  have ha : σ a.val = ζ ^ (0 : ℤ) • a.val := by
    simpa only [zpow_zero, one_smul] using lift_fixed a
  have hb : σ b.val = ζ ^ (0 : ℤ) • b.val := by
    simpa only [zpow_zero, one_smul] using lift_fixed b
  obtain ⟨N, hcut, hB⟩ := nativeField_twisted_borcherds_with_cutoff a.val b.val 0 0 ha hb
  refine ⟨N, fun j hj => Subtype.ext (hcut j hj), ?_⟩
  intro p q n v
  let A := stripResidue (0 - 3 * p) (nativeField a.val)
  let B := stripResidue 0 (nativeField b.val)
  let incl : sector s →ₗ[ℂ] State := (sector s).subtype
  have hincl : Function.Injective incl := Subtype.val_injective
  have haMode (m : ℤ) (w : sector s) :
      incl (((fixedField s a)[[p + m]]) w) = (A[[m]]) (incl w) := by
    change (((fixedField s a)[[p + m]]) w).val = (A[[m]]) w.val
    simp only [A, VertexOperator.ncoeff_apply, fixedField_coeff_val, stripResidue_coeff]
    rw [show 3 * (-(p + m) - 1) = 3 * (-m - 1) + (0 - 3 * p) by ring]
  have hbMode (m : ℤ) (w : sector s) :
      incl (((fixedField s b)[[m]]) w) = (B[[m]]) (incl w) := by
    change (((fixedField s b)[[m]]) w).val = (B[[m]]) w.val
    simp only [B, VertexOperator.ncoeff_apply, fixedField_coeff_val, stripResidue_coeff,
      add_zero]
  have h := LinearMap.congr_fun
    ((show TwistedBorcherdsAt nativeField a.val b.val 0 0 N from hB) p q n) (incl v)
  change (((residueField 1 n A B).operator)[[q]]) (incl v) = _ at h
  rw [(residueField 1 n A B).coefficient] at h
  apply hincl
  rw [map_sub, map_smul, map_sum]
  let left (j : ℕ) := (((-1 : ℂ) ^ j) * integerBinomial n j) •
    ((fixedField s a)[[p + n - j]]) (((fixedField s b)[[q + j]]) v)
  let right (j : ℕ) := (((-1 : ℂ) ^ j) * integerBinomial n j) •
    ((fixedField s b)[[q + n - j]]) (((fixedField s a)[[p + j]]) v)
  have hl : incl (∑ᶠ j, left j) = residueLeft n q A B (incl v) := by
    rw [show incl (∑ᶠ j, left j) = ∑ᶠ j, incl (left j) from
      incl.toAddMonoidHom.map_finsum_of_injective hincl left]
    unfold residueLeft
    apply finsum_congr
    intro j
    simp only [left, map_smul, show p + n - (j : ℤ) = p + (n - j) by ring, haMode, hbMode]
  have hr : incl (∑ᶠ j, right j) = residueRight n q A B (incl v) := by
    rw [show incl (∑ᶠ j, right j) = ∑ᶠ j, incl (right j) from
      incl.toAddMonoidHom.map_finsum_of_injective hincl right]
    unfold residueRight
    apply finsum_congr
    intro j
    simp only [right, map_smul, add_comm q n, haMode, hbMode]
  change incl (∑ᶠ j, left j) - epsilon n • incl (∑ᶠ j, right j) = _
  rw [hl, hr]
  simp only [residueCoefficient, mul_one, Int.cast_zero, zero_div, sub_zero, zero_add,
    zero_sub, LinearMap.sum_apply, LinearMap.smul_apply] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]
  apply congrArg (fun w : State => Ring.choose (p : ℂ) j • w)
  change C (nativeField (mu lattice a.val (n + j) b.val)) (-(3 * (p + q - j + 1))) v.val =
    (((fixedField s (fixedProduct a b (n + j)))[[p + q - j]]) v).val
  simp only [VertexOperator.ncoeff_apply, fixedField_coeff_val,
    show -(3 * (p + q - (j : ℤ) + 1)) = 3 * (-(p + q - j) - 1) by ring] <;> rfl

/-- The actual lattice conformal vector belongs to the fixed algebra. -/
def fixedOmega : fixedStates :=
  ⟨(Ω : NativeStates), (mem_fixedStates_iff _).mpr lift_omega⟩

/-- The zero mode of the restricted conformal field agrees with the actual
twisted conformal zero mode on the ambient carrier. -/
theorem fixedField_conformal_zero (s : Fin 3) (v : sector s) :
    (C (fixedField s fixedOmega) (-2) v).val = totalLZero v.val := by
  rw [fixedField_coeff_val, show 3 * (-2 : ℤ) = -6 by decide]
  change C (nativeField Ω) (-6) v.val = totalLZero v.val
  exact LinearMap.congr_fun native_conformal_coeff_neg_six_eq_totalLZero v.val

/-- Conformal monodromy is scalar on every native sector, with the original
vacuum phase on the sector of normalized eigenvalue one. -/
theorem conformalMonodromy_sector (s : Fin 3) (v : sector s) :
    conformalMonodromy v.val = (Complex.exp (τ * (16 / 9)) * ζ ^ s.val) • v.val := by
  have hv : gradingRotation v.val = ζ ^ s.val • v.val :=
    Module.End.mem_eigenspace_iff.mp v.property
  rw [conformalMonodromy, LinearMap.smul_apply, hv, smul_smul]

/-- The actual twisted ground state is nonzero in the sector with phase `e(16/9)`. -/
theorem vacuum_mem_sector_zero : vacuum ∈ sector 0 := by
  rw [sector, Module.End.mem_eigenspace_iff, Fin.val_zero, pow_zero, one_smul]
  have h := conformalMonodromy_totalLZero_eigenvector vacuum (16 / 9) totalLZero_vacuum
  change Complex.exp (τ * (16 / 9)) • gradingRotation vacuum =
    Complex.exp (τ * (16 / 9)) • vacuum at h
  have hc := congrArg (fun w : State => (Complex.exp (τ * (16 / 9)))⁻¹ • w) h
  simpa only [smul_smul, inv_mul_cancel₀ (Complex.exp_ne_zero _), one_smul] using hc

theorem sector_zero_ne_bot : sector 0 ≠ ⊥ := by
  intro h
  exact vacuum_ne_zero (by simpa only [h, Submodule.mem_bot] using vacuum_mem_sector_zero)

#print axioms fixedField
#print axioms fixedField_vacuum_coeff
#print axioms fixedField_borcherds
#print axioms fixedField_conformal_zero
#print axioms conformalMonodromy_sector
#print axioms sector_zero_ne_bot

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeConformalSector
