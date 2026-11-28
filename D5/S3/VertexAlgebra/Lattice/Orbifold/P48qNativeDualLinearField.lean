/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeDualLinearField
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeDualLinearField
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual restricted-dual field on all source states with vacuum and inverse residue. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeRestrictedDualField
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualResidue
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualTranslation
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFieldCarrierTransport
import OmegaBuild.Commands

/-! The actual lattice energy decomposition extends the homogeneous BPZ field
to the full source. The source lift preserves this decomposition, so coordinate
inversion reverses residues even for eigenstates of mixed conformal weight. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualLinearField

open scoped BigOperators DirectSum
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open LatticeActualConformalState (omega)
open LatticeActualConformalWard (omega_ncoeff)
open LatticeAllStateField (vacuum stateField_creativity)
open LatticePositiveEnergy (actualL0_eigen_iff_grade carrierCoeffEquiv carrierEnergyDecomposition
  chargeEnergy_nonneg energy grade mem_grade_iff)
open LatticeSugawaraConformal (translation)
open LatticeSugawaraCurrents (sugawaraMode)
open NativeStandardThirdLift (standardLift)
open P48qAllJetWickField (NativeStates nativeField nativeField_ground)
open P48qFieldCarrierTransport (InResidueOn)
open P48qNativeDualCoefficients (bpzCoeff bpzCoeff_apply_val)
open P48qNativeDualResidue (bpzDualCoeff_eq_zero_of_residue_ne)
open P48qNativeDualTranslation (oppositeField_translate_coeff)
open P48qNativeRestrictedDualField (ActualGrade GradeDual RestrictedDual coeff coeff_lof
  gradeCoeff oppositeField oppositeField_coeff shiftedGradeEquiv shiftedWeight)
open P48qThirdTwistedField (State)
open P48qTwistedChargeAction (lattice g g_cube g_isometry)
open P48qTwistedGeneratorVacuum (concreteChargedField_zero_coeff)
open private gram_det_unit from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qConformalVectorDecomposition
open private lift_sourceLZero from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeConformalSector
open private sourceLMinusOne_eq_translation source_translation_weight from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualTranslation

noncomputable section

local notation "L₀" => sugawaraMode lattice (actualInverse lattice) 0
local notation "L₁" => sugawaraMode lattice (actualInverse lattice) 1
local notation "T" => sugawaraMode lattice (actualInverse lattice) (-1)
local notation "σ" => standardLift lattice g g_cube g_isometry
local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)
local notation "C" => HVertexOperator.coeff

private abbrev SourceGrade (n : ℤ) : Type := ↥(LatticePositiveEnergy.grade lattice n)

private theorem source_grade_iff (n : ℤ) (a : NativeStates) :
    L₀ a = (n : ℂ) • a ↔ a ∈ grade lattice n :=
  actualL0_eigen_iff_grade lattice (actualInverse lattice)
    (actualInverse_left lattice gram_det_unit) (actualInverse_right lattice gram_det_unit) n a

private theorem source_grade_weight (n : ℤ) (a : grade lattice n) :
    L₀ a.val = (n.toNat : ℂ) • a.val := by
  by_cases hn : 0 ≤ n
  · have hc := congrArg (Int.cast : ℤ → ℂ) (Int.toNat_of_nonneg hn)
    rw [Int.cast_natCast] at hc
    rw [hc]
    exact (source_grade_iff n a.val).mpr a.property
  · have hz : a.val = 0 := by
      apply (carrierCoeffEquiv lattice).injective
      apply Finsupp.ext
      intro b
      rw [map_zero, Finsupp.zero_apply]
      change (a.val b.1).coeff b.2 = 0
      apply (mem_grade_iff lattice n a.val).mp a.property b
      have hb := chargeEnergy_nonneg lattice P48qGramPositivity.nebeGram_posDef b.1
      dsimp only [energy]
      omega
    rw [hz, map_zero, smul_zero]

private def bpzReadout (n : ℤ) (w : ℝ) (k : ℤ)
    (v : ActualGrade (shiftedWeight w n.toNat k)) : grade lattice n →ₗ[ℂ] ActualGrade w := by
  let u := shiftedGradeEquiv w n.toNat k v
  let term (j : ℕ) : grade lattice n →ₗ[ℂ] State :=
    (LinearMap.applyₗ (R := ℂ) u.val).comp
      ((LinearMap.proj (-k - 6 * (n.toNat : ℤ) + 3 * (j : ℤ))).comp
        ((C).comp (nativeField.comp ((L₁ ^ j).comp (grade lattice n).subtype))))
  let readout := (-1 : ℂ) ^ n.toNat • ∑ j ∈ Finset.range (n.toNat + 1),
    (j.factorial : ℂ)⁻¹ • term j
  exact readout.codRestrict _ (fun a => by
    have h := (bpzCoeff a.val n.toNat (source_grade_weight n a) (w : ℂ) k u).property
    rw [bpzCoeff_apply_val] at h
    simpa only [readout, term, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.applyₗ_apply_apply, LinearMap.proj_apply, Submodule.coe_subtype] using h)

private theorem gradeCoeff_eval (n : ℤ) (a : grade lattice n) (w : ℝ) (k : ℤ)
    (f : GradeDual w) (v : ActualGrade (shiftedWeight w n.toNat k)) :
    gradeCoeff a.val n.toNat (source_grade_weight n a) w k f v = f (bpzReadout n w k v a) := by
  change f (bpzCoeff a.val n.toNat (source_grade_weight n a) (w : ℂ) k
    (shiftedGradeEquiv w n.toNat k v)) = _
  apply congrArg (fun u : ActualGrade w => f u)
  apply Subtype.ext
  rw [bpzCoeff_apply_val]
  simp only [bpzReadout, LinearMap.codRestrict_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.applyₗ_apply_apply, LinearMap.proj_apply, Submodule.coe_subtype]

private def gradedField (n : ℤ) : grade lattice n →ₗ[ℂ] VertexOperator ℂ RestrictedDual where
  toFun a := oppositeField a.val n.toNat (source_grade_weight n a)
  map_add' a b := by
    classical
    apply HVertexOperator.coeff_inj
    funext k
    simp only [map_add, Pi.add_apply, oppositeField_coeff]
    apply DirectSum.linearMap_ext
    intro w
    apply LinearMap.ext
    intro f
    simp only [LinearMap.comp_apply, LinearMap.add_apply, coeff_lof]
    rw [← map_add]
    apply congrArg (DirectSum.lof ℂ ℝ GradeDual (shiftedWeight w n.toNat k))
    apply LinearMap.ext
    intro v
    simp only [LinearMap.add_apply, gradeCoeff_eval, map_add]
  map_smul' c a := by
    classical
    apply HVertexOperator.coeff_inj
    funext k
    simp only [RingHom.id_apply, map_smul, Pi.smul_apply, oppositeField_coeff]
    apply DirectSum.linearMap_ext
    intro w
    apply LinearMap.ext
    intro f
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, coeff_lof]
    rw [← map_smul]
    apply congrArg (DirectSum.lof ℂ ℝ GradeDual (shiftedWeight w n.toNat k))
    apply LinearMap.ext
    intro v
    simp only [LinearMap.smul_apply, gradeCoeff_eval, map_smul]

/-- The BPZ field on the actual restricted dual with arbitrary source states. -/
def dualField : NativeStates →ₗ[ℂ] VertexOperator ℂ RestrictedDual :=
  (DirectSum.toModule ℂ ℤ (VertexOperator ℂ RestrictedDual) gradedField).comp
    (carrierEnergyDecomposition lattice).toLinearMap

/-- The full linear field agrees with the given BPZ field on each source weight. -/
theorem dualField_homogeneous (a : NativeStates) (d : ℕ) (ha : L₀ a = (d : ℂ) • a) :
    dualField a = oppositeField a d ha := by
  classical
  let u : grade lattice (d : ℤ) := ⟨a, (source_grade_iff (d : ℤ) a).mp
    (by simpa only [Int.cast_natCast] using ha)⟩
  have h : carrierEnergyDecomposition lattice a =
      DirectSum.lof ℂ ℤ SourceGrade (d : ℤ) u := by
    apply (carrierEnergyDecomposition lattice).symm.injective
    rw [LinearEquiv.symm_apply_apply]
    exact (DirectSum.coeLinearMap_lof (grade lattice) (d : ℤ) u).symm
  change DirectSum.toModule ℂ ℤ (VertexOperator ℂ RestrictedDual) gradedField
    (carrierEnergyDecomposition lattice a) = _
  rw [h, DirectSum.toModule_lof] <;> rfl

/-- Source translation differentiates the full restricted-dual field in `z = x^3`. -/
theorem dualField_translate_coeff (a : NativeStates) (j : ℤ) :
    C (dualField (translation lattice a)) j =
      (((j + 3 : ℤ) : ℂ) / 3) • C (dualField a) (j + 3) := by
  classical
  let read (k : ℤ) : NativeStates →ₗ[ℂ] Module.End ℂ RestrictedDual :=
    ((LinearMap.proj k).comp C).comp dualField
  let sumGrades := DirectSum.coeLinearMap (grade lattice)
  have h : ((read j).comp T).comp sumGrades =
      ((((j + 3 : ℤ) : ℂ) / 3) • read (j + 3)).comp sumGrades := by
    apply DirectSum.linearMap_ext
    intro n
    apply LinearMap.ext
    intro u
    have hu := source_grade_weight n u
    simp only [LinearMap.comp_apply, sumGrades, DirectSum.coeLinearMap_lof,
      LinearMap.smul_apply, read, LinearMap.proj_apply]
    rw [dualField_homogeneous (T u.val) (n.toNat + 1) (source_translation_weight u.val n.toNat hu),
      dualField_homogeneous u.val n.toNat hu]
    exact oppositeField_translate_coeff u.val n.toNat hu j
  have hSum : sumGrades (carrierEnergyDecomposition lattice a) = a :=
    (carrierEnergyDecomposition lattice).symm_apply_apply a
  rw [← sourceLMinusOne_eq_translation]
  simpa only [LinearMap.comp_apply, LinearMap.smul_apply, hSum, read, LinearMap.proj_apply]
    using LinearMap.congr_fun h (carrierEnergyDecomposition lattice a)

private def liftOnGrade (n : ℤ) : grade lattice n →ₗ[ℂ] grade lattice n :=
  (σ).toLinearMap.restrict (fun a ha => (source_grade_iff n (σ a)).mp (by
    rw [← lift_sourceLZero, (source_grade_iff n a).mpr ha, map_smul]))

private theorem lift_on_decomposition (a : NativeStates) :
    DirectSum.lmap liftOnGrade (carrierEnergyDecomposition lattice a) =
      carrierEnergyDecomposition lattice (σ a) := by
  classical
  have h : (DirectSum.coeLinearMap (grade lattice)).comp (DirectSum.lmap liftOnGrade) =
      (σ).toLinearMap.comp (DirectSum.coeLinearMap (grade lattice)) := by
    apply DirectSum.linearMap_ext
    intro n
    apply LinearMap.ext
    intro u
    simp only [LinearMap.comp_apply, DirectSum.lmap_lof, DirectSum.coeLinearMap_lof,
      liftOnGrade, LinearMap.coe_restrict_apply]
  apply (carrierEnergyDecomposition lattice).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change ((DirectSum.coeLinearMap (grade lattice)).comp (DirectSum.lmap liftOnGrade))
    (carrierEnergyDecomposition lattice a) = σ a
  rw [h, LinearMap.comp_apply]
  exact congrArg (fun v : NativeStates => σ v)
    ((carrierEnergyDecomposition lattice).symm_apply_apply a)

/-- A lift eigenstate of eigenvalue `ζ^s` occupies residue `-s` on the dual. -/
theorem dualField_inResidue (a : NativeStates) (s : ℤ) (ha : σ a = ζ ^ s • a) :
    InResidueOn (-s) (dualField a) := by
  classical
  intro k hk
  let x := carrierEnergyDecomposition lattice a
  have hx : DirectSum.lmap liftOnGrade x = ζ ^ s • x := by
    rw [lift_on_decomposition a, ha, map_smul]
  have hEigen (n : ℤ) : (x n).val ∈ Module.End.eigenspace (σ).toLinearMap (ζ ^ s) := by
    apply Module.End.mem_eigenspace_iff.mpr
    have hn := congrArg (fun y : (⨁ m : ℤ, grade lattice m) => (y n).val) hx
    simpa only [DirectSum.lmap_apply, DirectSum.smul_apply, Submodule.coe_smul, liftOnGrade,
      LinearMap.coe_restrict_apply] using hn
  let read := ((LinearMap.proj k).comp C).comp
    (DirectSum.toModule ℂ ℤ (VertexOperator ℂ RestrictedDual) gradedField)
  change read x = 0
  have hsum : (∑ n ∈ x.support, DirectSum.lof ℂ ℤ SourceGrade n (x n)) = x := by
    simpa only [DirectSum.lof_eq_of] using DirectSum.sum_support_of x
  rw [← hsum, map_sum]
  apply Finset.sum_eq_zero
  intro n _
  change C (DirectSum.toModule ℂ ℤ (VertexOperator ℂ RestrictedDual) gradedField
    (DirectSum.lof ℂ ℤ SourceGrade n (x n))) k = 0
  rw [DirectSum.toModule_lof]
  change coeff (x n).val n.toNat (source_grade_weight n (x n)) k = 0
  apply DirectSum.linearMap_ext
  intro w
  apply LinearMap.ext
  intro f
  simp only [LinearMap.comp_apply, coeff_lof, LinearMap.zero_apply, gradeCoeff,
    bpzDualCoeff_eq_zero_of_residue_ne (x n).val n.toNat (source_grade_weight n (x n))
      s (hEigen n) (w : ℂ) k hk, map_zero]

/-- The residue clause for the inverse of the standard source lift. -/
theorem dualField_inverse_residue (a : NativeStates) (s : ℤ) (ha : (σ).symm a = ζ ^ s • a) :
    InResidueOn s (dualField a) := by
  have h := congrArg (fun v : NativeStates => σ v) ha
  change σ ((σ).symm a) = σ (ζ ^ s • a) at h
  rw [LinearEquiv.apply_symm_apply, map_smul] at h
  have hInv : σ a = ζ ^ (-s) • a := calc
    σ a = (ζ ^ s)⁻¹ • (ζ ^ s • σ a) := by
      rw [smul_smul, inv_mul_cancel₀ (zpow_ne_zero s (Units.ne_zero ThirdTwistedChargeCocycle.zeta)),
        one_smul]
    _ = ζ ^ (-s) • a := by rw [← h, zpow_neg]
  simpa only [neg_neg] using dualField_inResidue a (-s) hInv

private theorem vacuum_weight : L₀ (vacuum lattice) = ((0 : ℕ) : ℂ) • vacuum lattice := by
  have h := stateField_creativity lattice (omega lattice (actualInverse lattice)) 1 (by decide)
  rw [omega_ncoeff, sub_self] at h
  simpa only [Nat.cast_zero, zero_smul] using h

private theorem vacuum_bpz_apply (w : ℝ) (k : ℤ) (u : ActualGrade (shiftedWeight w 0 k)) :
    (bpzCoeff (vacuum lattice) 0 vacuum_weight (w : ℂ) k (shiftedGradeEquiv w 0 k u)).val =
      if k = 0 then u.val else 0 := by
  have hu : (shiftedGradeEquiv w 0 k u).val = u.val := by
    unfold shiftedGradeEquiv
    exact LinearEquiv.coe_ofEq_apply _ u
  have hNative : C (nativeField (vacuum lattice)) (-k) =
      if -k = 0 then (1 : Module.End ℂ State) else 0 := by
    rw [vacuum, nativeField_ground]
    exact concreteChargedField_zero_coeff (-k)
  rw [bpzCoeff_apply_val, Finset.sum_range_one, hu]
  simp only [pow_zero, one_smul, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one, inv_one,
    Nat.cast_zero, mul_zero, sub_zero, add_zero, hNative, neg_eq_zero]
  split_ifs <;> rfl

private theorem lof_eq_of_apply {p q : ℝ} (hpq : p = q) (f : GradeDual p) (g' : GradeDual q)
    (h : ∀ (u : ActualGrade p) (v : ActualGrade q), u.val = v.val → f u = g' v) :
    DirectSum.lof ℂ ℝ GradeDual p f = DirectSum.lof ℂ ℝ GradeDual q g' := by
  subst q
  exact congrArg (DirectSum.lof ℂ ℝ GradeDual p) (LinearMap.ext fun v => h v v rfl)

/-- The source vacuum acts as the constant identity field on the actual dual. -/
theorem dualField_vacuum : dualField (vacuum lattice) =
    (show VertexOperator ℂ RestrictedDual from
      HahnSeries.single.linearMap (R := ℂ) (V := RestrictedDual) (0 : ℤ)) := by
  classical
  rw [dualField_homogeneous _ 0 vacuum_weight]
  apply HVertexOperator.coeff_inj
  funext k
  have hSingle : C (HahnSeries.single.linearMap (R := ℂ) (V := RestrictedDual) (0 : ℤ)) k =
      if k = 0 then (1 : Module.End ℂ RestrictedDual) else 0 := by
    apply LinearMap.ext
    intro f
    change (HahnSeries.single (0 : ℤ) f).coeff k = _
    rw [HahnSeries.coeff_single]
    split_ifs <;> rfl
  rw [oppositeField_coeff, hSingle]
  apply DirectSum.linearMap_ext
  intro w
  apply LinearMap.ext
  intro f
  simp only [LinearMap.comp_apply, coeff_lof]
  by_cases hk : k = 0
  · subst k
    rw [if_pos rfl, Module.End.one_apply]
    apply lof_eq_of_apply (by simp [shiftedWeight])
    intro u v huv
    change f (bpzCoeff (vacuum lattice) 0 vacuum_weight (w : ℂ) 0
      (shiftedGradeEquiv w 0 0 u)) = f v
    exact congrArg (fun v' : ActualGrade w => f v')
      (Subtype.ext ((vacuum_bpz_apply w 0 u).trans ((if_pos rfl).trans huv)))
  · rw [if_neg hk, LinearMap.zero_apply]
    have hz : gradeCoeff (vacuum lattice) 0 vacuum_weight w k f = 0 := by
      apply LinearMap.ext
      intro u
      change f (bpzCoeff (vacuum lattice) 0 vacuum_weight (w : ℂ) k
        (shiftedGradeEquiv w 0 k u)) = 0
      have h : bpzCoeff (vacuum lattice) 0 vacuum_weight (w : ℂ) k
          (shiftedGradeEquiv w 0 k u) = 0 :=
        Subtype.ext ((vacuum_bpz_apply w k u).trans (if_neg hk))
      rw [h, map_zero]
    rw [hz, map_zero]

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualLinearField
