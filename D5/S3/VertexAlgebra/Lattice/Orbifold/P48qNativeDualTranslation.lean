/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeDualTranslation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeDualTranslation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual source translation of the native cubic field and its BPZ restricted dual. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeRestrictedDualField
import Batteries.Tactic.OpenPrivate
import OmegaBuild.Commands

/-! The vacuum residue gives source translation on each lift eigenspace.
Projection onto the residue of the output coefficient extends it to the
whole source. Coordinate inversion then gives source translation on the
restricted dual, with the physical derivative in `z = x^3`. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualTranslation

open scoped BigOperators Classical DirectSum
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open LatticeActualVertexAlgebra (translation_as_mode)
open LatticeAllStateField (vacuum)
open LatticeAllStateReconstruction (mu)
open LatticeSugawaraConformal (translation sugawaraMode_minus_one_eq_translation)
open LatticeSugawaraCurrents (sugawaraMode)
open LatticeSugawaraVirasoro (sugawaraMode_virasoro)
open NativeStandardThirdLift (standardLift standardLift_compatible)
open P48qAllJetWickField (NativeStates nativeField)
open P48qNativeDualCoefficients
  (bpzTerm bpzCoeff bpzCoeff_apply_val sourceLOne_pow_eq_zero_of_lt)
open P48qNativeRestrictedDualField
  (ActualGrade GradeDual shiftedWeight shiftedGradeEquiv gradeCoeff coeff_lof
    oppositeField oppositeField_coeff)
open P48qNativeVirasoro (native_vacuum_minus_two_fractional_mode)
open P48qThirdTwistedField (State)
open P48qTwistedChargeAction (lattice g g_cube g_isometry)
open private gram_det_unit from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qConformalVectorDecomposition
open private residueIndex liftProject_residue_coeff liftProject_residue_eigen from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeModeProductSpan
open private liftProject from D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativePairwiseLocality
open private sourceLOne_pow_weight from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualCoefficients

noncomputable section

local notation "C" => HVertexOperator.coeff
local notation "σ" => standardLift lattice g g_cube g_isometry
local notation "L₀" => sugawaraMode lattice (actualInverse lattice) 0
local notation "L₁" => sugawaraMode lattice (actualInverse lattice) 1
local notation "T" => sugawaraMode lattice (actualInverse lattice) (-1)

private theorem sourceLMinusOne_eq_translation : T = translation lattice :=
  sugawaraMode_minus_one_eq_translation lattice (actualInverse lattice)
    (actualInverse_left lattice gram_det_unit) (actualInverse_right lattice gram_det_unit)

/-- Source translation differentiates every coefficient of the actual native
field, including for sources with mixed weights and lift eigenvalues. -/
theorem nativeField_translate_coeff (a : NativeStates) (m : ℤ) :
    C (nativeField (T a)) m = (((m + 3 : ℤ) : ℂ) / 3) • C (nativeField a) (m + 3) := by
  let b := liftProject (residueIndex m) a
  have hIndex : residueIndex (m + 3) = residueIndex m := by
    apply Fin.ext
    change ((-(m + 3)) % 3).toNat = ((-m) % 3).toNat
    exact congrArg Int.toNat (by omega : (-(m + 3)) % 3 = (-m) % 3)
  have hComm (u : NativeStates) : T (σ u) = σ (T u) := by
    rw [sourceLMinusOne_eq_translation]
    exact ((standardLift_compatible lattice g g_cube g_isometry).2.2 u).symm
  have hProjected : T b = liftProject (residueIndex m) (T a) := by
    dsimp only [b, liftProject]
    simp only [map_smul, map_add, hComm]
  have hSource : C (nativeField (T b)) m = C (nativeField (T a)) m := by
    rw [hProjected, liftProject_residue_coeff]
  have hMode : C (nativeField b) (m + 3) = C (nativeField a) (m + 3) := by
    simpa only [hIndex] using liftProject_residue_coeff a (m + 3)
  have hVacuumProduct : mu lattice b (-2) (vacuum lattice) = T b := by
    rw [sourceLMinusOne_eq_translation, translation_as_mode] <;> rfl
  have h := native_vacuum_minus_two_fractional_mode b m (liftProject_residue_eigen a m) (-1)
  have hScalar : -(((-1 : ℤ) : ℂ) - (m : ℂ) / 3) = ((m + 3 : ℤ) : ℂ) / 3 := by
    push_cast <;> ring
  simpa only [hVacuumProduct, show m - 3 * (-1 + 1) = m by omega,
    show m - 3 * (-1) = m + 3 by omega, hSource, hMode, hScalar] using h

private theorem source_translation_weight (a : NativeStates) (d : ℕ) (ha : L₀ a = (d : ℂ) • a) :
    L₀ (T a) = ((d + 1 : ℕ) : ℂ) • T a := by
  have h := LinearMap.congr_fun
    (sugawaraMode_virasoro lattice (actualInverse lattice)
      (actualInverse_left lattice gram_det_unit) (actualInverse_right lattice gram_det_unit)
      0 (-1)) a
  have hComm : L₀ (T a) - T (L₀ a) = T a := by
    norm_num [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
      LinearMap.smul_apply] at h
    exact h
  rw [ha, map_smul] at hComm
  calc
    L₀ (T a) = T a + (d : ℂ) • T a := eq_add_of_sub_eq hComm
    _ = ((d + 1 : ℕ) : ℂ) • T a := by
      rw [Nat.cast_add, Nat.cast_one, add_smul, one_smul, add_comm]

private theorem sourceLOne_translation (a : NativeStates) :
    L₁ (T a) = T (L₁ a) + (2 : ℂ) • L₀ a := by
  have h := LinearMap.congr_fun
    (sugawaraMode_virasoro lattice (actualInverse lattice)
      (actualInverse_left lattice gram_det_unit) (actualInverse_right lattice gram_det_unit)
      1 (-1)) a
  have hComm : L₁ (T a) - T (L₁ a) = (2 : ℂ) • L₀ a := by
    norm_num [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
      LinearMap.smul_apply] at h
    exact h
  rw [eq_add_of_sub_eq hComm, add_comm]

private theorem sourceLOne_pow_succ_translation (a : NativeStates) (d : ℕ)
    (ha : L₀ a = (d : ℂ) • a) (j : ℕ) :
    (L₁ ^ (j + 1)) (T a) = T ((L₁ ^ (j + 1)) a) +
      (((j : ℂ) + 1) * (2 * (d : ℂ) - (j : ℂ))) • (L₁ ^ j) a := by
  induction j with
  | zero =>
      simpa only [Nat.zero_add, Nat.cast_zero, zero_add, sub_zero, one_mul, pow_zero,
        pow_one, Module.End.one_apply, ha, smul_smul] using sourceLOne_translation a
  | succ j ih =>
      have hNext : L₁ ((L₁ ^ j) a) = (L₁ ^ (j + 1)) a := by
        rw [pow_succ', Module.End.mul_apply]
      have hScalar :
          2 * ((d : ℂ) - ((j + 1 : ℕ) : ℂ)) + ((j : ℂ) + 1) * (2 * (d : ℂ) - (j : ℂ)) =
            (((j + 1 : ℕ) : ℂ) + 1) * (2 * (d : ℂ) - ((j + 1 : ℕ) : ℂ)) := by
        push_cast <;> ring
      simp only [pow_succ' L₁ (j + 1), Module.End.mul_apply, ih, map_add, map_smul]
      rw [sourceLOne_translation, sourceLOne_pow_weight a (d : ℂ) ha (j + 1),
        smul_smul, hNext, add_assoc, ← add_smul, hScalar]

private theorem bpz_sum_translate (a : NativeStates) (d : ℕ) (ha : L₀ a = (d : ℂ) • a)
    (k : ℤ) (v : State) :
    (-1 : ℂ) ^ (d + 1) • ∑ j ∈ Finset.range (d + 1 + 1),
      (j.factorial : ℂ)⁻¹ • bpzTerm (T a) (d + 1) k j v =
    (((k + 3 : ℤ) : ℂ) / 3) • ((-1 : ℂ) ^ d • ∑ j ∈ Finset.range (d + 1),
      (j.factorial : ℂ)⁻¹ • bpzTerm a d (k + 3) j v) := by
  let m (j : ℕ) : ℤ := -k - 6 * ((d + 1 : ℕ) : ℤ) + 3 * (j : ℤ)
  let dividedTerm (j : ℕ) : State := (j.factorial : ℂ)⁻¹ • bpzTerm a d (k + 3) j v
  let translatedTerm (j : ℕ) : State :=
    (j.factorial : ℂ)⁻¹ • bpzTerm (T a) (d + 1) k j v
  let derivativeTerm (j : ℕ) : State :=
    -((k : ℂ) / 3 + 2 * (d : ℂ) + 1 - (j : ℂ)) • dividedTerm j
  let commutatorTerm (j : ℕ) : State := (2 * (d : ℂ) - (j : ℂ)) • dividedTerm j
  have hIndex (j : ℕ) : m j + 3 = -(k + 3) - 6 * (d : ℤ) + 3 * (j : ℤ) := by
    dsimp only [m]
    push_cast <;> omega
  have hShift (j : ℕ) : m (j + 1) = m j + 3 := by
    dsimp only [m]
    push_cast <;> omega
  have hNative (j : ℕ) :
      C (nativeField (T ((L₁ ^ j) a))) (m j) v =
        -((k : ℂ) / 3 + 2 * (d : ℂ) + 1 - (j : ℂ)) • bpzTerm a d (k + 3) j v := by
    have hScalar :
        ((m j + 3 : ℤ) : ℂ) / 3 = -((k : ℂ) / 3 + 2 * (d : ℂ) + 1 - (j : ℂ)) := by
      rw [hIndex]
      push_cast <;> ring
    rw [nativeField_translate_coeff, LinearMap.smul_apply, hScalar, hIndex, bpzTerm]
  have hZero : translatedTerm 0 = derivativeTerm 0 := by
    change (Nat.factorial 0 : ℂ)⁻¹ • C (nativeField ((L₁ ^ 0) (T a))) (m 0) v = _
    have h := hNative 0
    simp only [pow_zero, Module.End.one_apply] at h ⊢
    rw [h]
    exact smul_comm _ _ _
  have hFactorial (j : ℕ) :
      ((j + 1).factorial : ℂ)⁻¹ * ((j : ℂ) + 1) = (j.factorial : ℂ)⁻¹ := by
    have hj : (j : ℂ) + 1 ≠ 0 := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j) : ((j + 1 : ℕ) : ℂ) ≠ 0)
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_inv_rev,
      mul_assoc, inv_mul_cancel₀ hj, mul_one]
  have hSucc (j : ℕ) :
      translatedTerm (j + 1) = derivativeTerm (j + 1) + commutatorTerm j := by
    change ((j + 1).factorial : ℂ)⁻¹ •
      C (nativeField ((L₁ ^ (j + 1)) (T a))) (m (j + 1)) v = _
    rw [sourceLOne_pow_succ_translation a d ha j]
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, LinearMap.add_apply,
      LinearMap.smul_apply]
    rw [hNative, hShift, hIndex, smul_add]
    change ((j + 1).factorial : ℂ)⁻¹ •
          (-((k : ℂ) / 3 + 2 * (d : ℂ) + 1 - ((j + 1 : ℕ) : ℂ)) •
            bpzTerm a d (k + 3) (j + 1) v) +
        ((j + 1).factorial : ℂ)⁻¹ •
          ((((j : ℂ) + 1) * (2 * (d : ℂ) - (j : ℂ))) • bpzTerm a d (k + 3) j v) = _
    apply congrArg₂ (· + ·)
    · exact smul_comm _ _ _
    · dsimp only [commutatorTerm, dividedTerm]
      rw [smul_smul, smul_smul, ← mul_assoc, hFactorial,
        mul_comm ((j.factorial : ℂ)⁻¹)]
  have hTop : derivativeTerm (d + 1) = 0 := by
    have hz := sourceLOne_pow_eq_zero_of_lt a d ha (d + 1) (by omega)
    simp only [derivativeTerm, dividedTerm, bpzTerm, hz, map_zero, Pi.zero_apply,
      LinearMap.zero_apply, smul_zero]
  have hSum : (∑ j ∈ Finset.range (d + 1 + 1), translatedTerm j) =
      ∑ j ∈ Finset.range (d + 1), (derivativeTerm j + commutatorTerm j) := by
    rw [Finset.sum_range_succ' translatedTerm (d + 1), hZero]
    simp only [hSucc, Finset.sum_add_distrib]
    have hDerivative := Finset.sum_range_succ' derivativeTerm (d + 1)
    rw [Finset.sum_range_succ derivativeTerm (d + 1), hTop, add_zero] at hDerivative
    rw [hDerivative]
    abel
  have hCombine (j : ℕ) : derivativeTerm j + commutatorTerm j =
      -(((k + 3 : ℤ) : ℂ) / 3) • dividedTerm j := by
    dsimp only [derivativeTerm, commutatorTerm]
    rw [← add_smul]
    congr 1
    push_cast <;> ring
  change (-1 : ℂ) ^ (d + 1) • (∑ j ∈ Finset.range (d + 1 + 1), translatedTerm j) =
    (((k + 3 : ℤ) : ℂ) / 3) • ((-1 : ℂ) ^ d • ∑ j ∈ Finset.range (d + 1), dividedTerm j)
  rw [hSum]
  simp_rw [hCombine]
  rw [← Finset.smul_sum, pow_succ, smul_smul, smul_smul]
  congr 1
  ring

/-- Precompose the BPZ coefficient with the real-to-complex grade cast. -/
private def gradeBPZ (a : NativeStates) (d : ℕ) (ha : L₀ a = (d : ℂ) • a)
    (w : ℝ) (k : ℤ) : ActualGrade (shiftedWeight w d k) →ₗ[ℂ] ActualGrade w :=
  (bpzCoeff a d ha (w : ℂ) k).comp (shiftedGradeEquiv w d k).toLinearMap

private theorem gradeBPZ_apply_val (a : NativeStates) (d : ℕ) (ha : L₀ a = (d : ℂ) • a)
    (w : ℝ) (k : ℤ) (u : ActualGrade (shiftedWeight w d k)) :
    (gradeBPZ a d ha w k u).val = (-1 : ℂ) ^ d • ∑ j ∈ Finset.range (d + 1),
      (j.factorial : ℂ)⁻¹ • bpzTerm a d k j u.val := by
  let bpzAt (s : State) : State := (-1 : ℂ) ^ d • ∑ j ∈ Finset.range (d + 1),
    (j.factorial : ℂ)⁻¹ • bpzTerm a d k j s
  have hCast : (shiftedGradeEquiv w d k u).val = u.val := by
    unfold shiftedGradeEquiv
    exact LinearEquiv.coe_ofEq_apply _ u
  have hCoeff : (gradeBPZ a d ha w k u).val = bpzAt (shiftedGradeEquiv w d k u).val :=
    bpzCoeff_apply_val a d ha (w : ℂ) k (shiftedGradeEquiv w d k u)
  exact hCoeff.trans (congrArg bpzAt hCast)

private theorem gradeBPZ_translate_apply_val (a : NativeStates) (d : ℕ)
    (ha : L₀ a = (d : ℂ) • a) (w : ℝ) (k : ℤ)
    (u : ActualGrade (shiftedWeight w (d + 1) k))
    (v : ActualGrade (shiftedWeight w d (k + 3))) (huv : u.val = v.val) :
    (gradeBPZ (T a) (d + 1) (source_translation_weight a d ha) w k u).val =
      (((k + 3 : ℤ) : ℂ) / 3) • (gradeBPZ a d ha w (k + 3) v).val := by
  let translatedSum (s : State) : State := (-1 : ℂ) ^ (d + 1) •
    ∑ j ∈ Finset.range (d + 1 + 1), (j.factorial : ℂ)⁻¹ • bpzTerm (T a) (d + 1) k j s
  calc
    _ = translatedSum u.val :=
      gradeBPZ_apply_val (T a) (d + 1) (source_translation_weight a d ha) w k u
    _ = translatedSum v.val := congrArg translatedSum huv
    _ = (((k + 3 : ℤ) : ℂ) / 3) • ((-1 : ℂ) ^ d • ∑ j ∈ Finset.range (d + 1),
          (j.factorial : ℂ)⁻¹ • bpzTerm a d (k + 3) j v.val) :=
      bpz_sum_translate a d ha k v.val
    _ = _ := congrArg (fun s : State => (((k + 3 : ℤ) : ℂ) / 3) • s)
      (gradeBPZ_apply_val a d ha w (k + 3) v).symm

private theorem gradeCoeff_eval (a : NativeStates) (d : ℕ) (ha : L₀ a = (d : ℂ) • a)
    (w : ℝ) (k : ℤ) (f : GradeDual w) (u : ActualGrade (shiftedWeight w d k)) :
    gradeCoeff a d ha w k f u = f (gradeBPZ a d ha w k u) := by
  have hDual := LinearMap.dualMap_comp_dualMap (shiftedGradeEquiv w d k).toLinearMap
    (bpzCoeff a d ha (w : ℂ) k)
  calc
    _ = (gradeBPZ a d ha w k).dualMap f u :=
      LinearMap.congr_fun (LinearMap.congr_fun hDual f) u
    _ = _ := LinearMap.dualMap_apply (gradeBPZ a d ha w k) f u

private theorem dual_apply_eq_smul_of_val_eq {V : Type*} [AddCommMonoid V] [Module ℂ V]
    {p : Submodule ℂ V} (f : Module.Dual ℂ p) (c : ℂ) (x y : p)
    (h : x.val = c • y.val) : f x = c • f y := by
  have hxy : x = c • y := Subtype.ext (h.trans (Submodule.coe_smul c y).symm)
  exact (congrArg (fun z : p => f z) hxy).trans (f.map_smul c y)

private theorem gradeCoeff_translate_apply (a : NativeStates) (d : ℕ)
    (ha : L₀ a = (d : ℂ) • a) (w : ℝ) (k : ℤ) (f : GradeDual w)
    (u : ActualGrade (shiftedWeight w (d + 1) k))
    (v : ActualGrade (shiftedWeight w d (k + 3))) (huv : u.val = v.val) :
    gradeCoeff (T a) (d + 1) (source_translation_weight a d ha) w k f u =
      (((k + 3 : ℤ) : ℂ) / 3) • gradeCoeff a d ha w (k + 3) f v := by
  let c : ℂ := ((k + 3 : ℤ) : ℂ) / 3
  let x := gradeBPZ (T a) (d + 1) (source_translation_weight a d ha) w k u
  let y := gradeBPZ a d ha w (k + 3) v
  calc
    _ = f x := gradeCoeff_eval (T a) (d + 1) (source_translation_weight a d ha) w k f u
    _ = c • f y := dual_apply_eq_smul_of_val_eq (V := State) f c x y
      (gradeBPZ_translate_apply_val a d ha w k u v huv)
    _ = _ := congrArg (fun z : ℂ => c • z) (gradeCoeff_eval a d ha w (k + 3) f v).symm

private theorem lof_eq_of_gradeDual_apply {p q : ℝ} (hpq : p = q)
    (f : GradeDual p) (g' : GradeDual q)
    (h : ∀ (u : ActualGrade p) (v : ActualGrade q), u.val = v.val → f u = g' v) :
    DirectSum.lof ℂ ℝ GradeDual p f = DirectSum.lof ℂ ℝ GradeDual q g' := by
  subst q
  exact congrArg (DirectSum.lof ℂ ℝ GradeDual p) (LinearMap.ext fun v => h v v rfl)

/-- On the actual restricted dual, translating a homogeneous source by
`L(-1)` gives the coefficient of the physical `z`-derivative. -/
theorem oppositeField_translate_coeff (a : NativeStates) (d : ℕ)
    (ha : L₀ a = (d : ℂ) • a) (k : ℤ) :
    C (oppositeField (T a) (d + 1) (source_translation_weight a d ha)) k =
      (((k + 3 : ℤ) : ℂ) / 3) • C (oppositeField a d ha) (k + 3) := by
  simp only [oppositeField_coeff]
  apply DirectSum.linearMap_ext
  intro w
  apply LinearMap.ext
  intro f
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, coeff_lof]
  rw [← map_smul]
  apply lof_eq_of_gradeDual_apply
  · unfold shiftedWeight
    push_cast <;> ring
  · intro u v huv
    rw [LinearMap.smul_apply]
    exact gradeCoeff_translate_apply a d ha w k f u v huv

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualTranslation
