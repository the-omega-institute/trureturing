/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenDimension
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenDimension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Any 258-point Q9 set supports two independent positive Huang eigenvectors. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Fintype.Card
import Batteries.Tactic.OpenPrivate

/-! A 258-point Q9 set supports at least two independent positive Huang eigenvectors. -/

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenDimension

open scoped BigOperators Classical
open D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open private huangMatrix from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private coeff matrix_coeff from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum

set_option autoImplicit false
noncomputable section

abbrev Q9 := BalancedCriticalSpectrum.Q 9

/- The carrier records both the original Huang eigen-equation and literal
   vanishing outside the selected finite set. -/
def supportedEigenSpace (U : Finset Q9) : Submodule Real (Q9 → Real) where
  carrier := {z | (huangMatrix 9).mulVec z = (3 : Real) • z ∧
    ∀ x ∉ U, z x = 0}
  zero_mem' := by
    constructor
    · simp
    · intro x hx
      simp
  add_mem' := by
    intro z w hz hw
    constructor
    · rw [show (huangMatrix 9).mulVec (z + w) =
          (huangMatrix 9).mulVec z + (huangMatrix 9).mulVec w by
            exact (huangMatrix 9).mulVecLin.map_add z w]
      rw [hz.1, hw.1, smul_add]
    · intro x hx
      rw [Pi.add_apply, hz.2 x hx, hw.2 x hx, add_zero]
  smul_mem' := by
    intro c z hz
    constructor
    · rw [show (huangMatrix 9).mulVec (c • z) =
          c • (huangMatrix 9).mulVec z by
            exact (huangMatrix 9).mulVecLin.map_smul c z]
      simp [hz.1, smul_smul, mul_comm]
    · intro x hx
      rw [Pi.smul_apply, hz.2 x hx, smul_zero]

@[simp] theorem mem_supportedEigenSpace_iff (U : Finset Q9) (z : Q9 → Real) :
    z ∈ supportedEigenSpace U ↔
      (huangMatrix 9).mulVec z = (3 : Real) • z ∧ ∀ x ∉ U, z x = 0 :=
  Iff.rfl

private def positiveCoordinates : Sensitivity.V 8 →ₗ[Real] (Q9 → Real) :=
  (coeff 9).toLinearMap.comp (Sensitivity.g 8)

private theorem positiveCoordinates_injective :
    Function.Injective positiveCoordinates := by
  intro v w h
  apply Sensitivity.g_injective
  apply (coeff 9).injective
  exact h

private theorem positiveCoordinates_eigen (v : Sensitivity.V 8) :
    (huangMatrix 9).mulVec (positiveCoordinates v) =
      (3 : Real) • positiveCoordinates v := by
  change (huangMatrix 9).mulVec (coeff 9 (Sensitivity.g 8 v)) = _
  rw [matrix_coeff, (coeff 9).symm_apply_apply]
  change coeff 9 (Sensitivity.f 9 (Sensitivity.g 8 v)) = _
  rw [Sensitivity.f_image_g (Sensitivity.g 8 v) ⟨v, rfl⟩]
  have hsqrt : Real.sqrt (((8 : Nat) : Real) + 1) = (3 : Real) := by
    apply (Real.sqrt_eq_iff_eq_sq
      (x := (((8 : Nat) : Real) + 1)) (y := (3 : Real))
      (by norm_num) (by norm_num)).2
    norm_num
  rw [hsqrt, map_smul]
  rfl

private def outsideRestriction (U : Finset Q9) :
    (Q9 → Real) →ₗ[Real] ({x : Q9 // x ∉ U} → Real) where
  toFun z := fun x => z x.1
  map_add' z w := by
    funext x
    rfl
  map_smul' c z := by
    funext x
    rfl

private def supportRestriction (U : Finset Q9) :
    Sensitivity.V 8 →ₗ[Real] ({x : Q9 // x ∉ U} → Real) :=
  (outsideRestriction U).comp positiveCoordinates

private def kerToSupported (U : Finset Q9) :
    LinearMap.ker (supportRestriction U) →ₗ[Real] supportedEigenSpace U where
  toFun v :=
    ⟨positiveCoordinates v.1,
      positiveCoordinates_eigen v.1,
      by
        intro x hx
        have hv := LinearMap.mem_ker.mp v.2
        have hvx := congrFun hv ⟨x, hx⟩
        change positiveCoordinates v.1 x = 0 at hvx
        exact hvx⟩
  map_add' v w := by
    apply Subtype.ext
    change positiveCoordinates (v.1 + w.1) =
      positiveCoordinates v.1 + positiveCoordinates w.1
    exact positiveCoordinates.map_add v.1 w.1
  map_smul' c v := by
    apply Subtype.ext
    change positiveCoordinates (c • v.1) = c • positiveCoordinates v.1
    exact positiveCoordinates.map_smul c v.1

private theorem kerToSupported_injective (U : Finset Q9) :
    Function.Injective (kerToSupported U) := by
  intro v w h
  apply Subtype.ext
  apply positiveCoordinates_injective
  exact congrArg Subtype.val h

private theorem complement_card (U : Finset Q9) (hU : U.card = 258) :
    Fintype.card {x : Q9 // x ∉ U} = 254 := by
  rw [Fintype.card_subtype_compl]
  rw [Sensitivity.Q.card, Fintype.card_coe U, hU]
  norm_num

theorem two_le_finrank_supportedEigenSpace (U : Finset Q9) (hU : U.card = 258) :
    2 ≤ Module.finrank Real (supportedEigenSpace U) := by
  have hsource : Module.finrank Real (Sensitivity.V 8) = 256 := by
    rw [Sensitivity.finrank_V]
    norm_num
  have htarget :
      Module.finrank Real ({x : Q9 // x ∉ U} → Real) = 254 := by
    rw [Module.finrank_fintype_fun_eq_card, complement_card U hU]
  let L := supportRestriction U
  have hrank := LinearMap.finrank_range_add_finrank_ker L
  have hrange : Module.finrank Real (LinearMap.range L) ≤ 254 := by
    have h := (LinearMap.range L).finrank_le
    rw [htarget] at h
    exact h
  rw [hsource] at hrank
  have hker : 2 ≤ Module.finrank Real (LinearMap.ker L) := by
    omega
  have hinj : Function.Injective (kerToSupported U) := kerToSupported_injective U
  have hle :
      Module.finrank Real (LinearMap.ker L) ≤
        Module.finrank Real (supportedEigenSpace U) := by
    exact LinearMap.finrank_le_finrank_of_injective hinj
  exact hker.trans hle

theorem exists_nonzero_supported_eigenvector (U : Finset Q9) (hU : U.card = 258) :
    ∃ z : Q9 → Real, z ≠ 0 ∧
      (huangMatrix 9).mulVec z = (3 : Real) • z ∧ ∀ x ∉ U, z x = 0 := by
  have hdim := two_le_finrank_supportedEigenSpace U hU
  have hpos : 0 < Module.finrank Real (supportedEigenSpace U) := by omega
  rcases (Module.finrank_pos_iff_exists_ne_zero.mp hpos) with ⟨z, hz⟩
  have hzfun : z.1 ≠ 0 := by
    intro hzero
    apply hz
    exact Subtype.ext hzero
  exact ⟨z.1, hzfun, (mem_supportedEigenSpace_iff U z.1).mp z.2⟩

theorem exists_nonzero_supported_eigenvector_vanishing_at
    (U : Finset Q9) (hU : U.card = 258) (x : Q9) :
    ∃ w : Q9 → Real, w ≠ 0 ∧ w x = 0 ∧
      (huangMatrix 9).mulVec w = (3 : Real) • w ∧ ∀ y ∉ U, w y = 0 := by
  let S := supportedEigenSpace U
  let ev : S →ₗ[Real] Real :=
    { toFun := fun z => z.1 x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hdim : 2 ≤ Module.finrank Real S := two_le_finrank_supportedEigenSpace U hU
  have hlt : Module.finrank Real Real < Module.finrank Real S := by
    rw [Module.finrank_self]
    omega
  have hker : LinearMap.ker ev ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hlt
  rcases Submodule.exists_mem_ne_zero_of_ne_bot hker with ⟨z, hzker, hz⟩
  have hzfun : z.1 ≠ 0 := by
    intro hzero
    apply hz
    exact Subtype.ext hzero
  have hxzero : z.1 x = 0 := by
    exact LinearMap.mem_ker.mp hzker
  exact ⟨z.1, hzfun, hxzero,
    (mem_supportedEigenSpace_iff U z.1).mp z.2⟩

end
end D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenDimension
