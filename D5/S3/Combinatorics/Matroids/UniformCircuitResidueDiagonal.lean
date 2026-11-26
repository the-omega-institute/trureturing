/- GID: D5/S3/Combinatorics/Matroids/UniformCircuitResidueDiagonal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/UniformCircuitResidueDiagonal
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Diagonal coordinate constraints after splitting the two exterior operations. -/

module

public import D5.S3.Combinatorics.Matroids.UniformCircuitResidueForms
public import Mathlib.Algebra.Module.Submodule.Equiv

/-! Diagonal equations in a basis adapted to the pivot and insertion vector. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.UniformCircuitResidueDiagonal

open AlternatingMap UniformCircuitResidueForms
set_option autoImplicit false

variable {I M N : Type*} [LinearOrder I] [AddCommGroup M] [AddCommGroup N]
variable {r : ℕ}

/-- Coefficients with a forbidden pivot and two scalar torsion conditions. -/
def diagonalCoordinates (N : Type*) [AddCommGroup N] (r : ℕ) (i j : I) (s d : ℤ) :
    Submodule ℤ (Set.powersetCard I r → N) where
  carrier := {f | (∀ F, i ∈ F → f F = 0) ∧
    (∀ F, j ∈ F → d • f F = 0) ∧ ∀ F, s • f F = 0}
  zero_mem' := by simp
  add_mem' hf hg := by
    refine ⟨fun F hF => ?_, fun F hF => ?_, fun F => ?_⟩
    · simp [hf.1 F hF, hg.1 F hF]
    · simp [smul_add, hf.2.1 F hF, hg.2.1 F hF]
    · simp [smul_add, hf.2.2 F, hg.2.2 F]
  smul_mem' t f hf := by
    refine ⟨fun F hF => ?_, fun F hF => ?_, fun F => ?_⟩
    · simp [Pi.smul_apply, hf.1 F hF]
    · rw [Pi.smul_apply, smul_comm d t, hf.2.1 F hF, smul_zero]
    · rw [Pi.smul_apply, smul_comm s t, hf.2.2 F, smul_zero]

theorem reduced_equations (b : Module.Basis I ℤ M) (i j : I) (s d : ℤ)
    (f : M [⋀^Fin (r + 1)]→ₗ[ℤ] N) :
    f.curryLeft (b i) = 0 ∧ f.curryLeft (s • b i + d • b j) = 0 ∧ s • f = 0 ↔
      (basisFormEquiv b).symm f ∈ diagonalCoordinates N (r + 1) i j s d := by
  let fcoord := (basisFormEquiv b).symm f
  have hi : f.curryLeft (b i) = 0 ↔ ∀ F, i ∈ F → fcoord F = 0 := by
    simpa only [one_smul] using curryLeft_smul_basis_eq_zero_iff b f 1 i
  have hj : f.curryLeft (d • b j) = 0 ↔ ∀ F, j ∈ F → d • fcoord F = 0 :=
    curryLeft_smul_basis_eq_zero_iff b f d j
  have hs : s • f = 0 ↔ ∀ F, s • fcoord F = 0 := by
    constructor
    · intro h F
      have hmap := congrArg (basisFormEquiv b).symm h
      rw [map_smul, _root_.map_zero] at hmap
      exact congrFun hmap F
    · intro h
      apply (basisFormEquiv b).symm.injective
      rw [map_smul, _root_.map_zero]
      exact funext h
  constructor
  · rintro ⟨hI, hY, hS⟩
    rw [map_add, map_zsmul, hI, smul_zero, zero_add] at hY
    exact ⟨hi.mp hI, hj.mp hY, hs.mp hS⟩
  · rintro ⟨hI, hJ, hS⟩
    refine ⟨hi.mpr hI, ?_, hs.mpr hS⟩
    rw [map_add, map_zsmul, hi.mpr hI, hj.mpr hJ, smul_zero, zero_add]

/-- An adapted integral basis diagonalizes the common kernel on alternating
forms with arbitrary additive coefficient group. -/
noncomputable def diagonalFormEquiv (b : Module.Basis I ℤ M) (a : M →ₗ[ℤ] ℤ)
    (i j : I) (d : ℤ) (y : M) (hi : a (b i) = 1) (hy : y = a y • b i + d • b j) :
    ↥((covectorWedgeLinear (N := N) (n := r + 2) a).ker ⊓ (insertVector y).ker) ≃ₗ[ℤ]
      diagonalCoordinates N (r + 1) i j (a y) d := by
  refine (pivotFormEquiv (N := N) a (b i) y hi).trans
    ((basisFormEquiv b).symm.ofSubmodules _ _ ?_)
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hI : g.curryLeft (b i) = 0 := hg.1.1
    have hY : g.curryLeft y = 0 := hg.1.2
    have hS : a y • g = 0 := hg.2
    conv at hY => lhs; arg 2; rw [hy]
    exact (reduced_equations b i j (a y) d g).mp ⟨hI, hY, hS⟩
  · intro hf
    let g := basisFormEquiv b f
    have hgf : (basisFormEquiv b).symm g = f := LinearEquiv.symm_apply_apply _ _
    have hmem : (basisFormEquiv b).symm g ∈ diagonalCoordinates N (r + 1) i j (a y) d :=
      hgf.symm ▸ hf
    obtain ⟨hI, hY, hS⟩ := (reduced_equations b i j (a y) d g).mpr hmem
    refine ⟨g, ⟨⟨hI, ?_⟩, hS⟩, hgf⟩
    change g.curryLeft y = 0
    conv => lhs; arg 2; rw [hy]
    exact hY

/-- Separate the coefficients by whether the distinguished nonpivot element
belongs to the indexing subset. -/
noncomputable def diagonalCoordinatesEquiv (i j : I) (s d : ℤ) :
    diagonalCoordinates N r i j s d ≃ₗ[ℤ]
      (({F : Set.powersetCard I r // i ∉ F ∧ j ∈ F} →
        ↥(Submodule.torsionBy ℤ N s ⊓ Submodule.torsionBy ℤ N d)) ×
       ({F : Set.powersetCard I r // i ∉ F ∧ j ∉ F} → Submodule.torsionBy ℤ N s)) := by
  classical
  let A := {F : Set.powersetCard I r // i ∉ F ∧ j ∈ F}
  let B := {F : Set.powersetCard I r // i ∉ F ∧ j ∉ F}
  let read : diagonalCoordinates N r i j s d →
      ((A → ↥(Submodule.torsionBy ℤ N s ⊓ Submodule.torsionBy ℤ N d)) ×
        (B → Submodule.torsionBy ℤ N s)) := fun f =>
      ⟨fun F => ⟨f.val F.val, f.prop.2.2 F.val, f.prop.2.1 F.val F.prop.2⟩,
       fun F => ⟨f.val F.val, f.prop.2.2 F.val⟩⟩
  let write (v : (A → ↥(Submodule.torsionBy ℤ N s ⊓ Submodule.torsionBy ℤ N d)) ×
      (B → Submodule.torsionBy ℤ N s)) : Set.powersetCard I r → N :=
    fun F => if hp : i ∈ F then 0 else
      if hx : j ∈ F then (v.1 ⟨F, hp, hx⟩).val else (v.2 ⟨F, hp, hx⟩).val
  refine {
    toFun := read
    invFun := fun v => ⟨write v, ?_⟩
    left_inv := ?_
    right_inv := ?_
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  · refine ⟨fun F hF => ?_, fun F hF => ?_, fun F => ?_⟩
    · simp [write, hF]
    · by_cases hi : i ∈ F
      · simp [write, hi]
      · simp only [write, dite_eq_right hi, dite_eq_left hF]
        exact (v.1 ⟨F, hi, hF⟩).prop.2
    · by_cases hi : i ∈ F
      · simp [write, hi]
      · by_cases hj : j ∈ F
        · simp only [write, dite_eq_right hi, dite_eq_left hj]
          exact (v.1 ⟨F, hi, hj⟩).prop.1
        · simp only [write, dite_eq_right hi, dite_eq_right hj]
          exact (v.2 ⟨F, hi, hj⟩).prop
  · intro f
    apply Subtype.ext
    funext F
    by_cases hi : i ∈ F
    · simp [write, hi, f.prop.1 F hi]
    · by_cases hj : j ∈ F
      · simp [write, read, hi, hj]
      · simp [write, read, hi, hj]
  · intro v
    apply Prod.ext
    · funext F
      apply Subtype.ext
      exact by
        change write v F.val = (v.1 F).val
        simp [write, F.prop.1, F.prop.2]
    · funext F
      apply Subtype.ext
      exact by
        change write v F.val = (v.2 F).val
        simp [write, F.prop.1, F.prop.2]

end D5.S3.Combinatorics.Matroids.UniformCircuitResidueDiagonal
