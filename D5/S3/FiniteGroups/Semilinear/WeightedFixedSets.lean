/- GID: D5/S3/FiniteGroups/Semilinear/WeightedFixedSets
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Semilinear/WeightedFixedSets
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Weighted semilinear fixed sets retain every zero coordinate and are counted by relative norm orders. -/

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.Tactic

/-! Relative-norm fixed-set counts for arbitrary finite lists of natural weights. -/

set_option autoImplicit false

open scoped Classical

namespace WeightedSemilinear

universe u
variable {F K : Type} [Field F] [Field K] [Fintype F] [Fintype K] [Algebra F K]

local notation "E[" σ "]" => (IntermediateField.fixedField (Subgroup.zpowers σ))
local notation "N[" σ "]" => Units.map (Algebra.norm E[σ] (S := K))

private theorem mem_fixed_iff (σ : Gal(K/F)) (x : K) :
    x ∈ IntermediateField.fixedField (Subgroup.zpowers σ) ↔ σ x = x := by
  rw [IntermediateField.mem_fixedField_iff]
  constructor
  · intro h
    exact h σ (Subgroup.mem_zpowers σ)
  · intro h τ hτ
    exact smul_eq_self_of_mem_zpowers hτ h

private def relativeGenerator (σ : Gal(K/F)) : Gal(K/E[σ]) :=
  IntermediateField.subgroupEquivAlgEquiv (Subgroup.zpowers σ)
    ⟨σ, Subgroup.mem_zpowers σ⟩

private theorem relativeGenerator_generates (σ : Gal(K/F)) :
    ∀ τ, τ ∈ Subgroup.zpowers (relativeGenerator σ) := by
  let e := IntermediateField.subgroupEquivAlgEquiv (Subgroup.zpowers σ)
  intro τ
  obtain ⟨k, hk⟩ := (e.symm τ).property
  refine ⟨k, ?_⟩
  change (e ⟨σ, Subgroup.mem_zpowers σ⟩) ^ k = τ
  rw [← map_zpow]
  calc
    e (⟨σ, Subgroup.mem_zpowers σ⟩ ^ k) = e (e.symm τ) := by
      congr 1
      exact Subtype.ext hk
    _ = τ := e.apply_symm_apply τ

private theorem norm_eq_one_of_solution (σ : Gal(K/F)) (a x : K)
    (hx : x ≠ 0) (heq : σ x = a * x) : Algebra.norm E[σ] a = 1 := by
  have hnorm : Algebra.norm E[σ] (σ x) = Algebra.norm E[σ] x :=
    Algebra.norm_eq_of_algEquiv (relativeGenerator σ) x
  rw [heq, map_mul] at hnorm
  exact (mul_eq_right₀ (Algebra.norm_ne_zero_iff.mpr hx)).mp hnorm

/-- A norm-one equation has a nonzero solution, with Hilbert 90's orientation reversed. -/
private theorem exists_solution (σ : Gal(K/F)) (a : K)
    (ha : Algebra.norm E[σ] a = 1) : ∃ x : K, x ≠ 0 ∧ σ x = a * x := by
  have hai : Algebra.norm E[σ] a⁻¹ = 1 := by simp [Algebra.norm_inv, ha]
  obtain ⟨y, hy⟩ := groupCohomology.exists_div_of_norm_eq_one
    (K := E[σ]) (L := K) (g := relativeGenerator σ) (relativeGenerator_generates σ) hai
  refine ⟨y, Units.ne_zero y, ?_⟩
  change (y : K) / σ (y : K) = a⁻¹ at hy
  have ha0 : a ≠ 0 := Algebra.norm_ne_zero_iff.mp (ha ▸ one_ne_zero)
  have hσy : σ (y : K) ≠ 0 := (map_ne_zero σ).mpr (Units.ne_zero y)
  have hy' : (y : K) = a⁻¹ * σ (y : K) := (div_eq_iff hσy).mp hy
  calc
    σ (y : K) = a * (a⁻¹ * σ (y : K)) := by field_simp
    _ = a * (y : K) := by rw [← hy']

/-- All solutions, including zero, are one nonzero solution times the fixed field. -/
private noncomputable def solutionEquiv (σ : Gal(K/F)) (a y : K)
    (hy : y ≠ 0) (hσy : σ y = a * y) :
    E[σ] ≃ {x : K // σ x = a * x} where
  toFun t := ⟨y * t, by
    rw [map_mul, hσy, (mem_fixed_iff σ t).mp t.property]
    ring⟩
  invFun x := ⟨x / y, (mem_fixed_iff σ _).mpr (by
    have ha : a ≠ 0 := by
      intro h
      have hz : σ y = 0 := by simpa [h] using hσy
      exact hy (σ.injective (hz.trans (map_zero σ).symm))
    rw [map_div₀, x.property, hσy]
    field_simp)⟩
  left_inv t := by apply Subtype.ext; simp [hy]
  right_inv x := by apply Subtype.ext; dsimp; field_simp

/-- Failure of the norm condition leaves exactly the zero solution. -/
theorem coordinate_card (σ : Gal(K/F)) (a : K) :
    Nat.card {x : K // σ x = a * x} =
      if Algebra.norm E[σ] a = 1 then Nat.card E[σ] else 1 := by
  classical
  split_ifs with ha
  · obtain ⟨y, hy, hσy⟩ := exists_solution σ a ha
    exact Nat.card_congr (solutionEquiv σ a y hy hσy).symm
  · have hz (x : {x : K // σ x = a * x}) : x.val = 0 := by
      by_contra hx
      exact ha (norm_eq_one_of_solution σ a x hx x.property)
    let e : {x : K // σ x = a * x} ≃ Unit :=
      { toFun := fun _ => ()
        invFun := fun _ => ⟨0, by simp⟩
        left_inv := fun x => Subtype.ext (hz x).symm
        right_inv := fun _ => rfl }
    exact (Nat.card_congr e).trans (by simp)

/-- Coordinate independence retains the full index type, including its empty case. -/
theorem vector_card {I : Type u} [Fintype I] (w : I → ℕ)
    (σ : Gal(K/F)) (c : Kˣ) :
    Nat.card {A : I → K // ∀ i, σ (A i) = (c : K) ^ w i * A i} =
      Nat.card E[σ] ^ (Finset.univ.filter (fun i => orderOf (N[σ] c) ∣ w i)).card := by
  classical
  let e : {A : I → K // ∀ i, σ (A i) = (c : K) ^ w i * A i} ≃
      (∀ i, {x : K // σ x = (c : K) ^ w i * x}) :=
    { toFun := fun A i => ⟨A.val i, A.property i⟩
      invFun := fun A => ⟨fun i => (A i).val, fun i => (A i).property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_pi]
  simp_rw [coordinate_card]
  have hn (i : I) : Algebra.norm E[σ] ((c : K) ^ w i) = 1 ↔
      orderOf (N[σ] c) ∣ w i := by
    rw [map_pow]
    change (↑((N[σ] c) ^ w i) : E[σ]) = 1 ↔ _
    rw [Units.val_eq_one, ← orderOf_dvd_iff_pow_eq_one]
  simp_rw [hn]
  rw [← Finset.prod_filter]
  simp

end WeightedSemilinear
