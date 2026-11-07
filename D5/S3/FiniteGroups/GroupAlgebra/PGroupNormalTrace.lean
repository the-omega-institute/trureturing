/- GID: D5/S3/FiniteGroups/GroupAlgebra/PGroupNormalTrace
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/PGroupNormalTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonzero trace detects normal elements for arbitrary Galois p-groups. -/

import D5.S3.FiniteGroups.GroupAlgebra.PGroupAugmentation
import D5.S3.ArithUnits.MinacNguyenTanQuestion35
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.RingTheory.Trace.Basic

/-!
The normal basis identifies the Galois module with its group algebra.
The cardinal nilpotence bound supplies the nil kernel required by the
augmentation-unit criterion. Trace is augmentation times the trace of the
chosen normal element; right multiplication by a unit preserves independence.
-/

namespace D5.S3.FiniteGroups.GroupAlgebra.PGroupNormalTrace

open MonoidAlgebra
open D5.S3.ArithUnits.MinacNguyenTanQuestion35 (augmentation)

/-
The following helper is transplanted from Kenta Kitamura,
AllPrimeGroups/NilAugmentation.lean, immutable revision
9253775c275153b1efb04f911b5c8740fed5a568, Apache-2.0.
Copyright 2026 Kenta Kitamura. License and NOTICE: docs/reports/licenses/all-prime-groups/.
Namespace, visibility and bound type names are adapted. Retire this transplant when this
repository's pinned Mathlib contains an equivalent unit criterion.
-/
private theorem isUnit_iff_augmentation_ne_zero {K A : Type*} [Field K] [Ring A]
    [Algebra K A] (ε : A →ₐ[K] K)
    (hnil : ∀ a : A, ε a = 0 → IsNilpotent a) (a : A) :
    IsUnit a ↔ ε a ≠ 0 := by
  constructor
  · intro h
    exact (h.map ε.toRingHom).ne_zero
  · intro ha
    let u := algebraMap K A (ε a)⁻¹
    have hu : IsUnit u := (isUnit_iff_ne_zero.mpr (inv_ne_zero ha)).map (algebraMap K A)
    have hn : IsNilpotent (u * a - 1) := hnil _ (by
      simp [u, map_sub, map_mul, AlgHom.commutes, ha])
    have hua : IsUnit (u * a) := by simpa only [sub_add_cancel] using hn.isUnit_add_one
    obtain ⟨U, hU⟩ := hu
    exact (Units.isUnit_units_mul U a).mp (by simpa only [hU] using hua)

/-- For a finite Galois extension in characteristic `p` with arbitrary p-group
Galois group, an element has independent conjugates exactly when its trace is nonzero. -/
theorem linearIndependent_conjugates_iff_trace_ne_zero
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hG : IsPGroup p (L ≃ₐ[K] L)) (x : L) :
    LinearIndependent K (fun σ : L ≃ₐ[K] L => σ x) ↔ Algebra.trace K L x ≠ 0 := by
  classical
  let Γ := L ≃ₐ[K] L
  let b := IsGalois.normalBasis K L
  let c := MonoidAlgebra.basis Γ K
  let e : MonoidAlgebra K Γ ≃ₗ[K] L := c.equiv b (Equiv.refl Γ)
  let θ := b 1
  let ε := augmentation K Γ
  have heof : ∀ g : Γ, e (of K Γ g) = g θ := by
    intro g
    change e (c g) = g θ
    rw [Module.Basis.equiv_apply]
    exact IsGalois.normalBasis_apply g
  have hequiv : ∀ (g : Γ) a, e (of K Γ g * a) = g (e a) := by
    intro g a
    induction a using MonoidAlgebra.induction_on with
    | of h => rw [← map_mul, heof, heof]; rfl
    | add a b ha hb => simp only [mul_add, map_add, ha, hb]
    | smul r a ha => simp only [mul_smul_comm, map_smul, ha]
  have htrace : ∀ a, Algebra.trace K L (e a) = ε a * Algebra.trace K L θ := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | of g =>
      rw [heof, Algebra.trace_eq_of_algEquiv]
      simp [ε, augmentation, MonoidAlgebra.lift_of]
    | add a b ha hb => simp only [map_add, ha, hb, add_mul]
    | smul r a ha => simp only [map_smul, ha, smul_eq_mul, mul_assoc]
  constructor
  · intro h hx
    have hsum : ∑ σ : Γ, σ x = 0 := by
      rw [← trace_eq_sum_automorphisms, hx, map_zero]
    have hone : (1 : K) = 0 := by
      exact (Fintype.linearIndependent_iff.mp h (fun _ => 1)
        (by simpa only [one_smul] using hsum)) 1
    exact one_ne_zero hone
  · intro hx
    let a := e.symm x
    have hea : e a = x := e.apply_symm_apply x
    have hε : ε a ≠ 0 := by
      intro hzero
      apply hx
      rw [← hea, htrace, hzero, zero_mul]
    have hnil : ∀ a : MonoidAlgebra K Γ, ε a = 0 → IsNilpotent a := by
      intro a ha
      have hbound := PGroupAugmentation.augmentation_ideal_pow_card (R := K) p hG
      exact ⟨Nat.card Γ, Ideal.pow_eq_zero_of_mem hbound le_rfl ha⟩
    have hu : IsUnit a := (isUnit_iff_augmentation_ne_zero ε hnil a).mpr hε
    let f : MonoidAlgebra K Γ →ₗ[K] L :=
      e.toLinearMap.comp (LinearMap.mulRight K a)
    have hinj : Function.Injective f := e.injective.comp hu.mul_left_injective
    have hind := c.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hinj)
    convert hind using 1
    ext g
    exact ((hequiv g a).trans (congrArg g hea)).symm

end D5.S3.FiniteGroups.GroupAlgebra.PGroupNormalTrace
