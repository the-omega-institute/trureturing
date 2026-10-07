/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryInvolutionField
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryInvolutionField
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

/-! Finite fields with a supplied, nonidentity involution. Artin's theorem,
finite-field Frobenius, and native trace/norm theorems are used directly. -/
namespace NikolovSegal.UnitaryField

variable {F : Type*} [Field F] [Finite F]

def fixedField (ι : F ≃+* F) : Subfield F :=
  FixedPoints.subfield (Subgroup.zpowers ι) F

@[simp] theorem mem_fixedField (ι : F ≃+* F) (x : F) :
    x ∈ fixedField ι ↔ ι x = x := by
  change (∀ g : Subgroup.zpowers ι, g • x = x) ↔ _
  constructor
  · intro h
    exact h ⟨ι, Subgroup.mem_zpowers ι⟩
  · intro h g
    exact smul_eq_self_of_mem_zpowers g.property h

theorem finrank_fixedField (ι : F ≃+* F)
    (hinv : Function.Involutive ι) (hne : ι ≠ RingEquiv.refl F) :
    Module.finrank (fixedField ι) F = 2 := by
  classical
  have ho : orderOf ι = 2 := orderOf_eq_prime (by ext x; exact hinv x) hne
  have hc : Nat.card (Subgroup.zpowers ι) = 2 := (Nat.card_zpowers ι).trans ho
  haveI : Finite (Subgroup.zpowers ι) := Nat.finite_of_card_ne_zero (by omega)
  letI := Fintype.ofFinite (Subgroup.zpowers ι)
  rw [fixedField, FixedPoints.finrank_eq_card, ← Nat.card_eq_fintype_card]
  exact hc

theorem card_field (ι : F ≃+* F)
    (hinv : Function.Involutive ι) (hne : ι ≠ RingEquiv.refl F) :
    Nat.card F = Nat.card (fixedField ι) ^ 2 := by
  rw [Module.natCard_eq_pow_finrank (K := fixedField ι), finrank_fixedField ι hinv hne]

def fixedAlgEquiv (ι : F ≃+* F) : F ≃ₐ[fixedField ι] F where
  __ := ι
  commutes' x := (mem_fixedField ι x).mp x.property

theorem involution_eq_pow (ι : F ≃+* F)
    (hinv : Function.Involutive ι) (hne : ι ≠ RingEquiv.refl F) (x : F) :
    ι x = x ^ Nat.card (fixedField ι) := by
  classical
  letI := Fintype.ofFinite (fixedField ι)
  obtain ⟨j, hj⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (fixedField ι) F).surjective
      (fixedAlgEquiv ι)
  have hjlt : j.val < 2 := by simpa [finrank_fixedField ι hinv hne] using j.isLt
  have hjne : j.val ≠ 0 := by
    intro h
    have hh : fixedAlgEquiv ι = 1 := by simpa [h] using hj.symm
    apply hne
    ext y
    exact DFunLike.congr_fun hh y
  have hjone : j.val = 1 := by omega
  have h := DFunLike.congr_fun hj x
  change (FiniteField.frobeniusAlgEquivOfAlgebraic (fixedField ι) F ^ j.val) x = ι x at h
  rw [hjone, pow_one] at h
  change x ^ Fintype.card (fixedField ι) = ι x at h
  rw [← Nat.card_eq_fintype_card] at h
  exact h.symm

theorem trace_formula (ι : F ≃+* F)
    (hinv : Function.Involutive ι) (hne : ι ≠ RingEquiv.refl F) (x : F) :
    (Algebra.trace (fixedField ι) F x : F) = x + ι x := by
  change algebraMap (fixedField ι) F (Algebra.trace (fixedField ι) F x) = _
  rw [FiniteField.algebraMap_trace_eq_sum_pow, finrank_fixedField ι hinv hne]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, add_zero, zero_add]
  rw [← involution_eq_pow ι hinv hne]

theorem norm_formula (ι : F ≃+* F)
    (hinv : Function.Involutive ι) (hne : ι ≠ RingEquiv.refl F) (x : F) :
    (Algebra.norm (fixedField ι) x : F) = x * ι x := by
  change algebraMap (fixedField ι) F (Algebra.norm (fixedField ι) x) = _
  rw [FiniteField.algebraMap_norm_eq_prod_pow, finrank_fixedField ι hinv hne]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, pow_zero, pow_one, one_mul]
  rw [← involution_eq_pow ι hinv hne]

theorem trace_surjective (ι : F ≃+* F)
    (hinv : Function.Involutive ι) (hne : ι ≠ RingEquiv.refl F)
    (t : fixedField ι) : ∃ x : F, x + ι x = t := by
  obtain ⟨x, hx⟩ := Algebra.trace_surjective (fixedField ι) F t
  exact ⟨x, (trace_formula ι hinv hne x).symm.trans (congrArg Subtype.val hx)⟩

theorem norm_units_surjective (ι : F ≃+* F)
    (hinv : Function.Involutive ι) (hne : ι ≠ RingEquiv.refl F)
    (t : (fixedField ι)ˣ) : ∃ x : Fˣ, (x : F) * ι x = (t : fixedField ι) := by
  obtain ⟨x, hx⟩ := FiniteField.unitsMap_norm_surjective (fixedField ι) F t
  refine ⟨x, (norm_formula ι hinv hne x).symm.trans ?_⟩
  exact congrArg (fun y : (fixedField ι)ˣ => ((y : fixedField ι) : F)) hx

noncomputable def normOne (ι : F ≃+* F) : Subgroup Fˣ :=
  (Units.map (Algebra.norm (fixedField ι) (S := F))).ker

@[simp] theorem mem_normOne (ι : F ≃+* F)
    (hinv : Function.Involutive ι) (hne : ι ≠ RingEquiv.refl F) (x : Fˣ) :
    x ∈ normOne ι ↔ (x : F) * ι x = 1 := by
  change Units.map (Algebra.norm (fixedField ι)) x = 1 ↔ _
  rw [Units.ext_iff]
  change Algebra.norm (fixedField ι) (x : F) = 1 ↔ _
  rw [← (Subfield.subtype (fixedField ι)).injective.eq_iff]
  change ((Algebra.norm (fixedField ι) (x : F) : fixedField ι) : F) = 1 ↔ _
  rw [norm_formula ι hinv hne]

theorem card_normOne (ι : F ≃+* F)
    (hinv : Function.Involutive ι) (hne : ι ≠ RingEquiv.refl F) :
    Nat.card (normOne ι) = Nat.card (fixedField ι) + 1 := by
  let f := Units.map (Algebra.norm (fixedField ι) (S := F))
  have hs := FiniteField.unitsMap_norm_surjective (fixedField ι) F
  have h := f.ker.card_mul_index
  rw [Subgroup.index_ker, f.range_eq_top.mpr hs, Subgroup.card_top,
    Nat.card_units, Nat.card_units, card_field ι hinv hne] at h
  have hQ : 2 ≤ Nat.card (fixedField ι) := Finite.one_lt_card
  have he : Nat.card (fixedField ι) ^ 2 - 1 =
      (Nat.card (fixedField ι) + 1) * (Nat.card (fixedField ι) - 1) := by
    have ht : Nat.card (fixedField ι) - 1 + 1 = Nat.card (fixedField ι) := by omega
    have hs : 1 ≤ Nat.card (fixedField ι) ^ 2 := by nlinarith
    have hh := Nat.sub_add_cancel hs
    nlinarith
  rw [he] at h
  exact Nat.eq_of_mul_eq_mul_right (by omega) h

end NikolovSegal.UnitaryField
