/- GID: D5/S3/Combinatorics/AdditiveCodes/AdditiveCodesFrobenius
   generality: G
   mirror-B: D5/B/S3/Combinatorics/AdditiveCodes/AdditiveCodesFrobenius
   mirror-E: none(waiver:general-frobenius-blocking-construction)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Projectivization.Cardinality]
   utility: none
   digest: Frobenius graph labels and an algebraic blocking set for every plane. -/

import Mathlib.LinearAlgebra.Projectivization.Cardinality
import D5.S3.Combinatorics.AdditiveCodes.AdditiveExtensionDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.AdditiveCodes

open scoped LinearAlgebra.Projectivization

/-- The complement of the nonzero Frobenius-collinearity cone blocks every plane;
Frobenius graph fibres provide labels whose equal-label differences avoid it. -/
theorem frobeniusBlocking (F : Type*) [Field F] [Finite F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (hF : ∃ c : F, c ^ p ≠ c) :
    ∃ B : Finset (Projectivization F (Fin 4 → F)),
      ∃ h : (Fin 4 → F) → (Fin 2 → F),
        1 < B.card ∧
        (∃ P : Projectivization F (Fin 4 → F), P ∉ B) ∧
        (∀ K : Submodule F (Fin 4 → F), Module.finrank F K = 2 →
          ∃ P ∈ B, P.submodule ≤ K) ∧
        (∀ x y : Fin 4 → F, (hxy : x ≠ y) → h x = h y →
          Projectivization.mk F (x - y) (sub_ne_zero.mpr hxy) ∉ B) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let V := Fin 4 → F
  let C : V → Prop := fun v =>
    (v 0 ≠ 0 ∨ v 1 ≠ 0) ∧ (v 2 ≠ 0 ∨ v 3 ≠ 0) ∧
      v 2 * (v 1) ^ p = v 3 * (v 0) ^ p
  have hscale (a : F) (ha : a ≠ 0) (v : V) : C (a • v) ↔ C v := by
    have hp : a ^ p ≠ 0 := pow_ne_zero p ha
    dsimp [C, V]
    simp only [mul_pow]
    have heq : a * v 2 * (a ^ p * v 1 ^ p) =
        a * v 3 * (a ^ p * v 0 ^ p) ↔ v 2 * v 1 ^ p = v 3 * v 0 ^ p := by
      calc
        _ ↔ (a * a ^ p) * (v 2 * v 1 ^ p) =
            (a * a ^ p) * (v 3 * v 0 ^ p) := by ring_nf
        _ ↔ _ := mul_right_inj' (mul_ne_zero ha hp)
    rw [heq]
    simp [mul_eq_zero, ha]
  let : Fintype (Projectivization F V) := Fintype.ofFinite _
  let B : Finset (Projectivization F V) := Finset.univ.filter (fun P => ¬ C P.rep)
  have hmem (v : V) (hv : v ≠ 0) :
      Projectivization.mk F v hv ∈ B ↔ ¬ C v := by
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep F v hv
    dsimp [B]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← ha]
    exact not_congr (hscale (a : F) a.ne_zero v)
  let h : V → (Fin 2 → F) := fun v => ![v 2 - (v 0) ^ p, v 3 - (v 1) ^ p]
  refine ⟨B, h, ?_, ?_, ?_, ?_⟩
  · let u : V := ![0, 0, 1, 0]
    let v : V := ![0, 0, 0, 1]
    have hu : u ≠ 0 := by intro he; have := congr_fun he 2; simp [u, V] at this
    have hv : v ≠ 0 := by intro he; have := congr_fun he 3; simp [v, V] at this
    have huB : Projectivization.mk F u hu ∈ B := by
      rw [hmem]; simp [C, u]
    have hvB : Projectivization.mk F v hv ∈ B := by
      rw [hmem]; simp [C, v]
    have huv : Projectivization.mk F u hu ≠ Projectivization.mk F v hv := by
      intro he
      obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' F u v hu hv).mp he
      have := congr_fun ha 2
      simp [u, v, V, Pi.smul_apply, smul_eq_mul] at this
    have hsub : {Projectivization.mk F u hu, Projectivization.mk F v hv} ⊆ B := by
      intro P hP
      simp only [Finset.mem_insert, Finset.mem_singleton] at hP
      rcases hP with rfl | rfl <;> assumption
    have := Finset.card_le_card hsub
    have hcard : 2 ≤ B.card := by simpa [huv] using this
    omega
  · let u : V := ![1, 0, 1, 0]
    have hu : u ≠ 0 := by intro he; have := congr_fun he 0; simp [u, V] at this
    refine ⟨Projectivization.mk F u hu, ?_⟩
    rw [hmem]
    simp [C, u, (Fact.out : p.Prime).ne_zero]
  · intro K hK
    by_contra hn
    have hall : ∀ v ∈ K, v ≠ 0 → C v := by
      intro v hv hv0
      by_contra hc
      apply hn
      refine ⟨Projectivization.mk F v hv0, (hmem v hv0).mpr hc, ?_⟩
      simpa only [Projectivization.submodule_mk] using
        (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv))
    let f : K →ₗ[F] (Fin 2 → F) :=
      { toFun := fun v => ![v.val 0, v.val 1]
        map_add' := by intro x y; ext i; fin_cases i <;> rfl
        map_smul' := by intro a x; ext i; fin_cases i <;> rfl }
    have hf : Function.Injective f := by
      apply (LinearMap.ker_eq_bot).mp
      apply eq_bot_iff.mpr
      intro v hv
      change v = 0
      have hvf : f v = 0 := hv
      have hv0 : (v : V) = 0 := by
        by_contra he
        have hc := (hall v.val v.property he).1
        have h0 := congr_fun hvf 0
        have h1 := congr_fun hvf 1
        change (v : V) 0 = 0 at h0
        change (v : V) 1 = 0 at h1
        exact hc.elim (fun ht => ht h0) (fun ht => ht h1)
      exact Subtype.ext hv0
    have hdim : Module.finrank F K = Module.finrank F (Fin 2 → F) := by
      simpa using hK
    have hsur : Function.Surjective f := by
      have he := (LinearEquiv.ofInjectiveOfFinrankEq f hf hdim).surjective
      change Function.Surjective
        (LinearEquiv.ofInjectiveOfFinrankEq f hf hdim).toLinearMap at he
      simpa only [LinearEquiv.coe_ofInjectiveOfFinrankEq] using he
    obtain ⟨u, hu⟩ := hsur (![1, 0] : Fin 2 → F)
    obtain ⟨v, hv⟩ := hsur (![0, 1] : Fin 2 → F)
    have hu0 : (u : V) 0 = 1 := by simpa [f] using congr_fun hu 0
    have hu1 : (u : V) 1 = 0 := by simpa [f] using congr_fun hu 1
    have hv0 : (v : V) 0 = 0 := by simpa [f] using congr_fun hv 0
    have hv1 : (v : V) 1 = 1 := by simpa [f] using congr_fun hv 1
    have huN : (u : V) ≠ 0 := by intro he; simp [he] at hu0
    have hvN : (v : V) ≠ 0 := by intro he; simp [he] at hv1
    have huC := hall u.val u.property huN
    have hvC := hall v.val v.property hvN
    have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
    have hu3 : (u : V) 3 = 0 := by
      simpa [hu0, hu1, hp0] using huC.2.2.symm
    have hv2 : (v : V) 2 = 0 := by
      simpa [hv0, hv1, hp0] using hvC.2.2
    have hu2 : (u : V) 2 ≠ 0 := by simpa [hu3] using huC.2.1
    have huvN : ((u + v : K) : V) ≠ 0 := by
      intro he
      have := congr_fun he 0
      simp [hu0, hv0] at this
    have huvC := hall (u + v).val (u + v).property huvN
    have huv23 : (u : V) 2 = (v : V) 3 := by
      simpa [hu0, hu1, hv0, hv1, hu3, hv2] using huvC.2.2
    obtain ⟨c, hc⟩ := hF
    have hcN : ((u + c • v : K) : V) ≠ 0 := by
      intro he
      have := congr_fun he 0
      simp [hu0, hv0] at this
    have hcC := hall (u + c • v).val (u + c • v).property hcN
    have he : (u : V) 2 * c ^ p = (u : V) 2 * c := by
      simpa [hu0, hu1, hv0, hv1, hu3, hv2, ← huv23, mul_comm] using hcC.2.2
    exact hc (mul_left_cancel₀ hu2 he)
  · intro x y hxy hlabel
    rw [hmem]
    push Not
    have h0 := congr_fun hlabel 0
    have h1 := congr_fun hlabel 1
    have hz : x 2 - y 2 = (x 0 - y 0) ^ p := by
      simp only [h, Matrix.cons_val_zero] at h0
      rw [sub_pow_char]
      exact sub_eq_sub_iff_sub_eq_sub.mpr h0
    have hw : x 3 - y 3 = (x 1 - y 1) ^ p := by
      simp only [h, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h1
      rw [sub_pow_char]
      exact sub_eq_sub_iff_sub_eq_sub.mpr h1
    have hhead : x 0 - y 0 ≠ 0 ∨ x 1 - y 1 ≠ 0 := by
      by_contra hh
      push Not at hh
      apply hxy
      funext i
      fin_cases i
      · exact sub_eq_zero.mp hh.1
      · exact sub_eq_zero.mp hh.2
      · apply sub_eq_zero.mp
        simpa [hh.1, (Fact.out : p.Prime).ne_zero] using hz
      · apply sub_eq_zero.mp
        simpa [hh.2, (Fact.out : p.Prime).ne_zero] using hw
    refine ⟨hhead, ?_, ?_⟩
    · simpa [hz, hw, pow_ne_zero_iff (Fact.out : p.Prime).ne_zero] using hhead
    · simp only [Pi.sub_apply, hz, hw]
      exact mul_comm _ _

end D5.S3.Combinatorics.AdditiveCodes
