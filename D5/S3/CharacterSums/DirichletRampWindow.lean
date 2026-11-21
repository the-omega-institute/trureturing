/- GID: D5/S3/CharacterSums/DirichletRampWindow
   generality: I
   mirror-B: D5/B/S3/CharacterSums/DirichletRampWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Concave envelopes for native character ramps from their active knots. -/

import D5.S3.CharacterSums.DirichletRampEndpoint
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
/-! # Finite character-ramp tests on a real window

The positive-part summands are affine between successive nonzero coefficients.
The interval endpoints and these knots determine comparison with a concave envelope.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset Set Real
open D5.S3.CharacterSums.DirichletRampEndpoint D5.S3.Weil.Mertens.IntegratedExplicit
noncomputable section
namespace D5.S3.CharacterSums.DirichletRampWindow
private abbrev coeff {N : ℕ} (χ : DirichletCharacter ℂ N) (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod N)

private theorem extend_ramp {N : ℕ} (χ : DirichletCharacter ℂ N) {y Z : ℝ} (hy : y ≤ Z) :
    characterRamp χ y = ∑ n ∈ Finset.Ioc 0 ⌊Z⌋₊,
      coeff χ n * ((max (y / n - 1) 0 : ℝ) : ℂ) := by
  rw [← Finset.sum_subset (s₁ := Finset.Ioc 0 ⌊y⌋₊)
    (Finset.Ioc_subset_Ioc_right (Nat.floor_mono hy))]
  · apply Finset.sum_congr rfl
    intro n _
    simp only [mangoldtRamp, Complex.ofReal_mul, coeff]
    ring
  · intro n hn hny
    obtain ⟨hn0, _⟩ := Finset.mem_Ioc.mp hn
    have hlt : ⌊y⌋₊ < n := by
      by_contra! h
      exact hny (Finset.mem_Ioc.mpr ⟨hn0,h⟩)
    have hp : (0:ℝ) < n := by exact_mod_cast hn0
    rw [max_eq_right (sub_nonpos.mpr ((div_le_one hp).mpr (Nat.lt_of_floor_lt hlt).le))]
    simp

private theorem affine {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hn : χ ≠ 1)
    {u x v a b : ℝ} (hu : u ≤ x) (hv : x ≤ v)
    (hc : ∀ n : ℕ, (n:ℝ) ∈ Set.Ioo u v → coeff χ n = 0)
    (hab : a+b=1) (hm : a*u+b*v=x) :
    gChi χ x = (a:ℂ)*gChi χ u + (b:ℂ)*gChi χ v := by
  have hab' : (a:ℂ)+(b:ℂ)=1 := by exact_mod_cast hab
  have hm' : (a:ℂ)*(u:ℂ)+(b:ℂ)*(v:ℂ)=(x:ℂ) := by exact_mod_cast hm
  have hsum : characterRamp χ x = (a:ℂ)*characterRamp χ u + (b:ℂ)*characterRamp χ v := by
    rw [extend_ramp χ hv, extend_ramp χ (hu.trans hv), extend_ramp χ (le_refl v),
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hnm => ?_
    have hpos : (0:ℝ)<n := by exact_mod_cast (Finset.mem_Ioc.mp hnm).1
    by_cases hnu : (n:ℝ) ≤ u
    · have hw (t : ℝ) (ht : (n:ℝ) ≤ t) : max (t / n - 1) 0 = t/n-1 :=
        max_eq_left (sub_nonneg.mpr ((one_le_div hpos).mpr ht))
      rw [hw _ (hnu.trans hu), hw _ hnu, hw _ (hnu.trans (hu.trans hv))]
      push_cast
      rw [← hm']
      linear_combination coeff χ n * hab'
    by_cases hvn : v ≤ (n:ℝ)
    · have hw (t : ℝ) (ht : t ≤ (n:ℝ)) : max (t / n - 1) 0 = 0 :=
        max_eq_right (sub_nonpos.mpr ((div_le_one hpos).mpr ht))
      simp [hw _ (hv.trans hvn), hw _ (hu.trans (hv.trans hvn)), hw _ hvn]
    · simp [hc n ⟨lt_of_not_ge hnu, lt_of_not_ge hvn⟩]
  simp only [gChi,ite_eq_right hn,hsum]
  rw [← hm']
  ring

/-- A concave envelope on a closed interval can be tested at its endpoints and interior active knots. -/
theorem concave_window_iff {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hn : χ ≠ 1)
    {Y Z : ℝ} (hZ : Y ≤ Z) (B : ℝ → ℝ) (hB : ConcaveOn ℝ (Set.Icc Y Z) B) :
    (∀ x ∈ Set.Icc Y Z, ‖gChi χ x‖ ≤ B x) ↔
    ‖gChi χ Y‖ ≤ B Y ∧ ‖gChi χ Z‖ ≤ B Z ∧
      ∀ n : ℕ, (n:ℝ) ∈ Set.Ioo Y Z → (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n:ZMod N) ≠ 0 →
        ‖gChi χ n‖ ≤ B n := by
  classical
  constructor
  · intro h
    exact ⟨h Y ⟨le_rfl,hZ⟩,h Z ⟨hZ,le_rfl⟩,fun n hn _ => h n ⟨hn.1.le,hn.2.le⟩⟩
  rintro ⟨hlo,hhi,hint⟩ x hx
  let T := (Finset.range (⌊Z⌋₊ + 1)).filter fun n : ℕ => (n:ℝ) ∈ Set.Ioo Y Z ∧ coeff χ n ≠ 0
  let points : Finset ℝ := insert Y (insert Z (T.image fun n : ℕ => (n:ℝ)))
  have hpoints {t : ℝ} (ht : t ∈ points) : t ∈ Set.Icc Y Z ∧ ‖gChi χ t‖ ≤ B t := by
    simp only [points,Finset.mem_insert,Finset.mem_image] at ht
    rcases ht with rfl | rfl | ⟨n, hm, rfl⟩
    · exact ⟨⟨le_rfl,hZ⟩,hlo⟩
    · exact ⟨⟨hZ,le_rfl⟩,hhi⟩
    · obtain ⟨_, hmem, hcoeff⟩ := Finset.mem_filter.mp hm
      exact ⟨⟨hmem.1.le,hmem.2.le⟩,hint _ hmem hcoeff⟩
  let L := points.filter fun t => t ≤ x
  let R := points.filter fun t => x ≤ t
  have hL : L.Nonempty := ⟨Y, Finset.mem_filter.mpr ⟨by simp [points],hx.1⟩⟩
  have hR : R.Nonempty := ⟨Z, Finset.mem_filter.mpr ⟨by simp [points],hx.2⟩⟩
  let u := L.max' hL
  let v := R.min' hR
  obtain ⟨hupt, hu⟩ := Finset.mem_filter.mp (L.max'_mem hL)
  obtain ⟨hvpt, hv⟩ := Finset.mem_filter.mp (R.min'_mem hR)
  change u ≤ x at hu
  change x ≤ v at hv
  obtain ⟨huI,eu⟩ := hpoints hupt
  obtain ⟨hvI,ev⟩ := hpoints hvpt
  have hz : ∀ n : ℕ, (n:ℝ) ∈ Set.Ioo u v → coeff χ n = 0 := by
    intro n hni
    by_contra hnon
    have hnZ : (n:ℝ) < Z := hni.2.trans_le hvI.2
    have hT : n ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
      have := Nat.le_floor hnZ.le
      omega),⟨huI.1.trans_lt hni.1,hnZ⟩,hnon⟩
    have hP : (n:ℝ) ∈ points := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hT))
    rcases le_total (n:ℝ) x with hnx|hxn
    · exact hni.1.not_ge (Finset.le_max' L _ (Finset.mem_filter.mpr ⟨hP,hnx⟩))
    · exact hni.2.not_ge (Finset.min'_le R _ (Finset.mem_filter.mpr ⟨hP,hxn⟩))
  rcases eq_or_lt_of_le (hu.trans hv) with heq|hlt
  · exact le_antisymm hu (heq ▸ hv) ▸ eu
  let a := (v-x)/(v-u)
  let b := (x-u)/(v-u)
  have hd := sub_pos.mpr hlt
  have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr hv) hd.le
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hu) hd.le
  have hab : a+b=1 := by dsimp [a,b]; field_simp; ring
  have hm : a*u+b*v=x := by dsimp [a,b]; field_simp; ring
  have hc := hB.2 huI hvI ha hb hab
  change a * B u + b * B v ≤ B (a*u+b*v) at hc
  rw [hm] at hc
  rw [affine hn hu hv hz hab hm]
  exact (norm_add_le ..).trans (by
    rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg ha,abs_of_nonneg hb]
    exact (add_le_add (mul_le_mul_of_nonneg_left eu ha) (mul_le_mul_of_nonneg_left ev hb)).trans hc)
/-- The power envelope and native logarithmic derivative admit a single finite window test. -/
theorem power_log_window_iff {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hn : χ ≠ 1)
    {p A c Y Z : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (hA : 0 ≤ A) (hc : 0 ≤ c) (hY : 0 < Y) (hZ : Y ≤ Z) :
    (∀ x ∈ Set.Icc Y Z, ‖gChi χ x‖ ≤ A * x ^ p ∧
      ‖deriv χ.LFunction 1 / χ.LFunction 1‖ ≤ c * log x) ↔
    (‖gChi χ Y‖ ≤ A * Y ^ p ∧ ‖gChi χ Z‖ ≤ A * Z ^ p ∧
      ∀ n : ℕ, (n:ℝ) ∈ Set.Ioo Y Z → (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n:ZMod N) ≠ 0 →
        ‖gChi χ n‖ ≤ A * (n : ℝ) ^ p) ∧
        ‖deriv χ.LFunction 1 / χ.LFunction 1‖ ≤ c * log Y := by
  have hconc : ConcaveOn ℝ (Set.Icc Y Z) (fun x : ℝ => x ^ p) :=
    (Real.concaveOn_rpow hp hp').subset (fun x hx => hY.le.trans hx.1) (convex_Icc ..)
  have hscaled : ConcaveOn ℝ (Set.Icc Y Z) (fun x : ℝ => A * x ^ p) :=
    ConcaveOn.smul hA hconc
  have hw := concave_window_iff hn hZ _ hscaled
  constructor
  · intro h
    exact ⟨hw.mp (fun x hx => (h x hx).1), (h Y ⟨le_rfl,hZ⟩).2⟩
  · rintro ⟨h,hd⟩ x hx
    exact ⟨hw.mpr h x hx, hd.trans (mul_le_mul_of_nonneg_left (log_le_log hY hx.1) hc)⟩
end D5.S3.CharacterSums.DirichletRampWindow
