/- GID: D5/S3/Quantum/Foundation/TrigonometricMomentGap
   generality: I
   mirror-B: D5/B/S3/Quantum/Foundation/TrigonometricMomentGap
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [D5/S3/Quantum/Foundation/WeightedRelationConfirmation]
   utility: none
   digest: Attained full-effect comparison on the original trigonometric moment body. -/

import D5.S3.Quantum.Foundation.WeightedRelationConfirmation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic

/-! The entire second trigonometric moment body and its homogeneous cone.
All confirming effects below are the original real-linear proper effects.
No finite state or effect selection enters the comparison domain. -/

noncomputable section
open Set
open scoped BigOperators

namespace D5.S3.Quantum.Foundation.TrigonometricMomentGap

open CircuitBalancedConfirmation WeightedRelationConfirmation

abbrev Coordinates := Fin 4 → ℝ
abbrev Carrier := ℝ × Coordinates

def momentCurve (θ : ℝ) : Coordinates :=
  ![Real.cos θ, Real.sin θ, Real.cos (2 * θ), Real.sin (2 * θ)]

def body : Set Coordinates := convexHull ℝ (range momentCurve)

def lift : Coordinates →ᵃ[ℝ] Carrier :=
  (AffineMap.const ℝ Coordinates (1 : ℝ)).prod (AffineMap.id ℝ Coordinates)

def curve (θ : ℝ) : Carrier := lift (momentCurve θ)

def states : Set Carrier := convexHull ℝ (range curve)

private theorem states_image : states = lift '' body := by
  rw [body, lift.image_convexHull]
  congr 1
  exact (range_comp lift momentCurve).symm

private theorem curve_mem (θ : ℝ) : curve θ ∈ states :=
  subset_convexHull ℝ _ ⟨θ, rfl⟩

private theorem states_unit {x : Carrier} (hx : x ∈ states) : x.1 = 1 := by
  rw [states_image] at hx
  rcases hx with ⟨z, _, rfl⟩
  rfl

private theorem radial_zero :
    ∃ t : ℝ, 0 ≤ t ∧ ∃ z ∈ states, (0 : Carrier) = t • z :=
  ⟨0, le_rfl, curve 0, curve_mem 0, by simp⟩

private theorem radial_add {x y : Carrier}
    (hx : ∃ t : ℝ, 0 ≤ t ∧ ∃ z ∈ states, x = t • z)
    (hy : ∃ t : ℝ, 0 ≤ t ∧ ∃ z ∈ states, y = t • z) :
    ∃ t : ℝ, 0 ≤ t ∧ ∃ z ∈ states, x + y = t • z := by
  rcases hx with ⟨r, hr, z, hz, rfl⟩
  rcases hy with ⟨s, hs, w, hw, rfl⟩
  by_cases h : r + s = 0
  · have hr0 : r = 0 := by linarith
    have hs0 : s = 0 := by linarith
    simpa [hr0, hs0] using radial_zero
  have hp : 0 < r + s := lt_of_le_of_ne (add_nonneg hr hs) (Ne.symm h)
  refine ⟨r + s, hp.le, (r / (r + s)) • z + (s / (r + s)) • w,
    (convex_convexHull ℝ _) hz hw (div_nonneg hr hp.le)
      (div_nonneg hs hp.le) (by field_simp), ?_⟩
  rw [smul_add, smul_smul, smul_smul]
  congr 1 <;> field_simp

def cone : PointedCone ℝ Carrier where
  carrier := {x | ∃ t : ℝ, 0 ≤ t ∧ ∃ z ∈ states, x = t • z}
  zero_mem' := radial_zero
  add_mem' := radial_add
  smul_mem' := by
    rintro ⟨r, hr⟩ x ⟨s, hs, z, hz, rfl⟩
    exact ⟨r * s, mul_nonneg hr hs, z, hz, by simp [smul_smul]⟩

def unit : Carrier →ₗ[ℝ] ℝ := LinearMap.fst ℝ ℝ Coordinates

private theorem states_mem_cone {x : Carrier} (hx : x ∈ states) : x ∈ cone :=
  ⟨1, zero_le_one, x, hx, by simp⟩

private theorem original_base : base cone unit = states := by
  ext x
  constructor
  · rintro ⟨⟨t, ht, z, hz, rfl⟩, hu⟩
    have ht1 : t = 1 := by simpa [unit, states_unit hz] using hu
    simpa [ht1] using hz
  · intro hx
    exact ⟨states_mem_cone hx, states_unit hx⟩

private theorem cone_strict {x : Carrier} (hx : x ∈ cone) (hne : x ≠ 0) :
    0 < unit x := by
  rcases hx with ⟨t, ht, z, hz, rfl⟩
  have ht0 : t ≠ 0 := by intro h; exact hne (by simp [h])
  simpa [unit, states_unit hz] using lt_of_le_of_ne ht (Ne.symm ht0)

private theorem effect_bounds (f : Carrier →ₗ[ℝ] ℝ)
    (h : ∀ θ : ℝ, 0 ≤ f (curve θ) ∧ f (curve θ) ≤ 1) :
    ∀ x ∈ states, 0 ≤ f x ∧ f x ≤ 1 := by
  apply convexHull_min
  · rintro _ ⟨θ, rfl⟩
    exact h θ
  · exact ((convex_Ici (0 : ℝ)).inter (convex_Iic 1)).is_linear_preimage f.isLinear

private theorem proper_on_curve (f : Carrier →ₗ[ℝ] ℝ) :
    proper cone unit f ↔ ∀ θ : ℝ, 0 ≤ f (curve θ) ∧ f (curve θ) ≤ 1 := by
  constructor
  · intro hf θ
    exact hf _ (states_mem_cone (curve_mem θ))
  · intro hf x hx
    rcases hx with ⟨t, ht, z, hz, rfl⟩
    have hb := effect_bounds f hf z hz
    simpa [unit, map_smul, states_unit hz] using
      And.intro (mul_nonneg ht hb.1) (mul_le_mul_of_nonneg_left hb.2 ht)

def effect (a : ℝ) (b : Coordinates) : Carrier →ₗ[ℝ] ℝ :=
  a • LinearMap.fst ℝ ℝ Coordinates +
    ∑ i : Fin 4, b i • ((LinearMap.proj i).comp (LinearMap.snd ℝ ℝ Coordinates))

def trigonometric (a : ℝ) (b : Coordinates) (θ : ℝ) : ℝ :=
  a + b 0 * Real.cos θ + b 1 * Real.sin θ +
    b 2 * Real.cos (2 * θ) + b 3 * Real.sin (2 * θ)

private theorem effect_curve (a : ℝ) (b : Coordinates) (θ : ℝ) :
    effect a b (curve θ) = trigonometric a b θ := by
  simp [effect, curve, lift, momentCurve, trigonometric, Fin.sum_univ_succ]
  ring

private theorem all_linear_effects (f : Carrier →ₗ[ℝ] ℝ) :
    ∃ a b, f = effect a b := by
  refine ⟨f (1, 0), fun i => f (0, Pi.single i 1), ?_⟩
  ext x
  have hx : x = x.1 • (1, (0 : Coordinates)) +
      ∑ i : Fin 4, x.2 i • (0, Pi.single i 1) := by
    ext i
    · simp
    · simp [Fin.sum_univ_succ]
      fin_cases i <;> simp [Pi.single_apply]
  conv_lhs => rw [hx]
  simp [effect, map_add, map_smul, map_sum, mul_comm]

def p : Carrier := curve 0
def x : Carrier := (1 / 2 : ℝ) • (curve (Real.pi / 2) + curve (-Real.pi / 2))
def y : Carrier := curve Real.pi
def mixed : Carrier := (1 / 2 : ℝ) • (x + y)
def angle : ℝ := Real.arccos (-2 / 3)
def z : Carrier := (1 / 2 : ℝ) • (curve angle + curve (-angle))
def attainer : Carrier →ₗ[ℝ] ℝ := effect (17 / 50) ![12 / 25, 0, 9 / 50, 0]

private theorem midpoint_mem {a b : Carrier} (ha : a ∈ states) (hb : b ∈ states) :
    (1 / 2 : ℝ) • (a + b) ∈ states := by
  simpa [smul_add] using (convex_convexHull ℝ (range curve)) ha hb
    (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num)

private theorem state_members : p ∈ states ∧ x ∈ states ∧ y ∈ states ∧
    mixed ∈ states ∧ z ∈ states := by
  have hx := midpoint_mem (curve_mem (Real.pi / 2)) (curve_mem (-Real.pi / 2))
  exact ⟨curve_mem 0, hx, curve_mem Real.pi,
    midpoint_mem hx (curve_mem Real.pi), midpoint_mem (curve_mem angle) (curve_mem (-angle))⟩

private theorem decomposition : mixed = (1 / 10 : ℝ) • p + (9 / 10 : ℝ) • z := by
  have hc : Real.cos angle = -2 / 3 := Real.cos_arccos (by norm_num) (by norm_num)
  ext i
  · norm_num [mixed, x, y, p, z, curve, lift]
  · fin_cases i <;>
      simp [mixed, x, y, p, z, curve, lift, momentCurve, Real.cos_two_mul,
        Real.sin_two_mul, Real.cos_neg, Real.sin_neg, hc] <;> ring

private theorem attainer_formula (θ : ℝ) :
    attainer (curve θ) = ((3 * Real.cos θ + 2) / 5) ^ 2 := by
  rw [attainer, effect_curve]
  simp [trigonometric, Real.cos_two_mul]
  ring

private theorem attainer_proper : proper cone unit attainer := by
  apply (proper_on_curve attainer).mpr
  intro θ
  rw [attainer_formula]
  constructor
  · positivity
  · have hlo := Real.neg_one_le_cos θ
    have hhi := Real.cos_le_one θ
    nlinarith [sq_nonneg (Real.cos θ + 1)]

private theorem attainer_confirms : confirms cone unit p attainer := by
  refine ⟨attainer_proper, ?_⟩
  norm_num [p, attainer_formula]

private theorem attainer_value : attainer mixed = 1 / 10 := by
  rw [decomposition, map_add, map_smul, map_smul, attainer_confirms.2]
  have hz : attainer z = 0 := by
    have hc : Real.cos angle = -2 / 3 := Real.cos_arccos (by norm_num) (by norm_num)
    simp [z, map_smul, map_add, attainer_formula, hc, Real.cos_neg]
  norm_num [hz]

private theorem universal_lower (f : Carrier →ₗ[ℝ] ℝ) (hf : confirms cone unit p f) :
    (1 / 10 : ℝ) ≤ f mixed := by
  have hpos := (hf.1 z (states_mem_cone state_members.2.2.2.2)).1
  rw [decomposition, map_add, map_smul, map_smul, hf.2]
  dsimp only [smul_eq_mul]
  linarith

/-- The minimum is over every original globally proper real-linear confirmer.
The coefficient description is surjective onto all such effects. -/
theorem attained_full_effect_gap :
    base cone unit = lift '' body ∧
    (∀ f : Carrier →ₗ[ℝ] ℝ, ∃ a b, f = effect a b) ∧
    (∀ a b, proper cone unit (effect a b) ↔
      ∀ θ : ℝ, 0 ≤ trigonometric a b θ ∧ trigonometric a b θ ≤ 1) ∧
    (∀ w ∈ cone, w ≠ 0 → 0 < unit w) ∧
    p ∈ base cone unit ∧ x ∈ base cone unit ∧ y ∈ base cone unit ∧
    mixed ∈ base cone unit ∧ z ∈ base cone unit ∧
    (∀ f, confirms cone unit p f → (1 / 10 : ℝ) ≤ f mixed) ∧
    confirms cone unit p attainer ∧ attainer mixed = 1 / 10 ∧
    comparison cone unit p mixed = 1 / 10 := by
  refine ⟨original_base.trans states_image, all_linear_effects, ?_,
    fun _ hw hn => cone_strict hw hn, ?_, ?_, ?_, ?_, ?_, universal_lower,
    attainer_confirms, attainer_value, ?_⟩
  · intro a b
    simpa only [effect_curve] using proper_on_curve (effect a b)
  · rw [original_base]; exact state_members.1
  · rw [original_base]; exact state_members.2.1
  · rw [original_base]; exact state_members.2.2.1
  · rw [original_base]; exact state_members.2.2.2.1
  · rw [original_base]; exact state_members.2.2.2.2
  · rw [← attainer_value]
    exact attained_comparison (states_mem_cone state_members.2.2.2.1) attainer
      attainer_confirms (fun f hf => attainer_value ▸ universal_lower f hf)

end D5.S3.Quantum.Foundation.TrigonometricMomentGap
