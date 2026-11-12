/- GID: D5/S3/Quantum/Foundation/TrigonometricMomentGap
   generality: I
   mirror-B: D5/B/S3/Quantum/Foundation/TrigonometricMomentGap
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [D5/S3/Quantum/Foundation/WeightedRelationConfirmation]
   utility: none
   digest: Attained full-effect comparison on the original trigonometric moment body. -/

import D5.S3.Quantum.Foundation.WeightedRelationConfirmation
import D5.S3.Quantum.Foundation.WholePairBallConfirmation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic

/-! The entire second trigonometric moment body and its homogeneous cone.
All confirming effects below are the original real-linear proper effects.
No finite state or effect selection enters the comparison domain. -/

noncomputable section
open Set
open scoped BigOperators

namespace D5.S3.Quantum.Foundation.TrigonometricMomentGap

open CircuitBalancedConfirmation WeightedRelationConfirmation
open WholePairBallConfirmation

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
  unfold states
  congr 1
  exact range_comp lift momentCurve

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
  apply LinearMap.ext
  intro x
  have hx : x = x.1 • (1, (0 : Coordinates)) +
      ∑ i : Fin 4, x.2 i • (0, Pi.single i 1) := by
    ext i
    · simp [Fin.sum_univ_succ]
    · simp [Fin.sum_univ_succ]
      fin_cases i <;> simp [Pi.single_apply]
  calc
    f x = f (x.1 • (1, (0 : Coordinates)) +
        ∑ i : Fin 4, x.2 i • (0, Pi.single i 1)) := congrArg f hx
    _ = x.1 * f (1, 0) + ∑ i : Fin 4, x.2 i * f (0, Pi.single i 1) := by
      rw [map_add, map_smul, map_sum]
      simp only [map_smul, smul_eq_mul]
    _ = _ := by simp [effect, mul_comm]

private theorem unique_support_hull {S : Set Carrier} {v : Carrier}
    (l : Carrier →ₗ[ℝ] ℝ) (h : ∀ w ∈ S, w = v ∨ l w < l v) :
    ∀ w ∈ convexHull ℝ S, w = v ∨ l w < l v := by
  apply convexHull_min h
  intro w hw z hz a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using hz
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simpa [hb0, ha1] using hw
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have he : a * l v + b * l v = l v := by rw [← add_mul, hab, one_mul]
  rcases hw with rfl | hw <;> rcases hz with rfl | hz
  · left
    rw [← add_smul, hab, one_smul]
  · right
    simp only [map_add, map_smul, smul_eq_mul]
    nlinarith [mul_pos hb' (sub_pos.mpr hz)]
  · right
    simp only [map_add, map_smul, smul_eq_mul]
    nlinarith [mul_pos ha' (sub_pos.mpr hw)]
  · right
    simp only [map_add, map_smul, smul_eq_mul]
    nlinarith [mul_pos ha' (sub_pos.mpr hw), mul_pos hb' (sub_pos.mpr hz)]

private theorem curve_eq_of_cos_sub {a θ : ℝ} (h : Real.cos (θ - a) = 1) :
    curve θ = curve a := by
  have he : Real.cos θ * Real.cos a + Real.sin θ * Real.sin a = 1 := by
    simpa only [Real.cos_sub] using h
  have hsq : (Real.cos θ - Real.cos a) ^ 2 + (Real.sin θ - Real.sin a) ^ 2 = 0 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq a]
  have hc : Real.cos θ = Real.cos a := by
    nlinarith [sq_nonneg (Real.cos θ - Real.cos a), sq_nonneg (Real.sin θ - Real.sin a)]
  have hs : Real.sin θ = Real.sin a := by
    nlinarith [sq_nonneg (Real.cos θ - Real.cos a), sq_nonneg (Real.sin θ - Real.sin a)]
  ext i
  · rfl
  · fin_cases i <;> simp [curve, lift, momentCurve, Real.cos_two_mul, Real.sin_two_mul, hc, hs]

private theorem curve_extreme (a : ℝ) : curve a ∈ states.extremePoints ℝ := by
  let l := effect 0 ![Real.cos a, Real.sin a, 0, 0]
  have hl (θ : ℝ) : l (curve θ) = Real.cos (θ - a) := by
    simp [l, effect_curve, trigonometric, Real.cos_sub]
    ring
  have hp : l (curve a) = 1 := by simp [hl]
  have hbound : ∀ w ∈ states, w = curve a ∨ l w < l (curve a) := by
    apply unique_support_hull l
    rintro _ ⟨θ, rfl⟩
    by_cases he : Real.cos (θ - a) = 1
    · exact Or.inl (curve_eq_of_cos_sub he)
    · right
      rw [hl, hp]
      exact lt_of_le_of_ne (Real.cos_le_one _) he
  refine ⟨curve_mem a, ?_⟩
  intro w hw z hz hseg
  by_contra hne
  have hwlt := (hbound w hw).resolve_left hne
  have hzle : l z ≤ l (curve a) := by
    rcases hbound z hz with rfl | hzlt
    · exact le_rfl
    · exact hzlt.le
  obtain ⟨r, s, hr, hs, hrs, he⟩ := hseg
  have he' := congrArg l he
  simp only [map_add, map_smul, smul_eq_mul] at he'
  nlinarith [mul_pos hr (sub_pos.mpr hwlt), mul_nonneg hs.le (sub_nonneg.mpr hzle)]

private theorem original_pure : pure cone unit = range curve := by
  rw [CircuitBalancedConfirmation.pure, original_base]
  apply Subset.antisymm (extremePoints_convexHull_subset (𝕜 := ℝ))
  rintro _ ⟨a, rfl⟩
  exact curve_extreme a

def pairSupport (a b : ℝ) : Carrier →ₗ[ℝ] ℝ :=
  effect (1 + Real.cos (a - b) / 2)
    ![-Real.cos a - Real.cos b, -Real.sin a - Real.sin b,
      Real.cos (a + b) / 2, Real.sin (a + b) / 2]

private theorem pair_support_formula (a b θ : ℝ) :
    pairSupport a b (curve θ) = (1 - Real.cos (θ - a)) * (1 - Real.cos (θ - b)) := by
  rw [pairSupport, effect_curve]
  simp only [trigonometric, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Matrix.head_cons, Real.cos_sub, Real.cos_add, Real.sin_add,
    Real.cos_two_mul, Real.sin_two_mul]
  linear_combination -(Real.sin a * Real.sin b) * Real.sin_sq_add_cos_sq θ

private theorem pair_support_nonnegative (a b : ℝ) :
    ∀ w ∈ cone, 0 ≤ pairSupport a b w := by
  have hh : ∀ w ∈ states, 0 ≤ pairSupport a b w := by
    apply convexHull_min
    · rintro _ ⟨θ, rfl⟩
      change 0 ≤ pairSupport a b (curve θ)
      rw [pair_support_formula]
      exact mul_nonneg (sub_nonneg.mpr (Real.cos_le_one _))
        (sub_nonneg.mpr (Real.cos_le_one _))
    · exact (convex_Ici (0 : ℝ)).is_linear_preimage (pairSupport a b).isLinear
  rintro _ ⟨t, ht, w, hw, rfl⟩
  simpa only [map_smul, smul_eq_mul] using mul_nonneg ht (hh w hw)

private theorem zero_hull_face {S Z : Set Carrier} (g : Carrier →ₗ[ℝ] ℝ)
    (hZ : Convex ℝ Z) (hz : ∀ w ∈ Z, g w = 0)
    (hS : ∀ w ∈ S, w ∈ Z ∨ 0 < g w) :
    ∀ w ∈ convexHull ℝ S, g w = 0 → w ∈ Z := by
  have hh : convexHull ℝ S ⊆ {w | w ∈ Z ∨ 0 < g w} := by
    apply convexHull_min hS
    intro w hw z hz' a b ha hb hab
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simpa [ha0, hb1] using hz'
    by_cases hb0 : b = 0
    · have ha1 : a = 1 := by linarith
      simpa [hb0, ha1] using hw
    have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    rcases hw with hw | hw <;> rcases hz' with hz' | hz'
    · exact Or.inl (hZ hw hz' ha hb hab)
    · right
      simp only [map_add, map_smul, smul_eq_mul, hz w hw, mul_zero, zero_add]
      exact mul_pos hb' hz'
    · right
      simp only [map_add, map_smul, smul_eq_mul, hz z hz', mul_zero, add_zero]
      exact mul_pos ha' hw
    · right
      simp only [map_add, map_smul, smul_eq_mul]
      exact add_pos (mul_pos ha' hw) (mul_pos hb' hz')
  intro w hw hgw
  exact (hh hw).resolve_right (by rw [hgw]; exact lt_irrefl _)

private theorem whole_zero_face (a b : ℝ) :
    {w ∈ base cone unit | pairSupport a b w = 0} = segment ℝ (curve a) (curve b) := by
  have hza : pairSupport a b (curve a) = 0 := by simp [pair_support_formula]
  have hzb : pairSupport a b (curve b) = 0 := by simp [pair_support_formula]
  have hseg : ∀ w ∈ segment ℝ (curve a) (curve b), pairSupport a b w = 0 := by
    rintro _ ⟨r, s, hr, hs, hrs, rfl⟩
    simp [map_add, map_smul, hza, hzb]
  ext w
  constructor
  · rintro ⟨hw, hzero⟩
    rw [original_base] at hw
    apply zero_hull_face (pairSupport a b) (convex_segment _ _) hseg _ w hw hzero
    rintro _ ⟨θ, rfl⟩
    by_cases h : pairSupport a b (curve θ) = 0
    · rw [pair_support_formula] at h
      rcases mul_eq_zero.mp h with ha | hb
      · left
        rw [curve_eq_of_cos_sub (by linarith : Real.cos (θ - a) = 1)]
        exact left_mem_segment ℝ _ _
      · left
        rw [curve_eq_of_cos_sub (by linarith : Real.cos (θ - b) = 1)]
        exact right_mem_segment ℝ _ _
    · exact Or.inr (lt_of_le_of_ne
        (pair_support_nonnegative a b _ (states_mem_cone (curve_mem θ))) (Ne.symm h))
  · intro hw
    refine ⟨?_, hseg w hw⟩
    rw [original_base]
    exact (convex_convexHull ℝ (range curve)).segment_subset (curve_mem a) (curve_mem b) hw

private theorem entire_pair_base (a b : ℝ) :
    pairBase cone unit (curve a) (curve b) = segment ℝ (curve a) (curve b) := by
  let g := pairSupport a b
  let F : cone.Face := {
    toSubmodule := cone ⊓ PointedCone.ofSubmodule (LinearMap.ker g)
    isFaceOf := {
      le := inf_le_left
      mem_of_smul_add_mem := by
        intro v w r hv hw hr hvw
        refine ⟨hv, ?_⟩
        have he : r * g v + g w = 0 := by
          have he' : g (r • v + w) = 0 := hvw.2
          simpa only [map_add, map_smul, smul_eq_mul] using he'
        have hv0 := pair_support_nonnegative a b v hv
        have hw0 := pair_support_nonnegative a b w hw
        change g v = 0
        nlinarith } }
  have ha : curve a ∈ F := ⟨states_mem_cone (curve_mem a), by simp [g, pair_support_formula]⟩
  have hb : curve b ∈ F := ⟨states_mem_cone (curve_mem b), by simp [g, pair_support_formula]⟩
  ext w
  constructor
  · intro hw
    rw [← whole_zero_face]
    exact ⟨hw.1, (hw.2 F ha hb).2⟩
  · intro hw
    refine ⟨?_, fun G hGa hGb => ?_⟩
    · rw [original_base]
      exact (convex_convexHull ℝ (range curve)).segment_subset (curve_mem a) (curve_mem b) hw
    · exact (G.toPointedCone.convex).segment_subset hGa hGb hw

private theorem one_axis_norm (v : EuclideanSpace ℝ (Fin 1)) : ‖v‖ = |v 0| := by
  rw [EuclideanSpace.norm_eq]
  simp [Real.sqrt_sq_eq_abs]

private def segmentChart (a b : ℝ) (hab : curve a ≠ curve b) :
    BallChart cone unit (curve a) (curve b) where
  dim := 1
  dim_pos := by decide
  param := (AffineMap.lineMap (curve b) (curve a)).comp
    ((1 / 2 : ℝ) • (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0).toAffineMap +
      AffineMap.const ℝ (EuclideanSpace ℝ (Fin 1)) (1 / 2 : ℝ))
  injective := by
    intro v w he
    have hh := AffineMap.lineMap_injective ℝ (Ne.symm hab) he
    apply PiLp.ext
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change (1 / 2 : ℝ) * v 0 + 1 / 2 = (1 / 2 : ℝ) * w 0 + 1 / 2 at hh
    linarith
  whole := by
    rw [entire_pair_base, segment_symm, segment_eq_image_lineMap]
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨(1 / 2 : ℝ) * v 0 + 1 / 2, ?_, rfl⟩
      have hv' : |v 0| ≤ 1 := by simpa [one_axis_norm] using hv
      constructor <;> linarith [(abs_le.mp hv').1, (abs_le.mp hv').2]
    · rintro ⟨t, ht, rfl⟩
      refine ⟨WithLp.toLp 2 (fun _ : Fin 1 => 2 * t - 1), ?_, ?_⟩
      · simp only [Metric.mem_closedBall, dist_zero_right, one_axis_norm]
        change |2 * t - 1| ≤ 1
        exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      · change AffineMap.lineMap (curve b) (curve a) ((1 / 2 : ℝ) * (2 * t - 1) + 1 / 2) = _
        congr 1
        ring

private theorem original_B : wholePairBalls cone unit := by
  intro p q hpq
  have hp : (p : Carrier) ∈ range curve := by rw [← original_pure]; exact p.property
  have hq : (q : Carrier) ∈ range curve := by rw [← original_pure]; exact q.property
  obtain ⟨a, ha⟩ := hp
  obtain ⟨b, hb⟩ := hq
  have hab : curve a ≠ curve b := by
    intro he
    exact hpq (Subtype.ext (ha.symm.trans (he.trans hb)))
  rw [← ha, ← hb]
  exact ⟨segmentChart a b hab⟩

private theorem compact_hull {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {S : Set E} (hc : IsCompact S) (hne : S.Nonempty) :
    IsCompact (convexHull ℝ S) := by
  classical
  obtain ⟨s₀, hs₀⟩ := hne
  let n := Module.finrank ℝ E + 1
  let P : Set ((Fin n → ℝ) × (Fin n → E)) :=
    stdSimplex ℝ (Fin n) ×ˢ Set.pi univ (fun _ => S)
  let F : (Fin n → ℝ) × (Fin n → E) → E := fun p => ∑ i, p.1 i • p.2 i
  have hP : IsCompact P := (isCompact_stdSimplex ℝ _).prod
    (isCompact_univ_pi (fun _ => hc))
  have hF : Continuous F := by unfold F; fun_prop
  have heq : F '' P = convexHull ℝ S := by
    apply Subset.antisymm
    · rintro _ ⟨p, hp, rfl⟩
      exact mem_convexHull_of_exists_fintype p.1 p.2 hp.1.1 hp.1.2
        (fun i => hp.2 i (mem_univ i)) rfl
    · intro x hx
      rw [convexHull_eq_union] at hx
      simp only [mem_iUnion] at hx
      obtain ⟨t, ht, hi, hx⟩ := hx
      obtain ⟨w, hw, hw₁, hwx⟩ := Finset.mem_convexHull'.mp hx
      have hcard : Fintype.card t ≤ Fintype.card (Fin n) := by
        simpa [n] using hi.card_le_finrank_succ.trans
          (Nat.add_le_add_right (Submodule.finrank_le _) 1)
      obtain ⟨e : t ↪ Fin n⟩ := Function.Embedding.nonempty_of_card_le hcard
      let w' := Function.extend e (fun i : t => w i) 0
      let z' := Function.extend e (fun i : t => (i : E)) (fun _ => s₀)
      refine ⟨(w', z'), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · intro j
        by_cases hj : ∃ i, e i = j
        · obtain ⟨i, rfl⟩ := hj
          simpa [w', e.injective.extend_apply] using hw i i.property
        · simp [w', Function.extend_apply' _ _ _ hj]
      · change (∑ j, Function.extend e (fun i : t => w i) 0 j) = 1
        rw [Finset.sum_extend_zero_of_injective _ e.injective (fun _ => Finset.mem_univ _)]
        simpa only [Finset.univ_eq_attach, Finset.sum_attach] using hw₁
      · intro j _
        by_cases hj : ∃ i, e i = j
        · obtain ⟨i, rfl⟩ := hj
          simpa [z', e.injective.extend_apply] using ht i.property
        · simpa [z', Function.extend_apply' _ _ _ hj] using hs₀
      · change (∑ j, w' j • z' j) = x
        rw [show (fun j => w' j • z' j) =
            Function.extend e (fun i : t => w i • (i : E)) 0 by
          funext j
          by_cases hj : ∃ i, e i = j
          · obtain ⟨i, rfl⟩ := hj
            simp [w', z', e.injective.extend_apply]
          · simp [w', z', Function.extend_apply' _ _ _ hj]]
        rw [Finset.sum_extend_zero_of_injective _ e.injective (fun _ => Finset.mem_univ _)]
        calc
          (∑ i : t, w i • (i : E)) = ∑ y ∈ t, w y • y :=
            Finset.sum_attach t (fun y => w y • y)
          _ = x := hwx
  rw [← heq]
  exact hP.image hF

private theorem continuous_momentCurve : Continuous momentCurve := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [momentCurve, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] <;> fun_prop

private theorem compact_body : IsCompact body := by
  have hp : Function.Periodic momentCurve (2 * Real.pi) := by
    intro θ
    ext i
    fin_cases i <;> simp [momentCurve, mul_add, Real.cos_add_two_pi,
      Real.sin_add_two_pi, show 2 * (2 * Real.pi) = 2 * Real.pi + 2 * Real.pi by ring,
      ← add_assoc]
  exact compact_hull (hp.compact_of_continuous (by positivity) continuous_momentCurve)
    (range_nonempty _)

private theorem compact_states : IsCompact states := by
  rw [states_image]
  exact compact_body.image lift.continuous_of_finiteDimensional

private theorem vanishing_effect (f : Carrier →ₗ[ℝ] ℝ)
    (hf : ∀ θ, f (curve θ) = 0) : f = 0 := by
  obtain ⟨a, b, rfl⟩ := all_linear_effects f
  have h₀ := hf 0
  have hπ := hf Real.pi
  have hplus := hf (Real.pi / 2)
  have hminus := hf (-Real.pi / 2)
  have h₄ := hf (Real.pi / 4)
  simp [effect_curve, trigonometric, neg_div] at h₀ hπ hplus hminus h₄
  have ha : a = 0 := by linarith
  have hb₀ : b 0 = 0 := by linarith
  have hb₁ : b 1 = 0 := by linarith
  have hb₂ : b 2 = 0 := by linarith
  have hb₃ : b 3 = 0 := by linarith
  have hb : b = 0 := by ext i; fin_cases i <;> assumption
  simp [ha, hb, effect]

private theorem span_curve : Submodule.span ℝ (range curve) = ⊤ := by
  by_contra h
  obtain ⟨f, hf, hker⟩ := (Submodule.span ℝ (range curve)).exists_le_ker_of_lt_top
    (lt_top_iff_ne_top.mpr h)
  exact hf (vanishing_effect f (fun θ => hker (Submodule.subset_span ⟨θ, rfl⟩)))

private theorem body_fullspan : affineSpan ℝ body = ⊤ := by
  have hzero : (0 : Coordinates) ∈ body := by
    apply mem_convexHull_of_exists_fintype (fun _ : Fin 4 => (1 / 4 : ℝ))
      ![momentCurve 0, momentCurve Real.pi, momentCurve (Real.pi / 2),
        momentCurve (-Real.pi / 2)]
    · intro _; norm_num
    · norm_num
    · intro i; fin_cases i <;> exact ⟨_, rfl⟩
    · ext i; fin_cases i <;> norm_num [Fin.sum_univ_succ, momentCurve, neg_div, Real.cos_two_mul]
  have hs : Submodule.span ℝ body = ⊤ := by
    by_contra h
    obtain ⟨f, hf, hker⟩ := (Submodule.span ℝ body).exists_le_ker_of_lt_top
      (lt_top_iff_ne_top.mpr h)
    have hz : f.comp (LinearMap.snd ℝ ℝ Coordinates) = 0 := by
      apply vanishing_effect
      intro θ
      exact hker (Submodule.subset_span (subset_convexHull ℝ _ ⟨θ, rfl⟩))
    apply hf
    apply LinearMap.ext
    intro w
    exact LinearMap.congr_fun hz (0, w)
  rw [affineSpan_eq_span_of_zero_mem (subset_affineSpan ℝ body hzero), hs]
  rfl

private theorem cone_generating : Submodule.span ℝ (cone : Set Carrier) = ⊤ :=
  top_unique (span_curve ▸ Submodule.span_mono (by
    rintro _ ⟨θ, rfl⟩; exact states_mem_cone (curve_mem θ)))

private theorem cone_salient : (cone : ConvexCone ℝ Carrier).Salient := by
  intro w hw hn hneg
  have h₁ := cone_strict hw hn
  have h₂ := cone_strict hneg (neg_ne_zero.mpr hn)
  rw [map_neg] at h₂
  linarith

private theorem cone_closed : IsClosed (cone : Set Carrier) := by
  rw [← isSeqClosed_iff_isClosed]
  intro v w hv hlim
  choose t ht z hz he using hv
  have htval (n) : t n = (v n).1 := by rw [he n]; simp [states_unit (hz n)]
  obtain ⟨z₀, hz₀, φ, hφ, hzl⟩ := compact_states.tendsto_subseq hz
  have htl : Filter.Tendsto (t ∘ φ) Filter.atTop (nhds w.1) := by
    simpa only [Function.comp_def, htval] using
      (continuous_fst.tendsto w).comp (hlim.comp hφ.tendsto_atTop)
  have ht₀ : 0 ≤ w.1 := ge_of_tendsto htl (Filter.Eventually.of_forall (fun n => ht (φ n)))
  refine ⟨w.1, ht₀, z₀, hz₀, ?_⟩
  apply tendsto_nhds_unique (hlim.comp hφ.tendsto_atTop)
  simpa only [Function.comp_def, he] using htl.smul hzl

def p : Carrier := curve 0
def x : Carrier := (1 / 2 : ℝ) • (curve (Real.pi / 2) + curve (-Real.pi / 2))
def y : Carrier := curve Real.pi
def mixed : Carrier := (1 / 2 : ℝ) • (x + y)
def angle : ℝ := Real.arccos (-2 / 3)
def z : Carrier := (1 / 2 : ℝ) • (curve angle + curve (-angle))
def attainer : Carrier →ₗ[ℝ] ℝ := effect (17 / 50) ![12 / 25, 0, 9 / 50, 0]

private theorem midpoint_mem {a b : Carrier} (ha : a ∈ states) (hb : b ∈ states) :
    (1 / 2 : ℝ) • (a + b) ∈ states := by
  simpa only [states, smul_add] using (convex_convexHull ℝ (range curve)) ha hb
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
      norm_num [mixed, x, y, p, z, curve, lift, momentCurve, neg_div, Real.cos_two_mul,
        Real.sin_two_mul, Real.cos_neg, Real.sin_neg, hc]

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
    norm_num [z, map_smul, map_add, attainer_formula, hc, Real.cos_neg]
  norm_num [hz]

private theorem universal_lower (f : Carrier →ₗ[ℝ] ℝ) (hf : confirms cone unit p f) :
    (1 / 10 : ℝ) ≤ f mixed := by
  have hpos := (hf.1 z (states_mem_cone state_members.2.2.2.2)).1
  rw [decomposition, map_add, map_smul, map_smul, hf.2]
  dsimp only [smul_eq_mul]
  linarith

private theorem endpoint_exclusions :
    (∃ f, confirms cone unit p f ∧ f x = 0) ∧
    (∃ f, confirms cone unit p f ∧ f y = 0) := by
  let fx := effect (1 / 2) ![0, 0, 1 / 2, 0]
  let fy := effect (1 / 2) ![1 / 2, 0, 0, 0]
  have hfx (θ : ℝ) : fx (curve θ) = Real.cos θ ^ 2 := by
    simp [fx, effect_curve, trigonometric, Real.cos_two_mul]
    ring
  have hfy (θ : ℝ) : fy (curve θ) = (1 + Real.cos θ) / 2 := by
    simp [fy, effect_curve, trigonometric]
    ring
  have hpx : proper cone unit fx := (proper_on_curve fx).mpr (fun θ => by
    rw [hfx]
    exact ⟨sq_nonneg _, by nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]⟩)
  have hpy : proper cone unit fy := (proper_on_curve fy).mpr (fun θ => by
    rw [hfy]
    constructor <;> linarith [Real.neg_one_le_cos θ, Real.cos_le_one θ])
  constructor
  · refine ⟨fx, ⟨hpx, ?_⟩, ?_⟩
    · norm_num [p, hfx]
    · norm_num [x, map_smul, map_add, hfx, neg_div]
  · refine ⟨fy, ⟨hpy, ?_⟩, ?_⟩
    · norm_num [p, hfy]
    · norm_num [y, hfy]

private theorem proper_coefficients {a : ℝ} {b : Coordinates}
    (hf : proper cone unit (effect a b)) : ∀ i, |b i| ≤ 4 := by
  have h := (proper_on_curve _).mp hf
  have hzero := h 0
  have hpi := h Real.pi
  have hplus := h (Real.pi / 2)
  have hminus := h (-Real.pi / 2)
  have hfour := h (Real.pi / 4)
  simp [effect_curve, trigonometric, neg_div, Real.cos_two_mul, Real.sin_two_mul] at
    hzero hpi hplus hminus hfour
  have ha : -1 ≤ a ∧ a ≤ 1 := by constructor <;> linarith
  have hb0 : -1 ≤ b 0 ∧ b 0 ≤ 1 := by constructor <;> linarith
  have hb1 : -1 ≤ b 1 ∧ b 1 ≤ 1 := by constructor <;> linarith
  have hb2 : -1 ≤ b 2 ∧ b 2 ≤ 1 := by constructor <;> linarith
  have hr : 0 ≤ Real.sqrt 2 / 2 ∧ Real.sqrt 2 / 2 ≤ 1 := by
    constructor <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hprod0 : -1 ≤ b 0 * (Real.sqrt 2 / 2) ∧ b 0 * (Real.sqrt 2 / 2) ≤ 1 := by
    constructor <;> nlinarith [mul_nonneg (by linarith : 0 ≤ b 0 + 1) hr.1,
      mul_nonneg (by linarith : 0 ≤ 1 - b 0) hr.1]
  have hprod1 : -1 ≤ b 1 * (Real.sqrt 2 / 2) ∧ b 1 * (Real.sqrt 2 / 2) ≤ 1 := by
    constructor <;> nlinarith [mul_nonneg (by linarith : 0 ≤ b 1 + 1) hr.1,
      mul_nonneg (by linarith : 0 ≤ 1 - b 1) hr.1]
  intro i
  fin_cases i <;> apply abs_le.mpr <;> constructor <;> nlinarith

private def variation (θ : ℝ) : ℝ := ∑ i : Fin 4, |momentCurve θ i - momentCurve 0 i|

private theorem uniform_effect_variation {f : Carrier →ₗ[ℝ] ℝ}
    (hf : proper cone unit f) (θ : ℝ) :
    |f (curve θ) - f (curve 0)| ≤ 4 * variation θ := by
  obtain ⟨a, b, rfl⟩ := all_linear_effects f
  have hb := proper_coefficients hf
  have he : effect a b (curve θ) - effect a b (curve 0) =
      ∑ i : Fin 4, b i * (momentCurve θ i - momentCurve 0 i) := by
    simp [effect, curve, lift, Fin.sum_univ_succ]
    ring
  rw [he]
  calc
    |∑ i, b i * (momentCurve θ i - momentCurve 0 i)| ≤
        ∑ i, |b i * (momentCurve θ i - momentCurve 0 i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, 4 * |momentCurve θ i - momentCurve 0 i| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hb i) (abs_nonneg _)
    _ = 4 * variation θ := (Finset.mul_sum _ _ _).symm

private theorem original_A_fails : ¬ allAntipodes cone unit := by
  have hc : Continuous variation := by
    unfold variation
    apply continuous_finsetSum
    intro i _
    exact (((continuous_apply i).comp continuous_momentCurve).sub continuous_const).abs
  obtain ⟨r, hr, hbound⟩ := Metric.continuousAt_iff.mp (hc.continuousAt (x := 0))
    (1 / 4) (by norm_num)
  let θ := min (r / 2) (Real.pi / 2)
  have hθpos : 0 < θ := lt_min (by linarith) (by positivity)
  have hθr : θ < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hθpi : θ ≤ Real.pi := (min_le_right _ _).trans (by linarith [Real.pi_pos])
  have hv : variation θ < 1 / 4 := by
    have hh := hbound (by simpa [Real.dist_eq, abs_of_pos hθpos] using hθr)
    simpa [variation, Real.dist_eq, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))] using hh
  have hne : curve 0 ≠ curve θ := by
    intro he
    have hh := congrArg (fun w : Carrier => w.2 0) he
    have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0 : ℝ) ≤ 0) hθpi hθpos
    simp [curve, lift, momentCurve] at hh
    simp only [Real.cos_zero] at hcos
    linarith
  let pp : pure cone unit := ⟨curve 0, by rw [original_pure]; exact ⟨0, rfl⟩⟩
  let qq : pure cone unit := ⟨curve θ, by rw [original_pure]; exact ⟨θ, rfl⟩⟩
  let chart := segmentChart 0 θ hne
  let n : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ => 1)
  have hn : ‖n‖ = 1 := by simp [one_axis_norm, n]
  have hleft : chart.param n = curve 0 := by
    change AffineMap.lineMap (curve θ) (curve 0) ((1 / 2 : ℝ) * 1 + 1 / 2) = _
    norm_num
  have hright : chart.param (-n) = curve θ := by
    change AffineMap.lineMap (curve θ) (curve 0) ((1 / 2 : ℝ) * (-1) + 1 / 2) = _
    norm_num
  intro hA
  have hh := hA pp qq (fun he => hne (Subtype.ext_iff.mp he)) chart n hn
    (hleft ▸ pp.property)
  rw [hleft, hright] at hh
  obtain ⟨f, hf, hzero⟩ := hh
  have hu := uniform_effect_variation hf.1 θ
  rw [hf.2, hzero] at hu
  norm_num at hu
  linarith

private theorem zero_gluing_fails : ¬ zeroGluing cone unit := by
  intro h
  have hp : p ∈ pure cone unit := by rw [original_pure]; exact ⟨0, rfl⟩
  have hx : x ∈ base cone unit := by rw [original_base]; exact state_members.2.1
  have hy : y ∈ base cone unit := by rw [original_base]; exact state_members.2.2.1
  obtain ⟨f, hf, hz⟩ := h ⟨p, hp⟩ x y hx hy endpoint_exclusions.1 endpoint_exclusions.2
  have hb := universal_lower f hf
  change f mixed = 0 at hz
  rw [hz] at hb
  norm_num at hb

/-- The minimum is over every original globally proper real-linear confirmer.
The coefficient description is surjective onto all such effects. -/
theorem attained_full_effect_gap :
    base cone unit = lift '' body ∧
    pure cone unit = range curve ∧
    IsCompact body ∧ affineSpan ℝ body = ⊤ ∧
    IsClosed (cone : Set Carrier) ∧ (cone : ConvexCone ℝ Carrier).Salient ∧
    Submodule.span ℝ (cone : Set Carrier) = ⊤ ∧
    (∀ a b : ℝ, {w ∈ base cone unit | pairSupport a b w = 0} =
      segment ℝ (curve a) (curve b)) ∧
    (∀ a b : ℝ, pairBase cone unit (curve a) (curve b) =
      segment ℝ (curve a) (curve b)) ∧
    wholePairBalls cone unit ∧ ¬ allAntipodes cone unit ∧
    (∀ f : Carrier →ₗ[ℝ] ℝ, ∃ a b, f = effect a b) ∧
    (∀ a b, proper cone unit (effect a b) ↔
      ∀ θ : ℝ, 0 ≤ trigonometric a b θ ∧ trigonometric a b θ ≤ 1) ∧
    (∀ w ∈ cone, w ≠ 0 → 0 < unit w) ∧
    p ∈ base cone unit ∧ x ∈ base cone unit ∧ y ∈ base cone unit ∧
    mixed ∈ base cone unit ∧ z ∈ base cone unit ∧
    (∀ f, confirms cone unit p f → (1 / 10 : ℝ) ≤ f mixed) ∧
    confirms cone unit p attainer ∧ attainer mixed = 1 / 10 ∧
    comparison cone unit p mixed = 1 / 10 ∧
    (∃ f, confirms cone unit p f ∧ f x = 0) ∧
    (∃ f, confirms cone unit p f ∧ f y = 0) ∧ ¬ zeroGluing cone unit := by
  refine ⟨original_base.trans states_image, original_pure, compact_body, body_fullspan,
    cone_closed, cone_salient, cone_generating, whole_zero_face,
    entire_pair_base, original_B, original_A_fails, all_linear_effects, ?_,
    fun _ hw hn => cone_strict hw hn, ?_, ?_, ?_, ?_, ?_, universal_lower,
    attainer_confirms, attainer_value, ?_, endpoint_exclusions.1,
    endpoint_exclusions.2, zero_gluing_fails⟩
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
