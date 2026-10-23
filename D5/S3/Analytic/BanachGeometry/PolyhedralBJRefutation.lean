/- GID: D5/S3/Analytic/BanachGeometry/PolyhedralBJRefutation
   generality: G
   mirror-B: D5/B/S3/Analytic/BanachGeometry/PolyhedralBJRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/BanachGeometry/PolyhedralBJRefutation.claim; result=D5/S3/Analytic/BanachGeometry/PolyhedralBJRefutation.result; claim=D5/S3/Analytic/BanachGeometry/PolyhedralBJRefutation.claim
   digest: Two independent extreme-point tests do not force a scalar isometry in a polyhedral Banach plane. -/

/- Source: Manna–Mandal–Paul–Sain, arXiv:2511.20345v1, final Open Question.
   admission_basis: open-problem-resolution
   preregistration: https://github.com/the-omega-institute/trureturing/issues/19309
   The ordinary counterexample predates this native-implementation registration.
   Reuse: LinfKNumber.BJOrth, PreservesBJAt, active_not_BJ;
     native Submodule normed-space instances, finite-dimensional completeness
     and continuity, Basis.finTwoProd, mem_extremePoints_iff_left.
   Definitions and live consumers:
     fieldClaim -> claim; claim -> result; facetPlane -> Plane;
     Plane -> point, coordinates, operator, result;
     point -> coordinates, operator_point, norm_point, selected_extreme,
       extreme_finite, preserves_first, preserves_second, not_scalar_isometry;
     coordinates -> dimension, operator, selected_extreme, result;
     coordinateOperator -> operator; operator -> preserves_first,
       preserves_second, not_scalar_isometry, result.
   Per-lemma proof_shape and live consumers:
     plane_relation: bind-only; coordinates, extreme_finite, selected_extreme
     dimension: bind-only; result
     norm_point: bind-only; preserves_first, preserves_second,
       selected_extreme, not_scalar_isometry, result
     ball_iff: bind-only; not_extreme_of_tangent, extreme_finite, selected_extreme
     operator_point: bind-only; preserves_first, preserves_second, not_scalar_isometry
     not_extreme_of_tangent: content; two_active
     two_active: content; extreme_finite
     extreme_finite: content; result
     saturated: bind-only; selected_extreme
     selected_extreme: bind-only; result
     product_of_bj: bind-only; preserves_first, preserves_second
     bj_of_product: bind-only; preserves_first, preserves_second
     preserves_first: bind-only; result
     preserves_second: bind-only; result
     not_scalar_isometry: bind-only; result
     result: content; designated external open-question refutation.
   The geometric content constructs feasible symmetric tangent segments and
   restricts actual extreme points to a finite set. Every helper is consumed.
   No classification, complex counterexample or priority assertion is made. -/

import D5.S3.Analytic.BanachGeometry.LinfKNumber
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.Tactic.FinCases

/-! # A polyhedral counterexample to independent extreme-point tests -/

noncomputable section
open Set Module
namespace D5.S3.Analytic.BanachGeometry.PolyhedralBJRefutation
open LinfKNumber (BJOrth PreservesBJAt active_not_BJ)

/-- The source assertion for one of its two scalar fields. Convex extremality is real. -/
def fieldClaim (𝕜 : Type) [RCLike 𝕜] : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] [FiniteDimensional 𝕜 E],
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    ∀ (n : ℕ), Module.finrank 𝕜 E = n →
      ((Metric.closedBall (0 : E) 1).extremePoints ℝ).Finite →
      ∀ (v : Fin n → E), LinearIndependent 𝕜 v →
        (∀ i, v i ∈ (Metric.closedBall (0 : E) 1).extremePoints ℝ ∧ ‖v i‖ = 1) →
        ∀ T : E →L[𝕜] E,
          (∀ i y, (∀ t : 𝕜, ‖v i‖ ≤ ‖v i + t • y‖) →
            ∀ t : 𝕜, ‖T (v i)‖ ≤ ‖T (v i) + t • T y‖) →
          ∃ (c : 𝕜) (U : E →ₗᵢ[𝕜] E), T = c • U.toContinuousLinearMap

/-- The complete real-or-complex universal question of arXiv:2511.20345v1. -/
def claim : Prop := fieldClaim ℝ ∧ fieldClaim ℂ

/-- The plane section carrying the three facet readings. -/
def facetPlane : Submodule ℝ (Fin 3 → ℝ) where
  carrier := {w | w 2 = w 1 - w 0 / 2}
  zero_mem' := by simp
  add_mem' := by intro u v hu hv; simp only [mem_ofPred_eq, Pi.add_apply] at *; linarith
  smul_mem' := by
    intro c v hv
    simp only [mem_ofPred_eq, Pi.smul_apply, smul_eq_mul] at *
    rw [hv]; ring

abbrev Plane := facetPlane

/-- Coordinates in the Banach plane: the inherited norm is max(|a|,|a + b|,|a / 2 + b|). -/
def point (a b : ℝ) : Plane :=
  ⟨![a, a + b, a / 2 + b], by change a / 2 + b = a + b - a / 2; ring⟩

private lemma plane_relation (w : Plane) : w.val 2 = w.val 1 - w.val 0 / 2 := w.property

/-- Algebraic coordinates, without identifying the norm with the usual product norm. -/
def coordinates : (ℝ × ℝ) ≃ₗ[ℝ] Plane where
  toFun z := point z.1 z.2
  invFun w := (w.val 0, w.val 1 - w.val 0)
  left_inv := by intro z; ext <;> simp [point]
  right_inv := by
    intro w
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [point]; linarith [plane_relation w]
  map_add' := by intro x y; apply Subtype.ext; funext i; fin_cases i <;> simp [point] <;> ring
  map_smul' := by intro c x; apply Subtype.ext; funext i; fin_cases i <;> simp [point] <;> ring

instance : CompleteSpace Plane := FiniteDimensional.complete ℝ Plane

private lemma dimension : Module.finrank ℝ Plane = 2 := by
  rw [← coordinates.finrank_eq]
  simp [Module.finrank_prod]

private lemma norm_point (a b : ℝ) :
    ‖point a b‖ = max (max |a| |a + b|) |a / 2 + b| := by
  change ‖(![a, a + b, a / 2 + b] : Fin 3 → ℝ)‖ = _
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    fin_cases i <;> simp only [Real.norm_eq_abs]
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
    · exact le_max_right _ _
  · apply max_le
    · apply max_le
      · simpa [Real.norm_eq_abs] using norm_le_pi_norm (![a, a + b, a / 2 + b] : Fin 3 → ℝ) 0
      · simpa [Real.norm_eq_abs] using norm_le_pi_norm (![a, a + b, a / 2 + b] : Fin 3 → ℝ) 1
    · simpa [Real.norm_eq_abs] using norm_le_pi_norm (![a, a + b, a / 2 + b] : Fin 3 → ℝ) 2

private lemma ball_iff (w : Plane) :
    w ∈ Metric.closedBall (0 : Plane) 1 ↔ ∀ i, |w.val i| ≤ 1 := by
  rw [Metric.mem_closedBall, dist_zero_right]
  change ‖w.val‖ ≤ 1 ↔ _
  simpa [Real.norm_eq_abs] using pi_norm_le_iff_of_nonneg (x := w.val) zero_le_one

private def coordinateOperator : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun z := (z.1 + z.2, -(3 / 2 : ℝ) * z.2)
  map_add' := by intro x y; ext <;> simp <;> ring
  map_smul' := by intro c x; ext <;> simp <;> ring

/-- The actual bounded endomorphism in facet coordinates. -/
def operator : Plane →L[ℝ] Plane := LinearMap.toContinuousLinearMap
  (coordinates.toLinearMap.comp (coordinateOperator.comp coordinates.symm.toLinearMap))

private lemma operator_point (a b : ℝ) :
    operator (point a b) = point (a + b) (-(3 / 2 : ℝ) * b) := by
  apply Subtype.ext
  funext i
  fin_cases i <;> simp [operator, coordinateOperator, coordinates, point]

private lemma not_extreme_of_tangent (w v : Plane) (hv : v ≠ 0)
    (hw : w ∈ Metric.closedBall (0 : Plane) 1)
    (ht : ∀ i, |w.val i| = 1 → v.val i = 0) :
    w ∉ (Metric.closedBall (0 : Plane) 1).extremePoints ℝ := by
  classical
  have hb := (ball_iff w).mp hw
  have local_bound (i : Fin 3) : ∃ e : ℝ, 0 < e ∧
      ∀ d : ℝ, |d| < e → |w.val i + d * v.val i| ≤ 1 := by
    by_cases hi : |w.val i| = 1
    · exact ⟨1, zero_lt_one, fun d _ => by simp [ht i hi, hi]⟩
    · have hs : 0 < 1 - |w.val i| := sub_pos.mpr (lt_of_le_of_ne (hb i) hi)
      refine ⟨(1 - |w.val i|) / (|v.val i| + 1), div_pos hs (by positivity), ?_⟩
      intro d hd
      have hm := (lt_div_iff₀ (by positivity : 0 < |v.val i| + 1)).mp hd
      calc
        |w.val i + d * v.val i| ≤ |w.val i| + |d * v.val i| := abs_add_le _ _
        _ = |w.val i| + |d| * |v.val i| := by rw [abs_mul]
        _ ≤ 1 := by nlinarith [abs_nonneg d]
  choose e he hbnd using local_bound
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ e Finset.univ_nonempty
  let d := e j / 2
  have hd : 0 < d := by dsimp [d]; linarith [he j]
  have hsmall (i : Fin 3) : |d| < e i ∧ |-d| < e i := by
    rw [abs_of_pos hd, abs_neg, abs_of_pos hd]
    have := hj i (Finset.mem_univ i)
    dsimp [d]; constructor <;> linarith [he j]
  have hplus : w + d • v ∈ Metric.closedBall (0 : Plane) 1 := by
    apply (ball_iff _).mpr
    intro i
    exact hbnd i d (hsmall i).1
  have hminus : w - d • v ∈ Metric.closedBall (0 : Plane) 1 := by
    apply (ball_iff _).mpr
    intro i
    simpa [sub_eq_add_neg] using hbnd i (-d) (hsmall i).2
  intro hx
  have h := (mem_extremePoints_iff_left.mp hx).2 _ hplus _ hminus
    (mem_openSegment_add_sub (𝕜 := ℝ) w (d • v))
  have hz : d • v = 0 := add_left_cancel (h.trans (add_zero w).symm)
  exact hv ((smul_eq_zero.mp hz).resolve_left hd.ne')

private lemma two_active (w : Plane)
    (hw : w ∈ (Metric.closedBall (0 : Plane) 1).extremePoints ℝ) :
    (|w.val 0| = 1 ∧ |w.val 1| = 1) ∨
    (|w.val 0| = 1 ∧ |w.val 2| = 1) ∨
    (|w.val 1| = 1 ∧ |w.val 2| = 1) := by
  by_cases h0 : |w.val 0| = 1
  · by_cases h1 : |w.val 1| = 1
    · exact Or.inl ⟨h0, h1⟩
    · by_cases h2 : |w.val 2| = 1
      · exact Or.inr (Or.inl ⟨h0, h2⟩)
      · exfalso
        apply not_extreme_of_tangent w (point 0 1) (by
          intro h; have := congrArg (fun z : Plane => z.val 1) h; norm_num [point] at this)
          hw.1 _ hw
        intro i hi
        fin_cases i <;> simp_all [point]
  · by_cases h1 : |w.val 1| = 1
    · by_cases h2 : |w.val 2| = 1
      · exact Or.inr (Or.inr ⟨h1, h2⟩)
      · exfalso
        apply not_extreme_of_tangent w (point 1 (-1)) (by
          intro h; have := congrArg (fun z : Plane => z.val 0) h; norm_num [point] at this)
          hw.1 _ hw
        intro i hi
        fin_cases i <;> simp_all [point]
    · exfalso
      apply not_extreme_of_tangent w (point 2 (-1)) (by
        intro h; have := congrArg (fun z : Plane => z.val 0) h; norm_num [point] at this)
        hw.1 _ hw
      intro i hi
      fin_cases i <;> simp_all [point]

private lemma extreme_finite :
    ((Metric.closedBall (0 : Plane) 1).extremePoints ℝ).Finite := by
  have hsub : (Metric.closedBall (0 : Plane) 1).extremePoints ℝ ⊆
      {point 1 0, point (-1) 0, point 0 1, point 0 (-1),
        point (-1) (3 / 2), point 1 (-(3 / 2))} := by
    intro w hw
    have hr := plane_relation w
    have hb := (ball_iff w).mp hw.1
    have h0 := abs_le.mp (hb 0)
    have h1 := abs_le.mp (hb 1)
    have h2 := abs_le.mp (hb 2)
    rcases two_active w hw with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    all_goals
      rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp ha with ha | ha <;>
        rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hb with hb | hb
    all_goals
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      first
      | left; apply Subtype.ext; funext i; fin_cases i <;> simp [point] <;> linarith
      | right; left; apply Subtype.ext; funext i; fin_cases i <;> simp [point] <;> linarith
      | right; right; left; apply Subtype.ext; funext i; fin_cases i <;> simp [point] <;> linarith
      | right; right; right; left; apply Subtype.ext; funext i; fin_cases i <;>
          simp [point] <;> linarith
      | right; right; right; right; left; apply Subtype.ext; funext i; fin_cases i <;>
          simp [point] <;> linarith
      | right; right; right; right; right; apply Subtype.ext; funext i; fin_cases i <;>
          simp [point] <;> linarith
  exact (Set.toFinite _).subset hsub

private lemma saturated (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) (hc : c ≤ 1) (hd : d ≤ 1) (h : a * c + b * d = 1) : c = 1 := by
  by_contra hn
  have hpos := mul_pos ha (sub_pos.mpr (lt_of_le_of_ne hc hn))
  have hnonneg := mul_nonneg hb.le (sub_nonneg.mpr hd)
  nlinarith

private lemma selected_extreme (k : Fin 2) :
    coordinates (Basis.finTwoProd ℝ k) ∈
      (Metric.closedBall (0 : Plane) 1).extremePoints ℝ := by
  have proof (a b : ℝ) (hpt : (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1)) :
      point a b ∈ (Metric.closedBall (0 : Plane) 1).extremePoints ℝ := by
    rcases hpt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals
      apply mem_extremePoints_iff_left.mpr
      refine ⟨?_, ?_⟩
    any_goals
      rw [Metric.mem_closedBall, dist_zero_right, norm_point]; norm_num
    all_goals
      intro u hu v hv hs
      rcases hs with ⟨a, b, ha, hb, hab, heq⟩
      have bu := (ball_iff u).mp hu
      have bv := (ball_iff v).mp hv
      have eqn (i : Fin 3) := congrArg (fun z : Plane => z.val i) heq
      simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] at eqn
    · have e0 : u.val 0 = 1 := saturated a b _ _ ha hb hab
        (abs_le.mp (bu 0)).2 (abs_le.mp (bv 0)).2 (by simpa [point] using eqn 0)
      have e1 : u.val 1 = 1 := saturated a b _ _ ha hb hab
        (abs_le.mp (bu 1)).2 (abs_le.mp (bv 1)).2 (by simpa [point] using eqn 1)
      apply Subtype.ext; funext i
      fin_cases i <;> simp [point] <;> linarith [plane_relation u]
    · have e1 : u.val 1 = 1 := saturated a b _ _ ha hb hab
        (abs_le.mp (bu 1)).2 (abs_le.mp (bv 1)).2 (by simpa [point] using eqn 1)
      have e2 : u.val 2 = 1 := saturated a b _ _ ha hb hab
        (abs_le.mp (bu 2)).2 (abs_le.mp (bv 2)).2 (by simpa [point] using eqn 2)
      apply Subtype.ext; funext i
      fin_cases i <;> simp [point] <;> linarith [plane_relation u]
  fin_cases k
  · change coordinates (Basis.finTwoProd ℝ 0) ∈ _
    rw [Basis.finTwoProd_zero]
    exact proof 1 0 (Or.inl ⟨rfl, rfl⟩)
  · change coordinates (Basis.finTwoProd ℝ 1) ∈ _
    rw [Basis.finTwoProd_one]
    exact proof 0 1 (Or.inr ⟨rfl, rfl⟩)

private lemma product_of_bj (w z : Plane) (hw : ‖w‖ = 1) (i j : Fin 3)
    (hactive : ∀ k, |w.val k| = 1 → k = i ∨ k = j) (h : BJOrth w z) :
    (z.val i * w.val i) * (z.val j * w.val j) ≤ 0 := by
  by_contra hn
  have hp : 0 < (z.val i * w.val i) * (z.val j * w.val j) := lt_of_not_ge hn
  have hw0 : w.val ≠ 0 := by
    intro heq
    have : ‖w‖ = 0 := by change ‖w.val‖ = 0; rw [heq, norm_zero]
    linarith
  rcases mul_pos_iff.mp hp with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · apply active_not_BJ hw0 _ h
    intro k hk
    have hk' : |w.val k| = 1 := by simpa only [Submodule.norm_coe, hw] using hk
    rcases hactive k hk' with rfl | rfl
    · exact hi
    · exact hj
  · have hneg : BJOrth w.val (-z.val) := by
      intro t
      change ‖w‖ ≤ ‖w + t • (-z)‖
      simpa only [smul_neg, neg_smul] using h (-t)
    apply active_not_BJ hw0 _ hneg
    intro k hk
    have hk' : |w.val k| = 1 := by simpa only [Submodule.norm_coe, hw] using hk
    rcases hactive k hk' with rfl | rfl
    · simpa only [Pi.neg_apply, neg_mul] using neg_pos.mpr hi
    · simpa only [Pi.neg_apply, neg_mul] using neg_pos.mpr hj

private lemma bj_of_product (w z : Plane) (hw : ‖w‖ = 1) (i j : Fin 3)
    (hi : |w.val i| = 1) (hj : |w.val j| = 1)
    (hp : (z.val i * w.val i) * (z.val j * w.val j) ≤ 0) : BJOrth w z := by
  intro t
  rw [hw]
  have lower (k : Fin 3) (hk : |w.val k| = 1)
      (hs : 0 ≤ t * (z.val k * w.val k)) : 1 ≤ ‖w + t • z‖ := by
    have hcoord : 1 ≤ |w.val k + t * z.val k| := by
      rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hk with hk | hk
      · rw [hk] at hs ⊢
        calc
          1 ≤ 1 + t * z.val k := by nlinarith
          _ ≤ |1 + t * z.val k| := le_abs_self _
      · rw [hk] at hs ⊢
        calc
          1 ≤ -(-1 + t * z.val k) := by nlinarith
          _ ≤ |-1 + t * z.val k| := neg_le_abs _
    exact hcoord.trans (by simpa [Real.norm_eq_abs] using
        (norm_le_pi_norm ((w + t • z).val) k))
  rcases mul_nonpos_iff.mp hp with ⟨hzi, hzj⟩ | ⟨hzi, hzj⟩
  · by_cases ht : 0 ≤ t
    · exact lower i hi (mul_nonneg ht hzi)
    · exact lower j hj (mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge ht) hzj)
  · by_cases ht : 0 ≤ t
    · exact lower j hj (mul_nonneg ht hzj)
    · exact lower i hi (mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge ht) hzi)

private lemma preserves_first : PreservesBJAt operator.toLinearMap (point 1 0) := by
  intro y hy
  obtain ⟨⟨a, b⟩, rfl⟩ := coordinates.surjective y
  have hp := product_of_bj (point 1 0) (point a b) (by rw [norm_point]; norm_num) 0 1
    (by intro k hk; fin_cases k <;> norm_num [point] at *) hy
  simp [point] at hp
  change BJOrth (operator (point 1 0)) (operator (point a b))
  rw [operator_point, operator_point]
  norm_num
  apply bj_of_product _ _ (by rw [norm_point]; norm_num) 0 1
    (by norm_num [point]) (by norm_num [point])
  simp only [point, Matrix.cons_val_zero, Matrix.cons_val_one]
  nlinarith [sq_nonneg (a + b)]

private lemma preserves_second : PreservesBJAt operator.toLinearMap (point 0 1) := by
  intro y hy
  obtain ⟨⟨a, b⟩, rfl⟩ := coordinates.surjective y
  have hp := product_of_bj (point 0 1) (point a b) (by rw [norm_point]; norm_num) 1 2
    (by intro k hk; fin_cases k <;> norm_num [point] at *) hy
  simp [point] at hp
  change BJOrth (operator (point 0 1)) (operator (point a b))
  rw [operator_point, operator_point]
  norm_num
  apply bj_of_product _ _ (by rw [norm_point]; norm_num) 0 2
    (by norm_num [point]) (by norm_num [point])
  simp only [point, Matrix.cons_val_zero, Matrix.cons_val]
  nlinarith [sq_nonneg (a + b)]

private lemma not_scalar_isometry :
    ¬ ∃ (c : ℝ) (U : Plane →ₗᵢ[ℝ] Plane), operator = c • U.toContinuousLinearMap := by
  rintro ⟨c, U, h⟩
  have hnorm (z : Plane) : ‖operator z‖ = |c| * ‖z‖ := by
    rw [h, smul_apply, norm_smul]
    change ‖c‖ * ‖U z‖ = _
    rw [U.norm_map, Real.norm_eq_abs]
  have hp := hnorm (point 1 0)
  have hr := hnorm (point (-1) (3 / 2))
  rw [operator_point, norm_point, norm_point] at hp hr
  norm_num at hp hr
  linarith

/-- The whole source assertion is false, witnessed by the complete real Banach plane above. -/
theorem result : ¬ claim := by
  intro h
  have hreal := h.1 Plane 2 dimension extreme_finite
    (fun i => coordinates (Basis.finTwoProd ℝ i))
    ((Basis.finTwoProd ℝ).map coordinates).linearIndependent
  have hpoints : ∀ i : Fin 2, coordinates (Basis.finTwoProd ℝ i) ∈
      (Metric.closedBall (0 : Plane) 1).extremePoints ℝ ∧
      ‖coordinates (Basis.finTwoProd ℝ i)‖ = 1 := by
    intro i
    refine ⟨selected_extreme i, ?_⟩
    fin_cases i
    · change ‖coordinates (Basis.finTwoProd ℝ 0)‖ = 1
      rw [Basis.finTwoProd_zero]
      change ‖point 1 0‖ = 1
      rw [norm_point]; norm_num
    · change ‖coordinates (Basis.finTwoProd ℝ 1)‖ = 1
      rw [Basis.finTwoProd_one]
      change ‖point 0 1‖ = 1
      rw [norm_point]; norm_num
  apply not_scalar_isometry
  apply hreal hpoints operator
  intro i
  fin_cases i
  · change PreservesBJAt operator.toLinearMap (coordinates (Basis.finTwoProd ℝ 0))
    rw [Basis.finTwoProd_zero]
    exact preserves_first
  · change PreservesBJAt operator.toLinearMap (coordinates (Basis.finTwoProd ℝ 1))
    rw [Basis.finTwoProd_one]
    exact preserves_second

#print axioms result

end D5.S3.Analytic.BanachGeometry.PolyhedralBJRefutation
