/- GID: D5/S3/Geometry/HyperbolicUpperHalfSpace
   generality: G
   mirror-B: D5/B/S3/Geometry/HyperbolicUpperHalfSpace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.UpperHalfPlane.Metric]
   utility: none
   digest: Hyperbolic upper half-space metric in arbitrary horizontal dimension. -/

import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Geometry.Euclidean.Inversion.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Geometry.HyperbolicUpperHalfSpace

variable (E : Type*)

/-- Euclidean ambient space with one distinguished height coordinate. -/
abbrev Ambient := WithLp 2 (E × ℝ)

/-- Points above the horizontal boundary plane. -/
abbrev UpperHalfSpace := {p : Ambient E // 0 < (WithLp.ofLp p).2}

variable {E}

/-- Positive height of an upper half-space point. -/
def height (p : UpperHalfSpace E) : ℝ := (WithLp.ofLp p.1).2

/-- Reflection in the horizontal boundary plane. -/
def reflect (p : Ambient E) : Ambient E :=
  WithLp.toLp 2 (p.fst, -p.snd)

variable [NormedAddCommGroup E]

theorem dist_reflect_sq (p q : Ambient E) :
    dist p (reflect q) ^ 2 = dist p q ^ 2 + 4 * p.snd * q.snd := by
  rw [WithLp.prod_dist_eq_of_L2, WithLp.prod_dist_eq_of_L2]
  dsimp [reflect]
  simp only [
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _)),
    Real.dist_eq, sq_abs]
  ring

theorem dist_self_reflect (p : UpperHalfSpace E) :
    dist (p.1 : Ambient E) (reflect p.1) = 2 * height p := by
  have hsq := dist_reflect_sq p.1 p.1
  simp only [dist_self] at hsq
  have hp : 0 < height p := p.2
  have hd : 0 ≤ dist (p.1 : Ambient E) (reflect p.1) := dist_nonneg
  dsimp [height] at *
  nlinarith

theorem dist_reflect_comm (p q : Ambient E) :
    dist p (reflect q) = dist q (reflect p) := by
  have hpq := dist_reflect_sq p q
  have hqp := dist_reflect_sq q p
  rw [dist_comm q p] at hqp
  have hp : 0 ≤ dist p (reflect q) := dist_nonneg
  have hq : 0 ≤ dist q (reflect p) := dist_nonneg
  nlinarith

/-- The standard curvature-minus-one distance formula, before proving its metric laws. -/
noncomputable def hyperbolicDist (p q : UpperHalfSpace E) : ℝ :=
  2 * Real.arsinh (dist (p.1 : Ambient E) q.1 / (2 * √(height p * height q)))

theorem hyperbolicDist_eq_zero_iff (p q : UpperHalfSpace E) :
    hyperbolicDist p q = 0 ↔ p = q := by
  have hden : 0 < 2 * √(height p * height q) := by
    exact mul_pos (by norm_num) (Real.sqrt_pos.2 (mul_pos p.2 q.2))
  constructor
  · intro h
    have hr : dist (p.1 : Ambient E) q.1 / (2 * √(height p * height q)) = 0 := by
      apply Real.arsinh_eq_zero_iff.mp
      exact (mul_eq_zero.mp h).resolve_left (by norm_num)
    have hd : dist (p.1 : Ambient E) q.1 = 0 := by
      rcases div_eq_zero_iff.mp hr with hd | hd
      · exact hd
      · exact (hden.ne' hd).elim
    exact Subtype.ext (dist_eq_zero.mp hd)
  · intro h
    subst q
    simp [hyperbolicDist]

theorem sinh_half_hyperbolicDist (p q : UpperHalfSpace E) :
    Real.sinh (hyperbolicDist p q / 2) =
      dist (p.1 : Ambient E) q.1 / (2 * √(height p * height q)) := by
  rw [hyperbolicDist, mul_div_cancel_left₀ (Real.arsinh _) (by norm_num), Real.sinh_arsinh]

theorem cosh_half_hyperbolicDist (p q : UpperHalfSpace E) :
    Real.cosh (hyperbolicDist p q / 2) =
      dist (p.1 : Ambient E) (reflect q.1) / (2 * √(height p * height q)) := by
  rw [← sq_eq_sq₀, Real.cosh_sq', sinh_half_hyperbolicDist,
    div_pow, div_pow, one_add_div, mul_pow, Real.sq_sqrt]
  · have href : dist (p.1 : Ambient E) (reflect q.1) ^ 2 =
        dist p.1 q.1 ^ 2 + 4 * height p * height q := dist_reflect_sq p.1 q.1
    have hp : 0 < height p := p.2
    have hq : 0 < height q := q.2
    have hprod : 0 < height p * height q := mul_pos hp hq
    rw [div_left_inj' (by positivity : (2 : ℝ) ^ 2 * (height p * height q) ≠ 0)]
    nlinarith [href]
  all_goals
    have hp : 0 < height p := p.2
    have hq : 0 < height q := q.2
    positivity

theorem sinh_half_hyperbolicDist_add (p q r : UpperHalfSpace E) :
    Real.sinh ((hyperbolicDist p q + hyperbolicDist q r) / 2) =
      (dist (p.1 : Ambient E) q.1 * dist r.1 (reflect q.1) +
        dist q.1 r.1 * dist p.1 (reflect q.1)) /
        (4 * height q * √(height p * height r)) := by
  rw [add_div, Real.sinh_add, sinh_half_hyperbolicDist,
    sinh_half_hyperbolicDist, cosh_half_hyperbolicDist,
    cosh_half_hyperbolicDist, dist_reflect_comm q.1 r.1]
  have hroot : √(height p * height q) * √(height q * height r) =
      height q * √(height p * height r) := by
    have hp : 0 ≤ height p := p.2.le
    have hq' : 0 ≤ height q := q.2.le
    rw [Real.sqrt_mul hp, Real.sqrt_mul hq', Real.sqrt_mul hp]
    have hq : √(height q) * √(height q) = height q :=
      Real.mul_self_sqrt hq'
    calc
      (√(height p) * √(height q)) * (√(height q) * √(height r)) =
          (√(height q) * √(height q)) * (√(height p) * √(height r)) := by ring
      _ = height q * (√(height p) * √(height r)) := by rw [hq]
  have hpq : 0 < √(height p * height q) :=
    Real.sqrt_pos.2 (mul_pos p.2 q.2)
  have hqr : 0 < √(height q * height r) :=
    Real.sqrt_pos.2 (mul_pos q.2 r.2)
  have hpr : 0 < √(height p * height r) :=
    Real.sqrt_pos.2 (mul_pos p.2 r.2)
  have hden :
      (2 * √(height p * height q)) * (2 * √(height q * height r)) =
        4 * height q * √(height p * height r) := by
    calc
      _ = 4 * (√(height p * height q) * √(height q * height r)) := by ring
      _ = 4 * (height q * √(height p * height r)) := by rw [hroot]
      _ = _ := by ring
  simp only [div_mul_div_comm]
  rw [← add_div, hden]
  congr 1
  ring

variable [InnerProductSpace ℝ E]

theorem hyperbolicDist_triangle (p q r : UpperHalfSpace E) :
    hyperbolicDist p r ≤ hyperbolicDist p q + hyperbolicDist q r := by
  have hcmp (u v : UpperHalfSpace E) (s : ℝ) :
      hyperbolicDist u v ≤ s ↔
        dist (u.1 : Ambient E) v.1 / (2 * √(height u * height v)) ≤
          Real.sinh (s / 2) := by
    rw [← div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2),
      ← Real.sinh_le_sinh, sinh_half_hyperbolicDist]
  rw [hcmp p r, sinh_half_hyperbolicDist_add]
  have hpt := EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist
    (p.1 : Ambient E) q.1 r.1 (reflect q.1)
  rw [dist_self_reflect q] at hpt
  have hq : 0 < height q := q.2
  have hs : 0 < √(height p * height r) :=
    Real.sqrt_pos.2 (mul_pos p.2 r.2)
  have hden : 0 < 4 * height q * √(height p * height r) := by positivity
  have heq : dist (p.1 : Ambient E) r.1 / (2 * √(height p * height r)) =
      (dist p.1 r.1 * (2 * height q)) /
        (4 * height q * √(height p * height r)) := by
    field_simp
    ring
  rw [heq, div_le_div_iff_of_pos_right hden]
  exact hpt

/-- A separate type keeps the hyperbolic metric distinct from the Euclidean coordinate metric. -/
structure HyperbolicSpace (E : Type*) where
  coordinates : UpperHalfSpace E

noncomputable instance hyperbolicMetricSpace : MetricSpace (HyperbolicSpace E) where
  dist p q := hyperbolicDist p.coordinates q.coordinates
  dist_self p := by simp [hyperbolicDist]
  dist_comm p q := by simp [hyperbolicDist, dist_comm, mul_comm]
  dist_triangle p q r := hyperbolicDist_triangle p.coordinates q.coordinates r.coordinates
  eq_of_dist_eq_zero := by
    intro p q h
    obtain ⟨p⟩ := p
    obtain ⟨q⟩ := q
    congr 1
    exact (hyperbolicDist_eq_zero_iff p q).mp h

/-- The real three-dimensional upper half-space model. -/
abbrev HyperbolicThreeSpace := HyperbolicSpace ℂ

/-- Horizontal translation preserves positive height. -/
def horizontalTranslate (u : E) (p : UpperHalfSpace E) : UpperHalfSpace E :=
  ⟨WithLp.toLp 2 (p.1.fst + u, height p), by
    change 0 < height p
    exact p.2⟩

omit [InnerProductSpace ℝ E] in
theorem hyperbolicDist_horizontalTranslate (u : E) (p q : UpperHalfSpace E) :
    hyperbolicDist (horizontalTranslate u p) (horizontalTranslate u q) =
      hyperbolicDist p q := by
  have heuc : dist ((horizontalTranslate u p).1 : Ambient E)
      (horizontalTranslate u q).1 = dist p.1 q.1 := by
    rw [WithLp.prod_dist_eq_of_L2, WithLp.prod_dist_eq_of_L2]
    simp [horizontalTranslate, height, dist_add_right]
  simp only [hyperbolicDist, heuc]
  rfl

/-- Horizontal translations act by hyperbolic isometries. -/
noncomputable def horizontalTranslation (u : E) :
    HyperbolicSpace E ≃ᵢ HyperbolicSpace E where
  toFun p := ⟨horizontalTranslate u p.coordinates⟩
  invFun p := ⟨horizontalTranslate (-u) p.coordinates⟩
  left_inv := by
    intro p
    cases p with
    | mk p =>
      change (⟨horizontalTranslate (-u) (horizontalTranslate u p)⟩ :
        HyperbolicSpace E) = ⟨p⟩
      congr 1
      apply Subtype.ext
      apply WithLp.ofLp_injective
      apply Prod.ext
      · simp [horizontalTranslate, add_assoc]
      · rfl
  right_inv := by
    intro p
    cases p with
    | mk p =>
      change (⟨horizontalTranslate u (horizontalTranslate (-u) p)⟩ :
        HyperbolicSpace E) = ⟨p⟩
      congr 1
      apply Subtype.ext
      apply WithLp.ofLp_injective
      apply Prod.ext
      · simp [horizontalTranslate, add_assoc]
      · rfl
  isometry_toFun := Isometry.of_dist_eq fun p q => by
    exact hyperbolicDist_horizontalTranslate u p.coordinates q.coordinates

theorem horizontalTranslation_zero :
    horizontalTranslation (0 : E) = 1 := by
  apply IsometryEquiv.ext
  intro p
  cases p with
  | mk p =>
    change (⟨horizontalTranslate 0 p⟩ : HyperbolicSpace E) = ⟨p⟩
    congr 1
    apply Subtype.ext
    apply WithLp.ofLp_injective
    apply Prod.ext
    · simp [horizontalTranslate]
    · rfl

theorem horizontalTranslation_add (u v : E) :
    horizontalTranslation (u + v) =
      horizontalTranslation u * horizontalTranslation v := by
  apply IsometryEquiv.ext
  intro p
  cases p with
  | mk p =>
    change (⟨horizontalTranslate (u + v) p⟩ : HyperbolicSpace E) =
      ⟨horizontalTranslate u (horizontalTranslate v p)⟩
    congr 1
    apply Subtype.ext
    apply WithLp.ofLp_injective
    apply Prod.ext
    · simp [horizontalTranslate, add_assoc, add_comm]
    · rfl

/-- Horizontal additive translations as an isometric group representation. -/
noncomputable def horizontalRepresentation :
    Multiplicative E →* (HyperbolicSpace E ≃ᵢ HyperbolicSpace E) where
  toFun u := horizontalTranslation (Multiplicative.toAdd u)
  map_one' := horizontalTranslation_zero
  map_mul' u v := horizontalTranslation_add (Multiplicative.toAdd u) (Multiplicative.toAdd v)

theorem horizontalTranslation_fixed_iff_zero (u : E) (p : HyperbolicSpace E) :
    horizontalTranslation u p = p ↔ u = 0 := by
  constructor
  · intro h
    have hfirst := congrArg (fun x : HyperbolicSpace E => x.coordinates.1.fst) h
    change p.coordinates.1.fst + u = p.coordinates.1.fst at hfirst
    have hfirst' : p.coordinates.1.fst + u = p.coordinates.1.fst + (0 : E) := by
      simpa using hfirst
    exact add_left_cancel hfirst'
  · intro h
    subst u
    rw [horizontalTranslation_zero]
    rfl

#print axioms hyperbolicDist_triangle
#print axioms hyperbolicMetricSpace
#print axioms horizontalRepresentation
#print axioms horizontalTranslation_fixed_iff_zero

end D5.S3.Geometry.HyperbolicUpperHalfSpace
