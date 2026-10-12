/- GID: D5/S3/Geometry/Hyperideal/LengthGramMetricSegments
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/LengthGramMetricSegments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.StdSimplex]
   utility: none
   digest: Actual isometric intervals, original affine-segment coverage and full ambient-between rigidity for the same frozen radial body. -/

import D5.S3.Geometry.Hyperideal.LengthGramPolytope
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Matrix
open Set
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.HyperbolicUpperHalfSpace
namespace D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem lorentz_null_orthogonal (X W : Fin 4 → ℝ)
    (hX : lorentz X X = -1) (hW : lorentz W W = 0)
    (horth : lorentz X W = 0) : W = 0 := by
  simp [lorentz, Fin.sum_univ_succ] at hX hW horth
  have hu : X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2 = X 3 ^ 2 - 1 := by nlinarith
  have hw : W 0 ^ 2 + W 1 ^ 2 + W 2 ^ 2 = W 3 ^ 2 := by nlinarith
  have ho : X 0 * W 0 + X 1 * W 1 + X 2 * W 2 = X 3 * W 3 := by linarith
  have hcs : (X 0 * W 0 + X 1 * W 1 + X 2 * W 2)^2 ≤
      (X 0^2 + X 1^2 + X 2^2) * (W 0^2 + W 1^2 + W 2^2) := by
    simpa [Fin.sum_univ_succ, add_assoc] using
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun i : Fin 3 => X i.castSucc) (fun i : Fin 3 => W i.castSucc))
  rw [ho, hu, hw] at hcs
  have ht : W 3 = 0 := by nlinarith only [hcs, sq_nonneg (W 3)]
  rw [ht] at hw
  have h0 : W 0 = 0 := by nlinarith [sq_nonneg (W 1), sq_nonneg (W 2)]
  have h1 : W 1 = 0 := by nlinarith [sq_nonneg (W 0), sq_nonneg (W 2)]
  have h2 : W 2 = 0 := by nlinarith [sq_nonneg (W 0), sq_nonneg (W 1)]
  ext k
  fin_cases k <;> simp [h0,h1,h2,ht]

def lift (p : HyperbolicThreeSpace) : Fin 4 → ℝ :=
  let x := p.coordinates.val.fst.re
  let y := p.coordinates.val.fst.im
  let h := height p.coordinates
  ![x/h, y/h, (x^2+y^2+h^2-1)/(2*h), (x^2+y^2+h^2+1)/(2*h)]

theorem lift_unit (p : HyperbolicThreeSpace) : lorentz (lift p) (lift p) = -1 := by
  have hh : height p.coordinates ≠ 0 := ne_of_gt p.coordinates.property
  simp [lift, lorentz, Fin.sum_univ_succ]
  field_simp
  ring

theorem lift_cosh (p q : HyperbolicThreeSpace) :
    lorentz (lift p) (lift q) = -Real.cosh (dist p q) := by
  have hp : 0 < height p.coordinates := p.coordinates.property
  have hq : 0 < height q.coordinates := q.coordinates.property
  have hs := sinh_half_hyperbolicDist p.coordinates q.coordinates
  change Real.sinh (dist p q / 2) = _ at hs
  have hc : Real.cosh (dist p q) = 1 + 2 *
      (dist (p.coordinates.val : Ambient ℂ) q.coordinates.val /
        (2 * Real.sqrt (height p.coordinates * height q.coordinates)))^2 := by
    calc
      _ = Real.cosh (2 * (dist p q / 2)) := by congr 1; ring
      _ = _ := by rw [Real.cosh_two_mul, Real.cosh_sq, hs]; ring
  rw [hc]
  rw [WithLp.prod_dist_eq_of_L2]
  simp only [div_pow, mul_pow, Real.sq_sqrt (mul_pos hp hq).le,
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _)), Real.dist_eq, sq_abs]
  rw [Complex.dist_eq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im]
  simp [lift, lorentz, Fin.sum_univ_succ, height]
  have hp0 : p.coordinates.val.snd ≠ 0 := ne_of_gt hp
  have hq0 : q.coordinates.val.snd ≠ 0 := ne_of_gt hq
  field_simp [hp0, hq0]
  ring


theorem lift_injective : Function.Injective lift := by
  intro p q heq
  have hd (p : HyperbolicThreeSpace) : lift p 3 - lift p 2 = 1 / height p.coordinates := by
    simp [lift]
    ring
  have hh : height p.coordinates = height q.coordinates := by
    apply inv_injective
    simpa only [← one_div, ← hd] using congrArg (fun Y : Fin 4 → ℝ => Y 3 - Y 2) heq
  have hx := congrFun heq 0
  have hy := congrFun heq 1
  simp only [lift, Matrix.cons_val_zero, Matrix.cons_val_one] at hx hy
  have hq : height q.coordinates ≠ 0 := ne_of_gt q.coordinates.property
  rw [hh] at hx hy
  have hx' := (div_left_inj' hq).mp hx
  have hy' := (div_left_inj' hq).mp hy
  cases p with
  | mk p =>
    cases q with
    | mk q =>
      congr 1
      apply Subtype.ext
      apply WithLp.ofLp_injective
      apply Prod.ext
      · exact Complex.ext hx' hy'
      · exact hh

theorem lift_of_coordinates (p : HyperbolicThreeSpace) (Y : Fin 4 → ℝ)
    (hu : lorentz Y Y = -1) (ht : 0 < Y 3)
    (hc : p.coordinates.val = WithLp.toLp 2
      (Complex.mk (Y 0 / (Y 3-Y 2)) (Y 1 / (Y 3-Y 2)), 1/(Y 3-Y 2))) :
    lift p = Y := by
  have hunit := hu
  simp [lorentz, Fin.sum_univ_succ] at hunit
  have hd : 0 < Y 3 - Y 2 := by nlinarith [sq_nonneg (Y 0), sq_nonneg (Y 1)]
  ext k
  fin_cases k <;> simp [lift, height, hc] <;> field_simp [hd.ne'] <;>
    nlinarith [sq_nonneg (Y 0), sq_nonneg (Y 1)]

theorem lorentz_linear (X Y Z W : Fin 4 → ℝ) (a b c d : ℝ) :
    lorentz (a • X + b • Y) (c • Z + d • W) =
    a*c*lorentz X Z + a*d*lorentz X W + b*c*lorentz Y Z + b*d*lorentz Y W := by
  simp [lorentz, Fin.sum_univ_succ]
  ring

theorem lorentz_symm (X Y : Fin 4 → ℝ) : lorentz X Y = lorentz Y X := by
  simp [lorentz, Fin.sum_univ_succ]
  ring

private theorem interpolation_pair (X Y : Fin 4 → ℝ) (D s t : ℝ)
    (hD : Real.sinh D ≠ 0) (hX : lorentz X X = -1) (hY : lorentz Y Y = -1)
    (hXY : lorentz X Y = -Real.cosh D) :
    lorentz ((Real.sinh (D-s)/Real.sinh D) • X + (Real.sinh s/Real.sinh D) • Y)
      ((Real.sinh (D-t)/Real.sinh D) • X + (Real.sinh t/Real.sinh D) • Y) =
      -Real.cosh (s-t) := by
  rw [lorentz_linear, lorentz_symm Y X, hX, hY, hXY]
  simp only [Real.sinh_sub, Real.cosh_sub]
  field_simp
  linear_combination (Real.sinh s * Real.sinh t) * (Real.cosh_sq_sub_sinh_sq D)


private def interpolate (X Y : Fin 4 → ℝ) (D t : ℝ) : Fin 4 → ℝ :=
  (Real.sinh (D-t)/Real.sinh D) • X + (Real.sinh t/Real.sinh D) • Y

private theorem interpolate_zero (X Y : Fin 4 → ℝ) (D : ℝ) (hD : Real.sinh D ≠ 0) :
    interpolate X Y D 0 = X := by simp [interpolate, hD]

private theorem interpolate_end (X Y : Fin 4 → ℝ) (D : ℝ) (hD : Real.sinh D ≠ 0) :
    interpolate X Y D D = Y := by simp [interpolate, hD]

theorem lorentz_right (X Y Z : Fin 4 → ℝ) (a b : ℝ) :
    lorentz X (a • Y + b • Z) = a * lorentz X Y + b * lorentz X Z := by
  simpa using lorentz_linear X X Y Z 1 0 a b

private theorem between_lift (p q z : HyperbolicThreeSpace) (hpq : p ≠ q)
    (hb : dist p z + dist z q = dist p q) :
    lift z = interpolate (lift p) (lift q) (dist p q) (dist p z) := by
  let D := dist p q
  let r := dist p z
  let T := interpolate (lift p) (lift q) D r
  have hD : Real.sinh D ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr (dist_pos.mpr hpq))
  have hpair (s t : ℝ) :
      lorentz (interpolate (lift p) (lift q) D s) (interpolate (lift p) (lift q) D t) =
        -Real.cosh (s-t) :=
    interpolation_pair _ _ _ _ _ hD (lift_unit p) (lift_unit q) (lift_cosh p q)
  have hu : lorentz T T = -1 := by simpa [T] using hpair r r
  have hTX : lorentz T (lift p) = -Real.cosh r := by
    simpa only [interpolate_zero _ _ _ hD, sub_zero] using hpair r 0
  have hTY : lorentz T (lift q) = -Real.cosh (D-r) := by
    have h := hpair D r
    rw [interpolate_end _ _ _ hD, lorentz_symm] at h
    exact h
  have hZX : lorentz (lift z) (lift p) = lorentz T (lift p) := by
    rw [hTX, lorentz_symm, lift_cosh]
  have hzq : dist z q = D-r := by dsimp [D,r]; linarith
  have hZY : lorentz (lift z) (lift q) = lorentz T (lift q) := by
    rw [hTY, lift_cosh, hzq]
  have hZT : lorentz (lift z) T = -1 := by
    calc
      _ = lorentz T T := by
        change lorentz (lift z) (_ • _ + _ • _) = lorentz T (_ • _ + _ • _)
        rw [lorentz_right, lorentz_right, hZX, hZY]
      _ = -1 := hu
  have hn : lorentz (lift z + (-1 : ℝ) • T) (lift z + (-1 : ℝ) • T) = 0 := by
    have h := lorentz_linear (lift z) T (lift z) T 1 (-1) 1 (-1)
    simpa [lift_unit, hu, hZT, lorentz_symm T (lift z)] using h
  have ho : lorentz (lift p) (lift z + (-1 : ℝ) • T) = 0 := by
    have h := lorentz_right (lift p) (lift z) T 1 (-1)
    have he : lorentz (lift p) (lift z) = lorentz (lift p) T := by
      simpa only [lorentz_symm (lift p)] using hZX
    simpa [he] using h
  have he := lorentz_null_orthogonal (lift p) (lift z + (-1 : ℝ) • T) (lift_unit p) hn ho
  ext k
  have hk := congrFun he k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hk
  change lift z k = T k
  linarith

theorem future_den (Y : Fin 4 → ℝ) (hu : lorentz Y Y = -1) (ht : 0 < Y 3) :
    0 < Y 3 - Y 2 := by
  simp [lorentz, Fin.sum_univ_succ] at hu
  nlinarith [sq_nonneg (Y 0), sq_nonneg (Y 1)]

def project (Y : Fin 4 → ℝ) (hu : lorentz Y Y = -1) (ht : 0 < Y 3) :
    HyperbolicThreeSpace :=
  ⟨⟨WithLp.toLp 2 (Complex.mk (Y 0/(Y 3-Y 2)) (Y 1/(Y 3-Y 2)), 1/(Y 3-Y 2)),
    one_div_pos.mpr (future_den Y hu ht)⟩⟩

theorem lift_time (p : HyperbolicThreeSpace) : 0 < lift p 3 := by
  simp only [lift, Matrix.cons_val_three]
  exact div_pos (by positivity) (mul_pos (by norm_num) p.coordinates.property)

private theorem interpolate_future (X Y : Fin 4 → ℝ) (D t : ℝ)
    (hD : 0 < D) (ht : t ∈ Icc 0 D) (hX : 0 < X 3) (hY : 0 < Y 3) :
    0 < interpolate X Y D t 3 := by
  have hsD := Real.sinh_pos_iff.mpr hD
  have ha : 0 ≤ Real.sinh (D-t)/Real.sinh D :=
    div_nonneg (Real.sinh_nonneg_iff.mpr (sub_nonneg.mpr ht.2)) hsD.le
  have hb : 0 ≤ Real.sinh t/Real.sinh D :=
    div_nonneg (Real.sinh_nonneg_iff.mpr ht.1) hsD.le
  change 0 < (Real.sinh (D-t)/Real.sinh D) * X 3 + (Real.sinh t/Real.sinh D) * Y 3
  rcases lt_or_eq_of_le ht.2 with hlt | heq
  · exact add_pos_of_pos_of_nonneg
      (mul_pos (div_pos (Real.sinh_pos_iff.mpr (sub_pos.mpr hlt)) hsD) hX)
      (mul_nonneg hb hY.le)
  · subst t
    simpa [hsD.ne'] using hY

private theorem hyperbolic_segment (p q : HyperbolicThreeSpace) (hpq : p ≠ q) :
    ∃ gamma : Icc (0 : ℝ) (dist p q) → HyperbolicThreeSpace,
      Isometry gamma ∧
      gamma ⟨0, by exact ⟨le_rfl, dist_nonneg⟩⟩ = p ∧
      gamma ⟨dist p q, by exact ⟨dist_nonneg, le_rfl⟩⟩ = q ∧
      (∀ t, lift (gamma t) = interpolate (lift p) (lift q) (dist p q) t) ∧
      range gamma = {z | dist p z + dist z q = dist p q} := by
  let D := dist p q
  have hD : 0 < D := dist_pos.mpr hpq
  have hsD := (Real.sinh_pos_iff.mpr hD).ne'
  let Y := fun t : Icc (0 : ℝ) D => interpolate (lift p) (lift q) D t
  have hu (t : Icc (0 : ℝ) D) : lorentz (Y t) (Y t) = -1 := by
    simpa only [Y, interpolate, sub_self, Real.cosh_zero] using
      interpolation_pair (lift p) (lift q) D t t hsD (lift_unit p) (lift_unit q) (lift_cosh p q)
  have ht (t : Icc (0 : ℝ) D) : 0 < Y t 3 :=
    interpolate_future _ _ _ _ hD t.property (lift_time p) (lift_time q)
  let gamma := fun t : Icc (0 : ℝ) D => project (Y t) (hu t) (ht t)
  have hg (t : Icc (0 : ℝ) D) : lift (gamma t) = Y t :=
    lift_of_coordinates _ _ (hu t) (ht t) rfl
  have hiso : Isometry gamma := by
    apply Isometry.of_dist_eq
    intro s t
    apply Real.cosh_strictMonoOn.injOn dist_nonneg dist_nonneg
    have h := interpolation_pair (lift p) (lift q) D s t hsD (lift_unit p) (lift_unit q) (lift_cosh p q)
    change lorentz (Y s) (Y t) = -Real.cosh ((s : ℝ)-(t : ℝ)) at h
    rw [← hg s, ← hg t, lift_cosh] at h
    simpa [Subtype.dist_eq, Real.dist_eq, Real.cosh_abs] using neg_injective h
  have h0 : gamma ⟨0, ⟨le_rfl,hD.le⟩⟩ = p := by
    apply lift_injective
    rw [hg]
    exact interpolate_zero _ _ _ hsD
  have h1 : gamma ⟨D, ⟨hD.le,le_rfl⟩⟩ = q := by
    apply lift_injective
    rw [hg]
    exact interpolate_end _ _ _ hsD
  refine ⟨gamma,hiso,h0,h1,hg,?_⟩
  ext z
  constructor
  · rintro ⟨t,rfl⟩
    change dist p (gamma t) + dist (gamma t) q = D
    rw [← h0, ← h1, hiso.dist_eq, hiso.dist_eq]
    simp only [Subtype.dist_eq, Real.dist_eq]
    rw [abs_of_nonpos (by linarith [t.property.1]), abs_of_nonpos (by linarith [t.property.2])]
    ring
  · intro hz
    have hr : dist p z ∈ Icc (0 : ℝ) D := ⟨dist_nonneg, by
      have := dist_nonneg (x := z) (y := q); change _ + _ = D at hz; linarith⟩
    refine ⟨⟨dist p z,hr⟩, ?_⟩
    apply lift_injective
    rw [hg]
    exact (between_lift p q z hpq hz).symm


/-- Actual arclength intervals in the image of the original affine segment,
for any fixed witnesses of the frozen radial-coordinate contract. -/
theorem same_body_metric_segments (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (m : Matrix (Fin 4) (Fin 4) ℝ) (f : cutBody l → HyperbolicThreeSpace)
    (hfinj : Function.Injective f)
    (hframe : ∀ v, ∃ y : Fin 4 → ℝ, y = (radial l v.val) ᵥ* m ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0 / (y 3-y 2)) (y 1 / (y 3-y 2)), 1/(y 3-y 2)))
    (lambda mu : cutBody l) :
    ∃ gamma : Icc (0 : ℝ) (dist (f lambda) (f mu)) → HyperbolicThreeSpace,
      Isometry gamma ∧
      gamma ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = f lambda ∧
      gamma ⟨dist (f lambda) (f mu), ⟨dist_nonneg, le_rfl⟩⟩ = f mu ∧
      range gamma = {z | ∃ v : cutBody l,
        v.val ∈ segment ℝ lambda.val mu.val ∧ f v = z} ∧
      range gamma = {z | dist (f lambda) z + dist z (f mu) = dist (f lambda) (f mu)} := by
  classical
  by_cases he : lambda = mu
  · subst mu
    let gamma : Icc (0 : ℝ) (dist (f lambda) (f lambda)) → HyperbolicThreeSpace := fun _ => f lambda
    have hiso : Isometry gamma := by
      apply Isometry.of_dist_eq
      intro s t
      have hs : (s : ℝ) = 0 := le_antisymm (by simpa using s.property.2) s.property.1
      have ht : (t : ℝ) = 0 := le_antisymm (by simpa using t.property.2) t.property.1
      simp [gamma, Subtype.dist_eq, hs, ht]
    refine ⟨gamma,hiso,rfl,rfl,?_,?_⟩
    · ext z
      simp only [mem_range, mem_setOf_eq, segment_same, mem_singleton_iff]
      constructor
      · rintro ⟨t,rfl⟩; exact ⟨lambda,rfl,rfl⟩
      · rintro ⟨v,hv,rfl⟩
        have hv' : v = lambda := Subtype.ext hv
        subst v
        exact ⟨⟨0,le_rfl,dist_nonneg⟩,rfl⟩
    · ext z
      constructor
      · rintro ⟨t,rfl⟩; simp [gamma]
      · intro hz
        have hz0 : dist (f lambda) z = 0 := by
          have := dist_nonneg (x := z) (y := f lambda)
          have := dist_nonneg (x := f lambda) (y := z)
          change dist (f lambda) z + dist z (f lambda) = dist (f lambda) (f lambda) at hz
          rw [dist_self] at hz
          linarith
        exact ⟨⟨0,le_rfl,dist_nonneg⟩,dist_eq_zero.mp hz0⟩
  have hpq : f lambda ≠ f mu := fun h => he (hfinj h)
  obtain ⟨gamma,hiso,h0,h1,hgamma,hbetween⟩ := hyperbolic_segment (f lambda) (f mu) hpq
  refine ⟨gamma,hiso,h0,h1,?_,hbetween⟩
  have hlift (v : cutBody l) : lift (f v) = (radial l v.val) ᵥ* m := by
    obtain ⟨y,hy,hu,ht,hc⟩ := hframe v
    exact (lift_of_coordinates _ _ hu ht hc).trans hy
  have hneg (v : cutBody l) : gramQuadratic l v.val < 0 :=
    (shared_radial_body l hl).2.2.2.1 v.val v.property
  let r := fun v : cutBody l => Real.sqrt (-gramQuadratic l v.val)
  have hr (v : cutBody l) : 0 < r v := Real.sqrt_pos.mpr (neg_pos.mpr (hneg v))
  have hconv : Convex ℝ (cutBody l) := by
    rw [← (LengthGramPolytope.cut_body_polytope l hl).2.1]
    exact convex_convexHull ℝ _
  let D := dist (f lambda) (f mu)
  have hD : 0 < D := dist_pos.mpr hpq
  have hsD := Real.sinh_pos_iff.mpr hD
  let a := fun t : ℝ => Real.sinh (D-t) / (Real.sinh D * r lambda)
  let b := fun t : ℝ => Real.sinh t / (Real.sinh D * r mu)
  let w := fun t : ℝ => b t / (a t+b t)
  have ha (t : ℝ) (ht : t ∈ Icc 0 D) : 0 ≤ a t :=
    div_nonneg (Real.sinh_nonneg_iff.mpr (sub_nonneg.mpr ht.2)) (mul_pos hsD (hr lambda)).le
  have hb (t : ℝ) (ht : t ∈ Icc 0 D) : 0 ≤ b t :=
    div_nonneg (Real.sinh_nonneg_iff.mpr ht.1) (mul_pos hsD (hr mu)).le
  have hab (t : ℝ) (ht : t ∈ Icc 0 D) : 0 < a t+b t := by
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · exact add_pos_of_pos_of_nonneg
        (div_pos (Real.sinh_pos_iff.mpr (sub_pos.mpr hlt)) (mul_pos hsD (hr lambda))) (hb t ht)
    · subst t
      exact add_pos_of_nonneg_of_pos (ha D ⟨hD.le,le_rfl⟩)
        (div_pos hsD (mul_pos hsD (hr mu)))
  have hw (t : ℝ) (ht : t ∈ Icc 0 D) : w t ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (hb t ht) (hab t ht).le,
      (div_le_one (hab t ht)).mpr (le_add_of_nonneg_left (ha t ht))⟩
  let nu : Icc (0 : ℝ) D → cutBody l := fun t =>
    ⟨(1-w t) • lambda.val + w t • mu.val,
      hconv lambda.property mu.property (sub_nonneg.mpr (hw t t.property).2)
        (hw t t.property).1 (sub_add_cancel 1 (w t))⟩
  have hnuseg (t : Icc (0 : ℝ) D) : (nu t).val ∈ segment ℝ lambda.val mu.val :=
    ⟨1-w t,w t,sub_nonneg.mpr (hw t t.property).2,(hw t t.property).1,
      sub_add_cancel 1 (w t),rfl⟩
  have hnugamma (t : Icc (0 : ℝ) D) : f (nu t) = gamma t := by
    have hscaled : (r (nu t) * (a t+b t)) • lift (f (nu t)) = lift (gamma t) := by
      have hrvec (v : cutBody l) : radial l v.val = (r v)⁻¹ • v.val := by
        ext i
        simp [radial,r,div_eq_mul_inv,mul_comm]
      rw [hgamma, hlift, hlift, hlift, hrvec, hrvec, hrvec]
      simp only [Matrix.smul_vecMul, interpolate, smul_smul]
      have hfac : (r (nu t)*(a t+b t)) * (r (nu t))⁻¹ = a t+b t := by
        field_simp [(hr (nu t)).ne']
      rw [hfac]
      change (a t+b t) • (((1-w t) • lambda.val + w t • mu.val) ᵥ* m) = _
      rw [Matrix.add_vecMul, Matrix.smul_vecMul, Matrix.smul_vecMul, smul_add, smul_smul, smul_smul]
      have hwA : (a t+b t)*(1-w t) = a t := by
        dsimp only [w]
        field_simp [(hab t t.property).ne']
        <;> ring
      have hwB : (a t+b t)*w t = b t := by
        dsimp only [w]
        field_simp [(hab t t.property).ne']
      rw [hwA,hwB]
      congr 1 <;> congr 1 <;> dsimp [a,b] <;> ring
    have hk : 0 < r (nu t) * (a t+b t) := mul_pos (hr _) (hab t t.property)
    have hsquare : (r (nu t) * (a t+b t))^2 = 1 := by
      have h := lorentz_linear (lift (f (nu t))) (lift (f (nu t)))
        (lift (f (nu t))) (lift (f (nu t))) (r (nu t)*(a t+b t)) 0 (r (nu t)*(a t+b t)) 0
      simp only [zero_smul, add_zero, mul_zero, zero_mul, lift_unit, mul_neg_one] at h
      rw [hscaled, lift_unit] at h
      nlinarith
    have hk1 : r (nu t)*(a t+b t) = 1 := by nlinarith
    apply lift_injective
    simpa only [hk1, one_smul] using hscaled
  have hwcont : ContinuousOn w (Icc 0 D) := by
    apply ContinuousOn.div
    · dsimp [b]; fun_prop
    · apply ContinuousOn.add <;> dsimp [a,b] <;> fun_prop
    · intro t ht; exact (hab t ht).ne'
  have hw0 : w 0 = 0 := by simp [w,b]
  have hwD : w D = 1 := by
    have hbD : b D ≠ 0 := ne_of_gt (div_pos hsD (mul_pos hsD (hr mu)))
    simp [w,a,hbD]
  ext z
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨nu t,hnuseg t,hnugamma t⟩
  · rintro ⟨v,hv,rfl⟩
    rw [segment_eq_image] at hv
    obtain ⟨c,hc,hvc⟩ := hv
    have himage := intermediate_value_Icc hD.le hwcont
    rw [hw0,hwD] at himage
    obtain ⟨t,ht,hwt⟩ := himage hc
    have hnu : nu ⟨t,ht⟩ = v := by
      apply Subtype.ext
      change (1-w t) • lambda.val + w t • mu.val = v.val
      rw [hwt]
      exact hvc
    exact ⟨⟨t,ht⟩, (hnugamma ⟨t,ht⟩).symm.trans (congrArg f hnu)⟩

#print axioms same_body_metric_segments
end D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
