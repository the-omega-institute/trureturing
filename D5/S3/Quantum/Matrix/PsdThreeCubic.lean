/- GID: D5/S3/Quantum/Matrix/PsdThreeCubic
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/PsdThreeCubic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.MeanInequalities]
   utility: none
   digest: A negative-cycle Gram estimate for three nonnegative edge weights. -/

module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic

/-! The quadratic-form premise below is used
   with the actual complex PSD matrix in PsdThreeCubicComplex. It is not a
   supplied diagonal frame or a hypothesis asserting cubic nonnegativity.
   The argument is elementary Gram geometry and scalar AM-GM; no literature
   priority is asserted. No computational checker or new axiom is used. -/

@[expose] public section
noncomputable section

namespace D5.S3.Quantum.Matrix.PsdThreeCubic

def root3 (a : ℝ) : ℝ := a ^ (1 / 3 : ℝ)

def allowance (a b c : ℝ) : ℝ :=
  2 * (Real.sqrt a * Real.sqrt b + Real.sqrt b * Real.sqrt c +
    Real.sqrt c * Real.sqrt a) + 6 * root3 (a * b * c)

def pairEnergy (a b c d e f x y z : ℝ) : ℝ :=
  a * (d + e) * x ^ 2 + b * (e + f) * y ^ 2 + c * (f + d) * z ^ 2

private theorem root3_nonneg {a : ℝ} (ha : 0 ≤ a) : 0 ≤ root3 a :=
  Real.rpow_nonneg ha _

private theorem root3_cube {a : ℝ} (ha : 0 ≤ a) : root3 a ^ 3 = a := by
  unfold root3
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
  norm_num

private theorem amgm_cube (a b c t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (ht : 0 ≤ t) (hcube : t ^ 3 = a * b * c) :
    3 * t ≤ a + b + c := by
  let u := root3 a * root3 b * root3 c
  have hu : 0 ≤ u := mul_nonneg
    (mul_nonneg (root3_nonneg ha) (root3_nonneg hb)) (root3_nonneg hc)
  have hu3 : u ^ 3 = a * b * c := by
    dsimp [u]
    rw [mul_pow, mul_pow, root3_cube ha, root3_cube hb, root3_cube hc]
  have htu : t = u := (pow_left_inj₀ ht hu (by norm_num : (3 : ℕ) ≠ 0)).mp
    (hcube.trans hu3.symm)
  have h := Real.geom_mean_le_arith_mean3_weighted
    (w₁ := (1 / 3 : ℝ)) (w₂ := (1 / 3 : ℝ)) (w₃ := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) ha hb hc (by norm_num)
  change u ≤ (1 / 3 : ℝ) * a + (1 / 3 : ℝ) * b + (1 / 3 : ℝ) * c at h
  rw [htu]
  linarith

private theorem sqrt_pair_lower (A B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    A ^ 2 + B * C ≤ Real.sqrt (A ^ 2 + C ^ 2) * Real.sqrt (A ^ 2 + B ^ 2) := by
  let u := Real.sqrt (A ^ 2 + C ^ 2)
  let v := Real.sqrt (A ^ 2 + B ^ 2)
  have hu : u ^ 2 = A ^ 2 + C ^ 2 := Real.sq_sqrt (by positivity)
  have hv : v ^ 2 = A ^ 2 + B ^ 2 := Real.sq_sqrt (by positivity)
  have huv : 0 ≤ u * v := by dsimp [u, v]; positivity
  have hr : 0 ≤ A ^ 2 + B * C := by positivity
  have hid : (u * v) ^ 2 - (A ^ 2 + B * C) ^ 2 = A ^ 2 * (B - C) ^ 2 := by
    rw [mul_pow, hu, hv]
    ring
  exact (sq_le_sq₀ hr huv).mp (by nlinarith [mul_nonneg (sq_nonneg A) (sq_nonneg (B-C))])

private theorem weighted_sqrt_pair (a b c x y z : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    a*x^2 + Real.sqrt b*Real.sqrt c*y*z ≤
      Real.sqrt (a*x^2+c*z^2) * Real.sqrt (a*x^2+b*y^2) := by
  have h := sqrt_pair_lower (Real.sqrt a*x) (Real.sqrt b*y) (Real.sqrt c*z)
    (by positivity) (by positivity)
  simpa only [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sq_sqrt hc,
    mul_assoc, mul_left_comm, mul_comm] using h

/-- The load-bearing Gram estimate. Zero weights and zero edges are allowed.
    All three diagonal values belong to the same quadratic form. -/
theorem negative_pair_bound (a b c d e f x y z : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hgram : ∀ u v w : ℝ, 0 ≤ d*u^2+e*v^2+f*w^2-
      2*(x*u*v+y*v*w+z*w*u)) :
    allowance a b c * (x*y*z) ≤ pairEnergy a b c d e f x y z := by
  let D := a*x^2+c*z^2
  let E := a*x^2+b*y^2
  let F := b*y^2+c*z^2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hq := hgram (Real.sqrt D) (Real.sqrt E) (Real.sqrt F)
  rw [Real.sq_sqrt hD, Real.sq_sqrt hE, Real.sq_sqrt hF] at hq
  have h1 := mul_le_mul_of_nonneg_left
    (weighted_sqrt_pair a b c x y z ha hb hc hx hy hz) hx
  have h2 := mul_le_mul_of_nonneg_left
    (weighted_sqrt_pair b c a y z x hb hc ha hy hz hx) hy
  have h3 := mul_le_mul_of_nonneg_left
    (weighted_sqrt_pair c a b z x y hc ha hb hz hx hy) hz
  have ham := amgm_cube (a*x^3) (b*y^3) (c*z^3)
    (root3 (a*b*c)*x*y*z) (by positivity) (by positivity) (by positivity)
    (by have hg := root3_nonneg (mul_nonneg (mul_nonneg ha hb) hc); positivity)
    (by rw [mul_pow, mul_pow, mul_pow, root3_cube (by positivity)]; ring)
  dsimp only [D, E, F] at hq
  simp only [add_comm] at hq h1 h2 h3
  dsimp only [allowance, pairEnergy]
  nlinarith only [hq, h1, h2, h3, ham]

/-- P396 is a sufficient, entirely polynomial comparison with the Gram
    allowance. This auxiliary theorem is used by the actual spectral binding.
    The all-zero weight case must be handled separately. -/
theorem allowance_of_p396 (a b c k : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hk : 0 ≤ k)
    (hs : 0 < a+b+c)
    (hcert : (a+b+c)*k^2 ≤ 4*(a+b+c)*(a*b+b*c+c*a)+396*a*b*c) :
    k ≤ allowance a b c := by
  let u := Real.sqrt a
  let v := Real.sqrt b
  let w := Real.sqrt c
  let g := root3 (a*b*c)
  let p := u*v+v*w+w*u
  have hu : u^2 = a := Real.sq_sqrt ha
  have hv : v^2 = b := Real.sq_sqrt hb
  have hw : w^2 = c := Real.sq_sqrt hc
  have hg : 0 ≤ g := root3_nonneg (by positivity)
  have hg3 : g^3 = a*b*c := root3_cube (by positivity)
  have huv : (u*v*w)^2 = a*b*c := by rw [mul_pow, mul_pow, hu, hv, hw]
  have hp : 3*g ≤ p := amgm_cube (u*v) (v*w) (w*u) g
    (by dsimp [u, v]; positivity) (by dsimp [v, w]; positivity)
    (by dsimp [w, u]; positivity) hg (by
      calc
        g^3 = a*b*c := hg3
        _ = (u*v*w)^2 := huv.symm
        _ = (u*v)*(v*w)*(w*u) := by ring)
  have ht := amgm_cube (u*v*w*u) (u*v*w*v) (u*v*w*w) (g^2)
    (by dsimp [u, v, w]; positivity) (by dsimp [u, v, w]; positivity)
    (by dsimp [u, v, w]; positivity) (sq_nonneg g) (by
      calc
        (g^2)^3 = (g^3)^2 := by ring
        _ = ((u*v*w)^2)^2 := by rw [hg3, huv]
        _ = (u*v*w*u)*(u*v*w*v)*(u*v*w*w) := by ring)
  have hp2id : p^2 = a*b+b*c+c*a+2*(u*v*w*u+u*v*w*v+u*v*w*w) := by
    dsimp only [p]
    calc
      (u*v+v*w+w*u)^2 = u^2*v^2+v^2*w^2+w^2*u^2+
        2*(u*v*w*u+u*v*w*v+u*v*w*w) := by ring
      _ = _ := by simp only [hu, hv, hw]
  have hpg := mul_le_mul_of_nonneg_right hp hg
  have hB : 4*(a*b+b*c+c*a)+132*g^2 ≤ (2*p+6*g)^2 := by
    nlinarith [hp2id, ht, hpg]
  have hsum := amgm_cube a b c g ha hb hc hg hg3
  have hsumg := mul_le_mul_of_nonneg_right hsum (sq_nonneg g)
  have hprod : 396*a*b*c ≤ 132*(a+b+c)*g^2 := by nlinarith only [hsumg, hg3]
  have hmul := mul_le_mul_of_nonneg_left hB hs.le
  have hscaled : (a+b+c)*k^2 ≤ (a+b+c)*(2*p+6*g)^2 := by
    nlinarith only [hcert, hprod, hmul]
  have hsq : k^2 ≤ (2*p+6*g)^2 :=
    le_of_mul_le_mul_left hscaled hs
  have hnonneg : 0 ≤ 2*p+6*g := by dsimp [p, u, v, w]; positivity
  exact (sq_le_sq₀ hk hnonneg).mp hsq

end D5.S3.Quantum.Matrix.PsdThreeCubic
