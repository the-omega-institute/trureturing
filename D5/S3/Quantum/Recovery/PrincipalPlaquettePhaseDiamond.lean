/- GID: D5/S3/Quantum/Recovery/PrincipalPlaquettePhaseDiamond
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PrincipalPlaquettePhaseDiamond
   mirror-E: none(waiver:principal-plaquette-phase-diamond)
   anchors: []
   utility: none
   digest: A single party's plaquette phase controls the native diamond error by a paired opposite-gauge test. -/

import D5.S3.Quantum.Recovery.PrincipalTrianglePhaseDiamond
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Single-party plaquette bounds for native channel distance

An opposite gauge preserves each physical paired coefficient while making
the first cross block uniform in the real-part/modulus ratio. Two
contraction tests then bound the native diamond error without a common
correlation quotient, cross-entry modulus dominance, or a phase condition
on the second party. The channel/dilation binding and original off-fibre
target coefficient remain explicit hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Recovery.PrincipalPlaquettePhaseDiamond

/-- The squared-norm contraction certificate for a raw cross block. -/
def IsTwoContraction (a b c d : ℂ) : Prop :=
  ∀ x y : ℂ, ‖a*x + b*y‖^2 + ‖c*x + d*y‖^2 ≤ ‖x‖^2 + ‖y‖^2

/-- Test the block on two normalized flat vectors, allowing arbitrary phases.
Only the four unit moduli, not a phase-gauge hypothesis, enter this lemma. -/
theorem contraction_flat_test {a b c d : ℂ} (h : IsTwoContraction a b c d)
    (s t u v : ℂ) (hs : ‖s‖ = 1) (ht : ‖t‖ = 1)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖s*(a*u + b*v) + t*(c*u + d*v)‖ ≤ 2 := by
  have hrow := h u v
  rw [hu, hv] at hrow
  have hsum : ‖a*u + b*v‖ + ‖c*u + d*v‖ ≤ 2 := by
    by_contra! hn
    have hh := mul_pos (sub_pos.mpr hn)
      (show 0 < ‖a*u + b*v‖ + ‖c*u + d*v‖ + 2 by positivity)
    nlinarith [sq_nonneg (‖a*u + b*v‖ - ‖c*u + d*v‖)]
  calc
    ‖s*(a*u + b*v) + t*(c*u + d*v)‖ ≤
        ‖s*(a*u + b*v)‖ + ‖t*(c*u + d*v)‖ := norm_add_le _ _
    _ = ‖a*u + b*v‖ + ‖c*u + d*v‖ := by simp [hs, ht]
    _ ≤ 2 := hsum

/-- A gauge giving all four entries the same real-part/modulus ratio gives
the exact L1 norm budget; no matrix norm implementation is needed. -/
theorem contraction_modulus_budget {a b c d : ℂ} {p : ℝ}
    (h : IsTwoContraction a b c d)
    (s t u v : ℂ) (hs : ‖s‖ = 1) (ht : ‖t‖ = 1)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (ha : (s*a*u).re = p*‖a‖) (hb : (s*b*v).re = p*‖b‖)
    (hc : (t*c*u).re = p*‖c‖) (hd : (t*d*v).re = p*‖d‖) :
    p*(‖a‖+‖b‖+‖c‖+‖d‖) ≤ 2 := by
  have he : (s*(a*u + b*v) + t*(c*u + d*v)).re =
      p*(‖a‖+‖b‖+‖c‖+‖d‖) := by
    rw [show s*(a*u + b*v) + t*(c*u + d*v) =
        ((s*a*u + s*b*v) + t*c*u) + t*d*v by ring]
    simp only [Complex.add_re, ha, hb, hc, hd]
    ring
  rw [← he]
  exact (Complex.re_le_norm _).trans (contraction_flat_test h s t u v hs ht hu hv)

theorem matrix_unit_product_floor {a b : ℂ} {δ : ℝ}
    (h : ‖(1/2 : ℂ) - a*b‖ ≤ δ) : 1/2-δ ≤ ‖a‖*‖b‖ := by
  have hhalf : ‖(1/2 : ℂ)‖ = 1/2 := by
    rw [show (1/2 : ℂ) = (((1/2 : ℝ)) : ℂ) by norm_num, Complex.norm_real]
    norm_num [Real.norm_eq_abs]
  have hh := norm_le_norm_add_norm_sub (a*b) (1/2 : ℂ)
  rw [hhalf, Complex.norm_mul, norm_sub_rev] at hh
  linarith

private theorem four_cauchy (a b c d A B C D : ℝ) :
    (a*A+b*B+c*C+d*D)^2 ≤ (a^2+b^2+c^2+d^2)*(A^2+B^2+C^2+D^2) := by
  have h : (a*B-b*A)^2+(a*C-c*A)^2+(a*D-d*A)^2+
        (b*C-c*B)^2+(b*D-d*B)^2+(c*D-d*C)^2 =
      (a^2+b^2+c^2+d^2)*(A^2+B^2+C^2+D^2)-(a*A+b*B+c*C+d*D)^2 := by ring
  have hp : 0 ≤ (a*B-b*A)^2+(a*C-c*A)^2+(a*D-d*A)^2+
        (b*C-c*B)^2+(b*D-d*B)^2+(c*D-d*C)^2 := by positivity
  linarith

/-- Exact real reduction for four paired products and two weighted
modulus budgets. The constant 16 is the square of the four entries. -/
theorem bilateral_scalar {a b c d A B C D p q m : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hp : 0 < p) (hq : 0 < q) (hm : 0 ≤ m)
    (h0 : m ≤ a*A) (h1 : m ≤ b*B) (h2 : m ≤ c*C) (h3 : m ≤ d*D)
    (hx : p*(a+b+c+d) ≤ 2) (hy : q*(A+B+C+D) ≤ 2) :
    m ≤ 1/(4*p*q) := by
  have hroot (x y : ℝ) (ex : 0 ≤ x) (ey : 0 ≤ y) (eh : m ≤ x*y) :
      Real.sqrt m ≤ Real.sqrt x * Real.sqrt y := by
    rw [← Real.sqrt_mul ex]
    exact Real.sqrt_le_sqrt eh
  have hs : 4*Real.sqrt m ≤ Real.sqrt a*Real.sqrt A+Real.sqrt b*Real.sqrt B+
      Real.sqrt c*Real.sqrt C+Real.sqrt d*Real.sqrt D := by
    linarith [hroot a A ha hA h0, hroot b B hb hB h1, hroot c C hc hC h2,
      hroot d D hd hD h3]
  have hsq := mul_le_mul hs hs (show 0 ≤ 4*Real.sqrt m by positivity)
    (show 0 ≤ Real.sqrt a*Real.sqrt A+Real.sqrt b*Real.sqrt B+
      Real.sqrt c*Real.sqrt C+Real.sqrt d*Real.sqrt D by positivity)
  have hcs := four_cauchy (Real.sqrt a) (Real.sqrt b) (Real.sqrt c) (Real.sqrt d)
      (Real.sqrt A) (Real.sqrt B) (Real.sqrt C) (Real.sqrt D)
  rw [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sq_sqrt hc, Real.sq_sqrt hd,
      Real.sq_sqrt hA, Real.sq_sqrt hB, Real.sq_sqrt hC, Real.sq_sqrt hD] at hcs
  have hprod : 16*m ≤ (a+b+c+d)*(A+B+C+D) := by
    have he := hsq.trans (by simpa only [pow_two] using hcs)
    nlinarith [Real.sq_sqrt hm]
  have hprod' := mul_le_mul_of_nonneg_left hprod (show 0 ≤ p*q by positivity)
  have hbud := mul_le_mul hx hy (show 0 ≤ q*(A+B+C+D) by positivity) (by norm_num)
  apply (le_div_iff₀ (show 0 < 4*p*q by positivity)).2
  calc
    m*(4*p*q) = (p*q*(16*m))/4 := by ring
    _ ≤ (p*q*((a+b+c+d)*(A+B+C+D)))/4 := by linarith
    _ = ((p*(a+b+c+d))*(q*(A+B+C+D)))/4 := by ring
    _ ≤ 1 := by linarith

noncomputable def plaquetteArg (a b c d : ℂ) : ℝ := Complex.arg (a*d*star (b*c))

theorem plaquette_arg_angle {a b c d : ℂ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    (Complex.arg a : Real.Angle) - Complex.arg b - Complex.arg c + Complex.arg d =
      (plaquetteArg a b c d : Real.Angle) := by
  unfold plaquetteArg
  rw [Complex.star_def,
    Complex.arg_mul_coe_angle (mul_ne_zero ha hd) ((map_ne_zero (starRingEnd ℂ)).mpr (mul_ne_zero hb hc)),
    Complex.arg_mul_coe_angle ha hd, Complex.arg_conj_coe_angle,
    Complex.arg_mul_coe_angle hb hc]
  abel

theorem plaquette_arg_abs_le_pi (a b c d : ℂ) : |plaquetteArg a b c d| ≤ Real.pi := by
  unfold plaquetteArg
  exact abs_le.mpr ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩

private theorem unit_mul_star (x : ℂ) (h : ‖x‖ = 1) : x * star x = 1 := by
  rw [Complex.star_def, Complex.mul_conj, ← Complex.sq_norm, h]
  norm_num

/-- The opposite gauge leaves the actual product unchanged. Testing the
product error against the conjugate of the gauged first entry replaces a
modulus lower bound on the other entry by a real-part lower bound. -/
theorem opposite_gauge_product_floor {x y s u : ℂ} {p δ : ℝ}
    (hx : x ≠ 0) (hs : ‖s‖ = 1) (hu : ‖u‖ = 1)
    (hre : (s*x*u).re = p*‖x‖) (hw : ‖(1/2 : ℂ)-x*y‖ ≤ δ) :
    p/2-δ ≤ ‖x‖ * (star s*y*star u).re := by
  let x' := s*x*u
  let y' := star s*y*star u
  have hprod : x'*y' = x*y := by
    calc
      x'*y' = (s*star s)*(u*star u)*(x*y) := by dsimp [x',y']; ring
      _ = _ := by rw [unit_mul_star s hs, unit_mul_star u hu, one_mul, one_mul]
  have hnorm : ‖x'‖ = ‖x‖ := by simp [x', hs, hu]
  have hxs : star x' * x' = ((‖x'‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.sq_norm]
  have hfirst : (star x' * (1/2 : ℂ)).re = x'.re/2 := by
    rw [show (1/2 : ℂ) = (((1/2 : ℝ)) : ℂ) by norm_num, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.star_def, Complex.conj_re]
    ring
  have hsecond : (((‖x'‖ ^ 2 : ℝ) : ℂ)*y').re = ‖x'‖^2*y'.re := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hp : (star x' * ((1/2 : ℂ)-x'*y')).re =
      x'.re/2 - ‖x'‖^2*y'.re := by
    rw [show star x' * ((1/2 : ℂ)-x'*y') = star x' * (1/2 : ℂ) -
        (star x' * x')*y' by ring, hxs, Complex.sub_re, hfirst, hsecond]
  have hn : ‖star x' * ((1/2 : ℂ)-x'*y')‖ = ‖x‖ * ‖(1/2 : ℂ)-x*y‖ := by
    calc
      _ = ‖star x'‖ * ‖(1/2 : ℂ)-x'*y'‖ := Complex.norm_mul _ _
      _ = _ := by rw [norm_star, hnorm, hprod]
  have hh := Complex.re_le_norm (star x' * ((1/2 : ℂ)-x'*y'))
  rw [hp, hn, hnorm] at hh
  have hδ := mul_le_mul_of_nonneg_left hw (norm_nonneg x)
  have h := hh.trans hδ
  change x'.re = p*‖x‖ at hre
  rw [hre] at h
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  apply (mul_le_mul_iff_of_pos_left hpos).mp
  change ‖x‖ * (p/2-δ) ≤ ‖x‖ * (‖x‖ * y'.re)
  nlinarith only [h]

/-- A single positive checkerboard cosine controls the other party only
through its contraction. There is no hypothesis on the other's phase. -/
theorem one_party_of_gauge {a b c d A B C D : ℂ} {p δ : ℝ}
    (hx : IsTwoContraction a b c d) (hy : IsTwoContraction A B C D)
    (hp : 0 < p) (hp1 : p ≤ 1)
    (s t u v : ℂ) (hs : ‖s‖ = 1) (ht : ‖t‖ = 1) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (ha : (s*a*u).re = p*‖a‖) (hb : (s*b*v).re = p*‖b‖)
    (hc : (t*c*u).re = p*‖c‖) (hd : (t*d*v).re = p*‖d‖)
    (h0 : ‖(1/2 : ℂ)-a*A‖ ≤ δ) (h1 : ‖(1/2 : ℂ)-b*B‖ ≤ δ)
    (h2 : ‖(1/2 : ℂ)-c*C‖ ≤ δ) (h3 : ‖(1/2 : ℂ)-d*D‖ ≤ δ) :
    p/2-1/(4*p) ≤ δ := by
  have hp' : 0 ≤ 1/(4*p) := by positivity
  by_cases hm : 0 < p/2-δ
  · have nz {x y : ℂ} (h : ‖(1/2 : ℂ)-x*y‖ ≤ δ) : x ≠ 0 := by
      have hf := matrix_unit_product_floor h
      intro hzero
      rw [hzero, norm_zero, zero_mul] at hf
      linarith
    have hA := opposite_gauge_product_floor (nz h0) hs hu ha h0
    have hB := opposite_gauge_product_floor (nz h1) hs hv hb h1
    have hC := opposite_gauge_product_floor (nz h2) ht hu hc h2
    have hD := opposite_gauge_product_floor (nz h3) ht hv hd h3
    have nonneg {x : ℂ} {r : ℝ} (h : p/2-δ ≤ ‖x‖*r) : 0 ≤ r := by
      by_contra! hh
      linarith [mul_nonpos_of_nonneg_of_nonpos (norm_nonneg x) hh.le]
    have hy' := contraction_flat_test hy (star s) (star t) (star u) (star v)
      (by simpa only [norm_star] using hs) (by simpa only [norm_star] using ht)
      (by simpa only [norm_star] using hu) (by simpa only [norm_star] using hv)
    have hy'' := (Complex.re_le_norm _).trans hy'
    rw [show star s*(A*star u+B*star v)+star t*(C*star u+D*star v) =
        ((star s*A*star u+star s*B*star v)+star t*C*star u)+star t*D*star v by ring] at hy''
    simp only [Complex.add_re] at hy''
    have h := bilateral_scalar
      (norm_nonneg a) (norm_nonneg b) (norm_nonneg c) (norm_nonneg d)
      (nonneg hA) (nonneg hB) (nonneg hC) (nonneg hD) hp zero_lt_one hm.le
      hA hB hC hD (contraction_modulus_budget hx s t u v hs ht hu hv ha hb hc hd)
      (by simpa only [one_mul] using hy'')
    rw [mul_one] at h
    linarith
  · linarith

open D5.S3.Quantum.Recovery.PrincipalTrianglePhase.RTPhaseBarrier

/-- The checkerboard normalization exposes both signs of the exact
entry phases. Its conjugate row and column gauges preserve entry products. -/
theorem shared_checkerboard_gauge_complex (a b c d : ℂ) (θ : ℝ)
    (hphase : (a.arg : Real.Angle) - b.arg - c.arg + d.arg = (θ : Real.Angle)) :
    ∃ s t u v : ℂ, ‖s‖ = 1 ∧ ‖t‖ = 1 ∧ ‖u‖ = 1 ∧ ‖v‖ = 1 ∧
      s * a * u = (‖a‖ : ℂ) * cis (θ / 4) ∧
      s * b * v = (‖b‖ : ℂ) * cis (-(θ / 4)) ∧
      t * c * u = (‖c‖ : ℂ) * cis (-(θ / 4)) ∧
      t * d * v = (‖d‖ : ℂ) * cis (θ / 4) := by
  let p := θ/4
  let r := a.arg-c.arg-2*p
  let s := p-a.arg
  let t := -p-b.arg
  have hcis : cis (a.arg-b.arg-c.arg+d.arg) = cis θ := by
    apply cis_congr_angle
    simpa only [Real.Angle.coe_add, Real.Angle.coe_sub] using hphase
  have valid (q : ℂ) (l r : ℝ) :
      cis l * q * cis r = (‖q‖ : ℂ) * cis (l+q.arg+r) := by
    rw [cis_add, cis_add]
    have hq : (‖q‖ : ℂ) * cis q.arg = q := Complex.norm_mul_exp_arg_mul_I q
    calc
      cis l * q * cis r = cis l * ((‖q‖ : ℂ) * cis q.arg) * cis r := by
        conv_lhs => rw [← hq]
      _ = _ := by ring
  have h₁ : 0+a.arg+s = p := by dsimp [s]; ring
  have h₂ : 0+b.arg+t = -p := by dsimp [t]; ring
  have h₃ : r+c.arg+s = -p := by dsimp [r,s]; ring
  have h₄ : r+d.arg+t = (a.arg-b.arg-c.arg+d.arg)-3*p := by dsimp [r,t]; ring
  have h₅ : cis (r+d.arg+t) = cis p := by
    rw [h₄, sub_eq_add_neg, cis_add, hcis, ← cis_add]
    congr 1
    dsimp [p]
    ring
  refine ⟨cis 0, cis r, cis s, cis t, norm_cis _, norm_cis _, norm_cis _, norm_cis _, ?_, ?_, ?_, ?_⟩
  · rw [valid, h₁]
  · rw [valid, h₂]
  · rw [valid, h₃]
  · rw [valid, h₅]

/-- The real-part projection of the checkerboard normalization. -/
theorem shared_checkerboard_gauge (a b c d : ℂ) (θ : ℝ)
    (hphase : (a.arg : Real.Angle) - b.arg - c.arg + d.arg = (θ : Real.Angle)) :
    ∃ s t u v : ℂ, ‖s‖ = 1 ∧ ‖t‖ = 1 ∧ ‖u‖ = 1 ∧ ‖v‖ = 1 ∧
      (s*a*u).re = Real.cos (θ/4)*‖a‖ ∧ (s*b*v).re = Real.cos (θ/4)*‖b‖ ∧
      (t*c*u).re = Real.cos (θ/4)*‖c‖ ∧ (t*d*v).re = Real.cos (θ/4)*‖d‖ := by
  obtain ⟨s,t,u,v,hs,ht,hu,hv,ha,hb,hc,hd⟩ :=
    shared_checkerboard_gauge_complex a b c d θ hphase
  refine ⟨s,t,u,v,hs,ht,hu,hv,?_,?_,?_,?_⟩ <;>
    (first | rw [ha] | rw [hb] | rw [hc] | rw [hd]) <;>
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, cis_re, Real.cos_neg, mul_comm]

/-- For arbitrary original block contractions, a small plaquette phase
of only one party is enough; the other party's phase is unrestricted. -/
theorem one_party_plaquette {a b c d A B C D : ℂ} {δ : ℝ}
    (hX : IsTwoContraction a b c d) (hY : IsTwoContraction A B C D)
    (h0 : ‖(1/2 : ℂ)-a*A‖ ≤ δ) (h1 : ‖(1/2 : ℂ)-b*B‖ ≤ δ)
    (h2 : ‖(1/2 : ℂ)-c*C‖ ≤ δ) (h3 : ‖(1/2 : ℂ)-d*D‖ ≤ δ) :
    let θ := plaquetteArg a b c d
    let p := Real.cos (θ/4)
    p/2-1/(4*p) ≤ δ ∧ 1/4-θ^2/32 ≤ δ := by
  let θ := plaquetteArg a b c d
  let p := Real.cos (θ/4)
  change p/2-1/(4*p) ≤ δ ∧ 1/4-θ^2/32 ≤ δ
  have hθ := plaquette_arg_abs_le_pi a b c d
  have hp : 1/2 ≤ p := by
    have hp' : Real.sqrt 2/2 ≤ p := by
      change Real.sqrt 2/2 ≤ Real.cos (θ/4)
      have harg : Real.cos (|θ|/4) = Real.cos (θ/4) := by
        simpa only [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ 4 by norm_num)] using Real.cos_abs (θ/4)
      rw [← harg, ← Real.cos_pi_div_four]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos]) (by linarith)
    have hroot : 1 ≤ Real.sqrt 2 := by
      by_contra! hn
      nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num),
        mul_pos (sub_pos.mpr hn) (show 0 < 1+Real.sqrt 2 by positivity)]
    linarith
  have hp0 : 0 < p := by linarith
  have hp1 : p ≤ 1 := Real.cos_le_one _
  have hδ : p/2-1/(4*p) ≤ δ := by
    by_cases ht : δ < 1/2
    · have nz {x y : ℂ} (h : ‖(1/2 : ℂ)-x*y‖ ≤ δ) : x ≠ 0 := by
        have hh := matrix_unit_product_floor h
        intro hz
        rw [hz,norm_zero,zero_mul] at hh
        linarith
      obtain ⟨s,t,u,v,hs,ht',hu,hv,ha,hb,hc,hd⟩ :=
        shared_checkerboard_gauge a b c d θ (plaquette_arg_angle (nz h0) (nz h1) (nz h2) (nz h3))
      exact one_party_of_gauge hX hY hp0 hp1 s t u v hs ht' hu hv ha hb hc hd h0 h1 h2 h3
    · have : 0 ≤ 1/(4*p) := by positivity
      linarith
  refine ⟨hδ, ?_⟩
  have hcos : 1-p ≤ θ^2/32 := by
    change 1-Real.cos (θ/4) ≤ θ^2/32
    nlinarith only [Real.one_sub_sq_div_two_le_cos (x := θ/4)]
  have hrecip : 1/(4*p) ≤ 3/4-p/2 := by
    apply (div_le_iff₀ (show 0 < (4*p) by positivity)).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hp)]
  linarith

/-- One nonnegative-real plaquette, without any condition on the other,
forces the exact quarter bound. Zero is allowed by the matrix-unit guard. -/
theorem quarter_of_one_nonnegative_real_plaquette {a b c d A B C D : ℂ} {δ : ℝ}
    (hX : IsTwoContraction a b c d) (hY : IsTwoContraction A B C D)
    (h0 : ‖(1/2 : ℂ)-a*A‖ ≤ δ) (h1 : ‖(1/2 : ℂ)-b*B‖ ≤ δ)
    (h2 : ‖(1/2 : ℂ)-c*C‖ ≤ δ) (h3 : ‖(1/2 : ℂ)-d*D‖ ≤ δ)
    (hx₀ : 0 ≤ (a*d*star (b*c)).re) (hx₁ : (a*d*star (b*c)).im = 0) :
    1/4 ≤ δ := by
  have hx : plaquetteArg a b c d = 0 := Complex.arg_eq_zero_iff.mpr ⟨hx₀,hx₁⟩
  have hh := (one_party_plaquette hX hY h0 h1 h2 h3).2
  norm_num [hx] at hh
  exact hh

open D5.S3.Quantum.Recovery.PrincipalTrianglePhase
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open scoped InnerProductSpace ComplexOrder Matrix

/-- The actual cross entries are not changed by the auxiliary Gram
completion. Either physical party's own fibre defects suffice. -/
theorem native_cross_contraction {F : Type*} [Fintype F] [DecidableEq F]
    (G : Matrix (F × Fin 2) (F × Fin 2) ℂ)
    (hG : G.PosSemidef)
    (defect : ∀ f : F, ((1 : Matrix (Fin 2) (Fin 2) ℂ) -
        RTPhaseCube.fibreBlock G f).PosSemidef)
    {f g : F} (hfg : f ≠ g) :
    IsTwoContraction (G (f,0) (g,0)) (G (f,0) (g,1))
      (G (f,1) (g,0)) (G (f,1) (g,1)) := by
  obtain ⟨v,hv⟩ := RTCompletion.column_gram (RTPhaseCube.completeFibres_posSemidef G hG defect)
  have hor (k : F) : Orthonormal ℂ (fun i : Fin 2 => v (k,i)) :=
    orthonormal_iff_ite.mpr (fun i j => by
      rw [hv, RTPhaseCube.completeFibres_same, Matrix.one_apply])
  intro x y
  have h := RTPhaseCube.two_basis_contraction (hor f) (hor g) x y
  simpa only [hv, RTPhaseCube.completeFibres_cross G f g _ _ hfg] using h

private theorem native_witness
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (first second : QuantumChannel a b) (i j : a) (p q : b) (x y : ℂ)
    (actual : NativeDiamond.matrixAction first (Matrix.single i j 1) p q = star (x*y))
    (target : NativeDiamond.matrixAction second (Matrix.single i j 1) p q = 1/2) :
    ‖(1/2 : ℂ)-x*y‖ ≤ diamondDistance first second := by
  have hz := NativeDiamond.matrixUnit_le_diamondDistance first second i j p q
  change ‖NativeDiamond.matrixAction first (Matrix.single i j 1) p q -
    NativeDiamond.matrixAction second (Matrix.single i j 1) p q‖ ≤ _ at hz
  rw [actual, target] at hz
  have he : star (x*y-(1/2 : ℂ)) = star (x*y)-1/2 := by rw [star_sub]; norm_num
  rwa [← he, norm_star, norm_sub_rev] at hz

/-- The explicit single-party lower bound for native channels carrying
these selected physical dilation records. There is no same-R or entry
dominance premise. The actual dilation/action and target correspondence
remain explicit. -/
theorem paired_one_party_native_diamond
    {a b F e₁ e₂ : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype F] [DecidableEq F] [Fintype e₁] [Fintype e₂]
    (first second : QuantumChannel a (b × b))
    (V : Matrix (b × e₁) a ℂ) (W : Matrix (b × e₂) a ℂ)
    (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1)
    (pair : ∀ X, NativeDiamond.matrixAction first X =
      RTDiamond.dilationAction (RTDiamond.pairedDilation V W) X)
    (f : a → b) (pick : F × Fin 2 ↪ a) (label : F → b)
    (byFibre : ∀ p : F × Fin 2, f (pick p) = label p.1)
    (i j : F) (hij : i ≠ j)
    (target : ∀ u v : Fin 2, NativeDiamond.matrixAction second
      (Matrix.single (pick (i,u)) (pick (j,v)) 1)
      (label i,label i) (label j,label j) = 1/2) :
    let G := (RTDiamond.forwardGram f V).submatrix pick pick
    let θ := plaquetteArg (G (i,0) (j,0)) (G (i,0) (j,1)) (G (i,1) (j,0)) (G (i,1) (j,1))
    let p := Real.cos (θ/4)
    p/2-1/(4*p) ≤ diamondDistance first second ∧
      1/4-θ^2/32 ≤ diamondDistance first second := by
  let G := (RTDiamond.forwardGram f V).submatrix pick pick
  let H := (RTDiamond.forwardGram f W).submatrix pick pick
  have hG : G.PosSemidef := (RTDiamond.forwardGram_psd f V).submatrix pick
  have hH : H.PosSemidef := (RTDiamond.forwardGram_psd f W).submatrix pick
  let emb (k : F) : Fin 2 ↪ a := ⟨fun t => pick (k,t), fun _ _ h =>
    congrArg Prod.snd (pick.injective h)⟩
  have dG (k : F) : ((1 : Matrix (Fin 2) (Fin 2) ℂ) - RTPhaseCube.fibreBlock G k).PosSemidef :=
    RTDiamond.forward_fibre_defect f V hV (emb k) (label k) (fun t => byFibre (k,t))
  have dH (k : F) : ((1 : Matrix (Fin 2) (Fin 2) ℂ) - RTPhaseCube.fibreBlock H k).PosSemidef :=
    RTDiamond.forward_fibre_defect f W hW (emb k) (label k) (fun t => byFibre (k,t))
  have witness (u v : Fin 2) :
      ‖(1/2 : ℂ)-G (i,u) (j,v)*H (i,u) (j,v)‖ ≤ diamondDistance first second := by
    apply native_witness first second (pick (i,u)) (pick (j,v))
      (label i,label i) (label j,label j) _ _ _ (target u v)
    rw [pair]
    simpa only [byFibre, G, H, Matrix.submatrix_apply] using
      RTDiamond.paired_channel_coefficient f V W (pick (i,u)) (pick (j,v))
  exact one_party_plaquette (native_cross_contraction G hG dG hij)
    (native_cross_contraction H hH dH hij)
    (witness 0 0) (witness 0 1) (witness 1 0) (witness 1 1)

end D5.S3.Quantum.Recovery.PrincipalPlaquettePhaseDiamond
