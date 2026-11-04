/- GID: D5/S3/Zeros/LeeYang/FiolDoubleHubGrid
   generality: I
   mirror-B: D5/B/S3/Zeros/LeeYang/FiolDoubleHubGrid
   mirror-E: none(waiver:analytic-family-proof)
   anchors: []
   utility: none
   digest: All-parameter physical double-hub grid identities. -/
import D5.S3.Zeros.LeeYang.FiolDoubleHubEndpoint
import D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Order.Fin.InsertNth

open scoped BigOperators
open Polynomial Finset
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Zeros.LeeYang
open FiolDoubleHubEndpoint
namespace FiolDoubleHub
private theorem Q_at_neg_one (d : ℕ) :
    (Q d).eval (-1) = (if Odd d then 1 else 4) *
      (3*(d:ℝ)^2*((d:ℝ)^2-1)+18) := by
  by_cases ho : Odd d
  · have he1 : Even (d+1) := ho.add_odd (by decide : Odd 1)
    have ho2 : Odd (d+2) := ho.add_even (by decide : Even 2)
    have hn : ¬ Even d := Nat.not_even_iff_odd.mpr ho
    have hn2 : ¬ Even (d+2) := Nat.not_even_iff_odd.mpr ho2
    have hu : (U d).eval (-1) = 1 := by simp [U,ho,S,neg_one_geom_sum,hn]
    have hv : (V d).eval (-1) = 0 := by simp [V,ho,S,neg_one_geom_sum,he1]
    have hw : (W d).eval (-1) = 1 := by simp [W,ho,S,neg_one_geom_sum,hn2]
    norm_num [Q,H,hu,hv,hw,ho]
    <;> ring
  · have he : Even d := Nat.not_odd_iff_even.mp ho
    have ho1 : Odd (d+1) := he.add_odd (by decide : Odd 1)
    have he2 : Even (d+2) := he.add (by decide : Even 2)
    have hu : (U d).eval (-1) = 2 := by norm_num [U,ho,H,he.neg_one_pow]
    have hv : (V d).eval (-1) = 0 := by simp [V,ho,H,ho1.neg_one_pow]
    have hw : (W d).eval (-1) = 2 := by norm_num [W,ho,H,he2.neg_one_pow]
    norm_num [Q,H,hu,hv,hw,ho]
    <;> ring

theorem R_neg_one_pos (m : ℕ) (hm : 1 ≤ m) : 0 < (R m).eval (-1) := by
  have hd : (2:ℝ) ≤ ((m+1:ℕ):ℝ) := by exact_mod_cast (by omega : 2 ≤ m+1)
  have hp : 0 < 3*((m+1:ℕ):ℝ)^2*(((m+1:ℕ):ℝ)^2-1)+18 := by
    have hh := mul_nonneg (sq_nonneg (((m+1:ℕ):ℝ)))
      (show 0 ≤ (((m+1:ℕ):ℝ)^2)-1 by nlinarith)
    nlinarith
  have hq : 0 < (Q (m+1)).eval (-1) := by
    rw [Q_at_neg_one]
    split_ifs <;> positivity
  simpa [R] using mul_pos (pow_pos (by norm_num : 0 < (2:ℝ)) (h (m+1))) hq

end FiolDoubleHub


namespace FiolDoubleHub
-- Positivity excludes a further factor at the point 1.
theorem Q_one_pos (d : ℕ) (hd : 2 ≤ d) : 0 < (Q d).eval 1 := by
  have hx : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hu : 0 < (U d).eval 1 := by
    by_cases ho : Odd d
    · simp [U,ho,S]; exact_mod_cast (by omega : 0 < d)
    · norm_num [U,ho,H]
  have hv : 0 < (V d).eval 1 := by
    by_cases ho : Odd d
    · simp [V,ho,S]; positivity
    · norm_num [V,ho,H]
  have hw : 0 < (W d).eval 1 := by
    by_cases ho : Odd d
    · simp [W,ho,S]; positivity
    · norm_num [W,ho,H]
  have hd1 : 0 < (d:ℝ)-1 := by linarith
  have hd2 : 0 < (d:ℝ)^2-1 := by nlinarith
  have hd3 : 0 < 2*(d:ℝ)-3 := by linarith
  have hd4 : 0 < 2*(d:ℝ)-1 := by linarith
  simp only [Q,H,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one,one_pow]
  positivity

private theorem h_even (d : ℕ) (hd : 1 ≤ d) : Even (h d) := by
  unfold h
  split_ifs
  · exact even_two_mul d
  · refine ⟨d-1, ?_⟩
    omega

theorem candidate_one_multiplicity (m : ℕ) (hm : 1 ≤ m) :
    Polynomial.rootMultiplicity (1:ℂ) ((R m).map Complex.ofRealHom) = h (m+1) := by
  have hd : 2 ≤ m+1 := by omega
  have hn : ¬ (Q (m+1)).IsRoot (1:ℝ) := ne_of_gt (Q_one_pos (m+1) hd)
  have hp : Q (m+1) ≠ 0 := by
    intro hz
    have hv := Q_one_pos (m+1) hd
    simpa only [hz,Polynomial.eval_zero,lt_self_iff_false] using hv
  have he : (1-Polynomial.X : Polynomial ℝ)^h (m+1) =
      (Polynomial.X-Polynomial.C 1)^h (m+1) := by
    rw [map_one]
    rw [show (1-Polynomial.X : Polynomial ℝ) = -(Polynomial.X-1) by ring]
    exact (h_even (m+1) (by omega)).neg_pow _
  have hr : Polynomial.rootMultiplicity (1:ℝ) (R m) = h (m+1) := by
    change Polynomial.rootMultiplicity (1:ℝ) ((1-Polynomial.X)^h (m+1)*Q (m+1)) = _
    rw [he,mul_comm,Polynomial.rootMultiplicity_mul_X_sub_C_pow hp,
      Polynomial.rootMultiplicity_eq_zero hn,zero_add]
  have hmap := Polynomial.eq_rootMultiplicity_map (p:=R m)
    (f:=Complex.ofRealHom) Complex.ofReal_injective (1:ℝ)
  rw [map_one,hr] at hmap
  exact hmap.symm

end FiolDoubleHub


-- The uniform d>=5 b-grid estimates, before the separate grid-spacing proof.
private theorem uniform_bounds (d : ℝ) (hd : 5 ≤ d) :
    let alpha := 4*d^2+6*d-1
    let beta := (3*d^4-19*d^2+8*d+8)/2
    let gamma := 32*d-14
    let f := fun t : ℝ => alpha*t^2-beta*t-gamma
    (0 < alpha ∧ alpha < 6*d^2 ∧ d^4 < beta ∧ 2*alpha < beta ∧ 0 < gamma ∧
      gamma < 2*beta/(d+1)) ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ 2 → f t < 0) ∧
    (∀ t : ℝ, 2/(d+1) ≤ -t → 0 < f t) := by
  dsimp only
  let alpha := 4*d^2+6*d-1
  let beta := (3*d^4-19*d^2+8*d+8)/2
  let gamma := 32*d-14
  have hdpos : 0 < d := by linarith
  have hsq : 25 ≤ d^2 := by nlinarith
  have hsq5 : 5*d ≤ d^2 := by nlinarith [mul_nonneg hdpos.le (show 0 ≤ d-5 by linarith)]
  have h4 : 25*d^2 ≤ d^4 := by
    nlinarith [mul_nonneg (sq_nonneg d) (show 0 ≤ d^2-25 by linarith)]
  have ha : 0 < alpha := by dsimp [alpha]; nlinarith [sq_nonneg d]
  have ha6 : alpha < 6*d^2 := by dsimp [alpha]; nlinarith
  have hb4 : d^4 < beta := by
    have hp := mul_pos (show 0 < d^2 by positivity) (show 0 < d^2-19 by linarith)
    dsimp [beta]
    nlinarith
  have hba : 2*alpha < beta := by
    have h12 : 12*d^2 < d^4 := by nlinarith
    linarith
  have hg : 0 < gamma := by dsimp [gamma]; linarith
  have hden : 0 < d+1 := by linarith
  have hratio : gamma < 2*beta/(d+1) := by
    apply (lt_div_iff₀ hden).2
    dsimp [gamma]
    have hsq1 : d ≤ d^2 := by nlinarith
    nlinarith
  refine ⟨⟨ha, ha6, hb4, hba, hg, hratio⟩, ?_, ?_⟩
  · intro t ht0 ht2
    have hb : alpha*t-beta < 0 := by
      have hmul := mul_le_mul_of_nonneg_left ht2 ha.le
      linarith
    have hp := mul_nonpos_of_nonneg_of_nonpos ht0 hb.le
    change alpha*t^2-beta*t-gamma < 0
    nlinarith
  · intro t ht
    have hb : 0 < beta := by linarith [pow_nonneg hdpos.le 4]
    have hmul := mul_le_mul_of_nonneg_left ht hb.le
    have hbeta : gamma < beta*(-t) := by
      calc
        gamma < 2*beta/(d+1) := hratio
        _ = beta*(2/(d+1)) := by ring
        _ ≤ beta*(-t) := hmul
    have hquad := mul_nonneg ha.le (sq_nonneg t)
    change 0 < alpha*t^2-beta*t-gamma
    nlinarith



private noncomputable def gridAngle (d k : ℕ) : ℝ :=
  (k:ℝ)*Real.pi/((d:ℝ)+1)

private theorem negative_grid_bound (d k : ℕ)
    (hleft : Real.pi/2 < gridAngle d k) (hright : gridAngle d k ≤ Real.pi) :
    2/((d:ℝ)+1) ≤ -(2*Real.cos (gridAngle d k)) := by
  have hden : 0 < (d:ℝ)+1 := by positivity
  have hp := Real.pi_pos
  have hreal : (d:ℝ)+1 < 2*(k:ℝ) := by
    have hh := (lt_div_iff₀ hden).mp hleft
    change Real.pi/2*((d:ℝ)+1) < (k:ℝ)*Real.pi at hh
    by_contra hn
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hp.le
    nlinarith
  have hn : d+1 < 2*k := by exact_mod_cast hreal
  have hgapint : (1:ℝ) ≤ 2*(k:ℝ)-((d:ℝ)+1) := by
    have h' : d+2 ≤ 2*k := by omega
    have h'' : (d:ℝ)+2 ≤ 2*(k:ℝ) := by exact_mod_cast h'
    linarith
  have hgap : Real.pi/(2*((d:ℝ)+1)) ≤ gridAngle d k-Real.pi/2 := by
    have heq : gridAngle d k-Real.pi/2 =
        (2*(k:ℝ)-((d:ℝ)+1))*(Real.pi/(2*((d:ℝ)+1))) := by
      dsimp [gridAngle]
      field_simp <;> ring
    rw [heq]
    have hm := mul_le_mul_of_nonneg_right hgapint
      (show 0 ≤ Real.pi/(2*((d:ℝ)+1)) by positivity)
    simpa using hm
  have hs := Real.mul_le_sin (show 0 ≤ gridAngle d k-Real.pi/2 by linarith)
    (show gridAngle d k-Real.pi/2 ≤ Real.pi/2 by linarith)
  have hm := mul_le_mul_of_nonneg_left hgap (show 0 ≤ 2/Real.pi by positivity)
  have hsimp : (2/Real.pi)*(Real.pi/(2*((d:ℝ)+1))) = 1/((d:ℝ)+1) := by
    field_simp <;> ring
  rw [hsimp] at hm
  rw [Real.sin_sub_pi_div_two] at hs
  rw [show (2:ℝ)/((d:ℝ)+1) = 2*(1/((d:ℝ)+1)) by ring]
  linarith

theorem actual_grid_sign (d k : ℕ) (hd : 5 ≤ d)
    (hk : 1 ≤ k) (hkd : k ≤ d+1) :
    let x : ℝ := d
    let t : ℝ := 2*Real.cos (gridAngle d k)
    let f := fun t : ℝ => (4*x^2+6*x-1)*t^2 -
      ((3*x^4-19*x^2+8*x+8)/2)*t-(32*x-14)
    if 2*k ≤ d+1 then f t < 0 else 0 < f t := by
  dsimp only
  have hden : 0 < (d:ℝ)+1 := by positivity
  have hp := Real.pi_pos
  have hθ0 : 0 < gridAngle d k := by
    dsimp [gridAngle]
    exact div_pos (mul_pos (by exact_mod_cast (by omega : 0 < k)) hp) hden
  have hθπ : gridAngle d k ≤ Real.pi := by
    apply (div_le_iff₀ hden).mpr
    have hh : (k:ℝ) ≤ (d:ℝ)+1 := by exact_mod_cast hkd
    nlinarith [mul_le_mul_of_nonneg_right hh hp.le]
  have h := uniform_bounds (d:ℝ) (by exact_mod_cast hd)
  split_ifs with hlow
  · have hθ : gridAngle d k ≤ Real.pi/2 := by
      apply (div_le_iff₀ hden).mpr
      have hh : 2*(k:ℝ) ≤ (d:ℝ)+1 := by exact_mod_cast hlow
      nlinarith [mul_le_mul_of_nonneg_right hh hp.le]
    apply h.2.1
    · exact mul_nonneg (by norm_num)
        (Real.cos_nonneg_of_mem_Icc ⟨by linarith,hθ⟩)
    · nlinarith [Real.cos_le_one (gridAngle d k)]
  · have hθ : Real.pi/2 < gridAngle d k := by
      apply (lt_div_iff₀ hden).mpr
      have hh : (d:ℝ)+1 < 2*(k:ℝ) := by exact_mod_cast (by omega : d+1 < 2*k)
      have hm := mul_lt_mul_of_pos_right hh hp
      nlinarith
    apply h.2.2
    exact negative_grid_bound d k hθ hθπ

-- Numerators 2j and 2j-1 are precisely the two b-grid definitions.
namespace FiolDoubleHubCentral
noncomputable def t (x : ℝ) := 2*Real.cos x
noncomputable def ell (x : ℝ) := 2*Real.cos (x/2)
noncomputable def u (d x : ℝ) := 2*Real.cos (d*x/2)
noncomputable def v (d x : ℝ) := 2*Real.cos ((d+1)*x/2)
def A (d : ℝ) := 2*d^4
noncomputable def B (d : ℝ) := (3/2 : ℝ)*d^2*(d^2-1)
def C (d : ℝ) := 4*d*(d-1)*(2*d-1)
def E (d : ℝ) := 8*d*(2*d-1)
private def alpha (d : ℝ) := 4*d^2+6*d-1
private noncomputable def beta (d : ℝ) := (3*d^4-19*d^2+8*d+8)/2
private def gamma (d : ℝ) := 32*d-14
noncomputable def f (d x : ℝ) := alpha d*x^2-beta d*x-gamma d
noncomputable def F (d x : ℝ) :=
  A d*t x*(v d x)^2 + ell x*((B d+C d+E d)*t x-E d)*u d x*v d x +
    f d (t x)*(u d x)^2

private theorem central_values (r : ℕ) :
    u (4*(r:ℝ)+2) (Real.pi/2) = 0 ∧
    v (4*(r:ℝ)+2) (Real.pi/2) = -Real.sqrt 2 * (-1:ℝ)^r ∧
    Real.sin ((4*(r:ℝ)+2)*(Real.pi/2)/2) = (-1:ℝ)^r := by
  have ha : (4*(r:ℝ)+2)*(Real.pi/2)/2 = Real.pi/2+(r:ℝ)*Real.pi := by ring
  have hb : ((4*(r:ℝ)+2)+1)*(Real.pi/2)/2 =
      Real.pi/4+Real.pi/2+(r:ℝ)*Real.pi := by ring
  simp only [u,v,ha,hb,Real.cos_add_nat_mul_pi,Real.sin_add_nat_mul_pi,
    Real.cos_pi_div_two,Real.sin_pi_div_two,mul_zero,mul_one]
  rw [Real.cos_add_pi_div_two,Real.sin_pi_div_four]
  constructor
  · trivial
  constructor
  · ring
  · trivial

theorem central_derivative (r : ℕ) :
    F (4*(r:ℝ)+2) (Real.pi/2) = 0 ∧
    HasDerivAt (F (4*(r:ℝ)+2))
      (-4*A (4*(r:ℝ)+2)-2*(4*(r:ℝ)+2)*E (4*(r:ℝ)+2)) (Real.pi/2) := by
  let d : ℝ := 4*(r:ℝ)+2
  let x₀ : ℝ := Real.pi/2
  have hu0 : u d x₀ = 0 := (central_values r).1
  have hv0 : v d x₀ = -Real.sqrt 2 * (-1:ℝ)^r := (central_values r).2.1
  have ht0 : t x₀ = 0 := by simp [t,x₀]
  have hl0 : ell x₀ = Real.sqrt 2 := by
    dsimp [ell,x₀]
    rw [show Real.pi/2/2=Real.pi/4 by ring, Real.cos_pi_div_four]
    ring
  have ht : HasDerivAt t (-2) x₀ := by
    change HasDerivAt (fun x : ℝ => 2*Real.cos x) (-2) x₀
    simpa only [x₀,Real.sin_pi_div_two,mul_neg,mul_one] using
      (Real.hasDerivAt_cos x₀).const_mul 2
  have harg : HasDerivAt (fun x : ℝ => d*x/2) (d/2) x₀ := by
    convert ((hasDerivAt_id x₀).const_mul d).div_const 2 using 1 <;> simp
  have hu : HasDerivAt (u d) (-d*(-1:ℝ)^r) x₀ := by
    change HasDerivAt (fun x : ℝ => 2*Real.cos (d*x/2)) _ _
    have h := ((Real.hasDerivAt_cos (d*x₀/2)).comp x₀ harg).const_mul 2
    convert h using 1
    · rfl
    · change -d*(-1:ℝ)^r = 2*(-Real.sin ((4*(r:ℝ)+2)*(Real.pi/2)/2)*(d/2))
      rw [(central_values r).2.2]
      ring
  have hv : DifferentiableAt ℝ (v d) x₀ := by
    change DifferentiableAt ℝ (fun x : ℝ => 2*Real.cos ((d+1)*x/2)) x₀
    fun_prop
  let b (x : ℝ) := ell x*((B d+C d+E d)*t x-E d)
  have hb : DifferentiableAt ℝ b x₀ := by dsimp [b,ell,t]; fun_prop
  let g (x : ℝ) := f d (t x)
  have hg : DifferentiableAt ℝ g x₀ := by dsimp [g,f,t]; fun_prop
  constructor
  · change F d x₀ = 0
    simp [F,hu0,ht0]
  · change HasDerivAt (F d) (-4*A d-2*d*E d) x₀
    have h := (((ht.mul (hv.hasDerivAt.pow 2)).const_mul (A d)).add
      ((hb.hasDerivAt.mul hu).mul hv.hasDerivAt)).add
        (hg.hasDerivAt.mul (hu.pow 2))
    convert h using 1
    · funext x
      dsimp [F,b,g]
      ring
    · have hs : ((-1:ℝ)^r)^2 = 1 := by
        rw [← pow_mul, mul_comm r 2, pow_mul]
        norm_num
      have hr : (Real.sqrt 2)^2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
      simp only [pow_two,Pi.mul_apply,Nat.reduceSub,Nat.cast_ofNat,pow_one]
      simp only [hu0,ht0,hv0,b,hl0,zero_mul,mul_zero,zero_pow,
        zero_add,add_zero]
      calc
        _ = -2*A d*((Real.sqrt 2)^2*((-1:ℝ)^r)^2) -
            d*E d*((Real.sqrt 2)^2*((-1:ℝ)^r)^2) := by rw [hr,hs]; ring
        _ = _ := by ring

end FiolDoubleHubCentral

end D5.S3.Zeros.LeeYang
