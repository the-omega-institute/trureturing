/- GID: D5/S3/Quantum/Recovery/PrincipalPlaquetteGaugeBudget
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PrincipalPlaquetteGaugeBudget
   mirror-E: none(waiver:principal-plaquette-gauge-budget)
   anchors: []
   utility: none
   digest: Checkerboard gauge and coherent error budgets for two contracting blocks. -/


import D5.S3.Quantum.Recovery.PrincipalPlaquettePhaseDiamond
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic


/-!
# Scalar and complex budgets for a checkerboard plaquette

The reusable two-block implications below combine modulus and projected error
budgets. Native channel witnesses are constructed by the importing module.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Quantum.Recovery.PrincipalPlaquetteGaugeBudget


section

namespace RTWeightBudget
open scoped BigOperators

/-- Four signed aligned errors explain the full sharp real-plaquette
constant when both a coherent budget and a squared budget are available. -/
theorem sharp_zero_phase_of_square_and_sum (e : Fin 4 → ℝ) (δ : ℝ)
    (hδ' : δ < 1/2)
    (hentry : ∀ i, e i ≤ δ)
    (hcoherent : (∑ i, e i) ≤ 2 * δ)
    (hF : (∑ i, (e i)^2) ≤ 2 * δ^2)
    (hsqrt : (∑ i, Real.sqrt (1/2 - e i)) ≤ 2) :
    Real.sqrt 2 - 1 ≤ δ := by
  let s := Real.sqrt (1/2)
  let b := Real.sqrt (1/2 - δ)
  let x (i : Fin 4) := Real.sqrt (1/2 - e i)
  have hs : 0 < s := Real.sqrt_pos.2 (by norm_num)
  have hss : s^2 = 1/2 := Real.sq_sqrt (by norm_num)
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hbb : b^2 = 1/2 - δ := Real.sq_sqrt (by linarith)
  have hxx (i : Fin 4) : (x i)^2 = 1/2 - e i :=
    Real.sq_sqrt (by linarith [hentry i])
  have hbx (i : Fin 4) : b ≤ x i := Real.sqrt_le_sqrt (by linarith [hentry i])
  have hsb : 0 < s + b := by positivity
  have hM : 0 < (s+b)^2 := pow_pos hsb 2
  have hentry' (i : Fin 4) : (s+b)^2 * (s-x i)^2 ≤ (e i)^2 := by
    have hle : (s+b)^2 ≤ (s+x i)^2 :=
      pow_le_pow_left₀ hsb.le (add_le_add le_rfl (hbx i)) 2
    apply (mul_le_mul_of_nonneg_right hle (sq_nonneg (s-x i))).trans
    rw [← mul_pow]
    have hprod : (s+x i)*(s-x i) = e i := by
      linear_combination hss - hxx i
    rw [hprod]
  have hdiff : (∑ i, (s-x i)^2) ≤ 2*(s-b)^2 := by
    apply (mul_le_mul_iff_of_pos_left hM).mp
    rw [Finset.mul_sum]
    calc
      (∑ i, (s+b)^2 * (s-x i)^2) ≤ ∑ i, (e i)^2 :=
        Finset.sum_le_sum fun i _ => hentry' i
      _ ≤ 2*δ^2 := hF
      _ = (s+b)^2 * (2*(s-b)^2) := by
        have hprod : (s+b)*(s-b) = δ := by linear_combination hss - hbb
        rw [← hprod]
        ring
  have hexpand (i : Fin 4) : e i + (s-x i)^2 = 2*s*(s-x i) := by
    linear_combination hxx i - hss
  have hsum : (∑ i : Fin 4, (e i + (s-x i)^2)) = ∑ i : Fin 4, 2*s*(s-x i) :=
    Finset.sum_congr rfl (fun i _ => hexpand i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  change (∑ i, x i) ≤ 2 at hsqrt
  have hmul := mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ 2*s by positivity)
  have hsb' : 2*s*b ≤ 2*s*(1-s) := by
    norm_num at hsum
    nlinarith only [hss, hbb, hsum, hcoherent, hdiff, hmul]
  have hbs : b ≤ 1-s := (mul_le_mul_iff_of_pos_left (show 0 < 2*s by positivity)).mp
    (by simpa only [mul_assoc] using hsb')
  have hsquare : b^2 ≤ (1-s)^2 := pow_le_pow_left₀ hb hbs 2
  have hrs : Real.sqrt 2 = 2*s := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg 2) (by positivity)).mp
    rw [Real.sq_sqrt (by norm_num)]
    nlinarith only [hss]
  rw [hrs]
  nlinarith only [hsquare, hss, hbb]

private theorem sharp_zero_phase_gauge (r y e : Fin 4 → ℝ) (δ : ℝ)
    (hδ : δ < 1 / 2) (hr : ∀ i, 0 ≤ r i)
    (hrsum : (∑ i, r i) ≤ 2) (hysum : (∑ i, y i) ≤ 2)
    (hg : ∀ i, r i * y i = 1 / 2 - e i)
    (he : ∀ i, e i ≤ δ) (hcoherent : (∑ i, e i) ≤ 2 * δ)
    (hF : (∑ i, (e i)^2) ≤ 2 * δ^2) :
    Real.sqrt 2 - 1 ≤ δ := by
  have hy (i : Fin 4) : 0 ≤ y i := by
    have hprod : 0 < r i * y i := by rw [hg i]; linarith [he i]
    exact (pos_of_mul_pos_right hprod (hr i)).le
  let q : Fin 4 → ℝ := fun i => Real.sqrt (1 / 2 - e i)
  have hq (i : Fin 4) : (q i)^2 ≤ r i * y i := by
    rw [hg i]
    exact (Real.sq_sqrt (by linarith [he i])).le
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun i _ => hr i) (fun i _ => hy i) (fun i _ => hq i)
  have hy0 : 0 ≤ ∑ i, y i := Finset.sum_nonneg fun i _ => hy i
  have hprod : (∑ i, r i) * (∑ i, y i) ≤ 4 := by
    calc
      _ ≤ 2 * (∑ i, y i) := mul_le_mul_of_nonneg_right hrsum hy0
      _ ≤ _ := by linarith
  have hsum : (∑ i, q i) ≤ 2 :=
    (sq_le_sq₀ (Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _) (by norm_num)).mp
      (by norm_num; exact hcs.trans hprod)
  exact sharp_zero_phase_of_square_and_sum e δ hδ he hcoherent hF hsum

private theorem phase_necessary_of_square_and_sum (e : Fin 4 → ℝ) (p q δ : ℝ)
    (hp : 0 < p) (hδ' : δ ≤ p/2)
    (hentry : ∀ i, e i ≤ δ)
    (hcoherent : (∑ i, e i) ≤ 2*(p+q)*δ)
    (hF : (∑ i, (e i)^2) ≤ 2 * δ^2)
    (hsqrt : (∑ i, Real.sqrt (p/2 - e i)) ≤ 2 / Real.sqrt p) :
    p+(1-p-q)*δ+Real.sqrt (p^2-2*p*δ) ≤ Real.sqrt 2 := by
  let s := Real.sqrt (p/2)
  let b := Real.sqrt (p/2 - δ)
  let x (i : Fin 4) := Real.sqrt (p/2 - e i)
  have hs : 0 < s := Real.sqrt_pos.2 (by linarith)
  have hss : s^2 = p/2 := Real.sq_sqrt (by linarith)
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hbb : b^2 = p/2 - δ := Real.sq_sqrt (by linarith)
  have hxx (i : Fin 4) : (x i)^2 = p/2 - e i :=
    Real.sq_sqrt (by linarith [hentry i])
  have hbx (i : Fin 4) : b ≤ x i := Real.sqrt_le_sqrt (by linarith [hentry i])
  have hsb : 0 < s + b := by positivity
  have hM : 0 < (s+b)^2 := pow_pos hsb 2
  have hentry' (i : Fin 4) : (s+b)^2 * (s-x i)^2 ≤ (e i)^2 := by
    have hle : (s+b)^2 ≤ (s+x i)^2 :=
      pow_le_pow_left₀ hsb.le (add_le_add le_rfl (hbx i)) 2
    apply (mul_le_mul_of_nonneg_right hle (sq_nonneg (s-x i))).trans
    rw [← mul_pow]
    have hprod : (s+x i)*(s-x i) = e i := by
      linear_combination hss - hxx i
    rw [hprod]
  have hdiff : (∑ i, (s-x i)^2) ≤ 2*(s-b)^2 := by
    apply (mul_le_mul_iff_of_pos_left hM).mp
    rw [Finset.mul_sum]
    calc
      (∑ i, (s+b)^2 * (s-x i)^2) ≤ ∑ i, (e i)^2 :=
        Finset.sum_le_sum fun i _ => hentry' i
      _ ≤ 2*δ^2 := hF
      _ = (s+b)^2 * (2*(s-b)^2) := by
        have hprod : (s+b)*(s-b) = δ := by linear_combination hss - hbb
        rw [← hprod]
        ring
  have hexpand (i : Fin 4) : e i + (s-x i)^2 = 2*s*(s-x i) := by
    linear_combination hxx i - hss
  have hsum : (∑ i : Fin 4, (e i + (s-x i)^2)) = ∑ i : Fin 4, 2*s*(s-x i) :=
    Finset.sum_congr rfl (fun i _ => hexpand i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  change (∑ i, x i) ≤ 2 / Real.sqrt p at hsqrt
  have hsp : Real.sqrt p = Real.sqrt 2*s := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hp.le, Real.sq_sqrt (by norm_num), hss]
    ring
  have hroot := (le_div_iff₀ (Real.sqrt_pos.2 hp)).1 hsqrt
  rw [hsp] at hroot
  have hm := mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg 2)
  have hmul : (∑ i, x i) * (Real.sqrt 2*s) * Real.sqrt 2 = 2*s*(∑ i, x i) := by
    calc
      _ = (Real.sqrt 2)^2*s*(∑ i, x i) := by ring
      _ = _ := by rw [Real.sq_sqrt (by norm_num)]
  rw [hmul] at hm
  have hsqrt' : Real.sqrt (p^2-2*p*δ) = 2*s*b := by
    rw [show p^2-2*p*δ = (2*s*b)^2 by
      rw [mul_pow, mul_pow, hss, hbb]
      ring]
    rw [Real.sqrt_sq (by positivity)]
  rw [hsqrt']
  norm_num at hsum
  nlinarith only [hss,hbb,hsum,hcoherent,hdiff,hm]

/-- A rational phase threshold for exclusion of the closed quarter sublevel. -/
theorem quarter_cutoff_tight_rational (e : Fin 4 → ℝ) (p q δ : ℝ)
    (hp : 899228/1000000 ≤ p) (hp' : p ≤ 1)
    (hq : 0 ≤ q) (hcircle : q^2 = 1-p^2)
    (hδ : δ ≤ 1/4)
    (hentry : ∀ i, e i ≤ δ)
    (hcoherent : (∑ i, e i) ≤ 2*(p+q)*δ)
    (hF : (∑ i, (e i)^2) ≤ 2 * δ^2)
    (hsqrt : (∑ i, Real.sqrt (p/2 - e i)) ≤ 2 / Real.sqrt p) : False := by
  have hp0 : 0 < p := by linarith
  have h := phase_necessary_of_square_and_sum e p q δ hp0 (by linarith)
    hentry hcoherent hF hsqrt
  have hpp : (899228/1000000:ℝ)^2 ≤ p^2 := pow_le_pow_left₀ (by norm_num) hp 2
  have hqmax : q ≤ 43748029/100000000 := by
    apply (sq_le_sq₀ hq (by norm_num)).mp
    nlinarith only [hcircle,hpp]
  have hpsum : 1 ≤ p+q := by
    have hsq : (1-p)^2 ≤ q^2 := by
      nlinarith only [hcircle, mul_nonneg hp0.le (sub_nonneg.mpr hp')]
    have := (sq_le_sq₀ (sub_nonneg.mpr hp') hq).mp hsq
    linarith
  have hrad : (29958179/50000000:ℝ)^2 ≤ p^2-2*p*δ := by
    have hh : (399228/1000000:ℝ) ≤ p-2*δ := by linarith
    have hm := mul_le_mul hp hh (by norm_num : (0:ℝ) ≤ 399228/1000000) hp0.le
    nlinarith only [hm]
  have hsr : 29958179/50000000 ≤ Real.sqrt (p^2-2*p*δ) := by
    apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by linarith)]
    exact hrad
  have hl := mul_le_mul_of_nonpos_left hδ (show 1-p-q ≤ 0 by linarith)
  have hb : (565685803/400000000:ℝ) ≤ Real.sqrt 2 := by linarith only [h,hp,hqmax,hsr,hl]
  have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 565685803/400000000) hb 2
  rw [Real.sq_sqrt (by norm_num)] at hh
  norm_num at hh

/-- The reciprocal variance budget gives a strict improvement over the
interval-only weight bound. The four denominators have arithmetic mean at most
one after normalization; their reciprocals then have a controlled second moment. -/
theorem one_party_gauge_block_lower_of_sum (r y e : Fin 4 → ℝ) (p δ : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hd : 0 ≤ δ)
    (hr : ∀ i, 1/2-δ ≤ r i)
    (hg : ∀ i, r i * y i = p/2-e i)
    (hy : (∑ i, y i) ≤ 2)
    (hsum : (∑ i, r i) ≤ 2/p)
    (hF : (∑ i, e i ^ 2) ≤ 2*δ^2) :
    Real.sqrt 2 * (p/2-1/(4*p)) ≤ δ := by
  let d : ℝ := p/2-1/(4*p)
  change Real.sqrt 2 * d ≤ δ
  by_contra! hlt
  have hsqrt : Real.sqrt (2 : ℝ) ≤ 2 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
    rw [Real.sq_sqrt (by norm_num)]
    norm_num
  have hrec : (1/4 : ℝ) ≤ 1/(4*p) :=
    (le_div_iff₀ (by positivity)).2 (by linarith)
  have hsmall : δ < 1/2 := by
    have h := mul_le_mul_of_nonneg_left (show d ≤ 1/4 by dsimp [d]; linarith)
      (Real.sqrt_nonneg 2)
    linarith
  have hpd : p*d = p^2/2-1/4 := by dsimp [d]; field_simp
  let a : Fin 4 → ℝ := fun i => 2*p*r i
  have ha0 (i : Fin 4) : 0 < a i := by
    dsimp [a]
    exact mul_pos (by positivity) (by linarith only [hr i, hsmall])
  let t : Fin 4 → ℝ := fun i => 1/a i
  have hat (i : Fin 4) : a i*t i = 1 := mul_one_div_cancel (ha0 i).ne'
  have ht0 (i : Fin 4) : 0 < t i := one_div_pos.mpr (ha0 i)
  have hsa : (∑ i, a i) ≤ 4 := by
    simp only [a, ← Finset.mul_sum]
    have h := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2*p by positivity)
    have h' : 2*p*(2/p) = 4 := by field_simp; norm_num
    rwa [h'] at h
  let D : ℝ := (∑ i, t i)-4
  have hD : 0 ≤ D := by
    have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      (r := fun _ : Fin 4 => (1 : ℝ)) (f := a) (g := t) Finset.univ
      (fun i _ => (ha0 i).le) (fun i _ => (ht0 i).le)
      (fun i _ => by rw [hat, one_pow])
    norm_num at h
    have htSum : 0 ≤ ∑ i, t i := Finset.sum_nonneg (fun i _ => (ht0 i).le)
    dsimp [D]
    linarith only [h.trans (mul_le_mul_of_nonneg_right hsa htSum)]
  have hvariance : (∑ i, a i*(t i-1)^2) ≤ D := by
    have hid (i : Fin 4) : a i*(t i-1)^2 = t i-2+a i := by
      linear_combination (t i-2)*(hat i)
    simp_rw [hid, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    norm_num
    dsimp [D]
    linarith only [hsa]
  have ht (i : Fin 4) : t i ≤ 2+D := by
    have h₁ := Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin 4 => a j*(t j-1)^2)
      (fun j _ => mul_nonneg (ha0 j).le (sq_nonneg (t j-1))) (Finset.mem_univ i)
    have h₂ : a i*(t i-1)^2 = t i-2+a i := by
      linear_combination (t i-2)*(hat i)
    rw [h₂] at h₁
    linarith only [h₁.trans hvariance, (ha0 i).le]
  have htvar : (∑ i, (t i-1)^2) ≤ (2+D)*D := by
    calc
      _ ≤ ∑ i, (2+D)*(a i*(t i-1)^2) := by
        apply Finset.sum_le_sum
        intro i _
        have h := mul_le_mul_of_nonneg_right (ht i)
          (mul_nonneg (ha0 i).le (sq_nonneg (t i-1)))
        calc
          (t i-1)^2 = t i*(a i*(t i-1)^2) := by
            rw [← mul_assoc, mul_comm (t i) (a i), hat, one_mul]
          _ ≤ _ := h
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left hvariance (by linarith)
  let A : ℝ := ∑ i, t i ^ 2
  let S : ℝ := ∑ i, t i * e i
  have hA : A ≤ (2+D)^2 := by
    have h : (∑ i, (t i-1)^2) = A-2*(∑ i, t i)+4 := by
      simp_rw [show ∀ z : ℝ, (z-1)^2 = z^2-2*z+1 by intro; ring,
        Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      norm_num [A]
    rw [h] at htvar
    have hD' : D = (∑ i, t i)-4 := rfl
    calc
      A ≤ 2*(∑ i, t i)-4+(2+D)*D := by linarith only [htvar]
      _ = (2+D)^2 := by rw [show (∑ i, t i) = D+4 by linarith only [hD']]; ring
  have hpoint (i : Fin 4) : t i*e i = (p/2)*t i-(1/(2*p))*y i := by
    have hh := congrArg (fun z : ℝ => t i*z) (hg i)
    have ht' : t i*r i = 1/(2*p) := by
      apply (eq_div_iff (show 2*p ≠ 0 by positivity)).2
      calc
        _ = a i*t i := by dsimp [a]; ring
        _ = 1 := hat i
    change t i*(r i*y i) = t i*(p/2-e i) at hh
    rw [← mul_assoc, ht'] at hh
    linarith only [hh]
  have hS : 4*d+(p/2)*D ≤ S := by
    dsimp [S]
    simp_rw [hpoint, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have h := mul_le_mul_of_nonneg_left hy (show 0 ≤ 1/(2*p) by positivity)
    have he : 2*(1/(2*p)) = 1/p := by field_simp
    rw [mul_comm _ (2 : ℝ), he] at h
    have he' : 4*(1/(4*p)) = 1/p := by field_simp
    dsimp [D, d]
    nlinarith only [h, he']
  have hscale : 2*d ≤ p/2 := by
    have h := mul_le_mul_of_nonneg_left hp1 hp.le
    apply le_of_mul_le_mul_left ?_ hp
    nlinarith only [h, hpd, hp1]
  have hSd : 2*(2+D)*d ≤ S := by
    nlinarith only [hS, mul_le_mul_of_nonneg_right hscale hD]
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun i _ => sq_nonneg (t i))
  have hK : 0 < 2+D := by linarith
  have hSq : S^2 ≤ ((2+D)*(Real.sqrt 2*δ))^2 := calc
    _ ≤ A*(∑ i, e i^2) := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ t e
    _ ≤ A*(2*δ^2) := mul_le_mul_of_nonneg_left hF hA0
    _ ≤ (2+D)^2*(2*δ^2) := mul_le_mul_of_nonneg_right hA (by positivity)
    _ = _ := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
  have hroot := mul_lt_mul_of_pos_left hlt (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<2))
  rw [← mul_assoc, ← pow_two, Real.sq_sqrt (by norm_num)] at hroot
  have hStrict : (2+D)*(Real.sqrt 2*δ) < S := calc
    _ < (2+D)*(2*d) := mul_lt_mul_of_pos_left hroot hK
    _ = 2*(2+D)*d := by ring
    _ ≤ S := hSd
  have hnon : 0 ≤ (2+D)*(Real.sqrt 2*δ) := by positivity
  have hh := mul_pos (sub_pos.mpr hStrict) (show 0 < S+(2+D)*(Real.sqrt 2*δ) by linarith)
  nlinarith only [hh, hSq]

end RTWeightBudget

end

section

namespace RTMultiFibre

open Matrix
open scoped Matrix ComplexOrder BigOperators
open D5.S3.Quantum.Recovery.PrincipalPlaquettePhaseDiamond

private def projectedError (x y s u : ℂ) : ℝ :=
  (star (s*x*u) * ((1/2 : ℂ)-x*y)).re / ‖x‖

private theorem opposite_gauge_exact {x y s u : ℂ} {p : ℝ}
    (hx : x ≠ 0) (hs : ‖s‖ = 1) (hu : ‖u‖ = 1)
    (hre : (s*x*u).re = p*‖x‖) :
    ‖x‖ * (star s*y*star u).re = p/2-projectedError x y s u ∧
      (projectedError x y s u)^2 ≤ ‖(1/2 : ℂ)-x*y‖^2 := by
  let x' := s*x*u
  let y' := star s*y*star u
  have unit (z : ℂ) (h : ‖z‖ = 1) : z * star z = 1 := by
    rw [Complex.star_def, Complex.mul_conj, ← Complex.sq_norm, h]; norm_num
  have hprod : x'*y' = x*y := by
    calc
      x'*y' = (s*star s)*(u*star u)*(x*y) := by dsimp [x', y']; ring
      _ = _ := by rw [unit s hs, unit u hu, one_mul, one_mul]
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
  have hp0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hn : ‖star x' * ((1/2 : ℂ)-x*y)‖ = ‖x‖ * ‖(1/2 : ℂ)-x*y‖ := by
    rw [Complex.norm_mul, norm_star, hnorm]
  change ‖x‖ * y'.re = _ ∧ _
  constructor
  · unfold projectedError
    change ‖x‖ * y'.re = p/2 - (star x' * ((1/2 : ℂ)-x*y)).re / ‖x‖
    rw [← hprod, hp, hnorm, show x'.re = p*‖x‖ from hre]
    field_simp
    ring
  · have hh := Complex.abs_re_le_norm (star x' * ((1/2 : ℂ)-x*y))
    rw [hn] at hh
    unfold projectedError
    have hq : |(star x' * ((1/2 : ℂ)-x*y)).re / ‖x‖| ≤ ‖(1/2 : ℂ)-x*y‖ := by
      rw [abs_div, abs_of_pos hp0]
      exact (div_le_iff₀ hp0).2 (by simpa only [mul_comm] using hh)
    exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 hq |>.trans_eq' (sq_abs _)

open D5.S3.Quantum.Recovery.PrincipalTrianglePhase.RTPhaseBarrier

private theorem projectedError_of_phase {x y l m : ℂ} {α : ℝ}
    (hx : x ≠ 0) (h : l * x * m = (‖x‖ : ℂ) * cis α) :
    projectedError x y l m = Real.cos α * ((1 / 2 : ℂ) - x * y).re +
      Real.sin α * ((1 / 2 : ℂ) - x * y).im := by
  have sIm : (cis α).im = Real.sin α := by
    unfold cis
    simp [Complex.exp_mul_I, Complex.sin_ofReal_re]
  unfold projectedError
  rw [h, star_mul, Complex.star_def, Complex.conj_ofReal]
  have hreal (r : ℝ) (z : ℂ) : ((r : ℂ) * z).re = r * z.re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [mul_comm (starRingEnd ℂ (cis α)) (↑‖x‖ : ℂ), mul_assoc, hreal, mul_div_cancel_left₀ _ (norm_ne_zero_iff.mpr hx)]
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, cis_re, sIm]
  ring

private theorem signed_projection_sum_le {a b c d : ℂ} {p s δ : ℝ}
    (hp : 0 ≤ p) (h0 : ‖a+b+(c+d)‖ ≤ 2*δ) (h1 : ‖a-b-c+d‖ ≤ 2*δ) :
    (p*a.re+s*a.im) + (p*b.re-s*b.im) +
      ((p*c.re-s*c.im) + (p*d.re+s*d.im)) ≤ 2*(p+|s|)*δ := by
  have hr := mul_le_mul_of_nonneg_left ((Complex.re_le_norm _).trans h0) hp
  have hp' : s * (a-b-c+d).im ≤ |s| * (2*δ) := by
    calc
      _ ≤ |s * (a-b-c+d).im| := le_abs_self _
      _ = |s| * |(a-b-c+d).im| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm _).trans h1) (abs_nonneg _)
  simp only [Complex.add_re, Complex.add_im, Complex.sub_im] at hr hp'
  linarith only [hr, hp']

private theorem projectedError_of_zero_gauge {x y s u : ℂ}
    (h : x ≠ 0) (hs : ‖s‖ = 1) (hu : ‖u‖ = 1)
    (hre : (s * x * u).re = ‖x‖) :
    projectedError x y s u = ((1 / 2 : ℂ) - x * y).re := by
  let z := s * x * u
  have hn : ‖z‖ = ‖x‖ := by simp [z, hs, hu]
  have hi : z.im = 0 := by
    have he := Complex.sq_norm z
    rw [hn, Complex.normSq_apply, hre] at he
    have hi' : z.im ^ 2 = 0 := by nlinarith only [he]
    simpa using hi'
  have hz : z = ((‖x‖ : ℝ) : ℂ) := Complex.ext (by simpa [z] using hre) (by simpa using hi)
  unfold projectedError
  change (star z * ((1 / 2 : ℂ) - x * y)).re / ‖x‖ = _
  rw [hz, Complex.star_def, Complex.conj_ofReal, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_div_cancel_left₀ _ (norm_ne_zero_iff.mpr h)

private theorem contraction_entry_bounds {a b c d : ℂ} (h : IsTwoContraction a b c d) :
    ‖a‖ ≤ 1 ∧ ‖b‖ ≤ 1 ∧ ‖c‖ ≤ 1 ∧ ‖d‖ ≤ 1 := by
  have h0 := h 1 0
  have h1 := h 0 1
  norm_num at h0 h1
  exact ⟨(sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp (by nlinarith [sq_nonneg ‖c‖]),
    (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp (by nlinarith [sq_nonneg ‖d‖]),
    (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp (by nlinarith [sq_nonneg ‖a‖]),
    (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp (by nlinarith [sq_nonneg ‖b‖])⟩

/-- A block Frobenius error budget strengthens the one-party phase obstruction. -/
theorem improved_plaquette_of_frobenius {a b c d A B C D : ℂ} {δ : ℝ}
    (hX : IsTwoContraction a b c d) (hY : IsTwoContraction A B C D)
    (h0 : ‖(1/2 : ℂ)-a*A‖ ≤ δ) (h1 : ‖(1/2 : ℂ)-b*B‖ ≤ δ)
    (h2 : ‖(1/2 : ℂ)-c*C‖ ≤ δ) (h3 : ‖(1/2 : ℂ)-d*D‖ ≤ δ)
    (hF : ‖(1/2 : ℂ)-a*A‖^2 + ‖(1/2 : ℂ)-b*B‖^2 +
        (‖(1/2 : ℂ)-c*C‖^2 + ‖(1/2 : ℂ)-d*D‖^2) ≤ 2*δ^2) :
    let θ := plaquetteArg a b c d
    let p := Real.cos (θ/4)
    Real.sqrt 2 * (p/2-1/(4*p)) ≤ δ := by
  let θ := plaquetteArg a b c d
  let p := Real.cos (θ/4)
  change Real.sqrt 2 * (p/2-1/(4*p)) ≤ δ
  have hθ := plaquette_arg_abs_le_pi a b c d
  change |θ| ≤ Real.pi at hθ
  have hp0 : 0 < p := by
    change 0 < Real.cos (θ/4)
    apply Real.cos_pos_of_mem_Ioo
    constructor <;>
      linarith [le_abs_self θ, neg_abs_le θ, Real.pi_pos]
  have hp1 : p ≤ 1 := Real.cos_le_one _
  by_cases hsmall : δ < 1/2
  · obtain ⟨ya,yb,yc,yd⟩ := contraction_entry_bounds hY
    have lower {x y : ℂ} (hb : ‖y‖ ≤ 1)
        (h : ‖(1/2 : ℂ)-x*y‖ ≤ δ) : 1/2-δ ≤ ‖x‖ := by
      exact (matrix_unit_product_floor h).trans
        (by simpa using mul_le_mul_of_nonneg_left hb (norm_nonneg x))
    have za := lower ya h0
    have zb := lower yb h1
    have zc := lower yc h2
    have zd := lower yd h3
    have nz {x : ℂ} (h : 1/2-δ ≤ ‖x‖) : x ≠ 0 :=
      norm_pos_iff.mp (by linarith)
    obtain ⟨s,t,u,v,hs,ht,hu,hv,ha,hb,hc,hd⟩ :=
      shared_checkerboard_gauge a b c d θ (plaquette_arg_angle (nz za) (nz zb) (nz zc) (nz zd))
    obtain ⟨aa,aa2⟩ := opposite_gauge_exact (nz za) hs hu ha
    obtain ⟨ab,ab2⟩ := opposite_gauge_exact (nz zb) hs hv hb
    obtain ⟨ac,ac2⟩ := opposite_gauge_exact (nz zc) ht hu hc
    obtain ⟨ad,ad2⟩ := opposite_gauge_exact (nz zd) ht hv hd
    let r : Fin 4 → ℝ := ![‖a‖,‖b‖,‖c‖,‖d‖]
    let y : Fin 4 → ℝ := ![(star s*A*star u).re, (star s*B*star v).re,
      (star t*C*star u).re, (star t*D*star v).re]
    let e : Fin 4 → ℝ := ![projectedError a A s u, projectedError b B s v,
      projectedError c C t u, projectedError d D t v]
    apply RTWeightBudget.one_party_gauge_block_lower_of_sum r y e p δ hp0 hp1
      ((norm_nonneg _).trans h0)
    · intro i
      fin_cases i <;> first | exact za | exact zb | exact zc | exact zd
    · intro i
      fin_cases i <;> first | exact aa | exact ab | exact ac | exact ad
    · have h := (Complex.re_le_norm _).trans
        (contraction_flat_test hY (star s) (star t) (star u) (star v)
          (by simpa using hs) (by simpa using ht) (by simpa using hu) (by simpa using hv))
      rw [show star s*(A*star u+B*star v)+star t*(C*star u+D*star v) =
        ((star s*A*star u+star s*B*star v)+star t*C*star u)+star t*D*star v by ring] at h
      simp only [Complex.add_re] at h
      simp only [y, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Fin.sum_univ_zero, add_zero]
      simpa only [add_assoc] using h
    · have h := contraction_modulus_budget hX s t u v hs ht hu hv ha hb hc hd
      apply (le_div_iff₀ hp0).2
      simp [r, Fin.sum_univ_succ]
      nlinarith only [h]
    · simp [e, Fin.sum_univ_succ]
      linarith only [aa2,ab2,ac2,ad2,hF]
  · have hrec : (1/4 : ℝ) ≤ 1/(4*p) :=
      (le_div_iff₀ (by positivity)).2 (by linarith)
    have hsqrt : Real.sqrt (2 : ℝ) ≤ 2 := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
      rw [Real.sq_sqrt (by norm_num)]
      norm_num
    have h := mul_le_mul_of_nonneg_left
      (show p/2-1/(4*p) ≤ 1/4 by linarith) (Real.sqrt_nonneg 2)
    linarith

/-- The zero-phase scalar endpoint uses the flat sum in addition to the
row-wise squared error budget. -/
theorem sharp_zero_plaquette_of_coherent {a b c d A B C D : ℂ} {δ : ℝ}
    (hX : IsTwoContraction a b c d) (hY : IsTwoContraction A B C D)
    (hθ : plaquetteArg a b c d = 0)
    (h0 : ‖(1/2 : ℂ)-a*A‖ ≤ δ) (h1 : ‖(1/2 : ℂ)-b*B‖ ≤ δ)
    (h2 : ‖(1/2 : ℂ)-c*C‖ ≤ δ) (h3 : ‖(1/2 : ℂ)-d*D‖ ≤ δ)
    (hF : ‖(1/2 : ℂ)-a*A‖^2 + ‖(1/2 : ℂ)-b*B‖^2 +
        (‖(1/2 : ℂ)-c*C‖^2 + ‖(1/2 : ℂ)-d*D‖^2) ≤ 2*δ^2)
    (hcoherent : ((1/2 : ℂ)-a*A).re + ((1/2 : ℂ)-b*B).re +
        (((1/2 : ℂ)-c*C).re + ((1/2 : ℂ)-d*D).re) ≤ 2*δ) :
    Real.sqrt 2 - 1 ≤ δ := by
  by_cases hsmall : δ < 1/2
  · obtain ⟨ya,yb,yc,yd⟩ := contraction_entry_bounds hY
    have nz {x y : ℂ} (hb : ‖y‖ ≤ 1)
        (h : ‖(1/2 : ℂ)-x*y‖ ≤ δ) : x ≠ 0 := by
      have lower := (matrix_unit_product_floor h).trans
        (show ‖x‖ * ‖y‖ ≤ ‖x‖ by simpa using mul_le_mul_of_nonneg_left hb (norm_nonneg x))
      exact norm_pos_iff.mp (by linarith)
    have na := nz ya h0
    have nb := nz yb h1
    have nc := nz yc h2
    have nd := nz yd h3
    obtain ⟨s,t,u,v,hs,ht,hu,hv,ha,hb,hc,hd⟩ :=
      shared_checkerboard_gauge a b c d 0 (hθ ▸ plaquette_arg_angle na nb nc nd)
    simp only [zero_div, Real.cos_zero, one_mul] at ha hb hc hd
    let r : Fin 4 → ℝ := ![‖a‖,‖b‖,‖c‖,‖d‖]
    let y : Fin 4 → ℝ := ![(star s*A*star u).re, (star s*B*star v).re,
      (star t*C*star u).re, (star t*D*star v).re]
    let e : Fin 4 → ℝ := ![((1/2 : ℂ)-a*A).re, ((1/2 : ℂ)-b*B).re,
      ((1/2 : ℂ)-c*C).re, ((1/2 : ℂ)-d*D).re]
    have entry {x z l m : ℂ} (hn : x ≠ 0) (hl : ‖l‖ = 1) (hm : ‖m‖ = 1)
        (he : (l*x*m).re = ‖x‖) :
        ‖x‖ * (star l*z*star m).re = 1/2 - ((1/2 : ℂ)-x*z).re ∧
        (((1/2 : ℂ)-x*z).re)^2 ≤ ‖(1/2 : ℂ)-x*z‖^2 := by
      simpa only [projectedError_of_zero_gauge hn hl hm he] using
        opposite_gauge_exact hn hl hm (p := 1) (by simpa using he)
    obtain ⟨aa,aa2⟩ := entry na hs hu ha
    obtain ⟨ab,ab2⟩ := entry nb hs hv hb
    obtain ⟨ac,ac2⟩ := entry nc ht hu hc
    obtain ⟨ad,ad2⟩ := entry nd ht hv hd
    apply RTWeightBudget.sharp_zero_phase_gauge r y e δ hsmall
    · intro i
      fin_cases i <;> exact norm_nonneg _
    · have h := contraction_modulus_budget hX s t u v hs ht hu hv
          (p := 1) (by simpa using ha) (by simpa using hb) (by simpa using hc) (by simpa using hd)
      simpa [r, Fin.sum_univ_succ, add_assoc] using h
    · have h := (Complex.re_le_norm _).trans
        (contraction_flat_test hY (star s) (star t) (star u) (star v)
          (by simpa using hs) (by simpa using ht) (by simpa using hu) (by simpa using hv))
      rw [show star s*(A*star u+B*star v)+star t*(C*star u+D*star v) =
        ((star s*A*star u+star s*B*star v)+star t*C*star u)+star t*D*star v by ring] at h
      simp only [Complex.add_re] at h
      simpa [y, Fin.sum_univ_succ, add_assoc] using h
    · intro i
      fin_cases i <;> first | exact aa | exact ab | exact ac | exact ad
    · intro i
      fin_cases i <;> apply (Complex.re_le_norm _).trans <;>
        first | exact h0 | exact h1 | exact h2 | exact h3
    · simpa [e, Fin.sum_univ_succ, add_assoc] using hcoherent
    · simp only [e, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Fin.sum_univ_zero, add_zero]
      linarith only [aa2,ab2,ac2,ad2,hF]
  · have hsqrt : Real.sqrt (2 : ℝ) ≤ 3/2 := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
      rw [Real.sq_sqrt (by norm_num)]
      norm_num
    linarith

/-- A signed flat probe, used together with the squared row budget, excludes
diamond distance at or below a quarter on a sector of first-side phases. -/
theorem quarter_plaquette_of_signed_coherent
    {a b c d A B C D : ℂ} {δ : ℝ}
    (hX : IsTwoContraction a b c d) (hY : IsTwoContraction A B C D)
    (hcos : 899228/1000000 ≤ Real.cos (plaquetteArg a b c d / 4))
    (h0 : ‖(1/2 : ℂ)-a*A‖ ≤ δ) (h1 : ‖(1/2 : ℂ)-b*B‖ ≤ δ)
    (h2 : ‖(1/2 : ℂ)-c*C‖ ≤ δ) (h3 : ‖(1/2 : ℂ)-d*D‖ ≤ δ)
    (hF : ‖(1/2 : ℂ)-a*A‖^2 + ‖(1/2 : ℂ)-b*B‖^2 +
        (‖(1/2 : ℂ)-c*C‖^2 + ‖(1/2 : ℂ)-d*D‖^2) ≤ 2*δ^2)
    (hsum : ‖((1/2 : ℂ)-a*A) + ((1/2 : ℂ)-b*B) +
        (((1/2 : ℂ)-c*C) + ((1/2 : ℂ)-d*D))‖ ≤ 2*δ)
    (hsigned : ‖((1/2 : ℂ)-a*A) - ((1/2 : ℂ)-b*B) -
        ((1/2 : ℂ)-c*C) + ((1/2 : ℂ)-d*D)‖ ≤ 2*δ) :
    1/4 < δ := by
  by_contra! hsmall
  let θ := plaquetteArg a b c d
  let p := Real.cos (θ/4)
  let q := Real.sin (θ/4)
  have hl : 899228/1000000 ≤ p := hcos
  have hp0 : 0 < p := by linarith
  have hp1 : p ≤ 1 := Real.cos_le_one _
  have hunit : |q|^2 = 1-p^2 := by
    rw [sq_abs]
    have h := Real.sin_sq_add_cos_sq (θ/4)
    linarith
  have nz {x y : ℂ} (h : ‖(1/2 : ℂ)-x*y‖ ≤ δ) : x ≠ 0 := by
    intro hz
    have hfloor := matrix_unit_product_floor h
    rw [hz, norm_zero, zero_mul] at hfloor
    linarith
  obtain ⟨l,k,m,n,hl',hk,hm,hn,ha,hb,hc,hd⟩ :=
    shared_checkerboard_gauge_complex a b c d θ
      (plaquette_arg_angle (nz h0) (nz h1) (nz h2) (nz h3))
  have re_phase {x u v : ℂ} {α : ℝ} (h : u*x*v = (‖x‖ : ℂ)*cis α) :
      (u*x*v).re = Real.cos α * ‖x‖ := by
    rw [h, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, cis_re]
    ring
  have hA : (l*a*m).re = p*‖a‖ := re_phase ha
  have hB : (l*b*n).re = p*‖b‖ := by simpa only [Real.cos_neg] using re_phase hb
  have hC : (k*c*m).re = p*‖c‖ := by simpa only [Real.cos_neg] using re_phase hc
  have hD : (k*d*n).re = p*‖d‖ := re_phase hd
  obtain ⟨aa,aa2⟩ := opposite_gauge_exact (nz h0) hl' hm hA
  obtain ⟨ab,ab2⟩ := opposite_gauge_exact (nz h1) hl' hn hB
  obtain ⟨ac,ac2⟩ := opposite_gauge_exact (nz h2) hk hm hC
  obtain ⟨ad,ad2⟩ := opposite_gauge_exact (nz h3) hk hn hD
  let r : Fin 4 → ℝ := ![‖a‖,‖b‖,‖c‖,‖d‖]
  let y : Fin 4 → ℝ := ![(star l*A*star m).re, (star l*B*star n).re,
    (star k*C*star m).re, (star k*D*star n).re]
  let e : Fin 4 → ℝ := ![projectedError a A l m, projectedError b B l n,
    projectedError c C k m, projectedError d D k n]
  let S : Fin 4 → ℝ := ![‖(1/2 : ℂ)-a*A‖, ‖(1/2 : ℂ)-b*B‖,
    ‖(1/2 : ℂ)-c*C‖, ‖(1/2 : ℂ)-d*D‖]
  have hrsum : (∑ i, r i) ≤ 2/p := by
    apply (le_div_iff₀ hp0).2
    have h := contraction_modulus_budget hX l k m n hl' hk hm hn hA hB hC hD
    simp only [r, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero]
    linarith only [h]
  have hysum : (∑ i, y i) ≤ 2 := by
    have h := (Complex.re_le_norm _).trans
      (contraction_flat_test hY (star l) (star k) (star m) (star n)
        (by simpa using hl') (by simpa using hk) (by simpa using hm) (by simpa using hn))
    rw [show star l*(A*star m+B*star n)+star k*(C*star m+D*star n) =
      ((star l*A*star m+star l*B*star n)+star k*C*star m)+star k*D*star n by ring] at h
    simp only [Complex.add_re] at h
    simpa [y, Fin.sum_univ_succ, add_assoc] using h
  have hg (i : Fin 4) : r i * y i = p/2-e i := by
    fin_cases i <;> first | exact aa | exact ab | exact ac | exact ad
  have hr (i : Fin 4) : 0 ≤ r i := by
    fin_cases i <;> exact norm_nonneg _
  have hE (i : Fin 4) : (e i)^2 ≤ (S i)^2 := by
    fin_cases i <;> first | exact aa2 | exact ab2 | exact ac2 | exact ad2
  have hδ : 0 ≤ δ := (norm_nonneg _).trans h0
  have hentry (i : Fin 4) : e i ≤ δ := by
    have hS : S i ≤ δ := by
      fin_cases i <;> first | exact h0 | exact h1 | exact h2 | exact h3
    have hnon : 0 ≤ S i := by fin_cases i <;> exact norm_nonneg _
    have hsq := (hE i).trans ((sq_le_sq₀ hnon hδ).mpr hS)
    exact (le_abs_self _).trans ((sq_le_sq₀ (abs_nonneg _) hδ).mp (by rwa [sq_abs]))
  have hF' : (∑ i, (e i)^2) ≤ 2*δ^2 := by
    simp only [e, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero]
    linarith only [aa2,ab2,ac2,ad2,hF]
  have hcoherent : (∑ i, e i) ≤ 2*(p+|q|)*δ := by
    simp only [e, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero, projectedError_of_phase (nz h0) ha,
      projectedError_of_phase (nz h1) hb, projectedError_of_phase (nz h2) hc,
      projectedError_of_phase (nz h3) hd, Real.cos_neg, Real.sin_neg]
    have h := signed_projection_sum_le hp0.le hsum hsigned (s := q)
    dsimp [p, q] at h ⊢
    linarith only [h]
  have hy (i : Fin 4) : 0 ≤ y i := by
    have hprod : 0 < r i * y i := by rw [hg i]; linarith [hentry i]
    exact (pos_of_mul_pos_right hprod (hr i)).le
  let x (i : Fin 4) := Real.sqrt (p/2-e i)
  have hx (i : Fin 4) : (x i)^2 ≤ r i*y i := by
    rw [hg i]
    exact (Real.sq_sqrt (by linarith [hentry i])).le
  have hcauchy := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun i _ => hr i) (fun i _ => hy i) (fun i _ => hx i)
  have hprod : (∑ i, r i)*(∑ i, y i) ≤ (2 / Real.sqrt p)^2 := by
    calc
      _ ≤ (2/p)*2 := mul_le_mul hrsum hysum
        (Finset.sum_nonneg fun i _ => hy i) (by positivity)
      _ = _ := by rw [div_pow, Real.sq_sqrt hp0.le]; ring
  have hroot : (∑ i, x i) ≤ 2/Real.sqrt p :=
    (sq_le_sq₀ (Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _) (by positivity)).mp
      (hcauchy.trans hprod)
  exact RTWeightBudget.quarter_cutoff_tight_rational e p |q| δ hl hp1
    (abs_nonneg _) hunit hsmall hentry hcoherent hF' hroot

end RTMultiFibre

end

end D5.S3.Quantum.Recovery.PrincipalPlaquetteGaugeBudget
