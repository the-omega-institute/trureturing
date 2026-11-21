/- GID: D5/S3/CharacterSums/SplittingProgressionExponentialTail
   generality: I
   mirror-B: D5/B/S3/CharacterSums/SplittingProgressionExponentialTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: On the splitting progression both truncated quadratic Mangoldt sums at the same real height pass outside an exponentially small set of integer indices. -/

import D5.S3.CharacterSums.JacobiTupleInterval
import D5.S3.CharacterSums.SplittingProgressionMangoldtSupply
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Real Finset Filter
open D5.S3.CharacterSums.JacobiTupleInterval
open D5.S3.CharacterSums.SplittingProgressionMangoldtSupply
open D5.S3.CharacterSums.DyadicMangoldtPrimeSupply (cutoff coefficient_bounds)
namespace D5.S3.CharacterSums.SplittingProgressionExponentialTail

private def primeSum (P : Finset ℕ) (a : ℕ → ℝ) (b m i : ℕ) : ℝ :=
  ∑ p ∈ P, a p*(jacobiSym (p:ℤ) (b+m*i):ℝ)

private lemma moment_discrepancy (P : Finset ℕ) (a : ℕ → ℝ) (b m A L n : ℕ)
    (hp : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hb : b%4=3) (hm : 4 ∣ m) :
    let Q := ∏ p ∈ P, p
    let S := primeSum P a b m
    |(∑ i ∈ range L, (S (A+i))^n) - (L:ℝ)/Q * ∑ i ∈ range Q, (S i)^n| ≤
      2*(∑ p ∈ P, (p:ℝ)*|a p|)^n := by
  classical
  intro Q S
  let C (f : Fin n → P) : ℝ := ∏ j, a (f j)
  let R (f : Fin n → P) := row (fun j => (f j:ℕ)) b m
  have expansion (i : ℕ) : S i ^ n = ∑ f : Fin n → P, C f * R f i := by
    change (∑ p ∈ P, a p*(jacobiSym (p:ℤ) (b+m*i):ℝ))^n = _
    rw [← Finset.sum_coe_sort P]
    rw [Fintype.sum_pow]
    apply sum_congr rfl; intro f _
    exact prod_mul_distrib
  have expandBlock (start len : ℕ) :
      (∑ i ∈ range len, S (start+i)^n) = ∑ f : Fin n → P, C f * block (R f) start len := by
    simp_rw [expansion]; rw [sum_comm]
    apply sum_congr rfl; intro f _; simp [block,mul_sum]
  have defect (f : Fin n → P) :
      |block (R f) A L - (L:ℝ)/Q * block (R f) 0 Q| ≤ 2*∏ j, ((f j:ℕ):ℝ) := by
    have h := tuple_interval_mean P (fun j => (f j:ℕ)) (fun j => (f j).property) hp b m A L hb hm
    simpa only [R,Q,div_eq_mul_inv,mul_left_comm,mul_assoc,mul_comm] using h
  have h0 := expandBlock 0 Q
  simp only [zero_add] at h0
  rw [expandBlock,h0,mul_sum,← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  have point (f : Fin n → P) :
      |C f * block (R f) A L - (L:ℝ)/Q*(C f*block (R f) 0 Q)| ≤
      2*∏ j, ((f j:ℕ):ℝ)*|a (f j)| := by
    rw [show C f * block (R f) A L - (L:ℝ)/Q*(C f*block (R f) 0 Q) =
      C f*(block (R f) A L-(L:ℝ)/Q*block (R f) 0 Q) by ring,abs_mul]
    apply (mul_le_mul_of_nonneg_left (defect f) (abs_nonneg _)).trans_eq
    dsimp only [C]
    rw [Finset.abs_prod,prod_mul_distrib]; ring
  apply (sum_le_sum (fun f _ => point f)).trans_eq
  rw [← mul_sum]; congr 1
  rw [← Finset.sum_coe_sort P, Fintype.sum_pow]

private lemma one_coordinate {F : Type*} [Fintype F] (χ : F → ℝ) (a : ℝ)
    (hχ : ∀ z, χ z = -1 ∨ χ z = 0 ∨ χ z = 1) (hmean : ∑ z, χ z = 0) :
    (∑ z, exp (a * χ z)) ≤ (Fintype.card F : ℝ) * exp (a^2/2) := by
  have line (z : F) : exp (a * χ z) ≤ cosh a + χ z * sinh a := by
    rcases hχ z with hz|hz|hz <;> rw [hz]
    · simp only [mul_neg_one,neg_one_mul,← sub_eq_add_neg]; rw [cosh_sub_sinh]
    · simpa only [mul_zero,exp_zero,zero_mul,add_zero] using (show 1 ≤ cosh a by nlinarith [cosh_sq a,cosh_pos a,sq_nonneg (sinh a)])
    · simp only [mul_one,one_mul,cosh_add_sinh,le_refl]
  calc
    _ ≤ ∑ z, (cosh a + χ z * sinh a) := sum_le_sum (fun z _ => line z)
    _ = (Fintype.card F : ℝ)*cosh a := by rw [sum_add_distrib,← sum_mul,hmean]; simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (cosh_le_exp_half_sq a) (by positivity)

/-- The exponential averages factor over the residue coordinates even if a character vanishes. -/
private lemma product_mgf {ι : Type*} [Fintype ι] [DecidableEq ι] {F : ι → Type*} [∀ i, Fintype (F i)]
    (χ : ∀ i, F i → ℝ) (a : ι → ℝ) (t : ℝ)
    (hχ : ∀ i z, χ i z = -1 ∨ χ i z = 0 ∨ χ i z = 1)
    (hmean : ∀ i, ∑ z, χ i z = 0) :
    (∑ z : (∀ i, F i), exp (t * ∑ i, a i * χ i (z i))) ≤
      (Fintype.card (∀ i, F i):ℝ) * exp (t^2*(∑ i, (a i)^2)/2) := by
  classical
  have fact (z : ∀ i, F i) :
      exp (t * ∑ i, a i * χ i (z i)) = ∏ i, exp ((t*a i) * χ i (z i)) := by
    rw [mul_sum,exp_sum]; apply prod_congr rfl; intro i _; congr 1; ring
  calc
    _ = ∏ i, ∑ z, exp ((t*a i)*χ i z) := by
      rw [Fintype.prod_sum]; exact sum_congr rfl (fun z _ => fact z)
    _ ≤ ∏ i, (Fintype.card (F i):ℝ)*exp ((t*a i)^2/2) := by
      apply prod_le_prod₀ (fun i _ => sum_nonneg (fun z _ => (exp_pos _).le))
        (fun i _ => one_coordinate (χ i) (t*a i) (hχ i) (hmean i))
    _ = _ := by
      rw [prod_mul_distrib,← exp_sum,Fintype.card_pi,Nat.cast_prod]; congr 2
      rw [mul_sum,sum_div]; apply sum_congr rfl; intro i _; ring

private lemma even_power_from_exps {t : ℝ} (ht : 0 < t) (s : ℝ) (k : ℕ) :
    s^(2*k) ≤ ((2*k).factorial:ℝ)/t^(2*k) * (exp (t*s) + exp (-t*s)) := by
  have h := pow_div_factorial_le_exp |t*s| (abs_nonneg (t*s)) (2*k)
  have hsame : |t*s|^(2*k) = t^(2*k)*s^(2*k) := by rw [← abs_pow,abs_of_nonneg (Even.pow_nonneg (even_two_mul k) _),mul_pow]
  rw [hsame] at h
  have hfact : (0:ℝ)<(2*k).factorial := by exact_mod_cast Nat.factorial_pos _
  have hmag : exp |t*s| ≤ exp (t*s) + exp (-t*s) := by
    rcases le_total 0 (t*s) with hs|hs
    · rw [abs_of_nonneg hs]; linarith only [exp_pos (-t*s)]
    · rw [abs_of_nonpos hs,neg_mul]; linarith only [exp_pos (t*s)]
  have hmul := (div_le_iff₀ hfact).1 (h.trans hmag)
  rw [div_mul_eq_mul_div,le_div_iff₀ (pow_pos ht _)]
  simpa only [mul_comm] using hmul

private lemma complete_even_moment {ι : Type*} [Fintype ι] [DecidableEq ι] {F : ι → Type*} [∀ i, Fintype (F i)]
    (χ : ∀ i, F i → ℝ) (a : ι → ℝ) {t : ℝ} (ht : 0 < t) (k : ℕ)
    (hχ : ∀ i z, χ i z = -1 ∨ χ i z = 0 ∨ χ i z = 1)
    (hmean : ∀ i, ∑ z, χ i z = 0) :
    (∑ z : (∀ i, F i), (∑ i, a i * χ i (z i))^(2*k)) ≤
      ((2*k).factorial:ℝ)/t^(2*k) *
        (2 * (Fintype.card (∀ i,F i):ℝ) * exp (t^2*(∑ i, (a i)^2)/2)) := by
  have hp := product_mgf χ a t hχ hmean
  have hm := product_mgf χ a (-t) hχ hmean
  rw [neg_sq] at hm
  apply (sum_le_sum (fun z _ => even_power_from_exps ht (∑ i, a i * χ i (z i)) k)).trans
  rw [← mul_sum,sum_add_distrib]
  exact mul_le_mul_of_nonneg_left (by linarith only [hp,hm]) (by positivity)

private theorem complete_moment_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {F : ι → Type*}
    [∀ i, Fintype (F i)] (χ : ∀ i, F i → ℝ) (a : ι → ℝ) (k : ℕ) (hk : 0 < k)
    {V : ℝ} (hV : 0 < V) (hvar : (∑ i, (a i)^2) ≤ V)
    (hχ : ∀ i z, χ i z = -1 ∨ χ i z = 0 ∨ χ i z = 1)
    (hmean : ∀ i, ∑ z, χ i z = 0) :
    (∑ z : (∀ i, F i), (∑ i, a i * χ i (z i))^(2*k)) ≤
      2*(Fintype.card (∀ i,F i):ℝ)*(2*exp 1*k*V)^k := by
  let t := sqrt (2*k/V)
  have hkr : (0:ℝ) < k := by exact_mod_cast hk
  have ht : 0 < t := sqrt_pos.2 (by positivity)
  have ht2 : t^2 = 2*(k:ℝ)/V := sq_sqrt (by positivity)
  have hfac : ((2*k).factorial:ℝ) ≤ (2*(k:ℝ))^(2*k) := by exact_mod_cast (2*k).factorial_le_pow
  have hs : t^2 * (∑ i, (a i)^2) / 2 ≤ k := by
    apply le_trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hvar (sq_nonneg t)) (by norm_num)) 
    rw [ht2]; field_simp; linarith
  have hrat : ((2*k).factorial:ℝ)/t^(2*k) ≤ (2*k*V:ℝ)^k := by
    apply (div_le_iff₀ (pow_pos ht _)).2
    rw [pow_mul,ht2,← mul_pow]
    have heq : 2*(k:ℝ)*V*(2*k/V) = (2*k)^2 := by field_simp
    rw [heq,← pow_mul]; exact hfac
  apply (complete_even_moment χ a ht k hχ hmean).trans
  calc
    _ ≤ (2*k*V:ℝ)^k * (2 * (Fintype.card (∀ i,F i):ℝ) * exp (k:ℝ)) := by
      gcongr
    _ = _ := by
      rw [show exp (k:ℝ) = exp 1 ^ k by simp]
      calc
        _ = (2*(Fintype.card (∀ i,F i):ℝ)) * ((2*k*V)^k * exp 1^k) := by ring
        _ = _ := by rw [← mul_pow]; congr 2; ring

/-- The loss at the endpoints involves only primes occurring in each expanded monomial. -/
private theorem affine_interval_even_moment (P : Finset ℕ) (a : ℕ → ℝ)
    (b m A L k : ℕ) (hk : 0 < k) (hb : b%4=3) (hm : 4 ∣ m)
    (hp : ∀ p ∈ P, p.Prime ∧ p≠2) (hc : ∀ p ∈ P, m.Coprime p)
    {V : ℝ} (hV : 0 < V) (hvar : (∑ p ∈ P, (a p)^2) ≤ V) :
    (∑ i ∈ range L, (∑ p ∈ P, a p*(jacobiSym (p:ℤ) (b+m*(A+i)):ℝ))^(2*k)) ≤
      2*L*(2*exp 1*k*V)^k + 2*(∑ p ∈ P, (p:ℝ)*|a p|)^(2*k) := by
  classical
  let _ : ∀ p : P, NeZero (p : ℕ) := fun p => ⟨(hp p p.2).1.ne_zero⟩
  let Q := ∏ p ∈ P, p
  have hQ : 0 < (Q:ℝ) := Nat.cast_pos.2 (Finset.prod_pos (fun p h => (hp p h).1.pos))
  have hvar' : (∑ p : P, (a p)^2) ≤ V := by
    exact (Finset.sum_coe_sort P (fun p : ℕ => (a p)^2)).le.trans hvar
  have full := complete_moment_bound (fun p : P => coordinate (hp p p.2).1)
    (fun p => a p) k hk hV hvar' (fun p => (coordinate_laws p (hp p p.2).1 (hp p p.2).2).1)
    (fun p => (coordinate_laws p (hp p p.2).1 (hp p p.2).2).2)
  have card : Fintype.card ((p : P) → ZMod (p:ℕ)) = Q := by
    simp only [Fintype.card_pi,ZMod.card]; exact Finset.prod_coe_sort P id
  rw [card,← affine_complete_crt P hp b m 0 (2*k) hb hm hc (fun p => a p)] at full
  simp only [zero_add] at full
  have re (i : ℕ) := Finset.sum_coe_sort P (fun p : ℕ => a p*(jacobiSym (p:ℤ) (b+m*i):ℝ))
  simp_rw [re] at full
  have defect := moment_discrepancy P a b m A L (2*k) hp hb hm
  have top := (le_abs_self _).trans defect
  change (∑ i ∈ range L, (primeSum P a b m (A+i))^(2*k)) -
    (L:ℝ)/Q*(∑ i ∈ range Q, (primeSum P a b m i)^(2*k)) ≤ _ at top
  change (∑ i ∈ range Q, (primeSum P a b m i)^(2*k)) ≤ _ at full
  have whole := mul_le_mul_of_nonneg_left full (show 0 ≤ (L:ℝ)/Q by positivity)
  rw [show (L:ℝ)/Q*(2*Q*(2*exp 1*k*V)^k) = 2*L*(2*exp 1*k*V)^k by field_simp] at whole
  change (∑ i ∈ range L, (primeSum P a b m (A+i))^(2*k)) ≤ _
  linarith only [whole,top]

/-- The cost of each endpoint is exponential in k log x; the interval length
has exponent x^(ε/5) (log x)^2. The complete-period contribution uses a
positive power saving in the per-pair moment-to-threshold ratio. -/
private theorem absorb_interval_moment {ε : ℝ} (hε : 0 < ε) (B : ℝ) (hB : 0 < B) :
    ∀ᶠ x : ℝ in atTop,
      let y := x^(ε/5)
      let k := ⌊y⌋₊
      let t := x^(1/2+ε)/4
      let N := cutoff x
      let V := (log N)^2*x*(1+log N)
      let W := (N:ℝ)^2*log N
      ∀ L : ℕ, exp (y*(log x)^2)/(4*exp (4*y)) ≤ L →
        2*L*(2*exp 1*k*V)^k + 2*W^(2*k) ≤
          (L:ℝ)*exp (-B*y)/2*t^(2*k) := by
  have hc := (isLittleO_log_rpow_rpow_atTop 3 hε).bound
    (show (0:ℝ) < 1/64160000 by norm_num)
  have hpow := tendsto_rpow_atTop (show 0 < 4*ε/5 by linarith)
  filter_upwards [eventually_ge_atTop (1:ℝ),tendsto_log_atTop.eventually_ge_atTop (2500+B),
    (tendsto_rpow_atTop (show 0 < ε/5 by linarith)).eventually_ge_atTop 2,
    hc,hpow.eventually_ge_atTop (32*exp 1*exp (2*B+4)),
    (tendsto_rpow_atTop (show 0 < 1/2+ε by linarith)).eventually_ge_atTop 4] with x hx hl hy hc hconst ht
  intro y k t N V W L hL
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hlog : 1 ≤ log x := by linarith
  have hN : 1 ≤ N := Nat.floor_pos.2 (one_le_pow₀ hx)
  have hNl : 0 ≤ log N := log_nonneg (by exact_mod_cast hN)
  have hNu : (N:ℝ) ≤ x^(400:ℕ) := Nat.floor_le (by positivity)
  have hlogN := log_le_log (show 0 < (N:ℝ) by exact_mod_cast hN) hNu
  rw [log_pow] at hlogN
  have hNl2 := (sq_le_sq₀ hNl (by positivity : 0 ≤ (400:ℝ)*log x)).2 hlogN
  change ‖(log x)^(3:ℝ)‖ ≤ _*‖x^ε‖ at hc
  rw [Real.norm_eq_abs,Real.rpow_ofNat, abs_of_nonneg (by positivity),
    Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg hxpos.le _)] at hc
  have hg : (log N)^2*(1+log N) ≤ x^ε := by
    have h1 : 1+log N ≤ 401*log x := by norm_num at hlogN; linarith
    have h := mul_le_mul hNl2 h1 (by linarith) (sq_nonneg _)
    nlinarith only [h,hc]
  have hV : V ≤ x*x^ε := by dsimp [V]; nlinarith only [mul_le_mul_of_nonneg_left hg hxpos.le]
  have hV0 : 0 ≤ V := by dsimp [V]; positivity
  have hk : (k:ℝ) ≤ y := Nat.floor_le (rpow_nonneg hxpos.le _)
  have hky : y < (k:ℝ)+1 := Nat.lt_floor_add_one y
  have hy2 : 2 ≤ y := hy
  have hk1 : 1 ≤ (k:ℝ) := by linarith only [hky,hy2]
  have ht1 : 1 ≤ t := by dsimp [t]; linarith
  have hsq : t^2 = x*x^(2*ε)/16 := by
    dsimp [t]; rw [div_pow,← rpow_mul_natCast hxpos.le,
      show (1/2+ε)*(2:ℕ) = 1+2*ε by push_cast; ring,rpow_add hxpos,rpow_one]; norm_num
  have scale : 2*exp 1*k*V ≤ exp (-(2*B+4))*t^2 := by
    have hp : y*x^ε*x^(4*ε/5) = x^(2*ε) := by
      dsimp [y]; rw [← rpow_add hxpos,← rpow_add hxpos]; congr 1;ring
    have hc' : 32*exp 1 ≤ exp (-(2*B+4))*x^(4*ε/5) := by
      rw [exp_neg,← div_eq_inv_mul]; apply (le_div_iff₀ (exp_pos _)).2; exact hconst
    calc
      _ ≤ 2*exp 1*y*(x*x^ε) := by gcongr
      _ = (32*exp 1)*(x*y*x^ε)/16 := by ring
      _ ≤ (exp (-(2*B+4))*x^(4*ε/5))*(x*y*x^ε)/16 := by gcongr
      _ = exp (-(2*B+4))*t^2 := by rw [hsq,← hp];ring
  have hmain : 2*L*(2*exp 1*k*V)^k ≤ (L:ℝ)*exp (-B*y)/4*t^(2*k) := by
    have h := pow_le_pow_left₀ (by positivity) scale k
    rw [mul_pow (exp _) (t^2),← exp_nat_mul,← pow_mul] at h
    have h8 : (8:ℝ) ≤ exp 4 := by
      have he := quadratic_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 4)
      norm_num at he;linarith
    have h8' : 8*exp ((k:ℝ)* -(2*B+4)) ≤ exp (-B*y) := by
      calc
        _ ≤ exp 4 * exp ((k:ℝ)* -(2*B+4)) := by gcongr
        _ ≤ _ := by rw [← exp_add];apply exp_le_exp.mpr; nlinarith only [hk1,mul_le_mul_of_nonneg_left (show y ≤ 2*k by linarith) hB.le]
    have h' := mul_le_mul_of_nonneg_right h8' (pow_nonneg (zero_le_one.trans ht1) (2*k))
    nlinarith only [mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (α:=ℝ) L),
      mul_le_mul_of_nonneg_left h' (Nat.cast_nonneg (α:=ℝ) L)]
  have hW0 : 0 ≤ W := by dsimp [W]; positivity
  have hW : W ≤ exp (1200*log x) := by
    have hlN : log N ≤ x^(400:ℕ) := (log_le_self (Nat.cast_nonneg _)).trans hNu
    calc
      _ ≤ (x^(400:ℕ))^2*x^(400:ℕ) := by dsimp [W]; gcongr
      _ = x^(1200:ℕ) := by ring
      _ = exp (1200*log x) := by
        have h := Real.exp_nat_mul (log x) 1200
        rw [exp_log hxpos] at h
        exact h.symm
  have hWk := pow_le_pow_left₀ hW0 hW (2*k)
  rw [← exp_nat_mul] at hWk
  have hDom : (32:ℝ)*exp (4*y)*exp (B*y)*W^(2*k) ≤ exp (y*(log x)^2) := by
    have h32 : (32:ℝ) ≤ exp 6 := by
      have h := pow_div_factorial_le_exp (6:ℝ) (by norm_num) 3
      norm_num at h;linarith
    calc
      _ ≤ exp 6 * exp (4*y) * exp (B*y) * exp ((2*k:ℕ)*(1200*log x)) := by gcongr
      _ ≤ _ := by
        rw [← exp_add,← exp_add,← exp_add];apply exp_le_exp.mpr
        push_cast
        have h1 := mul_le_mul_of_nonneg_right hk (by positivity : 0 ≤ 2400*log x)
        have h2 := mul_nonneg (by linarith : 0 ≤ log x - (2400+B+10)) (by linarith : 0 ≤ log x)
        have h3 := mul_le_mul_of_nonneg_left (show 2400*log x + B+7 ≤ (log x)^2 by nlinarith only [h2,mul_nonneg hB.le (by linarith : 0 ≤ log x-1),hl,hB]) (by linarith : 0 ≤ y)
        nlinarith only [h1,h3,hy2]
  have hsize := (div_le_iff₀ (by positivity : 0 < 4*exp (4*y))).1 hL
  have hEnd : 2*W^(2*k) ≤ (L:ℝ)*exp (-B*y)/4 := by
    have h := (le_of_mul_le_mul_left (a := 4*exp (4*y)) (b := 8*exp (B*y)*W^(2*k)) (c := (L:ℝ))
      (by nlinarith only [hDom,hsize]) (by positivity : 0 < 4*exp (4*y)))
    rw [neg_mul,exp_neg]; field_simp
    linarith only [h]
  have htn := one_le_pow₀ ht1 (n:=2*k)
  nlinarith only [hmain,hEnd,mul_le_mul_of_nonneg_left htn (show 0 ≤ (L:ℝ)*exp (-B*y)/4 by positivity)]

private lemma fourth_threshold_error {ε : ℝ} (hε : 0 < ε) (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ x : ℝ in atTop, K*sqrt x + log 2 + Chebyshev.theta (x^(ε/5)) ≤ x^(1/2+ε)/4 := by
  let C := K+log 2+log 4
  have he := (tendsto_rpow_atTop (show 0 < 3*ε/4 by linarith)).eventually_ge_atTop (4*C)
  filter_upwards [eventually_ge_atTop (1:ℝ),he] with x hx hc
  have hxpos := zero_lt_one.trans_le hx
  let E := x^(1/2+ε/4)
  have hroot : sqrt x ≤ E := by rw [sqrt_eq_rpow];exact rpow_le_rpow_of_exponent_le hx (by linarith)
  have hy : x^(ε/5) ≤ E := rpow_le_rpow_of_exponent_le hx (by linarith)
  have hE : 1 ≤ E := one_le_rpow hx (by linarith)
  have ht := (Chebyshev.theta_le_log4_mul_x (rpow_nonneg hxpos.le (ε/5))).trans
    (mul_le_mul_of_nonneg_left hy (log_nonneg (by norm_num)))
  have hpow : x^(1/2+ε) = E*x^(3*ε/4) := by
    dsimp [E];rw [← rpow_add hxpos];congr 1;ring
  rw [hpow]
  have h := mul_le_mul_of_nonneg_left hc (zero_le_one.trans hE)
  dsimp only [C] at h
  nlinarith only [h,ht,mul_le_mul_of_nonneg_left hroot hK,
    mul_le_mul_of_nonneg_left hE (log_nonneg (by norm_num : (1:ℝ) ≤ 2))]

/-- At the reference exponential length, either quadratic test has an arbitrarily
large fixed exponential saving, uniformly over the first denominator. -/
theorem splitting_progression_exponential_tail (ε B : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ q b m A L : ℕ, b%4=3 → 4 ∣ m →
      (∀ p : ℕ, p.Prime → p ∣ m → (p:ℝ) ≤ x^(ε/5) ∨ cutoff x < p) →
      exp (x^(ε/5)*(log x)^2)/(4*exp (4*x^(ε/5))) ≤ L →
      ((failures x ε q b m A L).card:ℝ) ≤ L*exp (-B*x^(ε/5)) := by
  classical
  let rate := max 1 B
  have hr : 0 < rate := zero_lt_one.trans_le (le_max_left _ _)
  obtain ⟨K,hK,herr⟩ := clipped_coprime_prime_error
  filter_upwards [eventually_ge_atTop (2:ℝ),fourth_threshold_error hε K hK,
    absorb_interval_moment hε rate hr,
    (tendsto_rpow_atTop (show 0 < ε/5 by linarith)).eventually_ge_atTop 2] with x hx err scale hy
  intro q b m A L hb hm hfactor hlen
  let y := x^(ε/5)
  let N := cutoff x
  let k := ⌊y⌋₊
  let t := x^(1/2+ε)/4
  let P := (Icc 1 N).filter (fun p => Nat.Prime p ∧ p ≠ 2 ∧ m.Coprime p)
  let d (i : ℕ) := b+m*(A+i)
  let c (p : ℕ) := log p * min 1 (x/p)
  let g (v : ℕ → ℝ) (i : ℕ) := ∑ p ∈ P, (c p*v p)*(jacobiSym (p:ℤ) (d i):ℝ)
  let V := (log N)^2*x*(1+log N)
  let W := (N:ℝ)^2*log N
  have hxpos : 0 < x := by linarith
  have hk : 0 < k := Nat.floor_pos.mpr (by dsimp [y];linarith)
  have hN : 2 ≤ N := Nat.le_floor (by
    change ((2:ℕ):ℝ) ≤ x^(400:ℕ)
    exact hx.trans (le_self_pow₀ (by linarith) (by decide)))
  have hNp : 1 < (N:ℝ) := by exact_mod_cast (show 1<N by omega)
  have hlog := log_pos hNp
  have hV : 0 < V := by dsimp [V];positivity
  have hW : 0 ≤ W := by dsimp [W];positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have hP (p : ℕ) (hp : p ∈ P) := (mem_filter.1 hp).2
  have hcoeff := coefficient_bounds x hxpos.le N (by omega) P (filter_subset _ _)
  have moment (v : ℕ → ℝ) (hv : ∀ n, |v n| ≤ 1) :
      (∑ i ∈ range L, (g v i)^(2*k)) ≤ (L:ℝ)*exp (-rate*y)/2*t^(2*k) := by
    have ha (p : ℕ) (hp : p ∈ P) : 0 ≤ c p := by
      exact mul_nonneg (log_nonneg (by exact_mod_cast (hP p hp).1.one_le))
        (le_min zero_le_one (div_nonneg hxpos.le p.cast_nonneg))
    have hc (p : ℕ) (hp : p ∈ P) : |c p*v p| ≤ c p := by
      rw [abs_mul,abs_of_nonneg (ha p hp)];exact mul_le_of_le_one_right (ha p hp) (hv p)
    have hs : (∑ p ∈ P, (c p*v p)^2) ≤ V := by
      apply le_trans _ hcoeff.1;apply sum_le_sum; intro p hp
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (ha p hp)).2 (hc p hp)
    have hmass : (∑ p ∈ P, (p:ℝ)*|c p*v p|) ≤ W :=
      (sum_le_sum (fun p hp => mul_le_mul_of_nonneg_left (hc p hp) p.cast_nonneg)).trans hcoeff.2
    have h := affine_interval_even_moment P (fun p => c p*v p)
      b m A L k hk hb hm (fun p hp => ⟨(hP p hp).1,(hP p hp).2.1⟩) (fun p hp => (hP p hp).2.2) hV hs
    apply le_trans h
    apply le_trans _ (scale L hlen)
    gcongr
  have error (v : ℕ → ℝ) (hv : ∀ n, |v n| ≤ 1) (i : ℕ) :
      |twistedBy x N (d i) v - g v i| ≤ t := by
    have he := herr x y N m (d i) v hxpos hv hfactor
    have heq : (Icc 1 N).filter (fun p => p.Prime ∧ p ≠ 2 ∧ p.Coprime m) = P := by
      ext p;simp [P,Nat.coprime_comm]
    rw [heq] at he; exact he.trans err
  let v (n : ℕ) := (jacobiSym (n:ℤ) q:ℝ)
  have hv n : |v n| ≤ 1 := by
    rcases jacobiSym.trichotomy (n:ℤ) q with h|h|h <;> simp [v,h]
  have pass (w : ℕ → ℝ) (hw : ∀ n, |w n| ≤ 1) (i : ℕ)
      (h : x^(1/2+ε)/2 < |twistedBy x N (d i) w|) : t ≤ |g w i| := by
    have tr := abs_add_le (twistedBy x N (d i) w-g w i) (g w i)
    rw [sub_add_cancel] at tr
    have he := error w hw i
    dsimp only [t] at *; linarith
  let S := failures x ε q b m A L
  have hp (z : ℝ) (hz : t ≤ |z|) : t^(2*k) ≤ z^(2*k) := by
    have h := pow_le_pow_left₀ ht.le hz (2*k)
    rwa [← abs_pow,abs_of_nonneg (Even.pow_nonneg (even_two_mul k) _)] at h
  have hbad : (S.card:ℝ)*t^(2*k) ≤ (L:ℝ)*exp (-rate*y)*t^(2*k) := calc
    _ = ∑ _i ∈ S, t^(2*k) := by simp
    _ ≤ ∑ i ∈ S, ((g (fun _ => 1) i)^(2*k)+(g v i)^(2*k)) := by
      apply sum_le_sum; intro i hi
      rcases (mem_filter.mp hi).2 with h|h
      · exact (hp _ (pass _ (by simp) i h)).trans (le_add_of_nonneg_right (Even.pow_nonneg (even_two_mul k) _))
      · exact (hp _ (pass _ hv i h)).trans (le_add_of_nonneg_left (Even.pow_nonneg (even_two_mul k) _))
    _ ≤ ∑ i ∈ range L, ((g (fun _ => 1) i)^(2*k)+(g v i)^(2*k)) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ =>
        add_nonneg (Even.pow_nonneg (even_two_mul k) _) (Even.pow_nonneg (even_two_mul k) _))
    _ ≤ _ := by rw [sum_add_distrib];linarith only [moment (fun _ => 1) (by simp),moment v hv]
  apply ((mul_le_mul_iff_left₀ (pow_pos ht _)).mp hbad).trans
  apply mul_le_mul_of_nonneg_left _ L.cast_nonneg
  apply exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (neg_le_neg (le_max_right 1 B)) (rpow_nonneg hxpos.le _)

end D5.S3.CharacterSums.SplittingProgressionExponentialTail
