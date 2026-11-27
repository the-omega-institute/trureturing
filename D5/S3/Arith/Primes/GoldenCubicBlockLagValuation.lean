/- GID: D5/S3/Arith/Primes/GoldenCubicBlockLagValuation
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicBlockLagValuation
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Native golden-binomial lifting gives all-lag valuations and exact periods of later cubic blocks. -/

import D5.S1.Scale.GoldenCubicBlockCongruences
import Mathlib.Data.Int.ModEq
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Arith.Primes.GoldenCubicBlockLagValuation

variable {R : Type*} [CommRing R]

theorem pow_expand_two (x : R) (n : ℕ) :
    ∃ t : R, (1+x)^n = 1 + (n:R)*x + (n.choose 2:R)*x^2 + x^3*t := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨(n.choose 2 : R) + (1+x)*t, ?_⟩
    rw [pow_succ, ht, Nat.choose_succ_succ, Nat.choose_one_right,
      Nat.cast_add, Nat.cast_succ]
    push_cast; ring

theorem pow_expand_one (x : R) (n : ℕ) :
    ∃ t : R, (1+x)^n = 1 + (n:R)*x + x^2*t := by
  obtain ⟨t, ht⟩ := pow_expand_two x n
  exact ⟨(n.choose 2 : R)+x*t, by rw [ht]; ring⟩

theorem odd_dvd_choose_two (p : ℕ) (hp : Odd p) : p ∣ p.choose 2 := by
  obtain ⟨k, hk⟩ := hp
  use k
  rw [Nat.choose_two_right, hk]
  have hd : (2*k+1-1) = 2*k := by omega
  rw [hd]
  have hh : (2*k+1)*(2*k)=(2*k+1)*k*2 := by ring
  rw [hh]
  omega

theorem lift_one (p s : ℕ) (hp : Odd p) (hs : 1 ≤ s) (c : R) :
    ∃ t : R, (1+(p:R)^s*c)^p = 1 + (p:R)^(s+1)*(c+(p:R)*t) := by
  obtain ⟨k,hk⟩ := odd_dvd_choose_two p hp
  obtain ⟨t,ht⟩ := pow_expand_two ((p:R)^s*c) p
  let d := s-1
  have hd : s=d+1 := by dsimp [d]; omega
  refine ⟨(p:R)^d*(k:R)*c^2 + (p:R)^(2*d)*c^3*t, ?_⟩
  rw [ht,hk, Nat.cast_mul,hd]
  simp only [pow_succ, pow_add, two_mul]
  ring

theorem lift_many (p s e : ℕ) (hp : Odd p) (hs : 1 ≤ s) (c : R) :
    ∃ t : R, (1+(p:R)^s*c)^(p^e) = 1 + (p:R)^(s+e)*(c+(p:R)*t) := by
  induction e with
  | zero => exact ⟨0, by simp⟩
  | succ e ih =>
    obtain ⟨t,ht⟩ := ih
    obtain ⟨v,hv⟩ := lift_one p (s+e) hp (by omega) (c+(p:R)*t)
    exact ⟨t+v, by rw [pow_succ, pow_mul,ht,hv]; ring⟩

theorem lift_factored_exp (p s e a : ℕ) (hp : Odd p) (hs : 1 ≤ s) (c : R) :
    ∃ t : R, (1+(p:R)^s*c)^(p^e*a) = 1 + (p:R)^(s+e)*((a:R)*c+(p:R)*t) := by
  obtain ⟨t,ht⟩ := lift_many p s e hp hs c
  let C := c+(p:R)*t
  obtain ⟨v,hv⟩ := pow_expand_one ((p:R)^(s+e)*C) a
  have hh : s+e=(s+e-1)+1 := by omega
  refine ⟨(a:R)*t+(p:R)^(s+e-1)*C^2*v, ?_⟩
  rw [pow_mul,ht]
  change (1+(p:R)^(s+e)*C)^a = _
  rw [hv]
  generalize he : s+e-1 = d at *
  rw [hh]; simp only [pow_succ]; dsimp [C]; ring


theorem trace_even_sub (u z : R) (huz : u*z=1) (A B : ℕ) (hBA : B ≤ A) :
    u^A+z^A-(u^B+z^B) = (u^(A-B)-1)*(u^(A+B)-1)*z^A := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hBA
  have hB : u^B*z^B=1 := by rw [← mul_pow,huz,one_pow]
  have hd : u^d*z^d=1 := by rw [← mul_pow,huz,one_pow]
  simp only [Nat.add_sub_cancel_left, pow_add]
  calc
    _ = (u ^ d - 1) * (u ^ B * (u ^ B * z ^ B) * (u ^ d * z ^ d) -
                          z ^ B * z ^ d) := by
      rw [hB,hd]; linear_combination z^B*hd
    _ = _ := by ring

open D5.S0.Carrier D5.S1.Scale
theorem cast_trace_sq (n : ℕ) (hn : Odd n) :
    (goldenLucas n : D5.S0.Carrier.GoldenInt)^2 + 3 =
      (D5.S0.Carrier.phi ^ n)^2 +
        (D5.S0.Carrier.conj (D5.S0.Carrier.phi ^ n))^2 + 1 := by
  open D5.S0.Carrier D5.S1.Scale in
  have hnorm : phi ^ n * conj (phi ^ n) = -1 := by
    rw [← norm_eq_mul_conj, norm_phi_pow, hn.neg_one_pow]
    simp
  rw [goldenLucas, ← add_conj_eq_trace]
  linear_combination 2*hnorm

open D5.S0.Carrier D5.S1.Scale

/-- The full leading residue after dividing out the proposed block-collision
depth. Neither primality in the golden ring nor a chosen split root is needed. -/
theorem native_block_leading
    (p h m A B e f a b : ℕ) (c : ℤ)
    (hp : Odd p) (hh : 1 ≤ h) (hm : Odd m) (hA : Odd A) (hB : Odd B) (hBA : B ≤ A)
    (hL : goldenLucas m = (p:ℤ)^h*c)
    (he : A-B=p^e*a) (hf : A+B=p^f*b) :
    ∃ t : ℤ, (goldenLucas (m*A)^2 + 3) - (goldenLucas (m*B)^2 + 3) =
      (p:ℤ)^(2*h+e+f)*((a:ℤ)*b*c^2 + (p:ℤ)*t) := by
  let w : GoldenInt := phi^m
  let u := w^2
  let z := (conj w)^2
  let P : GoldenInt := p
  let C : GoldenInt := c
  have hnorm : w * conj w = -1 := by
    dsimp [w]
    rw [← norm_eq_mul_conj, norm_phi_pow, hm.neg_one_pow]
    simp
  have huz : u*z=1 := by
    dsimp [u,z]
    rw [← mul_pow,hnorm]
    norm_num
  have hu : u = 1+P^h*(C*w) := by
    dsimp [u]
    have ht : w+conj w=P^h*C := by
      rw [add_conj_eq_trace]
      change (goldenLucas m : GoldenInt) = _
      rw [hL]
      push_cast
      rfl
    linear_combination w*ht-hnorm
  have hu1 : ∃ t : GoldenInt, u = 1+P*t := by
    obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hh
    exact ⟨P^d*(C*w), by rw [hu,hd,pow_add,pow_one]; ring⟩
  obtain ⟨tw,hw⟩ := hu1
  have hz : z=1+P*(-tw*z) := by linear_combination huz - z*hw
  obtain ⟨sz,hsz⟩ := pow_expand_one (P*(-tw*z)) A
  have hzA : z^A=1+P*((A:GoldenInt)*(-tw*z)+P*(-tw*z)^2*sz) := by
    conv_lhs => rw [hz,hsz]
    ring
  obtain ⟨s1,hs1⟩ := lift_factored_exp p h e a hp hh (C*w)
  obtain ⟨s2,hs2⟩ := lift_factored_exp p h f b hp hh (C*w)
  have h1 : u^(A-B)-1=P^(h+e)*((a:GoldenInt)*(C*w)+P*s1) := by
    rw [he,hu,hs1]; ring
  have h2 : u^(A+B)-1=P^(h+f)*((b:GoldenInt)*(C*w)+P*s2) := by
    rw [hf,hu,hs2]; ring
  have hcast (n : ℕ) (hn : Odd n) :
      ((goldenLucas (m*n)^2+3:ℤ) : GoldenInt) = u^n+z^n+1 := by
    push_cast
    rw [cast_trace_sq (m*n) (hm.mul hn),pow_mul]
    have hc : conj ((phi^m)^n) = (conj (phi^m))^n := map_pow conjEquiv _ _
    rw [hc]
    simp only [u,z,w, ← pow_mul, Nat.mul_comm n 2, Nat.mul_assoc]
  have hmain :
      ((goldenLucas (m*A)^2+3:ℤ) : GoldenInt) -
      ((goldenLucas (m*B)^2+3:ℤ) : GoldenInt) =
      P^(2*h+e+f)*(((a:GoldenInt)*(C*w)+P*s1)*((b:GoldenInt)*(C*w)+P*s2)*z^A) := by
    rw [hcast A hA,hcast B hB]
    calc
      _ = u^A+z^A-(u^B+z^B) := by ring
      _ = _ := by rw [trace_even_sub u z huz A B hBA, h1,h2]
                  simp only [two_mul,pow_add]; ring
  let q := (A:GoldenInt)*(-tw*z)+P*(-tw*z)^2*sz
  let v := ((a:GoldenInt)*(C*w)+P*s1)*((b:GoldenInt)*(C*w)+P*s2)
  have hv :
      v*z^A = (a:GoldenInt)*b*C^2 + P*((a:GoldenInt)*b*C^2*tw +
        (a:GoldenInt)*C*w*s2+(b:GoldenInt)*C*w*s1+P*s1*s2+v*q) := by
    rw [hzA]
    dsimp [q,v]
    have hw2 : w^2=1+P*tw := hw
    linear_combination (a:GoldenInt)*b*C^2*hw2
  rw [show ((a:GoldenInt)*(C*w)+P*s1)*((b:GoldenInt)*(C*w)+P*s2) = v by rfl, hv] at hmain
  refine ⟨((a:GoldenInt)*b*C^2*tw +
        (a:GoldenInt)*C*w*s2+(b:GoldenInt)*C*w*s1+P*s1*s2+v*q).a, ?_⟩
  have ha := congrArg GoldenInt.a hmain
  have hpi : P^(2*h+e+f) = (((p:ℤ)^(2*h+e+f) : ℤ) : GoldenInt) := by push_cast; rfl
  have habc : (a:GoldenInt)*b*C^2 = ((((a:ℤ)*b*c^2) : ℤ) : GoldenInt) := by
    push_cast; rfl
  rw [hpi,habc,sub_eq_add_neg] at ha
  rw [habc]
  simpa only [P,a_add,a_neg,a_intCast,a_natCast,a_mul,b_intCast,b_natCast,
    zero_mul,add_zero,sub_eq_add_neg] using ha


private theorem exact_depth {p s : ℕ} (hp : p.Prime) {c : ℤ}
    (hc : ¬ (p:ℤ) ∣ c) : padicValInt p ((p:ℤ)^s*c) = s := by
  have hn : (p:ℤ)^s ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have hc0 : c ≠ 0 := fun h => hc (h ▸ dvd_zero _)
  have hz := mul_ne_zero hn hc0
  have hlo := ((padicValInt_dvd_iff_of_ne_one hp.ne_one s ((p:ℤ)^s*c)).mp
    (dvd_mul_right _ _)).resolve_left hz
  have hhi : ¬ s+1 ≤ padicValInt p ((p:ℤ)^s*c) := by
    intro h
    obtain ⟨d,hd⟩ := (padicValInt_dvd_iff_of_ne_one hp.ne_one (s+1) _).mpr (Or.inr h)
    rw [pow_succ,mul_assoc] at hd
    exact hc ⟨d, mul_left_cancel₀ hn hd⟩
  omega

private theorem int_split_depth {p : ℕ} (hp : p.Prime) {z : ℤ} (hz : z ≠ 0) :
    ∃ c : ℤ, z = (p:ℤ)^padicValInt p z*c ∧ ¬ (p:ℤ) ∣ c := by
  obtain ⟨c,hc⟩ := padicValInt_dvd (p := p) z
  refine ⟨c,hc,?_⟩
  rintro ⟨d,hd⟩
  have hh : (p:ℤ)^(padicValInt p z+1) ∣ z :=
    ⟨d, by rw [pow_succ,mul_assoc,← hd,← hc]⟩
  have hv := ((padicValInt_dvd_iff_of_ne_one hp.ne_one _ _).mp hh).resolve_left hz
  omega

private theorem nat_split_depth {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : n ≠ 0) :
    ∃ a : ℕ, n=p^padicValNat p n*a ∧ ¬ (p:ℤ) ∣ a := by
  have hfn : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := pow_padicValNat_dvd (p := p) (n := n)
  refine ⟨a,ha,?_⟩
  intro hd
  have hdNat : p ∣ a := by exact_mod_cast hd
  obtain ⟨b,hb⟩ := hdNat
  apply pow_succ_padicValNat_not_dvd (p := p) hn
  exact ⟨b,by rw [pow_succ,mul_assoc,← hb,← ha]⟩

/-- Exact all-lag valuation of the difference of two later golden blocks
at arbitrary positive odd strides (no split-field premise). -/
theorem native_block_lag_valuation (p m A B : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hm : Odd m) (hA : Odd A) (hB : Odd B) (hBA : B < A)
    (hL0 : goldenLucas m ≠ 0) (hL : (p:ℤ) ∣ goldenLucas m) :
    padicValInt p ((goldenLucas (m*A)^2+3)-(goldenLucas (m*B)^2+3)) =
      2*padicValInt p (goldenLucas m) + padicValNat p (A-B) + padicValNat p (A+B) := by
  have h1 : 1 ≤ padicValInt p (goldenLucas m) := by
    apply ((padicValInt_dvd_iff_of_ne_one hp.ne_one 1 _).mp ?_).resolve_left hL0
    simpa using hL
  obtain ⟨c,hc,hcnd⟩ := int_split_depth hp hL0
  obtain ⟨a,ha,hand⟩ := nat_split_depth hp (show A-B ≠ 0 by omega)
  obtain ⟨b,hb,hbnd⟩ := nat_split_depth hp (show A+B ≠ 0 by omega)
  obtain ⟨t,ht⟩ := native_block_leading p _ m A B _ _ a b c hpodd h1 hm hA hB hBA.le hc ha hb
  rw [ht]
  apply exact_depth hp
  intro h
  have hs : (p:ℤ) ∣ (a:ℤ)*b*c^2 := by
    have hs := dvd_sub h (dvd_mul_right (p:ℤ) t)
    simpa only [Int.add_sub_cancel] using hs
  have hpI : Prime (p:ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa)
  rcases hpI.dvd_mul.mp hs with hab | hc2
  · exact (hpI.dvd_mul.mp hab).elim hand hbnd
  · rw [pow_two] at hc2
    exact (hpI.dvd_mul.mp hc2).elim hcnd hcnd


theorem native_cubic_seed_lag_valuation (p m j k : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hp3 : p ≠ 3) (hm : Odd m) (hjk : k < j)
    (hL0 : goldenLucas m ≠ 0) (hL : (p:ℤ) ∣ goldenLucas m) :
    padicValInt p ((goldenLucas (m*3^j)^2+3)-(goldenLucas (m*3^k)^2+3)) =
      2*padicValInt p (goldenLucas m) + padicValNat p (9^(j-k)-1) := by
  have : Fact p.Prime := ⟨hp⟩
  have hpnd : ¬p ∣ 3 := fun h => hp3 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h)
  have hval₃ : padicValNat p 3 = 0 := padicValNat.eq_zero_of_not_dvd hpnd
  have hvalPow : padicValNat p (3^k) = 0 := by rw [padicValNat.pow 3 k,hval₃,mul_zero]
  have h3lt : 3^k < 3^j := Nat.pow_lt_pow_right (by decide) hjk
  rw [native_block_lag_valuation p m _ _ hp hpodd hm ((by decide : Odd (3:ℕ)).pow)
    ((by decide : Odd (3:ℕ)).pow) h3lt hL0 hL]
  let q : ℕ := 3^(j-k)
  have hq : 1 < q := by
    dsimp [q]
    exact Nat.one_lt_pow (by omega) (by decide)
  have hq₉ : 9^(j-k) = q*q := by
    simp [q, ← mul_pow]
  have hpow : 3^j=3^k*q := by
    dsimp [q]
    rw [← pow_add, Nat.add_sub_of_le hjk.le]
  have hsub : 3^j-3^k = 3^k*(q-1) := by rw [hpow,Nat.mul_sub_left_distrib,Nat.mul_one]
  have hadd : 3^j+3^k = 3^k*(q+1) := by rw [hpow,Nat.mul_add,Nat.mul_one]
  have hfac : (q-1)*(q+1)=9^(j-k)-1 := by
    rw [hq₉,Nat.mul_sub_right_distrib,one_mul,Nat.mul_add,mul_one]
    omega
  rw [hsub,hadd,padicValNat.mul (pow_ne_zero _ (by decide : (3:ℕ) ≠ 0)) (by omega),
    padicValNat.mul (pow_ne_zero _ (by decide : (3:ℕ) ≠ 0)) (by omega),
    hvalPow, zero_add, zero_add, Nat.add_assoc, ← padicValNat.mul (by omega : q-1 ≠ 0)
      (by omega : q+1 ≠ 0), hfac]

/-- At a prime dividing any earlier cubic golden block, differences of
later block observations have exact collision depth given by the power of
nine minus one, offset by twice the earlier block's depth. -/
theorem golden_cubic_block_all_lag_valuation
    (p i j t : ℕ) (hp : p.Prime) (hpodd : Odd p) (hp3 : p ≠ 3) (hi : 1 ≤ i)
    (hit : i < t) (htj : t < j) (hpB : (p:ℤ) ∣ goldenLucas (3^i)^2+3) :
    padicValInt p ((goldenLucas (3^j)^2+3)-(goldenLucas (3^t)^2+3)) =
      2*padicValInt p (goldenLucas (3^i)^2+3) + padicValNat p (9^(j-t)-1) := by
  have : Fact p.Prime := ⟨hp⟩
  let x := goldenLucas (3^i)
  have hxnd : ¬ (p:ℤ) ∣ x := by
    intro hx
    have hd : (p:ℤ) ∣ 3 := by
      have hh := dvd_sub hpB (dvd_trans hx (dvd_pow_self _ (by decide : (2:ℕ) ≠ 0)))
      change (p:ℤ) ∣ x^2+3-x^2 at hh
      rwa [show x^2+3-x^2=(3:ℤ) by ring] at hh
    have hh : p ∣ 3 := by exact_mod_cast hd
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hh)
  have hx0 : x ≠ 0 := fun hz => hxnd (hz ▸ dvd_zero _)
  have hxval : padicValInt p x = 0 := by
    by_contra h
    have hd := (padicValInt_dvd_iff_of_ne_one hp.ne_one 1 x).mpr (Or.inr (by omega))
    exact hxnd (by simpa using hd)
  have hB0 : x^2+3 ≠ 0 := by positivity
  have hrec : goldenLucas (3^(i+1))=x*(x^2+3) :=
    (golden_cubic_lucas_block i hi).2.2.2.2.2
  have hseed0 : goldenLucas (3^(i+1)) ≠ 0 := by rw [hrec]; exact mul_ne_zero hx0 hB0
  have hseed : (p:ℤ) ∣ goldenLucas (3^(i+1)) := by rw [hrec]; exact dvd_mul_of_dvd_right hpB x
  have hseedval : padicValInt p (goldenLucas (3^(i+1))) = padicValInt p (x^2+3) := by
    rw [hrec,padicValInt.mul hx0 hB0,hxval,zero_add]
  have h := native_cubic_seed_lag_valuation p (3^(i+1)) (j-(i+1)) (t-(i+1))
    hp hpodd hp3 ((by decide : Odd (3:ℕ)).pow) (by omega) hseed0 hseed
  have hj : (3:ℕ)^(i+1)*3^(j-(i+1))=3^j := by rw [←pow_add,Nat.add_sub_of_le (by omega)]
  have ht : (3:ℕ)^(i+1)*3^(t-(i+1))=3^t := by rw [←pow_add,Nat.add_sub_of_le (by omega)]
  have hdiff : (j-(i+1))-(t-(i+1))=j-t := by omega
  rw [hj,ht,hdiff,hseedval] at h
  exact h


/-- The centered form with no excluded prime hypotheses: the native
block congruences show that its prime factors are neither two nor three. -/
theorem golden_cubic_tail_clock_valuation
    (p i n m : ℕ) (hp : p.Prime) (hi : 1 ≤ i) (hmn : m < n)
    (hpB : (p:ℤ) ∣ goldenLucas (3^i)^2+3) :
    padicValInt p ((goldenLucas (3^(i+1+n))^2+3)-(goldenLucas (3^(i+1+m))^2+3)) =
      2*padicValInt p (goldenLucas (3^i)^2+3) + padicValNat p (9^(n-m)-1) := by
  let b := goldenLucas (3^i)^2+3
  have hb80 : (b : ZMod 80) = ((19:ℤ):ZMod 80) :=
    (golden_cubic_lucas_block i hi).2.2.2.2.1
  have hb9 : (b : ZMod 9) = ((1:ℤ):ZMod 9) :=
    (golden_cubic_lucas_block i hi).2.2.1
  have hr80 := (ZMod.intCast_eq_intCast_iff' b 19 80).mp hb80
  have hr9 := (ZMod.intCast_eq_intCast_iff' b 1 9).mp hb9
  have hn2 : p ≠ 2 := by
    rintro rfl
    have hw : b % 2 = 0 := Int.emod_eq_zero_of_dvd hpB
    omega
  have hn3 : p ≠ 3 := by
    rintro rfl
    have hw : b % 3 = 0 := Int.emod_eq_zero_of_dvd hpB
    omega
  have h := golden_cubic_block_all_lag_valuation p i (i+1+n) (i+1+m)
    hp (hp.odd_of_ne_two hn2) hn3 hi (by omega) (by omega) hpB
  have hs : i+1+n-(i+1+m) = n-m := by omega
  rwa [hs] at h


private theorem nine_positive_lag (n : ℕ) (hn : 0 < n) :
    1 < (9:ℕ)^n := by
  exact one_lt_pow₀ (by norm_num) (by omega)

private theorem nine_lag_clock (p precision n m : ℕ) (hp : p.Prime)
    (hp9 : IsCoprime (p:ℤ) 9) (hmn : m < n) :
    (9:ℤ)^n ≡ 9^m [ZMOD (p:ℤ)^precision] ↔
      precision ≤ padicValNat p (9^(n-m)-1) := by
  have hpos := nine_positive_lag (n-m) (by omega)
  have hf : (9:ℤ)^m - 9^n = -(↑((9:ℕ)^(n-m)-1) : ℤ)*9^m := by
    have he : n = (n-m)+m := by omega
    conv_lhs => rhs; rw [he, pow_add]
    rw [Nat.cast_sub (by omega : 1 ≤ (9:ℕ)^(n-m))]
    push_cast
    ring
  have hc : IsCoprime ((p:ℤ)^precision) ((9:ℤ)^m) :=
    hp9.pow_left.pow_right
  rw [Int.modEq_iff_dvd, hf]
  constructor
  · intro hh
    have hi := hc.dvd_of_dvd_mul_right hh
    rw [Int.dvd_neg, ← Nat.cast_pow] at hi
    exact (padicValNat_dvd_iff_le_of_ne_one hp.ne_one (by omega)).mp
      (Int.natCast_dvd.mp hi)
  · intro hh
    have hi := (padicValNat_dvd_iff_le_of_ne_one hp.ne_one (by omega)).mpr hh
    have hj : ((p^precision : ℕ) : ℤ) ∣ ((9^(n-m)-1 : ℕ) : ℤ) := by
      exact_mod_cast hi
    rw [Nat.cast_pow] at hj
    exact (dvd_neg.mpr hj).trans (dvd_mul_right _ _)

/-- Reducing at depth 2h+r is exactly the multiplicative clock modulo p^r,
provided the sequence has the native all-lag valuations. This gives a
pairwise collision criterion, not only the first return from the seed. -/
theorem clock_of_exact_lags (p h precision : ℕ) (hp : p.Prime)
    (hh : 0 < h) (hp9 : IsCoprime (p:ℤ) 9) (B : ℕ → ℤ)
    (hlag : ∀ n m : ℕ, m < n →
      padicValInt p (B n-B m) = 2*h + padicValNat p (9^(n-m)-1))
    (n m : ℕ) (hmn : m < n) :
    B n ≡ B m [ZMOD (p:ℤ)^(2*h+precision)] ↔
      (9:ℤ)^n ≡ 9^m [ZMOD (p:ℤ)^precision] := by
  have hv := hlag n m hmn
  have hne : B n-B m ≠ 0 := by
    intro hd
    rw [hd, padicValInt.zero] at hv
    omega
  rw [nine_lag_clock p precision n m hp hp9 hmn, Int.modEq_iff_dvd]
  rw [show B m-B n = -(B n-B m) by ring, Int.dvd_neg]
  rw [padicValInt_dvd_iff_of_ne_one hp.ne_one, or_iff_right hne, hv]
  omega

/-- Before the doubled seed depth, later block values cannot be distinguished. -/
theorem constant_below_exact_lags (p h a : ℕ) (hp : p.Prime) (ha : a ≤ 2*h)
    (B : ℕ → ℤ) (hlag : ∀ n m : ℕ, m < n →
      padicValInt p (B n-B m) = 2*h + padicValNat p (9^(n-m)-1)) (n m : ℕ) :
    B n ≡ B m [ZMOD (p:ℤ)^a] := by
  have forward (s t : ℕ) (h : t < s) : B s ≡ B t [ZMOD (p:ℤ)^a] := by
    rw [Int.modEq_iff_dvd, show B t-B s = -(B s-B t) by ring, Int.dvd_neg]
    rw [padicValInt_dvd_iff_of_ne_one hp.ne_one, hlag s t h]
    exact Or.inr (ha.trans (Nat.le_add_right _ _))
  rcases lt_trichotomy m n with h | h | h
  · exact forward n m h
  · cases h
    rfl
  · exact (forward m n h).symm

/-- Every return period, not only the smallest, is exactly a
multiplicative return period of nine at the reduced precision. -/
theorem periods_of_exact_lags (p h precision : ℕ) (hp : p.Prime)
    (hh : 0 < h) (hp9 : IsCoprime (p:ℤ) 9) (B : ℕ → ℤ)
    (hlag : ∀ n m : ℕ, m < n →
      padicValInt p (B n-B m) = 2*h + padicValNat p (9^(n-m)-1))
    (lag : ℕ) :
    (∀ n, B (n+lag) ≡ B n [ZMOD (p:ℤ)^(2*h+precision)]) ↔
      (9:ℤ)^lag ≡ 1 [ZMOD (p:ℤ)^precision] := by
  by_cases h0 : lag = 0
  · subst lag
    simp
  constructor
  · intro hr
    have hs := (clock_of_exact_lags p h precision hp hh hp9 B hlag (0+lag) 0
      (by omega)).mp (hr 0)
    simpa using hs
  · intro hr n
    apply (clock_of_exact_lags p h precision hp hh hp9 B hlag (n+lag) n (by omega)).mpr
    simpa [pow_add] using hr.mul_left ((9:ℤ)^n)



private theorem previous_block_depth_pos (p i : ℕ) (hp : p.Prime)
    (hB : (p:ℤ) ∣ goldenLucas (3^i)^2+3) :
    0 < padicValInt p (goldenLucas (3^i)^2+3) :=
  ((padicValInt_dvd_iff_of_ne_one hp.ne_one 1 _).mp
    (by simpa using hB)).resolve_left (by positivity)

private theorem previous_block_prime_coprime_nine (p i : ℕ) (hp : p.Prime)
    (hi : 1 ≤ i) (hB : (p:ℤ) ∣ goldenLucas (3^i)^2+3) :
    IsCoprime (p:ℤ) 9 := by
  let b := goldenLucas (3^i)^2+3
  have hb9 : (b : ZMod 9) = ((1:ℤ):ZMod 9) :=
    (golden_cubic_lucas_block i hi).2.2.1
  have hr := (ZMod.intCast_eq_intCast_iff' b 1 9).mp hb9
  have hp3 : ¬ p ∣ 3 := by
    intro hd
    have he : p = 3 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hd
    rw [he] at hB
    have hw : b % 3 = 0 := Int.emod_eq_zero_of_dvd hB
    omega
  have hc : IsCoprime (p:ℤ) (3:ℤ) := (hp.coprime_iff_not_dvd.mpr hp3).isCoprime
  simpa using (hc.pow_right (n := 2))

/-- For two later observations, reduce by twice the earlier block depth:
the exact collision test is equality of powers of nine at the remaining
precision. This holds at every precision, not just in an initial window. -/
theorem golden_cubic_tail_collision (p i precision n m : ℕ) (hp : p.Prime)
    (hi : 1 ≤ i) (hB : (p:ℤ) ∣ goldenLucas (3^i)^2+3) (hmn : m < n) :
    goldenLucas (3^(i+1+n))^2+3 ≡ goldenLucas (3^(i+1+m))^2+3
      [ZMOD (p:ℤ)^(2*padicValInt p (goldenLucas (3^i)^2+3)+precision)] ↔
      (9:ℤ)^n ≡ 9^m [ZMOD (p:ℤ)^precision] :=
  clock_of_exact_lags p _ precision hp (previous_block_depth_pos p i hp hB)
    (previous_block_prime_coprime_nine p i hp hi hB)
    (fun j => goldenLucas (3^(i+1+j))^2+3)
    (fun a b hab => golden_cubic_tail_clock_valuation p i a b hp hi hab hB) n m hmn

/-- At or below twice the earlier depth all later blocks are congruent. -/
theorem golden_cubic_tail_constant (p i precision n m : ℕ) (hp : p.Prime)
    (hi : 1 ≤ i) (hB : (p:ℤ) ∣ goldenLucas (3^i)^2+3)
    (ha : precision ≤ 2*padicValInt p (goldenLucas (3^i)^2+3)) :
    goldenLucas (3^(i+1+n))^2+3 ≡ goldenLucas (3^(i+1+m))^2+3
      [ZMOD (p:ℤ)^precision] :=
  constant_below_exact_lags p _ precision hp ha
    (fun j => goldenLucas (3^(i+1+j))^2+3)
    (fun a b hab => golden_cubic_tail_clock_valuation p i a b hp hi hab hB) n m

/-- Every return period is a multiple of the order of nine at the
reduced precision. Combined with the preceding constant window, this
determines the full later-block congruence clock. -/
theorem golden_cubic_tail_period (p i precision lag : ℕ) (hp : p.Prime)
    (hi : 1 ≤ i) (hB : (p:ℤ) ∣ goldenLucas (3^i)^2+3) :
    (∀ n : ℕ,
      goldenLucas (3^(i+1+(n+lag)))^2+3 ≡ goldenLucas (3^(i+1+n))^2+3
        [ZMOD (p:ℤ)^(2*padicValInt p (goldenLucas (3^i)^2+3)+precision)]) ↔
      orderOf (9 : ZMod (p^precision)) ∣ lag := by
  rw [periods_of_exact_lags p _ precision hp (previous_block_depth_pos p i hp hB)
    (previous_block_prime_coprime_nine p i hp hi hB)
    (fun j => goldenLucas (3^(i+1+j))^2+3)
    (fun a b hab => golden_cubic_tail_clock_valuation p i a b hp hi hab hB)]
  rw [orderOf_dvd_iff_pow_eq_one]
  simpa only [Int.cast_pow, Int.cast_ofNat, Int.cast_one, Nat.cast_pow]
    using (ZMod.intCast_eq_intCast_iff ((9:ℤ)^lag) 1 (p^precision)).symm

end D5.S3.Arith.Primes.GoldenCubicBlockLagValuation
