/- GID: D5/S3/Arith/Primes/GoldenCubicNonbranchReturn
   generality: G
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicNonbranchReturn
   mirror-E: none(waiver:proved-all-precision-signed-cubic-period)
   anchors: []
   utility: none
   digest: A signed Laurent return determines the least period of the cubic trace above every periodic nonbranch odd-prime residue. -/

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.QuadraticAlgebra.Defs
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Prime.Pow
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators

namespace D5.S3.Arith.Primes.GoldenCubicNonbranchReturn

/-- One signed Lucas tripling step on the literal trace. -/
def step {R : Type*} [CommRing R] (x : R) : R := x^3+3*x

/-- Iterate the literal cubic trace recurrence. -/
def trace {R : Type*} [CommRing R] : ℕ → R → R
  | 0,x => x
  | j+1,x => step (trace j x)

private theorem trace_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (n : ℕ) (x : R) : f (trace n x)=trace n (f x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [trace,step,ih,map_ofNat]

private theorem trace_add {R : Type*} [CommRing R] (i j : ℕ) (x : R) :
    trace (i+j) x=trace j (trace i x) := by
  induction j with
  | zero => simp [trace]
  | succ j ih => rw [←Nat.add_assoc,trace,trace,ih]

section
variable {R : Type*} [CommRing R]

/-- Linear binomial approximation with an explicit quadratic remainder
over any commutative ring. -/
private theorem linear_remainder (x : R) (n : ℕ) :
    ∃ t : R, (1+x)^n-1=(n:R)*x+x^2*t := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨t,ht⟩ := ih
    refine ⟨(n:R)+t*(1+x), ?_⟩
    rw [pow_succ, show (1+x)^n=1+((n:R)*x+x^2*t) by linear_combination ht,
      Nat.cast_succ]
    ring

private theorem lift_nat_exponent (p d n : ℕ) (hd : 0<d) (v : R) :
    ∃ t : R, (1+(p:R)^d*v)^n-1=(p:R)^d*((n:R)*v+(p:R)*t) := by
  obtain ⟨t,ht⟩ := linear_remainder ((p:R)^d*v) n
  refine ⟨(p:R)^(d-1)*v^2*t,?_⟩
  rw [ht]
  have h : (p:R)^(d-1)*(p:R)=(p:R)^d := by
    rw [←pow_succ, Nat.sub_add_cancel hd]
  have he : (p:R)*((p:R)^(d-1)*v^2*t)=(p:R)^d*v^2*t := by
    calc
      _ = ((p:R)^(d-1)*(p:R))*v^2*t := by ring
      _ = _ := by rw [h]
  rw [he]
  ring

/-- Raising a 1-unit to the (odd) prime multiplies its leading p-adic
layer by p, without assuming that p is prime in the target ring. -/
private theorem lift_prime_exponent {p d : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hd : 0<d) (v : R) :
    ∃ t : R, (1+(p:R)^d*v)^p-1=(p:R)^(d+1)*(v+(p:R)*t) := by
  let P : R := p
  let x := P^d*v
  let f := fun i : ℕ => x^i * (p.choose i:R)
  let T := ∑ i ∈ Finset.range (p-1), f (i+1+1)
  have hT : P^(d+2) ∣ T := by
    apply Finset.dvd_sum
    intro j hj
    have hi : j+1+1 ≤ p := by
      have h := Finset.mem_range.mp hj
      omega
    let i := j+1+1
    change P^(d+2) ∣ f i
    have h2 : 2 ≤ i := by dsimp [i]; omega
    have hi' : i ≤ p := hi
    have hx : x^i=P^(d*i)*v^i := by rw [show x=P^d*v from rfl,mul_pow,pow_mul]
    by_cases hl : i=p
    · have hle : d+2 ≤ d*i := by
        have hh : 3*d ≤ i*d := Nat.mul_le_mul_right d (by omega)
        rw [Nat.mul_comm i d] at hh
        omega
      rw [show f i=x^i*(p.choose i:R) from rfl,hx]
      exact dvd_trans (pow_dvd_pow P hle) (dvd_mul_right _ _ |>.trans (dvd_mul_right _ _))
    · obtain ⟨c,hc⟩ := hp.dvd_choose_self (show i≠0 by omega) (show i<p by omega)
      have he : (p.choose i:R) = P*(c:R) := by rw [hc,Nat.cast_mul]
      have hle : d+2 ≤ d*i+1 := by
        have hh : 2*d ≤ i*d := Nat.mul_le_mul_right d h2
        rw [Nat.mul_comm i d] at hh
        omega
      rw [show f i=x^i*(p.choose i:R) from rfl,hx,he,
        show P^(d*i)*v^i*(P*(c:R))=P^(d*i+1)*(v^i*(c:R)) by rw [pow_succ]; ring]
      exact dvd_trans (pow_dvd_pow P hle) (dvd_mul_right _ _)
  obtain ⟨t,ht⟩ := hT
  have he : (1+x)^p-1=x*P+T := by
    rw [add_comm 1 x,add_pow]
    simp only [one_pow,mul_one]
    change (∑ i ∈ Finset.range (p+1), f i)-1=x*P+T
    rw [show p+1=(p-1)+1+1 by omega,Finset.sum_range_succ',Finset.sum_range_succ']
    simp [f,T,P,Nat.choose_one_right]
    ring
  refine ⟨t,?_⟩
  change (1+x)^p-1=P^(d+1)*(v+P*t)
  rw [he,ht,show x=P^d*v from rfl,pow_succ P (d+1),pow_succ P d]
  ring

/-- Any number of prime-power lifts preserves the first nonzero coefficient
when measured after the shifted p-power. -/
private theorem lift_prime_power {p d : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hd : 0<d) (v : R) (e : ℕ) :
    ∃ t : R, (1+(p:R)^d*v)^(p^e)-1=(p:R)^(d+e)*(v+(p:R)*t) := by
  induction e with
  | zero => exact ⟨0, by simp⟩
  | succ e ih =>
    obtain ⟨t,ht⟩ := ih
    obtain ⟨u,hu⟩ := lift_prime_exponent hp hp3 (show 0<d+e by omega) (v+(p:R)*t)
    refine ⟨t+u, ?_⟩
    rw [pow_succ p e,pow_mul,
      show (1+(p:R)^d*v)^(p^e)=1+(p:R)^(d+e)*(v+(p:R)*t) by
        linear_combination ht,hu,←Nat.add_assoc]
    ring

/-- With no primality of p in R, compute the exact leading coefficient for
a general exponent presented as a prime power times a residual exponent. -/
private theorem lift_factored_exponent {p d : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hd : 0<d) (v : R) (e k : ℕ) :
    ∃ t : R,
      (1+(p:R)^d*v)^(p^e*k)-1=(p:R)^(d+e)*((k:R)*v+(p:R)*t) := by
  obtain ⟨t,ht⟩ := lift_prime_power hp hp3 hd v e
  obtain ⟨u,hu⟩ := lift_nat_exponent p (d+e) k (by omega) (v+(p:R)*t)
  refine ⟨(k:R)*t+u, ?_⟩
  rw [pow_mul,show (1+(p:R)^d*v)^(p^e)=1+(p:R)^(d+e)*(v+(p:R)*t) by
          linear_combination ht,hu]
  ring

/-- The residual exponent in the leading coefficient is prime to p. -/
private theorem lift_exact_nat {p d m : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hd : 0<d) (hm : m≠0) (v : R) :
    ∃ k : ℕ, ¬p∣k ∧ ∃ t : R, (1+(p:R)^d*v)^m-1 =
        (p:R)^(d+padicValNat p m)*((k:R)*v+(p:R)*t) := by
  let : Fact p.Prime := ⟨hp⟩
  have hmdiv : p^(padicValNat p m)∣m := (padicValNat_dvd_iff_le hm).2 le_rfl
  obtain ⟨k,hk⟩ := hmdiv
  have hn : ¬p∣k := by
    rintro ⟨c,hc⟩
    apply pow_succ_padicValNat_not_dvd (p:=p) hm
    exact ⟨c, hk.trans (by rw [hc,pow_succ,mul_assoc])⟩
  refine ⟨k,hn,?_⟩
  obtain ⟨t,ht⟩ := lift_factored_exponent hp hp3 hd v (padicValNat p m) k
  exact ⟨t,(congrArg (fun n : ℕ => (1+(p:R)^d*v)^n-1) hk).trans ht⟩

/-- Multiplicative units preserve every divisibility layer in both directions. -/
private theorem dvd_mul_unit_right_iff (a x : R) (u : Rˣ) :
    a ∣ x*(u:R) ↔ a ∣ x := by
  constructor
  · rintro ⟨c,hc⟩
    refine ⟨c*((u⁻¹:Rˣ):R),?_⟩
    have he := congrArg (fun v : R => v*((u⁻¹:Rˣ):R)) hc
    simpa only [mul_assoc,Units.mul_inv,mul_one] using he
  · rintro ⟨c,hc⟩
    exact ⟨c*(u:R),by rw [hc,mul_assoc]⟩

private theorem unit_zpow_sub_one_negative_dvd (a : R) (u : Rˣ) (n : ℕ) :
    a ∣ (((u^(-(n:ℤ)):Rˣ):R)-1) ↔ a ∣ (((u^n:Rˣ):R)-1) := by
  rw [zpow_neg,zpow_natCast]
  let U : Rˣ := u^n
  change a ∣ (((U⁻¹:Rˣ):R)-1) ↔ a ∣ ((U:R)-1)
  have hf : (((U⁻¹:Rˣ):R)-1) = ((U:R)-1)*(-(U⁻¹:Rˣ):Rˣ) := by
    simp only [Units.val_neg,sub_mul,mul_neg,Units.mul_inv]
    ring
  rw [hf]
  exact dvd_mul_unit_right_iff a _ _

/-- The intrinsic divisibility filtration needs cancellability of the
scalar p, not a domain hypothesis on R. -/
private theorem exact_layer_iff (P x v : R) (d s : ℕ)
    (hc : Function.Injective (fun z : R => P*z))
    (hv : ¬P∣v) (hx : x=P^d*v) : P^s∣x ↔ s ≤ d := by
  have hc' (n : ℕ) : Function.Injective (fun z : R => P^n*z) := by
    induction n with
    | zero => intro y z e; simpa using e
    | succ n ih =>
      intro y z e
      change P^(n+1)*y=P^(n+1)*z at e
      simp only [pow_succ,mul_assoc] at e
      exact hc (ih e)
  constructor
  · intro h
    by_contra hsd
    obtain ⟨y,hy⟩ := dvd_trans (pow_dvd_pow P (by omega : d+1 ≤ s)) h
    rw [hx,pow_succ,mul_assoc] at hy
    exact hv ⟨y,hc' d hy⟩
  · intro h
    rw [hx]
    exact dvd_trans (pow_dvd_pow P h) (dvd_mul_right _ _)

/-- Exact coefficient depth as a divisibility predicate, for signed
exponents. The residue ring need not be a domain. -/
private theorem exact_unit_zpow_dvd {S : Type*} [CommRing S] {p d : ℕ}
    (hp : p.Prime) (hp3 : 3 ≤ p) (hd : 0<d)
    (ρ : R →+* S) (hρ : ρ (p:R)=0)
    (hunits : ∀ k : ℕ, ¬p∣k → IsUnit (k:S))
    (hc : Function.Injective (fun z : R => (p:R)*z))
    (u : Rˣ) (v : R) (hu : (u:R)=1+(p:R)^d*v) (hv : ρ v≠0)
    (m : ℤ) (s : ℕ) :
    (p:R)^s ∣ (((u^m:Rˣ):R)-1) ↔ m=0 ∨ s ≤ d+padicValInt p m := by
  have H (n : ℕ) (hn : n≠0) :
      (p:R)^s∣(((u^n:Rˣ):R)-1) ↔ s ≤ d+padicValNat p n := by
    obtain ⟨k,hk,t,ht⟩ := lift_exact_nat hp hp3 hd hn v
    rw [Units.val_pow_eq_pow_val,hu]
    apply exact_layer_iff _ _ _ _ _ hc _ ht
    intro hh
    obtain ⟨z,hz⟩ := hh
    have he := congrArg ρ hz
    simp only [map_add,map_mul,map_natCast,hρ,zero_mul,add_zero] at he
    have he' : (k:S)*ρ v=0 := by
      simpa only [map_natCast,hρ,zero_mul] using he
    obtain ⟨w,hw⟩ := hunits k hk
    rw [←hw] at he'
    have hz := congrArg (fun x : S => (((w⁻¹:Sˣ):S))*x) he'
    rw [←mul_assoc, Units.inv_mul, one_mul, mul_zero] at hz
    exact hv hz
  cases m with
  | ofNat n =>
    by_cases hn : n=0
    · subst n
      simp
    · change (p:R)^s ∣ (((u^(n:ℤ):Rˣ):R)-1) ↔ (n:ℤ)=0 ∨ _
      have hvn : padicValInt p (Int.ofNat n)=padicValNat p n := padicValInt.of_nat (n:=n)
      rw [hvn,zpow_natCast,show ((n:ℤ)=0) ↔ False from iff_false_intro (Int.natCast_ne_zero.mpr hn),false_or]
      exact H n hn
  | negSucc n =>
    have he : Int.negSucc n = -((n+1:ℕ):ℤ) := by omega
    rw [he,unit_zpow_sub_one_negative_dvd]
    have hn : n+1≠0 := Nat.succ_ne_zero n
    have hneg : -((n+1:ℕ):ℤ)≠0 := neg_ne_zero.mpr (Int.natCast_ne_zero.mpr hn)
    rw [show (-((n+1:ℕ):ℤ)=0) ↔ False from iff_false_intro hneg,false_or]
    change _ ↔ s ≤ d+padicValNat p (-((n+1:ℕ):ℤ)).natAbs
    rw [Int.natAbs_neg,Int.natAbs_natCast]
    exact H (n+1) hn
end

section
private abbrev Quad {R : Type*} [CommRing R] (y : R) := QuadraticAlgebra R 1 y

private def gen {R : Type*} [CommRing R] (y : R) : (Quad y)ˣ where
  val := ⟨0,1⟩
  inv := ⟨-y,1⟩
  val_inv := by ext <;> simp [QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]
  inv_val := by ext <;> simp [QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]

/-- Laurent trace is meaningful over any commutative ring, not just fields. -/
private def uTrace {R : Type*} [CommRing R] (v : Rˣ) : R :=
  (v:R)-((v⁻¹:Rˣ):R)

private theorem gen_trace {R : Type*} [CommRing R] (y : R) :
    uTrace (gen y) = algebraMap R (Quad y) y := by
  ext <;> simp [uTrace,gen]

private theorem uTrace_cubing {R : Type*} [CommRing R] (v : Rˣ) (n : ℕ) :
    trace n (uTrace v) = uTrace (v^3^n) := by
  induction n with
  | zero => simp [trace]
  | succ n ih =>
    rw [trace,ih,pow_succ (3:ℕ),pow_mul]
    let u : Rˣ := v^3^n
    let a : R := u
    let b : R := (u⁻¹:Rˣ)
    change step (uTrace u)=uTrace (u^3)
    simp only [uTrace,←inv_pow,Units.val_pow_eq_pow_val,step]
    change (a-b)^3+3*(a-b)=a^3-b^3
    have h : a*b=1 := Units.mul_inv u
    linear_combination -3*(a-b)*h

private theorem uTrace_flip {R : Type*} [CommRing R] (v : Rˣ) :
    uTrace (-v⁻¹) = uTrace v := by
  simp [uTrace,sub_eq_add_neg,add_comm]

def multiplier (flip : Bool) (k : ℕ) : ℤ := if flip then -(k:ℤ) else k

private def eps {R : Type*} [CommRing R] (flip : Bool) : Rˣ := if flip then -1 else 1

/-- An orientation-adjusted lift of one chosen iterate. The negative
orientation changes v^k by the deck involution −(v^k)⁻¹. -/
private def lift {R : Type*} [CommRing R] (flip : Bool) (k : ℕ) (v : Rˣ) : Rˣ :=
  eps flip * v^(multiplier flip k)

private def geo (m : ℤ) : ℕ → ℤ
  | 0 => 0
  | n+1 => 1+m*geo m n

private def baseUnit {R : Type*} [CommRing R] (flip : Bool) (k : ℕ) (v : Rˣ) : Rˣ :=
  eps flip * v^(multiplier flip k-1)

private theorem lift_trace {R : Type*} [CommRing R] (flip : Bool) (ell : ℕ) (v : Rˣ) :
    uTrace (lift flip (3^ell) v) = trace ell (uTrace v) := by
  rw [uTrace_cubing]
  cases flip
  · change uTrace ((1:Rˣ)*v^((3^ell:ℕ):ℤ))=uTrace (v^3^ell)
    rw [zpow_natCast,one_mul]
  · change uTrace ((-1:Rˣ)*v^(-((3^ell:ℕ):ℤ)))=uTrace (v^3^ell)
    rw [zpow_neg,zpow_natCast,neg_one_mul]
    exact uTrace_flip (v^3^ell)

private theorem lift_current {R : Type*} [CommRing R] (flip : Bool) (k : ℕ) (v : Rˣ) :
    lift flip k v = v * baseUnit flip k v := by
  have h : v*v^(multiplier flip k-1)=v^(multiplier flip k) := by
    calc
      _ = v^(1:ℤ)*v^(multiplier flip k-1) := by rw [zpow_one]
      _ = _ := by rw [←zpow_add]; congr 1; omega
  rw [lift,baseUnit,mul_left_comm,h]

/-- The signed geometric series encodes all iterates, including an
arbitrary negative exponent. No p-adic or field argument enters. -/
private theorem lift_factor {R : Type*} [CommRing R] (flip : Bool) (k : ℕ) (v : Rˣ) (n : ℕ) :
    ((lift flip k)^[n]) v = v * (baseUnit flip k v)^(geo (multiplier flip k) n) := by
  induction n with
  | zero => simp [geo]
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih,geo,zpow_add,zpow_mul]
    rw [lift,mul_zpow,←mul_assoc,←lift, lift_current]
    simp only [mul_assoc]
    rw [←zpow_mul,←zpow_mul,mul_comm (geo (multiplier flip k) n)]
    rw [zpow_one]

private theorem all_lift_trace {R : Type*} [CommRing R] (flip : Bool) (ell : ℕ) (v : Rˣ) (n : ℕ) :
    uTrace (((lift flip (3^ell))^[n]) v)=trace (ell*n) (uTrace v) := by
  induction n with
  | zero => simp [trace]
  | succ n ih =>
    rw [Function.iterate_succ_apply',lift_trace,ih,Nat.mul_succ,trace_add]

private theorem uTrace_diff {R : Type*} [CommRing R] (v t : Rˣ) :
    uTrace t-uTrace v = ((t:R)-(v:R))*(1+(((v*t)⁻¹:Rˣ):R)) := by
  let a : R := v
  let b : R := (v⁻¹:Rˣ)
  let c : R := t
  let d : R := (t⁻¹:Rˣ)
  have hab : a*b=1 := Units.mul_inv v
  have hcd : c*d=1 := Units.mul_inv t
  rw [mul_inv_rev,Units.val_mul]
  change (c-d)-(a-b)=(c-a)*(1+d*b)
  linear_combination d*hab-b*hcd

/-- Exact integer quadratic-order factorization of the original WSS
displacement; the signed exponent is the ordinary geometric sum. -/
private theorem integral_displacement (y : ℤ) (flip : Bool) (ell n : ℕ) :
    let v := gen y
    let t := ((lift flip (3^ell))^[n]) v
    let U := baseUnit flip (3^ell) v
    let m := geo (multiplier flip (3^ell)) n
    algebraMap ℤ (Quad y) (trace (ell*n) y-y) =
      (((U^m:(Quad y)ˣ):Quad y)-1)*((v:Quad y)*(1+(((v*t)⁻¹:(Quad y)ˣ):Quad y))) := by
  dsimp only
  rw [map_sub,trace_map,←gen_trace,←all_lift_trace flip ell (gen y) n,uTrace_diff]
  have h := congrArg (fun z : (Quad y)ˣ => (z:Quad y)) (lift_factor flip (3^ell) (gen y) n)
  rw [Units.val_mul] at h
  conv_lhs => arg 1; rw [h]
  ring
end

section
/-- Base change on the free rank-two coefficients, available even if
the target ring is not a field. -/
private def quadMap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (y : R) :
    Quad y →+* Quad (f y) where
  toFun v := ⟨f v.re,f v.im⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp [QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]
  map_add' x z := by ext <;> simp
  map_mul' x z := by ext <;> simp

private def conjugate {R : Type*} [CommRing R] (y : R) : Quad y →+* Quad y where
  toFun x := ⟨x.re+y*x.im,-x.im⟩
  map_one' := by ext <;> simp [QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp <;> ring
  map_mul' a b := by ext <;> simp <;> ring

/-- The sign of a nonbranch return is consistent in the genuine residue
quadratic algebra. No factor-is-a-domain or splitting-field assumption
is made on that algebra; only the scalar field is used for b²=1. -/
private theorem orientation {K : Type*} [Field K] (y : K) (h2 : (2:K)≠0)
    (hD : y^2+4≠0) (ell : ℕ) (ht : trace ell y=y) :
    (gen y)^3^ell=gen y ∨ (gen y)^3^ell= -(gen y)⁻¹ := by
  let u := gen y
  let v := u^3^ell
  let a : K := (v:Quad y).re
  let b : K := (v:Quad y).im
  have huconj : conjugate y (u:Quad y)= -((u⁻¹:(Quad y)ˣ):Quad y) := by
    ext <;> simp [conjugate,u,gen]
  have hconj : conjugate y (v:Quad y)= -((v⁻¹:(Quad y)ˣ):Quad y) := by
    change conjugate y ((u^3^ell:(Quad y)ˣ):Quad y)= -(((u^3^ell)⁻¹:(Quad y)ˣ):Quad y)
    simp only [Units.val_pow_eq_pow_val,map_pow,huconj,←inv_pow]
    have hodd : Odd ((3:ℕ)^ell) := (by decide : Odd (3:ℕ)).pow
    exact hodd.neg_pow _
  have hsum : (v:Quad y)+conjugate y (v:Quad y)=algebraMap K (Quad y) y := by
    rw [hconj,←sub_eq_add_neg]
    change uTrace (u^3^ell)=_
    rw [←uTrace_cubing,gen_trace,←trace_map,ht]
  have hprod : (v:Quad y)*conjugate y (v:Quad y)= -1 := by
    rw [hconj,mul_neg,Units.mul_inv]
  have hl : 2*a+y*b=y := by
    have h := congrArg QuadraticAlgebra.re hsum
    change a+(a+y*b)=y at h
    linear_combination h
  have hn : a*(a+y*b)-b^2= -1 := by
    have h := congrArg QuadraticAlgebra.re hprod
    change a*(a+y*b)+1*b*(-b)= -(1:K) at h
    linear_combination h
  have hzero : (y^2+4)*(b^2-1)=0 := by
    linear_combination (2*a+y*b+y)*hl-4*hn
  have hB : b^2-1=0 := (mul_eq_zero.mp hzero).resolve_left hD
  have hb : b=1 ∨ b= -1 := by
    have H : (b-1)*(b+1)=0 := by linear_combination hB
    simpa [sub_eq_zero,←eq_neg_iff_add_eq_zero] using mul_eq_zero.mp H
  change v=u ∨ v= -u⁻¹
  rcases hb with hh|hh
  · have ha : a=0 := by
      rw [hh] at hl
      have H : 2*a=0 := by linear_combination hl
      exact (mul_eq_zero.mp H).resolve_left h2
    left
    apply Units.ext
    exact QuadraticAlgebra.ext ha hh
  · have ha : a=y := by
      rw [hh] at hl
      have H : 2*(a-y)=0 := by linear_combination hl
      exact sub_eq_zero.mp ((mul_eq_zero.mp H).resolve_left h2)
    right
    apply Units.ext
    have har : ((-u⁻¹:(Quad y)ˣ):Quad y).re=y := by simp [u,gen]
    exact QuadraticAlgebra.ext (ha.trans har.symm) hh

private theorem residue_fixed_orientation {K : Type*} [Field K]
    (y : K) (h2 : (2:K)≠0) (hD : y^2+4≠0) (ell : ℕ) (ht : trace ell y=y) :
    ∃ flip : Bool, lift flip (3^ell) (gen y)=gen y := by
  rcases orientation y h2 hD ell ht with h|h
  · refine ⟨false,?_⟩
    change (1:(Quad y)ˣ)*(gen y)^((3^ell:ℕ):ℤ)=gen y
    rw [zpow_natCast,one_mul,h]
  · refine ⟨true,?_⟩
    change (-1:(Quad y)ˣ)*(gen y)^(-((3^ell:ℕ):ℤ))=gen y
    rw [zpow_neg,zpow_natCast,neg_one_mul,h,inv_neg,inv_inv,neg_neg]
end

section
private abbrev reduce (p : ℕ) (y : ℤ) : Quad y →+* Quad (y:ZMod p) :=
  quadMap (Int.castRingHom (ZMod p)) y

private theorem mapUnit_neg {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (u : Rˣ) : Units.map f.toMonoidHom (-u) = -(Units.map f.toMonoidHom u) := by
  apply Units.ext
  simp [Units.coe_map,Units.val_neg]

private theorem map_gen {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (y : R) :
    Units.map (quadMap f y).toMonoidHom (gen y)=gen (f y) := by
  apply Units.ext
  ext <;> simp [quadMap,gen]

private theorem map_lift {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (flip : Bool) (k : ℕ) (u : Rˣ) :
    Units.map f.toMonoidHom (lift flip k u) = lift flip k (Units.map f.toMonoidHom u) := by
  unfold lift
  rw [map_mul,map_zpow]
  cases flip <;> simp [eps]

private theorem map_lift_iterate {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (flip : Bool) (k : ℕ) (u : Rˣ)
    (hfix : lift flip k (Units.map f.toMonoidHom u)=Units.map f.toMonoidHom u) (n : ℕ) :
    Units.map f.toMonoidHom (((lift flip k)^[n]) u)=Units.map f.toMonoidHom u := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',map_lift,ih,hfix]

private theorem reduce_baseUnit {p : ℕ} (y : ℤ) (flip : Bool) (k : ℕ)
    (hfix : lift flip k (gen (y:ZMod p))=gen (y:ZMod p)) :
    reduce p y ((baseUnit flip k (gen y): (Quad y)ˣ):Quad y)=1 := by
  let f := (reduce p y).toMonoidHom
  have H : Units.map f (lift flip k (gen y))=Units.map f (gen y) := by
    rw [map_lift (reduce p y)]
    change lift flip k (Units.map (quadMap (Int.castRingHom (ZMod p)) y).toMonoidHom (gen y))=
      Units.map (quadMap (Int.castRingHom (ZMod p)) y).toMonoidHom (gen y)
    rw [map_gen (Int.castRingHom (ZMod p)) y]
    exact hfix
  rw [lift_current,map_mul] at H
  have H' : Units.map f (baseUnit flip k (gen y))=1 :=
    mul_left_cancel (by simpa only [mul_one] using H)
  exact congrArg (fun u : (Quad (y:ZMod p))ˣ => (u:Quad (y:ZMod p))) H'

private theorem disc_unit {K : Type*} [Field K] (y : K) (hD : y^2+4≠0) :
    IsUnit ((gen y:Quad y)+(((gen y)⁻¹:(Quad y)ˣ):Quad y)) := by
  let d : Quad y := (gen y:Quad y)+(((gen y)⁻¹:(Quad y)ˣ):Quad y)
  have h : d^2=algebraMap K (Quad y) (y^2+4) := by
    have hd : d=⟨-y,2⟩ := by ext <;> simp [d,gen,one_add_one_eq_two]
    rw [hd,pow_two]
    ext <;> simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,
      QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.algebraMap_im] <;> ring
  apply IsUnit.of_mul_eq_one (d * algebraMap K (Quad y) (y^2+4)⁻¹)
  rw [←mul_assoc,←pow_two,h,←map_mul,mul_inv_cancel₀ hD,map_one]

private def tailFactor (y : ℤ) (flip : Bool) (k n : ℕ) : Quad y :=
  let u := gen y
  let t := ((lift flip k)^[n]) u
  (u:Quad y)*(1+(((u*t)⁻¹:(Quad y)ˣ):Quad y))

private theorem tailFactor_unit_modp {p : ℕ} [Fact p.Prime] (y : ℤ) (flip : Bool) (k n : ℕ)
    (hfix : lift flip k (gen (y:ZMod p))=gen (y:ZMod p))
    (hD : (y:ZMod p)^2+4≠0) :
    IsUnit (reduce p y (tailFactor y flip k n)) := by
  let f := reduce p y
  let u := gen (y:ZMod p)
  have hmap : Units.map f.toMonoidHom (gen y)=u := map_gen _ _
  have ht : Units.map f.toMonoidHom (((lift flip k)^[n]) (gen y))=u := by
    apply (map_lift_iterate f flip k (gen y) (by rwa [hmap]) n).trans hmap
  have hu := disc_unit (y:ZMod p) hD
  unfold tailFactor
  change IsUnit (f ((gen y:Quad y)*(1+((((gen y)*((lift flip k)^[n]) (gen y))⁻¹:(Quad y)ˣ):Quad y))))
  rw [map_mul,map_add,map_one]
  have hv : f ((gen y:Quad y))=(u:Quad (y:ZMod p)) :=
    congrArg (fun v : (Quad (y:ZMod p))ˣ => (v:Quad (y:ZMod p))) hmap
  have hinv :
      f ((((gen y)*((lift flip k)^[n]) (gen y))⁻¹:(Quad y)ˣ):Quad y) =
        (((u*u)⁻¹:(Quad (y:ZMod p))ˣ):Quad (y:ZMod p)) := by
    change ((Units.map f.toMonoidHom _:(Quad (y:ZMod p))ˣ):Quad (y:ZMod p))=_
    rw [map_inv,map_mul,hmap,ht]
  rw [hv,hinv]
  change IsUnit ((u:Quad (y:ZMod p))*(1+(((u*u)⁻¹:(Quad (y:ZMod p))ˣ):Quad (y:ZMod p))))
  rw [mul_add,mul_one,mul_inv_rev,Units.val_mul,←mul_assoc,Units.mul_inv,one_mul]
  exact hu

private def normCoord {R : Type*} [CommRing R] {y : R} (z : Quad y) : R :=
  z.re^2+y*z.re*z.im-z.im^2

private theorem mul_conj_norm {R : Type*} [CommRing R] {y : R} (z : Quad y) :
    z*conjugate y z = algebraMap R (Quad y) (normCoord z) := by
  ext <;> simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,
    QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.algebraMap_im,conjugate,normCoord] <;> dsimp <;> ring

private theorem norm_maps {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {y : R}
    (u : Quad y) : normCoord (quadMap f y u)=f (normCoord u) := by
  simp [quadMap,normCoord]

private theorem scalar_unit_of_modp {p : ℕ} [Fact p.Prime] (k : ℕ) (a : ℤ)
    (ha : (a:ZMod p)≠0) : IsUnit (a:ZMod (p^k)) := by
  have hp : Nat.Prime p := Fact.out
  have hn : ¬ p∣a.natAbs := by
    intro h
    exact ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mpr (Int.ofNat_dvd_left.mpr h))
  have h : IsUnit (a.natAbs:ZMod (p^k)) :=
    (ZMod.isUnit_iff_coprime a.natAbs (p^k)).mpr
      ((hp.coprime_iff_not_dvd.mpr hn).symm.pow_right _)
  cases a with
  | ofNat a => simpa using h
  | negSucc a => simpa using h.neg

private theorem reduce_unit_at_power {p : ℕ} [Fact p.Prime] (y : ℤ) (u : Quad y)
    (hu : IsUnit (reduce p y u)) (k : ℕ) :
    IsUnit (reduce (p^k) y u) := by
  have hn : ((normCoord u:ℤ):ZMod p)≠0 := by
    intro he
    have H := hu.mul (hu.map (conjugate (y:ZMod p)))
    rw [mul_conj_norm,norm_maps] at H
    change IsUnit (algebraMap (ZMod p) (Quad (y:ZMod p)) ((normCoord u:ℤ):ZMod p)) at H
    rw [he,map_zero] at H
    exact H.ne_zero rfl
  have hh := (scalar_unit_of_modp k (normCoord u) hn).map (algebraMap (ZMod (p^k)) (Quad (y:ZMod (p^k))))
  change IsUnit (algebraMap (ZMod (p^k)) (Quad (y:ZMod (p^k)))
    ((Int.castRingHom (ZMod (p^k))) (normCoord u))) at hh
  rw [←norm_maps (Int.castRingHom (ZMod (p^k))) u,←mul_conj_norm] at hh
  exact isUnit_of_mul_isUnit_left hh

/-- Exact coordinatewise kernel of reduction, including exponent zero. -/
private theorem scalar_dvd_iff_reduce_zero (m : ℕ) (y : ℤ) (z : Quad y) :
    algebraMap ℤ (Quad y) (m:ℤ)∣z ↔ reduce m y z=0 := by
  rw [QuadraticAlgebra.algebraMap_dvd_iff]
  change _ ↔ (⟨(z.re:ZMod m),(z.im:ZMod m)⟩:Quad (y:ZMod m))=0
  rw [QuadraticAlgebra.ext_iff]
  simp [ZMod.intCast_zmod_eq_zero_iff_dvd]

private theorem mul_preserves_scalar_dvd {p : ℕ} [Fact p.Prime]
    (y : ℤ) (u z : Quad y) (hu : IsUnit (reduce p y u)) (k : ℕ) :
    (algebraMap ℤ (Quad y) ((p^k:ℕ):ℤ) ∣ z*u) ↔
      (algebraMap ℤ (Quad y) ((p^k:ℕ):ℤ) ∣ z) := by
  rw [scalar_dvd_iff_reduce_zero,scalar_dvd_iff_reduce_zero,map_mul]
  have hU := reduce_unit_at_power y u hu k
  exact ⟨fun h => hU.mul_right_cancel (by simpa using h),fun h => by simp [h]⟩

private theorem nonbranch_integral_content {p : ℕ} [Fact p.Prime] (y : ℤ) (ell : ℕ)
    (h2 : (2:ZMod p)≠0) (hD : (y:ZMod p)^2+4≠0)
    (hr : trace ell (y:ZMod p)=(y:ZMod p)) :
    ∃ flip : Bool,
      let U := baseUnit flip (3^ell) (gen y)
      let μ := multiplier flip (3^ell)
      reduce p y (U:Quad y)=1 ∧
      ∀ n k : ℕ, ((p^k:ℕ):ℤ)∣trace (ell*n) y-y ↔
        algebraMap ℤ (Quad y) ((p^k:ℕ):ℤ) ∣
          (((U^geo μ n:(Quad y)ˣ):Quad y)-1) := by
  obtain ⟨flip,hflip⟩ := residue_fixed_orientation (y:ZMod p) h2 hD ell hr
  refine ⟨flip,reduce_baseUnit y flip (3^ell) hflip,?_⟩
  intro n k
  let t := (((baseUnit flip (3^ell) (gen y))^geo (multiplier flip (3^ell)) n:(Quad y)ˣ):Quad y)-1
  have h := integral_displacement y flip ell n
  change algebraMap ℤ (Quad y) (trace (ell*n) y-y)=t*tailFactor y flip (3^ell) n at h
  rw [←QuadraticAlgebra.algebraMap_dvd_iff_dvd, h]
  exact mul_preserves_scalar_dvd y _ _ (tailFactor_unit_modp y flip (3^ell) n hflip hD) k
end

section
private theorem scalar_trace {R : Type*} [CommRing R] {y : R} (z : Quad y) :
    z+conjugate y z = algebraMap R (Quad y) (2*z.re+y*z.im) := by
  ext <;> simp only [QuadraticAlgebra.re_add,QuadraticAlgebra.im_add,
    QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.algebraMap_im,conjugate] <;> dsimp <;> ring

/-- Frobenius is injective over the nonbranch residue quadratic algebra,
even when it is split and consequently has zero divisors. No extension
field or algebraic closure is used. -/
private theorem residue_frobenius_injective {p : ℕ} [Fact p.Prime] (y : ZMod p)
    (h2 : (2:ZMod p)≠0) (hD : y^2+4≠0) :
    Function.Injective (fun z : Quad y => z^p) := by
  have hp : Nat.Prime p := Fact.out
  let A := Quad y
  let R := ZMod p
  let f := algebraMap R A
  let _ : CharP A p := ⟨fun n => by
    rw [←map_natCast f,←map_zero f]
    have hf : Function.Injective f := QuadraticAlgebra.algebraMap_injective
    rw [hf.eq_iff]
    exact CharP.cast_eq_zero_iff R p n⟩
  have H (z : A) (hz : z^p=0) : z=0 := by
    have hcon : (conjugate y z)^p=0 := by rw [←map_pow,hz,map_zero]
    have hsum : (z+conjugate y z)^p=0 := by rw [add_pow_char _ _ p,hz,hcon,add_zero]
    have hprod : (z*conjugate y z)^p=0 := by rw [mul_pow,hz,zero_mul]
    rw [scalar_trace,←map_pow] at hsum
    rw [mul_conj_norm,←map_pow] at hprod
    have hlin : 2*z.re+y*z.im=0 := pow_eq_zero_iff hp.ne_zero |>.mp
      (QuadraticAlgebra.algebraMap_injective (R:=R) (a:=1) (b:=y)
        (hsum.trans (map_zero f).symm))
    have hn : normCoord z=0 := pow_eq_zero_iff hp.ne_zero |>.mp
      (QuadraticAlgebra.algebraMap_injective (R:=R) (a:=1) (b:=y)
        (hprod.trans (map_zero f).symm))
    have hd : (y^2+4)*z.im^2=0 := by
      unfold normCoord at hn
      linear_combination (2*z.re+y*z.im)*hlin-4*hn
    have him : z.im=0 :=
      (pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp
        ((mul_eq_zero.mp hd).resolve_left hD)
    have hre : z.re=0 := by
      rw [him,mul_zero,add_zero] at hlin
      exact (mul_eq_zero.mp hlin).resolve_left h2
    exact QuadraticAlgebra.ext hre him
  intro v w he
  change v^p=w^p at he
  apply sub_eq_zero.mp
  exact H (v-w) (by rw [sub_pow_char,he,sub_self])

private theorem residue_prime_power_injective {p : ℕ} [Fact p.Prime] (y : ZMod p)
    (h2 : (2:ZMod p)≠0) (hD : y^2+4≠0) (e : ℕ) :
    Function.Injective (fun z : Quad y => z^(p^e)) := by
  induction e with
  | zero =>
    intro u v h
    change u^(p^0)=v^(p^0) at h
    simpa only [pow_zero,pow_one] using h
  | succ e ih =>
    intro u v h
    apply ih
    apply residue_frobenius_injective y h2 hD
    change u^(p^(e+1))=v^(p^(e+1)) at h
    simpa only [pow_succ (n:=e),pow_mul] using h

/-- A signed p-unit anchor reduces to 1 whenever its p^e-th power equals
the residue return unit. This is the exact no-extension bridge for h≥1. -/
private theorem signed_anchor_principal {p : ℕ} [Fact p.Prime] (hp2 : 2<p)
    (y : ℤ) (flip : Bool) (k e : ℕ) (N : ℤ)
    (hN : multiplier flip k-1=(p:ℤ)^e*N)
    (h2 : (2:ZMod p)≠0) (hD : (y:ZMod p)^2+4≠0)
    (hU : reduce p y ((baseUnit flip k (gen y):(Quad y)ˣ):Quad y)=1) :
    let V : (Quad y)ˣ := eps flip * (gen y)^N
    V^(p^e)=baseUnit flip k (gen y) ∧ reduce p y (V:Quad y)=1 := by
  dsimp only
  have hp : Nat.Prime p := Fact.out
  have hOdd : Odd (p^e) := (hp.odd_of_ne_two (by omega)).pow
  have hε : (eps flip:(Quad y)ˣ)^(p^e)=eps flip := by
    cases flip
    · simp [eps]
    · exact hOdd.neg_one_pow
  have hV : ((eps flip:(Quad y)ˣ) * gen y ^ N)^(p^e)=baseUnit flip k (gen y) := by
    rw [baseUnit,mul_pow,hε,hN]
    congr 1
    rw [←zpow_natCast,←zpow_mul,Nat.cast_pow,mul_comm N]
  refine ⟨hV,?_⟩
  apply residue_prime_power_injective (y:ZMod p) h2 hD e
  change (reduce p y (((eps flip:(Quad y)ˣ)*gen y ^ N: (Quad y)ˣ):Quad y))^(p^e)=
    (1:Quad (y:ZMod p))^(p^e)
  rw [one_pow,←map_pow,←Units.val_pow_eq_pow_val,hV,hU]
end

section
/-- Divisibility by a scalar in the integral free rank-two ring is exactly
divisibility of both integer coordinates. -/
private theorem quad_scalar_dvd {y a : ℤ} (z : Quad y) :
    (a:Quad y) ∣ z ↔ a ∣ z.re ∧ a ∣ z.im := by
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨⟨t.re,by simp⟩,⟨t.im,by simp⟩⟩
  · rintro ⟨⟨r,hr⟩,⟨i,hi⟩⟩
    refine ⟨⟨r,i⟩,?_⟩
    ext <;> simp [hr,hi]

private theorem quad_natCast_mul_injective {y : ℤ} {p : ℕ} (hp : p≠0) :
    Function.Injective (fun z : Quad y => (p:Quad y)*z) := by
  intro x y h
  apply QuadraticAlgebra.ext
  · have e := congrArg QuadraticAlgebra.re h
    simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.re_natCast,
      QuadraticAlgebra.im_natCast,zero_mul,mul_zero,add_zero] at e
    exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr hp) e
  · have e := congrArg QuadraticAlgebra.im h
    simp only [QuadraticAlgebra.im_mul,QuadraticAlgebra.re_natCast,
      QuadraticAlgebra.im_natCast,zero_mul,mul_zero,add_zero] at e
    exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr hp) e

private theorem pair_exact {p : ℕ} [Fact p.Prime] (a b : ℤ) (h : a≠0 ∨ b≠0) :
    ∃ d : ℕ, (p:ℤ)^d∣a ∧ (p:ℤ)^d∣b ∧
        ¬((p:ℤ)^(d+1)∣a ∧ (p:ℤ)^(d+1)∣b) := by
  by_cases ha : a=0
  · have hb := h.resolve_left (not_not.mpr ha)
    refine ⟨padicValInt p b,ha ▸ dvd_zero _,padicValInt_dvd b,?_⟩
    intro q
    have he := (padicValInt_dvd_iff (padicValInt p b+1) b).1 q.2
    exact he.elim hb (by omega)
  by_cases hb : b=0
  · refine ⟨padicValInt p a,padicValInt_dvd a,hb ▸ dvd_zero _,?_⟩
    intro q
    have he := (padicValInt_dvd_iff (padicValInt p a+1) a).1 q.1
    exact he.elim ha (by omega)
  by_cases hr : padicValInt p a ≤ padicValInt p b
  · refine ⟨padicValInt p a,padicValInt_dvd a,
      (padicValInt_dvd_iff _ b).2 (Or.inr hr),?_⟩
    intro q
    have he := (padicValInt_dvd_iff (padicValInt p a+1) a).1 q.1
    exact he.elim ha (by omega)
  · refine ⟨padicValInt p b,(padicValInt_dvd_iff _ a).2 (Or.inr (by omega)),
      padicValInt_dvd b,?_⟩
    intro q
    have he := (padicValInt_dvd_iff (padicValInt p b+1) b).1 q.2
    exact he.elim hb (by omega)

/-- Every nonzero element has a primitive coefficient pair after taking out
its exact p-power in the free rank-two ring. -/
private theorem quad_content_rep {p : ℕ} [Fact p.Prime] {y : ℤ}
    (z : Quad y) (hz : z≠0) :
    ∃ d : ℕ, ∃ v : Quad y, z=(p:Quad y)^d*v ∧ ¬(p:Quad y)∣v := by
  have h : z.re≠0 ∨ z.im≠0 := by
    by_contra! h0
    exact hz (QuadraticAlgebra.ext h0.1 h0.2)
  obtain ⟨d,hre,him,hn⟩ := pair_exact (p:=p) z.re z.im h
  have hc (k : ℕ) : (p:Quad y)^k=(((p:ℤ)^k : ℤ):Quad y) := by
    rw [Int.cast_pow,Int.cast_natCast]
  have hd : (p:Quad y)^d∣z := by
    rw [hc,quad_scalar_dvd]
    exact ⟨hre,him⟩
  obtain ⟨v,hv⟩ := hd
  refine ⟨d,v,hv,?_⟩
  rintro ⟨u,hu⟩
  have h' : (p:Quad y)^(d+1)∣z := ⟨u,by rw [hv,hu,pow_succ,mul_assoc]⟩
  rw [hc,quad_scalar_dvd] at h'
  exact hn h'
end

section
private theorem pcast_eq {p : ℕ} (y : ℤ) (s : ℕ) :
    (p:Quad y)^s=algebraMap ℤ (Quad y) ((p^s:ℕ):ℤ) := by
  rw [map_natCast,Nat.cast_pow]

private theorem cast_unit {p : ℕ} [Fact p.Prime] (y : ℤ) (k : ℕ) (hk : ¬p∣k) :
    IsUnit (k:Quad (y:ZMod p)) := by
  have hn : (k:ZMod p)≠0 := fun h => hk ((ZMod.natCast_eq_zero_iff k p).1 h)
  have hu : IsUnit (k:ZMod p) := isUnit_iff_ne_zero.mpr hn
  simpa using hu.map (algebraMap (ZMod p) (Quad (y:ZMod p)))

private theorem reduce_p {p : ℕ} (y : ℤ) : reduce p y (p:Quad y)=0 := by
  rw [map_natCast]
  change (algebraMap (ZMod p) (Quad (y:ZMod p))) (p:ZMod p)=0
  rw [ZMod.natCast_self,map_zero]

/-- A 1-unit in the quadratic integer order is either the identity or
has a positive exact p-depth and a primitive two-coordinate quotient. -/
private theorem nontrivial_quad_unit_content {p : ℕ} [Fact p.Prime] (y : ℤ)
    (u : (Quad y)ˣ) (hU : reduce p y (u:Quad y)=1) (hn : (u:Quad y)≠1) :
    ∃ d : ℕ, 0<d ∧ ∃ v : Quad y, (u:Quad y)=1+(p:Quad y)^d*v ∧
      reduce p y v≠0 := by
  obtain ⟨d,v,hv,hprim⟩ := quad_content_rep (p:=p) ((u:Quad y)-1) (sub_ne_zero.mpr hn)
  have hvn : reduce p y v≠0 := by
    intro h
    have ht := (scalar_dvd_iff_reduce_zero p y v).2 h
    exact hprim (by simpa only [map_natCast] using ht)
  have hd : 0<d := by
    by_contra! h0
    have e : d=0 := by omega
    rw [e,pow_zero,one_mul] at hv
    have e' := congrArg (reduce p y) hv
    exact hvn (by simpa only [map_sub,hU,map_one,sub_self] using e'.symm)
  exact ⟨d,hd,v,by linear_combination hv,hvn⟩

private theorem geo_factor (μ : ℤ) (n : ℕ) : (μ-1)*geo μ n=μ^n-1 := by
  induction n with
  | zero => simp [geo]
  | succ n ih =>
    rw [geo,pow_succ]
    linear_combination μ*ih

/-- Exact remaining-depth form of the nonbranch return law: the depth
anchor is strictly positive and the sole lag-dependent term is the
signed multiplier power minus one. -/
private theorem nonbranch_exact_multiplier {p : ℕ} [Fact p.Prime] (hp : 3<p)
    (y : ℤ) (ell : ℕ) (he : 0<ell) (hD : (y:ZMod p)^2+4≠0)
    (hr : trace ell (y:ZMod p)=(y:ZMod p)) :
    ∃ flip : Bool,
      let μ := multiplier flip (3^ell)
      (∀ n, trace (ell*n) y=y) ∨
      ∃ d : ℕ, 0<d ∧ ∀ n s : ℕ,
        ((p^s:ℕ):ℤ)∣trace (ell*n) y-y ↔
          μ^n-1=0 ∨ s ≤ d+padicValInt p (μ^n-1) := by
  have pp : p.Prime := Fact.out
  have h2 : (2:ZMod p)≠0 := fun h => (Nat.not_dvd_of_pos_of_lt (by decide : 0<2) (by omega : 2<p))
    ((ZMod.natCast_eq_zero_iff 2 p).1 h)
  obtain ⟨flip,hU,hcontent⟩ := nonbranch_integral_content (p:=p) y ell h2 hD hr
  let U := baseUnit flip (3^ell) (gen y)
  let μ := multiplier flip (3^ell)
  let e := padicValInt p (μ-1)
  have hmu : μ-1≠0 := by
    have hk : 1<(3:ℕ)^ell := Nat.one_lt_pow he.ne' (by decide)
    have hk' : 1<((3^ell:ℕ):ℤ) := by exact_mod_cast hk
    cases flip <;> simp [μ,multiplier] at * <;> omega
  obtain ⟨N,hN⟩ := padicValInt_dvd (p:=p) (μ-1)
  change μ-1=(p:ℤ)^e*N at hN
  let V : (Quad y)ˣ := eps flip * (gen y)^N
  have ⟨hV,hVr⟩ : V^(p^e)=U ∧ reduce p y (V:Quad y)=1 :=
    signed_anchor_principal (by omega : 2<p) y flip (3^ell) e N hN h2 hD hU
  change V^(p^e)=U at hV
  change reduce p y (V:Quad y)=1 at hVr
  refine ⟨flip,?_⟩
  change (∀ n, trace (ell*n) y=y) ∨ _
  by_cases h : (V:Quad y)=1
  · left
    have h1 : V=1 := Units.ext (by simpa using h)
    have hU1 : U=1 := by simpa [h1] using hV.symm
    intro n
    have H := integral_displacement y flip ell n
    change algebraMap ℤ (Quad y) (trace (ell*n) y-y) =
      ((((U^geo μ n:(Quad y)ˣ):Quad y)-1)) * _ at H
    rw [hU1,one_zpow,Units.val_one,sub_self,zero_mul] at H
    have h0 := congrArg QuadraticAlgebra.re H
    exact sub_eq_zero.mp (by simpa using h0)
  · obtain ⟨d,hd,v,hv,hvn⟩ := nontrivial_quad_unit_content (p:=p) y V hVr h
    refine Or.inr ⟨d,hd,?_⟩
    intro n s
    rw [hcontent n s,←pcast_eq]
    change (p:Quad y)^s ∣ (((U^geo μ n:(Quad y)ˣ):Quad y)-1) ↔ _
    rw [←hV,←zpow_natCast,←zpow_mul,Nat.cast_pow]
    rw [exact_unit_zpow_dvd pp (by omega) hd (reduce p y) (reduce_p y) (cast_unit (p:=p) y)
      (quad_natCast_mul_injective pp.ne_zero) V v hv hvn]
    change ((p:ℤ)^e * geo μ n=0 ∨ s ≤ d+padicValInt p ((p:ℤ)^e * geo μ n)) ↔
      μ^n-1=0 ∨ s ≤ d+padicValInt p (μ^n-1)
    rw [←geo_factor μ n]
    have hp0 : (p:ℤ)^e≠0 := pow_ne_zero _ (Int.natCast_ne_zero.mpr pp.ne_zero)
    by_cases hg : geo μ n=0
    · simp [hg]
    · rw [padicValInt.mul hmu hg,padicValInt.mul hp0 hg]
      have hpv : padicValInt p ((p:ℤ)^e)=e := by
        rw [←Nat.cast_pow,padicValInt.of_nat,padicValNat.pow,padicValNat_self,mul_one]
      rw [hpv]
      simp [mul_eq_zero,hg,hmu,e,hp0]
end

section
private theorem trace_is_iterate {R : Type*} [CommRing R] (n : ℕ) (x : R) :
    trace n x=(((step : R → R)^[n]) x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [trace,ih,Function.iterate_succ_apply']

private theorem mod_return_iff (M n : ℕ) (y : ℤ) :
    trace n (y:ZMod M)=(y:ZMod M) ↔ (M:ℤ)∣trace n y-y := by
  have H := trace_map (Int.castRingHom (ZMod M)) n y
  change ((trace n y:ℤ):ZMod M)=trace n (y:ZMod M) at H
  rw [←H,←sub_eq_zero,←Int.cast_sub,ZMod.intCast_zmod_eq_zero_iff_dvd]

private theorem order_zmod_iff (M : ℕ) (μ : ℤ) (n : ℕ) :
    orderOf ((μ:ℤ):ZMod M)∣n ↔ (M:ℤ)∣μ^n-1 := by
  rw [orderOf_dvd_iff_pow_eq_one,←sub_eq_zero,←ZMod.intCast_zmod_eq_zero_iff_dvd,Int.cast_sub,
    Int.cast_pow,Int.cast_one]

private theorem mul_period {R : Type*} [CommRing R] (x : R) (ell m : ℕ)
    (hr : ∀ n, trace n x=x → ell∣n)
    (hm : ∀ n, trace (ell*n) x=x ↔ m∣n) :
    Function.minimalPeriod step x=ell*m := by
  refine Nat.dvd_antisymm ?_ ?_
  · apply Function.IsPeriodicPt.minimalPeriod_dvd
    change (step^[ell*m]) x=x
    rw [←trace_is_iterate]
    exact (hm m).2 dvd_rfl
  · have h := Function.iterate_minimalPeriod (f:=step) (x:=x)
    rw [←trace_is_iterate] at h
    obtain ⟨t,ht⟩ := hr _ h
    rw [ht] at h ⊢
    exact Nat.mul_dvd_mul_left _ ((hm t).1 h)

/-- A variable lifted-period readout, retaining the actual residue period and
the nonbranch hypotheses on the literal base recurrence. The input triple
records the prime, integer seed, and positive precision. -/
def NonbranchPeriodLaw (observed : (ℕ × ℤ × ℕ) → ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 3<p → ∀ (y : ℤ), (y:ZMod p)^2+4≠0 →
    0<Function.minimalPeriod step (y:ZMod p) →
    let ell := Function.minimalPeriod step (y:ZMod p)
    ∃ flip : Bool,
      let μ := multiplier flip (3^ell)
      (∀ s : ℕ, 0<s → observed (p,y,s)=ell) ∨
      ∃ d : ℕ, 0<d ∧ ∀ s : ℕ, 0<s →
        observed (p,y,s)=ell*orderOf ((μ:ℤ):ZMod (p^(s-d)))

/-- Exact minimal period in every positive precision above a nonbranch
periodic residue, without any extension of the finite coefficient ring. -/
theorem nonbranch_minimal_period :
    let observed := fun q : ℕ × ℤ × ℕ =>
      Function.minimalPeriod step (q.2.1:ZMod (q.1^q.2.2))
    NonbranchPeriodLaw observed := by
  dsimp only
  unfold NonbranchPeriodLaw
  intro p _ hp y hD hper
  let ell := Function.minimalPeriod step (y:ZMod p)
  have h0 : trace ell (y:ZMod p)=(y:ZMod p) := by
    rw [trace_is_iterate]
    exact Function.iterate_minimalPeriod
  obtain ⟨flip,H⟩ := nonbranch_exact_multiplier hp y ell hper hD h0
  let μ := multiplier flip (3^ell)
  have lag (s : ℕ) (hs : 0<s) (n : ℕ) (hn : trace n (y:ZMod (p^s))=(y:ZMod (p^s))) :
      ell∣n := by
    let ρ : ZMod (p^s) →+* ZMod p := ZMod.castHom (dvd_pow_self p hs.ne') _
    have H := congrArg ρ hn
    rw [trace_map,show ρ (y:ZMod (p^s))=(y:ZMod p) from map_intCast ρ y,trace_is_iterate] at H
    exact Function.IsPeriodicPt.minimalPeriod_dvd H
  refine ⟨flip,?_⟩
  rcases H with hh | ⟨d,hd,hh⟩
  · left
    intro s hs
    simpa only [mul_one] using
      (mul_period (y:ZMod (p^s)) ell 1 (lag s hs) fun n => by
        rw [mod_return_iff,hh n,sub_self]
        simp)
  · refine Or.inr ⟨d,hd,?_⟩
    intro s hs
    apply mul_period _ ell _ (lag s hs)
    intro n
    rw [mod_return_iff, hh n s, order_zmod_iff]
    rw [Nat.cast_pow,padicValInt_dvd_iff]
    have h : s-d ≤ padicValInt p (μ^n-1) ↔ s ≤ d+padicValInt p (μ^n-1) := by omega
    rw [h]
end

end D5.S3.Arith.Primes.GoldenCubicNonbranchReturn
