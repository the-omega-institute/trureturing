/- GID: D5/S3/Arith/Congruence/BourasA363347PrimeMultiplicity
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/BourasA363347PrimeMultiplicity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Prime values other than five occur twice in Bouras A363347. -/

/-
admission_basis: open-problem-resolution (#18626; Proved)
escape_witness: BourasShared.denominator_formula_aux (live recurrence and factorial identity).
Direct frozen dependencies: none; pinned Mathlib only.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21990
public theorem BourasPolynomials.cast_U; proof_shape: bind-only; escape_witness: none;
consumers: BourasA363102.result.
public theorem BourasRoots.root_fiber_eq_pair; proof_shape: bind-only; escape_witness: none;
consumers: both result proofs.
public theorem BourasRoots.square_residue_pair; proof_shape: bind-only; escape_witness: none;
consumers: both result proofs.
public theorem BourasPrimeValues.U_prime_constraints; proof_shape: content; escape_witness:
BourasShared.denominator_formula_aux; consumers: BourasA363102.result.
public theorem BourasPrimeValues.U_prime_of_root; proof_shape: content; escape_witness: BourasShared.denominator_formula_aux;
consumers: BourasA363102.result.
public theorem BourasA363347.result; proof_shape: content; escape_witness: BourasShared.denominator_formula_aux; consumers:
settling result.
The continued-fraction definitions retain the source's right fold and rational denominator.
The prime quantifier ranges over values that occur at indices at least three.
Set.ncard is applied after the occurrence set is exhibited as a finite pair or triple.
The shared helpers are public exactly where the second delivered module uses them.
-/

import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Field.ZMod

/-! Prime occurrence counts for rational continued-fraction denominators. -/

namespace D5.S3.Arith.Congruence.BourasA363347PrimeMultiplicity

set_option autoImplicit false

namespace BourasA356360

/-- The nested fraction `2 - 3/(3 - 4/(4 - ... ((n-1) - n/x)))`, for `n ≥ 3`: the right fold of
`t ↦ k - (k+1)/t` over `k = 2, …, n-1`, starting from `x`. -/
def nested (n : ℕ) (x : ℚ) : ℚ :=
  (List.range' 2 (n - 2)).foldr (fun (k : ℕ) (t : ℚ) => (k : ℚ) - ((k : ℚ) + 1) / t) x

/-- The continued fraction `1/(2-3/(3-4/(4-5/(...(n-1)-n/x))))`. -/
def K (n : ℕ) (x : ℚ) : ℚ := 1 / nested n x

end BourasA356360

set_option autoImplicit false
open BourasA356360
namespace BourasShared

private def c : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | m + 2 => (m + 3 : ℤ) * (c (m + 1) - c m)

private theorem nested_succ (n : ℕ) (hn : 3 ≤ n) (x : ℚ) :
    nested (n + 1) x = nested n ((n : ℚ) - (n + 1) / x) := by
  unfold nested
  have he : n + 1 - 2 = (n - 2) + 1 := by omega
  rw [he, List.range'_concat]
  simp only [Nat.one_mul, List.foldr_append, List.foldr_cons, List.foldr_nil]
  have hi : 2 + (n - 2) = n := by omega
  rw [hi]

private theorem closed_aux (m : ℕ) (x : ℚ)
    (hx : x < 0 ∨ 0 < ((m : ℚ) + 2) * x - (m + 3) * (m + 1)) :
    K (m + 3) x = ((c (m + 1) : ℚ) * x - (m + 3) * c m) /
      (((m : ℚ) + 2) * x - (m + 3) * (m + 1)) := by
  induction m generalizing x with
  | zero =>
    have hx0 : x ≠ 0 := by rcases hx with h | h <;> norm_num at * <;> linarith
    simp only [Nat.zero_add, c]
    norm_num [K, nested, List.range', List.foldr] at *
    field_simp
  | succ m ih =>
    have hm : (0 : ℚ) ≤ m := Nat.cast_nonneg m
    have hx0 : x ≠ 0 := by
      rcases hx with h | h
      · exact ne_of_lt h
      · intro h0
        simp only [h0, mul_zero, Nat.cast_add, Nat.cast_one] at h
        nlinarith
    let y : ℚ := (m + 3 : ℕ) - ((m + 3 : ℕ) + 1) / x
    have he : ((m : ℚ) + 2) * y - (m + 3) * (m + 1) =
        (((m : ℚ) + 3) * x - (m + 4) * (m + 2)) / x := by
      dsimp [y]
      push_cast
      field_simp
      ring
    have hd : (((m : ℚ) + 3) * x - (m + 4) * (m + 2)) ≠ 0 := by
      rcases hx with h | h
      · have : ((m : ℚ) + 3) * x < 0 := mul_neg_of_pos_of_neg (by linarith) h
        nlinarith
      · push_cast at h
        exact ne_of_gt (by nlinarith [h])
    have hy : 0 < ((m : ℚ) + 2) * y - (m + 3) * (m + 1) := by
      rw [he]
      rcases hx with h | h
      · have hnum : (((m : ℚ) + 3) * x - (m + 4) * (m + 2)) < 0 := by
          have : ((m : ℚ) + 3) * x < 0 := mul_neg_of_pos_of_neg (by linarith) h
          nlinarith
        exact div_pos_of_neg_of_neg hnum h
      · push_cast at h
        apply div_pos (by nlinarith [h])
        by_contra hn
        have hxle : x ≤ 0 := le_of_not_gt hn
        have := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ (m : ℚ) + 3) hxle
        nlinarith
    have hK : K (m + 1 + 3) x = K (m + 3) y := by
      unfold K
      have hi : m + 1 + 3 = (m + 3) + 1 := by exact Nat.add_right_comm m 1 3
      rw [hi, nested_succ (m + 3) (by omega)]
    rw [hK, ih y (Or.inr hy), he, div_div_eq_mul_div]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show m + 1 + 1 = m + 2 by omega, c]
    push_cast
    apply congrArg₂ (fun a b : ℚ => a / b)
    · dsimp [y]
      push_cast
      field_simp [hx0]
      ring
    · ring

private theorem factorial_identity_aux (m : ℕ) :
    2 * (((m : ℤ) + 3) * (m + 1) * c (m + 1) -
      (m + 3) * (m + 2) * c m) = ((m + 3).factorial : ℤ) := by
  induction m with
  | zero => norm_num [c, Nat.factorial_succ]
  | succ m ih =>
    rw [show m + 1 + 3 = (m + 3) + 1 by omega, Nat.factorial_succ]
    push_cast
    rw [show m + 1 + 1 = m + 2 by omega, c]
    push_cast
    calc
      _ = ((m : ℤ) + 4) * (2 * ((m + 3) * (m + 1) * c (m + 1) -
          (m + 3) * (m + 2) * c m)) := by ring
      _ = _ := by rw [ih]; ring

private theorem denominator_formula_aux (m : ℕ) (x : ℤ) (hx : x < 0) :
    (K (m + 3) x).den =
      (((m : ℤ) + 2) * x - (m + 3) * (m + 1)).natAbs /
        Nat.gcd (((m : ℤ) + 2) * x - (m + 3) * (m + 1)).natAbs
          ((m + 3).factorial / 2) := by
  let D : ℤ := ((m : ℤ) + 2) * x - (m + 3) * (m + 1)
  let N : ℤ := c (m + 1) * x - (m + 3) * c m
  let F : ℤ := ((m + 3).factorial / 2 : ℕ)
  have hD : D ≠ 0 := by
    dsimp [D]
    have hm : (0 : ℤ) ≤ m := Int.natCast_nonneg m
    have hmul : ((m : ℤ) + 2) * x < 0 := mul_neg_of_pos_of_neg (by omega) hx
    nlinarith
  have hc : K (m + 3) x = (N : ℚ) / D := by
    have h := closed_aux m (x : ℚ) (Or.inl (by exact_mod_cast hx))
    simpa only [D, N, Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_natCast,
      Int.cast_ofNat, Int.cast_one] using h
  have hF : F = ((m : ℤ) + 3) * (m + 1) * c (m + 1) -
      (m + 3) * (m + 2) * c m := by
    have h := factorial_identity_aux m
    dsimp [F]
    omega
  have hlin : ((m : ℤ) + 2) * N = c (m + 1) * D + F := by
    rw [hF]
    dsimp [D, N]
    ring
  have hcop : Int.gcd D ((m : ℤ) + 2) = 1 := by
    have he : D + ((m : ℤ) + 2) * (m + 2 - x) = 1 := by dsimp [D]; ring
    calc
      _ = Int.gcd (D + ((m : ℤ) + 2) * (m + 2 - x)) ((m : ℤ) + 2) :=
        (Int.gcd_add_mul_left_left _ _ _).symm
      _ = 1 := by rw [he]; simp
  have hg : Int.gcd D N = Int.gcd D F := by
    calc
      _ = Int.gcd D (((m : ℤ) + 2) * N) :=
        (Int.gcd_mul_right_right_of_gcd_eq_one hcop).symm
      _ = Int.gcd D F := by rw [hlin, Int.gcd_mul_right_add_right]
  rw [hc, ← Rat.divInt_eq_div, Rat.den_divInt, if_neg hD, hg]
  simp only [F, Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast]
  rfl

end BourasShared

set_option autoImplicit false
namespace BourasPolynomials

private def T (n : ℕ) : ℕ := n ^ 2 + 2 * n - 4
def U (n : ℕ) : ℕ := n ^ 2 - 2

private theorem cast_T (n m : ℕ) (hn : 3 ≤ n) :
    (T n : ZMod m) = ((n : ZMod m) + 1) ^ 2 - 5 := by
  unfold T
  rw [Nat.cast_sub (by nlinarith : 4 ≤ n ^ 2 + 2 * n)]
  push_cast
  ring

theorem cast_U (n m : ℕ) (hn : 3 ≤ n) :
    (U n : ZMod m) = (n : ZMod m) ^ 2 - 2 := by
  unfold U
  rw [Nat.cast_sub (by nlinarith : 2 ≤ n ^ 2)]
  push_cast
  rfl

private theorem T_not_dvd (m n : ℕ) (hn : 3 ≤ n)
    (hm : m = 3 ∨ m = 7 ∨ m = 8 ∨ m = 25) : ¬m ∣ T n := by
  intro hd
  have hz := (ZMod.natCast_eq_zero_iff (T n) m).mpr hd
  rw [cast_T n m hn] at hz
  have hs : ((n : ZMod m) + 1) ^ 2 = 5 := sub_eq_zero.mp hz
  have hnone : ∀ z : ZMod m, z ^ 2 ≠ 5 := by
    rcases hm with rfl | rfl | rfl | rfl <;> decide +kernel
  exact hnone _ hs

private theorem U_not_dvd (m n : ℕ) (hn : 3 ≤ n)
    (hm : m = 3 ∨ m = 4 ∨ m = 5) : ¬m ∣ U n := by
  intro hd
  have hz := (ZMod.natCast_eq_zero_iff (U n) m).mpr hd
  rw [cast_U n m hn] at hz
  have hs : (n : ZMod m) ^ 2 = 2 := sub_eq_zero.mp hz
  have hnone : ∀ z : ZMod m, z ^ 2 ≠ 2 := by
    rcases hm with rfl | rfl | rfl <;> decide +kernel
  exact hnone _ hs

private theorem no_twice_prime_square_T (n p : ℕ) (hn : 3 ≤ n) (hodd : p % 2 = 1) :
    T n ≠ 2 * p ^ 2 := by
  intro he
  have hp8 : (p : ZMod 8) ^ 2 = 1 := by
    have hd := Nat.eight_dvd_sq_sub_one_of_odd (Nat.odd_iff.mpr hodd)
    have hpos : 1 ≤ p ^ 2 := Nat.one_le_pow 2 p (by omega)
    have hzero := (ZMod.natCast_eq_zero_iff (p ^ 2 - 1) 8).mpr hd
    rw [Nat.cast_sub hpos, Nat.cast_pow, Nat.cast_one] at hzero
    exact sub_eq_zero.mp hzero
  have hz := congrArg (fun v : ℕ => (v : ZMod 8)) he
  rw [cast_T n 8 hn] at hz
  push_cast at hz
  rw [hp8] at hz
  have hs : ((n : ZMod 8) + 1) ^ 2 = 7 := by
    calc
      _ = (((n : ZMod 8) + 1) ^ 2 - 5) + 5 := by ring
      _ = 7 := by rw [hz]; decide +kernel
  have hnone : ∀ z : ZMod 8, z ^ 2 ≠ 7 := by
    intro z hz
    have he : ((z.val ^ 2 : ℕ) : ZMod 8) = 7 := by
      simpa only [Nat.cast_pow, ZMod.natCast_zmod_val] using hz
    have hmod := (ZMod.natCast_eq_natCast_iff' (z.val ^ 2) 7 8).mp he
    have hfour : z.val ^ 2 % 4 = z.val % 2 := by
      exact_mod_cast Int.sq_emod_four (z.val : ℤ)
    norm_num at hmod
    omega
  exact hnone _ hs

end BourasPolynomials

set_option autoImplicit false
namespace BourasArithmetic

private def reduced (T F : ℕ) : ℕ := T / Nat.gcd T F

private theorem prime_footprint (T F p k : ℕ) (hT : 0 < T)
    (hp : reduced T F = p) (hk : p ^ k ∣ F) : p ^ (k + 1) ∣ T := by
  let g := Nat.gcd T F
  have hg : 0 < g := Nat.gcd_pos_of_pos_left F hT
  have hcop : Nat.Coprime p (F / g) := by
    rw [← hp]
    exact Nat.coprime_div_gcd_div_gcd hg
  have hFg : F = g * (F / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right T F)).symm
  have hd : p ^ k ∣ g := (hcop.pow_left k).dvd_of_dvd_mul_right (hFg ▸ hk)
  have hTg : T = p * g := by
    rw [← hp]
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_left T F)).symm
  rw [hTg, pow_succ']
  exact Nat.mul_dvd_mul_left p hd

private theorem pow_dvd_factorial_mul (p k : ℕ) (hp : 0 < p) :
    p ^ k ∣ (p * k).factorial := by
  have hprod : p.factorial ^ k ∣ (p * k).factorial := by
    simpa [Nat.mul_comm] using
      Nat.prod_factorial_dvd_factorial_sum (Finset.range k) (fun _ : ℕ => p)
  exact (pow_dvd_pow_of_dvd (Nat.dvd_factorial hp (le_refl p)) k).trans hprod

private theorem pow_dvd_factorial_floor (p n : ℕ) (hp : 0 < p) :
    p ^ (n / p) ∣ n.factorial := by
  exact (pow_dvd_factorial_mul p (n / p) hp).trans
    (Nat.factorial_dvd_factorial (Nat.mul_div_le n p))

private theorem two_mul_dvd_factorial (n d : ℕ) (hn : 4 ≤ n) (hd : 0 < d)
    (hdn : d ≤ n) : 2 * d ∣ n.factorial := by
  by_cases hsmall : d ≤ 2
  · rcases (by omega : d = 1 ∨ d = 2) with rfl | rfl
    · exact (by norm_num [Nat.factorial_succ] : 2 ∣ Nat.factorial 4).trans (Nat.factorial_dvd_factorial hn)
    · exact (by norm_num [Nat.factorial_succ] : 4 ∣ Nat.factorial 4).trans (Nat.factorial_dvd_factorial hn)
  · have hd3 : 3 ≤ d := by omega
    have he : d = (d - 1) + 1 := by exact (Nat.sub_eq_iff_eq_add hd).mp rfl
    have htwo : 2 ∣ (d - 1).factorial := Nat.dvd_factorial (by decide) (by omega)
    apply Nat.dvd_trans _ (Nat.factorial_dvd_factorial hdn)
    rw [he, Nat.factorial_succ, ← he]
    simpa only [mul_comm] using Nat.mul_dvd_mul_left d htwo

private theorem divides_half_factorial (n d : ℕ) (hn : 4 ≤ n) (hd : 0 < d)
    (hdn : d ≤ n) : d ∣ n.factorial / 2 := by
  apply (Nat.dvd_div_iff_mul_dvd (Nat.dvd_factorial (by decide) (by omega) : 2 ∣ n.factorial)).mpr
  simpa only [mul_comm] using two_mul_dvd_factorial n d hn hd hdn

private theorem reduced_at_large_prime (n T p : ℕ) (hn : 4 ≤ n) (hT : 0 < T)
    (hp : p.Prime) (hnp : n < p) (hd : p ∣ T) (hb : T < (n + 1) * p) :
    reduced T (n.factorial / 2) = p := by
  obtain ⟨d, hd⟩ := hd
  have hd0 : 0 < d := by nlinarith [hp.pos]
  have hdn : d ≤ n := by nlinarith [hp.pos]
  have hdF : d ∣ n.factorial / 2 := divides_half_factorial n d hn hd0 hdn
  have hcop : p.Coprime (n.factorial / 2) :=
    (hp.coprime_factorial_of_lt hnp).of_dvd_right (Nat.div_dvd_of_dvd (Nat.dvd_factorial (by decide) (by omega)))
  unfold reduced
  rw [hd, hcop.gcd_mul_left_cancel d, Nat.gcd_eq_left hdF]
  exact Nat.mul_div_cancel p hd0

private theorem power_bound (p k : ℕ) (hp : 5 ≤ p) (hk : 3 ≤ k) :
    ((k + 1) * p) ^ 2 ≤ p ^ (k + 1) := by
  have hlinear := Nat.mul_le_pow (by decide : (2 : ℕ) ≠ 1) (k - 1)
  have hkpow : k + 1 ≤ 2 ^ (k - 1) := by omega
  have htwo : (2 ^ (k - 1) : ℕ) ^ 2 = 4 ^ (k - 1) := by
    rw [← pow_mul, Nat.mul_comm (k - 1) 2, pow_mul]
    norm_num
  calc
    ((k + 1) * p) ^ 2 ≤ (2 ^ (k - 1) * p) ^ 2 :=
      Nat.pow_le_pow_left (Nat.mul_le_mul_right p hkpow) 2
    _ = 4 ^ (k - 1) * p ^ 2 := by rw [mul_pow, htwo]
    _ ≤ p ^ (k - 1) * p ^ 2 :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega : 4 ≤ p) (k - 1))
    _ = p ^ ((k - 1) + 2) := (pow_add p (k - 1) 2).symm
    _ = p ^ (k + 1) := by congr 1; omega

private theorem quotient_bound (n T p : ℕ) (hp : 5 ≤ p) (hT : 0 < T)
    (hb : T < (n + 1) ^ 2) (hf : p ^ (n / p + 1) ∣ T) : n / p ≤ 2 := by
  by_contra hk
  have hk3 : 3 ≤ n / p := by omega
  have hnp : n + 1 ≤ (n / p + 1) * p := by
    have h : n < (n / p + 1) * p := by
      simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ n (by omega : 0 < p)
    exact Nat.succ_le_of_lt h
  have hpow := power_bound p (n / p) hp hk3
  have hdiv := Nat.le_of_dvd hT hf
  nlinarith

private theorem reduced_dvd (T F p : ℕ) (hp : reduced T F = p) : p ∣ T := by
  rw [← hp]
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left T F)

private theorem factorial_footprint (n T p : ℕ) (hn : 3 ≤ n) (hT : 0 < T)
    (hp : p.Prime) (hp2 : p ≠ 2) (hv : reduced T (n.factorial / 2) = p) :
    p ^ (n / p + 1) ∣ T := by
  have hpge : 2 ≤ p := hp.two_le
  have hcop : p.Coprime 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  have htwo : 2 ∣ n.factorial := Nat.dvd_factorial (by decide) (by omega)
  have hfact : n.factorial = 2 * (n.factorial / 2) := (Nat.mul_div_cancel' htwo).symm
  have hpow := pow_dvd_factorial_floor p n hp.pos
  rw [hfact] at hpow
  apply prime_footprint T (n.factorial / 2) p (n / p) hT hv
  exact (hcop.pow_left _).dvd_of_dvd_mul_left hpow

end BourasArithmetic
set_option autoImplicit false
open BourasA356360 BourasPolynomials BourasArithmetic
namespace BourasConnection

private theorem T_den (n : ℕ) (hn : 3 ≤ n) :
    (K n (-4)).den = reduced (T n) (n.factorial / 2) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n = m + 3 := ⟨n - 3, by omega⟩
  subst n
  have h := BourasShared.denominator_formula_aux m (-4) (by decide)
  have he : ((m : ℤ) + 2) * (-4) - (m + 3) * (m + 1) = -(T (m + 3) : ℤ) := by
    unfold T
    rw [Nat.cast_sub (by nlinarith : 4 ≤ (m + 3) ^ 2 + 2 * (m + 3))]
    push_cast
    ring
  rw [he, Int.natAbs_neg, Int.natAbs_natCast] at h
  exact h

private theorem U_den (n : ℕ) (hn : 3 ≤ n) :
    (K n (-2)).den = reduced (U n) (n.factorial / 2) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n = m + 3 := ⟨n - 3, by omega⟩
  subst n
  have h := BourasShared.denominator_formula_aux m (-2) (by decide)
  have he : ((m : ℤ) + 2) * (-2) - (m + 3) * (m + 1) = -(U (m + 3) : ℤ) := by
    unfold U
    rw [Nat.cast_sub (by nlinarith : 2 ≤ (m + 3) ^ 2)]
    push_cast
    ring
  rw [he, Int.natAbs_neg, Int.natAbs_natCast] at h
  exact h
end BourasConnection

set_option autoImplicit false
namespace BourasRoots

theorem root_fiber_eq_pair (p s r q : ℕ) (hp : p.Prime)
    (hr : 3 ≤ r) (hq : 3 ≤ q) (hrp : r + s < p) (hqp : q + s < p)
    (hsum : r + q + 2 * s = p) :
    {n : ℕ | 3 ≤ n ∧ n + s < p ∧
      ((n + s : ℕ) : ZMod p) ^ 2 = ((r + s : ℕ) : ZMod p) ^ 2} = {r, q} := by
  let : Fact p.Prime := ⟨hp⟩
  have hneg : ((q + s : ℕ) : ZMod p) = -((r + s : ℕ) : ZMod p) := by
    apply eq_neg_of_add_eq_zero_left
    calc
      ((q + s : ℕ) : ZMod p) + ((r + s : ℕ) : ZMod p) =
          ((r + q + 2 * s : ℕ) : ZMod p) := by push_cast; ring
      _ = 0 := by rw [hsum]; simp
  have hset : {n : ℕ | 3 ≤ n ∧ n + s < p ∧
      ((n + s : ℕ) : ZMod p) ^ 2 = ((r + s : ℕ) : ZMod p) ^ 2} = {r, q} := by
    ext n
    constructor
    · rintro ⟨hn, hnp, hroot⟩
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hroot with h | h
      · have hv := congrArg ZMod.val h
        simp only [ZMod.val_natCast_of_lt hnp, ZMod.val_natCast_of_lt hrp] at hv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        exact Or.inl (by omega)
      · rw [← hneg] at h
        have hv := congrArg ZMod.val h
        simp only [ZMod.val_natCast_of_lt hnp, ZMod.val_natCast_of_lt hqp] at hv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        exact Or.inr (by omega)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (rfl | rfl)
      · exact ⟨hr, hrp, rfl⟩
      · exact ⟨hq, hqp, by rw [hneg, neg_sq]⟩
  exact hset

theorem square_residue_pair (p s c : ℕ) (hp : p.Prime)
    (hcfg : (s = 0 ∧ c = 2 ∧ 7 ≤ p) ∨ (s = 1 ∧ c = 5 ∧ 11 ≤ p))
    (z : ZMod p) (hz : z ^ 2 = c) :
    ∃ r q : ℕ, 3 ≤ r ∧ 3 ≤ q ∧ r + s < p ∧ q + s < p ∧ r ≠ q ∧
      r + q + 2 * s = p ∧ ((r + s : ℕ) : ZMod p) ^ 2 = c := by
  let : Fact p.Prime := ⟨hp⟩
  have hpp : 7 ≤ p := by rcases hcfg with h | h <;> omega
  have hc : c < p := by rcases hcfg with h | h <;> omega
  have low : ∀ w : ZMod p, w ^ 2 = c → s + 3 ≤ w.val := by
    intro w hw
    have hw' : ((w.val ^ 2 : ℕ) : ZMod p) = (c : ZMod p) := by
      simpa only [Nat.cast_pow, ZMod.natCast_zmod_val] using hw
    have hmod := (ZMod.natCast_eq_natCast_iff' (w.val ^ 2) c p).mp hw'
    by_contra hnot
    have hsmall : w.val < s + 3 := by exact Nat.lt_of_not_le hnot
    have hsquare : w.val ^ 2 < p := by
      rcases hcfg with h | h
      · have : w.val < 3 := by omega
        nlinarith [h.2.2]
      · have : w.val < 4 := by omega
        nlinarith [h.2.2]
    rw [Nat.mod_eq_of_lt hsquare, Nat.mod_eq_of_lt hc] at hmod
    rcases hcfg with ⟨rfl, rfl, hp7⟩ | ⟨rfl, rfl, hp11⟩
    · have : w.val ≤ 2 := by omega
      interval_cases hv : w.val <;> norm_num [hv] at hmod
    · have : w.val ≤ 3 := by omega
      interval_cases hv : w.val <;> norm_num [hv] at hmod
  have hu := low z hz
  have hv := low (-z) (by simpa only [neg_sq] using hz)
  have huz := ZMod.val_lt z
  have hvz := ZMod.val_lt (-z)
  have hsum : z.val + (-z).val = p := by
    have hz0 : z ≠ 0 := by
      intro hz0
      simp only [hz0, ZMod.val_zero] at hu
      omega
    have hn := ZMod.neg_val z
    rw [if_neg hz0] at hn
    have hv := ZMod.val_lt z
    omega
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have hne : z.val - s ≠ (-z).val - s := by
    intro he
    have he' : z.val = (-z).val := by omega
    omega
  refine ⟨z.val - s, (-z).val - s, by omega, by omega,
    by omega, by omega, hne, by omega, ?_⟩
  have he : z.val - s + s = z.val := by omega
  simpa only [he, ZMod.natCast_zmod_val] using hz

end BourasRoots

set_option autoImplicit false
open BourasA356360 BourasPolynomials BourasArithmetic BourasConnection
namespace BourasPrimeValues

private theorem T_pos (n : ℕ) (hn : 3 ≤ n) : 0 < T n := by unfold T; omega
private theorem U_pos (n : ℕ) (hn : 3 ≤ n) : 0 < U n := by
  unfold U
  have hs := Nat.pow_le_pow_left hn 2
  norm_num at hs
  omega

private theorem T_equation (n : ℕ) (hn : 3 ≤ n) : T n + 4 = n ^ 2 + 2 * n := by
  unfold T
  omega
private theorem U_equation (n : ℕ) (hn : 3 ≤ n) : U n + 2 = n ^ 2 := by
  unfold U
  have hs := Nat.pow_le_pow_left hn 2
  norm_num at hs
  omega

private theorem T_prime_constraints (n p : ℕ) (hn : 3 ≤ n) (hp : p.Prime) (hp5 : p ≠ 5)
    (ha : (K n (-4)).den = p) : 11 ≤ p ∧ n < p ∧ p ∣ T n := by
  have hv : reduced (T n) (n.factorial / 2) = p := by rwa [T_den n hn] at ha
  have hT := T_pos n hn
  have hTe := T_equation n hn
  have hd := reduced_dvd (T n) (n.factorial / 2) p hv
  have hp2 : p ≠ 2 := by
    intro he
    rw [he] at hv hd
    have hn4 : 4 ≤ n := by
      by_contra h
      have : n = 3 := by omega
      subst n
      norm_num [T] at hd
    have hF := divides_half_factorial n 4 hn4 (by decide) hn4
    have h := prime_footprint (T n) (n.factorial / 2) 2 2 hT hv (by simpa using hF)
    exact T_not_dvd 8 n hn (Or.inr (Or.inr (Or.inl rfl))) (by simpa using h)
  have hp3 : p ≠ 3 := by
    intro he
    rw [he] at hd
    exact T_not_dvd 3 n hn (Or.inl rfl) hd
  have hp7 : p ≠ 7 := by
    intro he
    rw [he] at hd
    exact T_not_dvd 7 n hn (Or.inr (Or.inl rfl)) hd
  have hp11 : 11 ≤ p := by
    by_contra h
    have : p ≤ 10 := by omega
    clear ha hv hd
    interval_cases p <;> first | exact False.elim ((by decide +kernel : ¬Nat.Prime _) hp) | omega
  refine ⟨hp11, ?_, hd⟩
  by_contra hnp
  have hpn : p ≤ n := by exact Nat.le_of_not_lt hnp
  have hf := factorial_footprint n (T n) p hn hT hp hp2 hv
  have hk := quotient_bound n (T n) p (by omega) hT (by nlinarith) hf
  have hklo : 1 ≤ n / p := (Nat.one_le_div_iff hp.pos).mpr hpn
  have hnupper : n < (n / p + 1) * p := by
    simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ n hp.pos
  rcases (by omega : n / p = 1 ∨ n / p = 2) with hk1 | hk2
  · rw [hk1] at hf
    norm_num at hf
    obtain ⟨j, hj⟩ := hf
    have hjlo : 0 < j := by nlinarith
    have hjhi : j ≤ 3 := by
      rw [hk1] at hnupper
      nlinarith [hp.pos]
    interval_cases j
    · nlinarith [hp.pos]
    · exact no_twice_prime_square_T n p hn (hp.eq_two_or_odd.resolve_left hp2) (by nlinarith)
    · apply T_not_dvd 3 n hn (Or.inl rfl)
      exact ⟨p ^ 2, by nlinarith [hj]⟩
  · rw [hk2] at hf hnupper
    have hsize := Nat.le_of_dvd hT hf
    norm_num [pow_succ] at hsize
    have hfactor : p * p * p < 9 * (p * p) := by nlinarith
    have : p < 9 := (Nat.mul_lt_mul_right (Nat.mul_pos hp.pos hp.pos)).mp (by
      nlinarith [hfactor])
    omega

theorem U_prime_constraints (n p : ℕ) (hn : 3 ≤ n) (hp : p.Prime)
    (ha : (K n (-2)).den = p) : 7 ≤ p ∧ p ∣ U n ∧ (n < p ∨ n ^ 2 = 2 * p ^ 2 + 2) := by
  have hv : reduced (U n) (n.factorial / 2) = p := by rwa [U_den n hn] at ha
  have hU := U_pos n hn
  have hUe := U_equation n hn
  have hd := reduced_dvd (U n) (n.factorial / 2) p hv
  have hp2 : p ≠ 2 := by
    intro he
    rw [he] at hv hd
    have hn4 : 4 ≤ n := by
      by_contra h
      have : n = 3 := by omega
      subst n
      norm_num [U] at hd
    have hF := divides_half_factorial n 2 hn4 (by decide) (by omega)
    have h := prime_footprint (U n) (n.factorial / 2) 2 1 hU hv (by simpa using hF)
    exact U_not_dvd 4 n hn (Or.inr (Or.inl rfl)) (by simpa using h)
  have hp3 : p ≠ 3 := by
    intro he
    rw [he] at hd
    exact U_not_dvd 3 n hn (Or.inl rfl) hd
  have hp5 : p ≠ 5 := by
    intro he
    rw [he] at hd
    exact U_not_dvd 5 n hn (Or.inr (Or.inr rfl)) hd
  have hp7 : 7 ≤ p := by
    by_contra h
    have : p ≤ 6 := by omega
    clear ha hv hd
    interval_cases p <;> first | exact False.elim ((by decide +kernel : ¬Nat.Prime _) hp) | omega
  refine ⟨hp7, hd, ?_⟩
  by_cases hnp : n < p
  · exact Or.inl hnp
  · right
    have hpn : p ≤ n := by exact Nat.le_of_not_lt hnp
    have hf := factorial_footprint n (U n) p hn hU hp hp2 hv
    have hk := quotient_bound n (U n) p (by omega) hU (by nlinarith) hf
    have hklo : 1 ≤ n / p := (Nat.one_le_div_iff hp.pos).mpr hpn
    have hnupper : n < (n / p + 1) * p := by
      simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ n hp.pos
    rcases (by omega : n / p = 1 ∨ n / p = 2) with hk1 | hk2
    · rw [hk1] at hf
      norm_num at hf
      obtain ⟨j, hj⟩ := hf
      have hjlo : 0 < j := by nlinarith
      have hjhi : j ≤ 3 := by rw [hk1] at hnupper; nlinarith [hp.pos]
      interval_cases j
      · have hgap : p + 1 ≤ n := by
          by_contra hh
          have he : n = p := by omega
          rw [he] at hUe hj
          nlinarith
        have hsq := Nat.pow_le_pow_left hgap 2
        nlinarith [hp.pos]
      · nlinarith
      · exfalso
        apply U_not_dvd 3 n hn (Or.inl rfl)
        exact ⟨p ^ 2, by nlinarith [hj]⟩
    · rw [hk2] at hf hnupper
      have hsize := Nat.le_of_dvd hU hf
      norm_num [pow_succ] at hsize
      have hfactor : p * p * p < 9 * (p * p) := by nlinarith
      have hplt : p < 9 := (Nat.mul_lt_mul_right (Nat.mul_pos hp.pos hp.pos)).mp (by nlinarith)
      have hpval : p = 7 := by
        clear ha hv hd
        interval_cases p <;> first | exact False.elim ((by decide +kernel : ¬Nat.Prime _) hp) | omega
      rw [hpval] at hf hnupper hpn hk2 ⊢
      have hnlo : 14 ≤ n := by omega
      have hnhi : n ≤ 20 := by omega
      interval_cases n <;> norm_num [U] at hf

private theorem T_prime_of_root (n p : ℕ) (hn : 3 ≤ n) (hp : p.Prime)
    (hnp : n < p) (hd : p ∣ T n) : (K n (-4)).den = p := by
  by_cases he : n = 3
  · subst n
    have hpv : p = 11 := by
      norm_num [T] at hd
      rcases (Nat.dvd_prime (by decide : Nat.Prime 11)).mp hd with he | he
      · exact (hp.ne_one he).elim
      · exact he
    subst p
    decide +kernel
  · rw [T_den n hn]
    exact reduced_at_large_prime n (T n) p (by omega) (T_pos n hn) hp hnp hd
      (by have h := T_equation n hn; nlinarith)

theorem U_prime_of_root (n p : ℕ) (hn : 3 ≤ n) (hp : p.Prime)
    (hnp : n < p) (hd : p ∣ U n) : (K n (-2)).den = p := by
  by_cases he : n = 3
  · subst n
    have hpv : p = 7 := by
      norm_num [U] at hd
      rcases (Nat.dvd_prime (by decide : Nat.Prime 7)).mp hd with he | he
      · exact (hp.ne_one he).elim
      · exact he
    subst p
    decide +kernel
  · rw [U_den n hn]
    exact reduced_at_large_prime n (U n) p (by omega) (U_pos n hn) hp hnp hd
      (by have h := U_equation n hn; nlinarith)
end BourasPrimeValues

set_option autoImplicit false

namespace BourasA363347

open BourasA356360

/-- A363347: the denominator of `1/(2-3/(3-4/(4-5/(...(n-1)-n/(-4)))))`, `n ≥ 3`. -/
def a (n : ℕ) : ℕ := (K n (-4)).den

/-- Conjecture 3 of A363347 ("Except for 5, the primes all appear exactly twice."): every prime
value other than 5 is taken at exactly two indices `n ≥ 3`. -/
def claim : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 5 → (∃ n : ℕ, 3 ≤ n ∧ a n = p) →
    {n : ℕ | 3 ≤ n ∧ a n = p}.ncard = 2

end BourasA363347

namespace BourasA363347
open BourasPolynomials BourasPrimeValues BourasRoots

theorem result : claim := by
  intro p hp hp5 hex
  obtain ⟨n0, hn0, ha0⟩ := hex
  have h0 := T_prime_constraints n0 p hn0 hp hp5 ha0
  have hz : (((n0 : ZMod p) + 1) ^ 2) = 5 := by
    have hzero := (ZMod.natCast_eq_zero_iff (T n0) p).mpr h0.2.2
    rw [cast_T n0 p hn0] at hzero
    exact sub_eq_zero.mp hzero
  obtain ⟨r, q, hr, hq, hrp, hqp, hrq, hsum, hrroot⟩ :=
    square_residue_pair p 1 5 hp (Or.inr ⟨rfl, rfl, h0.1⟩) ((n0 : ZMod p) + 1) hz
  have hfiber := root_fiber_eq_pair p 1 r q hp hr hq hrp hqp hsum
  have h5 : (5 : ZMod p) ≠ 0 := by
    intro he
    have hd := (ZMod.natCast_eq_zero_iff 5 p).mp he
    have := Nat.le_of_dvd (by decide : 0 < 5) hd
    omega
  have hset : {n : ℕ | 3 ≤ n ∧ a n = p} = {r, q} := by
    ext n
    constructor
    · rintro ⟨hn, ha⟩
      have hc := T_prime_constraints n p hn hp hp5 ha
      have hz : ((n + 1 : ℕ) : ZMod p) ^ 2 = 5 := by
        have he := (ZMod.natCast_eq_zero_iff (T n) p).mpr hc.2.2
        rw [cast_T n p hn] at he
        simpa only [Nat.cast_add, Nat.cast_one] using sub_eq_zero.mp he
      have hnp : n + 1 < p := by
        by_contra hh
        have he : n + 1 = p := by omega
        apply h5
        simpa only [he, ZMod.natCast_self, zero_pow (by decide : 2 ≠ 0)] using hz.symm
      rw [← hfiber]
      exact ⟨hn, hnp, hz.trans hrroot.symm⟩
    · intro he
      rw [← hfiber] at he
      obtain ⟨hn, hnp, hz⟩ := he
      refine ⟨hn, ?_⟩
      apply T_prime_of_root n p hn hp (by omega)
      apply (ZMod.natCast_eq_zero_iff (T n) p).mp
      rw [cast_T n p hn]
      have hz5 := hz.trans hrroot
      simp only [Nat.cast_add, Nat.cast_one] at hz5
      rw [hz5]
      norm_num
  rw [hset]
  exact Set.ncard_pair hrq

end BourasA363347

end D5.S3.Arith.Congruence.BourasA363347PrimeMultiplicity
