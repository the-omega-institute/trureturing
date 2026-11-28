/- GID: D5/S3/Arith/Primes/GoldenCubicDyadicClock
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicDyadicClock
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Exact dyadic lag, periods, and residue image of native cubic Lucas blocks. -/

import D5.S1.Scale.GoldenCubicBlockCongruences
import D5.S3.Arith.Primes.GoldenCubicBlockTailOrbitImage
import Mathlib.Data.Int.ModEq
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-! The native dyadic orbit fills one residue class at every precision. -/

namespace D5.S3.Arith.Primes.GoldenCubicDyadicClock

open Function D5.S1.Scale

/-- The integer coordinate obtained by removing the systematic factor 16
from the squared Lucas trace. -/
def T (x : ℤ) : ℤ := x * (16*x+3)^2

private theorem odd_T {x : ℤ} (hx : Odd x) : Odd (T x) := by
  apply hx.mul
  have h : Odd (16*x+3) := ⟨8*x+1, by ring⟩
  exact h.pow

private theorem odd_T_iter (l : ℕ) {x : ℤ} (hx : Odd x) : Odd ((T^[l]) x) := by
  induction l with
  | zero => exact hx
  | succ l ih => rw [iterate_succ_apply']; exact odd_T ih

private theorem iterate_slope (l : ℕ) (x y : ℤ) :
    ∃ c : ℤ, (T^[l]) x-(T^[l]) y = (x-y)*(1+8*c) := by
  induction l with
  | zero => exact ⟨0, by simp⟩
  | succ l ih =>
    obtain ⟨a, ha⟩ := ih
    let s := (T^[l]) x
    let t := (T^[l]) y
    let b := 32*(s^2+s*t+t^2)+12*(s+t)+1
    have hb : T s-T t = (s-t)*(1+8*b) := by dsimp [T,b]; ring
    refine ⟨a+b+8*a*b, ?_⟩
    rw [iterate_succ_apply', iterate_succ_apply']
    change T s - T t = _
    rw [hb, show s-t = (x-y)*(1+8*a) from ha]
    ring

private theorem iterate_pow_two_exact (k : ℕ) (x : ℤ) (hx : Odd x) :
    ∃ u : ℤ, Odd u ∧ (T^[2^k]) x-x = (2:ℤ)^(k+3)*u := by
  induction k with
  | zero =>
    refine ⟨x*(32*x^2+12*x+1), hx.mul ⟨16*x^2+6*x, by ring⟩, ?_⟩
    simp only [pow_zero, iterate_one, zero_add]
    unfold T
    ring
  | succ k ih =>
    obtain ⟨u, hu, hgu⟩ := ih
    let g := T^[2^k]
    obtain ⟨a, ha⟩ := iterate_slope (2^k) (g x) x
    refine ⟨u*(1+4*a), hu.mul ⟨2*a, by ring⟩, ?_⟩
    rw [pow_succ, iterate_mul]
    change g^[2] x - x = _
    simp only [iterate_succ_apply']
    calc
      g (g x) - x = (g (g x)-g x)+(g x-x) := by ring
      _ = (2:ℤ)^(k+1+3)*(u*(1+4*a)) := by
        rw [show g (g x)-g x = (g x-x)*(1+8*a) from ha, show g x-x = _ from hgu,
          show k+1+3 = (k+3)+1 by omega, pow_succ]
        ring

private theorem iterate_pow_two_times (k q : ℕ) (x : ℤ) (hx : Odd x) :
    ∃ w : ℤ, (T^[2^k*q]) x-x = (2:ℤ)^(k+3)*((q : ℤ)+2*w) := by
  induction q with
  | zero => exact ⟨0, by simp⟩
  | succ q ih =>
    obtain ⟨u, hu⟩ := ih
    let y := (T^[2^k*q]) x
    have hy : Odd y := odd_T_iter _ hx
    obtain ⟨_, ⟨v, hv⟩, hstep⟩ := iterate_pow_two_exact k y hy
    refine ⟨u+v, ?_⟩
    rw [Nat.mul_succ, add_comm, iterate_add_apply]
    change (T^[2^k]) y-x = _
    calc
      _ = ((T^[2^k]) y-y)+(y-x) := by ring
      _ = _ := by rw [hstep, hv, show y-x = _ from hu, Nat.cast_succ]; ring

private theorem padicValInt_two_power_mul_odd (e : ℕ) (u : ℤ) (hu : Odd u) :
    padicValInt 2 ((2:ℤ)^e*u) = e := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hno : ¬ (2:ℤ) ∣ u := fun H => (Int.not_even_iff_odd.mpr hu) (even_iff_two_dvd.mpr H)
  have hu0 : u ≠ 0 := fun H => hno (H ▸ dvd_zero _)
  rw [padicValInt.mul (pow_ne_zero _ (by decide)) hu0,
    padicValInt.eq_zero_of_not_dvd hno, add_zero]
  have h : (2:ℤ)^e = ((2^e:ℕ):ℤ) := by simp
  rw [h, padicValInt.of_nat, padicValNat.prime_pow]

/-- Exact dyadic displacement of the cubic map at any odd integer, for every
nonzero iterate. -/
theorem dyadic_iterate_valuation {l : ℕ} (hl : l ≠ 0) {x : ℤ} (hx : Odd x) :
    padicValInt 2 ((T^[l]) x-x) = 3+padicValNat 2 l := by
  let k := padicValNat 2 l
  let q := l.divMaxPow 2
  have he : 2^k*q = l := Nat.pow_padicValNat_mul_divMaxPow 2 l
  have hq : Odd q := Nat.not_even_iff_odd.mp
    (fun H => Nat.not_dvd_divMaxPow (by decide) hl (even_iff_two_dvd.mp H))
  obtain ⟨w, hw⟩ := iterate_pow_two_times k q x hx
  rw [he] at hw
  rw [hw]
  have ho : Odd ((q:ℤ)+2*w) := by
    obtain ⟨a, ha⟩ := hq
    refine ⟨(a:ℤ)+w, ?_⟩
    rw [ha]
    push_cast
    ring
  rw [padicValInt_two_power_mul_odd _ _ ho]
  omega

private theorem goldenLucas_three : goldenLucas 3 = 4 := by
  open D5.S0.Carrier in norm_num [goldenLucas, trace, phi, pow_succ]

private theorem normalize_native (n : ℕ) :
    goldenLucas (3^(n+1))^2 = 16*((T^[n]) 1) := by
  induction n with
  | zero => norm_num [goldenLucas_three]
  | succ n ih =>
    have h := (golden_cubic_lucas_block (n+1) (by omega)).2.2.2.2.2
    rw [h, mul_pow, ih, iterate_succ_apply', T]
    ring

private theorem native_dyadic_lag_from (k l : ℕ) (hl : l ≠ 0) :
    padicValInt 2 ((goldenLucas (3^((l+k)+1))^2+3)-(goldenLucas (3^(k+1))^2+3)) =
      7+padicValNat 2 l := by
  rw [normalize_native, normalize_native, iterate_add_apply]
  let x := (T^[k]) 1
  change padicValInt 2 (16*(T^[l]) x+3-(16*x+3)) = _
  rw [show 16*(T^[l]) x+3-(16*x+3) = 16*((T^[l]) x-x) by ring]
  have hx : Odd x := odd_T_iter _ (by decide)
  have hval := dyadic_iterate_valuation hl hx
  have hx0 : (T^[l]) x-x ≠ 0 := by
    intro he
    rw [he, padicValInt.zero] at hval
    omega
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValInt.mul (by decide) hx0, hval]
  have h16 := padicValInt_two_power_mul_odd 4 1 (by decide)
  norm_num at h16
  rw [h16]
  omega

/-- The native later blocks have exact dyadic distance: a lag of depth k
has block separation of depth 7+k. -/
theorem golden_cubic_dyadic_lag (n m : ℕ) (hm : 1 ≤ m) (hmn : m < n) :
    padicValInt 2 ((goldenLucas (3^n)^2+3)-(goldenLucas (3^m)^2+3)) =
      7+padicValNat 2 (n-m) := by
  have h := native_dyadic_lag_from (m-1) (n-m) (by omega)
  rwa [show (n-m)+(m-1)+1 = n by omega, show (m-1)+1 = m by omega] at h

/-- The actual (unshifted) cubic block. -/
def dyadicBlock (n : ℕ) : ℤ := goldenLucas (3^n)^2+3

theorem dyadicBlock_one : dyadicBlock 1 = 19 := by
  norm_num [dyadicBlock, goldenLucas_three]

/-- Two positive-index blocks coincide modulo \(2^a\) exactly when their
indices differ by a multiple of \(2^{\max(0,a-7)}\). -/
theorem dyadicBlock_collision_iff (a n m : ℕ) (hm : 1 ≤ m) (hmn : m < n) :
    dyadicBlock n ≡ dyadicBlock m [ZMOD (2:ℤ)^a] ↔ 2^(a-7) ∣ n-m := by
  have hval := golden_cubic_dyadic_lag n m hm hmn
  change padicValInt 2 (dyadicBlock n-dyadicBlock m) = _ at hval
  have hne : dyadicBlock n-dyadicBlock m ≠ 0 := by
    intro he
    rw [he, padicValInt.zero] at hval
    omega
  have hD := padicValInt_dvd_iff_of_ne_one (by decide : (2:ℕ) ≠ 1) a
    (dyadicBlock n-dyadicBlock m)
  norm_num only [Nat.cast_ofNat] at hD
  rw [Int.modEq_iff_dvd, ← Int.dvd_neg,
    show -(dyadicBlock m-dyadicBlock n) = dyadicBlock n-dyadicBlock m by ring,
    hD, hval,
    or_iff_right hne, padicValNat_dvd_iff_le_of_ne_one (by decide : (2:ℕ) ≠ 1) (by omega : n-m ≠ 0)]
  omega

/-- All positive-index blocks reduce to 19 modulo 128. -/
theorem dyadicBlock_mod128 (n : ℕ) (hn : 1 ≤ n) :
    dyadicBlock n ≡ 19 [ZMOD 128] := by
  by_cases h : n=1
  · simp [h, dyadicBlock_one]
  have hh := (dyadicBlock_collision_iff 7 n 1 (by decide) (by omega)).mpr
    (by simp : (2:ℕ)^(7-7) ∣ n-1)
  simpa only [dyadicBlock_one, show (2:ℤ)^7=128 by decide] using hh

/-- Every shift preserving the dyadic tail at precision a is a multiple of
the stated exact period. -/
theorem dyadicBlock_period_iff (a l : ℕ) :
    (∀ m : ℕ, 1 ≤ m → dyadicBlock (m+l) ≡ dyadicBlock m [ZMOD (2:ℤ)^a]) ↔
    2^(a-7) ∣ l := by
  rcases eq_or_ne l 0 with rfl | hl
  · simp
  constructor
  · intro h
    simpa using (dyadicBlock_collision_iff a (1+l) 1 (by decide) (by omega)).mp (h 1 (by decide))
  · intro h m hm
    exact (dyadicBlock_collision_iff a (m+l) m hm (by omega)).mpr (by simpa using h)

theorem dyadicBlock_least_period (a : ℕ) :
    IsLeast {l : ℕ | 0 < l ∧ ∀ m : ℕ, 1 ≤ m →
      dyadicBlock (m+l) ≡ dyadicBlock m [ZMOD (2:ℤ)^a]} (2^(a-7)) := by
  refine ⟨⟨by positivity, (dyadicBlock_period_iff a _).mpr dvd_rfl⟩, ?_⟩
  intro l hl
  exact Nat.le_of_dvd hl.1 ((dyadicBlock_period_iff a l).mp hl.2)

/-- At every higher precision, the residues above 19 modulo 128 are all
visited in one cycle, with no requirement on an odd prime divisor. -/
theorem dyadicBlock_full_image (k : ℕ) (z : ℤ) :
    (∃ j < 2^k, dyadicBlock (j+1) ≡ z [ZMOD (2:ℤ)^(7+k)]) ↔ z ≡ 19 [ZMOD 128] := by
  let f (x : ℕ) := dyadicBlock (x+1)
  have hm : (128:ℤ) * ((2^k:ℕ):ℤ) = (2:ℤ)^(7+k) := by push_cast; rw [pow_add]; norm_num
  have hc (n m : ℕ) (h : m < n) : f n % 128 = f m % 128 ↔ (1:ℕ) ∣ n-m := by
    exact iff_of_true ((dyadicBlock_mod128 (n+1) (by omega)).trans
      (dyadicBlock_mod128 (m+1) (by omega)).symm) (one_dvd _)
  have hf (n m : ℕ) (h : m < n) :
      f n % (128 * ((2^k:ℕ):ℤ)) = f m % (128 * ((2^k:ℕ):ℤ)) ↔ 1 * 2^k ∣ n-m := by
    rw [hm]
    have hh := dyadicBlock_collision_iff (7+k) (n+1) (m+1) (by omega) (by omega)
    simpa only [Int.ModEq, f, show 7+k-7=k by omega, Nat.add_sub_add_right, one_mul] using hh
  have he := WSSFinitePhase.completeClockPhase 128 (by decide) 1 (2^k)
    (by decide) (by positivity) f hc hf 0 z
  simpa only [hm, f, zero_add, one_mul, Int.ModEq, dyadicBlock_one] using he

/-- Every residue in the advertised dyadic fibre has exactly one
representative in the first full cycle. -/
theorem dyadicBlock_one_cycle (k : ℕ) {z : ℤ} (hz : z ≡ 19 [ZMOD 128]) :
    ∃! j : Fin (2^k), dyadicBlock (j.val+1) ≡ z [ZMOD (2:ℤ)^(7+k)] := by
  obtain ⟨j,hj,hjz⟩ := (dyadicBlock_full_image k z).mpr hz
  refine ⟨⟨j,hj⟩,hjz,?_⟩
  intro t htz
  apply Fin.ext
  have hsmall (a b : ℕ) (ha : a < 2^k) (hba : b < a)
      (hh : dyadicBlock (a+1) ≡ dyadicBlock (b+1) [ZMOD (2:ℤ)^(7+k)]) : False := by
    have hd := (dyadicBlock_collision_iff (7+k) (a+1) (b+1) (by omega) (by omega)).mp hh
    rw [show 7+k-7=k by omega, Nat.add_sub_add_right] at hd
    have H := Nat.le_of_dvd (by omega : 0 < a-b) hd
    omega
  change t.val = j
  rcases lt_trichotomy t.val j with h | h | h
  · exact (hsmall j t.val hj h (hjz.trans htz.symm)).elim
  · exact h
  · exact (hsmall t.val j t.isLt h (htz.trans hjz.symm)).elim

end D5.S3.Arith.Primes.GoldenCubicDyadicClock
