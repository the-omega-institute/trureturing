/- GID: D5/S3/Factorization/QuadraticIdeals/GoldenCubicPrime67Clock
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/GoldenCubicPrime67Clock
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Prime 67 realizes a native cubic-splitting readout with exact least period sixteen. -/

import D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeCyclic
import Mathlib.Data.Nat.Find
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 8192

namespace D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrime67Clock

def IsPeriod {A : Type*} (w : ℕ → A) (p : ℕ) : Prop := ∀ n, w (n + p) = w n

def IsEventuallyPeriod {A : Type*} (w : ℕ → A) (p : ℕ) : Prop := ∃ t, ∀ n ≥ t, w (n + p) = w n

def IsLeastPositivePeriod {A : Type*} (w : ℕ → A) (p : ℕ) : Prop := 0 < p ∧ IsPeriod w p ∧ ∀ q, 0 < q → IsPeriod w q → p ≤ q

/-- One distinguished first read followed by incompatible reads is a
finite certificate excluding every nonzero period shorter than N. -/
theorem period_ge_of_prefix {A : Type*} (w : ℕ → A) (N p : ℕ)
    (hp : 0 < p) (h : IsPeriod w p)
    (hf : ∀ i, 0 < i → i < N → w i ≠ w 0) : N ≤ p := by
  by_contra hn
  exact hf p hp (by omega) (by simpa only [Nat.zero_add] using h 0)

private theorem period_mul {A : Type*} {w : ℕ → A} {q : ℕ}
    (h : IsPeriod w q) (n m : ℕ) : w (n + m * q) = w n := by
  induction m with
  | zero => simp
  | succ m ih => simpa only [Nat.succ_mul, Nat.add_assoc, ih] using h (n + m * q)

/-- A tail period of a purely periodic word is already a period from time
zero. Genuine transients are precisely the case where this argument does
not apply. -/
theorem eventual_iff_global_period {A : Type*} (w : ℕ → A) (p q : ℕ)
    (hq : 0 < q) (h : IsPeriod w q) :
    IsEventuallyPeriod w p ↔ IsPeriod w p := by
  constructor
  · rintro ⟨t, ht⟩ n
    have hs : t ≤ n + t * q := by
      have ha : t * 1 ≤ t * q := Nat.mul_le_mul_left t hq
      omega
    have he := ht (n + t * q) hs
    calc
      w (n + p) = w ((n + p) + t * q) := (period_mul h (n + p) t).symm
      _ = w ((n + t * q) + p) := by rw [Nat.add_right_comm]
      _ = w (n + t * q) := he
      _ = w n := period_mul h n t
  · intro hp
    exact ⟨0, fun n _ => hp n⟩

/-- The symbolic-dynamics consequence of finite pattern realization and
positive pure periodicity, with those two hypotheses kept separate from
any arithmetic or density claims. -/
theorem unbounded_least_periods {Probe A : Type*} (w : Probe → ℕ → A)
    (realize : ∀ N, ∃ t, ∀ i, 0 < i → i < N → w t i ≠ w t 0)
    (periodic : ∀ t, ∃ p, 0 < p ∧ IsPeriod (w t) p) :
    ∀ N, ∃ t p, N ≤ p ∧ IsLeastPositivePeriod (w t) p := by
  intro N
  obtain ⟨t, ht⟩ := realize N
  classical
  let p := Nat.find (periodic t)
  have hp : 0 < p ∧ IsPeriod (w t) p := Nat.find_spec (periodic t)
  refine ⟨t, p, period_ge_of_prefix (w t) N p hp.1 hp.2 ht, hp.1, hp.2, ?_⟩
  intro q hq hqp
  exact Nat.find_min' (periodic t) ⟨hq, hqp⟩

/-- The usual split-then-inert prefix is a sufficient realization premise. -/
theorem unbounded_of_split_inert_prefix {Probe : Type*} (w : Probe → ℕ → Bool)
    (realize : ∀ N, ∃ t, w t 0 = true ∧ ∀ i, 0 < i → i < N → w t i = false)
    (periodic : ∀ t, ∃ p, 0 < p ∧ IsPeriod (w t) p) :
    ∀ N, ∃ t p, N ≤ p ∧ IsLeastPositivePeriod (w t) p := by
  apply unbounded_least_periods w _ periodic
  intro N
  obtain ⟨t, h0, hi⟩ := realize N
  exact ⟨t, fun i hp hi' => by rw [h0, hi i hp hi']; decide⟩

open D5.S0.Carrier D5.S1.Scale
open D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeCyclic
open Polynomial

def cycle67 : Fin 16 → ZMod 67 := ![4, 9, 19, 15, 3, 36, 65, 53, 28, 60, 38, 46, 56, 43, 40, 1]

def bits67 : Fin 16 → Bool := ![true, false, false, false, false, true, true, false, true, true, false, false, false, false, false, false]

def rootCount (l : ZMod 67) : ℕ := (Finset.univ.filter (fun x : ZMod 67 => equation l x = 0)).card

def clockIndex (n : ℕ) : Fin 16 := ⟨n % 16, Nat.mod_lt _ (by decide)⟩

private theorem clock_add (n m : ℕ) : clockIndex (n + m) = clockIndex n + clockIndex m := by
  apply Fin.ext
  exact Nat.add_mod n m 16

private theorem clock_coe (i : Fin 16) : clockIndex i.val = i := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

private theorem cycle67_step : ∀ i : Fin 16, cycle67 (i + 1) = cycle67 i * (cycle67 i ^ 2 + 3) := by
  decide

private theorem native_cycle67 (n : ℕ) :
    (goldenLucas (3 ^ (n + 1)) : ZMod 67) = cycle67 (clockIndex n) := by
  induction n with
  | zero => norm_num [clockIndex, cycle67, goldenLucas, trace, phi, pow_succ]
  | succ n ih =>
    rw [(golden_cubic_lucas_block (n + 1) (by omega)).2.2.2.2.2, clock_add]
    push_cast
    rw [ih, show clockIndex 1 = 1 by decide, cycle67_step]

private theorem modulo67_rootCount :
    ∀ i : Fin 16, rootCount (cycle67 i) = if bits67 i then 3 else 0 := by
  decide

private theorem rejects_all_short_nonzero_shifts :
    ∀ p : Fin 16, p ≠ 0 → ∃ i : Fin 16, bits67 (i + p) ≠ bits67 i := by
  decide

/-- Count of distinct roots in the residue field determines the literal
split reading of the canonical cubic, at the actual native level n+1. -/
def nativeSplit67 (n : ℕ) : Bool := decide (rootCount (goldenLucas (3 ^ (n + 1)) : ZMod 67) = 3)

theorem nativeSplit67_eq (n : ℕ) :
    nativeSplit67 n = bits67 (clockIndex n) := by
  unfold nativeSplit67
  rw [native_cycle67, modulo67_rootCount]
  cases bits67 (clockIndex n) <;> decide

/-- The exact least positive period of the actual characteristic-67
polynomial split reading is sixteen. -/
theorem native_67_least_period : IsLeastPositivePeriod nativeSplit67 16 := by
  refine ⟨by decide, ?_, ?_⟩
  · intro n
    simp only [nativeSplit67_eq, clock_add, show clockIndex 16 = 0 by decide, add_zero]
  · intro q hq hp
    by_contra h
    have hq16 : q<16 := by omega
    let p : Fin 16 := ⟨q, hq16⟩
    have hp0 : p ≠ 0 := by
      intro e
      have h1 := congrArg Fin.val e
      change q = 0 at h1
      omega
    obtain ⟨i, hi⟩ := rejects_all_short_nonzero_shifts p hp0
    have he := hp i.val
    simp only [nativeSplit67_eq, clock_add, clock_coe] at he
    have hpq : clockIndex q = p := clock_coe p
    rw [hpq] at he
    exact hi he

/-- The clock prime 67 meets the residue restriction, with 5 genuinely
nonsquare (not just an unchecked Euler-criterion annotation). -/
theorem good_prime_67 :
    Nat.Prime 67 ∧ 67 % 3 = 1 ∧ ¬ ∃ x : ZMod 67, x ^ 2 = 5 := by
  decide

theorem native67_nonzero_block (n : ℕ) :
    (goldenLucas (3 ^ (n + 1)) : ZMod 67) ^ 2 + 3 ≠ 0 := by
  rw [native_cycle67]
  exact (show ∀ i : Fin 16, cycle67 i ^ 2 + 3 ≠ 0 by decide) _

end D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrime67Clock
