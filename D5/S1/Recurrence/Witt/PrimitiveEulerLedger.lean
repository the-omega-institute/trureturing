/- GID: D5/S1/Recurrence/Witt/PrimitiveEulerLedger
   generality: G
   mirror-B: D5/B/S1/Recurrence/Witt/PrimitiveEulerLedger
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every integer power series with constant term one has a unique primitive Euler ledger. -/

import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic

/- Duplicate-search audit (2026-09-02):
   * Exact D5 searches for primitive Euler ledgers and unique Euler products found
     no matching theorem.
   * Spelling and symbol searches covered Euler/Witt, `1 - X ^ n`, power-series
     products, coefficient recursion, and integer exponent accounts.
   * The formalization-receipt index has no receipt for the source atom, and its
     digest entry remains residual-open.
   * Generalized searches found only analytic Euler products and the first two
     concrete Witt-row identities, not the all-series existence/uniqueness result.
   * No matching declaration occurs on the remote mathematics lane tips.
   * Pinned Mathlib supplies `PowerSeries.binomialSeries_coeff`, `coeff_mul`, and
     generalized binomial coefficients, but no packaged Euler-ledger theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Finset

namespace D5.S1.Recurrence.Witt.PrimitiveEulerLedger

open PowerSeries

/-- The generalized-binomial power series `(1 - X^n)^(-c)`. Only positive
`n` are used in the ledger. -/
def eulerFactor (n : Nat) (c : Int) : Int⟦X⟧ :=
  PowerSeries.mk fun k =>
    if n ∣ k then (-1 : Int) ^ (k / n) * Ring.choose (-c) (k / n) else 0

@[simp] theorem coeff_eulerFactor (n k : Nat) (c : Int) :
    coeff k (eulerFactor n c) =
      if n ∣ k then (-1 : Int) ^ (k / n) * Ring.choose (-c) (k / n) else 0 := by
  simp [eulerFactor]

@[simp] theorem constantCoeff_eulerFactor (n : Nat) (c : Int) :
    constantCoeff (eulerFactor (n + 1) c) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp

theorem coeff_eulerFactor_of_pos_of_lt (n k : Nat) (c : Int)
    (hk : 0 < k) (hkn : k < n) :
    coeff k (eulerFactor n c) = 0 := by
  rw [coeff_eulerFactor, if_neg]
  exact Nat.not_dvd_of_pos_of_lt hk hkn

@[simp] theorem coeff_eulerFactor_self (n : Nat) (c : Int) :
    coeff (n + 1) (eulerFactor (n + 1) c) = c := by
  simp

private theorem coeff_mul_eulerFactor_of_lt
    (p : Int⟦X⟧) (n k : Nat) (c : Int) (hk : k < n + 1) :
    coeff k (p * eulerFactor (n + 1) c) = coeff k p := by
  rw [coeff_mul, Finset.sum_eq_single (k, 0)]
  · simp
  · intro pair hpair hne
    have hsum : pair.1 + pair.2 = k := Finset.mem_antidiagonal.mp hpair
    have hsnd : 0 < pair.2 := by
      by_contra hz
      have hz' : pair.2 = 0 := Nat.eq_zero_of_not_pos hz
      have hfst : pair.1 = k := by omega
      exact hne (Prod.ext hfst hz')
    have hsndlt : pair.2 < n + 1 := by omega
    rw [coeff_eulerFactor_of_pos_of_lt (n + 1) pair.2 c hsnd hsndlt, mul_zero]
  · exact fun h => (h (Finset.mem_antidiagonal.mpr rfl)).elim

private theorem coeff_mul_eulerFactor_self
    (p : Int⟦X⟧) (n : Nat) (c : Int) :
    coeff (n + 1) (p * eulerFactor (n + 1) c) =
      coeff (n + 1) p + c * constantCoeff p := by
  have hleft : (n + 1, 0) ∈ Finset.antidiagonal (n + 1) := by simp
  have hright : (0, n + 1) ∈
      (Finset.antidiagonal (n + 1)).erase (n + 1, 0) := by simp
  rw [coeff_mul, ← Finset.insert_erase hleft,
    Finset.sum_insert (Finset.notMem_erase _ _), Finset.sum_eq_single (0, n + 1)]
  · simp [mul_comm]
  · intro pair hpair hne
    have hanti : pair ∈ Finset.antidiagonal (n + 1) :=
      Finset.mem_of_mem_erase hpair
    have hsum : pair.1 + pair.2 = n + 1 := Finset.mem_antidiagonal.mp hanti
    have hnotleft : pair ≠ (n + 1, 0) := Finset.ne_of_mem_erase hpair
    have hsnd : 0 < pair.2 := by
      by_contra hz
      have hz' : pair.2 = 0 := Nat.eq_zero_of_not_pos hz
      have hfst : pair.1 = n + 1 := by omega
      exact hnotleft (Prod.ext hfst hz')
    have hsndlt : pair.2 < n + 1 := by
      by_contra hge
      have hsndeq : pair.2 = n + 1 := by omega
      have hfsteq : pair.1 = 0 := by omega
      exact hne (Prod.ext hfsteq hsndeq)
    rw [coeff_eulerFactor_of_pos_of_lt (n + 1) pair.2 c hsnd hsndlt, mul_zero]
  · exact fun h => (h hright).elim

/-- The successive finite products obtained by canceling one new coefficient
at each positive degree. -/
def eulerApprox (f : Int⟦X⟧) : Nat → Int⟦X⟧
  | 0 => 1
  | n + 1 =>
      eulerApprox f n *
        eulerFactor (n + 1) (coeff (n + 1) f - coeff (n + 1) (eulerApprox f n))

/-- The integer exponent selected when degree `n + 1` is first reached. -/
def primitiveEulerLedger (f : Int⟦X⟧) (n : Nat) : Int :=
  coeff (n + 1) f - coeff (n + 1) (eulerApprox f n)

/-- The finite Euler product through the first `N` positive degrees. -/
def ledgerProduct (c : Nat → Int) (N : Nat) : Int⟦X⟧ :=
  ∏ n ∈ Finset.range N, eulerFactor (n + 1) (c n)

/-- A ledger represents a series when every bounded coefficient interval is
already correct in the corresponding finite product. -/
def Represents (f : Int⟦X⟧) (c : Nat → Int) : Prop :=
  ∀ N k, k ≤ N → coeff k (ledgerProduct c N) = coeff k f

@[simp] private theorem ledgerProduct_zero (c : Nat → Int) :
    ledgerProduct c 0 = 1 := by
  simp [ledgerProduct]

private theorem ledgerProduct_succ (c : Nat → Int) (n : Nat) :
    ledgerProduct c (n + 1) =
      ledgerProduct c n * eulerFactor (n + 1) (c n) := by
  simp [ledgerProduct, Finset.prod_range_succ]

private theorem constantCoeff_ledgerProduct (c : Nat → Int) (N : Nat) :
    constantCoeff (ledgerProduct c N) = 1 := by
  induction N with
  | zero => simp
  | succ n ih =>
      rw [ledgerProduct_succ, map_mul, ih, constantCoeff_eulerFactor, one_mul]

private theorem constantCoeff_eulerApprox (f : Int⟦X⟧) (N : Nat) :
    constantCoeff (eulerApprox f N) = 1 := by
  induction N with
  | zero => simp [eulerApprox]
  | succ n ih =>
      rw [eulerApprox, map_mul, ih, constantCoeff_eulerFactor, one_mul]

private theorem eulerApprox_eq_ledgerProduct (f : Int⟦X⟧) (N : Nat) :
    eulerApprox f N = ledgerProduct (primitiveEulerLedger f) N := by
  induction N with
  | zero => simp [eulerApprox]
  | succ n ih =>
      rw [eulerApprox, ledgerProduct_succ, ← ih]
      rfl

private theorem coeff_eulerApprox_eq (f : Int⟦X⟧)
    (hconstant : constantCoeff f = 1) (N k : Nat) (hk : k ≤ N) :
    coeff k (eulerApprox f N) = coeff k f := by
  induction N with
  | zero =>
      have hk0 : k = 0 := by omega
      subst k
      calc
        coeff 0 (eulerApprox f 0) = 1 := by simp [eulerApprox]
        _ = coeff 0 f := by
          rw [coeff_zero_eq_constantCoeff_apply]
          exact hconstant.symm
  | succ n ih =>
      by_cases htop : k = n + 1
      · subst k
        rw [eulerApprox, coeff_mul_eulerFactor_self,
          constantCoeff_eulerApprox]
        ring
      · have hklt : k < n + 1 := by omega
        rw [eulerApprox, coeff_mul_eulerFactor_of_lt _ n k _ hklt]
        exact ih (by omega)

private theorem primitiveEulerLedger_represents (f : Int⟦X⟧)
    (hconstant : constantCoeff f = 1) :
    Represents f (primitiveEulerLedger f) := by
  intro N k hk
  rw [← eulerApprox_eq_ledgerProduct]
  exact coeff_eulerApprox_eq f hconstant N k hk

private theorem represents_unique (f : Int⟦X⟧) (c : Nat → Int)
    (hc : Represents f c) : c = primitiveEulerLedger f := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hprefix : ledgerProduct c n = ledgerProduct (primitiveEulerLedger f) n := by
        apply Finset.prod_congr rfl
        intro k hk
        have hkn : k < n := Finset.mem_range.mp hk
        rw [ih k hkn]
      have hdegree := hc (n + 1) (n + 1) le_rfl
      rw [ledgerProduct_succ, coeff_mul_eulerFactor_self,
        constantCoeff_ledgerProduct, mul_one, hprefix,
        ← eulerApprox_eq_ledgerProduct] at hdegree
      change c n = coeff (n + 1) f - coeff (n + 1) (eulerApprox f n)
      rw [eq_sub_iff_add_eq]
      simpa [add_comm] using hdegree

/-- **Unique primitive Euler ledger.** Every integer formal power series with
constant coefficient one has a unique integer exponent at each positive degree.
The product assertion is coefficientwise and finite on every truncation, which
is the formal local-finiteness condition. -/
theorem unique_primitive_euler_ledger (f : Int⟦X⟧)
    (hconstant : constantCoeff f = 1) :
    ∃! c : Nat → Int, Represents f c := by
  refine ⟨primitiveEulerLedger f, primitiveEulerLedger_represents f hconstant, ?_⟩
  intro c hc
  exact represents_unique f c hc

#print axioms unique_primitive_euler_ledger

end D5.S1.Recurrence.Witt.PrimitiveEulerLedger
