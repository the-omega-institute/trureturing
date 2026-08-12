/- GID: D5/S1/Deficit/ZeckendorfDisplacementReading
   generality: I
   mirror-B: D5/B/S1/Deficit/ZeckendorfDisplacementReading
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The Zeckendorf up-shift displacement decode S(v) = Σ_{k ∈ wdigits v} F_{k+1} (each occupied Fibonacci index k shifted to k+1) equals the shifted golden Beatty reading ⌊(v+1)·φ⌋ − 1. Proof: aggregate Binet turns S into v·φ + Σ_{k} ψ^k over the canonical (gap ≥ 2) digit list; a two-sided conjugate-error bound Σ ψ^k ∈ (−1/φ², 1/φ) makes S the unique integer in (v·φ − 1/φ², v·φ + 1/φ), and Int.floor_eq_iff with φ − 1 = 1/φ closes the closed form. This records the up-shift displacement reading identity (定理 6.44, third boxed clause); the deficit forms β′(v) = S(v) − v·φ and β(v) = S(v) − v·ψ and the length recovery ℓ = log n are not covered. -/

import Mathlib
import D5.S0.Conventions.WDigits

namespace D5.S1.Deficit.ZeckendorfDisplacementReading

open D5.S0.Conventions

local instance : IsTrans ℕ (fun a b ↦ b + 2 ≤ a) where
  trans _ _ _ hab hbc := by omega

private theorem inv_golden_sq_add_inv_golden :
    Real.goldenRatio⁻¹ ^ 2 + Real.goldenRatio⁻¹ = 1 := by
  rw [Real.inv_goldenRatio]
  nlinarith [Real.goldenConj_sq]

private theorem pow_add_pow_succ {r : ℝ} (hr : r ^ 2 + r = 1) {a : ℕ} (ha : 1 ≤ a) :
    r ^ a + r ^ (a + 1) = r ^ (a - 1) := by
  conv_lhs =>
    lhs
    rw [show a = a - 1 + 1 by omega, pow_succ]
  conv_lhs =>
    rhs
    rw [show a + 1 = (a - 1) + 2 by omega, pow_add]
  calc
    r ^ (a - 1) * r + r ^ (a - 1) * r ^ 2 =
        r ^ (a - 1) * (r ^ 2 + r) := by ring
    _ = r ^ (a - 1) := by rw [hr, mul_one]

private theorem sum_powers_le_sub_head {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hr : r ^ 2 + r = 1) {d a : ℕ} {l : List ℕ}
    (hgap : (a :: l).Pairwise fun x y => y + 2 ≤ x)
    (hmin : ∀ k ∈ a :: l, d + 1 ≤ k) :
    ((a :: l).map fun k => r ^ k).sum ≤ r ^ d - r ^ (a + 1) := by
  induction l generalizing a with
  | nil =>
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [le_sub_iff_add_le, pow_add_pow_succ hr (by have := hmin a (by simp); omega)]
      rw [pow_le_pow_iff_right_of_lt_one₀ hr0 hr1]
      have := hmin a (by simp)
      omega
  | cons b l ih =>
      rw [List.pairwise_cons] at hgap
      have hab : b + 2 ≤ a := hgap.1 b (by simp)
      have htail : (b :: l).Pairwise fun x y => y + 2 ≤ x := hgap.2
      have hmin_tail : ∀ k ∈ b :: l, d + 1 ≤ k := by
        intro k hk
        exact hmin k (by simp [hk])
      have hih := ih htail hmin_tail
      simp only [List.map_cons, List.sum_cons]
      calc
        r ^ a + (r ^ b + (l.map fun k => r ^ k).sum) ≤
            r ^ a + (r ^ d - r ^ (b + 1)) := by
              gcongr
              simpa only [List.map_cons, List.sum_cons] using hih
        _ ≤ r ^ d - r ^ (a + 1) := by
          have hpowers : r ^ a + r ^ (a + 1) ≤ r ^ (b + 1) := by
            rw [pow_add_pow_succ hr (by omega)]
            rw [pow_le_pow_iff_right_of_lt_one₀ hr0 hr1]
            omega
          linarith

private theorem sum_powers_lt {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hr : r ^ 2 + r = 1) {d : ℕ} {l : List ℕ}
    (hgap : l.Pairwise fun x y => y + 2 ≤ x)
    (hmin : ∀ k ∈ l, d + 1 ≤ k) :
    (l.map fun k => r ^ k).sum < r ^ d := by
  cases l with
  | nil => simpa using pow_pos hr0 d
  | cons a l =>
      refine (sum_powers_le_sub_head hr0 hr1 hr hgap hmin).trans_lt ?_
      exact sub_lt_self _ (pow_pos hr0 (a + 1))

private theorem sum_neg_powers_le_sum_powers {r : ℝ} (hr0 : 0 < r) :
    ∀ l : List ℕ,
      (l.map fun k => (-r) ^ k).sum ≤ (l.map fun k => r ^ k).sum := by
  intro l
  induction l with
  | nil => simp
  | cons k l ih =>
      simp only [List.map_cons, List.sum_cons]
      have hkpow : (-r) ^ k ≤ r ^ k := by
        simpa [abs_pow, abs_of_pos hr0] using le_abs_self ((-r) ^ k)
      exact add_le_add hkpow ih

private theorem neg_sum_odd_powers_le_sum_neg_powers {r : ℝ} (hr0 : 0 < r) :
    ∀ l : List ℕ,
      -((l.filter fun k => decide (Odd k)).map fun k => r ^ k).sum ≤
        (l.map fun k => (-r) ^ k).sum := by
  intro l
  induction l with
  | nil => simp
  | cons k l ih =>
      by_cases hk : Odd k
      · rw [List.filter_cons_of_pos (by simp [hk])]
        simp only [List.map_cons, List.sum_cons]
        rw [Odd.neg_pow hk]
        linarith
      · have heven : Even k := Nat.not_odd_iff_even.mp hk
        rw [List.filter_cons_of_neg (by simp [hk])]
        simp only [List.map_cons, List.sum_cons]
        rw [Even.neg_pow heven]
        have hpow : 0 ≤ r ^ k := (pow_pos hr0 k).le
        linarith

private theorem canonical_pairwise {l : List ℕ} (hl : l.IsZeckendorfRep) :
    l.Pairwise fun x y => y + 2 ≤ x := by
  rw [List.IsZeckendorfRep, List.isChain_iff_pairwise] at hl
  exact (List.pairwise_append.mp hl).1

private theorem canonical_two_le {l : List ℕ} (hl : l.IsZeckendorfRep) :
    ∀ k ∈ l, 2 ≤ k := by
  rw [List.IsZeckendorfRep, List.isChain_iff_pairwise] at hl
  intro k hk
  exact (List.pairwise_append.mp hl).2.2 k hk 0 (by simp)

/-- Two-sided conjugate-error bound: over a canonical Zeckendorf digit list the tail
`Σ_{k} ψ^k` lies in the open interval `(−1/φ², 1/φ)`. -/
private theorem conjugate_error_bounds {l : List ℕ} (hl : l.IsZeckendorfRep) :
    -(Real.goldenRatio⁻¹ ^ 2) < (l.map fun k => Real.goldenConj ^ k).sum ∧
      (l.map fun k => Real.goldenConj ^ k).sum < Real.goldenRatio⁻¹ := by
  let r : ℝ := Real.goldenRatio⁻¹
  have hr0 : 0 < r := inv_pos.mpr Real.goldenRatio_pos
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hr : r ^ 2 + r = 1 := inv_golden_sq_add_inv_golden
  have hconj : Real.goldenConj = -r := by
    dsimp [r]
    rw [Real.inv_goldenRatio]
    ring
  have hpair := canonical_pairwise hl
  have hmin := canonical_two_le hl
  have hupperPowers : (l.map fun k => r ^ k).sum < r := by
    simpa using sum_powers_lt hr0 hr1 hr hpair hmin
  have hupper : (l.map fun k => Real.goldenConj ^ k).sum < r := by
    rw [hconj]
    exact (sum_neg_powers_le_sum_powers hr0 l).trans_lt hupperPowers
  have hoddPair : (l.filter fun k => decide (Odd k)).Pairwise fun x y => y + 2 ≤ x :=
    hpair.filter _
  have hoddMin : ∀ k ∈ l.filter (fun k => decide (Odd k)), 3 ≤ k := by
    intro k hk
    have hk' := List.mem_filter.mp hk
    have htwo := hmin k hk'.1
    have hoddK : Odd k := by simpa using hk'.2
    have hne : k ≠ 2 := by
      intro heq
      subst k
      exact (by norm_num : ¬Odd 2) hoddK
    omega
  have hodd : (((l.filter fun k => decide (Odd k)).map fun k => r ^ k).sum) < r ^ 2 :=
    sum_powers_lt hr0 hr1 hr hoddPair hoddMin
  have hlower : -(r ^ 2) < (l.map fun k => Real.goldenConj ^ k).sum := by
    rw [hconj]
    exact lt_of_lt_of_le (neg_lt_neg hodd)
      (neg_sum_odd_powers_le_sum_neg_powers hr0 l)
  exact ⟨hlower, hupper⟩

/-- The **Zeckendorf up-shift displacement decode** `S(v) = Σ_{k ∈ wdigits v} F_{k+1}`: each occupied
Fibonacci index `k` of the canonical Zeckendorf digits of `v` is shifted to `k + 1`. -/
def displacementDecode (v : ℕ) : ℕ :=
  ((wdigits v).map fun k => Nat.fib (k + 1)).sum

/-- Aggregate Binet over an index list: `Σ F_{k+1} = φ · Σ F_k + Σ ψ^k`. -/
private theorem sum_fibsucc (l : List ℕ) :
    ((l.map fun k => (Nat.fib (k + 1) : ℝ)).sum) =
      Real.goldenRatio * (l.map fun k => (Nat.fib k : ℝ)).sum +
        (l.map fun k => Real.goldenConj ^ k).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have hbinet : (Nat.fib (a + 1) : ℝ) =
          Real.goldenRatio * (Nat.fib a : ℝ) + Real.goldenConj ^ a := by
        have := Real.fib_succ_sub_goldenRatio_mul_fib a
        linarith
      simp only [List.map_cons, List.sum_cons, ih, hbinet]
      ring

/-- Real reduction: `(S v : ℝ) = v · φ + Σ_{k ∈ wdigits v} ψ^k`. -/
private theorem decode_real (v : ℕ) :
    (displacementDecode v : ℝ) =
      (v : ℝ) * Real.goldenRatio +
        ((wdigits v).map fun k => Real.goldenConj ^ k).sum := by
  have hcastS : ((displacementDecode v : ℕ) : ℝ) =
      ((wdigits v).map fun k => (Nat.fib (k + 1) : ℝ)).sum := by
    unfold displacementDecode
    induction wdigits v with
    | nil => simp
    | cons a l ih => simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]
  have hdecodeReal : ((wdigits v).map fun k => (Nat.fib k : ℝ)).sum = (v : ℝ) := by
    have hcast : (((wdigits v).map Nat.fib).sum : ℝ) =
        ((wdigits v).map fun k => (Nat.fib k : ℝ)).sum := by
      induction wdigits v with
      | nil => simp
      | cons a l ih => simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]
    rw [← hcast, decode_wdigits]
  rw [hcastS, sum_fibsucc, hdecodeReal]
  ring

/-- **Displacement reading identity (定理 6.44, up-shift closed form).** The Zeckendorf up-shift
displacement decode equals the shifted golden Beatty reading:
`S(v) = ⌊(v + 1) · φ⌋ − 1` for every `v`.

Aggregate Binet reduces `(S v : ℝ)` to `v · φ + Σ_{k} ψ^k` over the canonical digit list; the
two-sided conjugate-error bound `Σ ψ^k ∈ (−1/φ², 1/φ)` makes `S v` the unique integer in
`(v·φ − 1/φ², v·φ + 1/φ)`, and `Int.floor_eq_iff` with `φ − 1 = 1/φ` yields the closed form.

Only the up-shift displacement reading identity is recorded. The deficit forms
`β′(v) = S(v) − v·φ` and `β(v) = S(v) − v·ψ`, and the downstream length recovery `ℓ = log n`, are
not covered. -/
theorem displacement_decode_eq_beatty_floor (v : ℕ) :
    (displacementDecode v : ℤ) =
      ⌊((v : ℝ) + 1) * Real.goldenRatio⌋ - 1 := by
  have hred : (displacementDecode v : ℝ) =
      (v : ℝ) * Real.goldenRatio +
        ((wdigits v).map fun k => Real.goldenConj ^ k).sum := decode_real v
  obtain ⟨hlo, hhi⟩ := conjugate_error_bounds (wdigits_isCanonical v)
  have hinvsq : Real.goldenRatio⁻¹ - 1 = -(Real.goldenRatio⁻¹ ^ 2) := by
    have := inv_golden_sq_add_inv_golden; linarith
  have hphi : Real.goldenRatio = 1 + Real.goldenRatio⁻¹ := by
    have hp : Real.goldenRatio⁻¹ = Real.goldenRatio - 1 := by
      rw [Real.inv_goldenRatio]; linarith [Real.goldenRatio_add_goldenConj]
    linarith
  have hexp : ((v : ℝ) + 1) * Real.goldenRatio =
      (v : ℝ) * Real.goldenRatio + Real.goldenRatio := by ring
  have hfloor : ⌊((v : ℝ) + 1) * Real.goldenRatio⌋ = (displacementDecode v : ℤ) + 1 := by
    rw [Int.floor_eq_iff]
    refine ⟨?_, ?_⟩
    · push_cast; linarith
    · push_cast; linarith
  rw [hfloor]; ring

end D5.S1.Deficit.ZeckendorfDisplacementReading
