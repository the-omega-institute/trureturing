/- GID: D5/S3/Analytic/GoldenEulerBetaZeckendorf
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   digest: The golden Euler exponent account in canonical Zeckendorf coordinates. -/

import D5.S3.Analytic.GoldenEulerBeta
import Mathlib.Data.Nat.Fib.Zeckendorf
import Mathlib.Tactic

/-! SEARCH RECEIPT (2026-09-03, pinned repository and pinned mathlib):
Repository searches for `Wythoff`, `Beatty`, `goldenRatio.*floor`,
`floor.*goldenRatio`, `zeckendorf`, least/last Zeckendorf indices, and parity
found `D5.S1.Words.ZeckendorfBeattyBridge.zeckendorf_beatty_bridge` and
`fibWord_eq_beatty_floor`.  They characterize membership of index two and a
shifted mechanical letter, but do not state the all-index least-parity floor
formula below.  `GoldenFiberCoordinates` has related private floor algebra,
and `ZeckendorfNormSign` has a related private conjugate-tail argument; neither
private result is reusable across its module boundary.

Pinned mathlib's `Mathlib.Data.Nat.Fib.Zeckendorf` supplies
`List.IsZeckendorfRep`, `Nat.isZeckendorfRep_zeckendorf`, and
`Nat.sum_zeckendorf_fib`; its complete declaration list was checked, and no
Beatty/Wythoff formula occurs there.  Searches of pinned mathlib for Wythoff,
Beatty, Rayleigh, golden-ratio floors, and last-index parity found only the
general Beatty-set theorems in `Mathlib.NumberTheory.Rayleigh`, not this
pointwise identity.  The proof therefore composes mathlib's canonical
Zeckendorf API with `Real.goldenConj_mul_fib_succ_add_fib`, golden-ratio
identities, and integer floor laws. -/

namespace D5.S3.Analytic.GoldenEulerBetaZeckendorf

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Analytic.GoldenEulerBeta

noncomputable section

local instance : IsTrans Nat (fun a b => b + 2 <= a) where
  trans _ _ _ hab hbc := by omega

private def shiftedFibSum (n : Nat) : Nat :=
  ((Nat.zeckendorf n).map fun k => Nat.fib (k - 1)).sum

private def conjugateError (n : Nat) : Real :=
  ((Nat.zeckendorf n).map fun k => Real.goldenConj ^ k).sum

private theorem canonical_pairwise (n : Nat) :
    (Nat.zeckendorf n).Pairwise (fun x y => y + 2 <= x) := by
  have h := Nat.isZeckendorfRep_zeckendorf n
  rw [List.IsZeckendorfRep, List.isChain_iff_pairwise] at h
  exact (List.pairwise_append.mp h).1

private theorem canonical_two_le (n : Nat) :
    forall k, k ∈ Nat.zeckendorf n -> 2 <= k := by
  have h := Nat.isZeckendorfRep_zeckendorf n
  rw [List.IsZeckendorfRep, List.isChain_iff_pairwise] at h
  intro k hk
  exact (List.pairwise_append.mp h).2.2 k hk 0 (by simp)

private theorem zeckendorf_ne_nil {n : Nat} (hn : 0 < n) :
    Nat.zeckendorf n ≠ [] := by
  intro hnil
  have hsum := Nat.sum_zeckendorf_fib n
  rw [hnil] at hsum
  simp at hsum
  omega

private theorem getLastD_eq_getLast {alpha : Type*} {l : List alpha}
    (hne : l ≠ []) (d : alpha) : l.getLastD d = l.getLast hne := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getLast_of_ne_nil hne]
  simp

private theorem inv_golden_sq_add_inv_golden :
    Real.goldenRatio⁻¹ ^ 2 + Real.goldenRatio⁻¹ = 1 := by
  rw [Real.inv_goldenRatio]
  nlinarith [Real.goldenConj_sq]

private theorem pow_add_pow_succ {r : Real} (hr : r ^ 2 + r = 1)
    {a : Nat} (ha : 1 <= a) : r ^ a + r ^ (a + 1) = r ^ (a - 1) := by
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

private theorem sum_powers_le_sub_head {r : Real} (hr0 : 0 < r)
    (hr1 : r < 1) (hr : r ^ 2 + r = 1) {d a : Nat} {l : List Nat}
    (hgap : (a :: l).Pairwise fun x y => y + 2 <= x)
    (hmin : forall k, k ∈ a :: l -> d + 1 <= k) :
    ((a :: l).map fun k => r ^ k).sum <= r ^ d - r ^ (a + 1) := by
  induction l generalizing a with
  | nil =>
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [le_sub_iff_add_le, pow_add_pow_succ hr (by
        have := hmin a (by simp)
        omega)]
      rw [pow_le_pow_iff_right_of_lt_one₀ hr0 hr1]
      have := hmin a (by simp)
      omega
  | cons b l ih =>
      rw [List.pairwise_cons] at hgap
      have hab : b + 2 <= a := hgap.1 b (by simp)
      have htail : (b :: l).Pairwise fun x y => y + 2 <= x := hgap.2
      have hminTail : forall k, k ∈ b :: l -> d + 1 <= k := by
        intro k hk
        exact hmin k (by simp [hk])
      have hih := ih htail hminTail
      simp only [List.map_cons, List.sum_cons]
      calc
        r ^ a + (r ^ b + (l.map fun k => r ^ k).sum) <=
            r ^ a + (r ^ d - r ^ (b + 1)) := by
              gcongr
              simpa only [List.map_cons, List.sum_cons] using hih
        _ <= r ^ d - r ^ (a + 1) := by
          have hpowers : r ^ a + r ^ (a + 1) <= r ^ (b + 1) := by
            rw [pow_add_pow_succ hr (by omega)]
            rw [pow_le_pow_iff_right_of_lt_one₀ hr0 hr1]
            omega
          linarith

private theorem sum_powers_lt {r : Real} (hr0 : 0 < r) (hr1 : r < 1)
    (hr : r ^ 2 + r = 1) {d : Nat} {l : List Nat}
    (hgap : l.Pairwise fun x y => y + 2 <= x)
    (hmin : forall k, k ∈ l -> d + 1 <= k) :
    (l.map fun k => r ^ k).sum < r ^ d := by
  cases l with
  | nil => simpa using pow_pos hr0 d
  | cons a l =>
      refine (sum_powers_le_sub_head hr0 hr1 hr hgap hmin).trans_lt ?_
      exact sub_lt_self _ (pow_pos hr0 (a + 1))

private theorem abs_sum_le_sum_abs : forall l : List Real,
    |l.sum| <= (l.map abs).sum
  | [] => by simp
  | x :: xs => by
      simp only [List.sum_cons, List.map_cons]
      exact (abs_add_le x xs.sum).trans
        (add_le_add le_rfl (abs_sum_le_sum_abs xs))

private theorem neg_sum_odd_powers_le_sum_neg_powers {r : Real}
    (hr0 : 0 < r) : forall l : List Nat,
    -((l.filter fun k => decide (Odd k)).map fun k => r ^ k).sum <=
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
        have hpow : 0 <= r ^ k := (pow_pos hr0 k).le
        linarith

private theorem conjugate_error_bounds (n : Nat) :
    -(Real.goldenRatio⁻¹ ^ 2) < conjugateError n ∧
      conjugateError n < Real.goldenRatio⁻¹ := by
  let l := Nat.zeckendorf n
  let r : Real := Real.goldenRatio⁻¹
  have hr0 : 0 < r := inv_pos.mpr Real.goldenRatio_pos
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hr : r ^ 2 + r = 1 := inv_golden_sq_add_inv_golden
  have hpsi : Real.goldenConj = -r := by
    dsimp [r]
    rw [Real.inv_goldenRatio]
    ring
  have hpair : l.Pairwise (fun x y => y + 2 <= x) := canonical_pairwise n
  have htwo : forall k, k ∈ l -> 2 <= k := canonical_two_le n
  have hpowers : (l.map fun k => r ^ k).sum < r := by
    simpa using sum_powers_lt hr0 hr1 hr hpair htwo
  have hupper : conjugateError n < r := by
    calc
      conjugateError n <= |conjugateError n| := le_abs_self _
      _ <= (l.map fun k => |Real.goldenConj ^ k|).sum := by
        dsimp [conjugateError, l]
        simpa only [List.map_map, Function.comp_def] using
          abs_sum_le_sum_abs
            ((Nat.zeckendorf n).map fun k => Real.goldenConj ^ k)
      _ = (l.map fun k => r ^ k).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro k hk
        rw [abs_pow, abs_of_neg Real.goldenConj_neg, hpsi]
        simp
      _ < r := hpowers
  let odds := l.filter fun k => decide (Odd k)
  have hoddPair : odds.Pairwise (fun x y => y + 2 <= x) := hpair.filter _
  have hoddMin : forall k, k ∈ odds -> 3 <= k := by
    intro k hk
    have hk' := List.mem_filter.mp hk
    have hkTwo := htwo k hk'.1
    have hkOdd : Odd k := by simpa using hk'.2
    rcases hkOdd with ⟨a, ha⟩
    omega
  have hodd : (odds.map fun k => r ^ k).sum < r ^ 2 :=
    sum_powers_lt hr0 hr1 hr hoddPair hoddMin
  have hlower : -(r ^ 2) < conjugateError n := by
    calc
      -(r ^ 2) < -(odds.map fun k => r ^ k).sum := neg_lt_neg hodd
      _ <= conjugateError n := by
        dsimp [odds, conjugateError, l]
        rw [hpsi]
        exact neg_sum_odd_powers_le_sum_neg_powers hr0 (Nat.zeckendorf n)
  exact ⟨by simpa [r] using hlower, by simpa [r] using hupper⟩

private theorem conjugate_error_sign {n : Nat} (hn : 0 < n) :
    (0 < conjugateError n <-> Even ((Nat.zeckendorf n).getLastD 0)) ∧
      (conjugateError n < 0 <-> Odd ((Nat.zeckendorf n).getLastD 0)) := by
  let l := Nat.zeckendorf n
  let k := l.getLastD 0
  let pre := l.dropLast
  have hne : l ≠ [] := zeckendorf_ne_nil hn
  have hpair : l.Pairwise (fun x y => y + 2 <= x) := canonical_pairwise n
  have hlast : l.getLast hne = k := (getLastD_eq_getLast hne 0).symm
  have hdecomp : pre ++ [k] = l := by
    dsimp [pre]
    simpa [hlast] using List.dropLast_append_getLast hne
  have htailGap : pre.Pairwise (fun x y => y + 2 <= x) :=
    hpair.sublist (List.dropLast_sublist l)
  have htailMin : forall j, j ∈ pre -> k + 2 <= j := by
    intro j hj
    have hrel := hpair.rel_dropLast_getLast hj
    rw [hlast] at hrel
    exact hrel
  let r : Real := Real.goldenRatio⁻¹
  have hr0 : 0 < r := inv_pos.mpr Real.goldenRatio_pos
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hr : r ^ 2 + r = 1 := inv_golden_sq_add_inv_golden
  have hpsi : Real.goldenConj = -r := by
    dsimp [r]
    rw [Real.inv_goldenRatio]
    ring
  have hpowEven : forall {m : Nat}, Even m ->
      Real.goldenConj ^ m = r ^ m := by
    intro m hm
    rw [hpsi, hm.neg_pow]
  have hpowOdd : forall {m : Nat}, Odd m ->
      Real.goldenConj ^ m = -(r ^ m) := by
    intro m hm
    rw [hpsi, hm.neg_pow]
  have htailAbs : |(pre.map fun j => Real.goldenConj ^ j).sum| < r ^ k := by
    calc
      |(pre.map fun j => Real.goldenConj ^ j).sum| <=
          (pre.map fun j => |Real.goldenConj ^ j|).sum := by
            simpa only [List.map_map, Function.comp_def] using
              abs_sum_le_sum_abs (pre.map fun j => Real.goldenConj ^ j)
      _ = (pre.map fun j => r ^ j).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro j hj
        rw [abs_pow, abs_of_neg Real.goldenConj_neg, hpsi]
        simp
      _ < r ^ (k + 1) := by
        apply sum_powers_lt hr0 hr1 hr htailGap
        intro j hj
        have := htailMin j hj
        omega
      _ < r ^ k := pow_lt_pow_right_of_lt_one₀ hr0 hr1 (by omega)
  have hsum : conjugateError n =
      Real.goldenConj ^ k + (pre.map fun j => Real.goldenConj ^ j).sum := by
    dsimp [conjugateError]
    change (l.map fun j => Real.goldenConj ^ j).sum = _
    rw [← hdecomp, List.map_append]
    simp [add_comm]
  have hparity : Even k ∨ Odd k := Nat.even_or_odd k
  change
    (0 < conjugateError n <-> Even k) ∧
      (conjugateError n < 0 <-> Odd k)
  constructor
  · constructor
    · intro hpos
      rcases hparity with heven | hodd
      · exact heven
      · rw [hsum, hpowOdd hodd] at hpos
        have hupper := (abs_lt.mp htailAbs).2
        exfalso
        linarith [pow_pos hr0 k]
    · intro heven
      rw [hsum, hpowEven heven]
      have hlower := (abs_lt.mp htailAbs).1
      linarith [pow_pos hr0 k]
  · constructor
    · intro hneg
      rcases hparity with heven | hodd
      · rw [hsum, hpowEven heven] at hneg
        have hlower := (abs_lt.mp htailAbs).1
        exfalso
        linarith [pow_pos hr0 k]
      · exact hodd
    · intro hodd
      rw [hsum, hpowOdd hodd]
      have hupper := (abs_lt.mp htailAbs).2
      linarith [pow_pos hr0 k]

private theorem fib_mul_inv_golden {k : Nat} (hk : 2 <= k) :
    (Nat.fib k : Real) * Real.goldenRatio⁻¹ =
      (Nat.fib (k - 1) : Real) - Real.goldenConj ^ k := by
  have h := Real.goldenConj_mul_fib_succ_add_fib (k - 1)
  rw [Nat.sub_add_cancel (by omega : 1 <= k)] at h
  rw [Real.inv_goldenRatio]
  linarith

private theorem sum_fib_mul_inv_golden {l : List Nat}
    (hmin : forall k, k ∈ l -> 2 <= k) :
    (l.map fun k => (Nat.fib k : Real) * Real.goldenRatio⁻¹).sum =
      (l.map fun k => (Nat.fib (k - 1) : Real)).sum -
        (l.map fun k => Real.goldenConj ^ k).sum := by
  induction l with
  | nil => simp
  | cons k l ih =>
      have hk : 2 <= k := hmin k (by simp)
      have htail : forall j, j ∈ l -> 2 <= j := by
        intro j hj
        exact hmin j (by simp [hj])
      simp only [List.map_cons, List.sum_cons]
      rw [fib_mul_inv_golden hk, ih htail]
      ring

private theorem div_golden_eq_shift_sub_error (n : Nat) :
    (n : Real) / Real.goldenRatio =
      (shiftedFibSum n : Real) - conjugateError n := by
  let l := Nat.zeckendorf n
  have hmin : forall k, k ∈ l -> 2 <= k := canonical_two_le n
  have hterms :
      (l.map fun k => (Nat.fib k : Real) * Real.goldenRatio⁻¹).sum =
        (l.map fun k => (Nat.fib (k - 1) : Real)).sum -
          (l.map fun k => Real.goldenConj ^ k).sum :=
    sum_fib_mul_inv_golden hmin
  have hdecode :
      (l.map fun k => (Nat.fib k : Real)).sum = (n : Real) := by
    have hcast : (((Nat.zeckendorf n).map Nat.fib).sum : Real) =
        ((Nat.zeckendorf n).map fun k => (Nat.fib k : Real)).sum := by
      induction Nat.zeckendorf n with
      | nil => simp
      | cons k ks ih => simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]
    dsimp [l]
    rw [← hcast, Nat.sum_zeckendorf_fib]
  have hmul :
      (l.map fun k => (Nat.fib k : Real)).sum * Real.goldenRatio⁻¹ =
        (l.map fun k => (Nat.fib k : Real) * Real.goldenRatio⁻¹).sum := by
    induction l with
    | nil => simp
    | cons k ks ih => simp only [List.map_cons, List.sum_cons, add_mul, ih]
  have hshiftCast :
      (shiftedFibSum n : Real) =
        (l.map fun k => (Nat.fib (k - 1) : Real)).sum := by
    have hcast :
        (((Nat.zeckendorf n).map fun k => Nat.fib (k - 1)).sum : Real) =
          ((Nat.zeckendorf n).map fun k => (Nat.fib (k - 1) : Real)).sum := by
      induction Nat.zeckendorf n with
      | nil => simp
      | cons k ks ih => simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]
    simpa [shiftedFibSum, l] using hcast
  rw [div_eq_mul_inv, ← hdecode, hmul, hterms, ← hshiftCast]
  rfl

private theorem floor_div_golden_zeckendorf {n : Nat} (hn : 0 < n) :
    ⌊(n : Real) / Real.goldenRatio⌋ =
      (shiftedFibSum n : Int) -
        if Even ((Nat.zeckendorf n).getLastD 0) then 1 else 0 := by
  let r : Real := Real.goldenRatio⁻¹
  let e := conjugateError n
  have hr0 : 0 < r := inv_pos.mpr Real.goldenRatio_pos
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hbounds := conjugate_error_bounds n
  have hsign := conjugate_error_sign hn
  have hdecomp := div_golden_eq_shift_sub_error n
  by_cases heven : Even ((Nat.zeckendorf n).getLastD 0)
  · rw [if_pos heven]
    apply Int.floor_eq_iff.mpr
    constructor
    · push_cast
      rw [hdecomp]
      have he_lt_one : conjugateError n < 1 := hbounds.2.trans hr1
      linarith
    · push_cast
      rw [hdecomp]
      linarith [hsign.1.mpr heven]
  · rw [if_neg heven, sub_zero]
    have hodd : Odd ((Nat.zeckendorf n).getLastD 0) :=
      Nat.not_even_iff_odd.mp heven
    apply Int.floor_eq_iff.mpr
    constructor
    · push_cast
      rw [hdecomp]
      linarith [hsign.2.mpr hodd]
    · push_cast
      dsimp [r, e] at hr0 hr1 hbounds
      rw [hdecomp]
      have hrSq_lt_one : Real.goldenRatio⁻¹ ^ 2 < 1 := by nlinarith
      linarith

private theorem floor_succ_div_golden_eq_shifted {n : Nat} (_hn : 0 < n) :
    ⌊((n + 1 : Nat) : Real) / Real.goldenRatio⌋ =
      (shiftedFibSum n : Int) := by
  let r : Real := Real.goldenRatio⁻¹
  let e := conjugateError n
  have hr : r ^ 2 + r = 1 := inv_golden_sq_add_inv_golden
  have hbounds := conjugate_error_bounds n
  have hdecomp := div_golden_eq_shift_sub_error n
  have hnext : ((n + 1 : Nat) : Real) / Real.goldenRatio =
      (shiftedFibSum n : Real) + (r - e) := by
    rw [Nat.cast_add, Nat.cast_one, add_div, hdecomp]
    simp only [one_div]
    ring
  have hnext' : ((n : Real) + 1) / Real.goldenRatio =
      (shiftedFibSum n : Real) + (r - e) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hnext
  apply Int.floor_eq_iff.mpr
  constructor
  · push_cast
    rw [hnext']
    linarith
  · push_cast
    rw [hnext']
    dsimp [r, e] at hbounds hr
    linarith

private theorem floor_div_golden_step {n : Nat} (hn : 0 < n) :
    ⌊((n + 1 : Nat) : Real) / Real.goldenRatio⌋ -
        ⌊(n : Real) / Real.goldenRatio⌋ =
      if Even ((Nat.zeckendorf n).getLastD 0) then 1 else 0 := by
  rw [floor_succ_div_golden_eq_shifted hn,
    floor_div_golden_zeckendorf hn]
  omega

private theorem floor_mul_golden_shift (v : Nat) :
    ⌊(((v : Real) + 1) * Real.goldenRatio)⌋ =
      (v + 1 : Int) + ⌊((v : Real) + 1) / Real.goldenRatio⌋ := by
  have hinv : Real.goldenRatio⁻¹ = Real.goldenRatio - 1 := by
    rw [Real.inv_goldenRatio]
    linarith [Real.goldenRatio_add_goldenConj]
  have harg : ((v : Real) + 1) * Real.goldenRatio =
      ((v + 1 : Nat) : Real) + ((v : Real) + 1) / Real.goldenRatio := by
    rw [div_eq_mul_inv, hinv]
    norm_num
    ring
  rw [harg, Int.floor_natCast_add]
  norm_num

private theorem o5_beta_zeckendorf_closed (v : Nat) :
    o5Beta v =
      (⌊((v : Real) + 1) / Real.goldenRatio⌋ : Real) +
        (v : Real) * Real.goldenRatio := by
  rw [o5_beta_closed_form]
  have hfract :=
    Int.floor_add_fract (((v : Real) + 1) * Real.goldenRatio)
  have hfloor := congrArg (fun z : Int => (z : Real))
    (floor_mul_golden_shift v)
  push_cast at hfloor
  simp only [Nat.cast_add, Nat.cast_one] at ⊢
  rw [one_div, Real.inv_goldenRatio,
    ← Real.goldenRatio_sub_goldenConj, ← Real.one_sub_goldenConj]
  linarith

private theorem o5_beta_zeckendorf_jump (v : Nat) :
    o5Beta (v + 1) - o5Beta v =
      if Even ((Nat.zeckendorf (v + 1)).getLastD 0) then
        Real.goldenRatio ^ 2 else Real.goldenRatio := by
  have hstep := floor_div_golden_step (n := v + 1) (by omega)
  have hstepReal := congrArg (fun z : Int => (z : Real)) hstep
  push_cast at hstepReal
  rw [o5_beta_zeckendorf_closed, o5_beta_zeckendorf_closed]
  simp only [Nat.cast_add, Nat.cast_one]
  by_cases heven : Even ((Nat.zeckendorf (v + 1)).getLastD 0)
  · rw [if_pos heven] at hstepReal ⊢
    rw [Real.goldenRatio_sq]
    linarith
  · rw [if_neg heven] at hstepReal ⊢
    linarith

/-- The golden Euler exponent account has a closed Beatty form, its Beatty
floor is the shifted Zeckendorf Fibonacci sum with the least-index parity
correction, and that same parity selects every exponent jump. -/
theorem golden_euler_beta_zeckendorf :
    (forall v : Nat,
      o5Beta v =
        (⌊((v : Real) + 1) / Real.goldenRatio⌋ : Real) +
          (v : Real) * Real.goldenRatio) ∧
      (forall n : Nat, 0 < n ->
        ⌊(n : Real) / Real.goldenRatio⌋ =
          (((Nat.zeckendorf n).map fun k => Nat.fib (k - 1)).sum : Int) -
            if Even ((Nat.zeckendorf n).getLastD 0) then 1 else 0) ∧
      (forall v : Nat,
        o5Beta (v + 1) - o5Beta v =
          if Even ((Nat.zeckendorf (v + 1)).getLastD 0) then
            Real.goldenRatio ^ 2 else Real.goldenRatio) := by
  refine ⟨o5_beta_zeckendorf_closed, ?_, o5_beta_zeckendorf_jump⟩
  intro n hn
  simpa [shiftedFibSum] using floor_div_golden_zeckendorf hn

#print axioms golden_euler_beta_zeckendorf

end

end D5.S3.Analytic.GoldenEulerBetaZeckendorf
