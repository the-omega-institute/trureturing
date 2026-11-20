/- GID: D5/S1/Words/Powers/CommonPositivePowers
   generality: G
   mirror-B: D5/B/S1/Words/Powers/CommonPositivePowers
   mirror-E: none(waiver:abstract-word-commutation-without-separate-evidence-artifact)
   anchors: []
   utility: none
   digest: Two finite words with equal positive natural powers commute. -/

/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in
`docs/reports/licenses/ietfree-LICENSE.txt`.
Authors: Sébastien Gouëzel
-/

module

public import Mathlib.Data.List.PeriodicityLemma

/-!
The periodic-list helpers through `append_comm_of_flatten_replicate_eq` are
transplanted from Sébastien Gouëzel's IETFree/ListPeriodicity.lean:
https://github.com/sgouezel/IETFree/blob/48a23a630f39ae7c439b9efcbd03e729c18406fd/IETFree/ListPeriodicity.lean
The immutable revision is 48a23a630f39ae7c439b9efcbd03e729c18406fd.
The transplant preserves the positive-exponent hypotheses and the Fine–Wilf
period/reassembly proof; ring normalization is replaced by elementary Nat
rewrites.
The private block lemmas include zero block length; the public positive-exponent assumptions remain unchanged.
The original prefix lemma and group applications are
outside this module. The complete Apache 2.0 license accompanies the source;
the upstream tree contains no NOTICE file.

Retirement: when this repository's own pinned Mathlib contains equivalent
same-signature List declarations, in particular
`List.append_comm_of_flatten_replicate_eq`, delete the corresponding
transplants and use those declarations by direct import. Acceptance elsewhere
without their presence in this repository's pin does not trigger retirement.

-/

public section

namespace D5.S1.Words.Powers.CommonPositivePowers

universe u

variable {α : Type u}

/-- The flattening of `k ≥ 1` copies of `w` has period `|w|`. -/
private theorem hasPeriod_flatten_replicate {w : List α} {k : ℕ} (hk : k ≠ 0) :
    (List.replicate k w).flatten.HasPeriod w.length := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [List.HasPeriod]
  have h1 : (List.replicate (k' + 1) w).flatten = w ++ (List.replicate k' w).flatten := by
    rw [List.replicate_succ, List.flatten_cons]
  have h2 : w ++ (List.replicate k' w).flatten = (List.replicate k' w).flatten ++ w := by
    rw [← h1, List.replicate_succ', List.flatten_concat]
  have hgoal : w ++ (w ++ (List.replicate k' w).flatten) =
      (w ++ (List.replicate k' w).flatten) ++ w := by
    rw [h2, ← List.append_assoc, h2]
  rw [h1, List.take_left, hgoal]
  exact List.prefix_append _ _

private theorem drop_mul_prefix {U : List α} {d : ℕ} (hper : U.HasPeriod d) (m : ℕ) :
    U.drop (m * d) <+: U := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hstep : U.drop ((m + 1) * d) = (U.drop (m * d)).drop d := by
        rw [List.drop_drop]
        congr 1
        simp only [Nat.add_mul, Nat.one_mul, Nat.add_comm]
      rw [hstep]
      refine (List.HasPeriod.drop_prefix d ?_).trans ih
      exact hper.infix ⟨U.take (m * d), [], by rw [List.take_append_drop, List.append_nil]⟩

private theorem take_drop_mul_eq_take {U : List α} {d : ℕ} (hper : U.HasPeriod d)
    {m : ℕ} (hlen : (m + 1) * d ≤ U.length) : (U.drop (m * d)).take d = U.take d := by
  have hX : U.drop (m * d) <+: U := drop_mul_prefix hper m
  have hXd : U.drop (m * d) = U.take (U.drop (m * d)).length := by
    rw [List.prefix_iff_eq_take] at hX
    exact hX
  have hlen2 : m * d + d ≤ U.length := by rwa [Nat.succ_mul] at hlen
  have hdX : d ≤ (U.drop (m * d)).length := by
    rw [List.length_drop]; omega
  rw [hXd, List.take_take, Nat.min_eq_left hdX]

private theorem take_eq_flatten_replicate_of_hasPeriod {U : List α} {d : ℕ}
    (hper : U.HasPeriod d) (m : ℕ) (hlen : m * d ≤ U.length) :
    U.take (m * d) = (List.replicate m (U.take d)).flatten := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hlen2 : m * d + d ≤ U.length := by rwa [Nat.succ_mul] at hlen
      have hlen' : m * d ≤ U.length := by omega
      have hstep : (U.drop (m * d)).take d = U.take d := take_drop_mul_eq_take hper hlen
      calc U.take ((m + 1) * d) = U.take (m * d + d) := by rw [Nat.succ_mul]
        _ = U.take (m * d) ++ (U.drop (m * d)).take d := List.take_add
        _ = (List.replicate m (U.take d)).flatten ++ U.take d := by rw [ih hlen', hstep]
        _ = (List.replicate (m + 1) (U.take d)).flatten := by
              rw [List.replicate_succ', List.flatten_concat]

/-- Two words with a common positive power commute. -/
theorem append_comm_of_flatten_replicate_eq {w v : List α} {M N : ℕ}
    (hM : M ≠ 0) (hN : N ≠ 0)
    (h : (List.replicate M w).flatten = (List.replicate N v).flatten) :
    w ++ v = v ++ w := by
  by_cases hw : w = []
  · simp [hw]
  by_cases hv : v = []
  · simp [hv]
  -- Both `w` and `v` are periods of the common word `U = flatten (replicate (2 * M) w)`, whose
  -- length is also a multiple of `N * |v|`; the periodicity lemma then makes `|w| + |v|` a period,
  -- and comparing the first `|w| + |v|` letters gives `w ++ v = v ++ w`.
  have hp : 0 < w.length := List.length_pos_of_ne_nil hw
  have hq : 0 < v.length := List.length_pos_of_ne_nil hv
  set d := Nat.gcd w.length v.length with hd
  have hdp : d ∣ w.length := by rw [hd]; exact Nat.gcd_dvd_left _ _
  have hdq : d ∣ v.length := by rw [hd]; exact Nat.gcd_dvd_right _ _
  set U := (List.replicate (2 * M) w).flatten with hU
  have hW : (List.replicate M w).flatten = w ++ (List.replicate (M - 1) w).flatten := by
    conv_lhs => rw [show M = M - 1 + 1 by omega]
    rw [List.replicate_succ, List.flatten_cons]
  have hV : (List.replicate N v).flatten = v ++ (List.replicate (N - 1) v).flatten := by
    conv_lhs => rw [show N = N - 1 + 1 by omega]
    rw [List.replicate_succ, List.flatten_cons]
  have hU2orig : (List.replicate (2 * M) w).flatten = (List.replicate (2 * N) v).flatten := by
    rw [Nat.two_mul, List.replicate_add, List.flatten_append, h,
      Nat.two_mul, List.replicate_add, List.flatten_append]
  have hU_eq : U = (List.replicate M w).flatten ++ (List.replicate M w).flatten := by
    rw [hU, Nat.two_mul, List.replicate_add, List.flatten_append]
  have hU2 : U = (List.replicate N v).flatten ++ (List.replicate N v).flatten := by
    rw [hU, hU2orig, Nat.two_mul, List.replicate_add, List.flatten_append]
  have hper_p : U.HasPeriod w.length := by
    rw [hU]; exact hasPeriod_flatten_replicate (by omega)
  have hper_q : U.HasPeriod v.length := by
    rw [hU, hU2orig]; exact hasPeriod_flatten_replicate (by omega)
  have hlenU : U.length = 2 * (List.replicate M w).flatten.length := by
    rw [hU_eq, List.length_append, Nat.two_mul]
  have hlenU2 : U.length = 2 * (List.replicate N v).flatten.length := by
    rw [hU2, List.length_append, Nat.two_mul]
  have hWlen : w.length ≤ (List.replicate M w).flatten.length := by
    rw [hW, List.length_append]; omega
  have hVlen : v.length ≤ (List.replicate N v).flatten.length := by
    rw [hV, List.length_append]; omega
  have hpU : 2 * w.length ≤ U.length := by rw [hlenU]; omega
  have hqU : 2 * v.length ≤ U.length := by rw [hlenU2]; omega
  have hfine : w.length + v.length - d ≤ U.length := by omega
  have hper_d : U.HasPeriod d := List.HasPeriod.gcd hper_p hper_q hfine
  have hUp : w.length ≤ U.length := by omega
  have hUq : v.length ≤ U.length := by omega
  have hwU : U.take w.length = w := by
    rw [hU_eq, hW, List.append_assoc, List.take_left]
  have hvU : U.take v.length = v := by
    rw [hU2, hV, List.append_assoc, List.take_left]
  have hpd : w.length / d * d = w.length := Nat.div_mul_cancel hdp
  have hqd : v.length / d * d = v.length := Nat.div_mul_cancel hdq
  have hwz' : U.take w.length = (List.replicate (w.length / d) (U.take d)).flatten := by
    have h1 := take_eq_flatten_replicate_of_hasPeriod hper_d (w.length / d)
      (by rw [hpd]; exact hUp)
    rwa [hpd] at h1
  have hvz' : U.take v.length = (List.replicate (v.length / d) (U.take d)).flatten := by
    have h1 := take_eq_flatten_replicate_of_hasPeriod hper_d (v.length / d)
      (by rw [hqd]; exact hUq)
    rwa [hqd] at h1
  have hwz : w = (List.replicate (w.length / d) (U.take d)).flatten := hwU.symm.trans hwz'
  have hvz : v = (List.replicate (v.length / d) (U.take d)).flatten := hvU.symm.trans hvz'
  rw [hwz, hvz, ← List.flatten_append, ← List.flatten_append, ← List.replicate_add,
    ← List.replicate_add, Nat.add_comm (w.length / d) (v.length / d)]

end D5.S1.Words.Powers.CommonPositivePowers
