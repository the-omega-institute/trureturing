/- GID: D5/S1/Deficit/Displacement/GeometricGapTailBound
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: For any R with Ring R, PartialOrder R, and IsStrictOrderedRing R, hypotheses 0 < r and r ^ 2 + r = 1 imply: if (a :: l).Pairwise (fun x y => y + 2 <= x) and every k in a :: l satisfies d + 1 <= k, then ((a :: l).map (fun k => r ^ k)).sum <= r ^ d - r ^ (a + 1); if l.Pairwise (fun x y => y + 2 <= x) and every k in l satisfies d + 1 <= k, then (l.map (fun k => r ^ k)).sum < r ^ d; the private recurrence over a ring assumes r ^ 2 + r = 1 and the positive-index condition 1 <= a. -/

import Mathlib

/- Provenance: Native proof over pinned mathlib. -/

/-!
Search receipt.

Provenance of this receipt: the implementing worker produced the Lean code but no
receipt, and was unavailable when that omission was found. Every search and every
coordinate recorded below was therefore run and read by the orchestrator, not by
the implementer. Treat it as an orchestrator attestation, not as the worker's
own record.

Candidates INSPECTED (pinned mathlib `fabf563a`, pinned Batteries, pinned Lean
core `v4.31.0`):
* Searched `Mathlib/Analysis/SpecificLimits/` and `Mathlib/Algebra/Order/` for a
  geometric bound over a gap-separated index list. No hit. The nearest family is
  `Mathlib/Analysis/SpecificLimits/Basic.lean:329`, `tsum_geometric_of_lt_one`,
  which sums the dense series over all of `ℕ` and does not bound a sparse
  sublist.
* Searched all of `Mathlib` for the recurrence shape `r ^ a + r ^ (a + 1) =
  r ^ (a - 1)` under `r ^ 2 + r = 1`, by name and by shape. No hit.
* `Mathlib/Algebra/Order/Ring/Defs.lean:131` declares
  `class IsStrictOrderedRing (R : Type*) [Semiring R] [PartialOrder R]`, which is
  why the public theorems ask for `[PartialOrder R]` and not `[LinearOrder R]`.

Repository state. In this checkout three frozen modules each carry the same
three-lemma group as `private` declarations over `ℝ`:
`D5/S1/Words/ZeckendorfBeattyBridge.lean`,
`D5/S1/Words/Powers/GoldenCubePeriodsSupport.lean`, and
`D5/S1/Deficit/ZeckendorfDisplacementReading.lean`. A fourth,
`D5/S1/Deficit/Displacement/ZeckendorfNormSign.lean`, carries the same group on
`origin/dev` but is absent from this checkout, whose working tree is 2478
commits behind. The distinction this file draws is not that no candidate states
the bound -- all of those private copies state it for arbitrary real `r` -- but
that none states it publicly and none states it over a type parameter.

Why the recurrence stays private. `D5/S1/Deficit/Displacement/GoldenInverseRecurrence`
already publishes the frozen theorem `inv_goldenRatio_pow_add_pow_succ`, which is
this recurrence at `r = Real.goldenRatio⁻¹`. Every consuming module instantiates
at exactly that value; `D5/S1/Words/Powers/GoldenCubePeriodsSupport.lean:112`
passes `inv_golden_sq_add_inv_golden` directly. Under the repository rule that a
stronger variant does not excuse a duplicate, publishing the generic recurrence
would be gold-plating, since no named consumer needs general `r`. It is kept
`private` here only because the two published proofs need it at general `r`.

Lemmas the proofs ACTUALLY USE: `pow_pos`, `lt_add_of_pos_left`,
`pow_le_pow_of_le_one`, `le_sub_iff_add_le`, `add_le_add_right`,
`sub_le_sub_left`, `sub_lt_self`, `List.pairwise_cons`, and the private
`pow_add_pow_succ` below. `mul_add`, `add_comm`, `mul_one`, `ring`, `abel`,
`omega`, `push_cast` and the `conv` rewrites are bookkeeping, not substantive
steps.

Article 11 screen. After stripping every rewrite, `simp`, and bookkeeping step,
`sum_powers_le_sub_head` retains substantive reasoning in both branches (the
head bound against the recurrence in `nil`, and the index-shifted combination
against the induction hypothesis in `cons`); `sum_powers_lt` retains one
substantive step, `sub_lt_self` applied to that head bound. Neither published
theorem is a zero-step wrapper of a pinned lemma.

Address and generality. Of the buckets holding private copies, only
`Deficit/Displacement` was below the split threshold, so it is the admissible
address rather than a thematic one; it does already host a `generality: G`
module. The `G` tag follows from the module importing only `Mathlib` and from
its theorems being stated over an arbitrary ring rather than over `ℝ` or the
golden ratio.

This list of inspected candidates is not claimed to be exhaustive.
-/

namespace D5.S1.Deficit.Displacement.GeometricGapTailBound

private theorem pow_add_pow_succ {R : Type*} [Ring R] {r : R}
    (hr : r ^ 2 + r = 1) {a : Nat} (ha : 1 <= a) :
    r ^ a + r ^ (a + 1) = r ^ (a - 1) := by
  conv_lhs =>
    lhs
    rw [show a = a - 1 + 1 by omega, pow_succ]
  conv_lhs =>
    rhs
    rw [show a + 1 = (a - 1) + 2 by omega, pow_add]
  calc
    r ^ (a - 1) * r + r ^ (a - 1) * r ^ 2 =
        r ^ (a - 1) * (r ^ 2 + r) := by
      rw [mul_add, add_comm]
    _ = r ^ (a - 1) := by
      rw [hr, mul_one]

theorem sum_powers_le_sub_head {R : Type*} [Ring R] [PartialOrder R]
    [IsStrictOrderedRing R] {r : R} (hr0 : 0 < r) (hr : r ^ 2 + r = 1)
    {d a : Nat} {l : List Nat}
    (hgap : (a :: l).Pairwise fun x y => y + 2 <= x)
    (hmin : ∀ k ∈ a :: l, d + 1 <= k) :
    ((a :: l).map fun k => r ^ k).sum <= r ^ d - r ^ (a + 1) := by
  have hr1 : r < 1 := by
    calc
      r < r ^ 2 + r := lt_add_of_pos_left r (pow_pos hr0 2)
      _ = 1 := hr
  induction l generalizing a with
  | nil =>
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [le_sub_iff_add_le, pow_add_pow_succ hr (by
        have := hmin a (by simp)
        omega)]
      apply pow_le_pow_of_le_one hr0.le hr1.le
      have := hmin a (by simp)
      omega
  | cons b l ih =>
      rw [List.pairwise_cons] at hgap
      have hab : b + 2 <= a := hgap.1 b (by simp)
      have htail : (b :: l).Pairwise fun x y => y + 2 <= x := hgap.2
      have hmin_tail : ∀ k ∈ b :: l, d + 1 <= k := by
        intro k hk
        exact hmin k (by simp [hk])
      have hih := ih htail hmin_tail
      simp only [List.map_cons, List.sum_cons]
      calc
        r ^ a + (r ^ b + (l.map fun k => r ^ k).sum) <=
            r ^ a + (r ^ d - r ^ (b + 1)) := by
          exact add_le_add_right (by
            simpa only [List.map_cons, List.sum_cons] using hih) _
        _ <= r ^ a + (r ^ d - (r ^ a + r ^ (a + 1))) := by
          apply add_le_add_right
          apply sub_le_sub_left
          rw [pow_add_pow_succ hr (by omega)]
          apply pow_le_pow_of_le_one hr0.le hr1.le
          omega
        _ = r ^ d - r ^ (a + 1) := by
          abel

theorem sum_powers_lt {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
    {r : R} (hr0 : 0 < r) (hr : r ^ 2 + r = 1) {d : Nat} {l : List Nat}
    (hgap : l.Pairwise fun x y => y + 2 <= x)
    (hmin : ∀ k ∈ l, d + 1 <= k) :
    (l.map fun k => r ^ k).sum < r ^ d := by
  cases l with
  | nil => simpa using pow_pos hr0 d
  | cons a l =>
      refine (sum_powers_le_sub_head hr0 hr hgap hmin).trans_lt ?_
      exact sub_lt_self _ (pow_pos hr0 (a + 1))

#print axioms sum_powers_le_sub_head
#print axioms sum_powers_lt

end D5.S1.Deficit.Displacement.GeometricGapTailBound
