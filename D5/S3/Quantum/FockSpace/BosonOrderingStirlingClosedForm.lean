/- GID: D5/S3/Quantum/FockSpace/BosonOrderingStirlingClosedForm
   generality: G
   mirror-B: D5/B/S3/Quantum/FockSpace/BosonOrderingStirlingClosedForm
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Proves Conjecture 5.3 of Maier, arXiv:2308.10332v4: for all r in Z, the generalized Stirling numbers S^_{n,k}(-1,2;r) behind boson operator ordering equal sum_j C(n-j, n-k) n! C(n+1, 2j+r-1) with the generalized binomial coefficient. -/

/-
proof_shape: result: content
escape_witness: form (2), the public conclusion `result` itself: both sides satisfy the difference
  recursion in k (`shatK`, `BK`) and, at k = 0, the first-order recursion in r (`ascDiff`, `BR0`);
  the k = 0 case is proved by induction on n with an integer induction in r from the anchor r = 1
  (`mainK0`), and the general case by induction on k (`mainAll`)
admission_basis: open-problem-resolution (issue #10170)
Direct frozen dependencies: D5/S0/Conventions/IntegerIndexBinomial (`binom`, the shared integer-lower-index
  binomial coefficient, moved there from D5/S0/Certificates/ShankarQStieltjesRefutation)
-/

import D5.S0.Conventions.IntegerIndexBinomial
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Int.Interval
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm

open Polynomial Finset
open D5.S0.Conventions.IntegerIndexBinomial (binom)

/-!
Maier, *Boson Operator Ordering Identities from Generalized Stirling and Eulerian Numbers*,
arXiv:2308.10332v4, §4–§5. The numbers `Ŝ_{n,k}(α, β; r)`, `0 ≤ k ≤ n`, are the coefficients in
`(βx + r)^{n, α} = Σ_k Ŝ_{n,k}(α, β; r) C(x, k)`, where `(y)^{n, α} = y (y - α) ⋯ (y - (n - 1) α)`;
Theorem 4.1 gives `Ŝ_{n,k} = Σ_{x ≤ k} (-1)^{k - x} C(k, x) (βx + r)^{n, α}`. For `α = -1`, `β = 2`
the factorial is rising. Conjecture 5.3: for all `r ∈ ℤ`,
`Ŝ_{n,k}(-1, 2; r) = Σ_{j = ⌊(2 - r)/2⌋}^{⌊(n + 2 - r)/2⌋} C(n - j, n - k) n! C(n + 1, 2j + r - 1)`,
where the upper argument `n - j` of the first binomial coefficient may be negative, so that it is
the generalized binomial coefficient.
-/

/-- `Ŝ_{n,k}(-1, 2; r)` by Theorem 4.1: `Σ_{x ≤ k} (-1)^{k - x} C(k, x) (2x + r)(2x + r + 1) ⋯
(2x + r + n - 1)`. -/
noncomputable def stirlingHat (n k : ℕ) (r : ℤ) : ℤ :=
  ∑ x ∈ range (k + 1), (-1) ^ (k - x) * (k.choose x : ℤ) *
    (ascPochhammer ℤ n).eval (2 * (x : ℤ) + r)

/-- The right side of Conjecture 5.3, with the generalized binomial coefficient `Ring.choose`. -/
def conjectureSum (n k : ℕ) (r : ℤ) : ℤ :=
  ∑ j ∈ Icc ((2 - r) / 2) (((n : ℤ) + 2 - r) / 2),
    Ring.choose ((n : ℤ) - j) (n - k) * (n.factorial : ℤ) *
      ((n + 1).choose (2 * j + r - 1).toNat : ℤ)

/-- Conjecture 5.3 of arXiv:2308.10332v4, for all `0 ≤ k ≤ n` and `r ∈ ℤ`. -/
def claim : Prop :=
  ∀ n k : ℕ, k ≤ n → ∀ r : ℤ, stirlingHat n k r = conjectureSum n k r

/-- The summand `C(n - j, n - k) C(n + 1, 2j + r - 1)` over all integers `j`. -/
private noncomputable def fB (n k : ℕ) (r j : ℤ) : ℤ :=
  Ring.choose ((n : ℤ) - j) (n - k) * binom (n + 1) (2 * j + r - 1)

/-- The finite sum over all integers `j` of the summand. -/
private noncomputable def B (n k : ℕ) (r : ℤ) : ℤ := ∑ᶠ j : ℤ, fB n k r j

/-- Both sides satisfy `f(k + 1, r) = f(k, r + 2) - f(k, r)` for `k < n`, and at `k = 0` both
satisfy `f_{n+1}(r) - f_{n+1}(r - 1) = (n + 1) f_n(r)` up to the factor `n!`, with the common
value `n!` at `r = 1`; induction on `n`, on `r` and then on `k` identifies them. -/
theorem result : claim := by
  have hbinom : ∀ (a : ℕ) (m : ℤ), binom a m = if 0 ≤ m then (a.choose m.toNat : ℤ) else 0 := by
    intro a m
    unfold binom
    split_ifs <;> first | rfl | omega
  have shatK : ∀ (n k : ℕ) (r : ℤ),
      stirlingHat n (k + 1) r = stirlingHat n k (r + 2) - stirlingHat n k r := by
    intro n k r
    let g : ℤ → ℤ := fun x => (ascPochhammer ℤ n).eval (2 * x + r)
    have hs : ∀ (m : ℕ) (y : ℤ), (fwdDiff 1)^[m] g y =
        ∑ x ∈ range (m + 1), (-1) ^ (m - x) * (m.choose x : ℤ) * g (y + x) := by
      intro m y
      rw [fwdDiff_iter_eq_sum_shift]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp
    have h0 : ∀ m, stirlingHat n m r = (fwdDiff 1)^[m] g 0 := by
      intro m; rw [hs]; simp [stirlingHat, g]
    have h1 : stirlingHat n k (r + 2) = (fwdDiff 1)^[k] g 1 := by
      rw [hs]; simp only [stirlingHat, g]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring_nf
    rw [h0, h0, h1, Function.iterate_succ_apply', fwdDiff]
    simp
  have shat0 : ∀ (n : ℕ) (r : ℤ),
      stirlingHat n 0 r = (ascPochhammer ℤ n).eval r := by
    intro n r
    simp [stirlingHat]
  have ascDiff : ∀ (n : ℕ) (r : ℤ),
      (ascPochhammer ℤ (n + 1)).eval r - (ascPochhammer ℤ (n + 1)).eval (r - 1) =
    (n + 1 : ℤ) * (ascPochhammer ℤ n).eval r := by
    intro n r
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_left, eval_mul, eval_X, eval_comp, eval_add,
      eval_X, eval_one, sub_add_cancel]
    ring
  have binom_succ : ∀ (a : ℕ) (m : ℤ),
      binom (a + 1) m = binom a m + binom a (m - 1) := by
    intro a m
    simp only [hbinom]
    rcases lt_trichotomy m 0 with hm | rfl | hm
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp
    · simp
    · obtain ⟨t, rfl⟩ : ∃ t : ℕ, m = (t : ℤ) + 1 := ⟨(m - 1).toNat, by omega⟩
      rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
      rw [show ((t : ℤ) + 1).toNat = t + 1 by omega, show ((t : ℤ) + 1 - 1).toNat = t by omega,
        Nat.choose_succ_succ']
      push_cast; ring
  have binom_ne : ∀ (a : ℕ) (m : ℤ) (h : binom a m ≠ 0),
      0 ≤ m ∧ m ≤ a := by
    intro a m h
    rw [hbinom] at h
    split_ifs at h with hm
    · refine ⟨hm, ?_⟩
      by_contra hc
      exact h (by rw [Nat.choose_eq_zero_of_lt (by omega)]; simp)
    · exact absurd rfl h
  have fB_supp : ∀ (n k : ℕ) (r : ℤ),
      Function.support (fB n k r) ⊆ ↑(Icc ((2 - r) / 2) (((n : ℤ) + 2 - r) / 2)) := by
    intro n k r j hj
    have h : binom (n + 1) (2 * j + r - 1) ≠ 0 := by
      intro h0; exact hj (by simp [fB, h0])
    obtain ⟨h1, h2⟩ := binom_ne _ _ h
    simp only [coe_Icc, Set.mem_Icc]
    push_cast at h2
    omega
  have rhs_eq : ∀ (n k : ℕ) (r : ℤ),
      conjectureSum n k r = (n.factorial : ℤ) * B n k r := by
    intro n k r
    rw [B, finsum_eq_sum_of_support_subset _ (fB_supp n k r), Finset.mul_sum, conjectureSum]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [Finset.mem_Icc] at hj
    simp only [fB, hbinom, if_pos (show (0 : ℤ) ≤ 2 * j + r - 1 by omega)]
    ring
  have supp_binom : ∀ (n : ℕ) (r : ℤ) (c : ℤ → ℤ),
      (Function.support fun j : ℤ => c j * binom (n + 1) (2 * j + r - 1)).Finite := by
    intro n r c
    refine (Finset.finite_toSet (Icc ((2 - r) / 2) (((n : ℤ) + 2 - r) / 2))).subset ?_
    intro j hj
    have h : binom (n + 1) (2 * j + r - 1) ≠ 0 := by
      intro h0; exact hj (by simp [h0])
    obtain ⟨h1, h2⟩ := binom_ne _ _ h
    simp only [coe_Icc, Set.mem_Icc]
    push_cast at h2
    omega
  have BK : ∀ (n k : ℕ) (hk : k + 1 ≤ n) (r : ℤ),
      B n (k + 1) r = B n k (r + 2) - B n k r := by
    intro n k hk r
    have hs : B n k (r + 2) =
        ∑ᶠ j : ℤ, Ring.choose ((n : ℤ) - j + 1) (n - k) * binom (n + 1) (2 * j + r - 1) := by
      rw [B, ← finsum_comp_equiv (Equiv.subRight (1 : ℤ))]
      refine finsum_congr fun j => ?_
      simp only [fB, Equiv.subRight_apply]
      congr 2 <;> ring
    rw [hs, B, B]
    simp only [fB]
    rw [← finsum_sub_distrib (supp_binom n r _) (supp_binom n r _)]
    refine finsum_congr fun j => ?_
    have hnk : n - k = (n - (k + 1)) + 1 := by omega
    rw [hnk, Ring.choose_succ_succ]
    ring
  have BR0 : ∀ (n : ℕ) (r : ℤ),
      B (n + 1) 0 r - B (n + 1) 0 (r - 1) = B n 0 r := by
    intro n r
    have e1 : ∀ t : ℤ, B (n + 1) 0 t =
        ∑ᶠ j : ℤ, (Ring.choose ((n : ℤ) + 1 - j) (n + 1) * binom (n + 1) (2 * j + t - 1) +
          Ring.choose ((n : ℤ) + 1 - j) (n + 1) * binom (n + 1) (2 * j + (t - 1) - 1)) := by
      intro t
      rw [B]
      refine finsum_congr fun j => ?_
      simp only [fB, Nat.sub_zero]
      rw [show n + 1 + 1 = (n + 1) + 1 from rfl, binom_succ]
      push_cast
      rw [show 2 * j + t - 1 - 1 = 2 * j + (t - 1) - 1 by ring]
      ring
    rw [e1, e1, finsum_add_distrib (supp_binom n r _) (supp_binom n (r - 1) _),
      finsum_add_distrib (supp_binom n (r - 1) _) (supp_binom n (r - 1 - 1) _)]
    have hshift :
        ∑ᶠ j : ℤ, Ring.choose ((n : ℤ) + 1 - j) (n + 1) * binom (n + 1) (2 * j + (r - 1 - 1) - 1) =
        ∑ᶠ j : ℤ, Ring.choose ((n : ℤ) - j) (n + 1) * binom (n + 1) (2 * j + r - 1) := by
      rw [← finsum_comp_equiv (Equiv.addRight (1 : ℤ))]
      refine finsum_congr fun j => ?_
      simp only [Equiv.coe_addRight]
      congr 2 <;> ring
    rw [hshift, B]
    simp only [fB, Nat.sub_zero]
    rw [show ∀ a b c : ℤ, a + b - (b + c) = a - c from fun a b c => by ring,
      ← finsum_sub_distrib (supp_binom n r _) (supp_binom n r _)]
    refine finsum_congr fun j => ?_
    rw [show (n : ℤ) + 1 - j = ((n : ℤ) - j) + 1 by ring, Ring.choose_succ_succ]
    ring
  have Banchor : ∀ (n : ℕ),
      B n 0 1 = 1 := by
    intro n
    rw [B, finsum_eq_single _ 0]
    · simp [fB, hbinom, Ring.choose_natCast]
    · intro j hj
      simp only [fB, Nat.sub_zero]
      rcases lt_or_gt_of_ne hj with hneg | hpos
      · have hn : ¬ (0 : ℤ) ≤ 2 * j + 1 - 1 := by omega
        simp only [hbinom, if_neg hn, mul_zero]
      · by_cases hjn : j ≤ n
        · have : (n : ℤ) - j = ((n - j.toNat : ℕ) : ℤ) := by omega
          rw [this, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega)]
          simp
        · have hc : binom (n + 1) (2 * j + 1 - 1) = 0 := by
            simp only [hbinom, if_pos (show (0 : ℤ) ≤ 2 * j + 1 - 1 by omega)]
            rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
          rw [hc, mul_zero]
  have B00 : ∀ (r : ℤ),
      B 0 0 r = 1 := by
    intro r
    rw [B, finsum_eq_single _ ((2 - r) / 2)]
    · simp only [fB, Nat.sub_zero, Ring.choose_zero_right, one_mul, hbinom]
      rw [if_pos (by omega)]
      have : (2 * ((2 - r) / 2) + r - 1).toNat ≤ 1 := by omega
      interval_cases h : (2 * ((2 - r) / 2) + r - 1).toNat <;> simp
    · intro j hj
      simp only [fB, Nat.sub_zero, Ring.choose_zero_right, one_mul, hbinom]
      split_ifs with h
      · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
      · rfl
  have mainK0 : ∀ (n : ℕ) (r : ℤ),
      (ascPochhammer ℤ n).eval r = (n.factorial : ℤ) * B n 0 r := by
    intro n r
    induction n generalizing r with
    | zero => simp [B00]
    | succ n ih =>
      let D : ℤ → ℤ := fun t =>
        (ascPochhammer ℤ (n + 1)).eval t - ((n + 1).factorial : ℤ) * B (n + 1) 0 t
      have hstep : ∀ t, D t = D (t - 1) := by
        intro t
        have h1 := ascDiff n t
        have h2 := BR0 n t
        have h3 := ih t
        simp only [D]
        rw [Nat.factorial_succ]
        push_cast at h1 h2 h3 ⊢
        linear_combination h1 - (↑n + 1) * ↑n.factorial * h2 + (↑n + 1) * h3
      have hD1 : D 1 = 0 := by
        simp only [D, ascPochhammer_eval_one, Banchor]; ring
      have hall : ∀ t, D t = 0 := by
        intro t
        induction t using Int.inductionOn' (b := 1) with
        | zero => exact hD1
        | succ t _ ht => rw [hstep (t + 1), add_sub_cancel_right, ht]
        | pred t _ ht => rw [← ht, hstep t]
      have := hall r
      simp only [D] at this
      linarith
  have mainAll : ∀ (n : ℕ),
      ∀ k, k ≤ n → ∀ r : ℤ, stirlingHat n k r = (n.factorial : ℤ) * B n k r := by
    intro n k
    induction k with
    | zero => intro _ r; rw [shat0, mainK0]
    | succ k ih =>
      intro hk r
      rw [shatK, ih (by omega), ih (by omega), BK n k hk]
      ring
  intro n k hk r
  rw [rhs_eq, mainAll n k hk r]

#print axioms claim
#print axioms result

end D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm
