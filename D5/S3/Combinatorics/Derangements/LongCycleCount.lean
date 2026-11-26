/- GID: D5/S3/Combinatorics/Derangements/LongCycleCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Derangements/LongCycleCount
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: [mathlib/module/Mathlib.GroupTheory.Perm.Centralizer]
   utility: none
   digest: For 2k > n, derangements with a k-cycle number C(n,k)(k-1)! D_(n-k). -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#221)
escape_witness: excluded_mul (summing over cycle types, the derangements with a k-cycle times
  k (n-k)! equal n! D_(n-k)), with term_mul (the class-size identity for k ::ₘ m' and m').
proof_shape:
  cnt: definition; consumers: term_mul, excluded_mul.
  term_mul, excluded_mul: content; consumers: excluded_mul, long_cycle.
  mem_D_iff: bind-only helper (TerminalDifference.noFixed_iff_sum); consumer: excluded_mul.
  long_cycle: content via excluded_mul.
Direct frozen dependencies: D5/S3/Combinatorics/Derangements/TerminalDifference (D, T, excluded,
  T_add_excluded, noFixed_iff_sum; statement_id
  sha256:30f6c3f4b3ec92fcc35b679f227332f248b5fb2e951966e3a6170f421fb9f74d).
utility: none (a general count theorem; no enumeration, checker, reduction or certified
  instance).
Search record (§3.1): TerminalDifference proves only the cases k = n and k = n - 2 (n >= 5);
  Mathlib's Perm.card_of_cycleType_mul_eq and Perm.exists_with_cycleType_iff are reused; no
  frozen module counts derangements with a prescribed long cycle. Kallat's ancillary sources
  treat only the column cases and are not used.
-/

import D5.S3.Combinatorics.Derangements.TerminalDifference

/-! # Derangements with a unique long cycle

For `2 ≤ k ≤ n` with `2k > n`, a derangement of `n` labels has at most one `k`-cycle, and the
derangements with a `k`-cycle number `C(n,k) (k-1)! D_(n-k)`. Equivalently
`D_n - T(n,k) = n! D_(n-k) / (k (n-k)!)`, where `T(n,k)` counts the derangements without a
`k`-cycle. The count is read off the cycle types: the cycle types with a part `k` are exactly
`k ::ₘ m'` for the cycle types `m'` of derangements of `n - k` labels, and the class sizes
satisfy `#(k ::ₘ m') · k (n-k)! = n! · #m'`.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Derangements.LongCycleCount

open Equiv Finset
open D5.S3.Combinatorics.Derangements.TerminalDifference

noncomputable section

/-- The number of permutations of `Fin N` with cycle type `m`. -/
private def cnt (N : ℕ) (m : Multiset ℕ) : ℕ :=
  #({g | g.cycleType = m} : Finset (Perm (Fin N)))

/-- The class sizes of `k ::ₘ m'` on `n` labels and of `m'` on `n - k` labels, for a derangement
type `m'` of `n - k` labels with all parts below `k`. -/
private lemma term_mul (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) (m' : Multiset ℕ)
    (hsum : m'.sum = n - k) (hge : ∀ a ∈ m', 2 ≤ a) (hlt : ∀ a ∈ m', a < k) :
    cnt n (k ::ₘ m') * (k * (n - k).factorial) = n.factorial * cnt (n - k) m' := by
  have hA := Perm.card_of_cycleType_mul_eq (α := Fin n) (k ::ₘ m')
  have hB := Perm.card_of_cycleType_mul_eq (α := Fin (n - k)) m'
  simp only [Fintype.card_fin, Multiset.sum_cons, hsum] at hA hB
  have hcA : k + (n - k) ≤ n ∧ ∀ a ∈ k ::ₘ m', 2 ≤ a := ⟨by omega, fun a ha => by
    rcases Multiset.mem_cons.mp ha with rfl | ha
    · exact hk
    · exact hge a ha⟩
  have hcB : n - k ≤ n - k ∧ ∀ a ∈ m', 2 ≤ a := ⟨le_rfl, hge⟩
  rw [ite_eq_left_of_eq_true _ _ (eq_true hcA)] at hA
  rw [ite_eq_left_of_eq_true _ _ (eq_true hcB)] at hB
  have hkm : k ∉ m' := fun h => (lt_irrefl k) (hlt k h)
  have hprod : ∏ c ∈ (k ::ₘ m').toFinset, ((k ::ₘ m').count c).factorial =
      ∏ c ∈ m'.toFinset, (m'.count c).factorial := by
    rw [Multiset.toFinset_cons, Finset.prod_insert (by simpa using hkm),
      Multiset.count_cons_self, Multiset.count_eq_zero_of_notMem hkm, zero_add,
      Nat.factorial_one, one_mul]
    apply Finset.prod_congr rfl
    intro c hc
    rw [Multiset.count_cons_of_ne]
    rintro rfl
    exact hkm (Multiset.mem_toFinset.mp hc)
  rw [hprod, Multiset.prod_cons, show n - (k + (n - k)) = 0 by omega, Nat.factorial_zero,
    one_mul] at hA
  rw [Nat.sub_self, Nat.factorial_zero, one_mul] at hB
  unfold cnt
  set P := m'.prod * ∏ c ∈ m'.toFinset, (m'.count c).factorial
  have hA' : #({g | g.cycleType = k ::ₘ m'} : Finset (Perm (Fin n))) * (k * P) =
      n.factorial := by rw [← hA]; ring
  rw [← hB, ← hA']
  ring

/-- The cycle types of derangements of `N` labels: multisets with parts at least two and sum
`N`. -/
private lemma mem_D_iff (N : ℕ) (p : Perm (Fin N)) : p ∈ D N ↔ p.cycleType.sum = N := by
  classical
  simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
  exact noFixed_iff_sum p

/-- Fiberwise over the cycle type, `excluded n k` times `k (n-k)!` is `n! D_(n-k)`. -/
private lemma excluded_mul (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) (h2 : n < 2 * k) :
    (excluded n k).card * (k * (n - k).factorial) = n.factorial * (D (n - k)).card := by
  classical
  have hex : ∀ p : Perm (Fin n), p ∈ excluded n k ↔ p.cycleType.sum = n ∧ k ∈ p.cycleType := by
    intro p
    simp only [excluded, Finset.mem_filter, ← mem_D_iff]
  rw [Finset.card_eq_sum_card_image Perm.cycleType (excluded n k),
    Finset.card_eq_sum_card_image Perm.cycleType (D (n - k)), Finset.sum_mul, Finset.mul_sum]
  symm
  refine Finset.sum_nbij' (fun m' => k ::ₘ m') (fun m => m.erase k) ?_ ?_ ?_ ?_ ?_
  · intro m' hm'
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hm'
    rw [Finset.mem_image]
    have hsum := (mem_D_iff (n - k) q).mp hq
    have hv : (k ::ₘ q.cycleType).sum ≤ Fintype.card (Fin n) ∧
        ∀ a ∈ k ::ₘ q.cycleType, 2 ≤ a := by
      refine ⟨by rw [Multiset.sum_cons, hsum, Fintype.card_fin]; omega, fun a ha => ?_⟩
      rcases Multiset.mem_cons.mp ha with rfl | ha
      · exact hk
      · exact Perm.two_le_of_mem_cycleType ha
    obtain ⟨p, hp⟩ := (Perm.exists_with_cycleType_iff (Fin n)).mpr hv
    refine ⟨p, (hex p).mpr ⟨?_, ?_⟩, hp⟩
    · rw [hp, Multiset.sum_cons, hsum]; omega
    · rw [hp]; exact Multiset.mem_cons_self k _
  · intro m hm
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hsum, hkm⟩ := (hex p).mp hp
    rw [Finset.mem_image]
    have he := Multiset.cons_erase hkm
    have hsum' : (p.cycleType.erase k).sum = n - k := by
      have := congrArg Multiset.sum he
      rw [Multiset.sum_cons] at this
      omega
    have hv : (p.cycleType.erase k).sum ≤ Fintype.card (Fin (n - k)) ∧
        ∀ a ∈ p.cycleType.erase k, 2 ≤ a :=
      ⟨by rw [hsum', Fintype.card_fin],
        fun a ha => Perm.two_le_of_mem_cycleType (Multiset.mem_of_mem_erase ha)⟩
    obtain ⟨q, hq⟩ := (Perm.exists_with_cycleType_iff (Fin (n - k))).mpr hv
    exact ⟨q, (mem_D_iff _ q).mpr (by rw [hq, hsum']), hq⟩
  · intro m' _
    exact Multiset.erase_cons_head k m'
  · intro m hm
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
    exact Multiset.cons_erase ((hex p).mp hp).2
  · intro m' hm'
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hm'
    have hsum := (mem_D_iff (n - k) q).mp hq
    have hfibE : #{p ∈ excluded n k | p.cycleType = k ::ₘ q.cycleType} =
        cnt n (k ::ₘ q.cycleType) := by
      unfold cnt
      congr 1
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hex]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨⟨?_, ?_⟩, h⟩
        · rw [h, Multiset.sum_cons, hsum]; omega
        · rw [h]; exact Multiset.mem_cons_self k _
    have hfibD : #{p ∈ D (n - k) | p.cycleType = q.cycleType} = cnt (n - k) q.cycleType := by
      unfold cnt
      congr 1
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_D_iff]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨by rw [h, hsum], h⟩
    rw [hfibE, hfibD]
    exact (term_mul n k hk hkn q.cycleType hsum (fun a ha => Perm.two_le_of_mem_cycleType ha)
      (fun a ha => by
        have := Multiset.le_sum_of_mem ha
        omega)).symm

/-- For `2 ≤ k ≤ n` with `2k > n`, the derangements of `n` labels with a `k`-cycle number
`C(n,k) (k-1)! D_(n-k)`, so `D_n - T(n,k) = C(n,k) (k-1)! D_(n-k) = n! D_(n-k) / (k (n-k)!)`;
here `D_0 = 1` and `D_1 = 0`. -/
theorem long_cycle (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) (h2 : n < 2 * k) :
    T n k + n.choose k * (k - 1).factorial * (D (n - k)).card = (D n).card ∧
    ((D n).card : ℤ) - T n k = (n.choose k * (k - 1).factorial * (D (n - k)).card : ℕ) ∧
    ((D n).card : ℚ) - T n k =
      (n.factorial : ℚ) * (D (n - k)).card / (k * (n - k).factorial) := by
  have hm := excluded_mul n k hk hkn h2
  have hsplit := T_add_excluded n k
  have hfact : n.factorial = n.choose k * (k - 1).factorial * (k * (n - k).factorial) := by
    rw [← Nat.choose_mul_factorial_mul_factorial hkn]
    conv_lhs => rw [show k = k - 1 + 1 by omega, Nat.factorial_succ]
    rw [show k - 1 + 1 = k by omega]
    ring
  have hpos : 0 < k * (n - k).factorial := Nat.mul_pos (by omega) (Nat.factorial_pos _)
  have hex : (excluded n k).card = n.choose k * (k - 1).factorial * (D (n - k)).card := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [hm, hfact]
    ring
  refine ⟨by rw [← hex]; exact hsplit, ?_, ?_⟩
  · rw [← hex]
    have : (T n k : ℤ) + (excluded n k).card = (D n).card := by exact_mod_cast hsplit
    linarith
  · have hQ : ((excluded n k).card : ℚ) * (k * (n - k).factorial) =
        (n.factorial : ℚ) * (D (n - k)).card := by exact_mod_cast hm
    have hsplitQ : (T n k : ℚ) + (excluded n k).card = (D n).card := by exact_mod_cast hsplit
    have hposQ : (0 : ℚ) < k * (n - k).factorial := by exact_mod_cast hpos
    have hdiff : ((D n).card : ℚ) - T n k = (excluded n k).card := by linarith
    rw [eq_div_iff hposQ.ne', ← hQ, hdiff]

end

end D5.S3.Combinatorics.Derangements.LongCycleCount
