/- GID: D5/S3/Arith/PrimitiveRoot/SievePrimeFactors
   generality: G
   mirror-B: D5/B/S3/Arith/PrimitiveRoot/SievePrimeFactors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/PrimitiveRoot/SieveThresholdExact.feasible_iff; premises=D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.reciprocal_tail_margin_five,D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.reciprocal_tail_margin_six
   digest: Ordered prime supports and uniform radical bounds. -/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.FinCases

/-! Ordered prime supports for uniform sieve parameters. -/

@[expose] public section
namespace D5.S3.Arith.PrimitiveRoot.SievePrimeFactors
open scoped BigOperators

theorem nth_prime_succ_le_of_prime {k p : Nat} (hp : Nat.Prime p)
    (h : Nat.nth Nat.Prime k < p) : Nat.nth Nat.Prime (k + 1) <= p := by
  by_contra hn
  have hp_lt : p < Nat.nth Nat.Prime (k + 1) := Nat.lt_of_not_ge hn
  exact (not_le_of_gt h) (Nat.le_nth_of_lt_nth_succ hp_lt hp)

theorem nth_prime_le_get {qs : List Nat} (hsorted : qs.SortedLT)
    (hprime : forall q, q ∈ qs -> Nat.Prime q) :
    forall i (hi : i < qs.length), Nat.nth Nat.Prime i <= qs[i] := by
  intro i
  induction i with
  | zero =>
      intro hi
      simpa using (hprime qs[0] (List.getElem_mem hi)).two_le
  | succ i ih =>
      intro hi
      have hi' : i < qs.length := by omega
      apply nth_prime_succ_le_of_prime (hprime qs[i + 1] (List.getElem_mem hi))
      exact lt_of_le_of_lt (ih hi')
        (hsorted.getElem_lt_getElem_of_lt (i := i) (j := i + 1) (by omega))

theorem nth_prime_five : Nat.nth Nat.Prime 5 = 13 := by
  have h := Nat.nth_count (p := Nat.Prime) (by decide : Nat.Prime 13)
  norm_num [Nat.count] at h
  exact h

theorem nth_prime_six : Nat.nth Nat.Prime 6 = 17 := by
  have h := Nat.nth_count (p := Nat.Prime) (by decide : Nat.Prime 17)
  norm_num [Nat.count] at h
  exact h

theorem nth_prime_seven : Nat.nth Nat.Prime 7 = 19 := by
  have h := Nat.nth_count (p := Nat.Prime) (by decide : Nat.Prime 19)
  norm_num [Nat.count] at h
  exact h

def firstEight : Fin 8 → ℕ := ![2, 3, 5, 7, 11, 13, 17, 19]

/-- A finite increasing prime sequence dominates each of the first eight prime ranks. -/
theorem prime_rank_lower {k : ℕ} (q : Fin k → ℕ) (i : Fin k)
    (hm : StrictMonoOn q (Set.Iic i)) (hp : ∀ j, j ≤ i → (q j).Prime)
    (hi : i.val < 8) :
    firstEight ⟨i.val, hi⟩ ≤ q i := by
  let f : Fin (i.val + 1) → ℕ := fun j => q ⟨j.val, by omega⟩
  have hsorted : (List.ofFn f).SortedLT := by
    apply List.sortedLT_ofFn_iff.mpr
    intro a b hab
    exact hm (by change a.val ≤ i.val; omega)
      (by change b.val ≤ i.val; omega) hab
  have hprime : ∀ p ∈ List.ofFn f, p.Prime := by
    intro p hp'
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp'
    exact hp _ (by change j.val ≤ i.val; omega)
  have h := nth_prime_le_get hsorted hprime i.val (by simp)
  have hn : ∀ j : Fin 8, Nat.nth Nat.Prime j.val = firstEight j := by
    intro j
    fin_cases j <;>
      simp [firstEight, nth_prime_five, nth_prime_six, nth_prime_seven]
  rw [hn ⟨i.val, hi⟩] at h
  simpa only [List.getElem_ofFn, f] using h

/-- The first eight members of any increasing prime sequence dominate the first eight primes. -/
theorem first_eight_le (q : Fin 8 → ℕ) (hm : StrictMono q)
    (hp : ∀ i, (q i).Prime) : ∀ i, firstEight i ≤ q i := by
  classical
  intro i
  exact prime_rank_lower q i (hm.strictMonoOn _) (fun j _ => hp j) i.isLt

/-- At least `8+m` distinct prime factors force a geometric radical lower bound. -/
theorem radical_lower (n m : ℕ) (hc : 8 + m ≤ n.primeFactors.card) :
    9699690 * 19 ^ m ≤ ∏ p ∈ n.primeFactors, p := by
  classical
  let t := n.primeFactors.card - 8
  have ht : n.primeFactors.card = 8 + t := by omega
  have hmt : m ≤ t := by omega
  let q := n.primeFactors.orderEmbOfFin ht
  have hp (i : Fin (8 + t)) : (q i).Prime :=
    Nat.prime_of_mem_primeFactors (Finset.orderEmbOfFin_mem _ ht i)
  have hfirst := first_eight_le (fun i : Fin 8 => q (i.castAdd t))
    (q.strictMono.comp (Fin.strictMono_castAdd t)) (fun i => hp (i.castAdd t))
  have htail (i : Fin t) : 19 ≤ q (Fin.natAdd 8 i) := by
    have hle : (⟨7, by omega⟩ : Fin (8 + t)) ≤ Fin.natAdd 8 i := by
      change 7 ≤ 8 + i.val
      omega
    have h := (hfirst 7).trans (q.monotone hle)
    norm_num [firstEight] at h
    omega
  calc
    9699690 * 19 ^ m ≤ 9699690 * 19 ^ t :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hmt)
    _ = (∏ i : Fin 8, firstEight i) * ∏ _i : Fin t, 19 := by
      norm_num [firstEight, Fin.prod_univ_succ]
    _ ≤ (∏ i : Fin 8, q (i.castAdd t)) * ∏ i : Fin t, q (Fin.natAdd 8 i) :=
      Nat.mul_le_mul (Finset.prod_le_prod (fun i _ => hfirst i))
        (Finset.prod_le_prod (fun i _ => htail i))
    _ = ∏ i : Fin (8 + t), q i := (Fin.prod_univ_add _).symm
    _ = ∏ p ∈ n.primeFactors, p := by
      rw [← Finset.map_orderEmbOfFin_univ n.primeFactors ht, Finset.prod_map]
      rfl

/-- The last at most six primes after a prefix of length at least two have bounded mass. -/
theorem reciprocal_tail_bound {r s : ℕ} (q : Fin (r + s) → ℕ)
    (hr : 2 ≤ r) (hs : s ≤ 6)
    (hm : StrictMonoOn q {j | j.val < s + 2})
    (hp : ∀ j, j.val < s + 2 → (q j).Prime)
    (hle : ∀ i : Fin s,
      q ⟨i.val + 2, by omega⟩ ≤ q (Fin.natAdd r i)) :
    (∑ i : Fin s, (q (Fin.natAdd r i) : ℝ)⁻¹) ≤
      ∑ i : Fin s, (firstEight ⟨i.val + 2, by omega⟩ : ℝ)⁻¹ := by
  classical
  let f : Fin s → ℝ := fun i =>
    (firstEight ⟨i.val + 2, by omega⟩ : ℝ)⁻¹
  have hpoint (i : Fin s) : (q (Fin.natAdd r i) : ℝ)⁻¹ ≤ f i := by
    let j0 : Fin (r + s) := ⟨i.val + 2, by omega⟩
    have hprefix {j : Fin (r + s)} (hj : j ≤ j0) : j.val < s + 2 := by
      change j.val ≤ i.val + 2 at hj
      omega
    have hm0 : StrictMonoOn q (Set.Iic j0) := by
      intro a ha b hb hab
      exact hm (hprefix ha) (hprefix hb) hab
    have hlow := prime_rank_lower q j0 hm0 (fun j hj => hp j (hprefix hj))
      (by change i.val + 2 < 8; omega)
    apply inv_anti₀
    · have hpos : ∀ j : Fin 8, 0 < firstEight j := by decide
      exact_mod_cast hpos ⟨i.val + 2, by omega⟩
    · exact_mod_cast hlow.trans (hle i)
  exact Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)

/-- At most five tail primes leave this uniform positive reciprocal margin. -/
theorem reciprocal_tail_margin_five {r s : ℕ} (q : Fin (r + s) → ℕ)
    (hr : 2 ≤ r) (hs : s ≤ 5)
    (hm : StrictMonoOn q {j | j.val < s + 2})
    (hp : ∀ j, j.val < s + 2 → (q j).Prime)
    (hle : ∀ i : Fin s,
      q ⟨i.val + 2, by omega⟩ ≤ q (Fin.natAdd r i)) :
    (36628 / 85085 : ℝ) ≤ 1 - ∑ i : Fin s, (q (Fin.natAdd r i) : ℝ)⁻¹ := by
  classical
  have hb := reciprocal_tail_bound q hr (by omega) hm hp hle
  have hnum : (∑ i : Fin s, (firstEight ⟨i.val + 2, by omega⟩ : ℝ)⁻¹) ≤
      48457 / 85085 := by
    interval_cases s <;> norm_num [firstEight, Fin.sum_univ_succ]
  linarith

/-- Six tail primes leave this uniform positive reciprocal margin. -/
theorem reciprocal_tail_margin_six {r : ℕ} (q : Fin (r + 6) → ℕ)
    (hr : 2 ≤ r) (hm : StrictMonoOn q {j | j.val < 8})
    (hp : ∀ j, j.val < 8 → (q j).Prime)
    (hle : ∀ i : Fin 6,
      q ⟨i.val + 2, by omega⟩ ≤ q (Fin.natAdd r i)) :
    (610847 / 1616615 : ℝ) ≤ 1 - ∑ i : Fin 6, (q (Fin.natAdd r i) : ℝ)⁻¹ := by
  classical
  have hb := reciprocal_tail_bound q hr (by omega) hm hp hle
  have hnum : (∑ i : Fin 6, (firstEight ⟨i.val + 2, by omega⟩ : ℝ)⁻¹) =
      1005768 / 1616615 := by norm_num [firstEight, Fin.sum_univ_succ]
  linarith

end D5.S3.Arith.PrimitiveRoot.SievePrimeFactors

-- The utility header grammar requires its metadata on one physical line.
set_option linter.style.longLine.maxLineLength 262
