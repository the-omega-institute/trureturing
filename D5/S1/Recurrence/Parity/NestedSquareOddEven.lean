/- GID: D5/S1/Recurrence/Parity/NestedSquareOddEven
   generality: G
   mirror-B: D5/B/S1/Recurrence/Parity/NestedSquareOddEven
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Hanna's A392210 conjecture: odd-index coefficients of the nested-square g.f. are even. -/
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
OEIS A392210 (Paul D. Hanna, 2026) has generating function
`x + sq(x/(1-x) + sq(x/(1-2x) + ...))`, equivalently `A(x) = x + A(x/(1-x))^2`, and the entry
states: "It appears that a(2*n-1) is even for n > 1."
-/

open PowerSeries

namespace D5.S1.Recurrence.Parity.NestedSquareOddEven

/-- `X / (1 - X)`, written as `X` times the all-ones series `1 + X + X^2 + ⋯`. -/
noncomputable def shift : PowerSeries ℤ := X * mk 1

/-- `A` satisfies Hanna's functional equation `A(x) = x + A(x/(1-x))^2`. -/
def IsNestedSquareGF (A : PowerSeries ℤ) : Prop :=
  A = X + (A.subst shift) ^ 2

/-- Hanna's conjecture for OEIS A392210, as a proposition. -/
def claim : Prop :=
  (∃ A : PowerSeries ℤ, IsNestedSquareGF A) ∧
    ∀ A : PowerSeries ℤ, IsNestedSquareGF A → ∀ n : ℕ, 1 < n → Even (coeff (2 * n - 1) A)

/-- The entry's coefficient recurrence `a(n) = Σ b(n-k) b(k)`, with `b` the binomial transform. -/
private noncomputable def recCoeff : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => ∑ i : Fin (n + 1),
      (∑ j : Fin (i.1 + 1), (Nat.choose i.1 j.1 : ℤ) * recCoeff (j.1 + 1)) *
        (∑ j : Fin (n + 1 - i.1), (Nat.choose (n - i.1) j.1 : ℤ) * recCoeff (j.1 + 1))
decreasing_by
  all_goals
    have := i.2
    have := j.2
    omega

/-- **Hanna's conjecture for OEIS A392210.** The functional equation has a solution, and every
solution has even coefficients at every odd index `2n - 1` with `n > 1`. -/
theorem result :
    (∃ A : PowerSeries ℤ, IsNestedSquareGF A) ∧
      ∀ A : PowerSeries ℤ, IsNestedSquareGF A → ∀ n : ℕ, 1 < n →
        Even (coeff (2 * n - 1) A) := by
  refine ⟨⟨mk recCoeff, ?_⟩, ?_⟩
  · -- The coefficients of `shift ^ (e + 1)` are binomial coefficients.
    have hpow : ∀ e m : ℕ, coeff m (shift ^ (e + 1)) =
        if e + 1 ≤ m then (Nat.choose (m - 1) e : ℤ) else 0 := by
      intro e m
      rw [shift, mul_pow, mk_one_pow_eq_mk_choose_add, coeff_X_pow_mul']
      split_ifs with h
      · rw [coeff_mk]; congr 2; omega
      · rfl
    have ha0 : recCoeff 0 = 0 := by rw [recCoeff]
    -- Substituting `shift` takes the binomial transform of the coefficients.
    have hsub : ∀ m, coeff m ((mk recCoeff).subst shift) =
        ∑ j ∈ Finset.range m, (Nat.choose (m - 1) j : ℤ) * recCoeff (j + 1) := by
      intro m
      rw [coeff_subst' (HasSubst.of_constantCoeff_zero' (by simp [shift]))]
      rw [finsum_eq_sum_of_support_subset (s := Finset.range (m + 1))]
      · rw [Finset.sum_range_succ', coeff_mk, ha0, zero_smul, add_zero]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mem_range] at hj
        rw [coeff_mk, hpow, if_pos (by omega), smul_eq_mul, mul_comm]
      · intro d hd
        simp only [Function.mem_support, ne_eq] at hd
        rw [Finset.coe_range, Set.mem_Iio]
        by_contra hlt
        apply hd
        rcases d with _ | e
        · omega
        · rw [hpow, if_neg (by omega), smul_zero]
    set b : ℕ → ℤ :=
      fun m => ∑ j ∈ Finset.range m, (Nat.choose (m - 1) j : ℤ) * recCoeff (j + 1) with hb
    have hb0 : b 0 = 0 := by simp [hb]
    have hF : ∀ m, coeff m ((mk recCoeff).subst shift) = b m := hsub
    unfold IsNestedSquareGF
    ext k
    rw [map_add, pow_two, coeff_mul, coeff_mk]
    simp_rw [hF]
    rcases k with _ | _ | n
    · simp [ha0, hb0]
    · rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp [coeff_X, hb0, recCoeff, Finset.sum_range_succ]
    · rw [coeff_X, if_neg (by omega), zero_add, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.sum_range_succ, Finset.sum_range_succ', hb0]
      simp only [zero_mul, add_zero]
      rw [show n + 1 + 1 - (n + 2) = 0 by omega, hb0, mul_zero, add_zero]
      rw [recCoeff, Fin.sum_univ_eq_sum_range (fun i =>
        (∑ j : Fin (i + 1), (Nat.choose i j.1 : ℤ) * recCoeff (j.1 + 1)) *
          (∑ j : Fin (n + 1 - i), (Nat.choose (n - i) j.1 : ℤ) * recCoeff (j.1 + 1)))]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      simp only [hb]
      rw [Fin.sum_univ_eq_sum_range (fun j => (Nat.choose i j : ℤ) * recCoeff (j + 1)),
        Fin.sum_univ_eq_sum_range (fun j => (Nat.choose (n - i) j : ℤ) * recCoeff (j + 1)),
        show n + 1 + 1 - (i + 1) = n + 1 - i by omega, show i + 1 - 1 = i by omega,
        show n + 1 - i - 1 = n - i by omega]
  · intro A hA n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega, hA, map_add, coeff_X, if_neg (by omega),
      zero_add, pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    -- The antidiagonal of an odd index pairs `(i, j)` with `(j, i)` and has no diagonal term.
    set F := A.subst shift
    set f : ℕ → ℤ := fun i => coeff i F * coeff (2 * m + 1 - i) F with hf
    change Even (∑ i ∈ Finset.range (2 * m + 1 + 1), f i)
    rw [show 2 * m + 1 + 1 = (m + 1) + (m + 1) by ring, Finset.sum_range_add]
    have hrefl : ∑ i ∈ Finset.range (m + 1), f (m + 1 + i) =
        ∑ i ∈ Finset.range (m + 1), f i := by
      rw [← Finset.sum_range_reflect f (m + 1)]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      simp only [hf]
      rw [show 2 * m + 1 - (m + 1 + i) = m + 1 - 1 - i by omega,
        show 2 * m + 1 - (m + 1 - 1 - i) = m + 1 + i by omega, mul_comm]
    rw [hrefl]
    exact ⟨_, rfl⟩

end D5.S1.Recurrence.Parity.NestedSquareOddEven
