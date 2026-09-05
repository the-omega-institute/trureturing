/- GID: D5/S3/Analytic/Boundary/LogMomentJetFromDyadicCount
   generality: G
   mirror-B: D5/B/S3/Analytic/Boundary/LogMomentJetFromDyadicCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A logarithmic dyadic counting gain yields finite lower-order boundary log moments. -/

/- Six-route duplicate and library-search audit (2026-09-04):
   * Repository keyword searches covered boundary log moments, logarithmic jets, sparse counting
     functions, dyadic shells, weighted harmonic sums, and convergence at exponent one.
   * Symbol/name variants included `logMoment`, `log_moment`, `Summable`, `indicator`,
     `Nat.log`, powers of logarithms divided by the index, and count/cardinality bounds.
   * The current accepted-event index, digestion backfill, digest text, and source atom hash were
     searched. The atom remains `residual-open`; the retired legacy formalization-receipt path has
     no current receipt to inspect.
   * Generalized searches included Abel/partial summation, nonnegative partitions, p-series,
     summability under finite shells, and the stronger smooth-series results. No theorem in D5 or
     pinned Mathlib derives this sparse logarithmic moment from a counting estimate.
   * Pinned Mathlib does provide `summable_partition`, `summable_subtype_iff_indicator`,
     `Real.summable_nat_pow_inv`, `Nat.pow_log_le_self`, `Nat.lt_pow_succ_log_self`,
     `Real.log_le_log`, and `Real.log_pow`; these are used directly below.
   * `origin/dev..origin/lane/math/*` had no in-flight commits when checked.

   The source's Vinogradov estimate and real exponent beta are made explicit here as a dyadic
   count with natural exponent k and constant C. This is the standard discrete consequence of
   N_A(x) << x/(log x)^k, with powers of log 2 absorbed into C. The source condition m < k - 1 is
   written as m + 1 < k, avoiding truncated natural subtraction. Requiring A subset {2,3,...}
   explicitly excludes the totalized `log 0` and division-by-zero branches; adding or removing
   the finitely many indices 0 and 1 does not affect the source convergence claim.
-/

import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Log

namespace D5.S3.Analytic.Boundary.LogMomentJetFromDyadicCount

open scoped BigOperators

/-- If the number of points of `A` in every base-two logarithmic shell is at most
`C * 2^j / (j+1)^k`, then every boundary logarithmic moment of order `m < k-1` is summable.
The supplied finite shells are required to be exactly the fibers of `Nat.log 2`, so the count
hypothesis cannot omit points of `A`. -/
theorem summable_log_moment_of_dyadic_count
    (A : Set ℕ) (hA : ∀ n ∈ A, 2 ≤ n)
    (m k : ℕ) (hm : m + 1 < k)
    (C : ℝ) (hC : 0 ≤ C)
    (shell : ℕ → Finset A)
    (hshell : ∀ j n, n ∈ shell j ↔ Nat.log 2 n = j)
    (hcount : ∀ j,
      ((shell j).card : ℝ) ≤
        C * (2 : ℝ) ^ j / (((j : ℝ) + 1) ^ k)) :
    Summable (A.indicator fun n : ℕ ↦ Real.log n ^ m / n) := by
  classical
  let moment : A → ℝ := fun n ↦ Real.log (n : ℕ) ^ m / (n : ℕ)
  have hmoment_nonneg : ∀ n, 0 ≤ moment n := by
    intro n
    exact div_nonneg (pow_nonneg (Real.log_natCast_nonneg n) m) (Nat.cast_nonneg n)
  have hshell_unique :
      ∀ n : A, ∃! j : ℕ, n ∈ ({x : A | x ∈ shell j} : Set A) := by
    intro n
    refine ⟨Nat.log 2 n, (hshell (Nat.log 2 n) n).2 rfl, ?_⟩
    intro j hj
    exact (hshell j n).1 hj |>.symm
  rw [← summable_subtype_iff_indicator]
  change Summable moment
  rw [summable_partition hmoment_nonneg hshell_unique]
  constructor
  · intro j
    exact Summable.of_finite
  · have hmk : m + 2 ≤ k := by omega
    have hmajor :
        Summable (fun j : ℕ ↦ C * Real.log 2 ^ m / (((j : ℝ) + 1) ^ 2)) := by
      have hbase : Summable (fun j : ℕ ↦ ((j : ℝ) ^ 2)⁻¹) :=
        Real.summable_nat_pow_inv.mpr (by norm_num)
      have hshifted : Summable (fun j : ℕ ↦ (((j : ℝ) + 1) ^ 2)⁻¹) := by
        simpa [Nat.cast_add, Nat.cast_one] using
          (summable_nat_add_iff (f := fun j : ℕ ↦ ((j : ℝ) ^ 2)⁻¹) 1).2 hbase
      simpa [div_eq_mul_inv, mul_assoc] using
        hshifted.mul_left (C * Real.log 2 ^ m)
    apply Summable.of_nonneg_of_le
      (fun j ↦ tsum_nonneg fun n : {x : A | x ∈ shell j} ↦ hmoment_nonneg n)
      (fun j ↦ ?_) hmajor
    let scale : ℝ := ((j : ℝ) + 1) * Real.log 2
    let shellMajorant : ℝ := scale ^ m / (2 : ℝ) ^ j
    have hscale_nonneg : 0 ≤ scale := by
      dsimp [scale]
      positivity
    have hshellMajorant_nonneg : 0 ≤ shellMajorant := by
      dsimp [shellMajorant]
      positivity
    have hterm : ∀ n ∈ shell j, moment n ≤ shellMajorant := by
      intro n hn
      have hnA : 2 ≤ (n : ℕ) := hA n n.property
      have hn_ne : (n : ℕ) ≠ 0 := by omega
      have hlogShell : Nat.log 2 (n : ℕ) = j := (hshell j n).1 hn
      have hlowerNat : 2 ^ j ≤ (n : ℕ) := by
        simpa [hlogShell] using Nat.pow_log_le_self 2 hn_ne
      have hupperNat : (n : ℕ) < 2 ^ (j + 1) := by
        simpa [hlogShell, Nat.succ_eq_add_one] using
          Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (n : ℕ)
      have hnReal : 0 < ((n : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < (n : ℕ))
      have hlower : (2 : ℝ) ^ j ≤ ((n : ℕ) : ℝ) := by exact_mod_cast hlowerNat
      have hupper : ((n : ℕ) : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
        exact_mod_cast hupperNat.le
      have hlog_le : Real.log (n : ℕ) ≤ scale := by
        calc
          Real.log (n : ℕ) ≤ Real.log ((2 : ℝ) ^ (j + 1)) :=
            Real.log_le_log hnReal hupper
          _ = scale := by simp [scale, Real.log_pow, Nat.cast_add, Nat.cast_one]
      have hlog_pow : Real.log (n : ℕ) ^ m ≤ scale ^ m :=
        pow_le_pow_left₀ (Real.log_natCast_nonneg n) hlog_le m
      calc
        moment n ≤ scale ^ m / ((n : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right hlog_pow (Nat.cast_nonneg n)
        _ ≤ shellMajorant := by
          dsimp [shellMajorant]
          exact div_le_div_of_nonneg_left (pow_nonneg hscale_nonneg m) (by positivity) hlower
    have hsumBound :
        (∑' n : {x : A | x ∈ shell j}, moment n) ≤
          ((shell j).card : ℝ) * shellMajorant := by
      rw [tsum_fintype]
      simpa [nsmul_eq_mul] using
        Finset.sum_le_card_nsmul Finset.univ
          (fun n : {x : A | x ∈ shell j} ↦ moment n) shellMajorant
          (fun n _ ↦ hterm n n.property)
    have hpowden : (((j : ℝ) + 1) ^ (m + 2)) ≤ ((j : ℝ) + 1) ^ k :=
      pow_le_pow_right₀ (by norm_num) hmk
    have hcount' :
        ((shell j).card : ℝ) ≤
          C * (2 : ℝ) ^ j / (((j : ℝ) + 1) ^ (m + 2)) :=
      (hcount j).trans <|
        div_le_div_of_nonneg_left (mul_nonneg hC (by positivity)) (by positivity) hpowden
    calc
      (∑' n : {x : A | x ∈ shell j}, moment n) ≤
          ((shell j).card : ℝ) * shellMajorant := hsumBound
      _ ≤ (C * (2 : ℝ) ^ j / (((j : ℝ) + 1) ^ (m + 2))) *
          shellMajorant := mul_le_mul_of_nonneg_right hcount' hshellMajorant_nonneg
      _ = C * Real.log 2 ^ m / (((j : ℝ) + 1) ^ 2) := by
        dsimp [shellMajorant, scale]
        rw [pow_add, mul_pow]
        field_simp

#print axioms summable_log_moment_of_dyadic_count

end D5.S3.Analytic.Boundary.LogMomentJetFromDyadicCount
