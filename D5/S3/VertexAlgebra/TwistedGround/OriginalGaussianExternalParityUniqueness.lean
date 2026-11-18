/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalParityUniqueness
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalParityUniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal kernel parity and positive-sector coefficient nonresonance. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadialSums
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness

/-! Parity retains the direct identity pairing in the full square contraction.
The coefficient theorem is the algebraic uniqueness step for the positive-sector
frequency and radial equations. Analytic extraction of these coefficients from
the literal kernels is not assumed to have been established here. -/

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalParityUniqueness

open OriginalGaussianMatrix OriginalGaussianAllIndexResolvent
open OriginalGaussianExternalResolvent OriginalGaussianExternalGeneratedSource

private lemma column_neg (out : Bool) (p : ℕ) (z : ℂ) (n : ℕ) :
    externalColumn out p (-z) n = (-1 : ℂ) ^ (n + 1) * externalColumn out p z n := by
  unfold externalColumn
  rw [neg_pow]
  ring

private lemma matrix_neg (z : ℂ) (s t : ℕ) :
    matrixEntry (-z) s t = (-1 : ℂ) ^ (s + t) * matrixEntry z s t := by
  unfold matrixEntry
  rw [neg_pow]
  ring

private lemma odd_neg (z : ℂ) (s t : ℕ) :
    explicitOddEntry (-z) s t = (-1 : ℂ) ^ (s + t) * explicitOddEntry z s t := by
  simp only [explicitOddEntry, neg_sq]
  rw [neg_pow z (s + t)]
  ring

/-- Every literal external J mode is even, without convergence or disk hypotheses. -/
theorem externalJ_neg (out : Bool) (p : ℕ) (out' : Bool) (q : ℕ) (z : ℂ) :
    externalJ out p out' q (-z) = externalJ out p out' q z := by
  unfold externalJ
  apply tsum_congr
  rintro ⟨s, t⟩
  dsimp only
  rw [column_neg, odd_neg, column_neg,
    pow_add (-1 : ℂ) (s + 1) (t + 1)]
  rcases neg_one_pow_eq_or ℂ (s + 1) with hs | hs <;>
    rcases neg_one_pow_eq_or ℂ (t + 1) with ht | ht <;>
    simp [hs, ht]

/-- Every literal full T mode is even; its identity pairing is included. -/
theorem externalT_neg (out : Bool) (p : ℕ) (out' : Bool) (q : ℕ) (z : ℂ) :
    externalT out p out' q (-z) = externalT out p out' q z := by
  unfold externalT
  congr 1
  · apply tsum_congr
    intro s
    rw [column_neg, column_neg]
    rcases neg_one_pow_eq_or ℂ (s + 1) with hs | hs <;> simp [hs]
  · apply tsum_congr
    rintro ⟨⟨s, k⟩, t⟩
    dsimp only
    rw [column_neg, matrix_neg, odd_neg, column_neg,
      pow_add (-1 : ℂ) (s + 1) (k + 1),
      pow_add (-1 : ℂ) (k + 1) (t + 1)]
    rcases neg_one_pow_eq_or ℂ (s + 1) with hs | hs <;>
      rcases neg_one_pow_eq_or ℂ (k + 1) with hk | hk <;>
      rcases neg_one_pow_eq_or ℂ (t + 1) with ht | ht <;>
      simp [hs, hk, ht]

/-- The full original generator is even in z in every signed sector. -/
theorem kernelMode_neg (square out out' : Bool) (u v z : ℂ) :
    kernelMode square out out' u v (-z) = kernelMode square out out' u v z := by
  unfold kernelMode
  apply tsum_congr
  intro pq
  rw [externalT_neg, externalJ_neg]

private lemma even_series_odd_coefficients_zero (f : ℂ → ℂ)
    (heven : ∀ z, f (-z) = f z) (a : ℕ → ℂ)
    (ha : HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ a) 0) (k : ℕ) (hk : Odd k) :
    a k = 0 := by
  have hn : HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ (fun n => (-1 : ℂ) ^ n * a n)) 0 := by
    have ha' : HasFPowerSeriesAt f
        (FormalMultilinearSeries.ofScalars ℂ a) ((-ContinuousLinearMap.id ℂ ℂ) 0) := by
      simpa using ha
    simpa only [neg_apply, ContinuousLinearMap.id_apply, neg_zero,
      Function.comp_def, heven, FormalMultilinearSeries.ofScalars_comp_neg_id]
      using ha'.compContinuousLinearMap (u := -ContinuousLinearMap.id ℂ ℂ) (x := 0)
  have he := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p k (fun _ => 1))
    (ha.eq_formalMultilinearSeries hn)
  simp [FormalMultilinearSeries.ofScalars, hk.neg_one_pow] at he
  linear_combination he / 2

/-- The two homogeneous ++T coefficient equations have no even-z solution
except zero. Missing negative external indices are explicitly zero. The
induction uses frequency difference off the diagonal and radial nonresonance
on the diagonal; no initial diagonal data or equality is a hypothesis. -/
theorem positive_even_coefficients_zero (c : ℕ → ℕ → ℕ → ℂ)
    (hodd : ∀ (p q k : ℕ), Odd k → c p q k = 0)
    (hdiff : ∀ (p q k : ℕ),
      ((p : ℂ) - q) * c p q k -
        (p + 1 / 2) * (if p = 0 then 0 else c (p - 1) q k) +
        (q + 1 / 2) * (if q = 0 then 0 else c p (q - 1) k) = 0)
    (hrad : ∀ (p q k : ℕ),
      ((k : ℂ) - p - q - 1) * c p q k +
        (p + 1 / 2) * (if p = 0 then 0 else c (p - 1) q k) +
        (q + 1 / 2) * (if q = 0 then 0 else c p (q - 1) k) = 0) :
    ∀ p q k, c p q k = 0 := by
  have h : ∀ d p q, p + q = d → ∀ k, c p q k = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro p q hpq k
      by_cases hk : Odd k
      · exact hodd p q k hk
      have hp : (if p = 0 then 0 else c (p - 1) q k) = 0 := by
        split_ifs with hzero
        · rfl
        · exact ih (p - 1 + q) (by omega) (p - 1) q rfl k
      have hq : (if q = 0 then 0 else c p (q - 1) k) = 0 := by
        split_ifs with hzero
        · rfl
        · exact ih (p + (q - 1)) (by omega) p (q - 1) rfl k
      by_cases he : p = q
      · have hnonzero : (k : ℂ) - p - q - 1 ≠ 0 := by
          intro hz
          have hcast : (k : ℂ) = ((p + p + 1 : ℕ) : ℂ) := by
            push_cast
            rw [← he] at hz
            linear_combination hz
          have hnat : k = p + p + 1 := by exact_mod_cast hcast
          exact hk ⟨p, by omega⟩
        have hz := hrad p q k
        rw [hp, hq] at hz
        exact (mul_eq_zero.mp (by simpa using hz)).resolve_left hnonzero
      · have hnonzero : (p : ℂ) - q ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast he)
        have hz := hdiff p q k
        rw [hp, hq] at hz
        exact (mul_eq_zero.mp (by simpa using hz)).resolve_left hnonzero
  intro p q k
  exact h (p + q) p q rfl k

/-- Conditional analytic identification of the literal ++T modes. The candidate
is even, and the Taylor coefficients of its difference from the full original
T obey both homogeneous equations, including zero negative-index boundaries.
Extracting these recurrence hypotheses from the differential equations remains
an explicit analytic obligation; they are not an assumed equality of kernels. -/
theorem externalT_positive_germ_unique (candidate : ℕ → ℕ → ℂ → ℂ)
    (heven : ∀ p q z, candidate p q (-z) = candidate p q z)
    (c : ℕ → ℕ → ℕ → ℂ)
    (hexp : ∀ p q, HasFPowerSeriesAt
      (fun z => externalT true p true q z - candidate p q z)
      (FormalMultilinearSeries.ofScalars ℂ (c p q)) 0)
    (hdiff : ∀ (p q k : ℕ),
      ((p : ℂ) - q) * c p q k -
        (p + 1 / 2) * (if p = 0 then 0 else c (p - 1) q k) +
        (q + 1 / 2) * (if q = 0 then 0 else c p (q - 1) k) = 0)
    (hrad : ∀ (p q k : ℕ),
      ((k : ℂ) - p - q - 1) * c p q k +
        (p + 1 / 2) * (if p = 0 then 0 else c (p - 1) q k) +
        (q + 1 / 2) * (if q = 0 then 0 else c p (q - 1) k) = 0) :
    ∀ p q, ∀ᶠ z in nhds (0 : ℂ), externalT true p true q z = candidate p q z := by
  have hodd : ∀ p q k, Odd k → c p q k = 0 := by
    intro p q k hk
    exact even_series_odd_coefficients_zero _
      (fun z => by rw [externalT_neg, heven]) _ (hexp p q) k hk
  have hc := positive_even_coefficients_zero c hodd hdiff hrad
  intro p q
  have hp : FormalMultilinearSeries.ofScalars ℂ (c p q) = 0 := by
    have hz : c p q = 0 := funext (hc p q)
    simp [hz]
  have h := hexp p q
  rw [hp] at h
  exact h.eventually_eq_zero.mono (fun z hz => sub_eq_zero.mp hz)

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalParityUniqueness
