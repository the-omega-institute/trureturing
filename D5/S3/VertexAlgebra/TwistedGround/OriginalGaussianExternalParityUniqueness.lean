/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalParityUniqueness
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalParityUniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal external kernel parity and exclusion of the positive-sector coefficient resonance. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadialSums

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

/-- The two homogeneous ++T coefficient equations have no even-z solution
except zero. Missing negative external indices are explicitly zero. The
induction uses frequency difference off the diagonal and radial nonresonance
on the diagonal; no initial diagonal data or equality is a hypothesis. -/
theorem positive_even_coefficients_zero (c : ℕ → ℕ → ℕ → ℂ)
    (hodd : ∀ p q k, Odd k → c p q k = 0)
    (hdiff : ∀ p q k,
      ((p : ℂ) - q) * c p q k -
        (p + 1 / 2) * (if p = 0 then 0 else c (p - 1) q k) +
        (q + 1 / 2) * (if q = 0 then 0 else c p (q - 1) k) = 0)
    (hrad : ∀ p q k,
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

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalParityUniqueness
