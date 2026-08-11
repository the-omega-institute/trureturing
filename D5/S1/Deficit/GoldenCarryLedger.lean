/- GID: D5/S1/Deficit/GoldenCarryLedger
   generality: G
   mirror-B: D5/B/S1/Deficit/GoldenCarryLedger
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: For any root x of x²=x+1 (both golden faces φ=goldenRatio and ψ=goldenConj), the adjacency carry x^{k+1}+x^{k+2}=x^{k+3} and the doubling carry 2x^{k+2}=x^{k+3}+x^k preserve value; the two-face invariance is the zero-deficit internal carry ledger. -/

import Mathlib

namespace D5.S1.Deficit.GoldenCarryLedger

open Real

/-- Adjacency carry rule `11 → 100`: for any root of `x² = x + 1`, powers satisfy
`x^{k+1} + x^{k+2} = x^{k+3}` (the value-preserving Zeckendorf carry). -/
theorem adjacency_of_sq (x : ℝ) (hx : x ^ 2 = x + 1) (k : ℕ) :
    x ^ (k + 1) + x ^ (k + 2) = x ^ (k + 3) := by
  have h : x ^ (k + 3) = x ^ (k + 1) * x ^ 2 := by ring
  rw [h, hx]; ring

/-- Doubling carry rule: `2·x^{k+2} = x^{k+3} + x^k` (from `x³ + 1 = 2x²`), the
value-preserving doubling rewrite. -/
theorem doubling_of_sq (x : ℝ) (hx : x ^ 2 = x + 1) (k : ℕ) :
    2 * x ^ (k + 2) = x ^ (k + 3) + x ^ k := by
  have h3 : x ^ (k + 3) = x ^ k * x ^ 3 := by ring
  have h2 : x ^ (k + 2) = x ^ k * x ^ 2 := by ring
  have hcube : x ^ 3 = 2 * x + 1 := by linear_combination (x + 1) * hx
  rw [h3, h2, hx, hcube]; ring

/-- The two-face carry ledger (命题 6.21): both conjugate golden roots `φ = goldenRatio`
and `ψ = goldenConj` satisfy `x² = x + 1`, so the adjacency and doubling carry rewrites
preserve value on **both** faces simultaneously — the internal rules are zero-deficit. -/
theorem carry_rewrite_face_invariant (k : ℕ) :
    (goldenRatio ^ (k + 1) + goldenRatio ^ (k + 2) = goldenRatio ^ (k + 3) ∧
      2 * goldenRatio ^ (k + 2) = goldenRatio ^ (k + 3) + goldenRatio ^ k) ∧
    (goldenConj ^ (k + 1) + goldenConj ^ (k + 2) = goldenConj ^ (k + 3) ∧
      2 * goldenConj ^ (k + 2) = goldenConj ^ (k + 3) + goldenConj ^ k) := by
  refine ⟨⟨adjacency_of_sq _ ?_ k, doubling_of_sq _ ?_ k⟩,
          ⟨adjacency_of_sq _ ?_ k, doubling_of_sq _ ?_ k⟩⟩
  · exact goldenRatio_sq
  · exact goldenRatio_sq
  · exact goldenConj_sq
  · exact goldenConj_sq

end D5.S1.Deficit.GoldenCarryLedger
