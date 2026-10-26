/- GID: D5/S3/Analytic/KilbasSaigo/Defs
   generality: G
   mirror-B: D5/B/S3/Analytic/KilbasSaigo/Defs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Gamma.Basic]
   utility: none
   digest: Kilbas–Saigo coefficients, real series, and two-sided hyperbolic bounds. -/

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

namespace D5.S3.Analytic.KilbasSaigo.Defs

/-- Coefficient ∏_{k=1}^{n} Γ(1+α((k−1)m+l))/Γ(1+α((k−1)m+l+1)). -/
noncomputable def ksCoeff (α m l : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, Real.Gamma (1 + α * (k * m + l)) / Real.Gamma (1 + α * (k * m + l + 1))

/-- The Kilbas–Saigo function E_{α,m,l}(z) for real z. -/
noncomputable def kilbasSaigo (α m l z : ℝ) : ℝ := ∑' n : ℕ, ksCoeff α m l n * z ^ n

/-- Conjecture 4.5. -/
def claim : Prop :=
  ∀ α m l x : ℝ, 0 < α → α ≤ 1 → 0 < m → m - 1 / α < l → 0 ≤ x →
    1 / (1 + Real.Gamma (1 + α * (l - m)) / Real.Gamma (1 + α * (l - m + 1)) * x) ≤ kilbasSaigo α m l (-x) ∧
    kilbasSaigo α m l (-x) ≤ 1 / (1 + Real.Gamma (1 + α * l) / Real.Gamma (1 + α * (1 + l)) * x)

end D5.S3.Analytic.KilbasSaigo.Defs
