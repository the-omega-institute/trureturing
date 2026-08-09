/- GID: D5/S3/Divergence/StrictGibbs
   generality: G
   mirror-B: D5/B/S3/Divergence/StrictGibbs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Deduce strict positivity of finite classical KL divergence from disequality. -/

/- Library-search audit trail (2026-08-09):
   * Repository-wide searches enumerated every `theorem` and `lemma` under `D5/`, then checked
     `klDivergence`, positivity, disequality, strictness, and rearranged inequality forms.
   * The only matching repository results are `kl_divergence_nonneg` and
     `kl_divergence_eq_zero_iff`; no existing strict form was found.
   * Pinned mathlib searches for `klDiv`, `klDiv_eq_zero_iff`, `toReal_klDiv`,
     `Fintype.*klDiv`, and `PMF.*klDiv` found only the measure-valued `ℝ≥0∞` theory, with no
     bridge to `ClassicalDPI.klDivergence`.
   * The proof below therefore composes the repository's nonnegativity and zero-equality
     characterization without rebuilding either result.
-/

import D5.S3.Divergence.GrandmotherTheorem
import D5.S3.Divergence.GibbsEquality

namespace D5.S3.Divergence.StrictGibbs

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Divergence.GrandmotherTheorem
open D5.S3.Divergence.GibbsEquality

/-- Distinct finite probability mass functions have strictly positive classical KL divergence
under discrete absolute continuity. -/
theorem kl_divergence_pos_of_ne {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (hq : (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1)
    (hac : ∀ i, q i = 0 → p i = 0)
    (hpq : p ≠ q) :
    0 < klDivergence p q := by
  exact (kl_divergence_nonneg p q hp hq hac).lt_of_ne fun hzero =>
    hpq ((kl_divergence_eq_zero_iff p q hp hq hac).mp hzero.symm)

end D5.S3.Divergence.StrictGibbs
