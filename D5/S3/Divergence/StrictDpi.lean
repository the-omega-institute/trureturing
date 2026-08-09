/- GID: D5/S3/Divergence/StrictDpi
   generality: G
   mirror-B: D5/B/S3/Divergence/StrictDpi
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Deduce strict positivity of the classical DPI defect from posterior disequality. -/

/- Library-search audit trail (2026-08-09):
   * Repository-wide searches enumerated every `theorem` and `lemma` under `D5/`, then checked
     `klDivergence`, `channelOutput`, `posterior`, defect, positivity, disequality, strictness,
     and rearranged inequality forms.
   * The only matching repository results are `dpi_defect_nonneg` and
     `dpi_defect_zero_iff_posteriors_eq`; no existing strict defect form was found.
   * Pinned mathlib searches for `klDiv`, data processing, chain rules, `toReal_klDiv`,
     `Fintype.*klDiv`, and `PMF.*klDiv` found only the measure-valued `ℝ≥0∞` theory, with no
     bridge to the repository's finite real divergence or posterior defect.
   * The proof below therefore composes the two repository results, using output positivity only
     to discharge the support premise in the Petz characterization.
-/

import D5.S3.Divergence.DpiDefect
import D5.S3.Divergence.PetzClassical

namespace D5.S3.Divergence.StrictDpi

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Divergence.DpiDefect
open D5.S3.Divergence.PetzClassical

/-- A posterior mismatch makes the finite classical data-processing defect strictly positive. -/
theorem dpi_defect_pos_of_posteriors_ne {X Y : Type*}
    [Fintype X] [Nonempty X] [Fintype Y]
    (p q : X → ℝ) (W : X → Y → ℝ)
    (hp : (∀ x, 0 < p x) ∧ ∑ x, p x = 1)
    (hq : (∀ x, 0 < q x) ∧ ∑ x, q x = 1)
    (hW : (∀ x y, 0 < W x y) ∧ ∀ x, ∑ y, W x y = 1)
    (hne : ∃ y, posterior W p y ≠ posterior W q y) :
    0 < klDivergence p q -
      klDivergence (channelOutput W p) (channelOutput W q) := by
  classical
  have hOutputPPos (y : Y) : 0 < channelOutput W p y := by
    rw [channelOutput]
    refine Finset.sum_pos' (fun x _ => (mul_pos (hp.1 x) (hW.1 x y)).le) ?_
    let x : X := Classical.choice inferInstance
    exact ⟨x, Finset.mem_univ x, mul_pos (hp.1 x) (hW.1 x y)⟩
  exact (dpi_defect_nonneg p q W hp hq hW).lt_of_ne fun hzero =>
    hne.elim fun y hposterior =>
      hposterior ((dpi_defect_zero_iff_posteriors_eq p q W hp hq hW).mp
        hzero.symm y (hOutputPPos y))

end D5.S3.Divergence.StrictDpi
