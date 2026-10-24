/- GID: D5/S3/Analytic/KarpZhangConjecture/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/KarpZhangConjecture/Result
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Both coefficientwise log-concavity assertions of Karp--Zhang Conjecture 5.2. -/

import D5.S3.Analytic.KarpZhangReciprocal.Result
import D5.S3.Analytic.KarpZhangGamma.Series

/-!
admission_basis: open-problem-resolution (#20997; Proved)
content theorem: result.
Per-declaration proof_shape:
* claim: bind-only definition; consumer: result; escape_witness: none.
* result: content; escape_witness: KarpZhangReciprocal.IntervalConvolution.score_variance_bound
  and KarpZhangGamma.Result.pairedKernel_sign, through reciprocal_half and gamma_half;
  consumer: external Conjecture 5.2 settlement.
The two imported halves and their supporting modules are same-delivery content,
not pre-existing frozen prerequisites. Direct frozen D5 dependencies: none.
The utility is none: this is a uniform theorem about all coefficient degrees,
not a bounded enumeration, checker, numerical reduction or certified instance.
-/

noncomputable section

namespace D5.S3.Analytic.KarpZhangConjecture.Result

/-- Conjecture 5.2: both formal-series Turanians have nonnegative coefficients,
with the source's sequence convention and arbitrary nonnegative real shifts. -/
def claim : Prop :=
  ∀ y : ℕ → ℝ, KarpZhangReciprocal.Result.IsLogConcave y →
    ∀ μ α β : ℝ, 0 < μ → 0 ≤ α → 0 ≤ β →
      ∀ m : ℕ, 0 ≤ KarpZhangReciprocal.Result.delta y μ α β m ∧
        0 ≤ KarpZhangGamma.Series.gammaDelta y μ α β m

/-- Both halves of Karp--Zhang Conjecture 5.2. -/
theorem result : claim := by
  intro y hy μ α β hμ hα hβ m
  exact ⟨KarpZhangReciprocal.Result.reciprocal_half y hy μ hμ α β hα hβ m,
    KarpZhangGamma.Series.gamma_half y hy μ α β hμ hα hβ m⟩

end D5.S3.Analytic.KarpZhangConjecture.Result
