/- GID: D5/S3/Analytic/AlternatingPoleCoefficients
   generality: G
   mirror-B: D5/B/S3/Analytic/AlternatingPoleCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A pole of order d+1 at minus one has alternating binomial coefficients of degree d. -/

import Mathlib.RingTheory.PowerSeries.Binomial

/- Provenance: thin honest wrapper over pinned mathlib's coefficient formula
   `PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose`, transported from
   `1 - X` to `1 + X` by `PowerSeries.coeff_rescale`. -/

namespace D5.S3.Analytic.AlternatingPoleCoefficients

/-- The coefficient of degree `n` in `(1 + X)^(-(degree + 1))` is the
alternating binomial polynomial `(-1)^n * choose (degree + n) degree`.

Thus increasing the pole order from `degree` to `degree + 1` raises the
polynomial degree of the alternating coefficient envelope by one. -/
theorem alternating_pole_coefficients (degree n : ℕ) :
    PowerSeries.coeff n
        (PowerSeries.rescale (-1 : ℤ)
          (PowerSeries.invOneSubPow ℤ (degree + 1)).val) =
      (-1 : ℤ) ^ n * Nat.choose (degree + n) degree := by
  rw [PowerSeries.coeff_rescale,
    PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose,
    PowerSeries.coeff_mk]

end D5.S3.Analytic.AlternatingPoleCoefficients
