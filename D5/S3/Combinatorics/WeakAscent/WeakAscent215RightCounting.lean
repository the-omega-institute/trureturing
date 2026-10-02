/- GID: D5/S3/Combinatorics/WeakAscent/WeakAscent215RightCounting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WeakAscent/WeakAscent215RightCounting
   mirror-E: none(waiver:right-continuation-series-certificate)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Inverse]
   utility: none
   digest: Degree recursion identifies every right-label continuation series. -/

import Mathlib.RingTheory.PowerSeries.Inverse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.WeakAscent.WeakAscent215RightCounting

open Finset PowerSeries

def continuationCounts : ℕ → ℕ → ℕ × ℕ
  | 0, _ => (1, 1)
  | degree + 1, budget =>
      ((continuationCounts degree (budget + 1)).1 +
          ∑ index ∈ range budget, (continuationCounts degree (index + 1)).2,
       (continuationCounts degree budget).1 + (continuationCounts degree (budget + 1)).2 +
          ∑ index ∈ range budget, (continuationCounts degree (index + 1)).2)

def qSeries (budget : ℕ) : PowerSeries ℚ :=
  mk fun degree => ((continuationCounts degree budget).1 : ℚ)

def pSeries (budget : ℕ) : PowerSeries ℚ :=
  mk fun degree => ((continuationCounts degree budget).2 : ℚ)

noncomputable def numerator (series : PowerSeries ℚ) : PowerSeries ℚ :=
  series ^ 2 * (1 - X ^ 2 * series ^ 2)⁻¹

noncomputable def ratio (series : PowerSeries ℚ) : PowerSeries ℚ :=
  numerator series * series⁻¹

noncomputable def positiveBase (series : PowerSeries ℚ) : PowerSeries ℚ :=
  numerator series * (1 + X * series)

end D5.S3.Combinatorics.WeakAscent.WeakAscent215RightCounting
