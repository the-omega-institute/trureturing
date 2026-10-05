/- GID: D5/S3/Arith/FibonacciAtomic/RawCommonSeedFrontier
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Arbitrary measurable controller laws have the exact raw common-seed frontier. -/

import D5.S3.Arith.FibonacciAtomic.FourExitRawParetoSpectrum
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.RawCommonSeedFrontier

open ActualTreeReadoutAcquisition FourExitRawEndpointSpectrum MeasureTheory
open scoped BigOperators ENNReal
local notation "Index" => fun k : Nat => Unit ⊕ (Fin k × Fin 4)

/-- At parameter t the baseline has mass 1-5kt; the four slot choices
have masses t,t,2t,t, with the first choosing the A-zero, H-two endpoint. -/
noncomputable def frontierMeasure (k : Nat) (t : ℝ) : Measure (Index k) :=
  Measure.sum (fun l => ENNReal.ofReal (match l with
    | .inl _ => 1 - 5 * (k : ℝ) * t
    | .inr p => if p.2 = 2 then 2 * t else t) • Measure.dirac l)

end D5.S3.Arith.FibonacciAtomic.RawCommonSeedFrontier
