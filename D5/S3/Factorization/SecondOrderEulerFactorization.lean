/- GID: D5/S3/Factorization/SecondOrderEulerFactorization
   generality: G
   mirror-B: D5/B/S3/Factorization/SecondOrderEulerFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Convergent local second-order factors assemble into the corresponding Euler product. -/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/- Provenance: thin honest wrapper over pinned mathlib's infinite-product
   composition (`HasProd.mul`, `HasSum.cexp`, `HasProd.congr_fun`, and
   `HasProd.unique`). No exact second-order wrapper was found upstream. -/

namespace D5.S3.Factorization.SecondOrderEulerFactorization

/-- A pointwise second-order factorization lifts to the global Euler product
when all three factor products and the logarithmic remainder have explicit
convergence witnesses. The third factor represents the reciprocal term; its
convergence is stated directly, so no nonvanishing assumption is hidden. -/
theorem second_order_euler_factorization
    {ι : Type*}
    {localFactor firstFactor secondFactor reciprocalFactor remainder : ι → ℂ}
    {localProduct firstProduct secondProduct reciprocalProduct remainderSum : ℂ}
    (hlocal : ∀ i,
      localFactor i = firstFactor i * secondFactor i * reciprocalFactor i *
        Complex.exp (remainder i))
    (hLocalProduct : HasProd localFactor localProduct)
    (hFirstProduct : HasProd firstFactor firstProduct)
    (hSecondProduct : HasProd secondFactor secondProduct)
    (hReciprocalProduct : HasProd reciprocalFactor reciprocalProduct)
    (hRemainder : HasSum remainder remainderSum) :
    localProduct = firstProduct * secondProduct * reciprocalProduct *
      Complex.exp remainderSum := by
  have hExpRemainder :
      HasProd (Complex.exp ∘ remainder) (Complex.exp remainderSum) :=
    hRemainder.cexp
  have hFactoredProduct :
      HasProd
        (fun i => firstFactor i * secondFactor i * reciprocalFactor i *
          Complex.exp (remainder i))
        (firstProduct * secondProduct * reciprocalProduct * Complex.exp remainderSum) :=
    ((hFirstProduct.mul hSecondProduct).mul hReciprocalProduct).mul hExpRemainder
  exact HasProd.unique hLocalProduct (hFactoredProduct.congr_fun hlocal)

end D5.S3.Factorization.SecondOrderEulerFactorization
