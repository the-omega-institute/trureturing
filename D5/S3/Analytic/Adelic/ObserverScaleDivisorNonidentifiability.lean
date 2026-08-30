/- GID: D5/S3/Analytic/Adelic/ObserverScaleDivisorNonidentifiability
   generality: G
   mirror-B: D5/B/S3/Analytic/Adelic/ObserverScaleDivisorNonidentifiability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Distinct positive observer scales have the same spectral zeta divisor. -/

import Mathlib.Analysis.Meromorphic.Order
import Mathlib.NumberTheory.LSeries.RiemannZeta

/- Library-search audit trail (2026-08-30):
   * Current D5 and origin/dev searches for observer spectral zeta constructors,
     exponential Riemann-zeta factors, and scale-divisor noninjectivity found no
     exact theorem or source-object definition.
   * Pinned Mathlib has no theorem constructing the observer collision below.
     Its exact local primitive `meromorphicOrderAt_mul_of_ne_zero` states that
     an analytic nonzero multiplier preserves meromorphic order, and is applied
     directly below.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Adelic.ObserverScaleDivisorNonidentifiability

noncomputable section

/-- The spectral zeta reading of a circle observer with positive circumference
`P` and positive propagation coefficient `c`. -/
def observerSpectralZeta (P c : Set.Ioi (0 : Real)) (s : Complex) : Complex :=
  2 * Complex.exp
      (-s * (Real.log (2 * Real.pi * (c : Real) / (P : Real)) : Complex)) *
    riemannZeta s

private theorem observer_spectral_zeta_order_eq
    (P c : Set.Ioi (0 : Real)) (s : Complex) :
    meromorphicOrderAt (observerSpectralZeta P c) s =
      meromorphicOrderAt riemannZeta s := by
  let factor : Complex -> Complex := fun z =>
    2 * Complex.exp
      (-z * (Real.log (2 * Real.pi * (c : Real) / (P : Real)) : Complex))
  have factorAnalytic : AnalyticAt Complex factor s := by
    dsimp [factor]
    fun_prop
  have factorNonzero : factor s ≠ 0 := by
    dsimp [factor]
    exact mul_ne_zero (by norm_num) (Complex.exp_ne_zero _)
  have factorization : observerSpectralZeta P c = factor * riemannZeta := by
    funext z
    rfl
  rw [factorization]
  exact meromorphicOrderAt_mul_of_ne_zero factorAnalytic factorNonzero

/-- Spectral zeros and poles cannot recover the observer scale: two observers
can have different positive `P`, different positive `c`, and different `P / c`,
while both spectral zeta functions have exactly the Riemann-zeta divisor. -/
theorem observer_scale_not_recoverable_from_spectral_divisor :
    ∃ P1 c1 P2 c2 : Set.Ioi (0 : Real),
      (P1 : Real) ≠ (P2 : Real) ∧
      (c1 : Real) ≠ (c2 : Real) ∧
      (P1 : Real) / (c1 : Real) ≠ (P2 : Real) / (c2 : Real) ∧
      ∀ s : Complex,
        meromorphicOrderAt (observerSpectralZeta P1 c1) s =
            meromorphicOrderAt riemannZeta s ∧
          meromorphicOrderAt (observerSpectralZeta P2 c2) s =
            meromorphicOrderAt riemannZeta s := by
  let P1 : Set.Ioi (0 : Real) := ⟨1, by norm_num⟩
  let c1 : Set.Ioi (0 : Real) := ⟨1, by norm_num⟩
  let P2 : Set.Ioi (0 : Real) := ⟨4, by norm_num⟩
  let c2 : Set.Ioi (0 : Real) := ⟨2, by norm_num⟩
  refine ⟨P1, c1, P2, c2, ?_, ?_, ?_, ?_⟩
  · norm_num [P1, P2]
  · norm_num [c1, c2]
  · norm_num [P1, c1, P2, c2]
  · intro s
    exact ⟨observer_spectral_zeta_order_eq P1 c1 s,
      observer_spectral_zeta_order_eq P2 c2 s⟩

#print axioms observer_scale_not_recoverable_from_spectral_divisor

end

end D5.S3.Analytic.Adelic.ObserverScaleDivisorNonidentifiability
