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

/-- Every pair of positive observers has the same spectral zero-pole divisor;
there are observers with both parameters distinct that share that divisor; and
no function of the divisor observation can recover `P / c` for every observer. -/
theorem observer_scale_not_recoverable_from_spectral_divisor :
    (∀ P1 c1 P2 c2 : Set.Ioi (0 : Real), ∀ s : Complex,
      meromorphicOrderAt (observerSpectralZeta P1 c1) s =
        meromorphicOrderAt (observerSpectralZeta P2 c2) s) ∧
    (∃ P1 c1 P2 c2 : Set.Ioi (0 : Real),
      P1 ≠ P2 ∧ c1 ≠ c2 ∧ ∀ s : Complex,
        meromorphicOrderAt (observerSpectralZeta P1 c1) s =
          meromorphicOrderAt (observerSpectralZeta P2 c2) s) ∧
    ¬ ∃ recover : (Complex → WithTop Int) → Real,
      ∀ P c : Set.Ioi (0 : Real),
        recover (fun s => meromorphicOrderAt (observerSpectralZeta P c) s) =
          (P : Real) / (c : Real) := by
  have allObservers :
      ∀ P1 c1 P2 c2 : Set.Ioi (0 : Real), ∀ s : Complex,
        meromorphicOrderAt (observerSpectralZeta P1 c1) s =
          meromorphicOrderAt (observerSpectralZeta P2 c2) s := by
    intro P1 c1 P2 c2 s
    calc
      meromorphicOrderAt (observerSpectralZeta P1 c1) s =
          meromorphicOrderAt riemannZeta s :=
        observer_spectral_zeta_order_eq P1 c1 s
      _ = meromorphicOrderAt (observerSpectralZeta P2 c2) s :=
        (observer_spectral_zeta_order_eq P2 c2 s).symm
  let P1 : Set.Ioi (0 : Real) := ⟨1, by norm_num⟩
  let c1 : Set.Ioi (0 : Real) := ⟨1, by norm_num⟩
  let P2 : Set.Ioi (0 : Real) := ⟨2, by norm_num⟩
  let c2 : Set.Ioi (0 : Real) := ⟨3, by norm_num⟩
  have differentP : P1 ≠ P2 := by
    intro equalObservers
    have equalValues : (P1 : Real) = (P2 : Real) :=
      congrArg Subtype.val equalObservers
    norm_num [P1, P2] at equalValues
  have differentC : c1 ≠ c2 := by
    intro equalObservers
    have equalValues : (c1 : Real) = (c2 : Real) :=
      congrArg Subtype.val equalObservers
    norm_num [c1, c2] at equalValues
  have sameDivisor : ∀ s : Complex,
      meromorphicOrderAt (observerSpectralZeta P1 c1) s =
        meromorphicOrderAt (observerSpectralZeta P2 c2) s := by
    intro s
    exact allObservers P1 c1 P2 c2 s
  refine ⟨allObservers, ⟨P1, c1, P2, c2, differentP, differentC, sameDivisor⟩, ?_⟩
  rintro ⟨recover, recoversRatio⟩
  have sameObservation :
      (fun s => meromorphicOrderAt (observerSpectralZeta P1 c1) s) =
        fun s => meromorphicOrderAt (observerSpectralZeta P2 c2) s := by
    funext s
    exact sameDivisor s
  have ratioEquality :
      (P1 : Real) / (c1 : Real) = (P2 : Real) / (c2 : Real) := by
    calc
      (P1 : Real) / (c1 : Real) =
          recover (fun s => meromorphicOrderAt (observerSpectralZeta P1 c1) s) :=
        (recoversRatio P1 c1).symm
      _ = recover (fun s => meromorphicOrderAt (observerSpectralZeta P2 c2) s) :=
        congrArg recover sameObservation
      _ = (P2 : Real) / (c2 : Real) := recoversRatio P2 c2
  norm_num [P1, c1, P2, c2] at ratioEquality

#print axioms observer_scale_not_recoverable_from_spectral_divisor

end

end D5.S3.Analytic.Adelic.ObserverScaleDivisorNonidentifiability
