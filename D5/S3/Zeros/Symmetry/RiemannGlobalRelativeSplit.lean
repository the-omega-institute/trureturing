/- GID: D5/S3/Zeros/Symmetry/RiemannGlobalRelativeSplit
   generality: G
   mirror-B: D5/B/S3/Zeros/Symmetry/RiemannGlobalRelativeSplit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Split critical-line localization into global reflection and relative coherence. -/

import D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction
import D5.S3.Weil.ZetaCore.Statement

/-!
# Global Reflection and Relative Coherence

The transverse support records the horizontal displacements of all classical
nontrivial zeta zeros in the open critical strip. The two source predicates are
represented directly: closure under displacement negation and subsingletonness
of that same support.

Library-search audit trail (2026-09-04):

* Exact D5 searches for the three source names and the complete equivalence
  found no frozen owner. Shape searches found `Zeta23.IsNontrivialZero`,
  `Zeta23.RH_implies_on_line`, and
  `golden_right_half_strip_implies_rh`; all three are reused here.
* Pinned Mathlib defines `RiemannHypothesis` and the Riemann zeta function, but
  searches for the transverse-support split and equivalences involving its
  hypothesis declaration found no exact theorem.
* Searches across the other installed Lean packages found no exact hit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Zeros.Symmetry.RiemannGlobalRelativeSplit

open D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction

/-- Horizontal displacements from one half of the nontrivial zeta zeros in the
open critical strip. -/
def transverseSupport : Set Real :=
  {d | exists rho : Complex,
    Zeta23.IsNontrivialZero rho /\
      d = rho.re - (1 : Real) / 2}

/-- The global transverse support is closed under reflection through zero. -/
def GlobalEvenRiemannHypothesis : Prop :=
  forall d, d ∈ transverseSupport -> -d ∈ transverseSupport

/-- All nontrivial zeros in the strip have one common horizontal reading. -/
def OneObserverRiemannHypothesis : Prop :=
  transverseSupport.Subsingleton

/-- Critical-line localization is equivalent to global reflection closure
together with relative coherence of the transverse zero support. -/
theorem riemann_hypothesis_iff_global_even_and_one_observer :
    RiemannHypothesis <->
      GlobalEvenRiemannHypothesis /\ OneObserverRiemannHypothesis := by
  change RiemannHypothesis <->
    (forall d, d ∈ transverseSupport -> -d ∈ transverseSupport) /\
      transverseSupport.Subsingleton
  constructor
  · intro hRiemann
    constructor
    · intro d hd
      obtain ⟨rho, hrho, hdValue⟩ := hd
      have hLine : rho.re = (1 : Real) / 2 :=
        Zeta23.RH_implies_on_line hRiemann hrho
      refine ⟨rho, hrho, ?_⟩
      linarith
    · intro a ha b hb
      obtain ⟨rho, hrho, haValue⟩ := ha
      obtain ⟨sigma, hsigma, hbValue⟩ := hb
      have hrhoLine : rho.re = (1 : Real) / 2 :=
        Zeta23.RH_implies_on_line hRiemann hrho
      have hsigmaLine : sigma.re = (1 : Real) / 2 :=
        Zeta23.RH_implies_on_line hRiemann hsigma
      linarith
  · rintro ⟨hEven, hOne⟩
    apply golden_right_half_strip_implies_rh
    intro rho hZero hHalf hOneBound
    have hrho : Zeta23.IsNontrivialZero rho :=
      ⟨hZero, by linarith, hOneBound⟩
    let d : Real := rho.re - (1 : Real) / 2
    have hd : d ∈ transverseSupport := ⟨rho, hrho, rfl⟩
    have hneg : -d ∈ transverseSupport := hEven d hd
    have hfixed : d = -d := hOne hd hneg
    dsimp [d] at hfixed
    linarith

#print axioms riemann_hypothesis_iff_global_even_and_one_observer

end D5.S3.Zeros.Symmetry.RiemannGlobalRelativeSplit
