/- GID: D5/S1/Solenoid/ThroatTransitionCocycle
   generality: I
   mirror-B: D5/B/S1/Solenoid/ThroatTransitionCocycle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equal visible projections determine unique hidden-fiber differences, which compose additively. -/

import D5.S1.Dynamics.UniversalSolenoid
import D5.S1.Solenoid.HiddenFiberCompact

namespace D5.S1.Solenoid.ThroatTransitionCocycle

open D5.S1.Dynamics

/-- Three lifts with equal visible projections have unique pointwise differences
in the hidden fiber, and the direct difference is the sum of the two successive
differences. Both the hidden-fiber differences and their cocycle law are
conclusions. -/
theorem three_lift_difference_cocycle
    {U : Type*}
    (sAlpha sBeta sGamma : U → UniversalSolenoid)
    (hAlphaBeta : UniversalSolenoid.projection ∘ sAlpha =
      UniversalSolenoid.projection ∘ sBeta)
    (hBetaGamma : UniversalSolenoid.projection ∘ sBeta =
      UniversalSolenoid.projection ∘ sGamma) :
    ∃ kAlphaBeta kBetaGamma kAlphaGamma : U → UniversalSolenoid,
      ((∀ u, UniversalSolenoid.projection (kAlphaBeta u) = 0) ∧
        (∀ u, sBeta u = sAlpha u + kAlphaBeta u) ∧
        ∀ k : U → UniversalSolenoid,
          ((∀ u, UniversalSolenoid.projection (k u) = 0) ∧
            (∀ u, sBeta u = sAlpha u + k u)) → k = kAlphaBeta) ∧
      ((∀ u, UniversalSolenoid.projection (kBetaGamma u) = 0) ∧
        (∀ u, sGamma u = sBeta u + kBetaGamma u) ∧
        ∀ k : U → UniversalSolenoid,
          ((∀ u, UniversalSolenoid.projection (k u) = 0) ∧
            (∀ u, sGamma u = sBeta u + k u)) → k = kBetaGamma) ∧
      ((∀ u, UniversalSolenoid.projection (kAlphaGamma u) = 0) ∧
        (∀ u, sGamma u = sAlpha u + kAlphaGamma u) ∧
        ∀ k : U → UniversalSolenoid,
          ((∀ u, UniversalSolenoid.projection (k u) = 0) ∧
            (∀ u, sGamma u = sAlpha u + k u)) → k = kAlphaGamma) ∧
      ∀ u, kAlphaGamma u = kAlphaBeta u + kBetaGamma u := by
  let kAlphaBeta := fun u => sBeta u - sAlpha u
  let kBetaGamma := fun u => sGamma u - sBeta u
  let kAlphaGamma := fun u => sGamma u - sAlpha u
  refine ⟨kAlphaBeta, kBetaGamma, kAlphaGamma, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro u
      rw [UniversalSolenoid.projection.map_sub]
      exact sub_eq_zero.mpr (congrFun hAlphaBeta u).symm
    · intro u
      simp [kAlphaBeta]
    · intro k hk
      funext u
      apply add_left_cancel (a := sAlpha u)
      calc
        sAlpha u + k u = sBeta u := (hk.2 u).symm
        _ = sAlpha u + kAlphaBeta u := by simp [kAlphaBeta]
  · refine ⟨?_, ?_, ?_⟩
    · intro u
      rw [UniversalSolenoid.projection.map_sub]
      exact sub_eq_zero.mpr (congrFun hBetaGamma u).symm
    · intro u
      simp [kBetaGamma]
    · intro k hk
      funext u
      apply add_left_cancel (a := sBeta u)
      calc
        sBeta u + k u = sGamma u := (hk.2 u).symm
        _ = sBeta u + kBetaGamma u := by simp [kBetaGamma]
  · refine ⟨?_, ?_, ?_⟩
    · intro u
      rw [UniversalSolenoid.projection.map_sub]
      exact sub_eq_zero.mpr ((congrFun hBetaGamma u).symm.trans
        (congrFun hAlphaBeta u).symm)
    · intro u
      simp [kAlphaGamma]
    · intro k hk
      funext u
      apply add_left_cancel (a := sAlpha u)
      calc
        sAlpha u + k u = sGamma u := (hk.2 u).symm
        _ = sAlpha u + kAlphaGamma u := by simp [kAlphaGamma]
  · intro u
    simp [kAlphaBeta, kBetaGamma, kAlphaGamma]

end D5.S1.Solenoid.ThroatTransitionCocycle
