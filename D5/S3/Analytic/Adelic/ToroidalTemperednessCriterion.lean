/- GID: D5/S3/Analytic/Adelic/ToroidalTemperednessCriterion
   generality: G
   mirror-B: D5/B/S3/Analytic/Adelic/ToroidalTemperednessCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Strip RH is equivalent to temperedness of every invisible Eisenstein parameter. -/

import D5.S3.Weil.ZetaRvm.CountByIntegral

/- Library-search audit trail (2026-08-29):
   * Repository searches for toroidal temperedness, Eisenstein temperedness,
     and RH equivalences found no exact frozen owner. The frozen scattering-line
     theorem has a different right-hand condition and is not a bind target.
   * The frozen theorem
     `Zeta23.RvM.completedRiemannZeta_eq_zero_iff` is the exact zero-locus
     constituent: it identifies the completed reading with the canonical
     nontrivial strip-zero predicate, and is applied in both directions.
   * Pinned Mathlib has no toroidal automorphic theorem. `mul_eq_zero` is the
     exact algebraic constituent used to recover the completed-zeta zero from
     the constructed period family.
   * Body-shape searches for completed-zeta times a twist family and for a
     toroidal-temperedness equivalence found no D5 primitive. The period and
     normalized spectral parameter are inlined, so no `def` or `abbrev` is
     introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Adelic.ToroidalTemperednessCriterion

open Zeta23
open Zeta23.RvM

/--
The strip-native Riemann hypothesis is equivalent to temperedness of every
nontrivial Eisenstein parameter whose completed-zeta twist periods all vanish.
Temperedness is exposed by the normalized parameter `s - 1 / 2` having zero
real part.
-/
theorem rh_iff_all_toroidal_eisenstein_tempered {Index : Type*}
    (twist : Index -> ℂ -> ℂ)
    (pointwiseNonvanishing : ∀ s, ∃ index, twist index s ≠ 0) :
    (∀ s, IsNontrivialZero s -> s.re = 1 / 2) ↔
      ∀ s,
        (∀ index, completedRiemannZeta s * twist index s = 0) ->
          (s - (1 / 2 : ℂ)).re = 0 := by
  constructor
  · intro hRH s invisible
    obtain ⟨index, twistNonzero⟩ := pointwiseNonvanishing s
    have completedZero : completedRiemannZeta s = 0 :=
      (mul_eq_zero.mp (invisible index)).resolve_right twistNonzero
    have line := hRH s (completedRiemannZeta_eq_zero_iff.mp completedZero)
    norm_num at line ⊢
    linarith
  · intro tempered s nontrivialZero
    have completedZero : completedRiemannZeta s = 0 :=
      completedRiemannZeta_eq_zero_iff.mpr nontrivialZero
    have invisible : ∀ index,
        completedRiemannZeta s * twist index s = 0 := by
      intro index
      rw [completedZero, zero_mul]
    have normalized := tempered s invisible
    norm_num at normalized ⊢
    linarith

example :
    ∃ twist : Unit -> ℂ -> ℂ,
      ∀ s, ∃ index, twist index s ≠ 0 := by
  exact ⟨fun _ _ => 1, fun _ => ⟨(), one_ne_zero⟩⟩

example : Nonempty ℂ := ⟨0⟩

#print axioms rh_iff_all_toroidal_eisenstein_tempered

end D5.S3.Analytic.Adelic.ToroidalTemperednessCriterion
