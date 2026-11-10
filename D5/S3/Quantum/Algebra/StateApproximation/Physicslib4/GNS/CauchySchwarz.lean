/- GID: D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/CauchySchwarz
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/CauchySchwarz
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Star.Module, mathlib/module/Mathlib.Analysis.CStarAlgebra.Classes]
   utility: none
   digest: Original real states, pure cyclic representations and self-adjoint operator approximation. -/

/- Source: Physicslib4, immutable revision 2337279e729998740898c4be8f6c7d24f3e641e1, Physicslib4/GNS/CauchySchwarz.lean.
Modified for ordinary D5 imports and necessary declaration selection; mathematical telescopes are preserved.
Full license and attribution: docs/reports/licenses/state-approximation-suppliers/.
Retire each transplanted result when the actual pinned mathlib contains an equivalent statement,
and replace its consumers with direct imports and applications of that pinned result. -/

/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Star.Module

/-!
# Cauchy-Schwarz inequality for positive linear functionals on a *-algebra

This file states the Cauchy-Schwarz inequality for positive linear functionals
on an arbitrary (not necessarily unital, not necessarily normed) *-algebra over
`ℂ`, following the AQFT-in-Lean blueprint section 10.1, label
`lmm:cauchy-schwarz-inequality`.

The hypothesis is **weaker than `Physicslib4.GNS.State`**: we only require a
`ℂ`-linear functional `ω : A →ₗ[ℂ] ℂ` together with positivity
`0 ≤ ω (star a * a)` for all `a`. Continuity and normalisation are *not*
assumed.

## Main statements

* `Physicslib4.GNS.omega_star_swap_conj`: for a positive linear functional `ω`
  on a *-algebra `A`, `ω (star a * b) = star (ω (star b * a))` for all
  `a, b : A`.
* `Physicslib4.GNS.cauchy_schwarz_inequality`: under the same hypotheses,
  `Complex.normSq (ω (star a * b)) ≤ (ω (star a * a)).re * (ω (star b * b)).re`
  for all `a, b : A`.

Both conclusions of the blueprint lemma are recorded; the primary entry-point
is `cauchy_schwarz_inequality`.

## Typeclass setup

The blueprint says "*-algebra"; the minimal Mathlib shape needed to state
the lemma is a complex `*`-ring, i.e. `[NonUnitalNonAssocRing A] [StarRing A]
[Module ℂ A]`. Continuity of `ω` and normalisation are not required.
-/

namespace Physicslib4
namespace GNS

open scoped ComplexOrder

variable {A : Type*} [NonUnitalNonAssocRing A] [StarRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A]

section
omit [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A]

/- Expansion: `ω (star (x + y) * (x + y))` via linearity. -/
private lemma omega_expand_add
    (ω : A →ₗ[ℂ] ℂ) (x y : A) :
    ω (star (x + y) * (x + y))
      = ω (star x * x) + ω (star x * y) + ω (star y * x) + ω (star y * y) := by
  rw [star_add, add_mul, mul_add, mul_add]
  simp [map_add]
  ring

end

/- Expansion: `ω (star (l • a + b) * (l • a + b))` via linearity. -/
private lemma omega_expand_smul_add
    (ω : A →ₗ[ℂ] ℂ) (l : ℂ) (a b : A) :
    ω (star (l • a + b) * (l • a + b))
      = (starRingEnd ℂ l * l) * ω (star a * a)
        + (starRingEnd ℂ l) * ω (star a * b)
        + l * ω (star b * a)
        + ω (star b * b) := by
  rw [star_add, star_smul, add_mul, mul_add, mul_add]
  simp [smul_mul_assoc, mul_smul_comm, map_add, map_smul, smul_eq_mul]
  ring

/-
Hermitian symmetry of a positive functional: ω(a* b) is the complex conjugate of ω(b* a).

A linear functional ω on a complex *-algebra is positive when ω(a* a) ≥ 0 for every a. The form
⟨a, b⟩ = ω(a* b) is then Hermitian, as an inner product is. The proof applies positivity to
a + b and ia + b.

Implementation note: ω is only linear (`A →ₗ[ℂ] ℂ`); continuity, normalisation and a unit are not
needed, and A is any complex *-ring with compatible scalar action.

Blueprint: the Hermitian symmetry used in lmm:cauchy-schwarz-inequality
-/
theorem omega_star_swap_conj
    (ω : A →ₗ[ℂ] ℂ) (hω : ∀ a : A, 0 ≤ ω (star a * a)) (a b : A) :
    ω (star a * b) = star (ω (star b * a)) := by
  set z := ω (star a * b)
  set w := ω (star b * a)
  have hRa_im : (ω (star a * a)).im = 0 := (Complex.nonneg_iff.mp (hω a)).2.symm
  have hRb_im : (ω (star b * b)).im = 0 := (Complex.nonneg_iff.mp (hω b)).2.symm
  have h1 := hω (a + b)
  rw [omega_expand_add ω a b] at h1
  have h1_im : (ω (star a * a) + z + w + ω (star b * b)).im = 0 :=
    (Complex.nonneg_iff.mp h1).2.symm
  have him_zw : z.im + w.im = 0 := by
    simp [Complex.add_im, hRa_im, hRb_im] at h1_im
    linarith
  have h2 := hω ((Complex.I) • a + b)
  rw [omega_expand_smul_add ω Complex.I a b] at h2
  have hII : (starRingEnd ℂ) Complex.I * Complex.I = 1 := by
    rw [Complex.conj_I, neg_mul, Complex.I_mul_I, neg_neg]
  rw [hII, one_mul, Complex.conj_I] at h2
  have h2_im : (ω (star a * a) + -Complex.I * z + Complex.I * w + ω (star b * b)).im = 0 :=
    (Complex.nonneg_iff.mp h2).2.symm
  have hre_zw : z.re = w.re := by
    simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      hRa_im, hRb_im] at h2_im
    linarith
  apply Complex.ext
  · rw [Complex.star_def, Complex.conj_re]; exact hre_zw
  · rw [Complex.star_def, Complex.conj_im]; linarith

/-
The Cauchy–Schwarz inequality |ω(a* b)|² ≤ ω(a* a) ω(b* b) for a positive linear functional ω.

The form ⟨a, b⟩ = ω(a* b) is a positive semi-definite Hermitian form on A, and this is the
Cauchy–Schwarz inequality for it; it holds although the form may be degenerate. It is the key
step in the GNS construction: if ω(n* n) = 0 then ω(b* n) = 0 for every b (`lmm1`). Every state
is a positive functional, so the inequality applies to states.

Implementation note: ω is only linear (`A →ₗ[ℂ] ℂ`), not assumed continuous or normalised, and
A is any complex *-ring with compatible scalar action. Since ω(a* a) and ω(b* b) are non-negative
reals, the right-hand side is written with real parts, and the left-hand side is
`Complex.normSq`.

Blueprint: lmm:cauchy-schwarz-inequality
-/
theorem cauchy_schwarz_inequality
    (ω : A →ₗ[ℂ] ℂ) (hω : ∀ a : A, 0 ≤ ω (star a * a)) (a b : A) :
    Complex.normSq (ω (star a * b))
      ≤ (ω (star a * a)).re * (ω (star b * b)).re := by
  set z := ω (star a * b) with hz_def
  set Ra := (ω (star a * a)).re with hRa_def
  set Rb := (ω (star b * b)).re with hRb_def
  have hRa_nn : 0 ≤ Ra := (Complex.nonneg_iff.mp (hω a)).1
  have hRb_nn : 0 ≤ Rb := (Complex.nonneg_iff.mp (hω b)).1
  have hRa_im : (ω (star a * a)).im = 0 := (Complex.nonneg_iff.mp (hω a)).2.symm
  have hRb_im : (ω (star b * b)).im = 0 := (Complex.nonneg_iff.mp (hω b)).2.symm
  have hRa_eq : ω (star a * a) = (Ra : ℂ) := by
    apply Complex.ext <;> simp [hRa_def, hRa_im]
  have hRb_eq : ω (star b * b) = (Rb : ℂ) := by
    apply Complex.ext <;> simp [hRb_def, hRb_im]
  have hsymm : ω (star b * a) = star z := by
    rw [hz_def, omega_star_swap_conj ω hω a b]; simp
  have key : ∀ l : ℂ, 0 ≤ ((starRingEnd ℂ) l * l) * (Ra : ℂ)
        + (starRingEnd ℂ) l * z + l * star z + (Rb : ℂ) := by
    intro l
    have h := hω (l • a + b)
    rw [omega_expand_smul_add ω l a b, hRa_eq, hRb_eq, ← hz_def, hsymm] at h
    exact h
  by_cases hRa_zero : Ra = 0
  · rw [hRa_zero, zero_mul]
    suffices h : Complex.normSq z = 0 by rw [h]
    by_contra hzne
    have hzpos : 0 < Complex.normSq z :=
      lt_of_le_of_ne (Complex.normSq_nonneg z) (Ne.symm hzne)
    set r : ℝ := (Rb + 1) / Complex.normSq z with hr_def
    have hr_pos : 0 < r := div_pos (by linarith) hzpos
    have hkey := key (-(r : ℂ) * z)
    rw [hRa_zero] at hkey
    have hexpr : (((starRingEnd ℂ) (-(r : ℂ) * z) * (-(r : ℂ) * z)) * ((0:ℝ) : ℂ)
        + (starRingEnd ℂ) (-(r : ℂ) * z) * z + (-(r : ℂ) * z) * star z + (Rb : ℂ)).re
        = -2 * r * Complex.normSq z + Rb := by
      simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply]
      ring
    have hkey_re := (Complex.nonneg_iff.mp hkey).1
    rw [hexpr] at hkey_re
    have hcalc : 2 * r * Complex.normSq z = 2 * (Rb + 1) := by
      rw [hr_def]; field_simp
    linarith
  · have hRa_pos : 0 < Ra := lt_of_le_of_ne hRa_nn (Ne.symm hRa_zero)
    have hkey := key (-z / (Ra : ℂ))
    have hexpr : (((starRingEnd ℂ) (-z / (Ra : ℂ)) * (-z / (Ra : ℂ))) * (Ra : ℂ)
        + (starRingEnd ℂ) (-z / (Ra : ℂ)) * z + (-z / (Ra : ℂ)) * star z + (Rb : ℂ)).re
        = -Complex.normSq z / Ra + Rb := by
      simp only [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
        Complex.normSq_apply, Complex.star_def]
      field_simp
      ring
    have hkey_re := (Complex.nonneg_iff.mp hkey).1
    rw [hexpr] at hkey_re
    have hineq : Complex.normSq z / Ra ≤ Rb := by
      have hneg : -Complex.normSq z / Ra = -(Complex.normSq z / Ra) := by ring
      linarith [hneg]
    rw [mul_comm]
    exact (div_le_iff₀ hRa_pos).mp hineq

end GNS
end Physicslib4
