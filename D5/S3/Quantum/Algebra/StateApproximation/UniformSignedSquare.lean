/- GID: D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique, mathlib/module/Mathlib.Analysis.InnerProductSpace.StarOrder, mathlib/module/Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic]
   utility: none
   digest: Uniform signed original-algebra square approximation for whole-state-space extreme real states. -/

import D5.S3.Quantum.Algebra.StateApproximation.IrreducibleBoundedLift
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Convex.Extreme
import D5.S3.Quantum.Algebra.CentralPositiveFunctionalExtension
import D5.S3.Quantum.Algebra.StateApproximation.TauCeti.Analysis.VonNeumannAlgebra.Density
import D5.S3.Quantum.Algebra.StateApproximation.TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Kaplansky
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique

section
/- Source: Physicslib4, immutable revision 2337279e729998740898c4be8f6c7d24f3e641e1, Physicslib4/GNS/Construction.lean.
Modified for ordinary D5 imports and necessary declaration selection; mathematical telescopes are preserved.
Full license and attribution: docs/reports/licenses/state-approximation-suppliers/.
Retire each transplanted result when the actual pinned mathlib contains an equivalent statement,
and replace its consumers with direct imports and applications of that pinned result. -/

/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/

namespace Physicslib4
namespace GNS

open scoped ComplexOrder
open scoped InnerProductSpace

theorem gns_construction.{u} {A : Type u} [CStarAlgebra A] (ω : State A) :
    ∃ (H : Type u)
      (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H),
        IsCyclicVector π Ω ∧
        (∀ a : A, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ) ∧
        (ω.IsFaithful → Function.Injective π) := by
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  haveI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  set f : A →ₚ[ℂ] ℂ := ω.toPositiveLinearMap with hf
  refine ⟨f.GNS, inferInstance, inferInstance, inferInstance, f.gnsStarAlgHom,
    ((f.toPreGNS 1 : f.PreGNS) : f.GNS), ?cyclic, ?rep, ?inj⟩
  case cyclic =>
    unfold IsCyclicVector
    have hkey : ∀ a : A,
        f.gnsStarAlgHom a ((f.toPreGNS 1 : f.PreGNS) : f.GNS)
          = ((f.toPreGNS a : f.PreGNS) : f.GNS) := by
      intro a
      simp [PositiveLinearMap.gnsStarAlgHom_apply,
            PositiveLinearMap.gnsNonUnitalStarAlgHom_apply,
            ContinuousLinearMap.completion_apply_coe,
            PositiveLinearMap.leftMulMapPreGNS_apply,
            PositiveLinearMap.ofPreGNS, PositiveLinearMap.toPreGNS]
      exact congrArg _ (congrArg _ (mul_one _))
    rw [show (Set.range fun a : A => f.gnsStarAlgHom a
              ((f.toPreGNS 1 : f.PreGNS) : f.GNS))
            = Set.range (fun a : A => ((f.toPreGNS a : f.PreGNS) : f.GNS)) by
              ext y
              refine ⟨fun ⟨a, ha⟩ => ⟨a, ?_⟩, fun ⟨a, ha⟩ => ⟨a, ?_⟩⟩
              · simp only at ha; rw [← ha]; exact (hkey a).symm
              · simp only at ha; rw [← ha]; exact (hkey a)]
    have h_range_eq : Set.range (fun a : A => ((f.toPreGNS a : f.PreGNS) : f.GNS))
        = Set.range ((↑) : f.PreGNS → f.GNS) := by
      ext y; constructor
      · rintro ⟨a, rfl⟩; exact ⟨f.toPreGNS a, rfl⟩
      · rintro ⟨p, rfl⟩
        refine ⟨f.ofPreGNS p, ?_⟩
        change ((f.toPreGNS (f.ofPreGNS p) : f.PreGNS) : f.GNS) = (p : f.GNS)
        rw [show f.toPreGNS (f.ofPreGNS p) = p from f.toPreGNS.apply_symm_apply p]
    rw [h_range_eq]
    exact UniformSpace.Completion.denseRange_coe
  case rep =>
    intro a
    have hkey : f.gnsStarAlgHom a ((f.toPreGNS 1 : f.PreGNS) : f.GNS)
        = ((f.toPreGNS a : f.PreGNS) : f.GNS) := by
      simp [PositiveLinearMap.gnsStarAlgHom_apply,
            PositiveLinearMap.gnsNonUnitalStarAlgHom_apply,
            ContinuousLinearMap.completion_apply_coe,
            PositiveLinearMap.leftMulMapPreGNS_apply,
            PositiveLinearMap.ofPreGNS, PositiveLinearMap.toPreGNS]
      exact congrArg _ (congrArg _ (mul_one _))
    rw [hkey, UniformSpace.Completion.inner_coe,
        PositiveLinearMap.preGNS_inner_def]
    change (ω a : ℂ) = f (star (f.ofPreGNS (f.toPreGNS 1)) * f.ofPreGNS (f.toPreGNS a))
    have h1 : f.ofPreGNS (f.toPreGNS 1) = 1 := f.toPreGNS.symm_apply_apply 1
    have h2 : f.ofPreGNS (f.toPreGNS a) = a := f.toPreGNS.symm_apply_apply a
    rw [h1, h2, star_one, one_mul]
    rfl
  case inj =>
    intro hfaith a b hab
    have hsub : f.gnsStarAlgHom (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    have hkey : ∀ c : A, f.gnsStarAlgHom c ((f.toPreGNS 1 : f.PreGNS) : f.GNS)
        = ((f.toPreGNS c : f.PreGNS) : f.GNS) := by
      intro c
      simp [PositiveLinearMap.gnsStarAlgHom_apply,
            PositiveLinearMap.gnsNonUnitalStarAlgHom_apply,
            ContinuousLinearMap.completion_apply_coe,
            PositiveLinearMap.leftMulMapPreGNS_apply,
            PositiveLinearMap.ofPreGNS, PositiveLinearMap.toPreGNS]
      exact congrArg _ (congrArg _ (mul_one _))
    have happ : f.gnsStarAlgHom (a - b) ((f.toPreGNS 1 : f.PreGNS) : f.GNS) = 0 := by
      rw [hsub]; rfl
    rw [hkey] at happ
    have hinner : (⟪((f.toPreGNS (a-b) : f.PreGNS) : f.GNS),
                    ((f.toPreGNS (a-b) : f.PreGNS) : f.GNS)⟫_ℂ) = 0 := by
      rw [happ, inner_zero_right]
    rw [UniformSpace.Completion.inner_coe, PositiveLinearMap.preGNS_inner_def] at hinner
    have hab_eq : f.ofPreGNS (f.toPreGNS (a - b)) = a - b :=
      f.toPreGNS.symm_apply_apply (a - b)
    rw [hab_eq] at hinner
    have h_omega : ω (star (a - b) * (a - b)) = 0 := hinner
    by_contra hne
    have hne' : a - b ≠ 0 := sub_ne_zero.mpr hne
    have hpos := hfaith (a - b) hne'
    rw [h_omega] at hpos
    exact lt_irrefl _ hpos

/-
Uniqueness of the GNS triple: two cyclic representations reproducing ω are unitarily equivalent.

Let (H₁, π₁, Ω₁) and (H₂, π₂, Ω₂) be representations of A with cyclic vectors, both reproducing
the state ω: ω(a) = ⟨Ω₁, π₁(a)Ω₁⟩ = ⟨Ω₂, π₂(a)Ω₂⟩. Then there is a unitary U : H₁ → H₂ with
UΩ₁ = Ω₂ and U π₁(a) = π₂(a) U for all a ∈ A. The map U sends π₁(a)Ω₁ to π₂(a)Ω₂; it preserves
inner products, since both equal ω(a* b), and it extends from the dense orbits to the whole spaces.
So the representation that a state determines is unique, and "the" GNS representation of ω is
well defined up to unitary equivalence.

Implementation note: U is a linear isometric equivalence `H₁ ≃ₗᵢ[ℂ] H₂`, and the two Hilbert
spaces may live in different universes.

Blueprint: thrm:gns-construction-theorem
-/
end GNS
end Physicslib4
end

section
/- Source: Physicslib4, immutable revision 2337279e729998740898c4be8f6c7d24f3e641e1, Physicslib4/GNS/ExtremeState.lean.
Modified for ordinary D5 imports and necessary declaration selection; mathematical telescopes are preserved.
Full license and attribution: docs/reports/licenses/state-approximation-suppliers/.
Retire each transplanted result when the actual pinned mathlib contains an equivalent statement,
and replace its consumers with direct imports and applications of that pinned result. -/

/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
/-!
# Pure states and extreme points of the state space

A state `ω` on a unital C*-algebra `A` is **pure** (`Physicslib4.GNS.IsPure`) when
every positive functional `ψ` dominated by `ω` is a scalar multiple of `ω`. The
convex-geometric counterpart is that `ω` is an **extreme point** of the (convex)
state space: it is not a nontrivial convex combination of two distinct states.

This file proves the equivalence

`IsPure ω ↔ ω.IsExtremePoint`,

a classical characterization of purity. The analytic crux is the identity

`‖φ‖ = (φ 1).re`

for a positive linear functional `φ` on a unital C*-algebra
(`norm_eq_re_apply_one_of_positive`), obtained from `PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one`
using the local spectral order and positivity of squares.
It is the bridge that lets us normalize positive functionals into states and back.

* `‖ψ‖ = (ψ 1).re` recovers the normalization `ω 1 = 1` for states
  (`State.apply_one`), pins the convex coefficients in the forward direction, and
  rescales the two pieces `ψ` and `ω - ψ` into states in the backward direction.
-/

namespace Physicslib4
namespace GNS

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A]

private lemma complex_ofReal_nonneg {r : ℝ} (hr : 0 ≤ r) : (0 : ℂ) ≤ (r : ℂ) :=
  Complex.nonneg_iff.mpr ⟨by simpa using hr, by simp⟩

private lemma complex_inv_ofReal_nonneg {r : ℝ} (hr : 0 ≤ r) : (0 : ℂ) ≤ ((r : ℂ))⁻¹ := by
  rw [← Complex.ofReal_inv]; exact complex_ofReal_nonneg (inv_nonneg.mpr hr)

private lemma norm_inv_ofReal_pos {r : ℝ} (hr : 0 < r) : ‖((r : ℂ))⁻¹‖ = r⁻¹ := by
  rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hr.le]

/- A C*-algebra carrying a state is nontrivial (a state has operator norm `1`,
so the algebra cannot be the zero ring). -/
private lemma nontrivial_of_state (ω : State A) : Nontrivial A := by
  rcases subsingleton_or_nontrivial A with hs | hn
  · exfalso
    have h0 : ω.toContinuousLinearMap = 0 := by
      ext a
      rw [Subsingleton.elim a 0, map_zero, zero_apply]
    have hnorm := ω.isNormalized
    rw [h0, norm_zero] at hnorm
    exact one_ne_zero hnorm.symm
  · exact hn

/- The spectral order is local: no order on the original algebra is assumed. -/
theorem norm_eq_re_apply_one_of_positive [Nontrivial A] {φ : A →L[ℂ] ℂ}
    (hpos : ∀ a : A, 0 ≤ φ (star a * a)) : ‖φ‖ = (φ 1).re := by
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let f : A →P[ℂ] ℂ := PositiveContinuousLinearMap.mk₀ φ fun a ha => by
    obtain ⟨b, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
    exact hpos b
  exact congrArg Complex.re (PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one f)

/- A state evaluates to `1` on the unit: `ω 1 = 1`. The real part is `‖ω‖ = 1`
(via `norm_eq_re_apply_one_of_positive` and normalization), and the imaginary part
vanishes by positivity at `1`. -/
theorem State.apply_one (ω : State A) : (ω 1 : ℂ) = 1 := by
  haveI := nontrivial_of_state ω
  have hpos : ∀ a, 0 ≤ ω.toContinuousLinearMap (star a * a) := ω.isPositive
  have hn := norm_eq_re_apply_one_of_positive hpos
  rw [ω.isNormalized] at hn
  have him : (ω.toContinuousLinearMap 1).im = 0 := by
    have h0 : (0 : ℂ) ≤ ω.toContinuousLinearMap 1 := by
      have := ω.isPositive 1; rwa [star_one, one_mul] at this
    exact (Complex.nonneg_iff.mp h0).2.symm
  apply Complex.ext
  · change (ω.toContinuousLinearMap 1).re = (1 : ℂ).re
    rw [Complex.one_re]; exact hn.symm
  · change (ω.toContinuousLinearMap 1).im = (1 : ℂ).im
    rw [Complex.one_im]; exact him

/-
An extreme point of the state space: ω is not a mixture t ω₁ + (1 − t) ω₂ of two distinct states.

The states of A form a convex set: a mixture of states with weights t and 1 − t is a state
(`State.convexCombo`). ω is extreme when ω = t ω₁ + (1 − t) ω₂ with 0 < t < 1 forces ω₁ = ω₂,
and then both equal ω. Physically, an extreme state carries no classical uncertainty about which
state the system is in. Extremality is equivalent to purity (`isPure_iff_isExtremePoint`) and to
membership in Mathlib's `extremePoints` of the state space
(`mem_extremePoints_iff_isExtremePoint`).

Implementation note: the decomposition is stated pointwise, ω(a) = t ω₁(a) + (1 − t) ω₂(a) for all
a ∈ A, with real t.

Blueprint: def:extreme-state
-/
def State.IsExtremePoint (ω : State A) : Prop :=
  ∀ (ω₁ ω₂ : State A) (t : ℝ), 0 < t → t < 1 →
    (∀ a, (ω a : ℂ) = (t : ℂ) * ω₁ a + (1 - t : ℂ) * ω₂ a) → ω₁ = ω₂

/- **Pure ⟹ extreme point.** If `ω` is pure and decomposes as a convex
combination `ω = t·ω₁ + (1-t)·ω₂` of states with `0 < t < 1`, then `t·ω₁` is a
positive functional dominated by `ω`, hence (by purity) a scalar multiple of `ω`;
evaluating at `1` (where all states give `1`) pins the scalar to `t`, forcing
`ω₁ = ω`, and symmetrically `ω₂ = ω`. -/
theorem isExtremePoint_of_isPure (ω : State A) (hpure : IsPure ω) :
    ω.IsExtremePoint := by
  haveI := nontrivial_of_state ω
  intro ω₁ ω₂ t ht0 ht1 hcomb
  set ψ : A →L[ℂ] ℂ := (t : ℂ) • ω₁.toContinuousLinearMap with hψ_def
  have hψapp : ∀ a, ψ a = (t : ℂ) * ω₁ a := by
    intro a; rw [hψ_def]
    show ((t : ℂ) • ω₁.toContinuousLinearMap) a = (t : ℂ) * ω₁ a
    rw [smul_apply]; rfl
  have htne : (t : ℂ) ≠ 0 := by rw [Ne, Complex.ofReal_eq_zero]; exact ht0.ne'
  have h1tne : (1 - (t : ℂ)) ≠ 0 := by
    have he : (1 - (t : ℂ)) = ((1 - t : ℝ) : ℂ) := by push_cast; ring
    rw [he, Ne, Complex.ofReal_eq_zero]; exact (by linarith : (0 : ℝ) < 1 - t).ne'
  -- `ψ` is positive and dominated by `ω`
  have hψpos : ∀ a, 0 ≤ ψ (star a * a) := by
    intro a; rw [hψapp]
    exact mul_nonneg (complex_ofReal_nonneg ht0.le) (ω₁.isPositive a)
  have hψdom : ∀ a, ψ (star a * a) ≤ ω (star a * a) := by
    intro a
    have hc := hcomb (star a * a)
    have hnn : (0 : ℂ) ≤ (1 - (t : ℂ)) * ω₂ (star a * a) := by
      refine mul_nonneg ?_ (ω₂.isPositive a)
      have he : (1 - (t : ℂ)) = ((1 - t : ℝ) : ℂ) := by push_cast; ring
      rw [he]; exact complex_ofReal_nonneg (by linarith)
    rw [hψapp]
    have hsub : ω (star a * a) - (t : ℂ) * ω₁ (star a * a)
        = (1 - (t : ℂ)) * ω₂ (star a * a) := by rw [hc]; ring
    exact sub_nonneg.mp (hsub ▸ hnn)
  -- purity gives the scalar
  obtain ⟨s, hs⟩ := hpure ψ hψpos hψdom
  have e1 := hs 1
  rw [hψapp, ω₁.apply_one, ω.apply_one, mul_one, mul_one] at e1
  -- `e1 : (t : ℂ) = s`
  have hst : s = (t : ℂ) := e1.symm
  have hω1eq : ∀ a, ω₁ a = ω a := by
    intro a
    have ea := hs a
    rw [hψapp, hst] at ea
    exact mul_left_cancel₀ htne ea
  have hω1 : ω₁ = ω := DFunLike.ext _ _ hω1eq
  have hω2eq : ∀ a, ω₂ a = ω a := by
    intro a
    have hc := hcomb a
    rw [hω1eq a] at hc
    have hh : (1 - (t : ℂ)) * ω₂ a = (1 - (t : ℂ)) * ω a := by linear_combination -hc
    exact mul_left_cancel₀ h1tne hh
  have hω2 : ω₂ = ω := DFunLike.ext _ _ hω2eq
  exact hω1.trans hω2.symm

/- **Extreme point ⟹ pure.** If `ω` is an extreme point and `ψ` is a positive
functional dominated by `ω`, set `λ = (ψ 1).re ∈ [0,1]`. For `λ ∈ (0,1)` the
rescaled functionals `λ⁻¹·ψ` and `(1-λ)⁻¹·(ω-ψ)` are states (normalized via
`norm_eq_re_apply_one_of_positive`) with `ω = λ·(λ⁻¹ψ) + (1-λ)·((1-λ)⁻¹(ω-ψ))`, so
extremality identifies them and forces `ψ = λ·ω`. The boundary cases `λ = 0`
(`ψ = 0`) and `λ = 1` (`ψ = ω`) are handled separately. -/
theorem isPure_of_isExtremePoint (ω : State A) (hext : ω.IsExtremePoint) :
    IsPure ω := by
  haveI := nontrivial_of_state ω
  intro ψ hψpos hψdom
  have hω1 : (ω 1 : ℂ) = 1 := ω.apply_one
  have hψ1 : (0 : ℂ) ≤ ψ 1 := by have := hψpos 1; rwa [star_one, one_mul] at this
  set lam : ℝ := (ψ 1).re with hlam_def
  have hlam_nn : 0 ≤ lam := (Complex.nonneg_iff.mp hψ1).1
  have hψnorm : ‖ψ‖ = lam := norm_eq_re_apply_one_of_positive hψpos
  -- `λ ≤ 1`
  have hlam_le1 : lam ≤ 1 := by
    have hd := hψdom 1
    rw [star_one, one_mul] at hd
    have hre := (Complex.le_def.mp hd).1
    rw [hlam_def]
    calc (ψ 1).re ≤ (ω 1).re := hre
      _ = 1 := by rw [hω1, Complex.one_re]
  rcases eq_or_lt_of_le hlam_nn with hlam0 | hlampos
  · -- `λ = 0` : `ψ = 0`
    refine ⟨0, fun a => ?_⟩
    have hψ0 : ψ = 0 := by
      rw [← norm_eq_zero]; rw [hψnorm, ← hlam0]
    rw [hψ0]; simp
  · rcases eq_or_lt_of_le hlam_le1 with hlam1 | hlamlt1
    · -- `λ = 1` : `ψ = ω`
      refine ⟨1, fun a => ?_⟩
      have hpossub : ∀ c, 0 ≤ (ω.toContinuousLinearMap - ψ) (star c * c) := by
        intro c; rw [sub_apply]; exact sub_nonneg.mpr (hψdom c)
      have hval : ((ω.toContinuousLinearMap - ψ) 1).re = 0 := by
        rw [sub_apply, Complex.sub_re]
        change (ω 1).re - (ψ 1).re = 0
        rw [hω1, Complex.one_re, ← hlam_def, hlam1]; ring
      have hnormsub := norm_eq_re_apply_one_of_positive hpossub
      rw [hval] at hnormsub
      have hzero : ω.toContinuousLinearMap - ψ = 0 := norm_eq_zero.mp hnormsub
      have heq : ω.toContinuousLinearMap = ψ := sub_eq_zero.mp hzero
      rw [one_mul]
      change ψ a = ω.toContinuousLinearMap a
      rw [heq]
    · -- `0 < λ < 1` : genuine convex decomposition
      have hlamne : (lam : ℂ) ≠ 0 := by
        rw [Ne, Complex.ofReal_eq_zero]; exact hlampos.ne'
      have h1lampos : 0 < 1 - lam := by linarith
      have h1lam_ofReal_ne : (((1 - lam : ℝ) : ℂ)) ≠ 0 := by
        rw [Ne, Complex.ofReal_eq_zero]; exact h1lampos.ne'
      -- the two rescaled states
      have hpos1 : ∀ a, 0 ≤ (((lam : ℂ))⁻¹ • ψ) (star a * a) := by
        intro a; rw [smul_apply]
        exact mul_nonneg (complex_inv_ofReal_nonneg hlampos.le) (hψpos a)
      have hnorm1 : ‖((lam : ℂ))⁻¹ • ψ‖ = 1 := by
        rw [norm_smul, norm_inv_ofReal_pos hlampos, hψnorm, inv_mul_cancel₀ hlampos.ne']
      have hpossub : ∀ c, 0 ≤ (ω.toContinuousLinearMap - ψ) (star c * c) := by
        intro c; rw [sub_apply]; exact sub_nonneg.mpr (hψdom c)
      have hnormsub : ‖ω.toContinuousLinearMap - ψ‖ = 1 - lam := by
        rw [norm_eq_re_apply_one_of_positive hpossub, sub_apply,
          Complex.sub_re]
        change (ω 1).re - (ψ 1).re = 1 - lam
        rw [hω1, Complex.one_re, ← hlam_def]
      have hpos2 : ∀ a, 0 ≤ ((((1 - lam : ℝ) : ℂ))⁻¹ • (ω.toContinuousLinearMap - ψ))
          (star a * a) := by
        intro a; rw [smul_apply]
        exact mul_nonneg (complex_inv_ofReal_nonneg h1lampos.le) (hpossub a)
      have hnorm2 : ‖(((1 - lam : ℝ) : ℂ))⁻¹ • (ω.toContinuousLinearMap - ψ)‖ = 1 := by
        rw [norm_smul, norm_inv_ofReal_pos h1lampos, hnormsub, inv_mul_cancel₀ h1lampos.ne']
      -- bundle as states
      set s1 : State A := ⟨((lam : ℂ))⁻¹ • ψ, hpos1, hnorm1⟩ with hs1
      set s2 : State A :=
        ⟨(((1 - lam : ℝ) : ℂ))⁻¹ • (ω.toContinuousLinearMap - ψ), hpos2, hnorm2⟩ with hs2
      have hs1a : ∀ a, s1 a = ((lam : ℂ))⁻¹ * ψ a := by
        intro a; rw [hs1]
        change (((lam : ℂ))⁻¹ • ψ) a = ((lam : ℂ))⁻¹ * ψ a
        rw [smul_apply]; rfl
      have hs2a : ∀ a, s2 a = (((1 - lam : ℝ) : ℂ))⁻¹ * (ω a - ψ a) := by
        intro a; rw [hs2]
        change ((((1 - lam : ℝ) : ℂ))⁻¹ • (ω.toContinuousLinearMap - ψ)) a
          = (((1 - lam : ℝ) : ℂ))⁻¹ * (ω a - ψ a)
        rw [smul_apply, sub_apply]; rfl
      have hcancel : (lam : ℂ) * ((lam : ℂ))⁻¹ = 1 := mul_inv_cancel₀ hlamne
      have hcancel2 : (1 - (lam : ℂ)) * (((1 - lam : ℝ) : ℂ))⁻¹ = 1 := by
        rw [show (1 - (lam : ℂ)) = (((1 - lam : ℝ) : ℂ)) from by push_cast; ring]
        exact mul_inv_cancel₀ h1lam_ofReal_ne
      have hdecomp : ∀ a, ω a = (lam : ℂ) * s1 a + (1 - lam : ℂ) * s2 a := by
        intro a
        rw [hs1a, hs2a, ← mul_assoc, ← mul_assoc, hcancel, hcancel2, one_mul, one_mul]
        ring
      have key : s1 = s2 := hext s1 s2 lam hlampos hlamlt1 hdecomp
      refine ⟨(lam : ℂ), fun a => ?_⟩
      have h := hdecomp a
      rw [key] at h
      have he : (lam : ℂ) * s2 a + (1 - lam : ℂ) * s2 a = s2 a := by ring
      rw [he] at h
      rw [← key, hs1a a] at h
      -- `h : ω a = (lam⁻¹ : ℂ) * ψ a`
      rw [h, ← mul_assoc, hcancel, one_mul]

/- **Purity ⟺ extreme point of the state space.** -/
theorem isPure_iff_isExtremePoint (ω : State A) : IsPure ω ↔ ω.IsExtremePoint :=
  ⟨isExtremePoint_of_isPure ω, isPure_of_isExtremePoint ω⟩

/- A `*`-automorphism of a C*-algebra as a continuous `ℂ`-linear map; it is
isometric (`StarAlgEquiv.isometry`), hence bounded with norm `≤ 1`. -/
theorem State.toContinuousLinearMap_injective :
    Function.Injective (State.toContinuousLinearMap : State A → (A →L[ℂ] ℂ)) := by
  intro ω₁ ω₂ h
  cases ω₁; cases ω₂
  simp only [State.mk.injEq]
  exact h

variable (A) in
/-
The state space of A: the set of all states, as a subset of the continuous linear functionals.

The states of A form a convex set (`convex_stateSpace`), whose extreme points are the pure
states (`mem_extremePoints_iff_isExtremePoint`, `isPure_iff_isExtremePoint`), so Mathlib's
`Convex` and `extremePoints` apply to it.

Implementation note: the set is the image of `State A` in `A →L[ℂ] ℂ`, regarded as a real vector
space through `NormedSpace.complexToReal`, with the norm topology. The weak-* compact version is
`weakStateSet`; mathematically the Krein–Milman theorem applies to it, and the library proves the
compactness, not the application.

Blueprint: the state space of thrm:state-space-convex-bridge
-/
def stateSpace : Set (A →L[ℂ] ℂ) := Set.range (State.toContinuousLinearMap : State A → _)

/- **The state space is convex.** A real convex combination `a·ω₁ + b·ω₂`
(`a, b ≥ 0`, `a + b = 1`) of two states is again a state, via `State.convexCombo`. -/
theorem mem_extremePoints_iff_isExtremePoint (ω : State A) :
    ω.toContinuousLinearMap ∈ (stateSpace A).extremePoints ℝ ↔ ω.IsExtremePoint := by
  rw [mem_extremePoints]
  constructor
  · rintro ⟨_, h⟩ ω₁ ω₂ t ht0 ht1 hdec
    have hseg : ω.toContinuousLinearMap
        ∈ openSegment ℝ ω₁.toContinuousLinearMap ω₂.toContinuousLinearMap := by
      refine ⟨t, 1 - t, ht0, by linarith, by ring, ?_⟩
      refine ContinuousLinearMap.ext fun c => ?_
      have hc := hdec c
      simp only [add_apply, smul_apply,
        Complex.real_smul]
      change (t : ℂ) * ω₁ c + ((1 - t : ℝ) : ℂ) * ω₂ c = ω c
      rw [hc]
      push_cast
      ring
    obtain ⟨he₁, he₂⟩ :=
      h ω₁.toContinuousLinearMap ⟨ω₁, rfl⟩ ω₂.toContinuousLinearMap ⟨ω₂, rfl⟩ hseg
    exact State.toContinuousLinearMap_injective (he₁.trans he₂.symm)
  · intro hext
    refine ⟨⟨ω, rfl⟩, ?_⟩
    rintro _ ⟨ω₁, rfl⟩ _ ⟨ω₂, rfl⟩ ⟨a, b, ha, hb, hab, heq⟩
    have hdec : ∀ c, (ω c : ℂ) = (a : ℂ) * ω₁ c + (1 - a : ℂ) * ω₂ c := by
      intro c
      have hc := congrArg (fun φ : A →L[ℂ] ℂ => φ c) heq
      simp only [add_apply, smul_apply,
        Complex.real_smul] at hc
      change (a : ℂ) * ω₁ c + (b : ℂ) * ω₂ c = ω c at hc
      rw [← hc]
      have hb' : b = 1 - a := by linarith
      rw [hb']; push_cast; ring
    have hω : ω₁ = ω₂ := hext ω₁ ω₂ a ha (by linarith) hdec
    subst hω
    have hcombo : ω₁.toContinuousLinearMap = ω.toContinuousLinearMap := by
      rw [← heq]
      refine ContinuousLinearMap.ext fun c => ?_
      rw [add_apply, smul_apply,
        smul_apply, Complex.real_smul, Complex.real_smul,
        ← add_mul, ← Complex.ofReal_add, hab, Complex.ofReal_one, one_mul]
    exact ⟨hcombo, hcombo⟩

variable {B : Type*} [CStarAlgebra B]

/- A unital `*`-homomorphism of C*-algebras as a continuous `ℂ`-linear map; it is
contractive (`‖π a‖ ≤ ‖a‖`, `NonUnitalStarAlgHom.norm_apply_le`), hence bounded with
norm `≤ 1`. -/
end GNS
end Physicslib4

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped ComplexOrder InnerProductSpace ComplexStarModule
open Physicslib4.GNS

namespace D5.S3.Quantum.Algebra.StateApproximation.ReconstructedStateGNS
universe u
variable {A : Type u} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]

def IsRealState (β : selfAdjoint A →ₗ[ℝ] ℝ) : Prop :=
  (∀ a : selfAdjoint A, 0 ≤ (a : A) → 0 ≤ β a) ∧ β 1 = 1

def realStateSpace (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :
    Set (selfAdjoint A →ₗ[ℝ] ℝ) := {β | IsRealState β}

theorem state_abs_le (β : selfAdjoint A →ₗ[ℝ] ℝ) (hβ : IsRealState β)
    (a : selfAdjoint A) : |β a| ≤ ‖a‖ := by
  have hm : Monotone β := by
    intro x y hxy
    have h := hβ.1 (y - x) (show 0 ≤ ((y - x : selfAdjoint A) : A) from sub_nonneg.mpr hxy)
    simpa only [map_sub, sub_nonneg] using h
  have hu : a ≤ ‖a‖ • (1 : selfAdjoint A) := by
    change (a : A) ≤ ‖a‖ • (1 : A)
    simpa [Algebra.algebraMap_eq_smul_one] using a.property.le_algebraMap_norm_self
  have hl : -(‖a‖ • (1 : selfAdjoint A)) ≤ a := by
    change -(‖a‖ • (1 : A)) ≤ (a : A)
    simpa [Algebra.algebraMap_eq_smul_one] using a.property.neg_algebraMap_norm_le_self
  have h1 := hm hu
  have h2 := hm hl
  simp only [map_smul, map_neg, hβ.2, smul_eq_mul, mul_one] at h1 h2
  exact abs_le.mpr ⟨h2, h1⟩

def realCLM (β : selfAdjoint A →ₗ[ℝ] ℝ) (hβ : IsRealState β) :
    StrongDual ℝ (selfAdjoint A) :=
  β.mkContinuous 1 (fun a => by simpa only [Real.norm_eq_abs, one_mul] using state_abs_le β hβ a)

theorem realCLM_norm_le (β : selfAdjoint A →ₗ[ℝ] ℝ) (hβ : IsRealState β) :
    ‖realCLM β hβ‖ ≤ 1 :=
  β.mkContinuous_norm_le zero_le_one (fun a => by
    simpa only [Real.norm_eq_abs, one_mul] using state_abs_le β hβ a)

def complexStateSpace (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :
    Set (A →L[ℂ] ℂ) := {φ | (∀ a : A, 0 ≤ a → 0 ≤ φ a) ∧ φ 1 = 1}

def restriction : (A →L[ℂ] ℂ) →ₗ[ℝ] (selfAdjoint A →ₗ[ℝ] ℝ) where
  toFun φ := {
    toFun a := (φ (a : A)).re
    map_add' a b := by simp
    map_smul' c a := by simp }
  map_add' φ ψ := by ext a; simp
  map_smul' c φ := by ext a; simp

def positiveMap (φ : A →L[ℂ] ℂ) (hφ : φ ∈ complexStateSpace A) : A →P[ℂ] ℂ :=
  PositiveContinuousLinearMap.mk₀ φ hφ.1

theorem state_moment (φ : A →L[ℂ] ℂ) (hφ : φ ∈ complexStateSpace A)
    (a : selfAdjoint A) : φ (a : A) = (restriction φ a : ℂ) := by
  exact (Complex.re_eq_ofReal_of_isSelfAdjoint (a.property.map' (positiveMap φ hφ))).mp rfl

theorem restriction_mem (φ : A →L[ℂ] ℂ) (hφ : φ ∈ complexStateSpace A) :
    restriction φ ∈ realStateSpace A := by
  refine ⟨fun a ha => (Complex.nonneg_iff.mp (hφ.1 a ha)).1, ?_⟩
  change (φ (1 : A)).re = 1
  rw [hφ.2, Complex.one_re]

theorem ext_selfAdjoint (φ ψ : A →L[ℂ] ℂ)
    (h : ∀ a : selfAdjoint A, φ (a : A) = ψ (a : A)) : φ = ψ := by
  ext a
  rw [← realPart_add_I_smul_imaginaryPart a]
  simp only [map_add, map_smul, h]

theorem exists_extension (β : selfAdjoint A →ₗ[ℝ] ℝ) (hβ : IsRealState β) :
    ∃ φ : A →L[ℂ] ℂ, φ ∈ complexStateSpace A ∧
      ∀ a : selfAdjoint A, φ (a : A) = (β a : ℂ) := by
  obtain ⟨p, n, hread, hmass⟩ :=
    D5.S3.Quantum.Algebra.CentralPositiveFunctionalExtension.exists_positive_extensions_norm_additive
      (selfAdjoint.submodule ℝ A) (fun a => a.property) (realCLM β hβ)
  have hdiff := hread (1 : selfAdjoint A)
  change β 1 = (p (1 : A)).re - (n (1 : A)).re at hdiff
  have hn0 : 0 ≤ (n (1 : A)).re :=
    (Complex.nonneg_iff.mp (n.map_nonneg (show 0 ≤ (1 : A) from zero_le_one))).1
  have hnb := realCLM_norm_le β hβ
  change (p (1 : A)).re + (n (1 : A)).re = ‖realCLM β hβ‖ at hmass
  have hnzero : (n (1 : A)).re = 0 := by
    rw [hβ.2] at hdiff
    linarith! only [hdiff, hmass, hnb, hn0]
  have hnnorm := congrArg Complex.re (PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one n)
  simp only [Complex.ofReal_re] at hnnorm
  have hnCLM : (n : A →L[ℂ] ℂ) = 0 := norm_eq_zero.mp (hnnorm.trans hnzero)
  have nz (a : A) : n a = 0 := congrArg (fun f : A →L[ℂ] ℂ => f a) hnCLM
  have hmom (a : selfAdjoint A) : p (a : A) = (β a : ℂ) := by
    apply (Complex.re_eq_ofReal_of_isSelfAdjoint (a.property.map' p)).mp
    have hr := hread a
    change β a = (p (a : A)).re - (n (a : A)).re at hr
    simpa only [nz, Complex.zero_re, sub_zero] using hr.symm
  refine ⟨p, ⟨fun a ha => p.map_nonneg ha, ?_⟩, hmom⟩
  simpa only [PositiveContinuousLinearMap.coe_toContinuousLinearMap,
    selfAdjoint.val_one, hβ.2, Complex.ofReal_one] using hmom 1

def extension (β : realStateSpace A) : complexStateSpace A :=
  ⟨(exists_extension β.val β.property).choose, (exists_extension β.val β.property).choose_spec.1⟩

theorem extension_moment (β : realStateSpace A) (a : selfAdjoint A) :
    (extension β).val (a : A) = (β.val a : ℂ) :=
  (exists_extension β.val β.property).choose_spec.2 a

theorem restriction_extension (β : realStateSpace A) : restriction (extension β).val = β.val := by
  ext a
  change ((extension β).val (a : A)).re = β.val a
  rw [extension_moment, Complex.ofReal_re]

theorem extension_restriction (φ : complexStateSpace A) :
    extension ⟨restriction φ.val, restriction_mem φ.val φ.property⟩ = φ := by
  apply Subtype.ext
  apply ext_selfAdjoint
  intro a
  exact (extension_moment _ a).trans (state_moment φ.val φ.property a).symm

def realComplexEquiv : realStateSpace A ≃ complexStateSpace A where
  toFun := extension
  invFun φ := ⟨restriction φ.val, restriction_mem φ.val φ.property⟩
  left_inv β := Subtype.ext (restriction_extension β)
  right_inv := extension_restriction

theorem extension_affine_iff (x y z : realStateSpace A) (s t : ℝ) :
    z.val = s • x.val + t • y.val ↔
      (extension z).val = s • (extension x).val + t • (extension y).val := by
  constructor
  · intro h
    apply ext_selfAdjoint
    intro a
    have ha := congrArg (fun f : selfAdjoint A →ₗ[ℝ] ℝ => f a) h
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at ha
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, extension_moment,
      Complex.real_smul, smul_eq_mul]
    exact_mod_cast ha
  · intro h
    have hr := congrArg (fun φ : A →L[ℂ] ℂ => restriction φ) h
    simpa only [map_add, map_smul, restriction_extension] using hr

section Transport
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {S : Set E} {T : Set F}

theorem extreme_forward (e : S ≃ T)
    (haff : ∀ x y z : S, ∀ s t : ℝ,
      z.val = s • x.val + t • y.val ↔ (e z).val = s • (e x).val + t • (e y).val)
    (x : S) (hx : x.val ∈ S.extremePoints ℝ) : (e x).val ∈ T.extremePoints ℝ := by
  rw [mem_extremePoints_iff_left] at hx ⊢
  refine ⟨(e x).property, ?_⟩
  intro y hy z hz hseg
  rcases hseg with ⟨s,t,hs,ht,hst,hcomb⟩
  let y' : S := e.symm ⟨y,hy⟩
  let z' : S := e.symm ⟨z,hz⟩
  have hc : (e x).val = s • (e y').val + t • (e z').val := by
    simpa only [y', z', e.apply_symm_apply] using hcomb.symm
  have hr := (haff y' z' x s t).mpr hc
  have hl := hx.2 y'.val y'.property z'.val z'.property ⟨s,t,hs,ht,hst,hr.symm⟩
  have he : y' = x := Subtype.ext hl
  have he' := congrArg (fun q : S => (e q).val) he
  simpa only [y', e.apply_symm_apply] using he'

theorem extreme_equiv (e : S ≃ T)
    (haff : ∀ x y z : S, ∀ s t : ℝ,
      z.val = s • x.val + t • y.val ↔ (e z).val = s • (e x).val + t • (e y).val)
    (x : S) : x.val ∈ S.extremePoints ℝ ↔ (e x).val ∈ T.extremePoints ℝ := by
  constructor
  · exact extreme_forward e haff x
  · intro h
    have haff' : ∀ x y z : T, ∀ s t : ℝ,
        z.val = s • x.val + t • y.val ↔
        (e.symm z).val = s • (e.symm x).val + t • (e.symm y).val := by
      intro x y z s t
      simpa only [e.apply_symm_apply] using (haff (e.symm x) (e.symm y) (e.symm z) s t).symm
    simpa only [e.symm_apply_apply] using extreme_forward e.symm haff' (e x) h
end Transport

theorem real_complex_extreme_iff (β : realStateSpace A) :
    β.val ∈ (realStateSpace A).extremePoints ℝ ↔
      (extension β).val ∈ (complexStateSpace A).extremePoints ℝ :=
  extreme_equiv realComplexEquiv extension_affine_iff β

def provider (φ : complexStateSpace A) : State A where
  toContinuousLinearMap := φ.val
  isPositive a := φ.property.1 (star a * a) (star_mul_self_nonneg a)
  isNormalized := by
    rw [norm_eq_re_apply_one_of_positive (fun a => φ.property.1 _ (star_mul_self_nonneg a))]
    rw [φ.property.2, Complex.one_re]

theorem provider_mem (ω : State A) : ω.toContinuousLinearMap ∈ complexStateSpace A :=
  ⟨fun a ha => ω.toPositiveLinearMap.map_nonneg ha, ω.apply_one⟩

theorem provider_stateSpace_eq : Physicslib4.GNS.stateSpace A = complexStateSpace A := by
  ext φ
  constructor
  · rintro ⟨ω,rfl⟩
    exact provider_mem ω
  · intro hφ
    exact ⟨provider ⟨φ,hφ⟩,rfl⟩

def originalState (β : realStateSpace A) : State A := provider (extension β)

theorem original_moment (β : realStateSpace A) (a : selfAdjoint A) :
    originalState β (a : A) = (β.val a : ℂ) := extension_moment β a

theorem original_extreme_iff (β : realStateSpace A) :
    β.val ∈ (realStateSpace A).extremePoints ℝ ↔ (originalState β).IsExtremePoint := by
  rw [← mem_extremePoints_iff_isExtremePoint, provider_stateSpace_eq]
  exact real_complex_extreme_iff β

theorem original_pure_iff (β : realStateSpace A) :
    β.val ∈ (realStateSpace A).extremePoints ℝ ↔ IsPure (originalState β) := by
  rw [isPure_iff_isExtremePoint]
  exact original_extreme_iff β

theorem actual_pure_gns (β : selfAdjoint A →ₗ[ℝ] ℝ) (hβ : IsRealState β)
    (hpure : β ∈ (realStateSpace A).extremePoints ℝ) :
    ∃ (φ : A →L[ℂ] ℂ), φ ∈ complexStateSpace A ∧
      (∀ a : selfAdjoint A, φ (a : A) = (β a : ℂ)) ∧
      (∀ ψ : A →L[ℂ] ℂ, ψ ∈ complexStateSpace A →
        (∀ a : selfAdjoint A, ψ (a : A) = (β a : ℂ)) → ψ = φ) ∧
      ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
        (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H),
        ‖Ω‖ = 1 ∧ Dense (Set.range (fun a : A => π a Ω)) ∧
        (∀ a : A, φ a = inner ℂ Ω (π a Ω)) ∧
        (∀ a : selfAdjoint A, inner ℂ Ω (π (a : A) Ω) = (β a : ℂ)) ∧
        (∀ T : H →L[ℂ] H, (∀ a : A, π a * T = T * π a) → ∃ c : ℂ, T = c • 1) := by
  let b : realStateSpace A := ⟨β,hβ⟩
  let ω := originalState b
  have hw : IsPure ω := (original_pure_iff b).mp hpure
  obtain ⟨H, hN, hI, hC, π, Ω, hcyc, hrep, _⟩ := gns_construction ω
  letI := hN
  letI := hI
  letI := hC
  have hn : ‖Ω‖ = 1 := by
    have hunit := hrep (1 : A)
    rw [map_one π, ContinuousLinearMap.one_apply] at hunit
    have hr : (1 : ℝ) = ‖Ω‖ ^ 2 := by
      simpa only [ω.apply_one, RCLike.one_re, ← norm_sq_eq_re_inner] using
        congrArg (RCLike.re : ℂ → ℝ) hunit
    nlinarith [norm_nonneg Ω]
  refine ⟨(extension b).val, (extension b).property, extension_moment b, ?_,
    H, hN, hI, hC, π, Ω, hn, hcyc, hrep, ?_, isIrreducible_of_isPure hcyc hrep hw⟩
  · intro ψ hψ hm
    exact ext_selfAdjoint _ _ (fun a => (hm a).trans (extension_moment b a).symm)
  · intro a
    exact (hrep a).symm.trans (original_moment b a)

end D5.S3.Quantum.Algebra.StateApproximation.ReconstructedStateGNS

end
end

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
noncomputable section
open Filter Topology InnerProductSpace
open scoped ComplexOrder InnerProductSpace ComplexStarModule CStarAlgebra

namespace D5.S3.Quantum.Algebra.StateApproximation.UniformSignedSquare
universe u v
variable {A : Type u} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]

/- Original algebra square, with its actual selfadjoint subtype. -/
def square (e : selfAdjoint A) : selfAdjoint A := ⟨(e : A)^2, e.property.pow 2⟩
/- The real sign, used only with a nonzero state reading. -/
def sigma (r : ℝ) : ℝ := if 0 < r then 1 else -1
/- The signed square is formed inside the original algebra. -/
def signedSquare (r : ℝ) (e : selfAdjoint A) : selfAdjoint A := sigma r • square e

theorem sigma_sq (r : ℝ) : sigma r * sigma r = 1 := by
  unfold sigma
  split <;> norm_num

theorem sigma_abs (r : ℝ) : |sigma r| = 1 := by
  unfold sigma
  split <;> norm_num

theorem signedSquare_cone (r : ℝ) (e : selfAdjoint A) :
    0 ≤ sigma r • (signedSquare r e : A) := by
  change 0 ≤ sigma r • (sigma r • ((e : A)^2))
  rw [smul_smul, sigma_sq, one_smul]
  exact e.property.sq_nonneg

theorem signedSquare_norm (r : ℝ) (e : selfAdjoint A) {L : ℝ}
    (hL : 0 ≤ L) (he : ‖e‖ ≤ L) : ‖(signedSquare r e : A)‖ ≤ L^2 := by
  change ‖sigma r • ((e : A)^2)‖ ≤ L^2
  rw [norm_smul, Real.norm_eq_abs, sigma_abs, one_mul]
  change ‖(e : A)‖ ≤ L at he
  exact (norm_pow_le (e : A) 2).trans (by nlinarith [norm_nonneg (e : A)])

section Representation
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/- The original square reading is exactly the represented vector norm squared. -/
theorem square_reading (β : selfAdjoint A →ₗ[ℝ] ℝ)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H)
    (hm : ∀ a : selfAdjoint A, inner ℂ Ω (π (a : A) Ω) = (β a : ℂ))
    (d : selfAdjoint A) : Real.sqrt (β (square d)) = ‖π (d : A) Ω‖ := by
  have hp : (π (d : A)).adjoint = π (d : A) :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mp (d.property.map π)
  have hn : ‖π (d : A) Ω‖^2 = (inner ℂ Ω (π ((d : A)^2) Ω)).re := by
    simpa only [map_pow, pow_two, map_mul, ContinuousLinearMap.mul_def, hp,
      RCLike.re_eq_complex_re] using
      (π (d : A)).apply_norm_sq_eq_inner_adjoint_right Ω
  have hb : β (square d) = ‖π (d : A) Ω‖^2 := by
    rw [hn]
    exact (congrArg Complex.re (hm (square d))).symm
  rw [hb, Real.sqrt_sq (norm_nonneg _)]

/- A positive rank-one endpoint has a selfadjoint square root with the required signed action. -/
theorem signed_endpoint (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H)
    (β : selfAdjoint A →ₗ[ℝ] ℝ)
    (hm : ∀ a : selfAdjoint A, inner ℂ Ω (π (a : A) Ω) = (β a : ℂ))
    (k : selfAdjoint A) (hr : β k ≠ 0) :
    ∃ T : H →L[ℂ] H, IsSelfAdjoint T ∧
      T (T Ω) = sigma (β k) • π (k : A) Ω := by
  let r : ℝ := β k
  let v : H := π (k : A) Ω
  have hi : inner ℂ v Ω = (r : ℂ) := by
    exact ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (k.property.map π)) Ω Ω).trans (hm k)
  have hratio : |r|⁻¹ * r = sigma r := by
    by_cases hp : 0 < r
    · rw [abs_of_pos hp, inv_mul_cancel₀ hp.ne', sigma, if_pos hp]
    · have hn : r < 0 := lt_of_le_of_ne (le_of_not_gt hp) hr
      rw [abs_of_neg hn, inv_neg, neg_mul, inv_mul_cancel₀ hr, sigma, if_neg hp]
  let S : H →L[ℂ] H := |r|⁻¹ • rankOne ℂ v v
  have hS : 0 ≤ S := by
    exact smul_nonneg (inv_nonneg.mpr (abs_nonneg r))
      (ContinuousLinearMap.nonneg_iff_isPositive.mpr (isPositive_rankOne_self v))
  have hSO : S Ω = sigma r • v := by
    have hrv : (r : ℂ) • v = r • v := IsScalarTower.algebraMap_smul ℂ r v
    simp only [S, ContinuousLinearMap.smul_apply, rankOne_apply, hi, hrv, smul_smul, hratio]
  refine ⟨CFC.sqrt S, IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg S), ?_⟩
  change (CFC.sqrt S * CFC.sqrt S) Ω = sigma r • v
  rw [CFC.sqrt_mul_sqrt_self S hS, hSO]
end Representation

/- Uniform signed original-square approximation for an arbitrary whole-space extreme real state. -/
theorem uniform_signed_original_square (β : selfAdjoint A →ₗ[ℝ] ℝ)
    (hβ : D5.S3.Quantum.Algebra.StateApproximation.ReconstructedStateGNS.IsRealState β) (hpure : β ∈ (D5.S3.Quantum.Algebra.StateApproximation.ReconstructedStateGNS.realStateSpace A).extremePoints ℝ)
    (k : selfAdjoint A) (hr : β k ≠ 0) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ η : ℝ, 0 < η → ∃ e : selfAdjoint A,
      ‖e‖ ≤ L ∧
      IsSelfAdjoint (signedSquare (β k) e : A) ∧
      0 ≤ sigma (β k) • (signedSquare (β k) e : A) ∧
      ‖(signedSquare (β k) e : A)‖ ≤ L^2 ∧
      Real.sqrt (β (square (signedSquare (β k) e - k))) < η := by
  obtain ⟨φ, hφ, hφβ, huniq, H, hN, hI, hC, π, Ω, hn, hcyc, hrep, hm, hirr⟩ :=
    D5.S3.Quantum.Algebra.StateApproximation.ReconstructedStateGNS.actual_pure_gns β hβ hpure
  letI := hN
  letI := hI
  letI := hC
  obtain ⟨T, hT, hTO⟩ := signed_endpoint π Ω β hm k hr
  obtain ⟨L, hL, happ⟩ := bounded_strong_lift π hirr T hT
  refine ⟨L, hL.le, ?_⟩
  intro η hη
  let δ : ℝ := η / (L + 1)
  have hδ : 0 < δ := div_pos hη (by linarith)
  obtain ⟨e, he, hx, hy⟩ := happ Ω (T Ω) δ hδ
  let E := π (e : A)
  have hE : ‖E‖ ≤ L := (NonUnitalStarAlgHom.norm_apply_le π (e : A)).trans he
  have herr : ‖E (E Ω) - T (T Ω)‖ < η := by
    have hid : E (E Ω) - T (T Ω) =
        E (E Ω - T Ω) + (E (T Ω) - T (T Ω)) := by simp only [map_sub]; abel
    rw [hid]
    calc
      _ ≤ ‖E (E Ω - T Ω)‖ + ‖E (T Ω) - T (T Ω)‖ := norm_add_le _ _
      _ ≤ L * ‖E Ω - T Ω‖ + ‖E (T Ω) - T (T Ω)‖ :=
        add_le_add (ContinuousLinearMap.le_of_opNorm_le E hE _) le_rfl
      _ < L * δ + δ := add_lt_add (mul_lt_mul_of_pos_left hx hL) hy
      _ = η := by dsimp [δ]; field_simp
  refine ⟨e, he, (signedSquare (β k) e).property,
    signedSquare_cone _ _, signedSquare_norm _ _ hL.le he, ?_⟩
  rw [square_reading β π Ω hm]
  have hid : π ((signedSquare (β k) e - k : selfAdjoint A) : A) Ω =
      sigma (β k) • (E (E Ω) - T (T Ω)) := by
    have hsign : sigma (β k) • T (T Ω) = π (k : A) Ω := by
      rw [hTO, smul_smul, sigma_sq, one_smul]
    change π.toAlgHom (sigma (β k) • ((e : A)^2) - (k : A)) Ω = _
    rw [map_sub, π.toAlgHom.map_smul_of_tower, map_pow, pow_two]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.mul_apply, smul_sub, hsign, E]
    rfl
  rw [hid, norm_smul, Real.norm_eq_abs, sigma_abs, one_mul]
  exact herr

end D5.S3.Quantum.Algebra.StateApproximation.UniformSignedSquare
