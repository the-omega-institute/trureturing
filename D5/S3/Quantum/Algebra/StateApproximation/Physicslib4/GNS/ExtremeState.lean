/- GID: D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/ExtremeState
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/ExtremeState
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.CStarAlgebra.Basic, mathlib/module/Mathlib.Analysis.CStarAlgebra.Spectrum, mathlib/module/Mathlib.Analysis.Convex.Extreme]
   utility: none
   digest: Original real states, pure cyclic representations and self-adjoint operator approximation. -/

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
import D5.S3.Quantum.Algebra.StateApproximation.Physicslib4.GNS.Irreducibility
import D5.S3.Quantum.Algebra.StateApproximation.Physicslib4.GNS.CauchySchwarz
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Convex.Extreme

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
(`norm_eq_re_apply_one_of_positive`), obtained from the Cauchy-Schwarz inequality
for positive functionals together with the C*-norm identity `‖star b * b‖ = ‖b‖²`.
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

/- **Norm of a positive functional.** For a positive linear functional `φ` on a
unital C*-algebra, `‖φ‖ = (φ 1).re`. The reverse bound `(φ 1).re ≤ ‖φ‖` is
immediate from `‖1‖ = 1`; the forward bound uses Cauchy-Schwarz with the first
slot equal to `1`, namely `‖φ b‖² ≤ (φ 1).re · (φ (b* b)).re ≤ (φ 1).re · ‖φ‖ · ‖b‖²`,
which gives `‖φ‖² ≤ (φ 1).re · ‖φ‖`. -/
theorem norm_eq_re_apply_one_of_positive [Nontrivial A] {φ : A →L[ℂ] ℂ}
    (hpos : ∀ a : A, 0 ≤ φ (star a * a)) : ‖φ‖ = (φ 1).re := by
  have hNnn : (0 : ℝ) ≤ ‖φ‖ := norm_nonneg _
  have hμnn : 0 ≤ (φ 1).re := (Complex.nonneg_iff.mp (by simpa using hpos 1)).1
  have h1 := φ.le_opNorm (1 : A)
  rw [CStarRing.norm_one, mul_one] at h1
  -- reverse bound: `(φ 1).re ≤ ‖φ‖`
  have hrev : (φ 1).re ≤ ‖φ‖ := ((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans h1
  refine le_antisymm ?_ hrev
  -- key bound from Cauchy-Schwarz
  have hbound : ∀ b : A, ‖φ b‖ ^ 2 ≤ (φ 1).re * ‖φ‖ * ‖b‖ ^ 2 := fun b => by
    have hcs := cauchy_schwarz_inequality (φ : A →ₗ[ℂ] ℂ) (fun c => by simpa using hpos c) 1 b
    simp only [ContinuousLinearMap.coe_coe, star_one, one_mul,
      Complex.normSq_eq_norm_sq] at hcs
    have hb2 := φ.le_opNorm (star b * b)
    rw [CStarRing.norm_star_mul_self] at hb2
    have hbb : (φ (star b * b)).re ≤ ‖φ‖ * (‖b‖ * ‖b‖) :=
      ((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans hb2
    calc ‖φ b‖ ^ 2 ≤ (φ 1).re * (φ (star b * b)).re := hcs
      _ ≤ (φ 1).re * (‖φ‖ * (‖b‖ * ‖b‖)) := mul_le_mul_of_nonneg_left hbb hμnn
      _ = (φ 1).re * ‖φ‖ * ‖b‖ ^ 2 := by ring
  -- forward bound: `‖φ‖ ≤ (φ 1).re`
  rcases eq_or_lt_of_le hNnn with hN0 | hNpos
  · rw [← hN0]; exact hμnn
  · have hCnn : 0 ≤ Real.sqrt ((φ 1).re * ‖φ‖) := Real.sqrt_nonneg _
    have hCsq : Real.sqrt ((φ 1).re * ‖φ‖) ^ 2 = (φ 1).re * ‖φ‖ :=
      Real.sq_sqrt (mul_nonneg hμnn hNnn)
    have hNC : ‖φ‖ ≤ Real.sqrt ((φ 1).re * ‖φ‖) :=
      φ.opNorm_le_bound hCnn fun b => by
        have hle := Real.sqrt_le_sqrt (show ‖φ b‖ ^ 2 ≤ (Real.sqrt ((φ 1).re * ‖φ‖) * ‖b‖) ^ 2 by
          rw [mul_pow, hCsq]; exact hbound b)
        rwa [Real.sqrt_sq (norm_nonneg _),
          Real.sqrt_sq (mul_nonneg hCnn (norm_nonneg _))] at hle
    nlinarith [mul_nonneg (sub_nonneg.mpr hNC) (add_nonneg hCnn hNnn), hCsq, hNpos]

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
