/- GID: D5/S3/Quantum/Algebra/StateApproximation/IrreducibleBoundedLift
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/StateApproximation/IrreducibleBoundedLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique, mathlib/module/Mathlib.Analysis.InnerProductSpace.StarOrder, mathlib/module/Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic]
   utility: none
   digest: Bounded original-algebra lifts in irreducible C*-representations. -/

import Mathlib.Analysis.CStarAlgebra.Classes
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
import D5.S3.Quantum.Algebra.StateApproximation.TauCeti.Analysis.VonNeumannAlgebra.Density
import D5.S3.Quantum.Algebra.StateApproximation.TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Kaplansky
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique

section
/- Source: Physicslib4, immutable revision 2337279e729998740898c4be8f6c7d24f3e641e1, Physicslib4/GNS/Basic.lean.
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
# Basic definitions for the GNS construction

This file formalises some basic notions used in the GNS construction, following
the AQFT-in-Lean blueprint, section 10.1.

## Main definitions

* `Physicslib4.GNS.State`: a state on an abstract C*-algebra, defined as a
  continuous linear functional that is positive (sends `star a * a` to a
  non-negative complex number) and normalised (operator norm equal to `1`).
  This corresponds to the blueprint label `def:state`.
* `Physicslib4.GNS.State.IsFaithful`: faithfulness of a state, asserting that
  `ω (star a * a) = 0` only when `a = 0`. Also part of `def:state`.
* `Physicslib4.GNS.IsCyclicVector`: a vector `Ω` of a Hilbert space `H` is
  cyclic for a representation `π : A →⋆ₐ[ℂ] (H →L[ℂ] H)` of an algebra `A`
  when the set `{ π a Ω : a ∈ A }` is dense in `H`.
  This corresponds to the blueprint label `def:cyclic-vector`.

## Notes

Mathlib has no packaged `State` type for C*-algebras, so one is introduced
here. The positivity condition is stated using the canonical
partial order on `ℂ` from Mathlib: `0 ≤ z` iff `z.re ≥ 0` and `z.im = 0`.

The blueprint statement of `def:cyclic-vector` only requires `A` to be an
algebra, but `IsCyclicVector` is declared under this file's ambient
`variable (A : Type*) [CStarAlgebra A]`, so in Lean `A` is a unital C*-algebra
(matching every call site in the project). The generality kept here is on the
`H` side: `H` is required only to be a complex Hilbert space, not fixed to the
GNS space of a particular state.
-/

namespace Physicslib4
namespace GNS

open scoped ComplexOrder

variable (A : Type*) [CStarAlgebra A]

/-
A state on a unital C*-algebra A: a positive, normalised continuous linear functional ω : A → ℂ.

The number ω(a) is the expectation value of the observable a in the state ω. Positivity asks
that ω(a* a) ≥ 0 for every a ∈ A, that is, ω(a* a) is real and non-negative. Normalisation asks
that the operator norm ‖ω‖ is 1; for a positive functional on a nonzero algebra the norm is
Re ω(1) (`norm_eq_re_apply_one_of_positive`), so this is the familiar ω(1) = 1. A density matrix
ρ gives the state a ↦ tr(ρa) of the algebra of bounded operators on a Hilbert space, but the
definition needs no Hilbert space: the GNS construction (`gns_construction`) produces one from ω.

Implementation note: the structure extends `A →L[ℂ] ℂ`, and a `FunLike` instance lets one write
`ω a`. Positivity uses Mathlib's partial order on ℂ (`ComplexOrder`), in which 0 ≤ z means that
z is real and non-negative.

Blueprint: def:state
-/
structure State extends A →L[ℂ] ℂ where
  /- Positivity: ω(a* a) is real and non-negative for every a ∈ A. -/
  isPositive : ∀ a : A, 0 ≤ toContinuousLinearMap (star a * a)
  /- Normalisation: the operator norm ‖ω‖ equals 1. -/
  isNormalized : ‖toContinuousLinearMap‖ = 1

namespace State

variable {A}

noncomputable instance : FunLike (State A) A ℂ where
  coe ω := ω.toContinuousLinearMap
  coe_injective := by
    intro ω₁ ω₂ h
    cases ω₁
    cases ω₂
    simp only [mk.injEq]
    exact DFunLike.coe_injective h

/-
A faithful state: ω(a* a) > 0 for every nonzero a ∈ A.

Since ω(a* a) ≥ 0 always, this says that ω(a* a) = 0 only for a = 0: no nonzero observable has
vanishing expectation of a* a. A faithful state has an injective GNS representation
(`gns_construction`), and its cyclic vector is separating (`separating_of_faithful`). On a
matrix algebra the Gibbs state a ↦ tr(e^(−βH) a)/Z is faithful, while a vector state
a ↦ ⟨ψ, aψ⟩ is not: it vanishes on a* a whenever a annihilates the unit vector ψ.

Blueprint: def:state
-/
def IsFaithful (ω : State A) : Prop :=
  ∀ a : A, a ≠ 0 → 0 < ω (star a * a)

/- Repackaging of a state as a Mathlib `PositiveLinearMap`, using the canonical
spectral order on the C*-algebra `A`, so that Mathlib's GNS infrastructure applies. -/
noncomputable def toPositiveLinearMap (ω : State A) [PartialOrder A] [StarOrderedRing A] :
    A →ₚ[ℂ] ℂ where
  toFun := ω.toContinuousLinearMap
  map_add' := by intro x y; exact map_add ω.toContinuousLinearMap x y
  map_smul' := by intro c x; exact map_smul ω.toContinuousLinearMap c x
  monotone' := by
    intro a b hab
    have hba : 0 ≤ b - a := sub_nonneg.mpr hab
    obtain ⟨y, hy⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hba
    have h_pos : 0 ≤ ω.toContinuousLinearMap (b - a) := by
      rw [hy]; exact ω.isPositive y
    have hsub : ω.toContinuousLinearMap (b - a)
        = ω.toContinuousLinearMap b - ω.toContinuousLinearMap a := by
      simp [map_sub]
    rw [hsub] at h_pos
    exact sub_nonneg.mp h_pos

end State

variable {A}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def IsCyclicVector (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H) : Prop :=
  Dense (Set.range fun a : A => π a Ω)

end GNS
end Physicslib4
end

section
/- Source: Physicslib4, immutable revision 2337279e729998740898c4be8f6c7d24f3e641e1, Physicslib4/GNS/Irreducibility.lean.
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
# Irreducibility of representations and Schur's lemma

A `*`-representation `π : A →⋆ₐ[ℂ] (H →L[ℂ] H)` is *irreducible* when its
commutant is trivial: the only bounded operators commuting with every `π a` are
the scalar multiples of the identity. This is the von Neumann (commutant) form of
irreducibility, the operator-algebra counterpart of "no nontrivial closed
invariant subspace".

The central analytic fact is the **topological Schur lemma** for a cyclic
representation: if `T` commutes with all `π a` and its diagonal GNS coefficient
`a ↦ ⟪Ω, T (π a Ω)⟫` is proportional to `a ↦ ⟪Ω, π a Ω⟫`, then `T` is the
corresponding scalar. The proof is pure Hilbert-space analysis: the off-diagonal
coefficients `⟪π b Ω, (T - c) (π a Ω)⟫` all vanish (using the `*`-representation
property and the commutation relation), so `(T - c)` annihilates the dense cyclic
orbit and is therefore zero.

This is the bridge between the commutant and the GNS state: a commutant operator
is a scalar exactly when its GNS coefficient is proportional to the state.
-/

namespace Physicslib4
namespace GNS

open scoped ComplexOrder InnerProductSpace

variable {A : Type*} [CStarAlgebra A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-
An irreducible representation: every bounded operator commuting with all π(a) is a multiple of 1.

The operators that commute with every π(a) form the commutant π(A)'. Irreducibility asks that
π(A)' consist of the scalars c·1 only. For a representation on a Hilbert space this is
equivalent to the absence of a nontrivial closed subspace invariant under all π(a), because the
orthogonal projection onto such a subspace lies in π(A)'; the library uses the commutant form.
A state is pure exactly when its GNS representation is irreducible (`isPure_iff_isIrreducible`),
and π is irreducible exactly when π(A)'' is all of B(H)
(`isIrreducible_iff_gnsVonNeumann_eq_univ`).

Implementation note: on the zero Hilbert space every operator is 0 = 0·1, so every representation
on it is irreducible in this sense; the usual convention excludes H = 0, and results that need a
nonzero space assume it.

Blueprint: def:irreducible-representation
-/
def IsIrreducible (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) : Prop :=
  ∀ T : H →L[ℂ] H, (∀ a : A, π a * T = T * π a) → ∃ c : ℂ, T = c • 1

/- **Topological Schur lemma (proportional coefficient ⟹ scalar).** Let `Ω` be a
cyclic vector for `π`. If `T` commutes with every `π a` and the diagonal GNS
coefficient `a ↦ ⟪Ω, T (π a Ω)⟫` equals `c` times `a ↦ ⟪Ω, π a Ω⟫`, then
`T = c • 1`. The key step is that all off-diagonal coefficients
`⟪π b Ω, (T - c) (π a Ω)⟫` vanish, so `(T - c)` kills the dense cyclic orbit. -/
theorem eq_smul_one_of_commute_of_cyclic
    {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {Ω : H} (hcyc : IsCyclicVector π Ω)
    {T : H →L[ℂ] H} (hT : ∀ a : A, π a * T = T * π a)
    {c : ℂ} (hprop : ∀ a : A, ⟪Ω, T (π a Ω)⟫_ℂ = c * ⟪Ω, π a Ω⟫_ℂ) :
    T = c • 1 := by
  have hcycdense : DenseRange (fun a : A => π a Ω) := hcyc
  -- Move `π b` to the other slot of the inner product via the adjoint `π (star b)`.
  have hadj : ∀ (b : A) (w : H), ⟪(π b) Ω, w⟫_ℂ = ⟪Ω, π (star b) w⟫_ℂ := fun b w => by
    rw [map_star, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  have hπ : ∀ b a : A, π (star b) (π a Ω) = π (star b * a) Ω := fun b a => by
    rw [← mul_apply_eq_comp, ← map_mul]
  -- `T` agrees with `c • ·` on the cyclic orbit: all off-diagonal coefficients match.
  have hkey : ∀ a : A, T (π a Ω) = c • (π a Ω) := fun a =>
    hcycdense.eq_of_inner_right ℂ fun b => by
      rw [hadj b (T (π a Ω)), ← mul_apply_eq_comp, hT (star b), mul_apply_eq_comp, hπ b a,
        hprop (star b * a), inner_smul_right, hadj b (π a Ω), hπ b a]
  -- Density + continuity upgrade the agreement to all of `H`.
  have hall := Continuous.ext_on hcycdense T.continuous
    (continuous_const.smul continuous_id) (by rintro _ ⟨a, rfl⟩; exact hkey a)
  exact ContinuousLinearMap.ext fun x => by
    rw [smul_apply, one_apply_eq_self]; exact congrFun hall x

/- **A commutant operator is a scalar iff its GNS coefficient is proportional to
the state.** In a cyclic representation reproducing `ω`, an operator `T` commuting
with all `π a` is a scalar multiple of the identity exactly when its diagonal
coefficient `a ↦ ⟪Ω, T (π a Ω)⟫` is a scalar multiple of `ω`. This is the precise
operator-theoretic bridge between irreducibility and purity: it is the forward
(easy) direction together with the topological Schur lemma. -/
def IsPure (ω : State A) : Prop :=
  ∀ ψ : A →L[ℂ] ℂ, (∀ a : A, 0 ≤ ψ (star a * a)) →
    (∀ a : A, ψ (star a * a) ≤ ω (star a * a)) →
      ∃ t : ℂ, ∀ a : A, ψ a = t * (ω a : ℂ)

/- The **GNS coefficient functional** `a ↦ ⟪Ω, T (π a Ω)⟫` of an operator `T`,
bundled as a continuous linear functional. -/
noncomputable def coeffFunctional (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H) (T : H →L[ℂ] H) :
    A →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun a => ⟪Ω, T (π a Ω)⟫_ℂ
      map_add' := fun a b => by simp only [map_add, add_apply, inner_add_right]
      map_smul' := fun c a => by
        simp only [map_smul, smul_apply, inner_smul_right, RingHom.id_apply, smul_eq_mul] }
    (‖Ω‖ * ‖T‖ * ‖Ω‖)
    (fun a => by
      have hT' : ‖T (π a Ω)‖ ≤ ‖T‖ * (‖a‖ * ‖Ω‖) :=
        (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
          (((π a).le_opNorm Ω).trans (mul_le_mul_of_nonneg_right
            (NonUnitalStarAlgHom.norm_apply_le π a) (norm_nonneg Ω))) (norm_nonneg T))
      exact (norm_inner_le_norm Ω _).trans
        ((mul_le_mul_of_nonneg_left hT' (norm_nonneg Ω)).trans_eq (by ring)))

@[simp] theorem coeffFunctional_apply (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H)
    (T : H →L[ℂ] H) (a : A) :
    coeffFunctional π Ω T a = ⟪Ω, T (π a Ω)⟫_ℂ := rfl

/- On an element `star a * a`, the coefficient functional of a commutant operator
`T` evaluates to `⟪π a Ω, T (π a Ω)⟫`. -/
theorem coeffFunctional_star_mul {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {Ω : H} {T : H →L[ℂ] H}
    (hT : ∀ a : A, π a * T = T * π a) (a : A) :
    coeffFunctional π Ω T (star a * a) = ⟪π a Ω, T (π a Ω)⟫_ℂ := by
  rw [coeffFunctional_apply]
  have hsplit : π (star a * a) Ω = π (star a) (π a Ω) := by
    rw [map_mul, mul_apply_eq_comp]
  rw [hsplit]
  have hcomm : T (π (star a) (π a Ω)) = π (star a) (T (π a Ω)) := by
    rw [← mul_apply_eq_comp, ← hT (star a), mul_apply_eq_comp]
  rw [hcomm]
  have hadjeq : ContinuousLinearMap.adjoint (π a) = π (star a) := by
    rw [← ContinuousLinearMap.star_eq_adjoint, map_star]
  rw [← hadjeq, ContinuousLinearMap.adjoint_inner_right]

/- **Pure ⟹ irreducible, self-adjoint case.** If `ω` is pure (in its cyclic GNS
representation reproducing `ω`) and `S` is a self-adjoint operator commuting with
all `π a`, then `S` is a scalar multiple of the identity. The proof scales `S`
into a positive operator `T = r·S + ½·1` with `0 ≤ T ≤ 1`, whose coefficient
functional is positive and dominated by `ω`; purity forces it proportional to
`ω`, so Schur's lemma makes `T` (hence `S`) a scalar. -/
theorem scalar_of_isSelfAdjoint_of_isPure
    {ω : State A} {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {Ω : H}
    (hcyc : IsCyclicVector π Ω) (hrep : ∀ a : A, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ)
    (hpure : IsPure ω) {S : H →L[ℂ] H} (hSsa : IsSelfAdjoint S)
    (hScomm : ∀ a : A, π a * S = S * π a) :
    ∃ c : ℂ, S = c • 1 := by
  obtain ⟨r, hrpos, hrS⟩ : ∃ r : ℝ, 0 < r ∧ r * ‖S‖ ≤ 2⁻¹ := by
    have hden : (0 : ℝ) < 2 * (‖S‖ + 1) := by positivity
    exact ⟨_, inv_pos.mpr hden, by rw [inv_mul_eq_div, div_le_iff₀ hden]; linarith only []⟩
  -- the scaled operator
  obtain ⟨T, hT_def⟩ : ∃ T : H →L[ℂ] H, T = (r : ℂ) • S + (2⁻¹ : ℂ) • 1 := ⟨_, rfl⟩
  have h1SA : IsSelfAdjoint (1 : H →L[ℂ] H) := .one _
  have h2 : (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) := by rw [Complex.ofReal_inv, Complex.ofReal_ofNat]
  have hhalf : (starRingEnd ℂ) (2⁻¹ : ℂ) = (2⁻¹ : ℂ) := by rw [h2]; exact Complex.conj_ofReal _
  have hTsa : IsSelfAdjoint T := by
    rw [hT_def]
    exact IsSelfAdjoint.add (.smul (Complex.conj_ofReal r) hSsa) (.smul hhalf h1SA)
  have hvv : ∀ v : H, Complex.re ⟪v, v⟫_ℂ = ‖v‖ ^ 2 := fun v => inner_self_eq_norm_sq (𝕜 := ℂ) v
  -- coefficient expansion of `re ⟪T v, v⟫`
  have hTexp : ∀ v : H,
      Complex.re ⟪T v, v⟫_ℂ = r * Complex.re ⟪S v, v⟫_ℂ + 2⁻¹ * ‖v‖ ^ 2 := fun v => by
    simp only [hT_def, add_apply, smul_apply, one_apply_eq_self, inner_add_left, inner_smul_left,
      Complex.add_re, h2, Complex.conj_ofReal, Complex.re_ofReal_mul, hvv]
  -- bound: |r · re ⟪S v, v⟫| ≤ ½‖v‖², hence `0 ≤ re ⟪T v, v⟫ ≤ ‖v‖²`
  have hTb : ∀ v : H, 0 ≤ Complex.re ⟪T v, v⟫_ℂ ∧ Complex.re ⟪T v, v⟫_ℂ ≤ ‖v‖ ^ 2 := fun v => by
    have hb : |r * Complex.re ⟪S v, v⟫_ℂ| ≤ 2⁻¹ * ‖v‖ ^ 2 := by
      rw [abs_mul, abs_of_pos hrpos]
      calc r * |Complex.re ⟪S v, v⟫_ℂ| ≤ r * (‖S‖ * ‖v‖ * ‖v‖) :=
            mul_le_mul_of_nonneg_left
              (((Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)).trans
                (mul_le_mul_of_nonneg_right (S.le_opNorm v) (norm_nonneg v))) hrpos.le
        _ = r * ‖S‖ * ‖v‖ ^ 2 := by ring
        _ ≤ 2⁻¹ * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right hrS (sq_nonneg ‖v‖)
    obtain ⟨hlo, hhi⟩ := abs_le.mp hb
    rw [hTexp v]
    exact ⟨neg_le_iff_add_nonneg.mp hlo, le_trans (add_le_add_left hhi _)
      (show (2 : ℝ)⁻¹ * ‖v‖ ^ 2 + 2⁻¹ * ‖v‖ ^ 2 ≤ ‖v‖ ^ 2 from le_of_eq (by ring))⟩
  -- `1 - T` is positive (and so is `T`, inlined below)
  have hTle : (1 - T).IsPositive := by
    refine ContinuousLinearMap.isPositive_def.mpr ⟨(h1SA.sub hTsa).isSymmetric, fun v => ?_⟩
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, sub_apply, one_apply_eq_self,
      inner_sub_left, map_sub, sub_nonneg]
    exact (hTb v).2.trans (hvv v).ge
  -- the coefficient functional is a dominated positive functional
  have hTcomm : ∀ a : A, π a * T = T * π a := fun a => by
    simp only [hT_def, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul,
      hScomm a]
  -- purity forces `T` to be a scalar
  obtain ⟨t, ht⟩ := hpure (coeffFunctional π Ω T)
    (fun a => by
      rw [coeffFunctional_star_mul hTcomm a]
      exact ContinuousLinearMap.IsPositive.inner_nonneg_right
        (ContinuousLinearMap.isPositive_def.mpr ⟨hTsa.isSymmetric, fun v => (hTb v).1⟩) _)
    (fun a => by
      have hpd := ContinuousLinearMap.IsPositive.inner_nonneg_right hTle (π a Ω)
      rw [sub_apply, one_apply_eq_self, inner_sub_right, sub_nonneg] at hpd
      rwa [coeffFunctional_star_mul hTcomm a, hrep (star a * a), map_mul, mul_apply_eq_comp,
        show π (star a) = ContinuousLinearMap.adjoint (π a) from by
          rw [← ContinuousLinearMap.star_eq_adjoint, map_star],
        ContinuousLinearMap.adjoint_inner_right])
  -- Schur's lemma makes `T`, hence `S`, a scalar
  refine ⟨(r : ℂ)⁻¹ * (t - 2⁻¹), ?_⟩
  rw [mul_smul, sub_smul, ← eq_sub_of_add_eq (hT_def.symm.trans
      (eq_smul_one_of_commute_of_cyclic hcyc hTcomm fun a => by rw [← hrep a]; exact ht a)),
    inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr hrpos.ne')]

/- **Pure ⟹ irreducible.** If a state `ω` is pure, then any cyclic representation
reproducing `ω` (in particular its GNS representation) is irreducible: the only
operators commuting with all `π a` are scalars. The proof decomposes a commuting
operator into its self-adjoint real and imaginary parts (the commutant is
`*`-closed), each of which is a scalar by `scalar_of_isSelfAdjoint_of_isPure`. -/
theorem isIrreducible_of_isPure
    {ω : State A} {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {Ω : H}
    (hcyc : IsCyclicVector π Ω) (hrep : ∀ a : A, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ)
    (hpure : IsPure ω) : IsIrreducible π := by
  intro T hTcomm
  -- the commutant is `*`-closed: `star T` also commutes
  have hstarcomm : ∀ a : A, π a * star T = star T * π a := fun a => by
    simpa only [star_mul, ← map_star, star_star] using (congrArg star (hTcomm (star a))).symm
  -- self-adjoint real and imaginary parts; the commutation relations are `Commute` algebra
  have hPcomm : ∀ a : A, π a * (T + star T) = (T + star T) * π a := fun a =>
    Commute.add_right (hTcomm a) (hstarcomm a)
  have hQSA : IsSelfAdjoint (Complex.I • (star T - T)) := by
    change star (Complex.I • (star T - T)) = Complex.I • (star T - T)
    rw [star_smul, star_sub, star_star, RCLike.star_def, Complex.conj_I,
      neg_smul, ← smul_neg, neg_sub]
  have hQcomm : ∀ a : A,
      π a * (Complex.I • (star T - T)) = (Complex.I • (star T - T)) * π a := fun a =>
    Commute.smul_right (Commute.sub_right (hstarcomm a) (hTcomm a)) _
  -- each part is a scalar
  obtain ⟨p, hp⟩ := scalar_of_isSelfAdjoint_of_isPure hcyc hrep hpure (.add_star_self T) hPcomm
  obtain ⟨q, hq⟩ := scalar_of_isSelfAdjoint_of_isPure hcyc hrep hpure hQSA hQcomm
  -- reconstruct `T` as a scalar: `T + star T` and `T - star T` are both scalars
  have hq' : T - star T = (Complex.I * q) • (1 : H →L[ℂ] H) := by
    rw [← smul_smul, ← hq, smul_smul, Complex.I_mul_I, neg_one_smul, neg_sub]
  refine ⟨2⁻¹ * (p + Complex.I * q), ?_⟩
  have h2T : (2 : ℂ) • T = (p + Complex.I * q) • (1 : H →L[ℂ] H) := by
    rw [two_smul, add_smul, ← hp, ← hq', add_add_sub_cancel]
  rw [mul_smul, ← h2T, inv_smul_smul₀ two_ne_zero]

/-
The von Neumann algebra π(A)'' generated by a representation π, as a set of operators.

The commutant S' of a set S of bounded operators is the set of operators commuting with every
element of S, and S'' = (S')' is its bicommutant. By von Neumann's density theorem every element
of π(A)'' is a strong-operator limit of elements of π(A)
(`exists_forall_norm_sub_lt_of_mem_bicommutant`), so π(A)'' adds to the represented observables
their limits, such as spectral projections. π is irreducible exactly when π(A)'' is all of B(H)
(`isIrreducible_iff_gnsVonNeumann_eq_univ`).

Implementation note: the commutant is `Set.centralizer`, taken in the bounded operators on H.
The name refers to the GNS representation, but π is any representation. The bundled version is
`gnsVonNeumannAlgebra`.
-/
def gnsVonNeumann (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) : Set (H →L[ℂ] H) :=
  Set.centralizer (Set.centralizer (Set.range π))

omit [CStarAlgebra A] in
/- The commutant (`Set.centralizer`) of a self-adjoint set of operators is
itself self-adjoint. -/
private theorem smul_one_mem_centralizer (c : ℂ) (S : Set (H →L[ℂ] H)) :
    (c • 1 : H →L[ℂ] H) ∈ Set.centralizer S :=
  Set.mem_centralizer_iff.mpr fun M _ => by
    rw [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]

/- **An irreducible representation generates a factor.** The von Neumann algebra
`π(A)''` of an irreducible representation has *trivial center*: an operator lies in
the center `π(A)'' ∩ (π(A)'')'` if and only if it is a scalar multiple of the
identity. The center is contained in `(π(A)'')' = π(A)'` (the triple commutant
collapses to the single one), which irreducibility makes the scalars; conversely
scalars are central. -/
theorem gnsVonNeumann_eq_univ_of_isIrreducible {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)}
    (hirr : IsIrreducible π) : gnsVonNeumann π = Set.univ := by
  have hcomm : Set.centralizer (Set.range π) = {T : H →L[ℂ] H | ∃ c : ℂ, T = c • 1} := by
    apply Set.Subset.antisymm
    · intro T hT
      exact hirr T fun a => Set.mem_centralizer_iff.mp hT (π a) ⟨a, rfl⟩
    · rintro _ ⟨c, rfl⟩
      exact smul_one_mem_centralizer c _
  unfold gnsVonNeumann
  rw [hcomm, Set.eq_univ_iff_forall]
  intro T
  rw [Set.mem_centralizer_iff]
  rintro _ ⟨c, rfl⟩
  rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]

/- **Irreducibility is equivalent to generating `\mathcal B(H)`.** A representation
is irreducible iff its generated von Neumann algebra is the whole of `\mathcal B(H)`.
The forward direction is `gnsVonNeumann_eq_univ_of_isIrreducible`; the converse uses
that `\mathcal B(H)` is a *central* `ℂ`-algebra (its center is the scalars): if the
bicommutant is everything then every operator commutes with the commutant, so any
operator commuting with `π(A)` is central, hence scalar. -/
end GNS
end Physicslib4
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


section Representation
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/- Symmetrization supplies an original selfadjoint preimage without faithfulness. -/
theorem selfAdjoint_lift (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    {b : H →L[ℂ] H} (hb : b ∈ π.range) (hbs : IsSelfAdjoint b) :
    ∃ a : selfAdjoint A, π (a : A) = b := by
  obtain ⟨a, rfl⟩ := hb
  let a' : selfAdjoint A := ⟨(2⁻¹ : ℝ) • (a + star a),
    (IsSelfAdjoint.all (2⁻¹ : ℝ)).smul (.add_star_self a)⟩
  refine ⟨a', ?_⟩
  change IsSelfAdjoint (π a) at hbs
  change π.toAlgHom ((2⁻¹ : ℝ) • (a + star a)) = π a
  rw [π.toAlgHom.map_smul_of_tower]
  change (2⁻¹ : ℝ) • π (a + star a) = π a
  rw [map_add π, map_star π, hbs.star_eq, ← two_smul ℝ (π a), smul_smul]
  norm_num

/- CFC truncation gives a bound in the original algebra before any accuracy is chosen. -/
theorem bounded_strong_lift (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hirr : Physicslib4.GNS.IsIrreducible π) (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) :
    ∃ L : ℝ, 0 < L ∧ ∀ (x y : H) (δ : ℝ), 0 < δ →
      ∃ e : selfAdjoint A, ‖e‖ ≤ L ∧
        ‖π (e : A) x - T x‖ < δ ∧ ‖π (e : A) y - T y‖ < δ := by
  let R : ℝ := 1 + ‖T‖
  have hR : 0 < R := by dsimp [R]; positivity
  let B : H →L[ℂ] H := R⁻¹ • T
  have hB : IsSelfAdjoint B := (IsSelfAdjoint.all (R⁻¹ : ℝ)).smul hT
  have hBnorm : ‖B‖ ≤ 1 := by
    dsimp [B]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    apply (inv_mul_le_iff₀ hR).2
    dsimp [R]
    linarith
  let U : H →L[ℂ] H := cfc TauCeti.kaplanskyFunInv B
  have hU : IsSelfAdjoint U := IsSelfAdjoint.cfc
  have hFU : cfc TauCeti.kaplanskyFun U = B :=
    hB.cfc_kaplanskyFun_cfc_kaplanskyFunInv hBnorm
  let q := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  let f : selfAdjoint A → H →Lₚₜ[ℂ] H := fun a => q (π (a : A))
  have himage : Set.range f = q '' ((π.range : Set (H →L[ℂ] H)) ∩
      selfAdjoint (H →L[ℂ] H)) := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨π (a : A), ⟨⟨(a : A), rfl⟩, a.property.map π⟩, rfl⟩
    · rintro ⟨b, ⟨hb, hbs⟩, rfl⟩
      obtain ⟨a, ha⟩ := selfAdjoint_lift π hb hbs
      exact ⟨a, congrArg q ha⟩
  have hclosure : q U ∈ closure (Set.range f) := by
    rw [himage, StarSubalgebra.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint]
    refine ⟨U, ⟨?_, hU⟩, rfl⟩
    have hu : U ∈ Physicslib4.GNS.gnsVonNeumann π := by
      rw [Physicslib4.GNS.gnsVonNeumann_eq_univ_of_isIrreducible hirr]
      exact Set.mem_univ U
    exact hu
  let l : Filter (selfAdjoint A) := Filter.comap f (𝓝 (q U))
  haveI : l.NeBot := by
    apply Filter.comap_neBot
    intro t ht
    obtain ⟨z, hz⟩ := mem_closure_iff_nhds'.mp hclosure t ht
    obtain ⟨a, ha⟩ := z.property
    exact ⟨a, ha ▸ hz⟩
  have hraw : ∀ x : H, Tendsto (fun a : selfAdjoint A => π (a : A) x) l (𝓝 (U x)) := by
    have hf : Tendsto f l (𝓝 (q U)) := tendsto_comap
    exact PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mp hf
  let e : selfAdjoint A → selfAdjoint A := fun a =>
    ⟨R • cfc TauCeti.kaplanskyFun (a : A),
      (IsSelfAdjoint.all R).smul IsSelfAdjoint.cfc⟩
  have henorm : ∀ a, ‖e a‖ ≤ R := by
    intro a
    change ‖R • cfc TauCeti.kaplanskyFun (a : A)‖ ≤ R
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    exact (mul_le_mul_of_nonneg_left (TauCeti.norm_cfc_kaplanskyFun_le (a : A)) hR.le).trans_eq (mul_one R)
  have hemap : ∀ a, π (e a : A) = R • cfc TauCeti.kaplanskyFun (π (a : A)) := by
    intro a
    change π.toAlgHom (R • cfc TauCeti.kaplanskyFun (a : A)) = _
    rw [π.toAlgHom.map_smul_of_tower]
    congr 1
    exact π.map_cfc TauCeti.kaplanskyFun (a : A)
      TauCeti.continuous_kaplanskyFun.continuousOn (by fun_prop)
      a.property (a.property.map π)
  have heconv : ∀ x : H, Tendsto (fun a => π (e a : A) x) l (𝓝 (T x)) := by
    intro x
    have hc := (TauCeti.tendsto_cfc_kaplanskyFun_apply
      (Eventually.of_forall (fun a : selfAdjoint A => a.property.map π)) hU hraw x).const_smul R
    have hRT : R • B = T := by
      dsimp [B]
      rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
    simpa only [hemap, ContinuousLinearMap.smul_apply, hFU, ← ContinuousLinearMap.smul_apply, hRT] using hc
  refine ⟨R, hR, ?_⟩
  intro x y δ hδ
  have hx := (tendsto_iff_norm_sub_tendsto_zero.mp (heconv x)).eventually_lt_const hδ
  have hy := (tendsto_iff_norm_sub_tendsto_zero.mp (heconv y)).eventually_lt_const hδ
  obtain ⟨a, hax, hay⟩ := (hx.and hy).exists
  exact ⟨e a, henorm a, hax, hay⟩

end Representation

end D5.S3.Quantum.Algebra.StateApproximation.UniformSignedSquare
