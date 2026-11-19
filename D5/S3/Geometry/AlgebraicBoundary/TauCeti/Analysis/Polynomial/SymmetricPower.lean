/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/Analysis/Polynomial/SymmetricPower
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/Analysis/Polynomial/SymmetricPower
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/Analysis/Polynomial/SymmetricPower.lean.
Adaptation: ordinary D5 import routes; selected declarations retain their original proofs.
License: docs/reports/licenses/TauCeti-LICENSE.txt. Original copyright notices follow.
Retire each transplanted declaration when the actual pinned mathlib supplies an equivalent
statement, and replace its consumers by direct imports and applications of that pinned owner.
This adaptation contributes no independent mathematical novelty or escape credit. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Polynomial.CauchyBound
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Topology.Algebra.Polynomial
public import D5.S3.Geometry.AlgebraicBoundary.TauCeti.RingTheory.Polynomial.SymmetricPower
public import D5.S3.Geometry.AlgebraicBoundary.TauCeti.Topology.Sym.Disjoint
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.Polynomial

/-!
# The elementary symmetric chart is a homeomorphism

`TauCeti.Sym.coeffEquiv` presents the `n`-th symmetric power of an algebraically closed field `K`
as the affine space `Fin n → K`, by sending an unordered `n`-tuple to the lower coefficients of the
monic polynomial having it as its root multiset. That equivalence is pure algebra. This file proves
that, when `K` is a proper normed field — `ℂ` being the case of interest — it is a
**homeomorphism** for the quotient topology of `TauCeti.Sym.instTopologicalSpace`.

Both halves are elementary, but neither is formal:

* the coefficients are polynomial in the roots, so the chart is continuous;
* the roots are *not* a polynomial function of the coefficients, and continuity of the inverse is
  the classical statement that the roots of a monic polynomial depend continuously on its
  coefficients. It is obtained here from **Cauchy's bound** `Polynomial.cauchyBound`: a root of a
  monic polynomial is bounded by its coefficients, so the coefficient map is proper, hence closed,
  and a closed continuous bijection is a homeomorphism.

The retained source supplies the useful proof dependencies. Further exact applications,
including their assumptions and boundary cases, are developed in the owning Blueprint.

-/

public section

-- `Polynomial` is opened outside `namespace TauCeti` so that it names Mathlib's namespace rather
-- than `TauCeti.Polynomial`, which the import above populates.
open Filter Polynomial Topology

namespace TauCeti

namespace Polynomial

/-! ### Analyticity of the coefficients -/

section Analyticity

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

end Analyticity

end Polynomial

namespace Sym

/-! ### Analyticity of the coefficients -/

section Analyticity

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsAlgClosed 𝕜] {n : ℕ}

end Analyticity

/-! ### Continuity of the coefficients -/

section Continuity

variable {ι R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- The coefficients of `∏ i ∈ s, (X - C (f i))` depend continuously on the tuple `f` of roots.

This is the elementary half of the chart: each coefficient is, up to sign, an elementary symmetric
function of the roots, so continuity of the ring operations is all that is used. -/
theorem continuous_coeff_prod_X_sub_C (s : Finset ι) (k : ℕ) :
    Continuous fun f : ι → R => (∏ i ∈ s, (X - C (f i))).coeff k := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty => simpa using continuous_const
  | @insert a s ha ih =>
    cases k with
    | zero =>
      have hpt : (fun f : ι → R => (∏ i ∈ insert a s, (X - C (f i))).coeff 0) =
          fun f => -f a * (∏ i ∈ s, (X - C (f i))).coeff 0 := by
        funext f
        rw [Finset.prod_insert ha, mul_coeff_zero]
        simp
      rw [hpt]
      exact (continuous_apply a).neg.mul (ih 0)
    | succ k =>
      have hpt : (fun f : ι → R => (∏ i ∈ insert a s, (X - C (f i))).coeff (k + 1)) =
          fun f => (∏ i ∈ s, (X - C (f i))).coeff k
            - f a * (∏ i ∈ s, (X - C (f i))).coeff (k + 1) := by
        funext f
        rw [Finset.prod_insert ha, sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul]
      rw [hpt]
      exact (ih k).sub ((continuous_apply a).mul (ih (k + 1)))

end Continuity

section Chart

variable {K : Type*} [NormedField K] [IsAlgClosed K] {n : ℕ}

/-- The coefficient map `(Fin n → K) → (Fin n → K)`, the elementary symmetric chart read on ordered
tuples, is continuous. -/
@[continuity, fun_prop]
theorem continuous_coeffEquiv_comp_ofFn :
    Continuous fun f : Fin n → K => coeffEquiv K n (ofFn f) := by
  refine continuous_pi fun i => ?_
  simp only [coeffEquiv_ofFn_apply]
  exact continuous_coeff_prod_X_sub_C Finset.univ i

/-- **Cauchy's bound** on the symmetric power: the points of an unordered tuple are bounded by one
more than the sup-norm of its elementary symmetric chart, because each of them is a root of the
monic polynomial those coordinates present. -/
theorem norm_le_norm_coeffEquiv_ofFn_add_one (f : Fin n → K) :
    ‖f‖ ≤ ‖coeffEquiv K n (ofFn f)‖ + 1 := by
  have hnonneg : (0 : ℝ) ≤ ‖coeffEquiv K n (ofFn f)‖ + 1 := by positivity
  refine (pi_norm_le_iff_of_nonneg hnonneg).2 fun j => ?_
  have hmonic : (toMonic (ofFn f) : K[X]).Monic := monic_toMonic _
  have hroot : (toMonic (ofFn f) : K[X]).IsRoot (f j) :=
    mem_iff_isRoot.1 (_root_.Sym.mem_coe.2 (mem_ofFn.2 ⟨j, rfl⟩))
  have hcauchy := hroot.norm_lt_cauchyBound hmonic.ne_zero
  have hbound : cauchyBound (toMonic (ofFn f) : K[X]) ≤ ‖coeffEquiv K n (ofFn f)‖₊ + 1 := by
    have hsup : ((Finset.range n).sup fun i => ‖(toMonic (ofFn f) : K[X]).coeff i‖₊)
        ≤ ‖coeffEquiv K n (ofFn f)‖₊ := by
      refine Finset.sup_le fun i hi => ?_
      rw [Finset.mem_range] at hi
      have hcoord := nnnorm_le_pi_nnnorm (coeffEquiv K n (ofFn f)) ⟨i, hi⟩
      rwa [coeffEquiv_apply_eq_coeff] at hcoord
    rw [cauchyBound, hmonic.leadingCoeff, nnnorm_one, div_one, natDegree_toMonic]
    exact add_le_add hsup le_rfl
  have : ‖f j‖₊ < ‖coeffEquiv K n (ofFn f)‖₊ + 1 := hcauchy.trans_le hbound
  simpa using (NNReal.coe_lt_coe.2 this).le

variable [ProperSpace K]

/-- The coefficient map is proper: bounded coefficients force bounded roots, by Cauchy's bound. -/
theorem isProperMap_coeffEquiv_comp_ofFn :
    IsProperMap fun f : Fin n → K => coeffEquiv K n (ofFn f) := by
  rw [isProperMap_iff_tendsto_cocompact]
  refine ⟨continuous_coeffEquiv_comp_ofFn, ?_⟩
  rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
  refine tendsto_atTop_mono (fun f => ?_)
    (tendsto_atTop_add_const_right _ (-1) tendsto_norm_cobounded_atTop)
  have := norm_le_norm_coeffEquiv_ofFn_add_one f
  linarith

/-- The elementary symmetric chart is a closed map. -/
theorem isClosedMap_coeffEquiv : IsClosedMap (coeffEquiv K n) := by
  intro C hC
  have himage : coeffEquiv K n '' C =
      (fun f : Fin n → K => coeffEquiv K n (ofFn f)) '' (ofFn ⁻¹' C) := by
    rw [← Set.image_image (coeffEquiv K n) ofFn (ofFn ⁻¹' C),
      Set.image_preimage_eq _ ofFn_surjective]
  rw [himage]
  exact isProperMap_coeffEquiv_comp_ofFn.isClosedMap _ (hC.preimage continuous_ofFn)

variable (K n)

/-- The **elementary symmetric chart** on the `n`-th symmetric power of a proper algebraically
closed normed field is a homeomorphism onto affine `n`-space: an unordered `n`-tuple is determined,
continuously and with continuous inverse, by the lower coefficients of its monic polynomial.

Continuity of the inverse is the classical continuity of the roots of a monic polynomial in its
coefficients; it comes from `TauCeti.Sym.isProperMap_coeffEquiv_comp_ofFn`, and hence from Cauchy's
bound. -/
noncomputable def coeffHomeomorph : Sym K n ≃ₜ (Fin n → K) :=
  (coeffEquiv K n).toHomeomorphOfContinuousClosed
    (continuous_iff_comp_ofFn.2 continuous_coeffEquiv_comp_ofFn) isClosedMap_coeffEquiv

/-- The chart homeomorphism is the chart equivalence. -/
@[simp]
theorem coeffHomeomorph_apply (s : Sym K n) : coeffHomeomorph K n s = coeffEquiv K n s := by
  simp [coeffHomeomorph]

/-- The inverse chart homeomorphism is the inverse chart equivalence. -/
@[simp]
theorem coeffHomeomorph_symm_apply (f : Fin n → K) :
    ((coeffHomeomorph K n).symm f : Sym K n) = (coeffEquiv K n).symm f := by
  simp [coeffHomeomorph]

variable {K n}

/-- **Continuity of roots on ordered tuples.** Every coefficient tuple close enough to that of the
ordered tuple `a` is the coefficient tuple of an ordered tuple `b` with each `b i` close to `a i`.

This is the continuity of `(coeffHomeomorph K n).symm`, read through the open quotient map
`TauCeti.Sym.ofFn`: it matches the roots with multiplicity, not merely each root to a nearby one. -/
theorem eventually_exists_ofFn_eq_coeffEquiv_symm (a : Fin n → K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c in 𝓝 (coeffEquiv K n (ofFn a)),
      ∃ b : Fin n → K, ofFn b = (coeffEquiv K n).symm c ∧ ∀ i, ‖a i - b i‖ < ε := by
  have hnhds : ofFn '' Metric.ball a ε ∈
      𝓝 ((coeffHomeomorph K n).symm (coeffHomeomorph K n (ofFn a))) := by
    rw [Homeomorph.symm_apply_apply]
    exact isOpenMap_ofFn.image_mem_nhds (Metric.ball_mem_nhds a hε)
  rw [← coeffHomeomorph_apply]
  filter_upwards [(coeffHomeomorph K n).symm.continuous.continuousAt.preimage_mem_nhds hnhds]
    with c ⟨b, hb, hbc⟩
  refine ⟨b, by simpa using hbc, fun i => ?_⟩
  rw [norm_sub_rev, ← dist_eq_norm]
  exact (dist_pi_lt_iff hε).1 hb i

end Chart

end Sym

end TauCeti
