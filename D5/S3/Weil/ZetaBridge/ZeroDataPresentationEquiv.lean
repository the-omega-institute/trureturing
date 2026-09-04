/- GID: D5/S3/Weil/ZetaBridge/ZeroDataPresentationEquiv
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/ZeroDataPresentationEquiv
   mirror-E: none(waiver:canonical-zero-presentation-interface)
   anchors: []
   digest: Expose the unique zero-preserving reindexing between exhaustive ZeroData presentations and prove symmetry equivariance. -/

import D5.S3.Weil.ZetaBridge.ZeroSumEnumerationInvariance
import D5.S3.Zeros.Symmetry.ZeroSymmetryAction

/-!
# Canonical equivalence between `ZeroData` presentations

Every `ZeroData` value is a duplicate-free exhaustive natural-number
presentation of the same set of nontrivial zeta zeros.  This module exposes the
reindexing that was previously proof-local in the zero-sum invariance theorem,
and proves that it transports analytic multiplicities, reflection,
conjugation, and the same-height mirror involution.

The equivalence is canonical only in the presentation sense: it is the unique
index equivalence preserving the represented complex zero.  No height ordering
or computability claim is made.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaBridge.ZeroDataPresentationEquiv

open D5.S3.Weil.Convention
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
open D5.S3.Zeros.Symmetry.ZeroSymmetryAction
open scoped ComplexConjugate

/-- The same-height mirror on indices: functional-equation reflection followed
by complex conjugation. -/
def mirrorIndex (Z : ZeroData) : Equiv.Perm ℕ :=
  Z.reflection.trans Z.conjugation

@[simp]
theorem mirrorIndex_apply (Z : ZeroData) (n : ℕ) :
    mirrorIndex Z n = Z.conjugation (Z.reflection n) := rfl

/-- The index mirror realizes `rho ↦ 1 - conj rho`. -/
theorem mirrorIndex_zero (Z : ZeroData) (n : ℕ) :
    Z.zero (mirrorIndex Z n) = 1 - conj (Z.zero n) := by
  change Z.zero (Z.conjugation (Z.reflection n)) = _
  rw [Z.zero_conjugation, Z.zero_reflection]
  simp

/-- The index mirror preserves analytic multiplicity. -/
theorem mirrorIndex_multiplicity (Z : ZeroData) (n : ℕ) :
    Z.multiplicity (mirrorIndex Z n) = Z.multiplicity n := by
  change Z.multiplicity (Z.conjugation (Z.reflection n)) = _
  rw [Z.multiplicity_conjugation, Z.multiplicity_reflection]

/-- In spectral-parameter coordinates the same-height mirror is complex
conjugation. -/
theorem mirrorIndex_gamma (Z : ZeroData) (n : ℕ) :
    Z.gamma (mirrorIndex Z n) = conj (Z.gamma n) := by
  change Z.gamma (Z.conjugation (Z.reflection n)) = _
  simp

/-- Reflection and conjugation make the same-height mirror an involution. -/
@[simp]
theorem mirrorIndex_involutive (Z : ZeroData) (n : ℕ) :
    mirrorIndex Z (mirrorIndex Z n) = n := by
  change Z.conjugation
      (Z.reflection (Z.conjugation (Z.reflection n))) = n
  rw [zero_symmetries_commute Z (Z.reflection n),
    Z.reflection_reflection, Z.conjugation_conjugation]

/-- The inverse permutation of the mirror is the mirror itself. -/
theorem mirrorIndex_symm (Z : ZeroData) :
    (mirrorIndex Z).symm = mirrorIndex Z := by
  apply Equiv.ext
  intro n
  apply (mirrorIndex Z).injective
  simp [mirrorIndex_involutive]

/-- A mirror index is fixed exactly at the critical-line fixed locus. -/
theorem mirrorIndex_fixed_iff_critical (Z : ZeroData) (n : ℕ) :
    mirrorIndex Z n = n ↔ (Z.zero n).re = criticalAbscissa := by
  exact mirror_index_fixed_iff_critical Z n

/-- The unique zero-preserving reindexing from `Z` to `Z'`. -/
noncomputable def zeroDataPresentationEquiv (Z Z' : ZeroData) : ℕ ≃ ℕ :=
  (zeroEquiv Z).trans (zeroEquiv Z').symm

/-- The presentation equivalence preserves represented zeros exactly. -/
theorem zeroDataPresentationEquiv_zero (Z Z' : ZeroData) (n : ℕ) :
    Z'.zero (zeroDataPresentationEquiv Z Z' n) = Z.zero n := by
  change ((zeroEquiv Z') ((zeroEquiv Z').symm (zeroEquiv Z n))).1 = Z.zero n
  rw [Equiv.apply_symm_apply]
  rfl

/-- The presentation equivalence preserves analytic multiplicity. -/
theorem zeroDataPresentationEquiv_multiplicity (Z Z' : ZeroData) (n : ℕ) :
    Z'.multiplicity (zeroDataPresentationEquiv Z Z' n) = Z.multiplicity n := by
  rw [multiplicity_eq_zeroMult Z', multiplicity_eq_zeroMult Z,
    zeroDataPresentationEquiv_zero]

/-- The presentation equivalence preserves the complex spectral parameter. -/
theorem zeroDataPresentationEquiv_gamma (Z Z' : ZeroData) (n : ℕ) :
    Z'.gamma (zeroDataPresentationEquiv Z Z' n) = Z.gamma n := by
  unfold ZeroData.gamma
  rw [zeroDataPresentationEquiv_zero]

/-- Reindexing intertwines functional-equation reflection. -/
theorem zeroDataPresentationEquiv_reflection (Z Z' : ZeroData) (n : ℕ) :
    zeroDataPresentationEquiv Z Z' (Z.reflection n) =
      Z'.reflection (zeroDataPresentationEquiv Z Z' n) := by
  apply Z'.zero_injective
  rw [zeroDataPresentationEquiv_zero, Z'.zero_reflection,
    zeroDataPresentationEquiv_zero, Z.zero_reflection]

/-- Reindexing intertwines complex conjugation. -/
theorem zeroDataPresentationEquiv_conjugation (Z Z' : ZeroData) (n : ℕ) :
    zeroDataPresentationEquiv Z Z' (Z.conjugation n) =
      Z'.conjugation (zeroDataPresentationEquiv Z Z' n) := by
  apply Z'.zero_injective
  rw [zeroDataPresentationEquiv_zero, Z'.zero_conjugation,
    zeroDataPresentationEquiv_zero, Z.zero_conjugation]

/-- Reindexing intertwines the same-height mirror involution. -/
theorem zeroDataPresentationEquiv_mirror (Z Z' : ZeroData) (n : ℕ) :
    zeroDataPresentationEquiv Z Z' (mirrorIndex Z n) =
      mirrorIndex Z' (zeroDataPresentationEquiv Z Z' n) := by
  apply Z'.zero_injective
  rw [zeroDataPresentationEquiv_zero, mirrorIndex_zero,
    mirrorIndex_zero, zeroDataPresentationEquiv_zero]

/-- A zero-preserving equivalence is forced to be the canonical presentation
reindexing. -/
theorem zeroDataPresentationEquiv_unique (Z Z' : ZeroData)
    (e : ℕ ≃ ℕ) (hzero : ∀ n, Z'.zero (e n) = Z.zero n) :
    e = zeroDataPresentationEquiv Z Z' := by
  apply Equiv.ext
  intro n
  apply Z'.zero_injective
  rw [hzero, zeroDataPresentationEquiv_zero]

/-- The canonical presentation equivalence from a presentation to itself is
identity. -/
theorem zeroDataPresentationEquiv_self (Z : ZeroData) :
    zeroDataPresentationEquiv Z Z = Equiv.refl ℕ := by
  symm
  apply zeroDataPresentationEquiv_unique Z Z
  intro n
  rfl

/-- Reversing presentation direction takes the inverse equivalence. -/
theorem zeroDataPresentationEquiv_symm (Z Z' : ZeroData) :
    (zeroDataPresentationEquiv Z Z').symm =
      zeroDataPresentationEquiv Z' Z := by
  apply zeroDataPresentationEquiv_unique Z' Z
  intro n
  have h := zeroDataPresentationEquiv_zero Z Z'
    ((zeroDataPresentationEquiv Z Z').symm n)
  simpa using h.symm

/-- Presentation transport composes functorially. -/
theorem zeroDataPresentationEquiv_trans (Z Z' Z'' : ZeroData) :
    (zeroDataPresentationEquiv Z Z').trans
        (zeroDataPresentationEquiv Z' Z'') =
      zeroDataPresentationEquiv Z Z'' := by
  apply zeroDataPresentationEquiv_unique Z Z''
  intro n
  rw [Equiv.trans_apply, zeroDataPresentationEquiv_zero,
    zeroDataPresentationEquiv_zero]

#print axioms mirrorIndex_fixed_iff_critical
#print axioms zeroDataPresentationEquiv_unique
#print axioms zeroDataPresentationEquiv_reflection
#print axioms zeroDataPresentationEquiv_conjugation
#print axioms zeroDataPresentationEquiv_mirror
#print axioms zeroDataPresentationEquiv_trans

end D5.S3.Weil.ZetaBridge.ZeroDataPresentationEquiv
