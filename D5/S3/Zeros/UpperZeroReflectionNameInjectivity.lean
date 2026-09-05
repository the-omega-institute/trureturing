/- GID: D5/S3/Zeros/UpperZeroReflectionNameInjectivity
   generality: I
   mirror-B: D5/B/S3/Zeros/UpperZeroReflectionNameInjectivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: RH is equivalent to injectivity of the unordered reflection-orbit name on upper zeros. -/

import D5.S3.Weil.ZetaBridge.AlternatingZetaContinuation
import D5.S3.Zeros.Symmetry.ZeroSymmetryAction
import Mathlib.Data.Sym.Sym2

/- Library-search audit trail (2026-09-05):
   * Repository searches for `reflection.*name`, `name.*inject`, `upper.*zero`,
     and the equivalent fixed-index formulation found
     `ZeroSymmetryAction.all_nontrivial_zeros_critical_iff_mirror_indices_fixed`,
     but no reflection-name map or injectivity characterization.
   * Digestion searches found proposed future module names
     `RHReflectionNameInjective` and `ReflectionNameSufficientIffRH`, but no
     corresponding Lean artifact on dev or any in-flight math lane.
   * Pinned Mathlib provides `Sym2.eq_iff`, used below for equality of unordered
     pairs. It has no theorem specializing orbit-name injectivity to zeta zeros.
   * `ZeroData.im_ne_zero` supplies the analytic fact that conjugation moves every
     lower nontrivial zero into the upper half-plane without a real-zero branch. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Zeros.UpperZeroReflectionNameInjectivity

open D5.S3.Weil.Convention
open D5.S3.Weil.ZeroSum
open D5.S3.Zeros.Symmetry.ZeroSymmetryAction
open scoped ComplexConjugate

/-- Indices of the nontrivial zeros in the open upper half-plane. -/
def UpperZeroIndex (Z : ZeroData) := {n : ℕ // 0 < (Z.zero n).im}

/-- Conjugate reflection preserves the upper half-plane. -/
def upperMirrorIndex (Z : ZeroData) (n : UpperZeroIndex Z) : UpperZeroIndex Z :=
  ⟨Z.conjugation (Z.reflection n.1), by
    rw [Z.zero_conjugation, Z.zero_reflection]
    simpa using n.2⟩

/-- The reflection name forgets orientation inside an upper-half-plane mirror orbit. -/
def upperZeroReflectionName (Z : ZeroData) (n : UpperZeroIndex Z) :
    Sym2 (UpperZeroIndex Z) :=
  s(n, upperMirrorIndex Z n)

private theorem upperMirrorIndex_involutive (Z : ZeroData) :
    Function.Involutive (upperMirrorIndex Z) := by
  intro n
  apply Subtype.ext
  change
    Z.conjugation
        (Z.reflection (Z.conjugation (Z.reflection n.1))) =
      n.1
  calc
    Z.conjugation
          (Z.reflection (Z.conjugation (Z.reflection n.1))) =
        Z.conjugation
          (Z.conjugation (Z.reflection (Z.reflection n.1))) :=
      congrArg Z.conjugation
        (zero_symmetries_commute Z (Z.reflection n.1))
    _ = n.1 := by simp

private theorem upper_zero_reflection_name_injective_iff_fixed (Z : ZeroData) :
    Function.Injective (upperZeroReflectionName Z) ↔
      ∀ n : UpperZeroIndex Z, upperMirrorIndex Z n = n := by
  constructor
  · intro hinjective n
    have hsame :
        upperZeroReflectionName Z n =
          upperZeroReflectionName Z (upperMirrorIndex Z n) := by
      unfold upperZeroReflectionName
      rw [upperMirrorIndex_involutive Z n]
      exact Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩)
    exact (hinjective hsame).symm
  · intro hfixed n m hsame
    unfold upperZeroReflectionName at hsame
    rw [hfixed n, hfixed m] at hsame
    rcases Sym2.eq_iff.mp hsame with h | h
    · exact h.1
    · exact h.1

/-- For any duplicate-free exhaustive zero enumeration, RH is equivalent to
injectivity of the unordered conjugate-reflection orbit name on its upper zeros.

An off-critical upper zero and its distinct mirror have the same unordered name;
on the critical line every such orbit is a singleton, so its name is injective. -/
theorem rh_iff_upper_zero_reflection_name_injective (Z : ZeroData) :
    (∀ {rho : ℂ}, IsNontrivialZero rho → rho.re = criticalAbscissa) ↔
      Function.Injective (upperZeroReflectionName Z) := by
  constructor
  · intro hRH
    apply (upper_zero_reflection_name_injective_iff_fixed Z).2
    intro n
    apply Subtype.ext
    change Z.conjugation (Z.reflection n.1) = n.1
    exact (mirror_index_fixed_iff_critical Z n.1).2
      (hRH (Z.zero_isNontrivial n.1))
  · intro hinjective rho hrho
    obtain ⟨n, rfl⟩ := Z.zero_exhaustive hrho
    have hfixed :
        ∀ u : UpperZeroIndex Z, upperMirrorIndex Z u = u :=
      (upper_zero_reflection_name_injective_iff_fixed Z).1 hinjective
    have him_ne : (Z.zero n).im ≠ 0 :=
      D5.S3.Weil.ZetaBridge.AlternatingZetaContinuation.ZeroData.im_ne_zero
        Z n (Z.zero_isNontrivial n)
    rcases lt_or_gt_of_ne him_ne with him_neg | him_pos
    · have hconj_pos : 0 < (Z.zero (Z.conjugation n)).im := by
        rw [Z.zero_conjugation]
        simpa using neg_pos.mpr him_neg
      have hconj_fixed := congrArg Subtype.val
        (hfixed ⟨Z.conjugation n, hconj_pos⟩)
      change
        Z.conjugation (Z.reflection (Z.conjugation n)) =
          Z.conjugation n at hconj_fixed
      have hconj_critical :=
        (mirror_index_fixed_iff_critical Z (Z.conjugation n)).1 hconj_fixed
      rw [Z.zero_conjugation] at hconj_critical
      simpa using hconj_critical
    · have hn_fixed := congrArg Subtype.val (hfixed ⟨n, him_pos⟩)
      change Z.conjugation (Z.reflection n) = n at hn_fixed
      exact (mirror_index_fixed_iff_critical Z n).1 hn_fixed

#print axioms rh_iff_upper_zero_reflection_name_injective

end D5.S3.Zeros.UpperZeroReflectionNameInjectivity
