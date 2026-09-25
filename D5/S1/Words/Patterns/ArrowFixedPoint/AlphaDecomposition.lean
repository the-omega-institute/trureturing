/- GID: D5/S1/Words/Patterns/ArrowFixedPoint/AlphaDecomposition
   generality: I
   mirror-B: D5/B/S1/Words/Patterns/ArrowFixedPoint/AlphaDecomposition
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The actual alpha avoidance class split at its largest transformed fixed label. -/

import D5.S1.Words.Patterns.ArrowFixedPoint.Predicates
import Mathlib.Combinatorics.Derangements.Finite

/-!
# Alpha extremal decomposition

This is the source-level first stage of the alpha codec.  It changes an
actual one-line avoider into its actual inverse-Foata permutation and splits
on whether that permutation has a fixed label.  In the nonempty branch the
largest fixed label is stored together with precisely the decreasing-order
condition used by the subsequent labelled deletion codec.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Patterns.ArrowFixedPoint

open Equiv Equiv.Perm Function

noncomputable section

/-- Fixed labels of a permutation, as a finite set. -/
def fixedLabels {n : ℕ} (p : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun x => p x = x

/-- The order condition below a proposed largest transformed fixed label. -/
def AlphaBelowDecreasing {n : ℕ} (p : Equiv.Perm (Fin n)) (M : Fin n) : Prop :=
  ∀ x1 x2 : Fin n, x1 < x2 → x2 < M → ¬ Before (theta p) x1 x2

/-- Actual transformed permutations with at least one fixed label and the
alpha condition below their uniquely determined largest fixed label. -/
structure AlphaFixedHatCode (n : ℕ) where
  hat : Equiv.Perm (Fin n)
  fixed_nonempty : (fixedLabels hat).Nonempty
  below_decreasing :
    AlphaBelowDecreasing hat ((fixedLabels hat).max' fixed_nonempty)

/-- The first source-level alpha code: either an actual derangement, or an
actual transformed permutation equipped with its largest fixed label. -/
abbrev AlphaExtremalCode (n : ℕ) :=
  derangements (Fin n) ⊕ AlphaFixedHatCode n

/-- The literal alpha avoidance class is reversibly split into its no-fixed
branch and its largest-fixed-label branch. -/
def alphaExtremalEquiv (n : ℕ) :
    {pi : Equiv.Perm (Fin n) // ¬ AlphaOccurs pi} ≃ AlphaExtremalCode n := by
  classical
  let encode : {pi : Equiv.Perm (Fin n) // ¬ AlphaOccurs pi} → AlphaExtremalCode n :=
    fun pi =>
      let p := theta.symm pi.1
      if hder : p ∈ derangements (Fin n) then
        Sum.inl ⟨p, hder⟩
      else
        let hnonempty : (fixedLabels p).Nonempty := by
          have hex : ∃ x, p x = x := by
            by_contra h
            apply hder
            intro x hx
            exact h ⟨x, hx⟩
          obtain ⟨x, hx⟩ := hex
          exact ⟨x, by simp [fixedLabels, hx]⟩
        let M := (fixedLabels p).max' hnonempty
        Sum.inr ⟨p, hnonempty, by
          have hMmem : M ∈ fixedLabels p := Finset.max'_mem _ _
          have hMfix : p M = M := by simpa [fixedLabels] using hMmem
          have hmax : ∀ f : Fin n, p f = f → f ≤ M := by
            intro f hf
            exact Finset.le_max' _ f (by simp [fixedLabels, hf])
          intro x1 x2 h12 h2M
          have hchar := (alpha_avoid_iff_below_largest_fixed pi.1 M
            (by simpa [p] using hMfix) (by simpa [p] using hmax)).mp pi.2
          simpa [AlphaBelowDecreasing, p] using hchar x1 x2 h12 h2M
        ⟩
  let decode : AlphaExtremalCode n → {pi : Equiv.Perm (Fin n) // ¬ AlphaOccurs pi} :=
    fun code => match code with
      | Sum.inl p => ⟨theta p.1, by
          rw [alpha_avoid_iff_below_decreasing]
          intro f hfix
          have : p.1 f ≠ f := p.2 f
          exact (this (by simpa using hfix)).elim⟩
      | Sum.inr code => ⟨theta code.hat, by
          rcases code with ⟨p, hnonempty, hdec⟩
          let M := (fixedLabels p).max' hnonempty
          have hMmem : M ∈ fixedLabels p := Finset.max'_mem _ _
          have hM : p M = M := by simpa [fixedLabels] using hMmem
          have hmax : ∀ f : Fin n, p f = f → f ≤ M := by
            intro f hf
            exact Finset.le_max' _ f (by simp [fixedLabels, hf])
          apply (alpha_avoid_iff_below_largest_fixed (theta p) M
            (by simpa using hM) (by simpa using hmax)).mpr
          simpa [AlphaBelowDecreasing] using hdec⟩
  refine {
    toFun := encode
    invFun := decode
    left_inv := ?_
    right_inv := ?_
  }
  · intro pi
    apply Subtype.ext
    simp only [decode, encode]
    by_cases hder : theta.symm pi.1 ∈ derangements (Fin n)
    · rw [dif_pos hder]
      exact theta.apply_symm_apply pi.1
    · rw [dif_neg hder]
      exact theta.apply_symm_apply pi.1
  · intro code
    rcases code with p | code
    · simp only [decode, encode]
      have hder : theta.symm (theta p.1) ∈ derangements (Fin n) := by
        simpa using p.2
      rw [dif_pos hder]
      congr 1
      apply Subtype.ext
      exact theta.symm_apply_apply p.1
    · rcases code with ⟨p, hnonempty, hdec⟩
      simp only [decode, encode]
      have hnotDer : p ∉ derangements (Fin n) := by
        intro h
        obtain ⟨M, hMmem⟩ := hnonempty
        exact h M (by simpa [fixedLabels] using hMmem)
      have hnotDer' : theta.symm (theta p) ∉ derangements (Fin n) := by
        simpa using hnotDer
      rw [dif_neg hnotDer']
      simp only [Equiv.symm_apply_apply]

end

end D5.S1.Words.Patterns.ArrowFixedPoint
