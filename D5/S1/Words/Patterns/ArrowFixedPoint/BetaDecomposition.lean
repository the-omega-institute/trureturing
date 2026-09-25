/- GID: D5/S1/Words/Patterns/ArrowFixedPoint/BetaDecomposition
   generality: I
   mirror-B: D5/B/S1/Words/Patterns/ArrowFixedPoint/BetaDecomposition
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The actual beta avoidance class split at its smallest transformed fixed label. -/

import D5.S1.Words.Patterns.ArrowFixedPoint.AlphaDecomposition

/-!
# Beta extremal decomposition

This source-level first stage changes an actual one-line beta avoider into its
actual inverse-Foata permutation and splits on whether that permutation has a
fixed label.  In the nonempty branch the smallest fixed label is uniquely
derived from the permutation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Patterns.ArrowFixedPoint

open Equiv Equiv.Perm Function

noncomputable section

/-- The order condition above a proposed smallest transformed fixed label. -/
def BetaAboveDecreasing {n : ℕ} (p : Equiv.Perm (Fin n)) (m : Fin n) : Prop :=
  ∀ x2 x3 : Fin n, x2 < x3 → m < x2 → ¬ Before (theta p) x2 x3

/-- Actual transformed permutations with at least one fixed label and the beta
condition above their uniquely determined smallest fixed label. -/
structure BetaFixedHatCode (n : ℕ) where
  hat : Equiv.Perm (Fin n)
  fixed_nonempty : (fixedLabels hat).Nonempty
  above_decreasing :
    BetaAboveDecreasing hat ((fixedLabels hat).min' fixed_nonempty)

/-- The first source-level beta code: either an actual derangement, or an
actual transformed permutation equipped with its derived smallest fixed label. -/
abbrev BetaExtremalCode (n : ℕ) :=
  derangements (Fin n) ⊕ BetaFixedHatCode n

/-- The literal beta avoidance class is reversibly split into its no-fixed
branch and its smallest-fixed-label branch. -/
def betaExtremalEquiv (n : ℕ) :
    {pi : Equiv.Perm (Fin n) // ¬ BetaOccurs pi} ≃ BetaExtremalCode n := by
  classical
  let encode : {pi : Equiv.Perm (Fin n) // ¬ BetaOccurs pi} → BetaExtremalCode n :=
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
        let m := (fixedLabels p).min' hnonempty
        Sum.inr ⟨p, hnonempty, by
          have hmmem : m ∈ fixedLabels p := Finset.min'_mem _ _
          have hmfix : p m = m := by simpa [fixedLabels] using hmmem
          have hmin : ∀ f : Fin n, p f = f → m ≤ f := by
            intro f hf
            exact Finset.min'_le _ f (by simp [fixedLabels, hf])
          intro x2 x3 h23 hm2
          have hchar := (beta_avoid_iff_above_smallest_fixed pi.1 m
            (by simpa [p] using hmfix) (by simpa [p] using hmin)).mp pi.2
          simpa [BetaAboveDecreasing, p] using hchar x2 x3 h23 hm2
        ⟩
  let decode : BetaExtremalCode n → {pi : Equiv.Perm (Fin n) // ¬ BetaOccurs pi} :=
    fun code => match code with
      | Sum.inl p => ⟨theta p.1, by
          rw [beta_avoid_iff_above_decreasing]
          intro f hfix
          have : p.1 f ≠ f := p.2 f
          exact (this (by simpa using hfix)).elim⟩
      | Sum.inr code => ⟨theta code.hat, by
          rcases code with ⟨p, hnonempty, hdec⟩
          let m := (fixedLabels p).min' hnonempty
          have hmmem : m ∈ fixedLabels p := Finset.min'_mem _ _
          have hm : p m = m := by simpa [fixedLabels] using hmmem
          have hmin : ∀ f : Fin n, p f = f → m ≤ f := by
            intro f hf
            exact Finset.min'_le _ f (by simp [fixedLabels, hf])
          apply (beta_avoid_iff_above_smallest_fixed (theta p) m
            (by simpa using hm) (by simpa using hmin)).mpr
          simpa [BetaAboveDecreasing] using hdec⟩
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
        obtain ⟨m, hmmem⟩ := hnonempty
        exact h m (by simpa [fixedLabels] using hmmem)
      have hnotDer' : theta.symm (theta p) ∉ derangements (Fin n) := by
        simpa using hnotDer
      rw [dif_neg hnotDer']
      simp only [Equiv.symm_apply_apply]

end

end D5.S1.Words.Patterns.ArrowFixedPoint
