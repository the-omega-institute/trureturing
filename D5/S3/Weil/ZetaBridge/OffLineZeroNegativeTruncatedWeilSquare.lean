/- GID: D5/S3/Weil/ZetaBridge/OffLineZeroNegativeTruncatedWeilSquare
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/OffLineZeroNegativeTruncatedWeilSquare
   mirror-E: none(waiver:kernel-verified-finite-cutoff-separator-only)
   anchors: []
   digest: A nonreal off-line zero in a cutoff yields a negative truncated Weil square. -/

import D5.S3.Weil.ZetaBridge.PrescribedPairNegativeOrbit
import D5.S3.Weil.TestFunctions.EvenTestFunctionFiniteInterpolation

/-!
# Off-line zero negative truncated Weil square

This is the finite-cutoff separator. It makes no assertion about limits,
`SymmetricConvergent`, or `zeroSum`; the explicit nonreal hypothesis `hIm`
stands in for the named M3-d gap.
-/

/- Library-search and duplication audit trail (2026-09-03):
   * The exact theorem name and the complete truncated-negative conclusion
     have no hit in D5 or pinned Mathlib.
   * D5 contains the existential test-function interpolation theorem and the
     prescribed-pair negative orbit theorem imported below; neither alone
     covers the finite-cutoff separator.
   * D5 hits for the off-line and nonreal hypothesis shapes occur in the
     frozen orbit machinery and are consumed by this proof.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaBridge.OffLineZeroNegativeTruncatedWeilSquare

open Complex
open D5.S3.Weil.Convention
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.TestFunctions.EvenTestFunctionFiniteInterpolation
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.ConvolutionSquareOrbitBounds
open D5.S3.Weil.ZetaBridge.PrescribedPairNegativeOrbit
open D5.S3.Zeros.Symmetry.ZeroSymmetryAction
open scoped ComplexConjugate

noncomputable section

/-- A nonreal off-line zero inside a symmetric cutoff admits a Weil test
function whose convolution square has strictly negative truncated zero sum. -/
theorem offLineZero_yields_negative_truncated_weil_square
    (Z : ZeroData) (n : ℕ) (T : ℝ)
    (hn : n ∈ Z.symmetricIndices T)
    (hOff : (Z.zero n).re ≠ criticalAbscissa)
    (hIm : (Z.zero n).im ≠ 0) :
    ∃ g : WeilTestFunction,
      (truncatedZeroSum Z (convolutionSquare g) T).re < 0 := by
  classical
  let I : Finset ℕ := Z.symmetricIndices T
  let rep : ℕ → ℕ := fun k => min k (Z.reflection k)
  have hGammaInj : Function.Injective Z.gamma := by
    intro i j hij
    apply Z.zero_injective
    rw [Z.zero_eq_critical_add_I_mul_gamma i,
      Z.zero_eq_critical_add_I_mul_gamma j, hij]
  have hrep_le (k : ℕ) : rep k ≤ Z.reflection (rep k) := by
    by_cases hk : k ≤ Z.reflection k
    · simp [rep, hk]
    · have hk' : Z.reflection k ≤ k := Nat.le_of_not_ge hk
      simp [rep, hk']
  have hrep_mem {k : ℕ} (hk : k ∈ I) : rep k ∈ I := by
    by_cases hle : k ≤ Z.reflection k
    · simpa [rep, Nat.min_eq_left hle] using hk
    · have hle' : Z.reflection k ≤ k := Nat.le_of_not_ge hle
      have hr : Z.reflection k ∈ Z.symmetricIndices T :=
        (Z.reflection_mem_symmetricIndices).2 (by simpa [I] using hk)
      simpa [I, rep, Nat.min_eq_right hle'] using hr
  have hrep_freq (k : ℕ) :
      Z.gamma (rep k) = Z.gamma k ∨
        Z.gamma (rep k) = -Z.gamma k := by
    by_cases hle : k ≤ Z.reflection k
    · left
      simp [rep, Nat.min_eq_left hle]
    · right
      have hle' : Z.reflection k ≤ k := Nat.le_of_not_ge hle
      simp [rep, Nat.min_eq_right hle']
  have hrep_eq_or (i j : ℕ) (hij : rep i = rep j) :
      i = j ∨ i = Z.reflection j := by
    by_cases hi : i ≤ Z.reflection i
    · by_cases hj : j ≤ Z.reflection j
      · left
        simpa [rep, Nat.min_eq_left hi, Nat.min_eq_left hj] using hij
      · right
        have hj' : Z.reflection j ≤ j := Nat.le_of_not_ge hj
        simpa [rep, Nat.min_eq_left hi, Nat.min_eq_right hj'] using hij
    · have hi' : Z.reflection i ≤ i := Nat.le_of_not_ge hi
      by_cases hj : j ≤ Z.reflection j
      · have hrij : Z.reflection i = j := by
          simpa [rep, Nat.min_eq_right hi', Nat.min_eq_left hj] using hij
        right
        have := congrArg Z.reflection hrij
        simpa using this
      · have hj' : Z.reflection j ≤ j := Nat.le_of_not_ge hj
        left
        apply Z.reflection.injective
        simpa [rep, Nat.min_eq_right hi', Nat.min_eq_right hj'] using hij
  have hConj : Z.conjugation n ≠ n := by
    intro hfixed
    have hzero := Z.zero_conjugation n
    rw [hfixed] at hzero
    have him := congrArg Complex.im hzero
    simp only [Complex.conj_im] at him
    apply hIm
    linarith
  have hMirror : Z.conjugation (Z.reflection n) ≠ n := by
    intro hfixed
    exact hOff ((mirror_index_fixed_iff_critical Z n).1 hfixed)
  have htargetRepNe : rep n ≠ rep (Z.conjugation n) := by
    intro heq
    rcases hrep_eq_or n (Z.conjugation n) heq with hnc | hnrc
    · exact hConj hnc.symm
    · apply hMirror
      calc
        Z.conjugation (Z.reflection n) =
            Z.reflection (Z.conjugation n) :=
          (zero_symmetries_commute Z n).symm
        _ = n := hnrc.symm
  let S : Finset ℂ := I.image (fun k => Z.gamma (rep k))
  have hsep : ∀ ⦃z w : ℂ⦄, z ∈ S → w ∈ S → z ≠ w → z ≠ -w := by
    intro z w hz hw hzw hneg
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
    apply hzw
    congr 1
    have hidx : rep i = Z.reflection (rep j) := by
      apply hGammaInj
      simpa using hneg
    apply Nat.le_antisymm
    · calc
        rep i ≤ Z.reflection (rep i) := hrep_le i
        _ = rep j := by rw [hidx, Z.reflection_reflection]
    · calc
        rep j ≤ Z.reflection (rep j) := hrep_le j
        _ = rep i := hidx.symm
  have htargetFreqNe :
      Z.gamma (rep n) ≠ Z.gamma (rep (Z.conjugation n)) := by
    intro heq
    exact htargetRepNe (hGammaInj heq)
  let a : S → ℂ := fun z =>
    if z.1 = Z.gamma (rep n) then 1
    else if z.1 = Z.gamma (rep (Z.conjugation n)) then -1
    else 0
  obtain ⟨g, hg⟩ := even_weilTestFunction_finite_interpolation S hsep a
  have hrep_in_S {k : ℕ} (hk : k ∈ I) : Z.gamma (rep k) ∈ S := by
    exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
  have hGrep (k : ℕ) (hk : k ∈ I) :
      fourierLaplace g (Z.gamma (rep k)) =
        if Z.gamma (rep k) = Z.gamma (rep n) then 1
        else if Z.gamma (rep k) = Z.gamma (rep (Z.conjugation n)) then -1
        else 0 := by
    simpa only [a] using hg ⟨Z.gamma (rep k), hrep_in_S hk⟩
  have hG (k : ℕ) (hk : k ∈ I) :
      fourierLaplace g (Z.gamma k) =
        if Z.gamma (rep k) = Z.gamma (rep n) then 1
        else if Z.gamma (rep k) = Z.gamma (rep (Z.conjugation n)) then -1
        else 0 := by
    rcases hrep_freq k with hsame | hneg
    · rw [← hsame]
      exact hGrep k hk
    · calc
        fourierLaplace g (Z.gamma k) =
            fourierLaplace g (-Z.gamma k) :=
          (fourierLaplace_neg g (Z.gamma k)).symm
        _ = fourierLaplace g (Z.gamma (rep k)) := by rw [hneg]
        _ = _ := hGrep k hk
  have hnI : n ∈ I := by simpa [I] using hn
  have hcI : Z.conjugation n ∈ I := by
    simpa [I] using (Z.conjugation_mem_symmetricIndices).2 hn
  have hz : fourierLaplace g (Z.gamma n) = 1 := by
    simpa using hG n hnI
  have hcval : fourierLaplace g (Z.gamma (Z.conjugation n)) = -1 := by
    have hne :
        Z.gamma (rep (Z.conjugation n)) ≠ Z.gamma (rep n) :=
      htargetFreqNe.symm
    simpa [hne] using hG (Z.conjugation n) hcI
  have hcz : fourierLaplace g (conj (Z.gamma n)) = -1 := by
    calc
      fourierLaplace g (conj (Z.gamma n)) =
          fourierLaplace g (-conj (Z.gamma n)) :=
        (fourierLaplace_neg g (conj (Z.gamma n))).symm
      _ = fourierLaplace g (Z.gamma (Z.conjugation n)) := by
        rw [Z.gamma_conjugation]
      _ = -1 := hcval
  let O : Finset ℕ :=
    {n, Z.reflection n, Z.conjugation n,
      Z.conjugation (Z.reflection n)}
  have hOsub : O ⊆ I := by
    intro k hk
    simp only [O, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact hnI
    · simpa [I] using (Z.reflection_mem_symmetricIndices).2 hn
    · exact hcI
    · simpa [I] using (Z.conjugation_mem_symmetricIndices).2
        ((Z.reflection_mem_symmetricIndices).2 hn)
  have hGzero (k : ℕ) (hk : k ∈ I) (hkO : k ∉ O) :
      fourierLaplace g (Z.gamma k) = 0 := by
    have hneN : Z.gamma (rep k) ≠ Z.gamma (rep n) := by
      intro heq
      rcases hrep_eq_or k n (hGammaInj heq) with hkn | hkn
      · exact hkO (by simp [O, hkn])
      · exact hkO (by simp [O, hkn])
    have hneC :
        Z.gamma (rep k) ≠ Z.gamma (rep (Z.conjugation n)) := by
      intro heq
      rcases hrep_eq_or k (Z.conjugation n) (hGammaInj heq) with hkc | hkc
      · exact hkO (by simp [O, hkc])
      · exact hkO (by
          simp [O, hkc, zero_symmetries_commute Z n])
    simpa [hneN, hneC] using hG k hk
  have hsummandZero (k : ℕ) (hk : k ∈ I) (hkO : k ∉ O) :
      zeroSummand Z (convolutionSquare g) k = 0 := by
    rw [zeroSummand, fourierLaplace_convolutionSquare_complex,
      hGzero k hk hkO]
    ring
  have hsum :
      (∑ k ∈ I, zeroSummand Z (convolutionSquare g) k) =
        ∑ k ∈ O, zeroSummand Z (convolutionSquare g) k := by
    symm
    exact Finset.sum_subset hOsub hsummandZero
  refine ⟨g, ?_⟩
  rw [truncatedZeroSum]
  change (∑ k ∈ I, zeroSummand Z (convolutionSquare g) k).re < 0
  rw [hsum]
  have hOrbit := prescribed_pair_gives_negative_zero_orbit
    Z n hOff hIm g hz hcz
  have hm := Z.multiplicity_pos n
  have hmR : 0 < (Z.multiplicity n : ℝ) := Nat.cast_pos.mpr hm
  rw [show (∑ k ∈ O, zeroSummand Z (convolutionSquare g) k).re =
      -4 * (Z.multiplicity n : ℝ) by simpa [O] using hOrbit]
  nlinarith

#print axioms offLineZero_yields_negative_truncated_weil_square

-- These checked terms expose the exact conditional hypothesis bundle and domains.
example (Z : ZeroData) (n : ℕ) (T : ℝ)
    (hn : n ∈ Z.symmetricIndices T)
    (hOff : (Z.zero n).re ≠ criticalAbscissa)
    (hIm : (Z.zero n).im ≠ 0) :
    n ∈ Z.symmetricIndices T ∧
      (Z.zero n).re ≠ criticalAbscissa ∧
      (Z.zero n).im ≠ 0 :=
  ⟨hn, hOff, hIm⟩

example (Z : ZeroData) : Nonempty ZeroData := ⟨Z⟩

example : Nonempty WeilTestFunction := ⟨standardTestFunction⟩

end

end D5.S3.Weil.ZetaBridge.OffLineZeroNegativeTruncatedWeilSquare
