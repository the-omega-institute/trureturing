/- GID: D5/S3/Weil/ZetaBridge/OffLineNonrealZeroNegativeWeilSquare
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/OffLineNonrealZeroNegativeWeilSquare
   mirror-E: none(waiver:kernel-verified-full-off-line-nonreal-separator)
   anchors: []
   digest: An off-line nonreal zero yields a Weil square with strictly negative full zero sum. -/

import D5.S3.Fourier.ConvolutionPowerAmplification
import D5.S3.Weil.TestFunctions.EvenTestFunctionFiniteInterpolation
import D5.S3.Weil.TestFunctions.FourierLaplaceClosedStripDecay
import D5.S3.Weil.ZetaBridge.PrescribedPairNegativeOrbit
import D5.S3.Weil.ZetaBridge.SymmetricConvergentOfZetaSummable

/-!
# Off-line nonreal zero negative Weil square

The explicit hypothesis `hIm` is the stand-in for the named M3-d gap.
This module proves a conditional separator and asserts no implication from O-6
to the Riemann hypothesis.
-/

/- Library-search audit trail (2026-09-03):
   * Exact D5 and pinned-Mathlib searches found no theorem with the full
     negative `zeroSum` conclusion, nor either named auxiliary theorem.
   * The frozen closed-strip decay, finite interpolation, prescribed negative
     orbit, convolution-power, and zeta-summability declarations are imported
     and applied below.
   * The frozen finite-cutoff separator contains analogous proof-local orbit
     representatives, but exposes no declaration that can be bound here. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaBridge.OffLineNonrealZeroNegativeWeilSquare

open Filter MeasureTheory
open D5.S3.Weil.Convention
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.TestFunctions.EvenTestFunctionFiniteInterpolation
open D5.S3.Weil.TestFunctions.FourierLaplaceClosedStripDecay
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.ZeroSum
open D5.S3.Fourier.ConvolutionPowerAmplification
open D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
open D5.S3.Weil.ZetaBridge.ConvolutionSquareOrbitBounds
open D5.S3.Weil.ZetaBridge.PrescribedPairNegativeOrbit
open D5.S3.Weil.ZetaBridge.SymmetricConvergentOfZetaSummable
open D5.S3.Zeros.Symmetry.ZeroSymmetryAction
open scoped ComplexConjugate ContDiff Convolution

noncomputable section

noncomputable def reflectionRep (Z : ZeroData) (j : ℕ) : ℕ :=
  min j (Z.reflection j)

noncomputable def zeroOrbit (Z : ZeroData) (n : ℕ) : Finset ℕ :=
  {n, Z.reflection n, Z.conjugation n,
    Z.conjugation (Z.reflection n)}

theorem gamma_injective (Z : ZeroData) : Function.Injective Z.gamma := by
  intro i j hij
  apply Z.zero_injective
  rw [Z.zero_eq_critical_add_I_mul_gamma i,
    Z.zero_eq_critical_add_I_mul_gamma j, hij]

private theorem reflectionRep_le (Z : ZeroData) (j : ℕ) :
    reflectionRep Z j ≤ Z.reflection (reflectionRep Z j) := by
  by_cases hj : j ≤ Z.reflection j
  · simp [reflectionRep, hj]
  · have hj' : Z.reflection j ≤ j := Nat.le_of_not_ge hj
    simp [reflectionRep, hj']

theorem reflectionRep_freq (Z : ZeroData) (j : ℕ) :
    Z.gamma (reflectionRep Z j) = Z.gamma j ∨
      Z.gamma (reflectionRep Z j) = -Z.gamma j := by
  by_cases hle : j ≤ Z.reflection j
  · left
    simp [reflectionRep, Nat.min_eq_left hle]
  · right
    have hle' : Z.reflection j ≤ j := Nat.le_of_not_ge hle
    simp [reflectionRep, Nat.min_eq_right hle']

theorem reflectionRep_eq_or (Z : ZeroData) (i j : ℕ)
    (hij : reflectionRep Z i = reflectionRep Z j) :
    i = j ∨ i = Z.reflection j := by
  by_cases hi : i ≤ Z.reflection i
  · by_cases hj : j ≤ Z.reflection j
    · left
      simpa [reflectionRep, Nat.min_eq_left hi, Nat.min_eq_left hj] using hij
    · right
      have hj' : Z.reflection j ≤ j := Nat.le_of_not_ge hj
      simpa [reflectionRep, Nat.min_eq_left hi,
        Nat.min_eq_right hj'] using hij
  · have hi' : Z.reflection i ≤ i := Nat.le_of_not_ge hi
    by_cases hj : j ≤ Z.reflection j
    · have hrij : Z.reflection i = j := by
        simpa [reflectionRep, Nat.min_eq_right hi',
          Nat.min_eq_left hj] using hij
      right
      have := congrArg Z.reflection hrij
      simpa using this
    · have hj' : Z.reflection j ≤ j := Nat.le_of_not_ge hj
      left
      apply Z.reflection.injective
      simpa [reflectionRep, Nat.min_eq_right hi',
        Nat.min_eq_right hj'] using hij

theorem reflectionRep_image_sep (Z : ZeroData) (I : Finset ℕ) :
    ∀ ⦃z w : ℂ⦄,
      z ∈ I.image (fun j => Z.gamma (reflectionRep Z j)) →
      w ∈ I.image (fun j => Z.gamma (reflectionRep Z j)) →
      z ≠ w → z ≠ -w := by
  intro z w hz hw hzw hneg
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
  apply hzw
  congr 1
  have hidx : reflectionRep Z i = Z.reflection (reflectionRep Z j) := by
    apply gamma_injective Z
    simpa using hneg
  apply Nat.le_antisymm
  · calc
      reflectionRep Z i ≤ Z.reflection (reflectionRep Z i) :=
        reflectionRep_le Z i
      _ = reflectionRep Z j := by rw [hidx, Z.reflection_reflection]
  · calc
      reflectionRep Z j ≤ Z.reflection (reflectionRep Z j) :=
        reflectionRep_le Z j
      _ = reflectionRep Z i := hidx.symm

private theorem zeroOrbit_conjugation_mem (Z : ZeroData) (n j : ℕ) :
    Z.conjugation j ∈ zeroOrbit Z n ↔ j ∈ zeroOrbit Z n := by
  simp only [zeroOrbit, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    rcases h with h | h | h | h
    · right; right; left
      apply Z.conjugation.injective
      simpa using h
    · right; right; right
      apply Z.conjugation.injective
      simpa using h
    · left
      apply Z.conjugation.injective
      simpa using h
    · right; left
      apply Z.conjugation.injective
      simpa using h
  · intro h
    rcases h with h | h | h | h
    · right; right; left
      simp [h]
    · right; right; right
      simp [h]
    · left
      simp [h]
    · right; left
      simp [h]

private theorem gamma_mem_closed_half_strip (Z : ZeroData) (j : ℕ) :
    |(Z.gamma j).im| ≤ (1 / 2 : ℝ) := by
  change |(spectralParameter (Z.zero j)).im| ≤ (1 / 2 : ℝ)
  rw [← gammaOf_eq_spectralParameter (Z.zero j)]
  exact (Zeta23.WeilEF.abs_gammaOf_im_lt (Z.zero_isNontrivial j).2).le

/-- An off-line nonreal zero admits a unit peak and a finite-exception killer.
The exceptional set is a spectral ball, hence closed under both stored symmetries. -/
theorem exists_peak_and_finite_exception_killer
    (Z : ZeroData) (n : ℕ)
    (hOff : (Z.zero n).re ≠ criticalAbscissa)
    (hIm : (Z.zero n).im ≠ 0) :
    ∃ b k : WeilTestFunction, ∃ E : Finset ℕ,
      (∀ j, j ∈ E ↔ Z.reflection j ∈ E) ∧
      (∀ j, j ∈ E ↔ Z.conjugation j ∈ E) ∧
      zeroOrbit Z n ⊆ E ∧
      fourierLaplace b (Z.gamma n) = 1 ∧
      fourierLaplace b (conj (Z.gamma n)) = 1 ∧
      fourierLaplace k (Z.gamma n) = 1 ∧
      fourierLaplace k (conj (Z.gamma n)) = -1 ∧
      (∀ j ∉ E,
        ‖fourierLaplace b (Z.gamma j)‖ ≤ 1 / 2 ∧
        ‖fourierLaplace b (conj (Z.gamma j))‖ ≤ 1 / 2) ∧
      (∀ j ∈ E, j ∉ zeroOrbit Z n →
        fourierLaplace k (Z.gamma j) = 0 ∧
        fourierLaplace k (conj (Z.gamma j)) = 0) := by
  classical
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
  have htargetRepNe :
      reflectionRep Z n ≠ reflectionRep Z (Z.conjugation n) := by
    intro heq
    rcases reflectionRep_eq_or Z n (Z.conjugation n) heq with hnc | hnrc
    · exact hConj hnc.symm
    · apply hMirror
      calc
        Z.conjugation (Z.reflection n) =
            Z.reflection (Z.conjugation n) :=
          (zero_symmetries_commute Z n).symm
        _ = n := hnrc.symm
  let I0 : Finset ℕ := {n, Z.conjugation n}
  let S0 : Finset ℂ := I0.image (fun j => Z.gamma (reflectionRep Z j))
  have hsep0 : ∀ ⦃z w : ℂ⦄, z ∈ S0 → w ∈ S0 → z ≠ w → z ≠ -w := by
    simpa only [S0] using reflectionRep_image_sep Z I0
  let a0 : S0 → ℂ := fun _ => 1
  obtain ⟨b, hb⟩ := even_weilTestFunction_finite_interpolation S0 hsep0 a0
  have hrep0 (j : ℕ) (hj : j ∈ I0) :
      Z.gamma (reflectionRep Z j) ∈ S0 :=
    Finset.mem_image.mpr ⟨j, hj, rfl⟩
  have hBrep (j : ℕ) (hj : j ∈ I0) :
      fourierLaplace b (Z.gamma (reflectionRep Z j)) = 1 := by
    simpa only [a0] using hb ⟨Z.gamma (reflectionRep Z j), hrep0 j hj⟩
  have hBn : fourierLaplace b (Z.gamma n) = 1 := by
    rcases reflectionRep_freq Z n with hsame | hneg
    · rw [← hsame]
      exact hBrep n (by simp [I0])
    · calc
        fourierLaplace b (Z.gamma n) = fourierLaplace b (-Z.gamma n) :=
          (fourierLaplace_neg b (Z.gamma n)).symm
        _ = fourierLaplace b (Z.gamma (reflectionRep Z n)) := by rw [hneg]
        _ = 1 := hBrep n (by simp [I0])
  have hBc : fourierLaplace b (Z.gamma (Z.conjugation n)) = 1 := by
    rcases reflectionRep_freq Z (Z.conjugation n) with hsame | hneg
    · rw [← hsame]
      exact hBrep (Z.conjugation n) (by simp [I0])
    · calc
        fourierLaplace b (Z.gamma (Z.conjugation n)) =
            fourierLaplace b (-Z.gamma (Z.conjugation n)) :=
          (fourierLaplace_neg b (Z.gamma (Z.conjugation n))).symm
        _ = fourierLaplace b
            (Z.gamma (reflectionRep Z (Z.conjugation n))) := by rw [hneg]
        _ = 1 := hBrep (Z.conjugation n) (by simp [I0])
  have hBcn : fourierLaplace b (conj (Z.gamma n)) = 1 := by
    calc
      fourierLaplace b (conj (Z.gamma n)) =
          fourierLaplace b (-conj (Z.gamma n)) :=
        (fourierLaplace_neg b (conj (Z.gamma n))).symm
      _ = fourierLaplace b (Z.gamma (Z.conjugation n)) := by
        rw [Z.gamma_conjugation]
      _ = 1 := hBc
  obtain ⟨C, hC, hdecay⟩ :=
    fourierLaplace_decay_closedStrip b (1 / 2) (by norm_num)
  let R : ℝ := max (2 * C + 1) ‖Z.gamma n‖
  let E : Finset ℕ := Z.symmetricIndices R
  have hnE : n ∈ E := by
    change n ∈ Z.symmetricIndices R
    rw [Z.mem_symmetricIndices]
    exact le_max_right _ _
  have hreflectionE (j : ℕ) : j ∈ E ↔ Z.reflection j ∈ E := by
    simpa only [E] using (Z.reflection_mem_symmetricIndices (T := R) (n := j)).symm
  have hconjugationE (j : ℕ) : j ∈ E ↔ Z.conjugation j ∈ E := by
    simpa only [E] using (Z.conjugation_mem_symmetricIndices (T := R) (n := j)).symm
  have hOsub : zeroOrbit Z n ⊆ E := by
    intro j hj
    simp only [zeroOrbit, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl
    · exact hnE
    · exact (hreflectionE n).1 hnE
    · exact (hconjugationE n).1 hnE
    · exact (hconjugationE (Z.reflection n)).1 ((hreflectionE n).1 hnE)
  have hdenominator (j : ℕ) (hj : j ∉ E) :
      2 * C ≤ 1 + (Z.gamma j).re ^ 2 := by
    have hnot : ¬ ‖Z.gamma j‖ ≤ R := by
      simpa only [E, Z.mem_symmetricIndices] using hj
    have hnorm : R < ‖Z.gamma j‖ := lt_of_not_ge hnot
    have hlarge : 2 * C + 1 < ‖Z.gamma j‖ :=
      lt_of_le_of_lt (le_max_left _ _) hnorm
    have hleft : 0 ≤ 2 * C + 1 := by linarith
    have hsq : (2 * C + 1) ^ 2 < ‖Z.gamma j‖ ^ 2 := by
      nlinarith [norm_nonneg (Z.gamma j)]
    have him := gamma_mem_closed_half_strip Z j
    have himsqAbs : |(Z.gamma j).im| ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      nlinarith [abs_nonneg (Z.gamma j).im]
    have himsq : (Z.gamma j).im ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      simpa only [sq_abs] using himsqAbs
    have hnormsq :
        ‖Z.gamma j‖ ^ 2 = (Z.gamma j).re ^ 2 + (Z.gamma j).im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    nlinarith [sq_nonneg C]
  have htail : ∀ j ∉ E,
      ‖fourierLaplace b (Z.gamma j)‖ ≤ 1 / 2 ∧
      ‖fourierLaplace b (conj (Z.gamma j))‖ ≤ 1 / 2 := by
    intro j hj
    have hden : 0 < 1 + (Z.gamma j).re ^ 2 := by positivity
    have hfrac : C / (1 + (Z.gamma j).re ^ 2) ≤ (1 / 2 : ℝ) := by
      apply (div_le_iff₀ hden).2
      nlinarith [hdenominator j hj]
    constructor
    · exact (hdecay (Z.gamma j) (gamma_mem_closed_half_strip Z j)).trans hfrac
    · have hstripConj : |(conj (Z.gamma j)).im| ≤ (1 / 2 : ℝ) := by
        simpa using gamma_mem_closed_half_strip Z j
      have hcdecay := hdecay (conj (Z.gamma j)) hstripConj
      simpa only [Complex.conj_re] using hcdecay.trans hfrac
  let S : Finset ℂ := E.image (fun j => Z.gamma (reflectionRep Z j))
  have hsep : ∀ ⦃z w : ℂ⦄, z ∈ S → w ∈ S → z ≠ w → z ≠ -w := by
    simpa only [S] using reflectionRep_image_sep Z E
  have htargetFreqNe :
      Z.gamma (reflectionRep Z n) ≠
        Z.gamma (reflectionRep Z (Z.conjugation n)) := by
    intro heq
    exact htargetRepNe (gamma_injective Z heq)
  let a : S → ℂ := fun z =>
    if z.1 = Z.gamma (reflectionRep Z n) then 1
    else if z.1 = Z.gamma (reflectionRep Z (Z.conjugation n)) then -1
    else 0
  obtain ⟨k, hk⟩ := even_weilTestFunction_finite_interpolation S hsep a
  have hrep_in_S {j : ℕ} (hj : j ∈ E) :
      Z.gamma (reflectionRep Z j) ∈ S :=
    Finset.mem_image.mpr ⟨j, hj, rfl⟩
  have hKrep (j : ℕ) (hj : j ∈ E) :
      fourierLaplace k (Z.gamma (reflectionRep Z j)) =
        if Z.gamma (reflectionRep Z j) = Z.gamma (reflectionRep Z n) then 1
        else if Z.gamma (reflectionRep Z j) =
            Z.gamma (reflectionRep Z (Z.conjugation n)) then -1
        else 0 := by
    simpa only [a] using hk ⟨Z.gamma (reflectionRep Z j), hrep_in_S hj⟩
  have hK (j : ℕ) (hj : j ∈ E) :
      fourierLaplace k (Z.gamma j) =
        if Z.gamma (reflectionRep Z j) = Z.gamma (reflectionRep Z n) then 1
        else if Z.gamma (reflectionRep Z j) =
            Z.gamma (reflectionRep Z (Z.conjugation n)) then -1
        else 0 := by
    rcases reflectionRep_freq Z j with hsame | hneg
    · rw [← hsame]
      exact hKrep j hj
    · calc
        fourierLaplace k (Z.gamma j) = fourierLaplace k (-Z.gamma j) :=
          (fourierLaplace_neg k (Z.gamma j)).symm
        _ = fourierLaplace k (Z.gamma (reflectionRep Z j)) := by rw [hneg]
        _ = _ := hKrep j hj
  have hKn : fourierLaplace k (Z.gamma n) = 1 := by
    simpa using hK n hnE
  have hcE : Z.conjugation n ∈ E := (hconjugationE n).1 hnE
  have hKc : fourierLaplace k (Z.gamma (Z.conjugation n)) = -1 := by
    have hne :
        Z.gamma (reflectionRep Z (Z.conjugation n)) ≠
          Z.gamma (reflectionRep Z n) := htargetFreqNe.symm
    simpa [hne] using hK (Z.conjugation n) hcE
  have hKcn : fourierLaplace k (conj (Z.gamma n)) = -1 := by
    calc
      fourierLaplace k (conj (Z.gamma n)) =
          fourierLaplace k (-conj (Z.gamma n)) :=
        (fourierLaplace_neg k (conj (Z.gamma n))).symm
      _ = fourierLaplace k (Z.gamma (Z.conjugation n)) := by
        rw [Z.gamma_conjugation]
      _ = -1 := hKc
  have hKzero (j : ℕ) (hj : j ∈ E) (hjO : j ∉ zeroOrbit Z n) :
      fourierLaplace k (Z.gamma j) = 0 := by
    have hneN :
        Z.gamma (reflectionRep Z j) ≠ Z.gamma (reflectionRep Z n) := by
      intro heq
      rcases reflectionRep_eq_or Z j n (gamma_injective Z heq) with hjn | hjn
      · exact hjO (by simp [zeroOrbit, hjn])
      · exact hjO (by simp [zeroOrbit, hjn])
    have hneC :
        Z.gamma (reflectionRep Z j) ≠
          Z.gamma (reflectionRep Z (Z.conjugation n)) := by
      intro heq
      rcases reflectionRep_eq_or Z j (Z.conjugation n)
          (gamma_injective Z heq) with hjc | hjc
      · exact hjO (by simp [zeroOrbit, hjc])
      · apply hjO
        simp only [zeroOrbit, Finset.mem_insert, Finset.mem_singleton]
        right; right; right
        calc
          j = Z.reflection (Z.conjugation n) := hjc
          _ = Z.conjugation (Z.reflection n) := zero_symmetries_commute Z n
    simpa [hneN, hneC] using hK j hj
  have hKzeroPair : ∀ j ∈ E, j ∉ zeroOrbit Z n →
      fourierLaplace k (Z.gamma j) = 0 ∧
      fourierLaplace k (conj (Z.gamma j)) = 0 := by
    intro j hj hjO
    have hcjE : Z.conjugation j ∈ E := (hconjugationE j).1 hj
    have hcjO : Z.conjugation j ∉ zeroOrbit Z n := by
      exact fun hcj => hjO ((zeroOrbit_conjugation_mem Z n j).1 hcj)
    constructor
    · exact hKzero j hj hjO
    · calc
        fourierLaplace k (conj (Z.gamma j)) =
            fourierLaplace k (-conj (Z.gamma j)) :=
          (fourierLaplace_neg k (conj (Z.gamma j))).symm
        _ = fourierLaplace k (Z.gamma (Z.conjugation j)) := by
          rw [Z.gamma_conjugation]
        _ = 0 := hKzero (Z.conjugation j) hcjE hcjO
  exact ⟨b, k, E, hreflectionE, hconjugationE, hOsub,
    hBn, hBcn, hKn, hKcn, htail, hKzeroPair⟩

/-- The frozen zeta-zero absolute summability theorem, transported to an arbitrary
duplicate-free `ZeroData` enumeration. -/
theorem zeroSummand_summable_of_zeroData
    (Z : ZeroData) (g : WeilTestFunction) : Summable (zeroSummand Z g) := by
  obtain ⟨hsummable, _hsum⟩ :=
    Zeta23.WeilEF.EF_lit_zetaZeroConfig (g : ℝ → ℂ)
      (g.contDiff.of_le (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by
        exact WithTop.coe_le_coe.mpr le_top))
      g.hasCompactSupport
  let setSubtypeEquiv : {rho : ℂ // Zeta23.IsNontrivialZero rho} ≃
      ↥{rho : ℂ | Zeta23.IsNontrivialZero rho} :=
    { toFun := fun rho => ⟨rho, rho.property⟩
      invFun := fun rho => ⟨rho, rho.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e := (zeroEquiv Z).trans setSubtypeEquiv
  let f : ↥{rho : ℂ | Zeta23.IsNontrivialZero rho} → ℂ := fun rho =>
    (Zeta23.zeroMult rho : ℂ) * Zeta23.paperFT (g : ℝ → ℂ) (Zeta23.gammaOf rho)
  let a : ℕ → ℂ := fun n => zeroSummand Z g n
  have hterm : ∀ n, f (e n) = a n := by
    intro n
    change (Zeta23.zeroMult (Z.zero n) : ℂ) *
        Zeta23.paperFT (g : ℝ → ℂ) (Zeta23.gammaOf (Z.zero n)) =
      (Z.multiplicity n : ℂ) * fourierLaplace g (Z.gamma n)
    rw [← multiplicity_eq_zeroMult Z n, paperFT_eq_fourierLaplace,
      gammaOf_eq_spectralParameter]
    rfl
  have ha : HasSum a (∑' rho, f rho) := by
    have hf : HasSum (f ∘ e) (∑' rho, f rho) :=
      e.hasSum_iff.mpr hsummable.hasSum
    exact hf.congr_fun fun n => (hterm n).symm
  simpa only [a] using ha.summable

/-- Exact pointwise transform factorization for the Burnol power packet. -/
private theorem fourierLaplace_convolutionSquare_power_killer
    (b k : WeilTestFunction) (N : ℕ) (z : ℂ) :
    fourierLaplace
        (convolutionSquare (convolve (convolutionSuccPower b N) k)) z =
      (fourierLaplace b z * conj (fourierLaplace b (conj z))) ^ (N + 1) *
        (fourierLaplace k z * conj (fourierLaplace k (conj z))) := by
  rw [fourierLaplace_convolutionSquare_complex,
    fourierLaplace_convolve_complex, fourierLaplace_convolve_complex,
    fourierLaplace_convolutionSuccPower,
    fourierLaplace_convolutionSuccPower]
  simp only [map_mul, map_pow, mul_pow]
  ring

/-- The same factorization with multiplicity included in `zeroSummand`. -/
private theorem zeroSummand_convolutionSquare_power_killer
    (Z : ZeroData) (b k : WeilTestFunction) (N j : ℕ) :
    zeroSummand Z
        (convolutionSquare (convolve (convolutionSuccPower b N) k)) j =
      (fourierLaplace b (Z.gamma j) *
          conj (fourierLaplace b (conj (Z.gamma j)))) ^ (N + 1) *
        zeroSummand Z (convolutionSquare k) j := by
  rw [zeroSummand, fourierLaplace_convolutionSquare_power_killer,
    zeroSummand, fourierLaplace_convolutionSquare_complex]
  ring

/-- Outside the selected orbit, the power packet is pointwise dominated by the
geometric factor times the killer's convolution-square summand. -/
private theorem norm_zeroSummand_power_killer_le
    (Z : ZeroData) (n : ℕ) (b k : WeilTestFunction) (E : Finset ℕ) (N j : ℕ)
    (hB : ∀ i ∉ E,
      ‖fourierLaplace b (Z.gamma i)‖ ≤ (1 / 2 : ℝ) ∧
      ‖fourierLaplace b (conj (Z.gamma i))‖ ≤ (1 / 2 : ℝ))
    (hK : ∀ i ∈ E, i ∉ zeroOrbit Z n →
      fourierLaplace k (Z.gamma i) = 0 ∧
      fourierLaplace k (conj (Z.gamma i)) = 0)
    (hjO : j ∉ zeroOrbit Z n) :
    ‖zeroSummand Z
        (convolutionSquare (convolve (convolutionSuccPower b N) k)) j‖ ≤
      (1 / 4 : ℝ) ^ (N + 1) *
        ‖zeroSummand Z (convolutionSquare k) j‖ := by
  rw [zeroSummand_convolutionSquare_power_killer, norm_mul, norm_pow]
  by_cases hjE : j ∈ E
  · have hKj := hK j hjE hjO
    have hzero : zeroSummand Z (convolutionSquare k) j = 0 := by
      rw [zeroSummand, fourierLaplace_convolutionSquare_complex, hKj.1]
      simp
    rw [hzero, norm_zero, mul_zero, mul_zero]
  · have hBj := hB j hjE
    have hbase :
        ‖fourierLaplace b (Z.gamma j) *
          conj (fourierLaplace b (conj (Z.gamma j)))‖ ≤ (1 / 4 : ℝ) := by
      rw [norm_mul, Complex.norm_conj]
      calc
        ‖fourierLaplace b (Z.gamma j)‖ *
            ‖fourierLaplace b (conj (Z.gamma j))‖ ≤
            (1 / 2 : ℝ) * (1 / 2 : ℝ) :=
          mul_le_mul hBj.1 hBj.2 (norm_nonneg _) (by norm_num)
        _ = 1 / 4 := by norm_num
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) hbase (N + 1)) (norm_nonneg _)

/-- Burnol's geometric tail estimate, with the majorant summed over the full
`ZeroData` enumeration.  The left-hand `tsum` ranges over the complement of the
four-point orbit. -/
theorem burnol_power_tail_bound
    (Z : ZeroData) (n : ℕ) (b k : WeilTestFunction) (E : Finset ℕ) (N : ℕ)
    (hB : ∀ i ∉ E,
      ‖fourierLaplace b (Z.gamma i)‖ ≤ (1 / 2 : ℝ) ∧
      ‖fourierLaplace b (conj (Z.gamma i))‖ ≤ (1 / 2 : ℝ))
    (hK : ∀ i ∈ E, i ∉ zeroOrbit Z n →
      fourierLaplace k (Z.gamma i) = 0 ∧
      fourierLaplace k (conj (Z.gamma i)) = 0) :
    Summable (fun j : {j : ℕ // j ∉ zeroOrbit Z n} =>
      zeroSummand Z
        (convolutionSquare (convolve (convolutionSuccPower b N) k)) j.1) ∧
    ‖∑' j : {j : ℕ // j ∉ zeroOrbit Z n},
      zeroSummand Z
        (convolutionSquare (convolve (convolutionSuccPower b N) k)) j.1‖ ≤
      (1 / 4 : ℝ) ^ (N + 1) *
        ∑' j : ℕ, ‖zeroSummand Z (convolutionSquare k) j‖ := by
  let c : ℝ := (1 / 4 : ℝ) ^ (N + 1)
  let tail : {j : ℕ // j ∉ zeroOrbit Z n} → ℂ := fun j =>
    zeroSummand Z
      (convolutionSquare (convolve (convolutionSuccPower b N) k)) j.1
  let major : ℕ → ℝ := fun j =>
    ‖zeroSummand Z (convolutionSquare k) j‖
  have hmajorAll : Summable major := by
    simpa only [major] using (zeroSummand_summable_of_zeroData Z
      (convolutionSquare k)).norm
  have hmajorSub : Summable (fun j : {j : ℕ // j ∉ zeroOrbit Z n} => major j.1) :=
    hmajorAll.subtype _
  have hscaled : Summable
      (fun j : {j : ℕ // j ∉ zeroOrbit Z n} => c * major j.1) :=
    hmajorSub.mul_left c
  have hpoint : ∀ j : {j : ℕ // j ∉ zeroOrbit Z n},
      ‖tail j‖ ≤ c * major j.1 := by
    intro j
    simpa only [tail, c, major] using
      norm_zeroSummand_power_killer_le Z n b k E N j.1 hB hK j.2
  have htailNorm : Summable (fun j => ‖tail j‖) :=
    hscaled.of_nonneg_of_le (fun j => norm_nonneg (tail j)) hpoint
  have htail : Summable tail := htailNorm.of_norm
  refine ⟨htail, ?_⟩
  change ‖∑' j, tail j‖ ≤ c * ∑' j, major j
  calc
    ‖∑' j, tail j‖ ≤ ∑' j, ‖tail j‖ :=
      norm_tsum_le_tsum_norm htailNorm
    _ ≤ ∑' j : {j : ℕ // j ∉ zeroOrbit Z n}, c * major j.1 :=
      htailNorm.tsum_le_tsum hpoint hscaled
    _ = c * ∑' j : {j : ℕ // j ∉ zeroOrbit Z n}, major j.1 := by
      rw [tsum_mul_left]
    _ ≤ c * ∑' j : ℕ, major j := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ c)
      exact hmajorAll.tsum_subtype_le major
        (fun j => j ∉ zeroOrbit Z n) (fun j => norm_nonneg _)

/-- A nonnegative finite majorant is eventually beaten by the geometric
`(1/4)^(N+1)` factor. -/
theorem exists_quarter_power_mul_lt
    (S epsilon : ℝ) (hS : 0 ≤ S) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, (1 / 4 : ℝ) ^ (N + 1) * S < epsilon := by
  by_cases hSzero : S = 0
  · exact ⟨0, by simp [hSzero, hepsilon]⟩
  · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hSzero)
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
      (div_pos hepsilon hSpos) (by norm_num : (1 / 4 : ℝ) < 1)
    refine ⟨N, lt_of_le_of_lt ?_ ((lt_div_iff₀ hSpos).mp hN)⟩
    apply mul_le_mul_of_nonneg_right _ hS
    rw [pow_succ]
    calc
      (1 / 4 : ℝ) ^ N * (1 / 4 : ℝ) ≤
          (1 / 4 : ℝ) ^ N * 1 :=
        mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
      _ = (1 / 4 : ℝ) ^ N := mul_one _

/-- Absolute summability identifies every symmetric `zeroSum` witness with the
ordinary `tsum` over the supplied enumeration. -/
theorem zeroSum_eq_tsum_of_zeroData
    (Z : ZeroData) (g : WeilTestFunction) (hZero : SymmetricConvergent Z g) :
    zeroSum Z g hZero = ∑' j : ℕ, zeroSummand Z g j := by
  apply zeroSum_eq_of_tendsto Z g hZero
  have hcutoff := (zeroSummand_summable_of_zeroData Z g).hasSum.comp
    (tendsto_symmetricIndices Z)
  simpa only [truncatedZeroSum, Function.comp_def] using hcutoff

/-- The completed nonreal off-line separator: convolution powering preserves
the prescribed negative orbit while making the absolutely summed complement
strictly smaller than its `4 * multiplicity` magnitude. -/
theorem offLineNonrealZero_yields_negative_weil_square
    (Z : ZeroData) (n : ℕ)
    (hOff : (Z.zero n).re ≠ criticalAbscissa)
    (hIm : (Z.zero n).im ≠ 0) :
    ∃ g : WeilTestFunction,
      ∃ hZero : SymmetricConvergent Z (convolutionSquare g),
        (zeroSum Z (convolutionSquare g) hZero).re < 0 := by
  classical
  obtain ⟨b, k, E, _hreflectionE, _hconjugationE, _hOsub,
      hBn, hBcn, hKn, hKcn, hB, hK⟩ :=
    exists_peak_and_finite_exception_killer Z n hOff hIm
  let S : ℝ := ∑' j : ℕ, ‖zeroSummand Z (convolutionSquare k) j‖
  have hS : 0 ≤ S := tsum_nonneg fun j => norm_nonneg _
  have hmult : 0 < 4 * (Z.multiplicity n : ℝ) := by
    exact mul_pos (by norm_num) (Nat.cast_pos.mpr (Z.multiplicity_pos n))
  obtain ⟨N, hN⟩ := exists_quarter_power_mul_lt S
    (4 * (Z.multiplicity n : ℝ)) hS hmult
  let g : WeilTestFunction := convolve (convolutionSuccPower b N) k
  have hgn : fourierLaplace g (Z.gamma n) = 1 := by
    dsimp only [g]
    rw [fourierLaplace_convolve_complex,
      fourierLaplace_convolutionSuccPower, hBn, hKn]
    simp
  have hgcn : fourierLaplace g (conj (Z.gamma n)) = -1 := by
    dsimp only [g]
    rw [fourierLaplace_convolve_complex,
      fourierLaplace_convolutionSuccPower, hBcn, hKcn]
    simp
  have horbit :
      (∑ j ∈ zeroOrbit Z n,
        zeroSummand Z (convolutionSquare g) j).re =
          -4 * (Z.multiplicity n : ℝ) := by
    simpa only [zeroOrbit] using
      prescribed_pair_gives_negative_zero_orbit Z n hOff hIm g hgn hgcn
  have htail := burnol_power_tail_bound Z n b k E N hB hK
  have htailStrict :
      ‖∑' j : {j : ℕ // j ∉ zeroOrbit Z n},
        zeroSummand Z (convolutionSquare g) j.1‖ <
          4 * (Z.multiplicity n : ℝ) := by
    apply lt_of_le_of_lt _ hN
    simpa only [g, S] using htail.2
  let hZero := symmetricConvergent_of_zeroData Z (convolutionSquare g)
  refine ⟨g, hZero, ?_⟩
  rw [zeroSum_eq_tsum_of_zeroData]
  have hall := zeroSummand_summable_of_zeroData Z (convolutionSquare g)
  have hdecomp := hall.sum_add_tsum_subtype_compl (zeroOrbit Z n)
  rw [← hdecomp, Complex.add_re, horbit]
  have htailRe :
      (∑' j : {j : ℕ // j ∉ zeroOrbit Z n},
        zeroSummand Z (convolutionSquare g) j.1).re <
          4 * (Z.multiplicity n : ℝ) :=
    (Complex.re_le_norm _).trans_lt htailStrict
  linarith

#print axioms exists_peak_and_finite_exception_killer
#print axioms burnol_power_tail_bound
#print axioms offLineNonrealZero_yields_negative_weil_square

-- These checked terms expose the exact hypothesis bundle and inhabited domains.
example (Z : ZeroData) (n : ℕ)
    (hOff : (Z.zero n).re ≠ criticalAbscissa)
    (hIm : (Z.zero n).im ≠ 0) :
    (Z.zero n).re ≠ criticalAbscissa ∧ (Z.zero n).im ≠ 0 :=
  ⟨hOff, hIm⟩

example (Z : ZeroData) : Nonempty ZeroData := ⟨Z⟩

example : Nonempty WeilTestFunction := ⟨standardTestFunction⟩

end

end D5.S3.Weil.ZetaBridge.OffLineNonrealZeroNegativeWeilSquare
