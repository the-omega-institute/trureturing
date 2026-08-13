/- GID: D5/S3/Weil/ZetaBridge/ClassicExplicitFormula
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/ClassicExplicitFormula
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Transport the hypothesis-free zeta formula into the frozen Weil vocabulary. -/

import D5.S3.Weil.PrimePoleTerms
import D5.S3.Weil.ZeroSum
import D5.S3.Weil.ZetaExplicit.Main

namespace D5.S3.Weil.ZetaBridge.ClassicExplicitFormula

open Filter MeasureTheory
open D5.S3.Weil.Convention D5.S3.Weil.TestFunctions
open D5.S3.Weil.FourierLaplace D5.S3.Weil.PrimePoleTerms
open D5.S3.Weil.ZeroSum
open scoped ArithmeticFunction

noncomputable section

/-- A duplicate-free exhaustive `ZeroData` enumeration is equivalent to the subtype of
nontrivial zeta zeros used by the ported explicit formula. -/
def zeroEquiv (Z : ZeroData) : ℕ ≃ {rho : ℂ // Zeta23.IsNontrivialZero rho} :=
  Equiv.ofBijective
    (fun n => ⟨Z.zero n, by
      simpa [D5.S3.Weil.ZeroSum.IsNontrivialZero, classicalZeta,
        Zeta23.IsNontrivialZero] using Z.zero_isNontrivial n⟩)
    ⟨fun _ _ h => Z.zero_injective (Subtype.ext_iff.mp h), fun rho => by
      obtain ⟨n, hn⟩ := Z.zero_exhaustive (by
        simpa [D5.S3.Weil.ZeroSum.IsNontrivialZero, classicalZeta,
          Zeta23.IsNontrivialZero] using rho.property)
      exact ⟨n, Subtype.ext hn⟩⟩

/-- The exact local factorization stored by `ZeroData` identifies its multiplicity with the
analytic order used by the ported zero configuration. -/
theorem multiplicity_eq_zeroMult (Z : ZeroData) (n : ℕ) :
    Z.multiplicity n = Zeta23.zeroMult (Z.zero n) := by
  obtain ⟨_hmpos, u, hu, hu0, hfac⟩ := Z.multiplicity_spec n
  have hzero := Z.zero_isNontrivial n
  have hne : Z.zero n ≠ 1 := by
    intro h
    rw [h] at hzero
    simpa [D5.S3.Weil.ZeroSum.IsNontrivialZero, classicalZeta] using hzero.2.2
  have hzeta : AnalyticAt ℂ riemannZeta (Z.zero n) :=
    analyticOn_riemannZeta (Z.zero n) (by simpa using hne)
  have hord : analyticOrderAt riemannZeta (Z.zero n) = Z.multiplicity n :=
    hzeta.analyticOrderAt_eq_natCast.mpr ⟨u, hu, hu0, by
      filter_upwards [hfac] with z hz
      simpa [classicalZeta, smul_eq_mul] using hz⟩
  simp [Zeta23.zeroMult, hord]

/-- The paper's positive-exponential transform agrees with the repository's negative-exponential
transform on even tests. -/
theorem paperFT_eq_fourierLaplace (g : WeilTestFunction) (z : ℂ) :
    Zeta23.paperFT (g : ℝ → ℂ) z = fourierLaplace g z := by
  calc
    Zeta23.paperFT (g : ℝ → ℂ) z = fourierLaplace g (-z) := by
      unfold Zeta23.paperFT fourierLaplace fourierKernel
      apply integral_congr_ae
      filter_upwards with x
      rw [mul_comm]
      congr 1
      ring
    _ = fourierLaplace g z := fourierLaplace_neg g z

/-- The paper and repository spectral parameters are definitionally the same complex number. -/
theorem gammaOf_eq_spectralParameter (rho : ℂ) :
    Zeta23.gammaOf rho = spectralParameter rho := by
  unfold Zeta23.gammaOf spectralParameter criticalAbscissa
  simp [div_eq_mul_inv]
  ring

/-- Symmetric spectral balls eventually contain every finite set of enumeration indices. -/
theorem tendsto_symmetricIndices (Z : ZeroData) :
    Tendsto (fun T : ℝ => Z.symmetricIndices T) atTop atTop := by
  rw [tendsto_atTop]
  intro s
  let B : ℝ := ∑ n ∈ s, ‖Z.gamma n‖
  filter_upwards [eventually_ge_atTop B] with T hT
  intro n hn
  rw [Z.mem_symmetricIndices]
  exact (Finset.single_le_sum (fun m _ => norm_nonneg (Z.gamma m)) hn).trans hT

/-- The ported prime coefficient `Lambda(n) / sqrt(n)` is the repository's
`Lambda(n) * n^(-1/2)`, including the totalized `n = 0` case. -/
theorem vonMangoldt_div_sqrt (n : ℕ) :
    ArithmeticFunction.vonMangoldt n / Real.sqrt n =
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hnpos.le]
    ring

/-- The literature RHS from the port is exactly the frozen pole-minus-prime-plus-archimedean
combination. -/
theorem literatureRHS_eq (g : WeilTestFunction) (hArch : ArchimedeanConvergent g) :
    Zeta23.EF.literatureRHS (g : ℝ → ℂ) =
      poleTerm g - primeTerm g + archimedeanTerm g hArch := by
  unfold Zeta23.EF.literatureRHS poleTerm primeTerm primeSummand archimedeanTerm
    archimedeanIntegrand Zeta23.EF.gammaBracket
  rw [paperFT_eq_fourierLaplace, paperFT_eq_fourierLaplace]
  have hprime :
      (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        (g (Real.log n) + g (-Real.log n))) =
      ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        (g (Real.log n) + g (-Real.log n)) := by
    apply tsum_congr
    intro n
    rw [vonMangoldt_div_sqrt]
    push_cast
    ring
  rw [hprime]
  have hpole : fourierLaplace g (Complex.I / 2) + fourierLaplace g (-Complex.I / 2) =
      fourierLaplace g (-Complex.I / 2) + fourierLaplace g (Complex.I / 2) := add_comm _ _
  have harch :
      (1 / (2 * Real.pi) : ℂ) *
          ∫ t : ℝ, Zeta23.paperFT (g : ℝ → ℂ) t *
            (((Complex.digamma (1 / 4 + Complex.I * (t : ℂ) / 2)).re -
              Real.log Real.pi : ℝ) : ℂ) =
        (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          ∫ t : ℝ,
            (((Complex.digamma (1 / 4 + Complex.I * (t : ℂ) / 2)).re -
              Real.log Real.pi : ℝ) : ℂ) * fourierLaplace g t := by
    congr 1
    · norm_cast
    · apply integral_congr_ae
      filter_upwards with t
      rw [paperFT_eq_fourierLaplace]
      ring
  rw [hpole, harch]

/-- The hypothesis-free port implies the classical explicit formula in the repository's frozen
`ZeroData`, `WeilTestFunction`, and symmetric-cutoff vocabulary. -/
theorem weil_explicit_formula
    (Z : ZeroData) (g : WeilTestFunction)
    (hZero : SymmetricConvergent Z g) (hArch : ArchimedeanConvergent g) :
    zeroSum Z g hZero = poleTerm g - primeTerm g + archimedeanTerm g hArch := by
  obtain ⟨hsummable, hsum⟩ :=
    Zeta23.WeilEF.EF_lit_zetaZeroConfig (g : ℝ → ℂ)
      (g.contDiff.of_le (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by
        exact WithTop.coe_le_coe.mpr le_top))
      g.hasCompactSupport
  let e := zeroEquiv Z
  let f : {rho : ℂ // Zeta23.IsNontrivialZero rho} → ℂ := fun rho =>
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
  have hcutoff : Tendsto (fun T : ℝ => ∑ n ∈ Z.symmetricIndices T, a n)
      atTop (nhds (∑' rho, f rho)) :=
    ha.comp (tendsto_symmetricIndices Z)
  have hzeroTsum : zeroSum Z g hZero = ∑' rho, f rho := by
    apply zeroSum_eq_of_tendsto Z g hZero
    simpa [truncatedZeroSum, a] using hcutoff
  calc
    zeroSum Z g hZero = ∑' rho, f rho := hzeroTsum
    _ = Zeta23.EF.literatureRHS (g : ℝ → ℂ) := by simpa [f] using hsum
    _ = poleTerm g - primeTerm g + archimedeanTerm g hArch := literatureRHS_eq g hArch

end

end D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
