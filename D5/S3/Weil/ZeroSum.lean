/- GID: D5/S3/Weil/ZeroSum
   generality: I
   mirror-B: none(waiver:formal-analysis-foundation-only)
   mirror-E: none(waiver:structural-explicit-formula-terms-only)
   anchors: []
   digest: Bind multiplicity-weighted zeta zeros through finite symmetric spectral cutoffs. -/

import D5.S3.Weil.FourierLaplace

namespace D5.S3.Weil.ZeroSum

open Filter MeasureTheory
open D5.S3.Weil.Convention D5.S3.Weil.TestFunctions
open D5.S3.Weil.FourierLaplace
open scoped ComplexConjugate

/-!
The spectral parameter is complex: `rho = 1 / 2 + i * gamma(rho)` holds
without RH.  Consequently the symmetric cutoff below uses the complex norm
`|gamma(rho)|`, not an assumption that every ordinate is real.
-/

/-- The nontrivial zeros are the zeros of the classical zeta in the open critical strip. -/
def IsNontrivialZero (rho : ℂ) : Prop :=
  classicalZeta rho = 0 ∧ 0 < rho.re ∧ rho.re < 1

/--
`rho` is a zero of exact order `m`: locally zeta is `(z - rho)^m` times an
analytic unit.  This avoids pretending that pinned mathlib provides a
zeta-specific zero-multiplicity API.
-/
def HasZetaZeroMultiplicity (rho : ℂ) (m : ℕ) : Prop :=
  0 < m ∧
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u rho ∧ u rho ≠ 0 ∧
      classicalZeta =ᶠ[nhds rho] fun z => (z - rho) ^ m * u z

/-- The complex spectral parameter in `rho = 1 / 2 + i * gamma(rho)`. -/
noncomputable def spectralParameter (rho : ℂ) : ℂ :=
  -Complex.I * (rho - (criticalAbscissa : ℂ))

/-- The critical-line parameterization is an identity, not RH. -/
theorem spectralParameter_reconstruct (rho : ℂ) :
    (criticalAbscissa : ℂ) + Complex.I * spectralParameter rho = rho := by
  unfold spectralParameter
  rw [← mul_assoc, show Complex.I * -Complex.I = (1 : ℂ) by simp]
  ring

/-- Functional-equation reflection negates the spectral parameter. -/
theorem spectralParameter_reflection (rho : ℂ) :
    spectralParameter (1 - rho) = -spectralParameter rho := by
  simp [spectralParameter, criticalAbscissa]
  ring

/-- Complex conjugation sends `gamma` to `-conj gamma`. -/
theorem spectralParameter_conjugation (rho : ℂ) :
    spectralParameter (conj rho) = -conj (spectralParameter rho) := by
  apply Complex.ext <;> simp [spectralParameter, criticalAbscissa]

/-- The symmetric cutoff radius attached to a zero. -/
noncomputable def spectralRadius (rho : ℂ) : ℝ :=
  ‖spectralParameter rho‖

/--
Explicit data missing from pinned mathlib: a duplicate-free exhaustive
enumeration of the classical nontrivial zeta zeros, their exact analytic
multiplicities, the two classical symmetries, and finite spectral balls.

No inhabitant is asserted here.  Downstream statements must carry a value of
this structure, so the missing classical enumeration theorem remains an
explicit assumption rather than a hidden axiom or a free zero-sum functional.
-/
structure ZeroData where
  zero : ℕ → ℂ
  multiplicity : ℕ → ℕ
  zero_injective : Function.Injective zero
  zero_isNontrivial : ∀ n, IsNontrivialZero (zero n)
  zero_exhaustive : ∀ {rho}, IsNontrivialZero rho → ∃ n, zero n = rho
  multiplicity_spec : ∀ n, HasZetaZeroMultiplicity (zero n) (multiplicity n)
  reflection : Equiv.Perm ℕ
  zero_reflection : ∀ n, zero (reflection n) = 1 - zero n
  multiplicity_reflection : ∀ n, multiplicity (reflection n) = multiplicity n
  conjugation : Equiv.Perm ℕ
  zero_conjugation : ∀ n, zero (conjugation n) = conj (zero n)
  multiplicity_conjugation : ∀ n, multiplicity (conjugation n) = multiplicity n
  locallyFinite : ∀ T : ℝ, {n | spectralRadius (zero n) ≤ T}.Finite

/-- The stored multiplicity is positive because it is an exact zero order. -/
theorem ZeroData.multiplicity_pos (Z : ZeroData) (n : ℕ) :
    0 < Z.multiplicity n :=
  (Z.multiplicity_spec n).1

/-- Exhaustiveness and duplicate-freeness identify each nontrivial zero exactly once. -/
theorem ZeroData.existsUnique_zero (Z : ZeroData) {rho : ℂ}
    (hrho : IsNontrivialZero rho) : ∃! n, Z.zero n = rho := by
  obtain ⟨n, hn⟩ := Z.zero_exhaustive hrho
  refine ⟨n, hn, ?_⟩
  intro m hm
  exact Z.zero_injective (hm.trans hn.symm)

/-- The spectral parameter of the `n`th distinct nontrivial zero. -/
noncomputable def ZeroData.gamma (Z : ZeroData) (n : ℕ) : ℂ :=
  spectralParameter (Z.zero n)

/-- Every enumerated zero has the fixed `1 / 2 + i * gamma` representation. -/
theorem ZeroData.zero_eq_critical_add_I_mul_gamma (Z : ZeroData) (n : ℕ) :
    Z.zero n = (criticalAbscissa : ℂ) + Complex.I * Z.gamma n := by
  exact (spectralParameter_reconstruct (Z.zero n)).symm

/-- Reflection pairs `gamma` with `-gamma`. -/
@[simp]
theorem ZeroData.gamma_reflection (Z : ZeroData) (n : ℕ) :
    Z.gamma (Z.reflection n) = -Z.gamma n := by
  rw [ZeroData.gamma, Z.zero_reflection]
  exact spectralParameter_reflection (Z.zero n)

/-- Conjugation pairs `gamma` with `-conj gamma`. -/
@[simp]
theorem ZeroData.gamma_conjugation (Z : ZeroData) (n : ℕ) :
    Z.gamma (Z.conjugation n) = -conj (Z.gamma n) := by
  rw [ZeroData.gamma, Z.zero_conjugation]
  exact spectralParameter_conjugation (Z.zero n)

/-- Reflection is involutive on the duplicate-free zero enumeration. -/
@[simp]
theorem ZeroData.reflection_reflection (Z : ZeroData) (n : ℕ) :
    Z.reflection (Z.reflection n) = n := by
  apply Z.zero_injective
  rw [Z.zero_reflection, Z.zero_reflection]
  ring

/-- Conjugation is involutive on the duplicate-free zero enumeration. -/
@[simp]
theorem ZeroData.conjugation_conjugation (Z : ZeroData) (n : ℕ) :
    Z.conjugation (Z.conjugation n) = n := by
  apply Z.zero_injective
  rw [Z.zero_conjugation, Z.zero_conjugation]
  simp

/-- The finite index set in the explicit symmetric cutoff `|gamma| ≤ T`. -/
noncomputable def ZeroData.symmetricIndices (Z : ZeroData) (T : ℝ) : Finset ℕ :=
  (Z.locallyFinite T).toFinset

/-- Membership in a symmetric cutoff is exactly the stated spectral norm bound. -/
@[simp]
theorem ZeroData.mem_symmetricIndices (Z : ZeroData) {T : ℝ} {n : ℕ} :
    n ∈ Z.symmetricIndices T ↔ ‖Z.gamma n‖ ≤ T := by
  simp [ZeroData.symmetricIndices, spectralRadius, ZeroData.gamma]

/-- Increasing the cutoff radius only adds zero indices. -/
theorem ZeroData.symmetricIndices_mono (Z : ZeroData) {T U : ℝ} (hTU : T ≤ U) :
    Z.symmetricIndices T ⊆ Z.symmetricIndices U := by
  intro n hn
  rw [Z.mem_symmetricIndices] at hn ⊢
  exact hn.trans hTU

/-- Every cutoff is closed under functional-equation reflection. -/
@[simp]
theorem ZeroData.reflection_mem_symmetricIndices (Z : ZeroData) {T : ℝ} {n : ℕ} :
    Z.reflection n ∈ Z.symmetricIndices T ↔ n ∈ Z.symmetricIndices T := by
  simp only [Z.mem_symmetricIndices, Z.gamma_reflection, norm_neg]

/-- Every cutoff is closed under complex conjugation. -/
@[simp]
theorem ZeroData.conjugation_mem_symmetricIndices (Z : ZeroData) {T : ℝ} {n : ℕ} :
    Z.conjugation n ∈ Z.symmetricIndices T ↔ n ∈ Z.symmetricIndices T := by
  simp only [Z.mem_symmetricIndices, Z.gamma_conjugation, norm_neg, Complex.norm_conj]

/-- Evenness of a Weil test makes its Fourier-Laplace transform even on `ℂ`. -/
theorem fourierLaplace_neg (g : WeilTestFunction) (z : ℂ) :
    fourierLaplace g (-z) = fourierLaplace g z := by
  unfold fourierLaplace
  rw [← integral_neg_eq_self
    (fun x : ℝ => fourierKernel (-z) x * g x) volume]
  apply integral_congr_ae
  filter_upwards with x
  rw [g.even]
  congr 1
  simp only [fourierKernel]
  congr 1
  push_cast
  ring

/-- The contribution of one distinct zero, with its analytic multiplicity. -/
noncomputable def zeroSummand (Z : ZeroData) (g : WeilTestFunction) (n : ℕ) : ℂ :=
  (Z.multiplicity n : ℂ) * fourierLaplace g (Z.gamma n)

/-- Reflected zeros have equal multiplicity-weighted contributions for even tests. -/
@[simp]
theorem zeroSummand_reflection (Z : ZeroData) (g : WeilTestFunction) (n : ℕ) :
    zeroSummand Z g (Z.reflection n) = zeroSummand Z g n := by
  simp [zeroSummand, Z.multiplicity_reflection, fourierLaplace_neg]

/-- The finite multiplicity-aware zero sum at symmetric radius `T`. -/
noncomputable def truncatedZeroSum (Z : ZeroData) (g : WeilTestFunction) (T : ℝ) : ℂ :=
  ∑ n ∈ Z.symmetricIndices T, zeroSummand Z g n

/-- The exact convergence obligation for the symmetric zero sum. -/
def SymmetricConvergent (Z : ZeroData) (g : WeilTestFunction) : Prop :=
  ∃ z : ℂ, Tendsto (fun T : ℝ => truncatedZeroSum Z g T) atTop (nhds z)

/-- The multiplicity-aware nontrivial-zero sum, gated by symmetric convergence. -/
noncomputable def zeroSum (Z : ZeroData) (g : WeilTestFunction)
    (h : SymmetricConvergent Z g) : ℂ :=
  h.choose

/-- The symmetric finite cutoffs converge to `zeroSum`. -/
theorem truncatedZeroSum_tendsto (Z : ZeroData) (g : WeilTestFunction)
    (h : SymmetricConvergent Z g) :
    Tendsto (fun T : ℝ => truncatedZeroSum Z g T) atTop (nhds (zeroSum Z g h)) :=
  h.choose_spec

/-- Any claimed symmetric limit is the defined zero sum. -/
theorem zeroSum_eq_of_tendsto (Z : ZeroData) (g : WeilTestFunction)
    (h : SymmetricConvergent Z g) {z : ℂ}
    (hz : Tendsto (fun T : ℝ => truncatedZeroSum Z g T) atTop (nhds z)) :
    zeroSum Z g h = z :=
  tendsto_nhds_unique (truncatedZeroSum_tendsto Z g h) hz

/-- The value of `zeroSum` is independent of the convergence witness. -/
theorem zeroSum_proof_irrel (Z : ZeroData) (g : WeilTestFunction)
    (h₁ h₂ : SymmetricConvergent Z g) :
    zeroSum Z g h₁ = zeroSum Z g h₂ :=
  zeroSum_eq_of_tendsto Z g h₁ (truncatedZeroSum_tendsto Z g h₂)

end D5.S3.Weil.ZeroSum
