/- GID: D5/S3/Quantum/Decoherence/ProductRecordBandwidth
   generality: G
   mirror-B: D5/B/S3/Quantum/Decoherence/ProductRecordBandwidth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact product-record bandwidth and its separation from bounded conditional entropy. -/

import D5.S3.Quantum.Decoherence.GibbsBathBandwidth
import D5.S3.Entropy.NamingWindow.GreenClassWindowEntropy
import D5.S3.Entropy.EntropyEquality
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import D5.S3.Quantum.Information.StrongSubadditivity
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Heterogeneous binary product records

The effective memory is in the product eigenbasis. Its full density matrix is
diagonal with the independent binary spectral laws as factors.
-/

set_option autoImplicit false

namespace GibbsBathBandwidth

open Matrix Filter
open scoped Matrix Topology ComplexOrder
open D5.S3.Entropy.MaxEntropy (shannonEntropy)
open D5.S3.Entropy.NamingWindow.GreenClassWindowEntropy
  (windowLaw windowLaw_sum_eq_one shannonEntropy_windowLaw)

noncomputable section

abbrev Word (k : ℕ) := Fin k → Bool

def bitSpectrum (s : ℝ) (x : Bool) : ℝ :=
  if x then (1 - s) / 2 else (1 + s) / 2

def productSpectrum {k : ℕ} (s : Fin k → ℝ) : Word k → ℝ :=
  windowLaw (fun i => bitSpectrum (s i))

def productMemory {k : ℕ} (s : Fin k → ℝ) : Matrix (Word k) (Word k) ℂ :=
  diagonalReal (productSpectrum s)

private theorem sum_bool (f : Bool → ℝ) : ∑ x, f x = f false + f true := by
  rw [Fintype.sum_bool, add_comm]

private theorem bitSpectrum_sum (s : ℝ) : ∑ x, bitSpectrum s x = 1 := by
  rw [sum_bool]
  simp only [bitSpectrum, Bool.false_eq_true, ite_false, ite_true]
  ring

private theorem bitSpectrum_pos {s : ℝ} (h₀ : 0 ≤ s) (h₁ : s < 1) (x : Bool) :
    0 < bitSpectrum s x := by
  cases x <;> simp [bitSpectrum] <;> linarith

theorem productSpectrum_sum {k : ℕ} (s : Fin k → ℝ) : ∑ x, productSpectrum s x = 1 :=
  windowLaw_sum_eq_one _ (fun i => bitSpectrum_sum (s i))

private theorem productSpectrum_pos {k : ℕ} {s : Fin k → ℝ}
    (h₀ : ∀ i, 0 ≤ s i) (h₁ : ∀ i, s i < 1) (x : Word k) :
    0 < productSpectrum s x := by
  unfold productSpectrum windowLaw
  exact Finset.prod_pos (fun i _ => bitSpectrum_pos (h₀ i) (h₁ i) (x i))

theorem productMemory_posDef {k : ℕ} {s : Fin k → ℝ}
    (h₀ : ∀ i, 0 ≤ s i) (h₁ : ∀ i, s i < 1) : (productMemory s).PosDef :=
  diagonalReal_posDef _ (productSpectrum_pos h₀ h₁)

theorem productMemory_trace {k : ℕ} (s : Fin k → ℝ) : (productMemory s).trace = 1 := by
  rw [productMemory, diagonalReal, trace_diagonal, ← Complex.ofReal_sum,
    productSpectrum_sum, Complex.ofReal_one]

private theorem productSpectrum_extrema {k : ℕ} {s : Fin k → ℝ}
    (h₀ : ∀ i, 0 ≤ s i) (h₁ : ∀ i, s i < 1) :
    minValue (productSpectrum s) = ∏ i, (1 - s i) / 2 ∧
    maxValue (productSpectrum s) = ∏ i, (1 + s i) / 2 := by
  have hlo (i : Fin k) (x : Bool) : bitSpectrum (s i) true ≤ bitSpectrum (s i) x := by
    cases x <;> simp [bitSpectrum]
    linarith [h₀ i]
  have hhi (i : Fin k) (x : Bool) : bitSpectrum (s i) x ≤ bitSpectrum (s i) false := by
    cases x <;> simp [bitSpectrum]
    linarith [h₀ i]
  have h (i : Fin k) (x : Bool) := (bitSpectrum_pos (h₀ i) (h₁ i) x).le
  have hmin (x : Word k) : productSpectrum s (fun _ => true) ≤ productSpectrum s x := by
    unfold productSpectrum windowLaw
    exact Finset.prod_le_prod₀ (fun i _ => h i true) (fun i _ => hlo i (x i))
  have hmax (x : Word k) : productSpectrum s x ≤ productSpectrum s (fun _ => false) := by
    unfold productSpectrum windowLaw
    exact Finset.prod_le_prod₀ (fun i _ => h i (x i)) (fun i _ => hhi i (x i))
  exact ⟨minValue_eq _ hmin, maxValue_eq _ hmax⟩

/-- The dimensionless minimum for the independent binary records. -/
def productWidth {k : ℕ} (s : Fin k → ℝ) : ℝ :=
  ∑ i, Real.log ((1 + s i) / (1 - s i))

theorem product_requiredWidth {k : ℕ} {s : Fin k → ℝ}
    (h₀ : ∀ i, 0 ≤ s i) (h₁ : ∀ i, s i < 1) (β : ℝ) :
    requiredWidth β (productMemory_posDef h₀ h₁) = β⁻¹ * productWidth s := by
  have he := diagonalReal_endpoints (productSpectrum s)
    (productMemory_posDef h₀ h₁).isHermitian
  have hp := productSpectrum_extrema h₀ h₁
  unfold requiredWidth productWidth
  change β⁻¹ * Real.log (maxValue (productMemory_posDef h₀ h₁).isHermitian.eigenvalues /
    minValue (productMemory_posDef h₀ h₁).isHermitian.eigenvalues) = _
  have hlo : minValue (productMemory_posDef h₀ h₁).isHermitian.eigenvalues =
      minValue (productSpectrum s) := he.1
  have hhi : maxValue (productMemory_posDef h₀ h₁).isHermitian.eigenvalues =
      maxValue (productSpectrum s) := he.2
  rw [hlo, hhi, hp.1, hp.2, ← Finset.prod_div_distrib]
  congr 1
  rw [Real.log_prod (fun i _ => by
    apply div_ne_zero <;> linarith [h₀ i, h₁ i])]
  apply Finset.sum_congr rfl
  intro i _
  rw [div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0)]

theorem product_bandwidth_lower_bound {B : Type*} [Fintype B] [DecidableEq B] [Nonempty B]
    {k : ℕ} {s : Fin k → ℝ} (h₀ : ∀ i, 0 ≤ s i) (h₁ : ∀ i, s i < 1)
    {β : ℝ} (hβ : 0 < β) (E : B → ℝ) (V : unitary (Matrix B B ℂ))
    (U : unitary (Matrix (B × Word k) (B × Word k) ℂ))
    (hU : Retains (gibbsBath β E V) (productMemory s) U) :
    β⁻¹ * productWidth s ≤ energyWidth E ∧ ∏ i, (1 + s i) ≤ (Fintype.card B : ℝ) := by
  have h := bandwidth_lower_bound hβ E V (productMemory_posDef h₀ h₁) U hU
  rw [product_requiredWidth h₀ h₁ β] at h
  have he : maxValue (productMemory_posDef h₀ h₁).isHermitian.eigenvalues =
      maxValue (productSpectrum s) := (diagonalReal_endpoints (productSpectrum s)
    (productMemory_posDef h₀ h₁).isHermitian).2
  have hcard : (Fintype.card (Word k) : ℝ) = ∏ _ : Fin k, (2 : ℝ) := by
    simp [Word]
  rw [he, (productSpectrum_extrema h₀ h₁).2, hcard, ← Finset.prod_mul_distrib] at h
  have heq (i : Fin k) : 2 * ((1 + s i) / 2) = 1 + s i := by ring
  simpa only [heq] using h

theorem product_bandwidth_attained {k : ℕ} {s : Fin k → ℝ}
    (h₀ : ∀ i, 0 ≤ s i) (h₁ : ∀ i, s i < 1) {β : ℝ} (hβ : 0 < β) :
    ∃ (E : Word k → ℝ) (V : unitary (Matrix (Word k) (Word k) ℂ)),
      energyWidth E = β⁻¹ * productWidth s ∧
        Retains (gibbsBath β E V) (productMemory s) tensorSwap := by
  have h := bandwidth_attained hβ (productMemory_posDef h₀ h₁) (productMemory_trace s)
  refine ⟨_, _, h.1.trans (product_requiredWidth h₀ h₁ β), h.2.2⟩

/-- Entropy of the uniform pure-record label ensemble less the spectral entropy
of its average memory. -/
def productConditionalEntropy {k : ℕ} (s : Fin k → ℝ) : ℝ :=
  Real.log (Fintype.card (Word k)) - shannonEntropy (productSpectrum s)

private theorem shannonEntropy_bitSpectrum (s : ℝ) :
    shannonEntropy (bitSpectrum s) = Real.binEntropy ((1 + s) / 2) := by
  rw [shannonEntropy, sum_bool, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [bitSpectrum, Bool.false_eq_true, ite_false, ite_true]
  rw [show (1 - s) / 2 = 1 - (1 + s) / 2 by ring]

theorem productConditionalEntropy_eq_sum {k : ℕ} (s : Fin k → ℝ) :
    productConditionalEntropy s = ∑ i, (Real.log 2 - Real.binEntropy ((1 + s i) / 2)) := by
  rw [productConditionalEntropy, productSpectrum, shannonEntropy_windowLaw _ (fun i =>
    bitSpectrum_sum (s i)), Finset.sum_sub_distrib]
  simp [shannonEntropy_bitSpectrum, Word, Real.log_pow, nsmul_eq_mul]

private theorem entropy_deficit_le_sq {s : ℝ} (h₀ : 0 ≤ s) (h₁ : s < 1) :
    Real.log 2 - Real.binEntropy ((1 + s) / 2) ≤ s ^ 2 := by
  have hp : 0 < 1 + s := by linarith
  have hm : 0 < 1 - s := by linarith
  have hp' := Real.log_le_sub_one_of_pos hp
  have hm' := Real.log_le_sub_one_of_pos hm
  have hplus := mul_le_mul_of_nonneg_left hp' (show 0 ≤ (1 + s) / 2 by positivity)
  have hminus := mul_le_mul_of_nonneg_left hm' (show 0 ≤ (1 - s) / 2 by positivity)
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog, Real.negMulLog,
    show 1 - (1 + s) / 2 = (1 - s) / 2 by ring,
    Real.log_div hp.ne' (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_div hm.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  linarith only [hplus, hminus]

theorem productConditionalEntropy_bounds {k : ℕ} {s : Fin k → ℝ}
    (h₀ : ∀ i, 0 ≤ s i) (h₁ : ∀ i, s i < 1) :
    0 ≤ productConditionalEntropy s ∧ productConditionalEntropy s ≤ ∑ i, s i ^ 2 := by
  rw [productConditionalEntropy_eq_sum]
  exact ⟨Finset.sum_nonneg (fun _ _ => sub_nonneg.mpr Real.binEntropy_le_log_two),
    Finset.sum_le_sum (fun i _ => entropy_deficit_le_sq (h₀ i) (h₁ i))⟩

private theorem width_lower {s : ℝ} (h₀ : 0 ≤ s) (h₁ : s < 1) :
    2 * s ≤ Real.log ((1 + s) / (1 - s)) := by
  have hn : 0 < 1 - s := by linarith
  have hx : 0 ≤ (2 * s) / (1 - s) := by positivity
  have harg : 1 + 2 * s / (1 - s) = (1 + s) / (1 - s) := by
    field_simp
    ring
  have hval : 2 * (2 * s / (1 - s)) / (2 * s / (1 - s) + 2) = 2 * s := by
    field_simp
    ring
  simpa only [harg, hval] using Real.le_log_one_add_of_nonneg hx

theorem productWidth_lower {k : ℕ} {s : Fin k → ℝ}
    (h₀ : ∀ i, 0 ≤ s i) (h₁ : ∀ i, s i < 1) :
    2 * (∑ i, s i) ≤ productWidth s := by
  rw [Finset.mul_sum, productWidth]
  exact Finset.sum_le_sum (fun i _ => width_lower (h₀ i) (h₁ i))

/-- Small overlaps with a nonzero limiting sum of squares force divergent minimum
bandwidth. Their conditional entropy remains eventually bounded. The function
`δ` can be taken to be the maximum overlap of a row. -/
theorem product_small_overlap {k : ℕ → ℕ} (s : (n : ℕ) → Fin (k n) → ℝ)
    (h₀ : ∀ n i, 0 ≤ s n i) (h₁ : ∀ n i, s n i < 1)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (henv : ∀ n i, s n i ≤ δ n)
    {lam : ℝ} (hlam : 0 < lam)
    (hsq : Tendsto (fun n => ∑ i, s n i ^ 2) atTop (𝓝 lam))
    {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun n => β⁻¹ * productWidth (s n)) atTop atTop ∧
      ∀ᶠ n in atTop, 0 ≤ productConditionalEntropy (s n) ∧
        productConditionalEntropy (s n) ≤ lam + 1 := by
  have hlarge : ∀ᶠ n in atTop, lam / 2 < ∑ i, s n i ^ 2 :=
    hsq.eventually (eventually_gt_nhds (by linarith))
  constructor
  · apply tendsto_atTop.2
    intro L
    let C := max 1 (β * L / 2)
    have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hsmall : ∀ᶠ n in atTop, δ n < (lam / 2) / C :=
      hδ.eventually (eventually_lt_nhds (div_pos (by positivity) hC))
    filter_upwards [hlarge, hsmall] with n hn hd
    have hsums : 0 ≤ ∑ i, s n i := Finset.sum_nonneg (fun i _ => h₀ n i)
    have hsqle : (∑ i, s n i ^ 2) ≤ δ n * (∑ i, s n i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right (henv n i) (h₀ n i))
    have hδpos : 0 < δ n := by
      by_contra! hnon
      exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hnon hsums)) ((by positivity : 0 < lam / 2).trans (hn.trans_le hsqle))
    have hsum : C ≤ ∑ i, s n i := by
      by_contra! hh
      have hbound := (lt_div_iff₀ hC).1 hd
      exact (not_lt_of_ge ((mul_le_mul_of_nonneg_left hh.le hδpos.le).trans hbound.le))
        (hn.trans_le hsqle)
    have hW := productWidth_lower (h₀ n) (h₁ n)
    have hL : β * L / 2 ≤ C := le_max_right _ _
    rw [← div_eq_inv_mul, le_div_iff₀ hβ]
    linarith
  · have hsmall : ∀ᶠ n in atTop, (∑ i, s n i ^ 2) < lam + 1 :=
      hsq.eventually (eventually_lt_nhds (by linarith))
    filter_upwards [hsmall] with n hn
    have h := productConditionalEntropy_bounds (h₀ n) (h₁ n)
    exact ⟨h.1, h.2.trans hn.le⟩

private theorem productWidth_upper {k : ℕ} {s : Fin k → ℝ} {δ : ℝ}
    (h₀ : ∀ i, 0 ≤ s i) (henv : ∀ i, s i ≤ δ) (hδ : δ < 1) :
    productWidth s ≤ 2 * (∑ i, s i) / (1 - δ) := by
  rw [productWidth, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  have hp : 0 < 1 + s i := by linarith [h₀ i]
  have hm : 0 < 1 - s i := by linarith [henv i]
  calc
    Real.log ((1 + s i) / (1 - s i)) ≤ (1 + s i) / (1 - s i) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hp hm)
    _ = 2 * s i / (1 - s i) := by
      field_simp
      ring
    _ ≤ 2 * s i / (1 - δ) :=
      div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (h₀ i))
        (by linarith) (by linarith [henv i])

/-- The divergent dimensionless minimum is asymptotic to twice the sum of overlaps. -/
theorem product_width_asymptotic {k : ℕ → ℕ} (s : (n : ℕ) → Fin (k n) → ℝ)
    (h₀ : ∀ n i, 0 ≤ s n i) (h₁ : ∀ n i, s n i < 1)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (henv : ∀ n i, s n i ≤ δ n)
    {lam : ℝ} (hlam : 0 < lam)
    (hsq : Tendsto (fun n => ∑ i, s n i ^ 2) atTop (𝓝 lam)) :
    Tendsto (fun n => productWidth (s n) / (2 * ∑ i, s n i)) atTop (𝓝 1) := by
  have hsqpos : ∀ᶠ n in atTop, 0 < ∑ i, s n i ^ 2 :=
    hsq.eventually (eventually_gt_nhds hlam)
  have hsum : ∀ᶠ n in atTop, 0 < 2 * ∑ i, s n i := by
    filter_upwards [hsqpos] with n hn
    have hle : (∑ i, s n i ^ 2) ≤ ∑ i, s n i := by
      refine Finset.sum_le_sum fun i _ => ?_
      simpa only [pow_two, one_mul] using mul_le_mul_of_nonneg_right (h₁ n i).le (h₀ n i)
    linarith
  have hδlt : ∀ᶠ n in atTop, δ n < 1 := hδ.eventually (eventually_lt_nhds zero_lt_one)
  have hinv : Tendsto (fun n => (1 - δ n)⁻¹) atTop (𝓝 1) := by
    have hsub : Tendsto (fun n => 1 - δ n) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hδ
    simpa using hsub.inv₀ one_ne_zero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv ?_ ?_
  · filter_upwards [hsum] with n hn
    exact (le_div_iff₀ hn).2 (by simpa using productWidth_lower (h₀ n) (h₁ n))
  · filter_upwards [hsum, hδlt] with n hn hd
    apply (div_le_iff₀ hn).2
    simpa only [div_eq_inv_mul] using productWidth_upper (h₀ n) (henv n) hd

section PureRecords

set_option backward.isDefEq.respectTransparency false

open scoped CStarAlgebra MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Entropy.EntropyEquality (entropy_eq_log_card_iff_uniform)
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition (DensityState)
open D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity (cfc_diagonal)
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Foundation.FiniteDensityPurification (toDensity)
open D5.S3.Quantum.Information
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.OrthogonalRecordEntropy
open D5.S3.Quantum.Information.StrongSubadditivity (entropy_toMState toMState_toDensity)

/-- The two records differ by the sign of their second amplitude. -/
def bitAmplitude (s : ℝ) (label coordinate : Bool) : ℝ :=
  if label && coordinate then -Real.sqrt (bitSpectrum s coordinate)
  else Real.sqrt (bitSpectrum s coordinate)

private theorem bitAmplitude_sq {s : ℝ} (h₀ : 0 ≤ s) (h₁ : s < 1) (j x : Bool) :
    bitAmplitude s j x ^ 2 = bitSpectrum s x := by
  unfold bitAmplitude
  split <;> simp [Real.sq_sqrt (bitSpectrum_pos h₀ h₁ x).le]

/-- The inner product between the two normalized binary amplitudes is the given overlap. -/
theorem bitAmplitude_overlap {s : ℝ} (h₀ : 0 ≤ s) (h₁ : s < 1) :
    ∑ x, bitAmplitude s false x * bitAmplitude s true x = s := by
  rw [sum_bool]
  simp only [bitAmplitude, Bool.false_and, Bool.true_and, Bool.false_eq_true, ite_false,
    ite_true, mul_neg, ← pow_two]
  rw [Real.sq_sqrt (bitSpectrum_pos h₀ h₁ false).le,
    Real.sq_sqrt (bitSpectrum_pos h₀ h₁ true).le]
  simp [bitSpectrum]
  ring

def productAmplitude {k : ℕ} (s : Fin k → ℝ) (label coordinate : Word k) : ℝ :=
  ∏ i, bitAmplitude (s i) (label i) (coordinate i)

private theorem productAmplitude_sq {k : ℕ} {s : Fin k → ℝ}
    (h₀ : ∀ i, 0 ≤ s i) (h₁ : ∀ i, s i < 1) (j x : Word k) :
    productAmplitude s j x ^ 2 = productSpectrum s x := by
  rw [productAmplitude, ← Finset.prod_pow]
  exact Finset.prod_congr rfl (fun i _ => bitAmplitude_sq (h₀ i) (h₁ i) _ _)

def productRecordKet {k : ℕ} (s : Fin k → ℝ)
    (h₀ : ∀ i, 0 ≤ s i) (h₁ : ∀ i, s i < 1) (j : Word k) : Ket (Word k) :=
  ⟨fun x => (productAmplitude s j x : ℂ), by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, ← pow_two, productAmplitude_sq h₀ h₁,
      productSpectrum_sum]⟩

private def uniformWord {k : ℕ} (_ : Word k) : ℝ :=
  (Fintype.card (Word k) : ℝ)⁻¹

private theorem uniformWord_nonneg {k : ℕ} (x : Word k) : 0 ≤ uniformWord x := by
  unfold uniformWord
  positivity

private theorem uniformWord_sum (k : ℕ) : ∑ x : Word k, uniformWord x = 1 := by
  simp [uniformWord]

/-- The uniform cq state of the pure product amplitudes. -/
def productCQ {k : ℕ} (s : Fin k → ℝ) (h₀ : ∀ i, 0 ≤ s i) (h₁ : ∀ i, s i < 1) :
    DensityState (Word k × Word k) :=
  recordState uniformWord uniformWord_nonneg (uniformWord_sum k)
    (fun j => toDensity (MState.pure (productRecordKet s h₀ h₁ j)))

private theorem bitAmplitude_cross {s : ℝ} (h₀ : 0 ≤ s) (h₁ : s < 1) (x y : Bool) :
    (∑ j, bitAmplitude s j x * bitAmplitude s j y) =
      if x = y then 2 * bitSpectrum s x else 0 := by
  rw [sum_bool]
  cases x <;> cases y <;>
    simp only [bitAmplitude, Bool.false_and, Bool.true_and, Bool.false_eq_true,
      Bool.true_eq_false, ite_false, ite_true, mul_neg, neg_mul, ← pow_two] <;>
    simp [Real.sq_sqrt (bitSpectrum_pos h₀ h₁ false).le,
      Real.sq_sqrt (bitSpectrum_pos h₀ h₁ true).le] <;> ring

private theorem productAmplitude_cross {k : ℕ} {s : Fin k → ℝ}
    (h₀ : ∀ i, 0 ≤ s i) (h₁ : ∀ i, s i < 1) (x y : Word k) :
    (∑ j, productAmplitude s j x * productAmplitude s j y) =
      if x = y then (Fintype.card (Word k) : ℝ) * productSpectrum s x else 0 := by
  simp only [productAmplitude, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i j => bitAmplitude (s i) j (x i) * bitAmplitude (s i) j (y i))]
  simp only [bitAmplitude_cross (h₀ _) (h₁ _)]
  by_cases hxy : x = y
  · subst y
    rw [ite_eq_left rfl]
    simp [productSpectrum, windowLaw, Finset.prod_mul_distrib, Word]
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra! h
      exact hxy (funext h)
    rw [ite_eq_right hxy]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

theorem productCQ_memory {k : ℕ} (s : Fin k → ℝ)
    (h₀ : ∀ i, 0 ≤ s i) (h₁ : ∀ i, s i < 1) :
    CStarMatrix.ofMatrix.symm (marginalLeft (productCQ s h₀ h₁)).1 = productMemory s := by
  unfold productCQ recordState
  rw [marginalLeft_mixture]
  simp only [marginalLeft_productState]
  ext x y
  let p := productSpectrum s
  change (∑ j : Word k, uniformWord j • Matrix.vecMulVec
      (fun u => (productAmplitude s j u : ℂ))
      (((productRecordKet s h₀ h₁ j : Ket (Word k)) : Bra (Word k)) : Word k → ℂ)) x y =
    diagonalReal p x y
  have hentry (j : Word k) :
      (((productRecordKet s h₀ h₁ j : Ket (Word k)) : Bra (Word k)) : Word k → ℂ) y =
        (productAmplitude s j y : ℂ) := by
    rw [Bra.eq_conj]
    exact Complex.conj_ofReal _
  simp only [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul, Matrix.vecMulVec_apply,
    hentry, uniformWord, ← Complex.ofReal_mul, ← Complex.ofReal_sum,
    ← Finset.mul_sum]
  rw [productAmplitude_cross h₀ h₁]
  by_cases hxy : x = y
  · simp [hxy, diagonalReal, p]
  · simp [hxy, diagonalReal]

private theorem densityEntropy_diagonal {M : Type*} [Fintype M] [DecidableEq M]
    (ρ : DensityState M) (p : M → ℝ) (hp : CStarMatrix.ofMatrix.symm ρ.1 = diagonalReal p) :
    vonNeumannEntropy ρ = shannonEntropy p := by
  have hmap : CStarMatrix.ofMatrix (cfc Real.negMulLog (diagonalReal p)) =
      cfc Real.negMulLog ρ.1 := by
    have hHerm := (density_posSemidef ρ).isHermitian
    rw [← hp]
    exact StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv Real.negMulLog _
      (Matrix.finite_real_spectrum.continuousOn _) CStarMatrix.ofMatrixL.continuous hHerm
      (by exact hHerm)
  rw [entropy_eq_trace_cfc, ← hmap, realTrace]
  change (Matrix.trace (cfc Real.negMulLog (diagonalReal p))).re = shannonEntropy p
  rw [diagonalReal, cfc_diagonal, trace_diagonal, Complex.re_sum, shannonEntropy]
  simp only [Complex.ofReal_re]

/-- The scalar entropy deficit is the conditional von Neumann entropy of the
same cq product state whose memory appears in the bandwidth theorem. -/
theorem productCQ_conditionalEntropy {k : ℕ} (s : Fin k → ℝ)
    (h₀ : ∀ i, 0 ≤ s i) (h₁ : ∀ i, s i < 1) :
    vonNeumannEntropy (productCQ s h₀ h₁) -
      vonNeumannEntropy (marginalLeft (productCQ s h₀ h₁)) = productConditionalEntropy s := by
  rw [densityEntropy_diagonal _ (productSpectrum s) (productCQ_memory s h₀ h₁)]
  have hprior : shannonEntropy (uniformWord (k := k)) = Real.log (Fintype.card (Word k)) :=
    (entropy_eq_log_card_iff_uniform uniformWord ⟨uniformWord_nonneg, uniformWord_sum k⟩).2 rfl
  have hpure (j : Word k) : vonNeumannEntropy (toDensity (MState.pure
      (productRecordKet s h₀ h₁ j))) = 0 := by
    rw [← entropy_toMState, toMState_toDensity, Sᵥₙ_of_pure_zero]
  unfold productCQ productConditionalEntropy
  rw [entropy_recordState]
  simp only [hpure, mul_zero, Finset.sum_const_zero, add_zero, hprior]

/-- The actual cq conditional entropy stays bounded in the regime where the
exact required bandwidth diverges. -/
theorem productCQ_small_overlap {k : ℕ → ℕ} (s : (n : ℕ) → Fin (k n) → ℝ)
    (h₀ : ∀ n i, 0 ≤ s n i) (h₁ : ∀ n i, s n i < 1)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (henv : ∀ n i, s n i ≤ δ n)
    {lam : ℝ} (hlam : 0 < lam)
    (hsq : Tendsto (fun n => ∑ i, s n i ^ 2) atTop (𝓝 lam))
    {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun n => requiredWidth β (productMemory_posDef (h₀ n) (h₁ n))) atTop atTop ∧
      ∀ᶠ n in atTop,
        let cq := productCQ (s n) (h₀ n) (h₁ n)
        let H := vonNeumannEntropy cq - vonNeumannEntropy (marginalLeft cq)
        0 ≤ H ∧ H ≤ lam + 1 := by
  have hw : (fun n => requiredWidth β (productMemory_posDef (h₀ n) (h₁ n))) =
      fun n => β⁻¹ * productWidth (s n) :=
    funext (fun n => product_requiredWidth (h₀ n) (h₁ n) β)
  rw [hw]
  simp only [productCQ_conditionalEntropy]
  exact product_small_overlap s h₀ h₁ δ hδ henv hlam hsq hβ

end PureRecords

end

end GibbsBathBandwidth
