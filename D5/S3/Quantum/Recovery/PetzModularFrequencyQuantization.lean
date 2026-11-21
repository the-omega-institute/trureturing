/- GID: D5/S3/Quantum/Recovery/PetzModularFrequencyQuantization
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PetzModularFrequencyQuantization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quantizing the retained modular frequencies controls the physical ordinary Petz error. -/

import D5.S3.Quantum.Recovery.PetzSupportedLogisticBound
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Retained modular frequency quantization

The spectral-pair masses are the positive-spectrum Nussbaum–Szkoła masses of
the actual retained states. Only the phases of the retained spectral
coefficients are changed. The ordinary Petz endpoint is common to every
assignment, including when either retained state is singular.
-/

set_option autoImplicit false

noncomputable section

universe u

open Matrix MeasureTheory
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix.Norms.Frobenius
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Divergence.CanonicalChannelDPI
open D5.S3.Quantum.Recovery.PetzSupportedChannelStrip
open D5.S3.Quantum.Recovery.PetzSupportedStinespringGram
open D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability (traceNorm_isometry)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (act)
open PetzExponentialBoundaryEvaluation
open ExponentialGramWeightedEvaluation (exponentialSum frequency)

open private frobenius_sq sum_evaluations traceNorm_gram_sub_le from
  D5.S3.Quantum.Recovery.PetzExponentialBoundaryEvaluation
open private columns columns_apply columns_isometry supportedFunction supportedFunction_id
  mode outputProduct outputProduct_sum exp_ratio boundary_scalar upper rowFactor rowFactor_gram
  lift lift_mul lift_conjTranspose compression sourceAmplitude sourceAmplitude_unit completed
  physicalFactor complementaryAmplitude dilationColumns phaseMatrix dilationColumns_isometry
  phase_unitary physicalFactor_unitTrace complete_gram Us upperIntegral_le_loss
  sourceBlock frobenius_sq_trace exists_retainedFirst_stinespring from
  D5.S3.Quantum.Recovery.PetzSupportedStinespringGram
open private modularPower_add modularPower_zero from D5.S3.Quantum.Recovery.PetzSupportedChannelStrip
open private integral_petzWeight_mul_cos integrable_petzWeight_mul_cos integrable_petzWeight
  integral_petzWeight from D5.S3.Analytic.PetzStripFiniteSeries
open private mode star_mode_mul norm_mode from D5.S3.Analytic.PetzLogisticEvaluation

namespace D5.S3.Quantum.Recovery.PetzModularFrequencyQuantization

variable {a b : Type u} [Fintype a] [DecidableEq a] [Nonempty a]
  [Fintype b] [DecidableEq b] [Nonempty b]
  {Φ : QuantumChannel a b} {ρ σ : DensityState a}

variable (D : SupportedRelativeModularData Φ ρ σ)

local notation "½" => (((1 / 2 : ℝ) : ℂ))
local notation "phase " t => ((t : ℂ) * Complex.I)

private abbrev scalarPhase := PetzLogisticEvaluation.mode

/-- The retained log likelihood log p minus log q on positive spectral pairs. -/
def retainedLogFrequency (k : D.L × D.K) : ℝ :=
  -Real.log (outputRatio D k)

private def overlap (k : D.L × D.K) : ℂ :=
  star (D.w k.1) ⬝ᵥ D.z k.2

/-- Mass of an eigenvector pair. Coincident frequencies contribute their
sum when this law is evaluated against a function of the frequency. -/
def spectralMass (k : D.L × D.K) : ℝ :=
  D.pk k.2 * ‖overlap D k‖ ^ 2

/-- The Fourier transform of the normalized logistic upper-strip weight. -/
def logisticCorrelation (x : ℝ) : ℝ :=
  if x = 0 then 1 else (x / 2) / Real.sinh (x / 2)

/-- Exact logistic cost of replacing each retained frequency by its assigned centre. -/
def phaseCost (assign : ℝ → ℝ) : ℝ :=
  ∑ k : D.L × D.K, spectralMass D k *
    (2 * (1 - logisticCorrelation (retainedLogFrequency D k - assign (retainedLogFrequency D k))))

/-- The assigned frequencies on atoms of positive mass must lie in the given set. -/
def UsesCentres (assign : ℝ → ℝ) (centres : Finset ℝ) : Prop :=
  ∀ k : D.L × D.K, 0 < spectralMass D k → assign (retainedLogFrequency D k) ∈ centres

private def retainedCoordinates (f : D.L × D.K → ℂ) : Matrix D.L D.K ℂ :=
  Matrix.of fun l k => (Real.sqrt (D.pk k / D.ql l) : ℂ) * f (l, k) * overlap D (l, k)

private def retainedFactor (f : D.L × D.K → ℂ) : Matrix b b ℂ :=
  columns D.hQ.1 * retainedCoordinates D f * (columns D.hT.1)ᴴ

private theorem retainedFactor_sum (f : D.L × D.K → ℂ) :
    retainedFactor D f = ∑ k : D.L × D.K,
      ((Real.sqrt (D.pk k.2 / D.ql k.1) : ℂ) * f k) • mode D k := by
  ext x y
  simp only [retainedFactor, retainedCoordinates, Matrix.mul_apply, Matrix.conjTranspose_apply,
    columns_apply, Fintype.sum_prod_type, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.of_apply, mode, Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_apply,
    Pi.smul_apply, Pi.star_apply, overlap, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem retainedFactor_exact (t : ℝ) :
    retainedFactor D (fun k => scalarPhase (retainedLogFrequency D k) t) =
      outputProduct D (upper t) := by
  rw [retainedFactor_sum, outputProduct_sum]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  have hr : 0 < outputRatio D k := div_pos k.1.2 k.2.2
  have hs := boundary_scalar (inv_pos.mpr hr) t
  rw [Real.log_inv, inv_div] at hs
  calc
    _ = Complex.exp ((-Real.log (outputRatio D k) : ℂ) * upper t) := by
      rw [hs]
      congr 1
      unfold scalarPhase PetzLogisticEvaluation.mode retainedLogFrequency
      congr 1
      push_cast
      ring
    _ = _ := by push_cast; ring_nf

private theorem reference_columns :
    D.Q * columns D.hQ.1 = columns D.hQ.1 * diagonal (fun l : D.L => (D.ql l : ℂ)) := by
  calc
    _ = supportedFunction D.hQ.1 Complex.ofReal * columns D.hQ.1 :=
      congrArg (· * columns D.hQ.1) (supportedFunction_id D.hQ).symm
    _ = _ := by
      simp only [supportedFunction, Matrix.mul_assoc, columns_isometry, Matrix.mul_one]

private theorem retainedFactor_pair (f g : D.L × D.K → ℂ) :
    (D.Q * (retainedFactor D f * (retainedFactor D g)ᴴ)).trace =
      ∑ k : D.L × D.K, (spectralMass D k : ℂ) * f k * star (g k) := by
  let V := columns D.hQ.1
  let U := columns D.hT.1
  let X := retainedCoordinates D f
  let Y := retainedCoordinates D g
  let Λ := diagonal (fun l : D.L => (D.ql l : ℂ))
  have hV : Vᴴ * V = 1 := columns_isometry D.hQ.1
  have hU : Uᴴ * U = 1 := columns_isometry D.hT.1
  have hQ : D.Q * V = V * Λ := reference_columns D
  change (D.Q * ((V * X * Uᴴ) * (V * Y * Uᴴ)ᴴ)).trace = _
  have heq : D.Q * ((V * X * Uᴴ) * (V * Y * Uᴴ)ᴴ) = V * (Λ * X * Yᴴ) * Vᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U _, hU, Matrix.one_mul, ← Matrix.mul_assoc D.Q V _, hQ]
    simp only [Matrix.mul_assoc]
  rw [heq, Matrix.trace_mul_comm (V * (Λ * X * Yᴴ)) Vᴴ, ← Matrix.mul_assoc, hV,
    Matrix.one_mul, Matrix.trace, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro l _
  simp only [Matrix.diag, Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Finset.mul_sum,
    retainedCoordinates, X, Y, Λ, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro k _
  have hroot : (Real.sqrt (D.pk k / D.ql l) : ℂ) ^ 2 = (D.pk k : ℂ) / (D.ql l : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (div_nonneg k.2.le l.2.le), Complex.ofReal_div]
  have hq : (D.ql l : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr l.2.ne'
  have hs : (D.ql l : ℂ) * (Real.sqrt (D.pk k / D.ql l) : ℂ) ^ 2 = (D.pk k : ℂ) := by
    rw [hroot, mul_div_cancel₀ _ hq]
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal, spectralMass, Complex.ofReal_mul,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  calc
    _ = ((D.ql l : ℂ) * (Real.sqrt (D.pk k / D.ql l) : ℂ) ^ 2) *
        (star (overlap D (l, k)) * overlap D (l, k)) * f (l, k) * star (g (l, k)) := by
      simp only [Complex.star_def]
      ring
    _ = _ := by rw [hs]; simp only [Complex.star_def]; ring

variable {e : Type u} [Fintype e] [DecidableEq e]

private def completionColumns (W : Matrix (b × e) a ℂ) (t : ℝ) :
    Matrix (b × e) (D.I ⊕ (b × e)) ℂ :=
  fromCols (dilationColumns D W * phaseMatrix D t)
    (1 - dilationColumns D W * (dilationColumns D W)ᴴ)

private theorem completionColumns_coisometry (W : Matrix (b × e) a ℂ) (hW : Wᴴ * W = 1)
    (t : ℝ) : completionColumns D W t * (completionColumns D W t)ᴴ = 1 := by
  let V := dilationColumns D W
  let U := phaseMatrix D t
  let P := V * Vᴴ
  have hV : Vᴴ * V = 1 := dilationColumns_isometry D W hW
  have hU : U * Uᴴ = 1 := phase_unitary D t
  have hP : P * P = P := by
    dsimp only [P]
    rw [Matrix.mul_assoc V Vᴴ (V * Vᴴ), ← Matrix.mul_assoc Vᴴ V Vᴴ, hV, Matrix.one_mul]
  have hPs : Pᴴ = P := by simp [P, Matrix.conjTranspose_mul]
  have hleft : (V * U) * (V * U)ᴴ = P := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U Uᴴ Vᴴ,
      hU, Matrix.one_mul, P]
  have hright : (1 - P) * (1 - P)ᴴ = 1 - P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPs, Matrix.mul_sub,
      Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hP, sub_self, sub_zero]
  change fromCols (V * U) (1 - P) * (fromCols (V * U) (1 - P))ᴴ = 1
  rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromCols_mul_fromRows, hleft, hright]
  abel

private def completedWithCoefficients (W : Matrix (b × e) a ℂ) (t : ℝ)
    (f : D.L × D.K → ℂ) : Matrix D.J (D.I ⊕ (b × e)) ℂ :=
  rowFactor D (upper t) * Wᴴ * lift (retainedFactor D f) * completionColumns D W t

/-- Completed physical amplitude with the assigned phases on the retained
pairs and the original outer phases and Stinespring columns. -/
def quantizedCompleted (W : Matrix (b × e) a ℂ) (assign : ℝ → ℝ) (t : ℝ) :
    Matrix D.J (D.I ⊕ (b × e)) ℂ :=
  completedWithCoefficients D W t (fun k => scalarPhase (assign (retainedLogFrequency D k)) t)

private theorem completedWithCoefficients_exact (W : Matrix (b × e) a ℂ) (t : ℝ) :
    completedWithCoefficients D W t (fun k => scalarPhase (retainedLogFrequency D k) t) =
      completed D W t := by
  rw [completedWithCoefficients, retainedFactor_exact]
  change physicalFactor D W t * completionColumns D W t = _
  rw [completionColumns, Matrix.mul_fromCols, completed, complementaryAmplitude, Matrix.mul_assoc]

private theorem common_endpoint (W : Matrix (b × e) a ℂ) (assign : ℝ → ℝ) :
    quantizedCompleted D W assign 0 = completed D W 0 := by
  rw [← completedWithCoefficients_exact D W 0, quantizedCompleted]
  congr 1
  funext k
  simp [scalarPhase, PetzLogisticEvaluation.mode]

private theorem completion_pair (M : SupportedRelativeModularModel Φ ρ σ)
    (W : Matrix (b × e) a ℂ) (hW : Wᴴ * W = 1)
    (hAction : ∀ X : Matrix a a ℂ, partialTraceRight (W * X * Wᴴ) = act Φ X)
    (t : ℝ) (X Y : Matrix b b ℂ) :
    let F := rowFactor M.data (upper t) * Wᴴ
    let C := completionColumns M.data W t
    ((F * lift X * C) * (F * lift Y * C)ᴴ).trace =
      (M.data.Q * (X * Yᴴ)).trace := by
  dsimp only
  let F := rowFactor M.data (upper t)
  let C := completionColumns M.data W t
  have hC : C * Cᴴ = 1 := completionColumns_coisometry M.data W hW t
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc C Cᴴ _, hC, Matrix.one_mul,
    ← Matrix.mul_assoc (lift X) (lift Y)ᴴ _, lift_conjTranspose, lift_mul]
  have hcompress : Wᴴ * (lift (e := e) (X * Yᴴ) * W) = M.data.Ψ (X * Yᴴ) := by
    rw [← Matrix.mul_assoc, compression W M hAction]
  rw [← Matrix.mul_assoc (lift (e := e) (X * Yᴴ)) W Fᴴ,
    ← Matrix.mul_assoc Wᴴ _ Fᴴ, hcompress,
    ← Matrix.mul_assoc F _ Fᴴ, Matrix.trace_mul_comm (F * M.data.Ψ (X * Yᴴ)) Fᴴ,
    ← Matrix.mul_assoc, rowFactor_gram, M.tracePair]
  rfl

private theorem completedWithCoefficients_pair (M : SupportedRelativeModularModel Φ ρ σ)
    (W : Matrix (b × e) a ℂ) (hW : Wᴴ * W = 1)
    (hAction : ∀ X : Matrix a a ℂ, partialTraceRight (W * X * Wᴴ) = act Φ X)
    (t : ℝ) (f g : M.data.L × M.data.K → ℂ) :
    (completedWithCoefficients M.data W t f *
      (completedWithCoefficients M.data W t g)ᴴ).trace =
      ∑ k : M.data.L × M.data.K, (spectralMass M.data k : ℂ) * f k * star (g k) := by
  rw [completedWithCoefficients, completedWithCoefficients, completion_pair M W hW hAction,
    retainedFactor_pair]

private theorem completedWithCoefficients_sub (W : Matrix (b × e) a ℂ) (t : ℝ)
    (f g : D.L × D.K → ℂ) :
    completedWithCoefficients D W t (fun k => f k - g k) =
      completedWithCoefficients D W t f - completedWithCoefficients D W t g := by
  have hcoord : retainedCoordinates D (fun k => f k - g k) =
      retainedCoordinates D f - retainedCoordinates D g := by
    ext l k
    simp only [retainedCoordinates, Matrix.of_apply, Matrix.sub_apply, mul_sub, sub_mul]
  have hfactor : retainedFactor D (fun k => f k - g k) = retainedFactor D f - retainedFactor D g := by
    simp only [retainedFactor, hcoord, Matrix.mul_sub, Matrix.sub_mul]
  have hlift (X Y : Matrix b b ℂ) : lift (e := e) (X - Y) = lift X - lift Y := by
    ext i j
    simp only [lift, Matrix.kroneckerMap_apply, Matrix.sub_apply, sub_mul]
  simp only [completedWithCoefficients, hfactor, hlift, Matrix.mul_sub, Matrix.sub_mul]

private theorem phase_sub_sq (x y t : ℝ) :
    ‖scalarPhase x t - scalarPhase y t‖ ^ 2 = 2 * (1 - Real.cos ((x - y) * t)) := by
  rw [norm_sub_sq (𝕜 := ℂ)]
  change ‖scalarPhase x t‖ ^ 2 - 2 *
    (star (scalarPhase x t) * scalarPhase y t).re + ‖scalarPhase y t‖ ^ 2 = _
  rw [norm_mode, norm_mode, star_mode_mul]
  have hcos : Real.cos ((y - x) * t) = Real.cos ((x - y) * t) := by
    rw [show (y - x) * t = -((x - y) * t) by ring, Real.cos_neg]
  simp only [one_pow,
    scalarPhase, PetzLogisticEvaluation.mode, Complex.exp_mul_I, Complex.add_re,
    Complex.ofReal_cos, Complex.ofReal_re, Complex.ofReal_sin, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, hcos]
  ring

private theorem phase_discrepancy (M : SupportedRelativeModularModel Φ ρ σ)
    (W : Matrix (b × e) a ℂ) (hW : Wᴴ * W = 1)
    (hAction : ∀ X : Matrix a a ℂ, partialTraceRight (W * X * Wᴴ) = act Φ X)
    (assign : ℝ → ℝ) (t : ℝ) :
    let D := M.data
    ‖completed D W t - quantizedCompleted D W assign t‖ ^ 2 =
      ∑ k : D.L × D.K, spectralMass D k * (2 * (1 -
        Real.cos ((retainedLogFrequency D k - assign (retainedLogFrequency D k)) * t))) := by
  dsimp only
  rw [← completedWithCoefficients_exact M.data W t, quantizedCompleted,
    ← completedWithCoefficients_sub]
  rw [frobenius_sq_trace,
    completedWithCoefficients_pair M W hW hAction, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k _
  let c := scalarPhase (retainedLogFrequency M.data k) t -
    scalarPhase (assign (retainedLogFrequency M.data k)) t
  change (((spectralMass M.data k : ℂ) * c) * star c).re = _
  rw [mul_assoc, Complex.star_def, Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq, phase_sub_sq]

private theorem integral_phase_cost (x : ℝ) :
    Integrable (fun t : ℝ => petzWeight t * (2 * (1 - Real.cos (x * t)))) ∧
    (∫ t : ℝ, petzWeight t * (2 * (1 - Real.cos (x * t)))) = 2 * (1 - logisticCorrelation x) := by
  have h (t : ℝ) : petzWeight t * (2 * (1 - Real.cos (x * t))) =
      2 * (petzWeight t - petzWeight t * Real.cos (x * t)) := by ring
  simp_rw [h]
  refine ⟨(integrable_petzWeight.sub (integrable_petzWeight_mul_cos x)).const_mul _, ?_⟩
  rw [integral_const_mul, integral_sub integrable_petzWeight (integrable_petzWeight_mul_cos x),
    integral_petzWeight, integral_petzWeight_mul_cos, logisticCorrelation]

/-- The completed physical Stinespring discrepancy has exactly the logistic
cost under the retained spectral law. -/
theorem exact_phase_discrepancy (M : SupportedRelativeModularModel Φ ρ σ)
    (W : Matrix (b × e) a ℂ) (hW : Wᴴ * W = 1)
    (hAction : ∀ X : Matrix a a ℂ, partialTraceRight (W * X * Wᴴ) = act Φ X)
    (assign : ℝ → ℝ) :
    (∫ t : ℝ, petzWeight t * ‖completed M.data W t - quantizedCompleted M.data W assign t‖ ^ 2) =
      phaseCost M.data assign := by
  simp_rw [phase_discrepancy M W hW hAction assign, Finset.mul_sum]
  rw [integral_finsetSum]
  · unfold phaseCost
    apply Finset.sum_congr rfl
    intro k _
    rw [show (fun t : ℝ => petzWeight t * (spectralMass M.data k *
        (2 * (1 - Real.cos ((retainedLogFrequency M.data k -
          assign (retainedLogFrequency M.data k)) * t))))) =
        (fun t : ℝ => spectralMass M.data k * (petzWeight t *
          (2 * (1 - Real.cos ((retainedLogFrequency M.data k -
            assign (retainedLogFrequency M.data k)) * t))))) from
        funext (fun _ => mul_left_comm _ _ _), integral_const_mul, (integral_phase_cost _).2]
  · intro k _
    simpa only [mul_left_comm (petzWeight _) (spectralMass M.data k)] using
      (integral_phase_cost (retainedLogFrequency M.data k -
        assign (retainedLogFrequency M.data k))).1.const_mul (spectralMass M.data k)

end D5.S3.Quantum.Recovery.PetzModularFrequencyQuantization
