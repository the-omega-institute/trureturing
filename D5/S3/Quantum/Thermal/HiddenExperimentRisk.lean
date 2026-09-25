/- GID: D5/S3/Quantum/Thermal/HiddenExperimentRisk
   generality: G
   mirror-B: D5/B/S3/Quantum/Thermal/HiddenExperimentRisk
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Adaptive local Kraus records ignore a hidden product factor, with a sharp randomized absolute-risk bound. -/

import Mathlib

/-!
The policy depends on the complete visible history, not on the hidden state.
Waiting unitaries can be included in the local Kraus operator. The matrix
identity holds even for unnormalised branches; hence zero-probability branches
do not require conditional-state division. Risk is a nonnegative Lebesgue
integral, so a nonintegrable estimator cannot acquire zero risk by convention.
The entropy range of arbitrary quantum density matrices is a separate obligation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Thermal.HiddenExperimentRisk

open Kronecker MeasureTheory
open scoped ENNReal

variable {a b o : Type*} [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b]

noncomputable def branch (K ρ : Matrix a a ℂ) : Matrix a a ℂ :=
  K * ρ * K.conjTranspose

/-- Local Kraus update preserves the actual hidden factor, including branch weights. -/
theorem branch_product (K ρ : Matrix a a ℂ) (σ : Matrix b b ℂ) :
    branch (K ⊗ₖ (1 : Matrix b b ℂ)) (ρ ⊗ₖ σ) = branch K ρ ⊗ₖ σ := by
  unfold branch
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    ← Matrix.mul_kronecker_mul, Matrix.mul_one]

noncomputable def visibleRecord (policy : List o → o → Matrix a a ℂ)
    (history : List o) (ρ : Matrix a a ℂ) : List o → Matrix a a ℂ
  | [] => ρ
  | x :: xs => visibleRecord policy (history ++ [x]) (branch (policy history x) ρ) xs

noncomputable def jointRecord (policy : List o → o → Matrix a a ℂ)
    (history : List o) (ρ : Matrix (a × b) (a × b) ℂ) :
    List o → Matrix (a × b) (a × b) ℂ
  | [] => ρ
  | x :: xs => jointRecord policy (history ++ [x])
      (branch (policy history x ⊗ₖ (1 : Matrix b b ℂ)) ρ) xs

/-- Induction over a genuinely adaptive visible policy, retaining full path history. -/
theorem adaptive_record_product (policy : List o → o → Matrix a a ℂ)
    (history : List o) (ρ : Matrix a a ℂ) (σ : Matrix b b ℂ) (record : List o) :
    jointRecord policy history (ρ ⊗ₖ σ) record =
      visibleRecord policy history ρ record ⊗ₖ σ := by
  induction record generalizing history ρ with
  | nil => rfl
  | cons x xs ih =>
      simp only [jointRecord, visibleRecord, branch_product]
      exact ih (history ++ [x]) (branch (policy history x) ρ)

/-- Every individual finite record has the same weight for all hidden trace-one states. -/
theorem adaptive_record_trace (policy : List o → o → Matrix a a ℂ)
    (history : List o) (ρ : Matrix a a ℂ) (σ : Matrix b b ℂ)
    (hσ : σ.trace = 1) (record : List o) :
    (jointRecord policy history (ρ ⊗ₖ σ) record).trace =
      (visibleRecord policy history ρ record).trace := by
  rw [adaptive_record_product, Matrix.trace_kronecker, hσ, mul_one]

theorem hidden_states_indistinguishable (policy : List o → o → Matrix a a ℂ)
    (ρ : Matrix a a ℂ) (σ τ : Matrix b b ℂ)
    (hσ : σ.trace = 1) (hτ : τ.trace = 1) :
    (fun record => (jointRecord policy [] (ρ ⊗ₖ σ) record).trace) =
      (fun record => (jointRecord policy [] (ρ ⊗ₖ τ) record).trace) := by
  funext record
  rw [adaptive_record_trace policy [] ρ σ hσ,
    adaptive_record_trace policy [] ρ τ hτ]

/-- Distribution of the estimator output, including all its independent randomisation. -/
noncomputable def risk (P : Measure ℝ) (θ : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal |z - θ| ∂P

private theorem two_endpoint_triangle (z L : ℝ) (hL : 0 ≤ L) :
    L ≤ |z| + |z - L| := by
  have ht := abs_add z (L - z)
  rw [show z + (L - z) = L by ring, abs_of_nonneg hL, abs_sub_comm L z] at ht
  exact ht

/-- For indistinguishable endpoint models, randomisation does not beat the diameter bound. -/
theorem endpoint_risk_sum (P : Measure ℝ) [IsProbabilityMeasure P]
    (L : ℝ) (hL : 0 ≤ L) :
    ENNReal.ofReal L ≤ risk P 0 + risk P L := by
  have hf : Measurable (fun z : ℝ => ENNReal.ofReal |z|) := by fun_prop
  have hh : ENNReal.ofReal L ≤
      ∫⁻ z : ℝ, ENNReal.ofReal |z| + ENNReal.ofReal |z - L| ∂P := by
    calc
      ENNReal.ofReal L = ∫⁻ _z : ℝ, ENNReal.ofReal L ∂P := by simp
      _ ≤ _ := lintegral_mono (fun z => by
        rw [← ENNReal.ofReal_add (abs_nonneg z) (abs_nonneg (z - L))]
        exact ENNReal.ofReal_le_ofReal (two_endpoint_triangle z L hL))
  rw [lintegral_add_left hf] at hh
  simpa only [risk, sub_zero] using hh

theorem randomized_minimax_lower (P : Measure ℝ) [IsProbabilityMeasure P]
    (L : ℝ) (hL : 0 ≤ L) :
    ENNReal.ofReal (L / 2) ≤ max (risk P 0) (risk P L) := by
  by_contra h
  have hm : max (risk P 0) (risk P L) < ENNReal.ofReal (L / 2) := lt_of_not_ge h
  have h0 := lt_of_le_of_lt (le_max_left (risk P 0) (risk P L)) hm
  have h1 := lt_of_le_of_lt (le_max_right (risk P 0) (risk P L)) hm
  have hs := ENNReal.add_lt_add h0 h1
  have hc : ENNReal.ofReal (L / 2) + ENNReal.ofReal (L / 2) = ENNReal.ofReal L := by
    rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
    congr 1
    ring
  rw [hc] at hs
  exact (not_lt_of_ge (endpoint_risk_sum P L hL)) hs

/-- The deterministic midpoint attains the uniform upper bound over the full interval. -/
theorem midpoint_risk_upper (L θ : ℝ) (hL : 0 ≤ L) (hθ0 : 0 ≤ θ) (hθL : θ ≤ L) :
    risk (Measure.dirac (L / 2)) θ ≤ ENNReal.ofReal (L / 2) := by
  have hb : |L / 2 - θ| ≤ L / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  simpa [risk] using ENNReal.ofReal_le_ofReal hb

/-- Lower and attained upper bound, quantified over arbitrary probability laws. -/
theorem sharp_no_information_risk (L : ℝ) (hL : 0 ≤ L) :
    (∀ P : Measure ℝ, IsProbabilityMeasure P →
      ENNReal.ofReal (L / 2) ≤ max (risk P 0) (risk P L)) ∧
    (∀ θ ∈ Set.Icc (0 : ℝ) L,
      risk (Measure.dirac (L / 2)) θ ≤ ENNReal.ofReal (L / 2)) := by
  constructor
  · intro P hP
    letI := hP
    exact randomized_minimax_lower P L hL
  · intro θ hθ
    exact midpoint_risk_upper L θ hL hθ.1 hθ.2

#print axioms hidden_states_indistinguishable
#print axioms sharp_no_information_risk

end D5.S3.Quantum.Thermal.HiddenExperimentRisk
