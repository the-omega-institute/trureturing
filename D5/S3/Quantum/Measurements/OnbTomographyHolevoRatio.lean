/- GID: D5/S3/Quantum/Measurements/OnbTomographyHolevoRatio
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/OnbTomographyHolevoRatio
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Full orthonormal qudit tomography has NHCRB at most d+1 times HCRB. -/

import D5.S3.Quantum.Foundation.FiniteTraceDistance

set_option autoImplicit false
open scoped BigOperators
open Matrix
open D5.S3.Quantum.Foundation.FiniteTraceDistance

namespace D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio
noncomputable section

/-- Hilbert–Schmidt orthonormal traceless Hermitian matrices, with source normalization. -/
def IsTracelessONB (d : ℕ)
    (λ : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ j, (λ j).IsHermitian) ∧ (∀ j, (λ j).trace = 0) ∧
  ∀ j k, (λ j * λ k).trace = if j = k then 1 else 0

/-- The full linear tomography model. Positivity is imposed in the claim. -/
def model (d : ℕ) (λ : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ)
    (θ : Fin (d ^ 2 - 1) → ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  (1 / (d : ℂ)) • 1 + ∑ j, (θ j : ℂ) • λ j

/-- The source's uncentered locally unbiased operators. -/
def IsLUB (d : ℕ) (λ : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ)
    (θ : Fin (d ^ 2 - 1) → ℝ)
    (x : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ k, (x k).IsHermitian) ∧ (∀ k, (model d λ θ * x k).trace = (θ k : ℂ)) ∧
  ∀ j k, (λ j * x k).trace = if j = k then 1 else 0

/-- The complex covariance matrix before subtracting the parameter square. -/
def zMatrix {d n : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ)
    (x : Fin n → Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun j k => (ρ * x j * x k).trace

/-- Entrywise imaginary part, embedded into the complex matrices for the trace norm. -/
def imPart {n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun j k => ((a j k).im : ℂ)

/-- Symmetric Hermitian blocks and the source's semidefinite constraint.
The block matrix is indexed by pairs consisting of a parameter and a quantum index. -/
def IsAdmissible {d n : ℕ} (x : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (l : Fin n → Fin n → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ j k, (l j k).IsHermitian) ∧ (∀ j k, l j k = l k j) ∧
  (fun a b : Fin n × Fin d => (l a.1 b.1 - x a.1 * x b.1) a.2 b.2).PosSemidef

/-- Holevo Cramér–Rao bound with identity weight, as the source infimum. -/
def hcrb (d : ℕ) (λ : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ)
    (θ : Fin (d ^ 2 - 1) → ℝ) : ℝ :=
  sInf {c : ℝ | ∃ x, IsLUB d λ θ x ∧
    c = (zMatrix (model d λ θ) x).trace.re +
      traceNorm (imPart (zMatrix (model d λ θ) x))} - ∑ j, θ j ^ 2

/-- Nagaoka–Hayashi Cramér–Rao bound with identity weight, as the source infimum. -/
def nhcrb (d : ℕ) (λ : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ)
    (θ : Fin (d ^ 2 - 1) → ℝ) : ℝ :=
  sInf {c : ℝ | ∃ x l, IsLUB d λ θ x ∧ IsAdmissible x l ∧
    c = (∑ j, (model d λ θ * l j j).trace).re} - ∑ j, θ j ^ 2

/-- The full-ONB form of the conjecture of Das et al., arXiv:2405.09622v2. -/
def claim : Prop :=
  ∀ d : ℕ, 2 ≤ d →
    ∀ λ : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ, IsTracelessONB d λ →
    ∀ θ : Fin (d ^ 2 - 1) → ℝ, (model d λ θ).PosSemidef →
      nhcrb d λ θ ≤ ((d : ℝ) + 1) * hcrb d λ θ

private def primal (d : ℕ)
    (λ : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ)
    (j k : Fin (d ^ 2 - 1)) : Matrix (Fin d) (Fin d) ℂ :=
  (((d : ℂ) + 1) / ((d : ℂ) + 2)) •
    (λ j * λ k + λ k * λ j + if j = k then 1 else 0)

private lemma model_trace {d : ℕ} (hd : 2 ≤ d)
    {λ : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hλ : IsTracelessONB d λ)
    (θ : Fin (d ^ 2 - 1) → ℝ) : (model d λ θ).trace = 1 := by
  sorry

private lemma basis_is_lub {d : ℕ}
    {λ : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hλ : IsTracelessONB d λ)
    (θ : Fin (d ^ 2 - 1) → ℝ) : IsLUB d λ θ λ := by
  sorry

private lemma unique_lub {d : ℕ} (hd : 2 ≤ d)
    {λ : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hλ : IsTracelessONB d λ)
    {θ : Fin (d ^ 2 - 1) → ℝ}
    {x : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hx : IsLUB d λ θ x) : x = λ := by
  sorry

private lemma casimir {d : ℕ} (hd : 2 ≤ d)
    {λ : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hλ : IsTracelessONB d λ) :
    ∑ j, λ j * λ j = (((d : ℂ) ^ 2 - 1) / (d : ℂ)) • 1 := by
  sorry

private lemma purity_expansion {d : ℕ} (hd : 2 ≤ d)
    {λ : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hλ : IsTracelessONB d λ)
    (θ : Fin (d ^ 2 - 1) → ℝ) :
    (model d λ θ * model d λ θ).trace.re = 1 / (d : ℝ) + ∑ j, θ j ^ 2 := by
  sorry

private lemma real_cost {d : ℕ} (hd : 2 ≤ d)
    {λ : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hλ : IsTracelessONB d λ)
    (θ : Fin (d ^ 2 - 1) → ℝ) :
    (zMatrix (model d λ θ) λ).trace.re = ((d : ℝ) ^ 2 - 1) / d := by
  have ht := model_trace hd hλ θ
  have hc := casimir hd hλ
  sorry

private lemma imaginary_bound {d : ℕ} (hd : 2 ≤ d)
    {λ : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hλ : IsTracelessONB d λ)
    (θ : Fin (d ^ 2 - 1) → ℝ) (hρ : (model d λ θ).PosSemidef) :
    (d : ℝ) * (model d λ θ * model d λ θ).trace.re - 1 ≤
      traceNorm (imPart (zMatrix (model d λ θ) λ)) := by
  sorry

private lemma holevo_exact {d : ℕ} (hd : 2 ≤ d)
    {λ : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hλ : IsTracelessONB d λ)
    (θ : Fin (d ^ 2 - 1) → ℝ) :
    hcrb d λ θ = (zMatrix (model d λ θ) λ).trace.re +
      traceNorm (imPart (zMatrix (model d λ θ) λ)) - ∑ j, θ j ^ 2 := by
  have hl := basis_is_lub hλ θ
  have hu := @unique_lub d hd λ hλ θ
  sorry

private lemma holevo_lower {d : ℕ} (hd : 2 ≤ d)
    {λ : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hλ : IsTracelessONB d λ)
    (θ : Fin (d ^ 2 - 1) → ℝ) (hρ : (model d λ θ).PosSemidef) :
    ((d : ℝ) ^ 2 - 1) / d ≤ hcrb d λ θ := by
  have he := holevo_exact hd hλ θ
  have hr := real_cost hd hλ θ
  have hi := imaginary_bound hd hλ θ hρ
  have hp := purity_expansion hd hλ θ
  sorry

private lemma primal_admissible {d : ℕ} (hd : 2 ≤ d)
    {λ : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hλ : IsTracelessONB d λ) :
    IsAdmissible λ (primal d λ) := by
  sorry

private lemma primal_cost {d : ℕ} (hd : 2 ≤ d)
    {λ : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hλ : IsTracelessONB d λ)
    (θ : Fin (d ^ 2 - 1) → ℝ) :
    (∑ j, (model d λ θ * primal d λ j j).trace).re =
      (((d : ℝ) ^ 2 - 1) * ((d : ℝ) + 1)) / d := by
  have hc := casimir hd hλ
  have ht := model_trace hd hλ θ
  sorry

private lemma admissible_cost_nonneg {d n : ℕ}
    {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : ρ.PosSemidef)
    {x : Fin n → Matrix (Fin d) (Fin d) ℂ} (hx : ∀ j, (x j).IsHermitian)
    {l : Fin n → Fin n → Matrix (Fin d) (Fin d) ℂ} (hl : IsAdmissible x l) :
    0 ≤ (∑ j, (ρ * l j j).trace).re := by
  sorry

private lemma nagaoka_upper {d : ℕ} (hd : 2 ≤ d)
    {λ : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hλ : IsTracelessONB d λ)
    (θ : Fin (d ^ 2 - 1) → ℝ) (hρ : (model d λ θ).PosSemidef) :
    nhcrb d λ θ ≤ (((d : ℝ) ^ 2 - 1) * ((d : ℝ) + 1)) / d - ∑ j, θ j ^ 2 := by
  have hl := basis_is_lub hλ θ
  have ha := primal_admissible hd hλ
  have hc := primal_cost hd hλ θ
  have hn := @admissible_cost_nonneg d (d ^ 2 - 1) (model d λ θ) hρ
  sorry

theorem result : claim := by
  intro d hd λ hλ θ hρ
  have hh := holevo_lower hd hλ θ hρ
  have hn := nagaoka_upper hd hλ θ hρ
  have hs : 0 ≤ ∑ j, θ j ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg (θ j))
  have hdpos : 0 ≤ (d : ℝ) + 1 := by positivity
  calc
    nhcrb d λ θ ≤ (((d : ℝ) ^ 2 - 1) * ((d : ℝ) + 1)) / d := by linarith
    _ = ((d : ℝ) + 1) * (((d : ℝ) ^ 2 - 1) / d) := by ring
    _ ≤ ((d : ℝ) + 1) * hcrb d λ θ := mul_le_mul_of_nonneg_left hh hdpos

end D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio
