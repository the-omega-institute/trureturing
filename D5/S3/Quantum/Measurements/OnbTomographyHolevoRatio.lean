/- GID: D5/S3/Quantum/Measurements/OnbTomographyHolevoRatio
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/OnbTomographyHolevoRatio
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Full orthonormal qudit tomography has NHCRB at most d+1 times HCRB. -/

import D5.S3.Quantum.Foundation.FiniteTraceDistance

/-! The source bounds use uncentered LUB operators and subtract the parameter square. -/

set_option autoImplicit false
open scoped BigOperators ComplexOrder
open Matrix
open D5.S3.Quantum.Foundation.FiniteTraceDistance

namespace D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio
noncomputable section

/-- Hilbert–Schmidt orthonormal traceless Hermitian matrices, with source normalization. -/
def IsTracelessONB (d : ℕ)
    (b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ j, (b j).IsHermitian) ∧ (∀ j, (b j).trace = 0) ∧
  ∀ j k, (b j * b k).trace = if j = k then 1 else 0

/-- The full linear tomography model. Positivity is imposed in the claim. -/
def model (d : ℕ) (b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ)
    (θ : Fin (d ^ 2 - 1) → ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  (1 / (d : ℂ)) • 1 + ∑ j, (θ j : ℂ) • b j

/-- The source's uncentered locally unbiased operators. -/
def IsLUB (d : ℕ) (b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ)
    (θ : Fin (d ^ 2 - 1) → ℝ)
    (x : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ k, (x k).IsHermitian) ∧ (∀ k, (model d b θ * x k).trace = (θ k : ℂ)) ∧
  ∀ j k, (b j * x k).trace = if j = k then 1 else 0

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
  (show Matrix (Fin n × Fin d) (Fin n × Fin d) ℂ from
    fun a b => (l a.1 b.1 - x a.1 * x b.1) a.2 b.2).PosSemidef

/-- Holevo Cramér–Rao bound with identity weight, as the source infimum. -/
def hcrb (d : ℕ) (b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ)
    (θ : Fin (d ^ 2 - 1) → ℝ) : ℝ :=
  sInf {c : ℝ | ∃ x, IsLUB d b θ x ∧
    c = (zMatrix (model d b θ) x).trace.re +
      traceNorm (imPart (zMatrix (model d b θ) x))} - ∑ j, θ j ^ 2

/-- Nagaoka–Hayashi Cramér–Rao bound with identity weight, as the source infimum. -/
def nhcrb (d : ℕ) (b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ)
    (θ : Fin (d ^ 2 - 1) → ℝ) : ℝ :=
  sInf {c : ℝ | ∃ x l, IsLUB d b θ x ∧ IsAdmissible x l ∧
    c = (∑ j, (model d b θ * l j j).trace).re} - ∑ j, θ j ^ 2

/-- The full-ONB form of the conjecture of Das et al., arXiv:2405.09622v2. -/
def claim : Prop :=
  ∀ d : ℕ, 2 ≤ d →
    ∀ b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ, IsTracelessONB d b →
    ∀ θ : Fin (d ^ 2 - 1) → ℝ, (model d b θ).PosSemidef →
      nhcrb d b θ ≤ ((d : ℝ) + 1) * hcrb d b θ

private def primal (d : ℕ)
    (b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ)
    (j k : Fin (d ^ 2 - 1)) : Matrix (Fin d) (Fin d) ℂ :=
  (((d : ℂ) + 1) / ((d : ℂ) + 2)) •
    (b j * b k + b k * b j + if j = k then 1 else 0)

private lemma model_trace {d : ℕ} (hd : 2 ≤ d)
    {b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hb : IsTracelessONB d b)
    (θ : Fin (d ^ 2 - 1) → ℝ) : (model d b θ).trace = 1 := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  simp [model, trace_add, trace_smul, trace_sum, hb.2.1, hd0]

private lemma basis_is_lub {d : ℕ}
    {b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hb : IsTracelessONB d b)
    (θ : Fin (d ^ 2 - 1) → ℝ) : IsLUB d b θ b := by
  classical
  refine ⟨hb.1, ?_, hb.2.2⟩
  intro k
  simp [model, add_mul, smul_mul, Finset.sum_mul, trace_add, trace_sum,
    trace_smul, hb.2.1, hb.2.2]

private lemma unique_lub {d : ℕ} (hd : 2 ≤ d)
    {b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hb : IsTracelessONB d b)
    {θ : Fin (d ^ 2 - 1) → ℝ}
    {x : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hx : IsLUB d b θ x) : x = b := by
  sorry

private lemma casimir {d : ℕ} (hd : 2 ≤ d)
    {b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hb : IsTracelessONB d b) :
    ∑ j, b j * b j = (((d : ℂ) ^ 2 - 1) / (d : ℂ)) • 1 := by
  sorry

private lemma purity_expansion {d : ℕ} (hd : 2 ≤ d)
    {b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hb : IsTracelessONB d b)
    (θ : Fin (d ^ 2 - 1) → ℝ) :
    (model d b θ * model d b θ).trace.re = 1 / (d : ℝ) + ∑ j, θ j ^ 2 := by
  have ht := model_trace hd hb θ
  have he := (basis_is_lub hb θ).2.1
  have hp : (model d b θ * model d b θ).trace =
      1 / (d : ℂ) + ∑ j, (θ j : ℂ) ^ 2 := by
    calc
      _ = (model d b θ * ((1 / (d : ℂ)) • 1 + ∑ j, (θ j : ℂ) • b j)).trace := rfl
      _ = _ := by
        simp only [mul_add, Matrix.mul_smul, mul_one, Finset.mul_sum, trace_add,
          trace_smul, trace_sum, ht, he, mul_one, smul_eq_mul, pow_two]
  have heq : (model d b θ * model d b θ).trace =
      ((1 / (d : ℝ) + ∑ j, θ j ^ 2 : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_natCast, Complex.ofReal_sum, Complex.ofReal_pow] using hp
  simpa only [Complex.ofReal_re] using congrArg Complex.re heq

private lemma real_cost {d : ℕ} (hd : 2 ≤ d)
    {b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hb : IsTracelessONB d b)
    (θ : Fin (d ^ 2 - 1) → ℝ) :
    (zMatrix (model d b θ) b).trace.re = ((d : ℝ) ^ 2 - 1) / d := by
  have ht := model_trace hd hb θ
  have hc := casimir hd hb
  have he : (zMatrix (model d b θ) b).trace =
      ((d : ℂ) ^ 2 - 1) / (d : ℂ) := by
    change (∑ j, (model d b θ * b j * b j).trace) = _
    simp_rw [mul_assoc]
    rw [← trace_sum, ← Finset.mul_sum, hc, Matrix.mul_smul, mul_one, trace_smul, ht]
    simp
  rw [he]
  have hh : ((d : ℂ) ^ 2 - 1) / (d : ℂ) =
      ((((d : ℝ) ^ 2 - 1) / d : ℝ) : ℂ) := by push_cast; rfl
  rw [hh, Complex.ofReal_re]

private lemma imaginary_bound {d : ℕ} (hd : 2 ≤ d)
    {b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hb : IsTracelessONB d b)
    (θ : Fin (d ^ 2 - 1) → ℝ) (hρ : (model d b θ).PosSemidef) :
    (d : ℝ) * (model d b θ * model d b θ).trace.re - 1 ≤
      traceNorm (imPart (zMatrix (model d b θ) b)) := by
  sorry

private lemma holevo_exact {d : ℕ} (hd : 2 ≤ d)
    {b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hb : IsTracelessONB d b)
    (θ : Fin (d ^ 2 - 1) → ℝ) :
    hcrb d b θ = (zMatrix (model d b θ) b).trace.re +
      traceNorm (imPart (zMatrix (model d b θ) b)) - ∑ j, θ j ^ 2 := by
  have hl := basis_is_lub hb θ
  have hu := @unique_lub d hd b hb θ
  have he : {c : ℝ | ∃ x, IsLUB d b θ x ∧
      c = (zMatrix (model d b θ) x).trace.re +
        traceNorm (imPart (zMatrix (model d b θ) x))} =
      {(zMatrix (model d b θ) b).trace.re +
        traceNorm (imPart (zMatrix (model d b θ) b))} := by
    ext c
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hu hx]
      exact Set.mem_singleton _
    · intro hc
      exact ⟨b, hl, Set.mem_singleton_iff.mp hc⟩
  rw [hcrb, he, csInf_singleton]

private lemma holevo_lower {d : ℕ} (hd : 2 ≤ d)
    {b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hb : IsTracelessONB d b)
    (θ : Fin (d ^ 2 - 1) → ℝ) (hρ : (model d b θ).PosSemidef) :
    ((d : ℝ) ^ 2 - 1) / d ≤ hcrb d b θ := by
  have he := holevo_exact hd hb θ
  have hr := real_cost hd hb θ
  have hi := imaginary_bound hd hb θ hρ
  have hp := purity_expansion hd hb θ
  have hs : 0 ≤ ∑ j, θ j ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg (θ j))
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hdiv : (d : ℝ) * (1 / (d : ℝ)) = 1 := by field_simp
  rw [he, hr]
  nlinarith

private lemma primal_admissible {d : ℕ} (hd : 2 ≤ d)
    {b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hb : IsTracelessONB d b) :
    IsAdmissible b (primal d b) := by
  sorry

private lemma primal_cost {d : ℕ} (hd : 2 ≤ d)
    {b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hb : IsTracelessONB d b)
    (θ : Fin (d ^ 2 - 1) → ℝ) :
    (∑ j, (model d b θ * primal d b j j).trace).re =
      (((d : ℝ) ^ 2 - 1) * ((d : ℝ) + 1)) / d := by
  have hc := casimir hd hb
  have ht := model_trace hd hb θ
  sorry

private lemma admissible_cost_nonneg {d n : ℕ}
    {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : ρ.PosSemidef)
    {x : Fin n → Matrix (Fin d) (Fin d) ℂ} (hx : ∀ j, (x j).IsHermitian)
    {l : Fin n → Fin n → Matrix (Fin d) (Fin d) ℂ} (hl : IsAdmissible x l) :
    0 ≤ (∑ j, (ρ * l j j).trace).re := by
  sorry

private lemma nagaoka_upper {d : ℕ} (hd : 2 ≤ d)
    {b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hb : IsTracelessONB d b)
    (θ : Fin (d ^ 2 - 1) → ℝ) (hρ : (model d b θ).PosSemidef) :
    nhcrb d b θ ≤ (((d : ℝ) ^ 2 - 1) * ((d : ℝ) + 1)) / d - ∑ j, θ j ^ 2 := by
  have hl := basis_is_lub hb θ
  have ha := primal_admissible hd hb
  have hc := primal_cost hd hb θ
  have hn := @admissible_cost_nonneg d (d ^ 2 - 1) (model d b θ) hρ
  have hbd : BddBelow {c : ℝ | ∃ x l, IsLUB d b θ x ∧ IsAdmissible x l ∧
      c = (∑ j, (model d b θ * l j j).trace).re} := by
    refine ⟨0, ?_⟩
    rintro c ⟨x, l, hx, ha, rfl⟩
    exact hn hx.1 ha
  have hf : (∑ j, (model d b θ * primal d b j j).trace).re ∈
      {c : ℝ | ∃ x l, IsLUB d b θ x ∧ IsAdmissible x l ∧
        c = (∑ j, (model d b θ * l j j).trace).re} :=
    ⟨b, primal d b, hl, ha, rfl⟩
  have hi := csInf_le hbd hf
  rw [nhcrb]
  rw [hc] at hi
  exact sub_le_sub_right hi _

theorem result : claim := by
  intro d hd b hb θ hρ
  have hh := holevo_lower hd hb θ hρ
  have hn := nagaoka_upper hd hb θ hρ
  have hs : 0 ≤ ∑ j, θ j ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg (θ j))
  have hdpos : 0 ≤ (d : ℝ) + 1 := by positivity
  calc
    nhcrb d b θ ≤ (((d : ℝ) ^ 2 - 1) * ((d : ℝ) + 1)) / d := by linarith
    _ = ((d : ℝ) + 1) * (((d : ℝ) ^ 2 - 1) / d) := by ring
    _ ≤ ((d : ℝ) + 1) * hcrb d b θ := mul_le_mul_of_nonneg_left hh hdpos

end
end D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio
