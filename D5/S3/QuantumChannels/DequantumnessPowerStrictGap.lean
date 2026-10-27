/- GID: D5/S3/QuantumChannels/DequantumnessPowerStrictGap
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/DequantumnessPowerStrictGap
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuantumChannels/DequantumnessPowerStrictGap.claim; result=D5/S3/QuantumChannels/DequantumnessPowerStrictGap.result; claim=D5/S3/QuantumChannels/DequantumnessPowerStrictGap.claim
   digest: A translated qubit contraction has strictly greater unrestricted dequantumness power. -/

import D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation
import D5.S3.Quantum.Information.ActualPureQubitGeometry

/-! Two-state ensemble quantumness for a translated qubit contraction. -/

set_option autoImplicit false
set_option linter.style.longLine false

open scoped BigOperators Matrix ComplexOrder
open Matrix
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsDensity IsCPTP)
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum

noncomputable section
namespace D5.S3.QuantumChannels.DequantumnessPowerStrictGap

/-- Equation (1) for the two weights `p` and `1-p`. -/
def quantumness (p : ℝ) (ρ σ : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  -(∑ i : Fin 2, ∑ j : Fin 2,
    (![p, 1-p] i * ![p, 1-p] j) *
      (Matrix.trace ((![ρ, σ] i * ![ρ, σ] j - ![ρ, σ] j * ![ρ, σ] i)^2)).re)

/-- All two-state qubit ensembles, including zero weights. -/
def TwoStateEnsemble (p : ℝ) (ρ σ : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  0 ≤ p ∧ p ≤ 1 ∧ IsDensity ρ ∧ IsDensity σ

/-- The source's unrestricted two-ingredient dequantumness power. -/
def dequantumnessPower (φ : MatrixMap (Fin 2) (Fin 2) ℂ) : ℝ :=
  sSup {x | ∃ p ρ σ, TwoStateEnsemble p ρ σ ∧
    x = quantumness p ρ σ - quantumness p (φ ρ) (φ σ)}

/-- The supremum of Equation (1) over all two-state qubit ensembles. -/
def maxQuantumness : ℝ :=
  sSup {x | ∃ p ρ σ, TwoStateEnsemble p ρ σ ∧ x = quantumness p ρ σ}

/-- The source's restriction to ensembles attaining maximal initial quantumness. -/
def restrictedDequantumnessPower (φ : MatrixMap (Fin 2) (Fin 2) ℂ) : ℝ :=
  sSup {x | ∃ p ρ σ, TwoStateEnsemble p ρ σ ∧ quantumness p ρ σ = maxQuantumness ∧
    x = quantumness p ρ σ - quantumness p (φ ρ) (φ σ)}

/-- Universal equality of the two source notions for qubit channels. -/
def claim : Prop := ∀ φ : MatrixMap (Fin 2) (Fin 2) ℂ,
  IsCPTP φ → dequantumnessPower φ = restrictedDequantumnessPower φ

private def channel : MatrixMap (Fin 2) (Fin 2) ℂ where
  toFun x := (1/2 : ℂ) • x + (Matrix.trace x / 2) • !![(3/4 : ℂ), 0; 0, 1/4]
  map_add' x y := by simp only [Matrix.trace_add, add_div, add_smul, smul_add]; abel
  map_smul' c x := by
    simp only [Matrix.trace_smul, smul_add, smul_smul, RingHom.id_apply]
    congr 1 <;> congr 1 <;> ring

private lemma dot_nonneg (r : Fin 3 → ℝ) : 0 ≤ r ⬝ᵥ r := by
  change 0 ≤ ∑ i, r i * r i
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (r i))

private lemma dot_cauchy (r s : Fin 3 → ℝ) :
    (r ⬝ᵥ s)^2 ≤ (r ⬝ᵥ r) * (s ⬝ᵥ s) := by
  change (∑ i, r i * s i)^2 ≤ (∑ i, r i * r i) * (∑ i, s i * s i)
  simpa only [pow_two] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ r s

private lemma orthonormal_cross_lower (r s : Fin 3 → ℝ)
    (hr : r ⬝ᵥ r = 1) (hs : s ⬝ᵥ s = 1) (hrs : r ⬝ᵥ s = 0) :
    let f := fun x : Fin 3 → ℝ => (1/2 : ℝ) • x + (1/4 : ℝ) • ![0, 0, 1]
    (1/4 : ℝ) * (1/2 - Real.sqrt 2 / 4)^2 ≤ (f r ⨯₃ f s) ⬝ᵥ (f r ⨯₃ f s) := by
  let f := fun x : Fin 3 → ℝ => (1/2 : ℝ) • x + (1/4 : ℝ) • ![0, 0, 1]
  change (1/4 : ℝ) * (1/2 - Real.sqrt 2 / 4)^2 ≤ (f r ⨯₃ f s) ⬝ᵥ (f r ⨯₃ f s)
  have hsr : s ⬝ᵥ r = 0 := by rw [dotProduct_comm, hrs]
  have hw : (r ⨯₃ s) ⬝ᵥ (r ⨯₃ s) = 1 := by
    rw [cross_dot_cross, hr, hs, hrs, hsr]
    norm_num
  have hproj : (f r ⨯₃ f s) ⬝ᵥ (r ⨯₃ s) = 1/4 + (r 2 + s 2)/8 := by
    rw [cross_dot_cross]
    dsimp only [f]
    simp only [add_dotProduct, smul_dotProduct, hr, hs, hrs, hsr]
    simp only [vec3_dotProduct, cons_val_zero, cons_val_one, cons_val_two, head_cons, tail_cons,
      zero_mul, one_mul, zero_add, smul_eq_mul]
    ring
  have hsum : (r 2 + s 2)^2 ≤ 2 := by
    have hc := dot_cauchy (r+s) (![0, 0, 1] : Fin 3 → ℝ)
    have hn : (r+s) ⬝ᵥ (r+s) = 2 := by
      rw [add_dotProduct, dotProduct_add, dotProduct_add, hr, hs, hrs, hsr]
      norm_num
    rw [hn] at hc
    simpa only [vec3_dotProduct, Pi.add_apply, cons_val_zero, cons_val_one,
      cons_val_two, head_cons, tail_cons, mul_zero, mul_one, zero_mul, one_mul, zero_add, add_zero,
      one_add_one_eq_two] using hc
  have hsqrt := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hsqrt0 := Real.sqrt_nonneg (2 : ℝ)
  have hsqrt2 : Real.sqrt 2 < 2 := by nlinarith
  have hb : -Real.sqrt 2 ≤ r 2 + s 2 := by nlinarith
  have hc := dot_cauchy (f r ⨯₃ f s) (r ⨯₃ s)
  rw [hw, mul_one, hproj] at hc
  have hsq : (1/4 - Real.sqrt 2/8)^2 ≤ (1/4 + (r 2+s 2)/8)^2 := by
    nlinarith
  nlinarith

private lemma density_bloch (ρ : Matrix (Fin 2) (Fin 2) ℂ) (hρ : IsDensity ρ) :
    ∃ r : EuclideanSpace ℝ (Fin 3), ρ = blochMatrix 1 r ∧ r.ofLp ⬝ᵥ r.ofLp ≤ 1 := by
  refine ⟨bloch ρ, ?_, ?_⟩
  · simpa only [hρ.2, Complex.one_re] using
      (bloch_geometry_of_isHermitian ρ hρ.1.isHermitian).1
  · have hn := norm_bloch_le_trace_of_posSemidef ρ hρ.1
    rw [hρ.2, Complex.one_re] at hn
    have hn2 : ‖bloch ρ‖^2 ≤ 1 := by nlinarith [norm_nonneg (bloch ρ)]
    rw [EuclideanSpace.real_norm_sq_eq] at hn2
    change (∑ i, (bloch ρ).ofLp i * (bloch ρ).ofLp i) ≤ 1
    simpa only [pow_two] using hn2

private lemma quantumness_bloch (p : ℝ) (r s : EuclideanSpace ℝ (Fin 3)) :
    quantumness p (blochMatrix 1 r) (blochMatrix 1 s) =
      p * (1-p) * ((r.ofLp ⨯₃ s.ofLp) ⬝ᵥ (r.ofLp ⨯₃ s.ofLp)) := by
  unfold quantumness blochMatrix
  simp [Fin.sum_univ_two, pow_two, Matrix.trace_fin_two, Matrix.mul_apply,
    cross_apply]
  ring

private lemma cross_bounds (r s : Fin 3 → ℝ)
    (hr : r ⬝ᵥ r ≤ 1) (hs : s ⬝ᵥ s ≤ 1) :
    0 ≤ (r ⨯₃ s) ⬝ᵥ (r ⨯₃ s) ∧ (r ⨯₃ s) ⬝ᵥ (r ⨯₃ s) ≤ 1 := by
  refine ⟨dot_nonneg _, ?_⟩
  rw [cross_dot_cross, dotProduct_comm s r]
  have hm : (r ⬝ᵥ r) * (s ⬝ᵥ s) ≤ 1 := by
    calc
      _ ≤ 1 * (s ⬝ᵥ s) := mul_le_mul_of_nonneg_right hr (dot_nonneg s)
      _ ≤ 1 := by simpa only [one_mul] using hs
  nlinarith [sq_nonneg (r ⬝ᵥ s)]

private lemma projection_density (ρ : Matrix (Fin 2) (Fin 2) ℂ)
    (hh : ρ.IsHermitian) (hp : ρ * ρ = ρ) (ht : ρ.trace = 1) : IsDensity ρ := by
  refine ⟨?_, ht⟩
  have h := Matrix.posSemidef_self_mul_conjTranspose ρ
  rwa [hh.eq, hp] at h

private lemma quantumness_bounds {p : ℝ} {ρ σ : Matrix (Fin 2) (Fin 2) ℂ}
    (h : TwoStateEnsemble p ρ σ) : 0 ≤ quantumness p ρ σ ∧ quantumness p ρ σ ≤ 1/4 := by
  obtain ⟨r, rfl, hr⟩ := density_bloch ρ h.2.2.1
  obtain ⟨s, rfl, hs⟩ := density_bloch σ h.2.2.2
  rw [quantumness_bloch]
  have hn := cross_bounds r.ofLp s.ofLp hr hs
  have hp : 0 ≤ p * (1-p) := mul_nonneg h.1 (sub_nonneg.mpr h.2.1)
  have hp1 : p * (1-p) ≤ 1/4 := by nlinarith [sq_nonneg (p-1/2)]
  exact ⟨mul_nonneg hp hn.1, by nlinarith [mul_nonneg hp (sub_nonneg.mpr hn.2)]⟩

private lemma maximizing_ensemble :
    ∃ p ρ σ, TwoStateEnsemble p ρ σ ∧ quantumness p ρ σ = 1/4 := by
  let ρ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]
  let σ : Matrix (Fin 2) (Fin 2) ℂ := !![1/2, 1/2; 1/2, 1/2]
  have hρ : IsDensity ρ := by
    apply projection_density
    · change ρᴴ = ρ
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ρ, Matrix.conjTranspose_apply]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [ρ, Matrix.mul_apply, Fin.sum_univ_two]
    · norm_num [ρ, Matrix.trace_fin_two]
  have hσ : IsDensity σ := by
    apply projection_density
    · change σᴴ = σ
      ext i j
      fin_cases i <;> fin_cases j <;> simp [σ, Matrix.conjTranspose_apply]
    · ext i j
      fin_cases i <;> fin_cases j <;> norm_num [σ, Matrix.mul_apply, Fin.sum_univ_two]
    · norm_num [σ, Matrix.trace_fin_two]
  refine ⟨1/2, ρ, σ, ⟨by norm_num, by norm_num, hρ, hσ⟩, ?_⟩
  unfold quantumness
  norm_num [ρ, σ, Fin.sum_univ_two, Matrix.trace_fin_two, pow_two, Matrix.mul_apply]

private lemma max_quantumness : maxQuantumness = 1/4 := by
  obtain ⟨p, ρ, σ, h, hq⟩ := maximizing_ensemble
  have hb : BddAbove {x | ∃ p ρ σ, TwoStateEnsemble p ρ σ ∧ x = quantumness p ρ σ} := by
    refine ⟨1/4, ?_⟩
    rintro x ⟨p, ρ, σ, h, rfl⟩
    exact (quantumness_bounds h).2
  apply le_antisymm
  · apply csSup_le
    · exact ⟨quantumness p ρ σ, p, ρ, σ, h, rfl⟩
    · rintro x ⟨p, ρ, σ, h, rfl⟩
      exact (quantumness_bounds h).2
  · exact le_csSup hb ⟨p, ρ, σ, h, hq.symm⟩

private lemma maximal_bloch {p : ℝ} {ρ σ : Matrix (Fin 2) (Fin 2) ℂ}
    (h : TwoStateEnsemble p ρ σ) (hq : quantumness p ρ σ = maxQuantumness) :
    ∃ r s : EuclideanSpace ℝ (Fin 3), ρ = blochMatrix 1 r ∧ σ = blochMatrix 1 s ∧
      p = 1/2 ∧ r.ofLp ⬝ᵥ r.ofLp = 1 ∧ s.ofLp ⬝ᵥ s.ofLp = 1 ∧
      r.ofLp ⬝ᵥ s.ofLp = 0 := by
  obtain ⟨r, hrho, hr⟩ := density_bloch ρ h.2.2.1
  obtain ⟨s, hsigma, hs⟩ := density_bloch σ h.2.2.2
  refine ⟨r, s, hrho, hsigma, ?_⟩
  rw [hrho, hsigma, quantumness_bloch, max_quantumness] at hq
  have hn := cross_bounds r.ofLp s.ofLp hr hs
  have hp0 : 0 ≤ p * (1-p) := mul_nonneg h.1 (sub_nonneg.mpr h.2.1)
  have hp1 : p * (1-p) ≤ 1/4 := by nlinarith [sq_nonneg (p-1/2)]
  have hp : p = 1/2 := by
    nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hn.2), sq_nonneg (p-1/2)]
  refine ⟨hp, ?_⟩
  rw [hp] at hq
  have hn1 : (r.ofLp ⨯₃ s.ofLp) ⬝ᵥ (r.ofLp ⨯₃ s.ofLp) = 1 := by nlinarith
  rw [cross_dot_cross, dotProduct_comm s.ofLp r.ofLp] at hn1
  have hm : (r.ofLp ⬝ᵥ r.ofLp) * (s.ofLp ⬝ᵥ s.ofLp) ≤ 1 := by
    calc
      _ ≤ 1 * (s.ofLp ⬝ᵥ s.ofLp) := mul_le_mul_of_nonneg_right hr (dot_nonneg s.ofLp)
      _ ≤ 1 := by simpa only [one_mul] using hs
  have hrs : r.ofLp ⬝ᵥ s.ofLp = 0 := by nlinarith [sq_nonneg (r.ofLp ⬝ᵥ s.ofLp)]
  refine ⟨?_, ?_, hrs⟩
  · nlinarith [mul_nonneg (dot_nonneg r.ofLp) (sub_nonneg.mpr hs)]
  · nlinarith [mul_nonneg (dot_nonneg s.ofLp) (sub_nonneg.mpr hr)]

private lemma channel_bloch (r : EuclideanSpace ℝ (Fin 3)) :
    channel (blochMatrix 1 r) =
      blochMatrix 1 (WithLp.toLp 2 ((1/2 : ℝ) • r.ofLp + (1/4 : ℝ) • ![0, 0, 1])) := by
  rw [channel.eq_1]
  change (1/2 : ℂ) • blochMatrix 1 r +
    (Matrix.trace (blochMatrix 1 r) / 2) • !![(3/4 : ℂ), 0; 0, 1/4] = _
  rw [blochMatrix_trace]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blochMatrix] <;> ring

private lemma channel_cptp : IsCPTP channel := by
  let k : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ :=
    ![!![(Real.sqrt 2 : ℂ)/2, 0; 0, (Real.sqrt 2 : ℂ)/2],
      !![(Real.sqrt 6 : ℂ)/4, 0; 0, 0],
      !![0, (Real.sqrt 6 : ℂ)/4; 0, 0],
      !![0, 0; (Real.sqrt 2 : ℂ)/4, 0],
      !![0, 0; 0, (Real.sqrt 2 : ℂ)/4]]
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h6 := Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
  have he : MatrixMap.of_kraus k k = channel := by
    ext x i j
    change (∑ n : Fin 5, k n * x * (k n)ᴴ) i j = _
    simp only [Fin.sum_univ_succ, Matrix.add_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [k, channel, Matrix.trace_fin_two] <;>
      ring_nf <;> simp only [h2, h6] <;> ring
  refine ⟨he ▸ MatrixMap.of_kraus_isCompletelyPositive k, ?_⟩
  intro x
  change Matrix.trace ((1/2 : ℂ) • x +
    (Matrix.trace x / 2) • !![(3/4 : ℂ), 0; 0, 1/4]) = Matrix.trace x
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_fin_two]
  norm_num
  ring

private lemma witness_loss :
    ∃ p ρ σ, TwoStateEnsemble p ρ σ ∧
      quantumness p ρ σ - quantumness p (channel ρ) (channel σ) = 1329215/5345344 := by
  let q : ℝ := Real.sqrt 145
  have hq : q^2 = 145 := Real.sq_sqrt (by norm_num)
  let ρ : Matrix (Fin 2) (Fin 2) ℂ := !![5/34, (q : ℂ)/34; (q : ℂ)/34, 29/34]
  let σ : Matrix (Fin 2) (Fin 2) ℂ := !![5/34, -(q : ℂ)/34; -(q : ℂ)/34, 29/34]
  have hρ : IsDensity ρ := by
    apply projection_density
    · change ρᴴ = ρ
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ρ, Matrix.conjTranspose_apply]
    · ext i j
      fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
        simp [ρ, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith
    · norm_num [ρ, Matrix.trace_fin_two]
  have hσ : IsDensity σ := by
    apply projection_density
    · change σᴴ = σ
      ext i j
      fin_cases i <;> fin_cases j <;> simp [σ, Matrix.conjTranspose_apply]
    · ext i j
      fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
        simp [σ, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith
    · norm_num [σ, Matrix.trace_fin_two]
  refine ⟨1/2, ρ, σ, ⟨by norm_num, by norm_num, hρ, hσ⟩, ?_⟩
  unfold quantumness
  simp [ρ, σ, channel, Fin.sum_univ_two, Matrix.trace_fin_two, pow_two, Matrix.mul_apply]
  nlinarith [sq_nonneg (q^2-145)]

private lemma restricted_loss {p : ℝ} {ρ σ : Matrix (Fin 2) (Fin 2) ℂ}
    (h : TwoStateEnsemble p ρ σ) (hq : quantumness p ρ σ = maxQuantumness) :
    quantumness p ρ σ - quantumness p (channel ρ) (channel σ) ≤
      (29 + 2 * Real.sqrt 2) / 128 := by
  obtain ⟨r, s, rfl, rfl, rfl, hr, hs, hrs⟩ := maximal_bloch h hq
  rw [quantumness_bloch, channel_bloch, channel_bloch, quantumness_bloch,
    cross_dot_cross, hr, hs, hrs, dotProduct_comm s.ofLp r.ofLp, hrs]
  have hb := orthonormal_cross_lower r.ofLp s.ofLp hr hs hrs
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  change _ ≤ (29 + 2 * Real.sqrt 2) / 128
  dsimp only at hb
  change (1/4 : ℝ) * (1/2 - Real.sqrt 2 / 4)^2 ≤ _ at hb
  nlinarith

private lemma power_lower : (1329215/5345344 : ℝ) ≤ dequantumnessPower channel := by
  apply le_csSup
  · refine ⟨1/4, ?_⟩
    rintro x ⟨p, ρ, σ, h, rfl⟩
    have hi := (quantumness_bounds h).2
    obtain ⟨r, hr, _⟩ := density_bloch ρ h.2.2.1
    obtain ⟨s, hs, _⟩ := density_bloch σ h.2.2.2
    have ho : 0 ≤ quantumness p (channel ρ) (channel σ) := by
      rw [hr, hs, channel_bloch, channel_bloch, quantumness_bloch]
      exact mul_nonneg (mul_nonneg h.1 (sub_nonneg.mpr h.2.1)) (dot_nonneg _)
    linarith
  · obtain ⟨p, ρ, σ, h, he⟩ := witness_loss
    exact ⟨p, ρ, σ, h, he.symm⟩

private lemma restricted_power_upper :
    restrictedDequantumnessPower channel ≤ (29 + 2 * Real.sqrt 2) / 128 := by
  apply csSup_le
  · obtain ⟨p, ρ, σ, h, hq⟩ := maximizing_ensemble
    refine ⟨quantumness p ρ σ - quantumness p (channel ρ) (channel σ),
      p, ρ, σ, h, ?_, rfl⟩
    rwa [max_quantumness]
  · rintro x ⟨p, ρ, σ, h, hq, rfl⟩
    exact restricted_loss h hq

private lemma strict_comparison :
    (29 + 2 * Real.sqrt 2) / 128 < (1329215/5345344 : ℝ) := by
  have h0 := Real.sqrt_nonneg (2 : ℝ)
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hb : Real.sqrt 2 < (236321/167042 : ℝ) := by nlinarith
  linarith

/-- The source's universal equality fails for a CPTP qubit map. -/
theorem result : ¬ claim := by
  intro h
  have he := h channel channel_cptp
  have hl := power_lower
  have hu := restricted_power_upper
  have hg := strict_comparison
  rw [he] at hl
  linarith

end D5.S3.QuantumChannels.DequantumnessPowerStrictGap
