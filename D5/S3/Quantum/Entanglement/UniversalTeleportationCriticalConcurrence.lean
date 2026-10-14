/- GID: D5/S3/Quantum/Entanglement/UniversalTeleportationCriticalConcurrence
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/UniversalTeleportationCriticalConcurrence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The exact critical concurrence for universal teleportation through qubit channels. -/

import D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
import D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness
import D5.S3.Quantum.Information.ActualPureQubitCostInfimum
import D5.S3.Quantum.Information.ActualQubitChordObstruction
import D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
import D5.S3.Weil.ZetaLinear.RankTrace
import D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Kronecker ComplexOrder
open D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
  (pauli blochA blochB corr vlen blochVec blochVec_eq_bloch vlen_eq_norm
    trace_mul_kron_one trace_mul_one_kron kron_sub vlen_e3)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness (spin sigma)
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum
  (bloch blochMatrix matrix_energy bloch_geometry_of_isHermitian)
open D5.S3.QuantumBounds.CHSHWitness renaming TwoQubitMatrix → TwoQubit
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (Pauli pauliMatrix)
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ)
open D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
  (pauli_hermitian letter_mul)

namespace D5.S3.Quantum.Entanglement.UniversalTeleportationCriticalConcurrence

def psi (a : ℝ) (p : Fin 2 × Fin 2) : ℂ :=
  if p = (0, 0) then (Real.sqrt a : ℂ)
  else if p = (1, 1) then (Real.sqrt (1 - a) : ℂ) else 0
def initial (a : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.vecMulVec (psi a) (star (psi a))
def IsChannel {m : ℕ} (K : Fin m → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∑ k, (K k)ᴴ * K k = 1
def NonUnital {m : ℕ} (K : Fin m → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∑ k, K k * (K k)ᴴ ≠ 1
def out {m : ℕ} (a : ℝ) (K : Fin m → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ∑ k, ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K k) * initial a *
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K k)ᴴ
def UsefulUQT (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : Prop :=
  ∃ (U V : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ),
    U ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ V ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
    (1 / 3 : ℝ) < t ∧
    corr ((U ⊗ₖ V) * ρ * (U ⊗ₖ V)ᴴ) = fun i j => if i = j then -t else 0
def Cstar : ℝ := Real.sqrt (5 - 2 * Real.sqrt 3) / 3
def conc (a : ℝ) : ℝ := 2 * Real.sqrt (a * (1 - a))
def claim : Prop :=
  ∀ a : ℝ, (1 / 2 : ℝ) < a → a < 1 →
    (∀ (m : ℕ) (K : Fin m → Matrix (Fin 2) (Fin 2) ℂ),
      IsChannel K → UsefulUQT (out a K) → Cstar < conc a) ∧
    (Cstar < conc a → ∃ (m : ℕ) (K : Fin m → Matrix (Fin 2) (Fin 2) ℂ),
      IsChannel K ∧ NonUnital K ∧ UsefulUQT (out a K))

private def rcrit : ℝ := (1 + Real.sqrt 3) / 3
private def tmax (r : ℝ) : ℝ :=
  (1 - r + Real.sqrt ((1 - r) * (1 + 3 * r))) / 2

private lemma critical_constants :
    2 / 3 < rcrit ∧ rcrit < 1 ∧ 0 ≤ Cstar ∧
      Cstar ^ 2 + rcrit ^ 2 = 1 ∧ rcrit ^ 2 - 2 / 3 * rcrit - 2 / 9 = 0 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  have hlow : 1 < Real.sqrt 3 := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 3)
  have hhigh : Real.sqrt 3 < 2 := (Real.sqrt_lt
    (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (0 : ℝ) ≤ 2)).mpr (by norm_num)
  have hc := Real.sq_sqrt (show 0 ≤ 5 - 2 * Real.sqrt 3 by linarith)
  dsimp [rcrit, Cstar]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · positivity
  constructor <;> nlinarith

private lemma eliminate_beta (r t β : ℝ) (hr : 0 ≤ r) (ht : 0 < t)
    (hcorner : r + β ≤ 1 - t)
    (hminor : (r - β) ^ 2 ≤ (1 - t) * (1 + 3 * t)) :
    r ^ 2 + r * t + t ^ 2 ≤ r + t := by
  have ht1 : t ≤ 1 := by nlinarith [sq_nonneg (r - β)]
  by_cases hsign : 0 ≤ 2 * r + t - 1
  · have hz : 2 * r + t - 1 ≤ r - β := by linarith
    have hp := mul_nonneg (show 0 ≤ r - β - (2 * r + t - 1) by linarith)
      (show 0 ≤ r - β + (2 * r + t - 1) by linarith)
    nlinarith
  · have hp := mul_nonpos_of_nonneg_of_nonpos hr (show r + t - 1 ≤ 0 by linarith)
    have hq := mul_nonpos_of_nonneg_of_nonpos ht.le (sub_nonpos.mpr ht1)
    nlinarith

private lemma r_lt_critical (r t : ℝ) (ht : (1 / 3 : ℝ) < t)
    (hb : r ^ 2 + r * t + t ^ 2 ≤ r + t) : r < rcrit := by
  obtain ⟨hR, _, _, _, he⟩ := critical_constants
  by_contra hn
  have hr : rcrit ≤ r := le_of_not_gt hn
  have hp := mul_nonneg (sub_nonneg.mpr hr) (show 0 ≤ r + rcrit + t - 1 by linarith)
  have hq := mul_pos (show 0 < t - 1 / 3 by linarith)
    (show 0 < rcrit + t - 2 / 3 by linarith)
  nlinarith

private lemma concurrence_threshold (a : ℝ) (ha : (1 / 2 : ℝ) < a) (ha1 : a < 1) :
    Cstar < conc a ↔ 2 * a - 1 < rcrit := by
  obtain ⟨hR, _, hC, he, _⟩ := critical_constants
  have hs := Real.sq_sqrt (show 0 ≤ a * (1 - a) by positivity)
  have hn := Real.sqrt_nonneg (a * (1 - a))
  have hsq : (conc a) ^ 2 + (2 * a - 1) ^ 2 = 1 := by dsimp [conc]; nlinarith
  have hc0 : 0 ≤ conc a := by dsimp [conc]; positivity
  constructor <;> intro h <;> nlinarith

private lemma tmax_properties (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (hrc : r < rcrit) :
    (1 / 3 : ℝ) < tmax r ∧ tmax r < 1 ∧
      (tmax r) ^ 2 = (1 - r) * (tmax r + r) := by
  have hs := Real.sq_sqrt (show 0 ≤ (1 - r) * (1 + 3 * r) by positivity)
  have hn := Real.sqrt_nonneg ((1 - r) * (1 + 3 * r))
  have ht : 0 < tmax r := by dsimp [tmax]; linarith
  have he : (tmax r) ^ 2 = (1 - r) * (tmax r + r) := by dsimp [tmax]; nlinarith
  have ht1 : tmax r < 1 := by
    by_contra h
    have hp := mul_nonneg (show 0 ≤ tmax r - 1 by linarith)
      (show 0 ≤ r + tmax r by linarith)
    nlinarith
  have hrt : 0 < r + tmax r - 1 := by
    have hp := mul_pos hr (show 0 < 1 - r by linarith)
    nlinarith
  obtain ⟨hR, _, _, _, hRe⟩ := critical_constants
  have hp := mul_neg_of_neg_of_pos (show r - rcrit < 0 by linarith)
    (show 0 < r + rcrit - 2 / 3 by linarith)
  have hthird : (1 / 3 : ℝ) < tmax r := by
    by_contra h
    have hq := mul_nonneg (show 0 ≤ 1 / 3 - tmax r by linarith)
      (show 0 ≤ r + 1 / 3 + tmax r - 1 by linarith)
    nlinarith
  exact ⟨hthird, ht1, he⟩

private def damping (γ : ℝ) : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![(Real.sqrt (1 - γ) : ℂ), 0; 0, 1], !![0, 0; (Real.sqrt γ : ℂ), 0]]

private lemma damping_channel (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    IsChannel (damping γ) := by
  have hs0 := Real.sq_sqrt hγ0
  have hs1 := Real.sq_sqrt (sub_nonneg.mpr hγ1)
  rw [IsChannel.eq_def]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp only [damping.eq_def, Fin.sum_univ_two, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.of_apply,
      Matrix.one_apply, map_zero, map_one, Complex.star_def, Complex.conj_ofReal, mul_zero, zero_mul,
      add_zero, zero_add, mul_one, one_mul, ← Complex.ofReal_mul, Complex.ofReal_re,
      Complex.ofReal_im, ← sq, hs0, hs1]
  all_goals norm_num [← Complex.ofReal_pow, hs0, hs1]
  all_goals nlinarith only [hs0, hs1]

private lemma damping_nonunital (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    NonUnital (damping γ) := by
  have hs := Real.sq_sqrt (sub_nonneg.mpr hγ1)
  rw [NonUnital.eq_def]
  intro h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 0).re) h
  simp only [damping.eq_def, Fin.sum_univ_two, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.of_apply, Matrix.one_apply, map_zero, map_one,
    Complex.star_def, Complex.conj_ofReal, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul,
    ← Complex.ofReal_mul, Complex.ofReal_re, Complex.add_re, ← sq, hs] at he
  norm_num [← Complex.ofReal_pow, hs] at he
  linarith

set_option maxHeartbeats 2000000 in
private lemma damping_useful (a t γ : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (ht : (1 / 3 : ℝ) < t)
    (hzz : 1 - 2 * a * γ = t) (hxy : 4 * a * (1 - a) * (1 - γ) = t ^ 2) :
    UsefulUQT (out a (damping γ)) := by
  have hs0 := Real.sq_sqrt ha0
  have hs1 := Real.sq_sqrt (sub_nonneg.mpr ha1)
  have hsγ := Real.sq_sqrt (sub_nonneg.mpr hγ1)
  have hsγ0 := Real.sq_sqrt hγ0
  have hcross : 2 * Real.sqrt a * Real.sqrt (1 - a) * Real.sqrt (1 - γ) = t := by
    have hnon : 0 ≤ 2 * Real.sqrt a * Real.sqrt (1 - a) * Real.sqrt (1 - γ) := by
      positivity
    have hs : (2 * Real.sqrt a * Real.sqrt (1 - a) * Real.sqrt (1 - γ)) ^ 2 = t ^ 2 := by
      calc
        _ = 4 * (Real.sqrt a) ^ 2 * (Real.sqrt (1 - a)) ^ 2 *
            (Real.sqrt (1 - γ)) ^ 2 := by ring
        _ = _ := by rw [hs0, hs1, hsγ]; exact hxy
    nlinarith
  ring_nf at hcross
  rw [UsefulUQT.eq_def]
  refine ⟨1, pauli 1, t, (Matrix.unitaryGroup (Fin 2) ℂ).one_mem, ?_, ht, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    change (pauliMatrix Pauli.Y)ᴴ * pauliMatrix Pauli.Y = 1
    rw [pauli_hermitian, letter_mul]
    simp [D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.letterPhase,
      D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.letterProduct,
      pauliMatrix]
  · funext i j
    fin_cases i <;> fin_cases j <;>
      simp only [corr.eq_def, out.eq_def, initial.eq_def, psi.eq_def, damping.eq_def,
        pauli.eq_def, pauliMatrix, qubitX, qubitZ, Matrix.trace, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        Matrix.vecMulVec_apply, Pi.star_apply, Complex.mul_re, Complex.mul_im, ← sq, hs0, hs1, hsγ,
        Matrix.kronecker_apply, Matrix.sum_apply, Matrix.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Matrix.of_apply, Matrix.one_apply, Matrix.diag_apply, Complex.star_def, Complex.conj_ofReal] <;>
      norm_num [Complex.mul_re, Complex.mul_im, ← sq, hs0, hs1, hsγ] <;>
      ring_nf <;>
      norm_num [← Complex.ofReal_pow, hs0, hs1, hsγ, hsγ0] <;>
      nlinarith only [hcross, hzz]

private lemma sufficient_two (a : ℝ) (ha : (1 / 2 : ℝ) < a) (ha1 : a < 1)
    (hC : Cstar < conc a) :
    ∃ K : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ,
      IsChannel K ∧ NonUnital K ∧ UsefulUQT (out a K) := by
  let r := 2 * a - 1
  let t := tmax r
  let γ := (1 - t) / (1 + r)
  have hr : 0 < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  obtain ⟨ht, ht1, he⟩ := tmax_properties r hr hr1 ((concurrence_threshold a ha ha1).mp hC)
  have hγ0 : 0 < γ := div_pos (sub_pos.mpr ht1) (by linarith)
  have hγ1 : γ < 1 := by
    apply (div_lt_one (show 0 < 1 + r by linarith)).mpr
    linarith
  have hzz : 1 - 2 * a * γ = t := by
    dsimp [γ]
    field_simp
    dsimp [r]
    ring
  have hxy : 4 * a * (1 - a) * (1 - γ) = t ^ 2 := by
    dsimp [γ]
    change 4 * a * (1 - a) * (1 - (1 - t) / (1 + r)) = (tmax r) ^ 2
    rw [he]
    field_simp
    dsimp [r]
    ring
  exact ⟨damping γ, damping_channel γ hγ0.le hγ1.le,
    damping_nonunital γ hγ0 hγ1.le,
    damping_useful a t γ (by linarith) ha1.le hγ0.le hγ1.le ht hzz hxy⟩

end D5.S3.Quantum.Entanglement.UniversalTeleportationCriticalConcurrence
