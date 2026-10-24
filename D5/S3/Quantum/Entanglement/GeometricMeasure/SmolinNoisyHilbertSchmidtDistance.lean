/- GID: D5/S3/Quantum/Entanglement/GeometricMeasure/SmolinNoisyHilbertSchmidtDistance
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/GeometricMeasure/SmolinNoisyHilbertSchmidtDistance
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Exact Hilbert–Schmidt distances of noisy Smolin states for four partitions. -/

import D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness
import D5.S3.QuantumChannels.ChannelTimeReversalNoGo
import D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence
import D5.S3.Quantum.Information.SLDSpectralEnergy
import D5.S3.Quantum.QuantumChannels.PositiveFilterTransposeRefutation
import D5.S3.Quantum.Information.EntanglementDistanceBellDiagonalRefutation
import D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
import D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness (sigma sigma_properties)
open D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence (IsSeparable)
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)

namespace D5.S3.Quantum.Entanglement.GeometricMeasure.SmolinNoisyHilbertSchmidtDistance

abbrev Q := Fin 2 × Fin 2 × Fin 2 × Fin 2

private def four (j : Fin 4) : Matrix Q Q ℂ :=
  sigma j ⊗ₖ (sigma j ⊗ₖ (sigma j ⊗ₖ sigma j))

private def S : Matrix Q Q ℂ := four 1 + four 2 + four 3

def smolin : Matrix Q Q ℂ := (1 / 16 : ℂ) • (1 + S)

def noisy (p : ℝ) : Matrix Q Q ℂ :=
  p • smolin + (1 - p) • ((1 / 16 : ℂ) • 1)

def SepOneOneTwo : Set (Matrix Q Q ℂ) :=
  convexHull ℝ {ρ | ∃ (a b : Matrix (Fin 2) (Fin 2) ℂ)
    (c : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ),
    IsDensity a ∧ IsDensity b ∧ IsDensity c ∧ ρ = a ⊗ₖ (b ⊗ₖ c)}

def SepFull : Set (Matrix Q Q ℂ) :=
  convexHull ℝ {ρ | ∃ (a b c d : Matrix (Fin 2) (Fin 2) ℂ),
    IsDensity a ∧ IsDensity b ∧ IsDensity c ∧ IsDensity d ∧
      ρ = a ⊗ₖ (b ⊗ₖ (c ⊗ₖ d))}

def SepTwoTwo : Set (Matrix Q Q ℂ) :=
  {ρ | IsSeparable (ρ.submatrix (Equiv.prodAssoc (Fin 2) (Fin 2) (Fin 2 × Fin 2))
    (Equiv.prodAssoc (Fin 2) (Fin 2) (Fin 2 × Fin 2)))}

def hsDist (X Y : Matrix Q Q ℂ) : ℝ :=
  Real.sqrt (Matrix.trace ((X - Y)ᴴ * (X - Y))).re

def f (p : ℝ) : ℝ :=
  if p ≤ 1 / 3 then 0 else Real.sqrt 3 / 4 * (p - 1 / 3)

def claim : Prop := ∀ p ∈ Set.Icc (0 : ℝ) 1,
  IsLeast {d | ∃ σ, IsSeparable σ ∧ d = hsDist (noisy p) σ} (f p) ∧
  IsLeast {d | ∃ σ ∈ SepOneOneTwo, d = hsDist (noisy p) σ} (f p) ∧
  IsLeast {d | ∃ σ ∈ SepFull, d = hsDist (noisy p) σ} (f p) ∧
  IsLeast {d | ∃ σ ∈ SepTwoTwo, d = hsDist (noisy p) σ} 0

private theorem hsDist_self (X : Matrix Q Q ℂ) : hsDist X X = 0 := by
  simpa only [hsDist, sub_self, Matrix.conjTranspose_zero, zero_mul, Matrix.trace_zero,
    Complex.zero_re] using Real.sqrt_zero

private theorem density_kron {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] {a : Matrix A A ℂ} {b : Matrix B B ℂ}
    (ha : IsDensity a) (hb : IsDensity b) : IsDensity (a ⊗ₖ b) := by
  exact ⟨ha.1.kronecker hb.1, by rw [trace_kronecker, ha.2, hb.2, mul_one]⟩

private theorem sep_product {A B : Type*} [Fintype A] [Fintype B]
    {a : Matrix A A ℂ} {b : Matrix B B ℂ}
    (ha : IsDensity a) (hb : IsDensity b) : IsSeparable (a ⊗ₖ b) := by
  refine ⟨1, fun _ => 1, fun _ => a, fun _ => b, by simp, by simp, ?_, ?_⟩
  · intro t
    exact ⟨ha, hb⟩
  · simp

private theorem sep_convex {A B : Type*} [Fintype A] [Fintype B] :
    Convex ℝ {ρ : Matrix (A × B) (A × B) ℂ | IsSeparable ρ} := by
  intro ρ hρ η hη u v hu hv huv
  obtain ⟨n, p, a, b, hp, hsum, hd, rfl⟩ := hρ
  obtain ⟨m, q, c, d, hq, hsum', hd', rfl⟩ := hη
  refine ⟨n + m, Fin.addCases (fun i => u * p i) (fun j => v * q j),
    Fin.addCases a c, Fin.addCases b d, ?_, ?_, ?_, ?_⟩
  · intro t
    refine Fin.addCases (fun i => ?_) (fun j => ?_) t
    · simpa using mul_nonneg hu (hp i)
    · simpa using mul_nonneg hv (hq j)
  · simp only [Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      ← Finset.mul_sum, hsum, hsum', mul_one]
    exact huv
  · intro t
    refine Fin.addCases (fun i => ?_) (fun j => ?_) t
    · simpa using hd i
    · simpa using hd' j
  · simp only [Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      Complex.ofReal_mul, mul_smul, ← Finset.smul_sum]
    rfl

private theorem full_subset_oneOneTwo : SepFull ⊆ SepOneOneTwo := by
  apply convexHull_mono
  rintro ρ ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩
  exact ⟨a, b, c ⊗ₖ d, ha, hb, density_kron hc hd, rfl⟩

private theorem oneOneTwo_subset_oneThree :
    SepOneOneTwo ⊆ (IsSeparable : Set (Matrix Q Q ℂ)) := by
  apply convexHull_min _ sep_convex
  rintro ρ ⟨a, b, c, ha, hb, hc, rfl⟩
  exact sep_product ha (density_kron hb hc)

private theorem full_subset_twoTwo : SepFull ⊆ SepTwoTwo := by
  have hconv : Convex ℝ SepTwoTwo := by
    intro ρ hρ η hη u v hu hv huv
    exact sep_convex hρ hη hu hv huv
  apply convexHull_min _ hconv
  rintro ρ ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩
  have he : (a ⊗ₖ (b ⊗ₖ (c ⊗ₖ d))).submatrix
      (Equiv.prodAssoc (Fin 2) (Fin 2) (Fin 2 × Fin 2))
      (Equiv.prodAssoc (Fin 2) (Fin 2) (Fin 2 × Fin 2)) =
      (a ⊗ₖ b) ⊗ₖ (c ⊗ₖ d) := by
    ext i j
    simp [Matrix.kroneckerMap_apply, mul_assoc]
  change IsSeparable _
  rw [he]
  exact sep_product (density_kron ha hb) (density_kron hc hd)

private theorem mixed_full : ((1 / 16 : ℂ) • (1 : Matrix Q Q ℂ)) ∈ SepFull := by
  let a : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • 1
  have ha : IsDensity a := by
    refine ⟨Matrix.PosSemidef.one.smul (by norm_num [Complex.nonneg_iff]), ?_⟩
    simp [a]
  apply subset_convexHull ℝ _
  refine ⟨a, a, a, a, ha, ha, ha, ha, ?_⟩
  norm_num [a, Matrix.smul_kronecker, Matrix.kronecker_smul,
    Matrix.one_kronecker_one, smul_smul]

private def axis : Fin 3 →
    D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli :=
  ![.X, .Y, .Z]

private theorem axis_sigma (j : Fin 3) :
    D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix (axis j) =
      sigma j.succ := by
  fin_cases j <;> rfl

private def parityProduct (j : Fin 3) (s : Bool × Bool × Bool) : Matrix Q Q ℂ :=
  let P := D5.S3.Quantum.Magic.WignerDistanceMinimum.spectral (axis j)
  P (if s.1 then 1 else 0) ⊗ₖ (P (if s.2.1 then 1 else 0) ⊗ₖ
    (P (if s.2.2 then 1 else 0) ⊗ₖ
      P (if Bool.xor s.1 (Bool.xor s.2.1 s.2.2) then 1 else 0)))

private def tau (j : Fin 3) : Matrix Q Q ℂ :=
  (1 / 16 : ℂ) • (1 + four j.succ)

private theorem tau_mixture (j : Fin 3) :
    tau j = ∑ s : Bool × Bool × Bool, (1 / 8 : ℝ) • parityProduct j s := by
  simp [tau, parityProduct, Fintype.sum_prod_type, Fintype.sum_bool,
    D5.S3.Quantum.Magic.WignerDistanceMinimum.spectral, axis_sigma,
    RCLike.real_smul_eq_coe_smul (K := ℂ), four,
    Matrix.add_kronecker, Matrix.kronecker_add, Matrix.smul_kronecker,
    Matrix.kronecker_smul, Matrix.one_kronecker_one, smul_smul]
  <;> module

private theorem tau_full (j : Fin 3) : tau j ∈ SepFull := by
  rw [tau_mixture]
  apply (convex_convexHull ℝ _).sum_mem
  · intro s _
    norm_num
  · norm_num
  · intro s _
    apply subset_convexHull ℝ _
    refine ⟨_, _, _, _, ?_, ?_, ?_, ?_, rfl⟩
    · exact ⟨by simpa [axis] using
          D5.S3.QuantumChannels.ChannelTimeReversalNoGo.PauliChannels.density_psd j s.1,
        by simpa [axis] using
          D5.S3.QuantumChannels.ChannelTimeReversalNoGo.PauliChannels.density_trace j s.1⟩
    · exact ⟨by simpa [axis] using
          D5.S3.QuantumChannels.ChannelTimeReversalNoGo.PauliChannels.density_psd j s.2.1,
        by simpa [axis] using
          D5.S3.QuantumChannels.ChannelTimeReversalNoGo.PauliChannels.density_trace j s.2.1⟩
    · exact ⟨by simpa [axis] using
          D5.S3.QuantumChannels.ChannelTimeReversalNoGo.PauliChannels.density_psd j s.2.2,
        by simpa [axis] using
          D5.S3.QuantumChannels.ChannelTimeReversalNoGo.PauliChannels.density_trace j s.2.2⟩
    · let e := Bool.xor s.1 (Bool.xor s.2.1 s.2.2)
      exact ⟨by simpa [axis, e] using
          D5.S3.QuantumChannels.ChannelTimeReversalNoGo.PauliChannels.density_psd j e,
        by simpa [axis, e] using
          D5.S3.QuantumChannels.ChannelTimeReversalNoGo.PauliChannels.density_trace j e⟩

private theorem boundary_full : noisy (1 / 3) ∈ SepFull := by
  have he : noisy (1 / 3) = ∑ j : Fin 3, (1 / 3 : ℝ) • tau j := by
    ext i k
    simp [noisy, smolin, tau, S, Fin.sum_univ_three, Matrix.smul_apply,
      RCLike.real_smul_eq_coe_mul]
    <;> ring
  rw [he]
  exact (convex_convexHull ℝ _).sum_mem (by intros; norm_num) (by norm_num)
    (fun j _ => tau_full j)

private theorem low_full (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1 / 3) :
    noisy p ∈ SepFull := by
  have he : noisy p = (3 * p) • noisy (1 / 3) +
      (1 - 3 * p) • ((1 / 16 : ℂ) • (1 : Matrix Q Q ℂ)) := by
    ext i j
    simp [noisy, Matrix.smul_apply, RCLike.real_smul_eq_coe_mul,
      Complex.ofReal_sub, Complex.ofReal_mul]
    <;> ring
  rw [he]
  exact (convex_convexHull ℝ _ ) boundary_full mixed_full
    (by positivity) (by linarith) (by ring)

private theorem trace_S : Matrix.trace S = 0 := by
  have ht (p : D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli)
      (hp : p ≠ .I) :
      Matrix.trace (D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix p) = 0 := by
    have h := D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.pauli_trace_pair p .I
    simpa only [show
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix .I = 1 from rfl,
      Matrix.mul_one, if_neg hp] using h
  simp only [S, four, Matrix.trace_add, Matrix.trace_kronecker]
  norm_num [sigma, ht .X (by decide), ht .Y (by decide), ht .Z (by decide)]

private theorem trace_S_sq : Matrix.trace (S * S) = 48 := by
  simp only [S, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add, four,
    ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]
  norm_num [sigma,
    D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.pauli_trace_pair]

private theorem trace_S_noisy (p : ℝ) : (Matrix.trace (S * noisy p)).re = 3 * p := by
  simp [noisy, smolin, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add,
    Matrix.trace_smul, trace_S, trace_S_sq, RCLike.real_smul_eq_coe_mul]
  <;> ring

private def triple (j : Fin 3) :
    Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ :=
  sigma j.succ ⊗ₖ (sigma j.succ ⊗ₖ sigma j.succ)

private theorem triple_hermitian (j : Fin 3) : (triple j)ᴴ = triple j := by
  simp only [triple, Matrix.conjTranspose_kronecker, (sigma_properties _).1]

private theorem triple_square (j : Fin 3) : triple j * triple j = 1 := by
  simp only [triple, ← Matrix.mul_kronecker_mul, (sigma_properties _).2,
    Matrix.one_kronecker_one]

private theorem triple_anti (i j : Fin 3) (h : i ≠ j) :
    triple i * triple j = -(triple j * triple i) := by
  have hb : sigma i.succ * sigma j.succ = -(sigma j.succ * sigma i.succ) := by
    rw [← axis_sigma i, ← axis_sigma j]
    have hs : D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.sgn
        (axis i) (axis j) = -1 := by
      fin_cases i <;> fin_cases j <;> simp_all [axis,
        D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.sgn,
        D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.anticomm]
    simpa only [hs, Int.cast_neg, Int.cast_one, neg_one_smul] using
      D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.letter_comm
        (axis i) (axis j)
  simp only [triple, ← Matrix.mul_kronecker_mul, hb]
  ext a b
  simp [Matrix.kroneckerMap_apply]

private theorem triple_sum_square (t : Fin 3 → ℝ) :
    (∑ j, (t j : ℂ) • triple j) * (∑ j, (t j : ℂ) • triple j) =
      ((∑ j, t j ^ 2 : ℝ) : ℂ) • 1 := by
  simp only [Fin.sum_univ_three, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Complex.ofReal_add, Complex.ofReal_pow]
  rw [triple_square 0, triple_square 1, triple_square 2,
    triple_anti 1 0 (by decide), triple_anti 2 0 (by decide),
    triple_anti 2 1 (by decide)]
  module

private theorem witness_product (a : Matrix (Fin 2) (Fin 2) ℂ)
    (b : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
    (ha : IsDensity a) (hb : IsDensity b) :
    (Matrix.trace (S * (a ⊗ₖ b))).re ≤ 1 := by
  let t : Fin 3 → ℝ := fun j => (triple j * b).trace.re
  let T := ∑ j, (t j : ℂ) • triple j
  let q := ∑ j, t j ^ 2
  have hT : Tᴴ = T := by
    simp only [T, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
      Complex.star_def, Complex.conj_ofReal, triple_hermitian]
  have hsq : T * T = (q : ℂ) • 1 := triple_sum_square t
  have hmean : (T * b).trace.re = q := by
    simp [T, q, t, Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum,
      Matrix.trace_smul, Complex.mul_re, pow_two]
  have hp := (Matrix.posSemidef_conjTranspose_mul_self (T - 1)).trace_mul_nonneg hb.1
  have hpR := (Complex.nonneg_iff.mp hp).1
  have he : (T - 1)ᴴ * (T - 1) * b = T * T * b - T * b - T * b + b := by
    rw [Matrix.conjTranspose_sub, hT, Matrix.conjTranspose_one]
    noncomm_ring
  rw [he] at hpR
  simp only [Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re,
    hsq, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, hb.2, smul_eq_mul,
    mul_one, Complex.ofReal_re, Complex.one_re, hmean] at hpR
  have htq : q ≤ 1 := by linarith
  have hqn : 0 ≤ q := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  let r := D5.S3.Quantum.Information.ActualPureQubitCostInfimum.bloch a
  have hn := D5.S3.Quantum.Information.ActualPureQubitCostInfimum.norm_bloch_le_trace_of_posSemidef
    a ha.1
  rw [ha.2, Complex.one_re] at hn
  have hrq : ∑ j, r j ^ 2 ≤ 1 := by
    have hn2 := (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mpr hn
    simpa only [EuclideanSpace.real_norm_sq_eq, one_pow] using hn2
  have haeq : a = D5.S3.Quantum.Information.ActualPureQubitCostInfimum.blochMatrix 1 r := by
    simpa only [ha.2, Complex.one_re] using
      (D5.S3.Quantum.Information.ActualPureQubitCostInfimum.bloch_geometry_of_isHermitian
        a ha.1.isHermitian).1
  have hpa (j : Fin 3) : (sigma j.succ * a).trace = (r j : ℂ) := by
    rw [haeq]
    fin_cases j <;> apply Complex.ext
    all_goals simp [sigma,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix,
      D5.S3.Quantum.FiniteDimensional.qubitX, D5.S3.Quantum.FiniteDimensional.qubitZ,
      D5.S3.Quantum.Information.ActualPureQubitCostInfimum.blochMatrix,
      Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im]
    all_goals ring
  have hexp : S = ∑ j : Fin 3, sigma j.succ ⊗ₖ triple j := by
    simp [S, four, triple, Fin.sum_univ_three]
  rw [hexp]
  simp only [Matrix.sum_mul, ← Matrix.mul_kronecker_mul, Matrix.trace_sum,
    Matrix.trace_kronecker, hpa, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  change (∑ j, r j * t j) ≤ 1
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => r j) t
  have hprod := mul_le_mul_of_nonneg_right hrq hqn
  change (∑ j, r j ^ 2) * q ≤ 1 * q at hprod
  change (∑ j, r j * t j) ^ 2 ≤ (∑ j, r j ^ 2) * q at hc
  nlinarith


private theorem witness_separable (σ : Matrix Q Q ℂ) (hσ : IsSeparable σ) :
    (Matrix.trace (S * σ)).re ≤ 1 := by
  obtain ⟨n, p, a, b, hp, hsum, hd, he⟩ := hσ
  rw [he]
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    Complex.re_sum, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  calc
    _ ≤ ∑ i, p i * 1 := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (witness_product (a i) (b i) (hd i).1 (hd i).2) (hp i)
    _ = 1 := by simpa using hsum


private theorem S_hermitian : Sᴴ = S := by
  simp only [S, four, Matrix.conjTranspose_add, Matrix.conjTranspose_kronecker,
    (sigma_properties _).1]

private theorem witness_cauchy (X : Matrix Q Q ℂ) :
    (Matrix.trace (S * X)).re ≤ Real.sqrt 48 * hsDist X 0 := by
  simp only [hsDist, sub_zero]
  let e := (Fintype.equivFin Q).symm
  have ht (M : Matrix Q Q ℂ) : (M.submatrix e e).trace = M.trace :=
    e.sum_comp (fun i => M i i)
  have hc := D5.S3.Quantum.Matrix.CartesianVariance.trace_product_cauchy
    (S.submatrix e e) (X.submatrix e e)
  simp only [RHLinalg.frobSq, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    ht, S_hermitian, trace_S_sq, RCLike.re_eq_complex_re] at hc
  simp only [Complex.re_ofNat] at hc
  have hn : 0 ≤ (Xᴴ * X).trace.re :=
    (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self X).trace_nonneg).1
  have hx := Real.sq_sqrt hn
  have h48 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 48)
  have hpos : 0 ≤ Real.sqrt 48 * Real.sqrt (Xᴴ * X).trace.re := by positivity
  simp only [Complex.normSq_apply] at hc
  change (S * X).trace.re ≤ Real.sqrt 48 * Real.sqrt (Xᴴ * X).trace.re
  have hmul : (Real.sqrt 48 * Real.sqrt (Xᴴ * X).trace.re) ^ 2 =
      48 * (Xᴴ * X).trace.re := by rw [mul_pow, h48, hx]
  have hreal : (S * X).trace.re ^ 2 ≤ 48 * (Xᴴ * X).trace.re := by
    nlinarith only [hc, sq_nonneg (S * X).trace.im]
  have hab : |(S * X).trace.re| ≤ Real.sqrt 48 * Real.sqrt (Xᴴ * X).trace.re :=
    (sq_le_sq₀ (abs_nonneg _) hpos).mp (by simpa only [sq_abs, hmul] using hreal)
  exact (le_abs_self _).trans hab


private theorem distance_lower (p : ℝ) (σ : Matrix Q Q ℂ)
    (hσ : IsSeparable σ) : f p ≤ hsDist (noisy p) σ := by
  by_cases hp : p ≤ 1 / 3
  · simp only [f, if_pos hp]
    exact Real.sqrt_nonneg _
  · have hw := witness_separable σ hσ
    have hc := witness_cauchy (noisy p - σ)
    have hdist : hsDist (noisy p - σ) 0 = hsDist (noisy p) σ := by
      simp [hsDist]
    rw [hdist] at hc
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, trace_S_noisy] at hc
    have hd : 0 ≤ hsDist (noisy p) σ := Real.sqrt_nonneg _
    have hs : Real.sqrt 48 = 4 * Real.sqrt 3 := by
      rw [show (48 : ℝ) = 16 * 3 by norm_num, Real.sqrt_mul (by norm_num)]
      norm_num
    have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hpos := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)
    rw [hs] at hc
    change 3 * p - (S * σ).trace.re ≤ 4 * Real.sqrt 3 * hsDist (noisy p) σ at hc
    simp only [f, if_neg hp]
    have hl : 3 * p - 1 ≤ 4 * Real.sqrt 3 * hsDist (noisy p) σ := by linarith
    have hm := mul_le_mul_of_nonneg_left hl (le_of_lt hpos)
    have h3d := congrArg (fun x : ℝ => x * hsDist (noisy p) σ) h3
    nlinarith

private theorem boundary_distance (p : ℝ) :
    hsDist (noisy p) (noisy (1 / 3)) = Real.sqrt 3 / 4 * |p - 1 / 3| := by
  have he : noisy p - noisy (1 / 3) = ((p - 1 / 3) / 16) • S := by
    ext i j
    simp [noisy, smolin, Matrix.smul_apply, RCLike.real_smul_eq_coe_mul,
      Complex.ofReal_sub, Complex.ofReal_div]
    <;> ring
  unfold hsDist
  rw [he]
  simp only [Matrix.conjTranspose_smul, conj_trivial, S_hermitian, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Matrix.trace_smul, trace_S_sq]
  simp only [star_trivial, RCLike.real_smul_eq_coe_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat,
    Complex.im_ofNat, mul_zero, sub_zero]
  change Real.sqrt (((p - 1 / 3) / 16) * ((p - 1 / 3) / 16) * 48) = _
  rw [show ((p - 1 / 3) / 16) * ((p - 1 / 3) / 16) * 48 =
      ((p - 1 / 3) / 4) ^ 2 * 3 by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_div]
  norm_num
  ring


private def bellSigns : Fin 4 → Fin 3 → ℂ :=
  ![![1, -1, 1], ![-1, 1, 1], ![1, 1, -1], ![-1, -1, -1]]

private theorem bell_pauli (μ : Fin 4) :
    D5.S3.Quantum.Information.EntanglementDistanceBellDiagonalRefutation.bellProjector μ =
      (1 / 4 : ℂ) • (1 +
        bellSigns μ 0 • (sigma 1 ⊗ₖ sigma 1) +
        bellSigns μ 1 • (sigma 2 ⊗ₖ sigma 2) +
        bellSigns μ 2 • (sigma 3 ⊗ₖ sigma 3)) := by
  fin_cases μ
  all_goals ext ⟨a, b⟩ ⟨c, d⟩
  all_goals fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  all_goals norm_num [
    D5.S3.Quantum.Information.EntanglementDistanceBellDiagonalRefutation.bellProjector,
    D5.S3.QuantumBounds.CHSHWitness.bellDensity,
    D5.S3.QuantumBounds.CHSHWitness.bellVector, Matrix.vecMulVec_apply, Pi.star_apply,
    D5.S3.Quantum.QubitWitnesses.bellCoefficients,
    D5.S3.QuantumBounds.CHSHWitness.complex_sqrt_two_inv_mul_self,
    bellSigns, sigma,
    D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix,
    D5.S3.Quantum.FiniteDimensional.qubitX, D5.S3.Quantum.FiniteDimensional.qubitZ,
    Matrix.kroneckerMap_apply, Matrix.mul_apply, Fin.sum_univ_two]

set_option maxHeartbeats 1000000 in
private theorem bell_density (μ : Fin 4) : IsDensity
    (D5.S3.Quantum.Information.EntanglementDistanceBellDiagonalRefutation.bellProjector μ) := by
  let U := sigma (![0, 3, 1, 2] μ) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
  have he : D5.S3.Quantum.Information.EntanglementDistanceBellDiagonalRefutation.bellProjector μ =
      U * D5.S3.QuantumBounds.CHSHWitness.bellDensity * Uᴴ := by
    fin_cases μ
    all_goals ext ⟨a, b⟩ ⟨c, d⟩
    all_goals fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
    all_goals norm_num [U,
      D5.S3.Quantum.Information.EntanglementDistanceBellDiagonalRefutation.bellProjector,
      D5.S3.QuantumBounds.CHSHWitness.bellDensity,
      D5.S3.QuantumBounds.CHSHWitness.bellVector, Matrix.vecMulVec_apply, Pi.star_apply,
      D5.S3.Quantum.QubitWitnesses.bellCoefficients,
      D5.S3.QuantumBounds.CHSHWitness.complex_sqrt_two_inv_mul_self,
      sigma, D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix,
      D5.S3.Quantum.FiniteDimensional.qubitX, D5.S3.Quantum.FiniteDimensional.qubitZ,
      Matrix.kroneckerMap_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.conjTranspose_apply]
    all_goals apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im]
  rw [he]
  have hB := D5.S3.QuantumBounds.CHSHWitness.bell_density_is_state
  have hU : Uᴴ * U = 1 := by
    simp only [U, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      (sigma_properties _).1, ← Matrix.mul_kronecker_mul,
      (sigma_properties _).2, Matrix.one_mul, Matrix.one_kronecker_one]
  refine ⟨hB.1.mul_mul_conjTranspose_same U, ?_⟩
  rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul, hB.2]

private theorem smolin_bell : smolin.submatrix
    (Equiv.prodAssoc (Fin 2) (Fin 2) (Fin 2 × Fin 2))
    (Equiv.prodAssoc (Fin 2) (Fin 2) (Fin 2 × Fin 2)) =
      ∑ μ : Fin 4, (1 / 4 : ℂ) •
        (D5.S3.Quantum.Information.EntanglementDistanceBellDiagonalRefutation.bellProjector μ ⊗ₖ
         D5.S3.Quantum.Information.EntanglementDistanceBellDiagonalRefutation.bellProjector μ) := by
  have hf (j : Fin 4) : (four j).submatrix
      (Equiv.prodAssoc (Fin 2) (Fin 2) (Fin 2 × Fin 2))
      (Equiv.prodAssoc (Fin 2) (Fin 2) (Fin 2 × Fin 2)) =
        (sigma j ⊗ₖ sigma j) ⊗ₖ (sigma j ⊗ₖ sigma j) := by
    ext i k
    simp [four, Matrix.kroneckerMap_apply, mul_assoc]
  simp only [smolin, S, Matrix.submatrix_smul, Matrix.submatrix_add,
    Matrix.submatrix_one_equiv, hf, Fin.sum_univ_four, bell_pauli]
  norm_num [bellSigns]
  have hnL (a b : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
      (-a) ⊗ₖ b = -(a ⊗ₖ b) := by ext i k; simp [Matrix.kroneckerMap_apply]
  have hnR (a b : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
      a ⊗ₖ (-b) = -(a ⊗ₖ b) := by ext i k; simp [Matrix.kroneckerMap_apply]
  simp only [Matrix.add_kronecker, Matrix.kronecker_add, Matrix.smul_kronecker,
    Matrix.kronecker_smul, Matrix.one_kronecker_one, smul_smul, hf, hnL, hnR, neg_neg]
  module

private theorem smolin_twoTwo : smolin ∈ SepTwoTwo := by
  refine ⟨4, fun _ => 1 / 4,
    D5.S3.Quantum.Information.EntanglementDistanceBellDiagonalRefutation.bellProjector,
    D5.S3.Quantum.Information.EntanglementDistanceBellDiagonalRefutation.bellProjector,
    by norm_num, by norm_num, fun μ => ⟨bell_density μ, bell_density μ⟩, ?_⟩
  simpa using smolin_bell

private theorem noisy_twoTwo (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    noisy p ∈ SepTwoTwo := by
  exact sep_convex smolin_twoTwo (full_subset_twoTwo mixed_full) hp.1
    (sub_nonneg.mpr hp.2) (by ring)

private theorem least_refinement (K : Set (Matrix Q Q ℂ))
    (hFK : SepFull ⊆ K) (hK : K ⊆ (IsSeparable : Set (Matrix Q Q ℂ)))
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    IsLeast {d | ∃ σ ∈ K, d = hsDist (noisy p) σ} (f p) := by
  constructor
  · by_cases h : p ≤ 1 / 3
    · refine ⟨noisy p, hFK (low_full p hp.1 h), ?_⟩
      rw [f, if_pos h, hsDist_self]
    · refine ⟨noisy (1 / 3), hFK boundary_full, ?_⟩
      rw [f, if_neg h, boundary_distance, abs_of_pos (by linarith)]
  · rintro d ⟨σ, hσ, rfl⟩
    exact distance_lower p σ (hK hσ)

theorem result : claim := by
  intro p hp
  have hF : SepFull ⊆ (IsSeparable : Set (Matrix Q Q ℂ)) :=
    full_subset_oneOneTwo.trans oneOneTwo_subset_oneThree
  refine ⟨least_refinement IsSeparable hF (fun _ h => h) p hp,
    least_refinement SepOneOneTwo full_subset_oneOneTwo oneOneTwo_subset_oneThree p hp,
    least_refinement SepFull (fun _ h => h) hF p hp, ?_⟩
  constructor
  · exact ⟨noisy p, noisy_twoTwo p hp, (hsDist_self _).symm⟩
  · rintro d ⟨σ, _, rfl⟩
    exact Real.sqrt_nonneg _

end D5.S3.Quantum.Entanglement.GeometricMeasure.SmolinNoisyHilbertSchmidtDistance
