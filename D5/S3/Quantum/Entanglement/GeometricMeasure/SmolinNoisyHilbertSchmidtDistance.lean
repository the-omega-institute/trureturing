/- GID: D5/S3/Quantum/Entanglement/GeometricMeasure/SmolinNoisyHilbertSchmidtDistance
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/GeometricMeasure/SmolinNoisyHilbertSchmidtDistance
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Exact Hilbert–Schmidt distances of noisy Smolin states for four partitions. -/

import D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness
import D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence
import D5.S3.Quantum.Information.SLDSpectralEnergy
import D5.S3.Quantum.Matrix.CartesianVariance
import D5.S3.Quantum.QuantumChannels.PositiveFilterTransposeRefutation
import D5.S3.Quantum.Magic.WignerDistanceMinimum
import D5.S3.Quantum.Information.EntanglementDistanceBellDiagonalRefutation

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

def SepOneThree : Set (Matrix Q Q ℂ) := {ρ | IsSeparable ρ}

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
  IsLeast {d | ∃ σ ∈ SepOneThree, d = hsDist (noisy p) σ} (f p) ∧
  IsLeast {d | ∃ σ ∈ SepOneOneTwo, d = hsDist (noisy p) σ} (f p) ∧
  IsLeast {d | ∃ σ ∈ SepFull, d = hsDist (noisy p) σ} (f p) ∧
  IsLeast {d | ∃ σ ∈ SepTwoTwo, d = hsDist (noisy p) σ} 0

private theorem hsDist_nonneg (X Y : Matrix Q Q ℂ) : 0 ≤ hsDist X Y := by
  exact Real.sqrt_nonneg _

private theorem hsDist_self (X : Matrix Q Q ℂ) : hsDist X X = 0 := by
  simp [hsDist]

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

private theorem oneOneTwo_subset_oneThree : SepOneOneTwo ⊆ SepOneThree := by
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

private theorem boundary_full : noisy (1 / 3) ∈ SepFull := by
  sorry

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
  simp only [S, four, Matrix.trace_add, Matrix.trace_kronecker]
  norm_num [sigma, D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix,
    D5.S3.Quantum.FiniteDimensional.qubitX, D5.S3.Quantum.FiniteDimensional.qubitZ,
    Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]

private theorem trace_S_sq : Matrix.trace (S * S) = 48 := by
  simp only [S, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add, four,
    ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]
  norm_num [sigma, D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix,
    D5.S3.Quantum.FiniteDimensional.qubitX, D5.S3.Quantum.FiniteDimensional.qubitZ,
    Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]

private theorem trace_S_noisy (p : ℝ) : (Matrix.trace (S * noisy p)).re = 3 * p := by
  simp [noisy, smolin, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add,
    Matrix.trace_smul, trace_S, trace_S_sq, RCLike.real_smul_eq_coe_mul]
  <;> ring

private theorem witness_product (a : Matrix (Fin 2) (Fin 2) ℂ)
    (b : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
    (ha : IsDensity a) (hb : IsDensity b) :
    (Matrix.trace (S * (a ⊗ₖ b))).re ≤ 1 := by
  sorry

private theorem witness_separable (σ : Matrix Q Q ℂ) (hσ : σ ∈ SepOneThree) :
    (Matrix.trace (S * σ)).re ≤ 1 := by
  sorry

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
    (hσ : σ ∈ SepOneThree) : f p ≤ hsDist (noisy p) σ := by
  by_cases hp : p ≤ 1 / 3
  · simpa only [f, if_pos hp] using hsDist_nonneg (noisy p) σ
  · have hw := witness_separable σ hσ
    have hc := witness_cauchy (noisy p - σ)
    have hdist : hsDist (noisy p - σ) 0 = hsDist (noisy p) σ := by
      simp [hsDist]
    rw [hdist] at hc
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, trace_S_noisy] at hc
    have hd := hsDist_nonneg (noisy p) σ
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


private theorem noisy_twoTwo (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    noisy p ∈ SepTwoTwo := by
  sorry

private theorem least_refinement (K : Set (Matrix Q Q ℂ))
    (hFK : SepFull ⊆ K) (hK : K ⊆ SepOneThree)
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
  have hF : SepFull ⊆ SepOneThree :=
    full_subset_oneOneTwo.trans oneOneTwo_subset_oneThree
  refine ⟨least_refinement SepOneThree hF (fun _ h => h) p hp,
    least_refinement SepOneOneTwo full_subset_oneOneTwo oneOneTwo_subset_oneThree p hp,
    least_refinement SepFull (fun _ h => h) hF p hp, ?_⟩
  constructor
  · exact ⟨noisy p, noisy_twoTwo p hp, (hsDist_self _).symm⟩
  · rintro d ⟨σ, _, rfl⟩
    exact hsDist_nonneg _ _

end D5.S3.Quantum.Entanglement.GeometricMeasure.SmolinNoisyHilbertSchmidtDistance
