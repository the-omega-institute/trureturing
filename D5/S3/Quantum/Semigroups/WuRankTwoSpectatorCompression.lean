/- GID: D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact cold cost and rank-two purity under normalized spectator compression. -/

/-
proof_shape: content
admission_basis: escape-witness
escape_witness: The signed cold overlap yields an exact completed square on the complex cold marginal.
Clipping the diagonal imbalance to the spectral interval gives an attained minimum.
The trace purity identity and complex remainder estimate give the joint bound
on the same square-root matrix.
-/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Matrix.Positivity
import D5.S3.Quantum.Matrix.CartesianVariance
import D5.S3.Quantum.Semigroups.WuTwoModeCliffordPluecker
import Mathlib.Analysis.Matrix.Order

/-!
The spectator compression in Section 2 of
`wu-cubic-unequal-near-diagonal/tracial-spectator-rank-two-proof.txt`.
The occupation index is (spectator, cold), and every trace is ordinary.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Kronecker

namespace D5.S3.Quantum.Semigroups.WuRankTwoSpectatorCompression

open WuCubicOperatorBridge (Frame Mat Occupation)
open WuCubicThermalBasis (e)
open WuTwoModeCliffordPluecker (jump jump_right)
open D5.S3.Quantum.FiniteDimensional (QubitMatrix qubitZ)
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (Pauli pauliMatrix)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceLeft partialTraceLeft_kronecker partialTraceLeft_posSemidef trace_partialTraceLeft)

local notation "Qubit" => QubitMatrix

/-- Include the cold matrix algebra into the two-mode algebra. -/
def liftCold (Q : Qubit) : Mat :=
  (1 : Qubit) ⊗ₖ Q

/-- The normalized spectator partial trace. -/
def coldMarginal (A : Mat) : Qubit :=
  (1 / 2 : ℝ) • partialTraceLeft A

def coldVacuum : Mat := liftCold (e * eᴴ)
def coldOccupied : Mat := liftCold (eᴴ * e)

/-- The cold quadratic form on the actual signed CAR frame. -/
def coldQuadratic (c q K : ℝ) (B : Mat) : ℝ :=
  c * (trace (B * B)).re + q * (trace (B * B * coldVacuum)).re -
    K * (trace (B * jump 0 * B * (jump 0)ᴴ)).re

private theorem pauliZ_adjoint : (pauliMatrix Pauli.Z)ᴴ = qubitZ :=
  D5.S3.Quantum.FiniteDimensional.qubit_weyl_star.2.2.1

private theorem pauliZ_mul_self : qubitZ * qubitZ = 1 := by
  simpa only [pow_two] using D5.S3.Quantum.FiniteDimensional.qubit_weyl_star.2.2.2.2

theorem cold_projectors :
    jump 0 * (jump 0)ᴴ = coldVacuum ∧
    (jump 0)ᴴ * jump 0 = coldOccupied ∧ coldVacuum + coldOccupied = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [jump_right, conjTranspose_kronecker, pauliZ_adjoint, ← mul_kronecker_mul]
    change (qubitZ * qubitZ) ⊗ₖ (e * eᴴ) = (1 : Qubit) ⊗ₖ (e * eᴴ)
    rw [pauliZ_mul_self]
  · rw [jump_right, conjTranspose_kronecker, pauliZ_adjoint, ← mul_kronecker_mul]
    change (qubitZ * qubitZ) ⊗ₖ (eᴴ * e) = (1 : Qubit) ⊗ₖ (eᴴ * e)
    rw [pauliZ_mul_self]
  · ext ⟨i, j⟩ ⟨k, l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num [coldVacuum, coldOccupied, liftCold, e, Matrix.kroneckerMap_apply,
        Matrix.one_apply, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
        Matrix.conjTranspose_apply]

theorem coldMarginal_posSemidef (A : Mat) (hA : A.PosSemidef) :
    (coldMarginal A).PosSemidef :=
  (partialTraceLeft_posSemidef hA).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)

private theorem liftCold_mul (P Q : Qubit) :
    liftCold P * liftCold Q = liftCold (P * Q) := by
  simp only [liftCold, ← mul_kronecker_mul, one_mul]

private theorem trace_liftCold (Q : Qubit) : trace (liftCold Q) = 2 * trace Q := by
  simp [liftCold, trace_kronecker, trace_one]

/-- The trace pairing with an included cold observable computes the partial trace. -/
theorem trace_mul_liftCold (A : Mat) (Q : Qubit) :
    trace (A * liftCold Q) = trace (partialTraceLeft A * Q) :=
  Matrix.trace_mul_one_kron_right A Q

private theorem partialTrace_liftCold (Q : Qubit) :
    partialTraceLeft (liftCold Q) = (2 : ℝ) • Q := by
  change partialTraceLeft (Matrix.kronecker (1 : Qubit) Q) = _
  rw [partialTraceLeft_kronecker, trace_one]
  norm_num [two_smul]

theorem coldMarginal_liftCold (Q : Qubit) : coldMarginal (liftCold Q) = Q := by
  have h : (1 / 2 : ℝ) * 2 = 1 := by norm_num
  rw [coldMarginal, partialTrace_liftCold, smul_smul, h, one_smul]

theorem liftCold_posSemidef {Q : Qubit} (hQ : Q.PosSemidef) :
    (liftCold Q).PosSemidef :=
  (Matrix.PosSemidef.one : (1 : Qubit).PosSemidef).kronecker hQ

private theorem partialTrace_sub (A B : Mat) :
    partialTraceLeft (A - B) = partialTraceLeft A - partialTraceLeft B := by
  ext i j
  simp [partialTraceLeft, Finset.sum_sub_distrib]

theorem partialTrace_remainder (A : Mat) :
    partialTraceLeft (A - liftCold (coldMarginal A)) = 0 := by
  have h : (2 : ℝ) * (1 / 2) = 1 := by norm_num
  rw [partialTrace_sub, partialTrace_liftCold, coldMarginal, smul_smul, h, one_smul, sub_self]

private theorem trace_coldMarginal (A : Mat) :
    (trace A).re = 2 * (trace (coldMarginal A)).re := by
  rw [coldMarginal, trace_smul, Complex.smul_re, trace_partialTraceLeft]
  ring

theorem trace_remainder_sq (A : Mat) :
    (trace ((A - liftCold (coldMarginal A)) * (A - liftCold (coldMarginal A)))).re =
      (trace (A * A)).re - 2 * (trace (coldMarginal A * coldMarginal A)).re := by
  let C := liftCold (coldMarginal A)
  let H := A - C
  have hHC : trace (H * C) = 0 := by
    change trace (H * liftCold (coldMarginal A)) = 0
    rw [trace_mul_liftCold]
    rw [show partialTraceLeft H = 0 from partialTrace_remainder A, zero_mul, trace_zero]
  have hCH : trace (C * H) = 0 := (trace_mul_comm _ _).trans hHC
  have hA : A = H + C := by dsimp [H]; abel
  have htrace : trace (A * A) = trace (H * H) + trace (C * C) := by
    conv_lhs => rw [hA]
    simp [add_mul, mul_add, trace_add, hHC, hCH]
  have hCC : trace (C * C) = 2 * trace (coldMarginal A * coldMarginal A) := by
    exact (congrArg trace (liftCold_mul _ _)).trans (trace_liftCold _)
  have h := congrArg Complex.re (htrace.trans (congrArg (trace (H * H) + ·) hCC))
  norm_num [Complex.add_re, Complex.mul_re] at h
  change (trace (H * H)).re = _
  linarith only [h]

private theorem hermitian_diagonal_im {Q : Qubit} (hQ : Q.IsHermitian) (i : Fin 2) :
    (Q i i).im = 0 := by
  have h := congrArg Complex.im (hQ.apply i i)
  simp only [Complex.star_def, Complex.conj_im] at h
  linarith

private theorem qubit_det (Q : Qubit) (hQ : Q.IsHermitian) :
    Q.det.re = (Q 0 0).re * (Q 1 1).re -
      ((Q 0 1).re ^ 2 + (Q 0 1).im ^ 2) := by
  rw [det_fin_two, ← hQ.apply 1 0]
  simp [Complex.star_def, Complex.mul_re, Complex.sub_re, Matrix.vecMul, dotProduct,
    hermitian_diagonal_im hQ] <;>
    ring

private theorem qubit_trace_det (Q : Qubit) (hQ : Q.IsHermitian) :
    (trace (Q * Q)).re = (trace Q).re ^ 2 - 2 * Q.det.re ∧
    (trace (Q * Q * (e * eᴴ))).re = (Q 0 0).re * (trace Q).re - Q.det.re := by
  constructor <;>
    simp [trace_fin_two, qubit_det Q hQ, Matrix.mul_apply, Fin.sum_univ_two,
      e, Matrix.conjTranspose_apply, ← hQ.apply 1 0, hermitian_diagonal_im hQ, Complex.star_def,
      Matrix.vecMul, dotProduct, Complex.mul_re, Complex.add_re, Complex.sub_re] <;> ring

/-- For a spectator compression the signed CAR overlap depends only on the
two cold diagonal entries. The identity is an equality of complex traces. -/
theorem trace_cold_overlap (Q : Qubit) :
    trace (liftCold Q * jump 0 * liftCold Q * (jump 0)ᴴ) = 2 * Q 0 0 * Q 1 1 := by
  have hq : trace (Q * e * Q * eᴴ) = Q 0 0 * Q 1 1 := by
    simp [trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, e,
      Matrix.conjTranspose_apply] <;> ring
  unfold liftCold
  rw [jump_right, conjTranspose_kronecker, pauliZ_adjoint]
  simp only [← mul_kronecker_mul, one_mul, mul_one]
  change trace ((qubitZ * qubitZ) ⊗ₖ (Q * e * Q * eᴴ)) = _
  rw [pauliZ_mul_self, trace_kronecker, hq]
  simp [trace_one, Fintype.card_fin, mul_assoc]

/-- Hermitian compression retains both components of the off-diagonal entry.
The square is in the physical cold diagonal imbalance, which equals
`(ν - μ) * z` in the spectral notation of Section 2. -/
theorem coldQuadratic_lift_eq (Q : Qubit) (hQ : Q.IsHermitian)
    (c q K : ℝ) (hK : 0 < K) :
    coldQuadratic c q K (liftCold Q) =
      (c - (K - q)^2 / (4 * K)) * (trace (liftCold Q * liftCold Q)).re -
      (K + q^2 / K) * Q.det.re +
      (K / 2) * (((Q 0 0).re - (Q 1 1).re) + q * (trace Q).re / K)^2 := by
  obtain ⟨htrace, hfield⟩ := qubit_trace_det Q hQ
  have h00 : (Q 0 0).im = 0 := hermitian_diagonal_im hQ 0
  have hsum : (trace Q).re = (Q 0 0).re + (Q 1 1).re := by
    rw [trace_fin_two, Complex.add_re]
  unfold coldQuadratic coldVacuum
  rw [trace_cold_overlap]
  simp only [liftCold_mul, trace_liftCold]
  norm_num [Complex.mul_re, Complex.mul_im, h00]
  rw [htrace, hfield, hsum]
  field_simp [hK.ne'] <;> ring

/-- The determinant coefficient is `(K + q²/K)/4` when expressed in `d = 4 det Q`. -/
theorem coldQuadratic_lift_lower (Q : Qubit) (hQ : Q.IsHermitian)
    (c q K : ℝ) (hK : 0 < K) :
    (c - (K - q)^2 / (4 * K)) * (trace (liftCold Q * liftCold Q)).re -
      (K + q^2 / K) / 4 * (4 * Q.det.re) ≤ coldQuadratic c q K (liftCold Q) := by
  rw [coldQuadratic_lift_eq Q hQ c q K hK]
  rw [show (K + q^2 / K) / 4 * (4 * Q.det.re) = (K + q^2 / K) * Q.det.re by ring]
  exact le_add_of_nonneg_right (by positivity)

theorem coldQuadratic_compression_lower (A : Mat) (hA : A.PosSemidef)
    (c q K : ℝ) (hK : 0 < K) :
    (c - (K - q)^2 / (4 * K)) *
        (trace (liftCold (coldMarginal A) * liftCold (coldMarginal A))).re -
      (K + q^2 / K) / 4 * (4 * (coldMarginal A).det.re) ≤
        coldQuadratic c q K (liftCold (coldMarginal A)) :=
  coldQuadratic_lift_lower _ (coldMarginal_posSemidef A hA).isHermitian c q K hK

/-- The determinant is the product of the two Hermitian eigenvalues. -/
theorem det_re_eq_eigenvalue_product (Q : Qubit) (hQ : Q.IsHermitian) :
    Q.det.re = hQ.eigenvalues 0 * hQ.eigenvalues 1 := by
  rw [hQ.det_eq_prod_eigenvalues, Fin.prod_univ_two]
  simp [RCLike.ofReal_eq_complex_ofReal, Complex.mul_re]

/-- Rank-two purity from the two trace moments of the square-root matrix.
The moments are those of eigenvalues `(0, 0, b, a)`, including `b = 0`. -/
theorem rankTwo_purity (A : Mat) (hA : A.IsHermitian) (a b : ℝ)
    (htrace : (trace A).re = a + b) (hsq : (trace (A * A)).re = a^2 + b^2) :
    (trace ((A - liftCold (coldMarginal A)) * (A - liftCold (coldMarginal A)))).re =
      (a - b)^2 / 2 + 4 * (coldMarginal A).det.re := by
  let Q := coldMarginal A
  have hQ : Q.IsHermitian := by
    change (((1 / 2 : ℝ) • partialTraceLeft A)ᴴ) = (1 / 2 : ℝ) • partialTraceLeft A
    have hp : (partialTraceLeft A).IsHermitian := by
      apply Matrix.IsHermitian.ext
      intro i j
      simp only [partialTraceLeft, star_sum]
      exact Finset.sum_congr rfl fun s _ => hA.apply (s, i) (s, j)
    rw [conjTranspose_smul, star_trivial, hp.eq]
  have htr := trace_coldMarginal A
  change (trace A).re = 2 * (trace Q).re at htr
  have ht : (trace Q).re = (a + b) / 2 := by linarith only [htr, htrace]
  rw [trace_remainder_sq, hsq]
  change a^2 + b^2 - 2 * (trace (Q * Q)).re = _
  rw [(qubit_trace_det Q hQ).1, ht]
  ring

private theorem qubit_trace (Q : Qubit) :
    (trace Q).re = (Q 0 0).re + (Q 1 1).re := by
  rw [trace_fin_two, Complex.add_re]

private theorem trace_re_eq_eigenvalue_sum (Q : Qubit) (hQ : Q.IsHermitian) :
    (trace Q).re = hQ.eigenvalues 0 + hQ.eigenvalues 1 := by
  rw [hQ.trace_eq_sum_eigenvalues, Fin.sum_univ_two]
  simp [RCLike.ofReal_eq_complex_ofReal]

private theorem qubit_posSemidef_of_trace_det (Q : Qubit) (hQ : Q.IsHermitian)
    (ht : 0 ≤ (trace Q).re) (hd : 0 ≤ Q.det.re) : Q.PosSemidef := by
  rw [trace_re_eq_eigenvalue_sum Q hQ] at ht
  rw [det_re_eq_eigenvalue_product Q hQ] at hd
  have nonneg_left (x y : ℝ) (hsum : 0 ≤ x + y) (hprod : 0 ≤ x * y) : 0 ≤ x := by
    by_contra! hx
    exact (not_lt_of_ge hprod) (mul_neg_of_neg_of_pos hx (by linarith))
  have h0 := nonneg_left _ _ ht hd
  have h1 := nonneg_left (hQ.eigenvalues 1) (hQ.eigenvalues 0)
    (by simpa only [add_comm] using ht) (by simpa only [mul_comm] using hd)
  apply hQ.posSemidef_iff_eigenvalues_nonneg.mpr
  intro i
  fin_cases i
  · exact h0
  · exact h1

private theorem imbalance_bounds (Q : Qubit) (hQ : Q.IsHermitian)
    (ν μ : ℝ) (hμν : μ ≤ ν)
    (ht : (trace Q).re = ν + μ) (hd : Q.det.re = ν * μ) :
    -(ν - μ) ≤ (Q 0 0).re - (Q 1 1).re ∧ (Q 0 0).re - (Q 1 1).re ≤ ν - μ := by
  rw [qubit_trace] at ht
  rw [qubit_det Q hQ] at hd
  apply abs_le_of_sq_le_sq' _ (sub_nonneg.mpr hμν)
  nlinarith only [congrArg (fun x : ℝ => x^2) ht, hd, sq_nonneg (Q 0 1).re,
    sq_nonneg (Q 0 1).im]

/-- Every diagonal imbalance in the spectral interval is realized by a PSD
cold matrix with trace `ν + μ` and determinant `ν * μ`.
The trace and determinant specify its unordered eigenvalues. -/
theorem exists_cold_matrix_imbalance (ν μ δ : ℝ) (hμ : 0 ≤ μ) (hμν : μ ≤ ν)
    (hlo : -(ν - μ) ≤ δ) (hhi : δ ≤ ν - μ) :
    ∃ Q : Qubit, Q.PosSemidef ∧ (trace Q).re = ν + μ ∧ Q.det.re = ν * μ ∧
      (Q 0 0).re - (Q 1 1).re = δ := by
  have hr : 0 ≤ (ν - μ)^2 - δ^2 := sub_nonneg.mpr (sq_le_sq' hlo hhi)
  let w : ℝ := Real.sqrt ((ν - μ)^2 - δ^2) / 2
  have hw : w^2 = ((ν - μ)^2 - δ^2) / 4 := by
    dsimp [w]
    rw [div_pow, Real.sq_sqrt hr]
    norm_num
  let Q : Qubit :=
    !![↑((ν + μ + δ) / 2), ↑w; ↑w, ↑((ν + μ - δ) / 2)]
  have hQ : Q.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Q, Complex.star_def]
  have ht : (trace Q).re = ν + μ := by
    simp [Q, trace_fin_two, Complex.add_re] <;> ring
  have hd : Q.det.re = ν * μ := by
    rw [qubit_det Q hQ]
    simp [Q] <;> nlinarith only [hw]
  have hδ : (Q 0 0).re - (Q 1 1).re = δ := by
    simp [Q] <;> ring
  exact ⟨Q, qubit_posSemidef_of_trace_det Q hQ (by linarith)
      (by rw [hd]; exact mul_nonneg (by linarith) hμ), ht, hd, hδ⟩

private theorem trace_lift_sq (Q : Qubit) (hQ : Q.IsHermitian) :
    (trace (liftCold Q * liftCold Q)).re = 2 * ((trace Q).re^2 - 2 * Q.det.re) := by
  rw [liftCold_mul, trace_liftCold]
  norm_num [Complex.mul_re, (qubit_trace_det Q hQ).1]

private theorem clamp_sq_le (g t x : ℝ) (hg : 0 ≤ g) (hxlo : -g ≤ x) (hxhi : x ≤ g) :
    (max (-g) (min g t) - t)^2 ≤ (x - t)^2 := by
  rcases lt_trichotomy t (-g) with hlo | heq | hgt
  · have ht : t ≤ g := by linarith
    rw [min_eq_right ht, max_eq_left hlo.le]
    exact (sq_le_sq₀ (by linarith) (by linarith)).2 (by linarith)
  · subst t
    simpa [min_eq_right (show -g ≤ g by linarith)] using sq_nonneg (x - -g)
  · by_cases hhi : t ≤ g
    · simpa [min_eq_right hhi, max_eq_right hgt.le] using sq_nonneg (x - t)
    · have hgt' : g < t := lt_of_not_ge hhi
      rw [min_eq_left hgt'.le, max_eq_right (show -g ≤ g by linarith)]
      have hsq : (t - g)^2 ≤ (t - x)^2 :=
        (sq_le_sq₀ (by linarith) (by linarith)).2 (by linarith)
      calc
        (g - t)^2 = (t - g)^2 := by ring
        _ ≤ (t - x)^2 := hsq
        _ = (x - t)^2 := by ring

/-- The minimum over PSD cold matrices at fixed eigenvalues is attained by
clipping the unconstrained imbalance to the spectral interval. The feasible
interior case attains the lower bound with square equal to zero. -/
theorem coldQuadratic_minimum (c q K ν μ : ℝ) (hK : 0 < K) (hμ : 0 ≤ μ) (hμν : μ ≤ ν) :
    let t := -(q * (ν + μ) / K)
    let δ := max (-(ν - μ)) (min (ν - μ) t)
    ∃ Q : Qubit, Q.PosSemidef ∧ (trace Q).re = ν + μ ∧ Q.det.re = ν * μ ∧
      (Q 0 0).re - (Q 1 1).re = δ ∧
      coldQuadratic c q K (liftCold Q) =
        (c - (K - q)^2 / (4 * K)) * (2 * (ν^2 + μ^2)) -
          (K + q^2 / K) * (ν * μ) + (K / 2) * (δ - t)^2 ∧
      ∀ R : Qubit, R.PosSemidef → (trace R).re = ν + μ → R.det.re = ν * μ →
        coldQuadratic c q K (liftCold Q) ≤ coldQuadratic c q K (liftCold R) := by
  dsimp only
  let t := -(q * (ν + μ) / K)
  let δ := max (-(ν - μ)) (min (ν - μ) t)
  have hg : 0 ≤ ν - μ := sub_nonneg.mpr hμν
  have hlo : -(ν - μ) ≤ δ := le_max_left _ _
  have hhi : δ ≤ ν - μ := max_le (by linarith) (min_le_left _ _)
  obtain ⟨Q, hQ, ht, hd, hδ⟩ := exists_cold_matrix_imbalance ν μ δ hμ hμν hlo hhi
  have formula (R : Qubit) (hR : R.PosSemidef) (hs : (trace R).re = ν + μ)
      (hp : R.det.re = ν * μ) :
      coldQuadratic c q K (liftCold R) =
        (c - (K - q)^2 / (4 * K)) * (2 * (ν^2 + μ^2)) -
          (K + q^2 / K) * (ν * μ) +
          (K / 2) * (((R 0 0).re - (R 1 1).re) - t)^2 := by
    rw [coldQuadratic_lift_eq R hR.isHermitian c q K hK, trace_lift_sq R hR.isHermitian, hs, hp]
    dsimp [t]
    ring
  have hvalue := formula Q hQ ht hd
  rw [hδ] at hvalue
  refine ⟨Q, hQ, ht, hd, hδ, hvalue, ?_⟩
  intro R hR hRt hRd
  obtain ⟨hRlo, hRhi⟩ := imbalance_bounds R hR.isHermitian ν μ hμν hRt hRd
  have hdist := clamp_sq_le (ν - μ) t _ hg hRlo hRhi
  rw [hvalue, formula R hR hRt hRd]
  have hdist' := mul_le_mul_of_nonneg_left hdist (by positivity : 0 ≤ K / 2)
  nlinarith [hdist']

private theorem jump_conjugation_lift (Q : Qubit) :
    jump 0 * liftCold Q * (jump 0)ᴴ = liftCold (e * Q * eᴴ) ∧
    (jump 0)ᴴ * liftCold Q * jump 0 = liftCold (eᴴ * Q * e) := by
  constructor
  · simp only [liftCold, jump_right, conjTranspose_kronecker, pauliZ_adjoint,
      ← mul_kronecker_mul, one_mul, mul_one]
    change (qubitZ * qubitZ) ⊗ₖ (e * Q * eᴴ) = (1 : Qubit) ⊗ₖ (e * Q * eᴴ)
    rw [pauliZ_mul_self]
  · simp only [liftCold, jump_right, conjTranspose_kronecker, pauliZ_adjoint,
      ← mul_kronecker_mul, one_mul, mul_one]
    change (qubitZ * qubitZ) ⊗ₖ (eᴴ * Q * e) = (1 : Qubit) ⊗ₖ (eᴴ * Q * e)
    rw [pauliZ_mul_self]

/-- Trace orthogonality also splits the field and the signed jump overlap. -/
theorem coldQuadratic_split (A : Mat) (c q K : ℝ) :
    coldQuadratic c q K A = coldQuadratic c q K (liftCold (coldMarginal A)) +
      coldQuadratic c q K (A - liftCold (coldMarginal A)) := by
  let Q := coldMarginal A
  let C := liftCold Q
  let H := A - C
  let J := jump 0
  have pair_zero (R : Qubit) : trace (H * liftCold R) = 0 := by
    rw [trace_mul_liftCold, show partialTraceLeft H = 0 from partialTrace_remainder A,
      zero_mul, trace_zero]
  have hHC : trace (H * C) = 0 := pair_zero Q
  have hCH : trace (C * H) = 0 := (trace_mul_comm _ _).trans hHC
  have hf₁ : trace (H * C * coldVacuum) = 0 := by
    rw [Matrix.mul_assoc]
    change trace (H * (liftCold Q * liftCold (e * eᴴ))) = 0
    rw [liftCold_mul, pair_zero]
  have hf₂ : trace (C * H * coldVacuum) = 0 := by
    rw [trace_mul_cycle C H coldVacuum, trace_mul_comm (coldVacuum * C) H]
    change trace (H * (liftCold (e * eᴴ) * liftCold Q)) = 0
    rw [liftCold_mul, pair_zero]
  have hj₁ : trace (H * J * C * Jᴴ) = 0 := by
    rw [Matrix.mul_assoc H J C, Matrix.mul_assoc H (J * C) Jᴴ]
    change trace (H * (jump 0 * liftCold Q * (jump 0)ᴴ)) = 0
    rw [(jump_conjugation_lift Q).1, pair_zero]
  have hj₂ : trace (C * J * H * Jᴴ) = 0 := by
    rw [trace_mul_cycle (C * J) H Jᴴ, trace_mul_comm (Jᴴ * (C * J)) H,
      ← Matrix.mul_assoc Jᴴ C J]
    change trace (H * ((jump 0)ᴴ * liftCold Q * jump 0)) = 0
    rw [(jump_conjugation_lift Q).2, pair_zero]
  have hA : A = C + H := by dsimp [H]; abel
  change coldQuadratic c q K A = coldQuadratic c q K C + coldQuadratic c q K H
  conv_lhs => rw [hA]
  change c * (trace ((C + H) * (C + H))).re +
      q * (trace ((C + H) * (C + H) * coldVacuum)).re -
      K * (trace ((C + H) * J * (C + H) * Jᴴ)).re =
    (c * (trace (C * C)).re + q * (trace (C * C * coldVacuum)).re -
      K * (trace (C * J * C * Jᴴ)).re) +
    (c * (trace (H * H)).re + q * (trace (H * H * coldVacuum)).re -
      K * (trace (H * J * H * Jᴴ)).re)
  simp only [add_mul, mul_add, trace_add,
    hHC, hCH, hf₁, hf₂, hj₁, hj₂, zero_add, add_zero, Complex.add_re]
  ring

/-- Reindex the existing trace Cauchy–Schwarz lemma from `Fin 4` to occupation
indices. Both norms use complex conjugate transpose. -/
private theorem trace_product_cauchy (X Y : Mat) :
    Complex.normSq (trace (X * Y)) ≤
      (trace (Xᴴ * X)).re * (trace (Yᴴ * Y)).re := by
  let equiv := Fintype.equivFin Occupation
  let reindex := Matrix.reindexRingEquiv ℂ equiv
  have hm (A B : Mat) : reindex (A * B) = reindex A * reindex B := reindex.map_mul A B
  have ht (A : Mat) : trace (reindex A) = trace A :=
    equiv.symm.sum_comp (fun i => A i i)
  have hs (A : Mat) : (reindex A)ᴴ = reindex Aᴴ :=
    Matrix.conjTranspose_reindex equiv equiv A
  simpa only [RHLinalg.frobSq, hs, ← hm, ht, RCLike.re_eq_complex_re] using
    D5.S3.Quantum.Matrix.CartesianVariance.trace_product_cauchy (reindex X) (reindex Y)

private theorem jump_norm_trace (H J : Mat) (hH : H.IsHermitian) :
    trace ((H * J)ᴴ * (H * J)) = trace (H * H * (J * Jᴴ)) := by
  calc
    _ = trace (Jᴴ * ((H * H) * J)) := by
      simp only [conjTranspose_mul, hH.eq, Matrix.mul_assoc]
    _ = trace (J * (Jᴴ * (H * H))) := trace_mul_cycle' _ _ _
    _ = _ := by
      rw [← Matrix.mul_assoc J Jᴴ (H * H), trace_mul_comm]

/-- The two weights are the squared Hilbert–Schmidt norms of `H J_c`
and `H J_c*`. This gives the physical overlap estimate on the same frame. -/
theorem cold_overlap_le (H : Mat) (hH : H.IsHermitian) :
    0 ≤ (trace (H * H * coldVacuum)).re ∧
    0 ≤ (trace (H * H * coldOccupied)).re ∧
    |(trace (H * jump 0 * H * (jump 0)ᴴ)).re| ≤
      Real.sqrt ((trace (H * H * coldVacuum)).re) *
        Real.sqrt ((trace (H * H * coldOccupied)).re) := by
  let J := jump 0
  have hP : J * Jᴴ = coldVacuum := cold_projectors.1
  have hN : Jᴴ * (Jᴴ)ᴴ = coldOccupied := by
    rw [conjTranspose_conjTranspose]
    exact cold_projectors.2.1
  have hU := (jump_norm_trace H J hH).trans (congrArg (fun P => trace (H * H * P)) hP)
  have hV := (jump_norm_trace H Jᴴ hH).trans (congrArg (fun P => trace (H * H * P)) hN)
  have hu : 0 ≤ (trace (H * H * coldVacuum)).re := by
    rw [← hU]
    exact (Complex.le_def.mp (posSemidef_conjTranspose_mul_self (H * J)).trace_nonneg).1
  have hv : 0 ≤ (trace (H * H * coldOccupied)).re := by
    rw [← hV]
    exact (Complex.le_def.mp (posSemidef_conjTranspose_mul_self (H * Jᴴ)).trace_nonneg).1
  have hcs := trace_product_cauchy (H * J) (H * Jᴴ)
  rw [hU, hV, ← Matrix.mul_assoc (H * J) H Jᴴ] at hcs
  refine ⟨hu, hv, ?_⟩
  let z := trace (H * J * H * Jᴴ)
  change |z.re| ≤ _
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt hu, Real.sq_sqrt hv]
  calc
    z.re ^ 2 ≤ Complex.normSq z := by
      simp only [Complex.normSq_apply]
      nlinarith only [sq_nonneg z.im]
    _ ≤ _ := hcs

/-- The weaker coefficient of Section 2 follows by two real squares after the
complex trace Cauchy–Schwarz step. -/
theorem coldQuadratic_remainder_lower (H : Mat) (hH : H.IsHermitian)
    (c q K : ℝ) (hK : 0 < K) :
    (c - (K - q)^2 / (4 * K) - K / 4) * (trace (H * H)).re ≤
      coldQuadratic c q K H := by
  obtain ⟨hu, hv, hoverlap⟩ := cold_overlap_le H hH
  let U := Real.sqrt ((trace (H * H * coldVacuum)).re)
  let V := Real.sqrt ((trace (H * H * coldOccupied)).re)
  have hU : U^2 = (trace (H * H * coldVacuum)).re := Real.sq_sqrt hu
  have hV : V^2 = (trace (H * H * coldOccupied)).re := Real.sq_sqrt hv
  have hmass : U^2 + V^2 = (trace (H * H)).re := by
    rw [hU, hV, ← Complex.add_re, ← trace_add, ← mul_add, cold_projectors.2.2, mul_one]
  have hsle :
      (c - (K - q)^2 / (4 * K) - K / 4) * (U^2 + V^2) ≤
        c * (U^2 + V^2) + q * U^2 - K * (U * V) := by
    have hid :
        c * (U^2 + V^2) + q * U^2 - K * (U * V) =
          (c - (K - q)^2 / (4 * K) - K / 4) * (U^2 + V^2) +
            ((K * (U - V) + q * (U + V) / 2)^2 + (q * (U - V) / 2)^2) / (2 * K) := by
      field_simp [hK.ne'] <;> ring
    rw [hid]
    exact le_add_of_nonneg_right (by positivity)
  rw [hmass, hU] at hsle
  refine hsle.trans ?_
  unfold coldQuadratic
  apply sub_le_sub_left
  exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans hoverlap) hK.le

/-- The numerical range of the determinant correction in the rank-two notation. -/
theorem rankTwo_det_bounds (A : Mat) (hA : A.PosSemidef) (a b : ℝ)
    (htrace : (trace A).re = a + b) :
    0 ≤ 4 * (coldMarginal A).det.re ∧
      4 * (coldMarginal A).det.re ≤ (a^2 + b^2 - (a - b)^2 / 2) / 2 := by
  let Q := coldMarginal A
  have hp := coldMarginal_posSemidef A hA
  have ht := trace_coldMarginal A
  rw [htrace, trace_re_eq_eigenvalue_sum Q hp.isHermitian] at ht
  have hd := det_re_eq_eigenvalue_product Q hp.isHermitian
  constructor
  · rw [hd]
    exact mul_nonneg (by norm_num) (mul_nonneg (hp.eigenvalues_nonneg 0) (hp.eigenvalues_nonneg 1))
  · rw [hd]
    nlinarith only [sq_nonneg (hp.isHermitian.eigenvalues 0 - hp.isHermitian.eigenvalues 1),
      congrArg (fun x : ℝ => x^2) ht]

/-- The square-root matrix on a complex orthonormal frame has the two moments
used by the purity and joint bounds, including the rank-one limit. -/
theorem rankTwo_frame_moments (U : Frame) (hU : Uᴴ * U = 1)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    let D : Matrix (Fin 4) (Fin 4) ℂ := diagonal ![0, 0, (b : ℂ), (a : ℂ)]
    let A := U * D * Uᴴ
    A.PosSemidef ∧ (trace A).re = a + b ∧ (trace (A * A)).re = a^2 + b^2 := by
  let levels : Fin 4 → ℂ := ![0, 0, (b : ℂ), (a : ℂ)]
  let D := diagonal levels
  let A := U * D * Uᴴ
  change A.PosSemidef ∧ (trace A).re = a + b ∧ (trace (A * A)).re = a^2 + b^2
  have hD : D.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> simp [levels, Complex.le_def, ha, hb]
  have htr (B : Matrix (Fin 4) (Fin 4) ℂ) : trace (U * B * Uᴴ) = trace B := by
    rw [trace_mul_cycle U B Uᴴ, hU, one_mul]
  have hAA : A * A = U * (D * D) * Uᴴ := by
    calc
      A * A = U * (D * ((Uᴴ * U) * D)) * Uᴴ := by simp only [A, Matrix.mul_assoc]
      _ = _ := by rw [hU, one_mul]
  refine ⟨hD.mul_mul_conjTranspose_same U, ?_, ?_⟩
  · change (trace (U * D * Uᴴ)).re = _
    rw [htr]
    simp [D, levels, Fin.sum_univ_four, Complex.add_re] <;> ring
  · rw [hAA, htr]
    norm_num [D, levels, Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply,
      Fin.sum_univ_four, Complex.add_re, Complex.mul_re] <;> ring

/-- Section 2, equation (5). The only energy input is the Section 1 lower
bound by the remainder purity on this same square-root matrix. -/
theorem rankTwo_joint_lower (A : Mat) (hA : A.PosSemidef) (a b Es c q K : ℝ)
    (hK : 0 < K) (htrace : (trace A).re = a + b)
    (hsq : (trace (A * A)).re = a^2 + b^2)
    (hEs : (trace ((A - liftCold (coldMarginal A)) *
      (A - liftCold (coldMarginal A)))).re ≤ Es) :
    (c - (K - q)^2 / (4 * K)) * (a^2 + b^2) +
      (1 - K / 4) * ((a - b)^2 / 2) +
      (1 - (2 * K + q^2 / K) / 4) * (4 * (coldMarginal A).det.re) ≤
        Es + coldQuadratic c q K A := by
  let Q := coldMarginal A
  let C := liftCold Q
  let H := A - C
  let ell := (a - b)^2 / 2
  let d := 4 * Q.det.re
  let kstar := c - (K - q)^2 / (4 * K)
  have hC : C.IsHermitian := (liftCold_posSemidef (coldMarginal_posSemidef A hA)).isHermitian
  have hH : H.IsHermitian := hA.isHermitian.sub hC
  have hpurity : (trace (H * H)).re = ell + d :=
    rankTwo_purity A hA.isHermitian a b htrace hsq
  have htotal : (trace (H * H)).re =
      a^2 + b^2 - (trace (C * C)).re := by
    have h := trace_remainder_sq A
    rw [hsq] at h
    have hc : (trace (C * C)).re = 2 * (trace (Q * Q)).re := by
      change (trace (liftCold Q * liftCold Q)).re = _
      rw [liftCold_mul, trace_liftCold]
      norm_num [Complex.mul_re]
    simpa only [hc] using h
  have hCC : (trace (C * C)).re = a^2 + b^2 - (ell + d) := by
    linarith only [htotal, hpurity]
  have hkC : kstar * (trace (C * C)).re - (K + q^2 / K) / 4 * d ≤
      coldQuadratic c q K C := coldQuadratic_compression_lower A hA c q K hK
  have hkH : (kstar - K / 4) * (trace (H * H)).re ≤ coldQuadratic c q K H :=
    coldQuadratic_remainder_lower H hH c q K hK
  change (trace (H * H)).re ≤ Es at hEs
  rw [hCC] at hkC
  rw [hpurity] at hkH hEs
  rw [coldQuadratic_split A c q K]
  change kstar * (a^2 + b^2) + (1 - K / 4) * ell +
    (1 - (2 * K + q^2 / K) / 4) * d ≤
      Es + (coldQuadratic c q K C + coldQuadratic c q K H)
  calc
    _ = (ell + d) + (kstar * (a^2 + b^2 - (ell + d)) - (K + q^2 / K) / 4 * d +
          (kstar - K / 4) * (ell + d)) := by ring
    _ ≤ _ := add_le_add hEs (add_le_add hkC hkH)

end D5.S3.Quantum.Semigroups.WuRankTwoSpectatorCompression
