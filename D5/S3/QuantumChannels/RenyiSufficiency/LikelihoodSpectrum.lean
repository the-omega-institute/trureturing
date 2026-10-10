/- GID: D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum
   mirror-E: none(waiver:kernel-checked-proof)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/QuantumChannels/RenyiSufficiency/BouquetFixedPoint.bouquet_fixed_point_rigidity; premises=D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.likelihoodPolynomial_separable,D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.rational_likelihood_charpoly
   digest: The bouquet likelihood matrices have simple spectra. -/

/-
proof_shape: likelihoodPolynomial_separable: content; escape_witness=likelihoodPolynomial_separable
  consumers: likelihood_separable
proof_shape: likelihood_simple_spectrum: content; escape_witness=likelihood_simple_spectrum
  consumers: likelihood_projectors_fixed
proof_shape: matrixPower_eq: bind-only; escape_witness=none
  consumers: matrixPower_diagonal, RenyiSufficiencyRefutation.weighted_trace_power_eq
proof_shape: cfc_diagonal_real: bind-only; escape_witness=none
  consumers: matrixPower_diagonal
proof_shape: rho_hermitian: bind-only; escape_witness=none
  consumers: rho_posDef, weightedRho_hermitian
proof_shape: sigma_posDef: bind-only; escape_witness=none
  consumers: BouquetFixedPoint.fixed_spectral_projectors, BouquetFixedPoint.state_matrix_fixed, BouquetFixedPoint.sigma_diagonal_projectors_fixed, BouquetFixedPoint.fixed_edge, BouquetFixedPoint.bouquet_fixed_point_rigidity
proof_shape: matrixPower_diagonal: bind-only; escape_witness=none
  consumers: likelihood_hermitian, BouquetFixedPoint.likelihood_entry, BouquetHolonomy.sigmaHalf_hermitian
proof_shape: weightedRho_hermitian: bind-only; escape_witness=none
  consumers: likelihood_hermitian, RenyiSufficiencyRefutation.weighted_trace_power_eq
escape_witness: likelihoodPolynomial_separable
admission_basis: escape-witness
Direct frozen dependencies:
  D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.diagonalStarAlgHom
  declaration statement_id: sha256:3da5fa3a2feed6b43a22b9342c899b6f94a1556ea1c0fb205175999a3338b7d1
  D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsDensity
  declaration statement_id: sha256:4ba4e6b5fd69f7af3d48c8ecc93d1d3efe0fbd32799aa8b021b502f76ad76988
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14881
-/

import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation

noncomputable section
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap
open D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsDensity)
namespace D5.S3.QuantumChannels.RenyiSufficiency.LikelihoodSpectrum


section
open Matrix
open scoped ComplexOrder MatrixOrder

def mpow {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (t : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  hA.cfc (fun x => x ^ t)

def matrixPower {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  if hA : A.IsHermitian then mpow hA t else 0

def matrixLog {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  if hA : A.IsHermitian then hA.cfc Real.log else 0

def Dmin {n : ℕ} (rho sigma : Matrix (Fin n) (Fin n) ℂ) (alpha : ℝ) : ℝ :=
  if alpha = 1 then (rho * (matrixLog rho - matrixLog sigma)).trace.re
  else (alpha - 1)⁻¹ * Real.log
    (matrixPower (matrixPower sigma ((1-alpha)/(2*alpha)) * rho *
      matrixPower sigma ((1-alpha)/(2*alpha))) alpha).trace.re

def DminFinite {n : ℕ} (rho sigma : Matrix (Fin n) (Fin n) ℂ) (alpha : ℝ) : Prop :=
  (1 ≤ alpha → LinearMap.range rho.toLin' ≤ LinearMap.range sigma.toLin') ∧
  (alpha < 1 → rho * sigma ≠ 0)

def IsPTP {n m : ℕ} (T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) : Prop :=
  IsPositive T ∧ ∀ X, (T X).trace = X.trace

def Interconvertible {n m : ℕ} (rho1 sigma1 : Matrix (Fin n) (Fin n) ℂ) (rho2 sigma2 : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ∃ (T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) (R : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ),
    IsPTP T ∧ IsPTP R ∧ T rho1 = rho2 ∧ T sigma1 = sigma2 ∧
      R rho2 = rho1 ∧ R sigma2 = sigma1


theorem matrixPower_eq {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (t : ℝ) :
    matrixPower A t = mpow hA t := by simp [matrixPower, hA]
end

section
open Matrix Polynomial
open scoped ComplexOrder MatrixOrder

def rho (minus : Bool) (e : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  !![1/5, e/5, -Complex.I*e/5, e/5, (if minus then Complex.I else -Complex.I)*e/5;
     e/5, 1/5, e/5, 0, 0;
     Complex.I*e/5, e/5, 1/5, 0, 0;
     e/5, 0, 0, 1/5, e/5;
     (if minus then -Complex.I else Complex.I)*e/5, 0, 0, e/5, 1/5]

def weightedRho (minus : Bool) (e : ℂ) (d : Fin 5 → ℂ) :=
  diagonal d * rho minus e * diagonal d


section
open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

private theorem cfc_diagonal_real (n : ℕ) (d : Fin n → ℝ) (f : ℝ → ℝ) :
    cfc f (diagonal (fun i => (d i : ℂ))) = diagonal (fun i => (f (d i) : ℂ)) := by
  let J := D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.diagonalStarAlgHom (n := Fin n)

  letI : ContinuousFunctionalCalculus ℝ (Fin n → ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  let v : Fin n → ℂ := fun i => (d i : ℂ)
  have hc : ContinuousOn f (spectrum ℝ v) := by
    rw [Pi.spectrum_eq]
    simpa only [v, ← Complex.coe_algebraMap, CFC.spectrum_algebraMap_eq, Set.iUnion_singleton_eq_range] using
      (Set.finite_range d).continuousOn f
  have hd : IsSelfAdjoint v := by ext i; simp [v]
  have hD : IsSelfAdjoint (J v) := hd.map J
  change cfc f (J v) = _
  rw [← J.map_cfc (R := ℝ) (p := IsSelfAdjoint) (q := IsSelfAdjoint) f v hc
      (J.toLinearMap.continuous_of_finiteDimensional) hd hD]
  rw [cfc_map_pi (S := ℂ) f v (by simpa only [← Pi.spectrum_eq] using hc) hd (fun i => by simp [v, IsSelfAdjoint])]
  change diagonal (fun i => cfc f (v i)) = _
  simp [v, ← Complex.coe_algebraMap, cfc_algebraMap]
end

section
open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

def sigma : Matrix (Fin 5) (Fin 5) ℂ := diagonal (fun i => ((((i.val + 1 : ℕ) : ℝ) / 15 : ℝ) : ℂ))

theorem rho_hermitian (minus : Bool) (e : ℝ) : (rho minus e).IsHermitian := by
  cases minus <;> apply IsHermitian.ext <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [rho]

theorem sigma_posDef : sigma.PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  exact_mod_cast (show (0 : ℝ) < ((i.val + 1 : ℕ) : ℝ) / 15 by positivity)

theorem matrixPower_diagonal {n : ℕ} (d : Fin n → ℝ) (t : ℝ) :
    matrixPower (diagonal (fun i => (d i : ℂ))) t =
      diagonal (fun i => ((d i ^ t : ℝ) : ℂ)) := by
  have hD : (diagonal (fun i => (d i : ℂ))).IsHermitian := by
    apply isHermitian_diagonal_of_self_adjoint
    ext i
    simp
  rw [matrixPower_eq hD, mpow, ← hD.cfc_eq, cfc_diagonal_real]

theorem weightedRho_hermitian (minus : Bool) (e : ℝ) (d : Fin 5 → ℝ) :
    (weightedRho minus e (fun i => (d i : ℂ))).IsHermitian := by
  have hD : (diagonal (fun i => (d i : ℂ))).IsHermitian := by
    apply isHermitian_diagonal_of_self_adjoint
    ext i
    simp
  exact (show (diagonal (fun i => (d i : ℂ))).conjTranspose * rho minus e *
      diagonal (fun i => (d i : ℂ)) = weightedRho minus e (fun i => (d i : ℂ)) by
      rw [hD.eq]; rfl) ▸ isHermitian_conjTranspose_mul_mul _ (rho_hermitian minus e)

end

section
open Matrix Polynomial

def likelihoodPolynomial : Polynomial ℂ :=
  C (1/1 : ℂ) * X ^ 5 +
    C (-137/20 : ℂ) * X ^ 4 +
    C (33749973/2000000 : ℂ) * X ^ 3 +
    C (-382499181/20000000 : ℂ) * X ^ 2 +
    C (80999686800081/8000000000000 : ℂ) * X ^ 1 +
    C (-16199902800081/8000000000000 : ℂ)

private def bezoutA : Polynomial ℂ :=
  C (-9759212253483351751066227919717062560000000000000000000000000/4724265368012440191317405185339589326884409376161427967981 : ℂ) * X ^ 3 +
    C (45712137440130276192583538884127324690800000000000000000000000/4724265368012440191317405185339589326884409376161427967981 : ℂ) * X ^ 2 +
    C (-20878647922846796999648582729819901923188168000000000000000000/1574755122670813397105801728446529775628136458720475989327 : ℂ) * X ^ 1 +
    C (2841951856423738565187521480295853318347548800000000000000000/524918374223604465701933909482176591876045486240158663109 : ℂ)

private def bezoutB : Polynomial ℂ :=
  C (1951842450696670350213245583943412512000000000000000000000000/4724265368012440191317405185339589326884409376161427967981 : ℂ) * X ^ 4 +
    C (-11816451645480493618308854226827940079600000000000000000000000/4724265368012440191317405185339589326884409376161427967981 : ℂ) * X ^ 3 +
    C (7857862677235580885738531095407048501891112000000000000000000/1574755122670813397105801728446529775628136458720475989327 : ℂ) * X ^ 2 +
    C (-2086411255124702031189237091707577142203515200000000000000000/524918374223604465701933909482176591876045486240158663109 : ℂ) * X ^ 1 +
    C (27068619176510353514064161458104823492846302472000000000000/24996113058266879319139709975341742470287880297150412529 : ℂ)

set_option maxHeartbeats 3000000 in
theorem likelihoodPolynomial_separable : likelihoodPolynomial.Separable := by
  rw [Polynomial.separable_def']
  refine ⟨bezoutA, bezoutB, ?_⟩
  apply Polynomial.funext
  intro z
  norm_num [likelihoodPolynomial, bezoutA, bezoutB, Polynomial.derivative_add,
    Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_C,
    Polynomial.derivative_X]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem rational_likelihood_charpoly (minus : Bool) :
    (rho minus (1/1000) * diagonal (fun i : Fin 5 => (15 : ℂ) / (i.val+1))).charpoly =
      likelihoodPolynomial := by
  have hm : rho minus (1/1000) * diagonal (fun i : Fin 5 => (15 : ℂ) / (i.val+1)) =
      !![3, 3/2000, -Complex.I/1000, 3/4000, (if minus then Complex.I else -Complex.I)*3/5000;
         3/1000, 3/2, 1/1000, 0, 0;
         Complex.I*3/1000, 3/2000, 1, 0, 0;
         3/1000, 0, 0, 3/4, 3/5000;
         (if minus then -Complex.I else Complex.I)*3/1000, 0, 0, 3/4000, 3/5] := by
    ext i j
    simp only [Matrix.mul_diagonal]
    cases minus <;> fin_cases i <;> fin_cases j <;> norm_num [rho] <;> ring
  rw [hm]
  apply Polynomial.funext
  intro z
  cases minus <;>
    simp [Matrix.charpoly, Matrix.det_succ_row_zero, Matrix.det_fin_two,
      Matrix.det_fin_one, Matrix.charmatrix_apply, Matrix.submatrix_apply,
      Fin.sum_univ_succ, Fin.succAbove, likelihoodPolynomial] <;>
    ring_nf <;>
    norm_num [← Polynomial.C_mul, ← Polynomial.C_add, ← Polynomial.C_sub, ← Polynomial.C_pow,
      Complex.I_sq] <;> ring_nf

private theorem rpow_negative_half_square (x : ℝ) (hx : 0 < x) :
    x ^ (-1/2 : ℝ) * x ^ (-1/2 : ℝ) = x⁻¹ := by
  rw [← Real.rpow_add hx]
  norm_num [Real.rpow_neg_one]

private theorem sigma_inverse_half_square :
    matrixPower sigma (-1/2) * matrixPower sigma (-1/2) =
      diagonal (fun i : Fin 5 => (15 : ℂ) / (i.val+1)) := by
  rw [show sigma = diagonal (fun i : Fin 5 => ((((i.val+1 : ℕ) : ℝ)/15 : ℝ) : ℂ)) from rfl,
    matrixPower_diagonal]
  simp only [Matrix.diagonal_mul_diagonal, ← Complex.ofReal_mul]
  congr 1
  funext i
  rw [rpow_negative_half_square _ (by positivity)]
  simp [inv_div]

def likelihood (minus : Bool) : Matrix (Fin 5) (Fin 5) ℂ :=
  matrixPower sigma (-1/2) * rho minus (1/1000) * matrixPower sigma (-1/2)

private theorem likelihood_charpoly (minus : Bool) :
    (likelihood minus).charpoly = likelihoodPolynomial := by
  unfold likelihood
  rw [Matrix.mul_assoc, Matrix.charpoly_mul_comm, Matrix.mul_assoc,
    sigma_inverse_half_square]
  exact rational_likelihood_charpoly minus

theorem likelihood_hermitian (minus : Bool) : (likelihood minus).IsHermitian := by
  let d : Fin 5 → ℝ := fun i => (((i.val+1 : ℕ) : ℝ)/15) ^ (-1/2 : ℝ)
  have hs : matrixPower sigma (-1/2) = diagonal (fun i => (d i : ℂ)) :=
    matrixPower_diagonal (fun i : Fin 5 => ((i.val+1 : ℕ) : ℝ)/15) (-1/2)
  simpa only [likelihood, hs, weightedRho, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat] using weightedRho_hermitian minus (1/1000) d

private theorem likelihood_separable (minus : Bool) : (likelihood minus).charpoly.Separable := by
  rw [likelihood_charpoly]
  exact likelihoodPolynomial_separable

theorem likelihood_simple_spectrum (minus : Bool) :
    Function.Injective (likelihood_hermitian minus).eigenvalues := by
  have hn := Polynomial.nodup_roots (likelihood_separable minus)
  rw [(likelihood_hermitian minus).roots_charpoly_eq_eigenvalues] at hn
  have hi := Multiset.inj_on_of_nodup_map hn
  intro i j he
  exact hi i (by simp) j (by simp) (by simp [Function.comp_def, he])
end

end
end D5.S3.QuantumChannels.RenyiSufficiency.LikelihoodSpectrum
