/- GID: D5/S3/Quantum/Measurement/AbsoluteTwoIncoherencePurityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/AbsoluteTwoIncoherencePurityRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurement/AbsoluteTwoIncoherencePurityRefutation.claim; result=D5/S3/Quantum/Measurement/AbsoluteTwoIncoherencePurityRefutation.result; claim=D5/S3/Quantum/Measurement/AbsoluteTwoIncoherencePurityRefutation.claim
   digest: Absolute two-incoherence does not force the purity bound. -/

/-
admission_basis: open-problem-resolution (#17863; Refuted)
escape_witness: none
proof_shape: IsAbsolutelyKIncoherent: bind-only; consumers: claim, witness_absolute
proof_shape: claim: bind-only; consumers: result
proof_shape: r: bind-only; consumers: r_sq, r_bounds
proof_shape: a: bind-only; consumers: spectral_trace, spectral_square, spectral_bounds
proof_shape: b: bind-only; consumers: spectral_trace, spectral_square, spectral_bounds
proof_shape: beta: bind-only; consumers: rho_diagonal, rho_purity, B5_frob
proof_shape: B5: bind-only; consumers: rho0, B5_hermitian, orbit_hermitian
proof_shape: rho0: bind-only; consumers: rho
proof_shape: rho: bind-only; consumers: rho_diagonal, rho_orbit
proof_shape: alpha: bind-only; consumers: parameter_identities, shifted_gram
proof_shape: p: bind-only; consumers: parameter_identities, near_saturation_data
proof_shape: s: bind-only; consumers: parameter_identities, orbit_polynomial
proof_shape: P5: bind-only; consumers: B5_split, columns_product
proof_shape: V: bind-only; consumers: shifted_gram, H
proof_shape: H: bind-only; consumers: H_rank, H_psd, H_entry_formula
proof_shape: epsilon: bind-only; consumers: gapConst, near_saturation_data
proof_shape: gapConst: bind-only; consumers: near_saturation_data, gap_n5, rho_pair_normalized
proof_shape: finalT: bind-only; consumers: rho_pair_normalized, witness_absolute, result
proof_shape: r_sq: bind-only; consumers: r_bounds, spectral_square, parameter_identities
proof_shape: r_bounds: bind-only; consumers: spectral_bounds, parameter_identities
proof_shape: spectral_trace: bind-only; consumers: rho_trace, rho_purity
proof_shape: spectral_square: bind-only; consumers: rho_purity, B5_frob
proof_shape: spectral_bounds: bind-only; consumers: rho_density, H_entry_close
proof_shape: rho_diagonal: bind-only; consumers: rho_trace, rho_density, rho_purity
proof_shape: rho_trace: bind-only; consumers: rho_density
proof_shape: rho_density: bind-only; consumers: witness_absolute
proof_shape: rho_purity: bind-only; consumers: result
proof_shape: frob_rows: bind-only; consumers: entry_sq_le_frob, local_row_bound, near_saturation_data
proof_shape: entry_sq_le_frob: bind-only; consumers: entry_norm_le_of_frob
proof_shape: entry_norm_le_one: bind-only; consumers: row_difference_le, H_entry_close
proof_shape: entry_norm_le_of_frob: bind-only; consumers: entry_norm_le_one, row_difference_le, near_saturation_data, H_entry_close
proof_shape: frob_sub_hermitian: bind-only; consumers: near_saturation_data
proof_shape: rowSq_hermitian: bind-only; consumers: near_saturation_data
proof_shape: local_row_bound: bind-only; consumers: near_saturation_data, H_entry_close
proof_shape: row_difference_le: bind-only; consumers: near_saturation_data
proof_shape: parameter_identities: bind-only; consumers: shifted_gram, near_saturation_data, H_entry_formula, scaled_center
proof_shape: B5_hermitian: bind-only; consumers: B5_frob, orbit_hermitian
proof_shape: B5_frob: bind-only; consumers: orbit_frob
proof_shape: B5_polynomial: bind-only; consumers: orbit_polynomial
proof_shape: orbit_hermitian: bind-only; consumers: near_saturation_data, H_entry_diagonal
proof_shape: orbit_frob: bind-only; consumers: near_saturation_data, H_entry_close
proof_shape: orbit_polynomial: bind-only; consumers: near_saturation_data
proof_shape: B5_split: bind-only; consumers: shifted_gram
proof_shape: columns_product: bind-only; consumers: shifted_gram
proof_shape: shifted_gram: bind-only; consumers: H_entry_formula
proof_shape: H_rank: bind-only; consumers: H_distance_lower
proof_shape: H_psd: bind-only; consumers: H_distance_lower
proof_shape: H_distance_lower: bind-only; consumers: gap_n5
proof_shape: near_saturation_data: bind-only; consumers: H_entry_close
proof_shape: H_entry_formula: bind-only; consumers: H_entry_diagonal, H_entry_close
proof_shape: H_entry_diagonal: bind-only; consumers: H_entry_close
proof_shape: scaled_center: bind-only; consumers: H_entry_close
proof_shape: H_entry_close: bind-only; consumers: H_distance_upper
proof_shape: H_distance_upper: bind-only; consumers: gap_n5
proof_shape: gap_n5: bind-only; consumers: rho_pair_normalized
proof_shape: rho_orbit: bind-only; consumers: rho_pair
proof_shape: rho_pair: bind-only; consumers: rho_pair_normalized
proof_shape: rho_pair_normalized: bind-only; consumers: witness_absolute
proof_shape: witness_absolute: content; consumers: result
proof_shape: result: content; consumers: settling result
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
The source predicates retain their literal expressions; proofs use the existing IsDensity and unitaryEvolution declarations.
The counterexample has dimension five; dimension four and a uniform all-dimension family are not asserted.
Experiment source: the-omega-institute/trureturing-experiments at cb4521985393e13d9517583014c2d21a6e82873f,
docs/reports/johnston-moein-pereira-plosker-2022-absolute-2-incoherence/check.py;
sha256:5cd6f44dd762913ea53d6073e94f2571525a6cf0a2bbe04cb6d36293dce7588a.
Issue #17863 records exit 0 (ALL_OK); the numerical checker supplies no premise of this proof.
Literature completeness and unpublished frame overlap are ASSUMED-UNVERIFIED as recorded in #17863.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/18980
-/

import D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics
import D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound
import D5.S3.Quantum.Matrix.CartesianVariance
import D5.S3.Quantum.Matrix.CommutatorGap
import D5.S3.Quantum.Measurement.AntidistinguishabilityOverlapNonTight
import D5.S3.Quantum.Measurement.FactorWidthTwoCone
import D5.S3.Quantum.Measurement.OverlapLowRankDistance
import D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
import D5.S3.Weil.ZetaLinear.HermitianPosPart
import D5.S3.Weil.ZetaLinear.PosIndex
import D5.S3.Weil.ZetaLinear.RankTrace
import D5.S3.Weil.ZetaLinear.Sylvester
import D5.S3.Weil.ZetaLinear.VonNeumann

set_option autoImplicit false
set_option maxHeartbeats 600000
open Matrix Finset Filter
open scoped BigOperators ComplexOrder Topology RealInnerProductSpace
noncomputable section

namespace D5.S3.Quantum.Measurement.AbsoluteTwoIncoherencePurityRefutation
open D5.S3.Quantum.Measurement.FactorWidthTwoCone
open D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics (unitaryEvolution)

/-- Definition 3: a mixed state `ρ` is absolutely `k`-incoherent if `U ρ U*` is `k`-incoherent
for every unitary `U`. -/
def IsAbsolutelyKIncoherent {n : ℕ} (k : ℕ) (ρ : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound.IsDensity ρ ∧
    ∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ, IsKIncoherentSum k (U * ρ * star U)

/-- Section 5, third open-question bullet: is the purity condition of Theorem 7,
`∑ⱼ λⱼ² ≤ 1/(n − 1)`, necessary for absolute 2-incoherence in every dimension `n ≥ 4`? -/
def claim : Prop :=
  ∀ n : ℕ, 4 ≤ n → ∀ ρ : Matrix (Fin n) (Fin n) ℂ, IsAbsolutelyKIncoherent 2 ρ →
    (ρ * ρ).trace.re ≤ 1 / ((n : ℝ) - 1)

open Matrix
open scoped ComplexOrder

private def r : ℝ := Real.sqrt 6
private def a : ℝ := (1 + r) / 5
private def b : ℝ := (1 - 2 * r / 3) / 5
private def beta (i : Fin 5) : ℝ := if i.val < 2 then a else b
private def B5 : Matrix (Fin 5) (Fin 5) ℂ := diagonal (fun i => (beta i : ℂ))
private def rho0 : Matrix (Fin 5) (Fin 5) ℂ := (1 / 4 : ℝ) • (1 - B5)
private def rho (t : ℝ) : Matrix (Fin 5) (Fin 5) ℂ :=
  AffineMap.lineMap (k := ℝ) rho0 ((1 / 5 : ℝ) • (1 : Matrix (Fin 5) (Fin 5) ℂ)) (-t)
private theorem r_sq : r ^ 2 = 6 := by
  exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)

private theorem r_bounds : 2 < r ∧ r < 5 / 2 := by
  have hr : 0 ≤ r := Real.sqrt_nonneg 6
  exact ⟨by nlinarith [r_sq], by nlinarith [r_sq]⟩

private theorem spectral_trace : 2 * a + 3 * b = 1 := by
  (unfold a b; ring)

private theorem spectral_square : 2 * a ^ 2 + 3 * b ^ 2 = 1 := by
  (unfold a b; nlinarith [r_sq])

private theorem spectral_bounds : 0 < a ∧ a < 7 / 10 ∧ -1 < b ∧ b < 0 := by
  (unfold a b; rcases r_bounds with ⟨hl, hu⟩; constructor; linarith; constructor; linarith; constructor <;> linarith)

private theorem rho_diagonal (t : ℝ) :
    rho t = diagonal (fun i => (((1 + t) * (1 - beta i) / 4 - t / 5 : ℝ) : ℂ)) := by
  {
    ext i j
    by_cases hij : i = j
    · subst j
      simp [rho, AffineMap.lineMap_apply_module, rho0, B5, Matrix.smul_apply, Complex.ofReal_sub, Complex.ofReal_mul,
        Complex.ofReal_div]
      ring
    · simp [rho, AffineMap.lineMap_apply_module, rho0, B5, Matrix.smul_apply, Matrix.one_apply_ne hij, hij]
  }

private theorem rho_trace (t : ℝ) : (rho t).trace = 1 := by
  {
    rw [rho_diagonal, Matrix.trace_diagonal]
    apply Complex.ext
    · simp only [Complex.re_sum, Complex.ofReal_re, Complex.one_re]
      norm_num [Fin.sum_univ_succ, beta]
      linear_combination -(1 + t) / 4 * spectral_trace
    · simp
  }

private theorem rho_density (t : ℝ) (ht : 0 ≤ t) (htu : t ≤ 1 / 10) :
    D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound.IsDensity (rho t) := by
  {
    refine ⟨?_, rho_trace t⟩
    rw [rho_diagonal, Matrix.posSemidef_diagonal_iff]
    intro i
    rw [Complex.nonneg_iff]
    refine ⟨?_, by simp⟩
    simp only [Complex.ofReal_re]
    have hab := spectral_bounds
    have hi : beta i < 7 / 10 := by
      unfold beta
      split_ifs <;> linarith [hab.2.1, hab.2.2.2]
    have hp : 0 ≤ t * (1 - beta i) := mul_nonneg ht (by linarith)
    nlinarith
  }

private theorem rho_purity (t : ℝ) :
    ((rho t) * (rho t)).trace.re = 1 / 5 + (1 + t) ^ 2 / 20 := by
  {
    rw [rho_diagonal, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    simp only [Complex.re_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
    norm_num [Fin.sum_univ_succ, beta]
    have hs := spectral_square
    have ht := spectral_trace
    nlinarith [sq_nonneg t]
  }

open D5.S3.Quantum.Matrix.CartesianVariance

variable {n : ℕ}
private theorem frob_rows (A : Matrix (Fin n) (Fin n) ℂ) :
    RHLinalg.frobSq A = ∑ i, (∑ j, Complex.normSq (A i j)) := by
  rw [frobSq_eq_sum, sum_comm]

private theorem entry_sq_le_frob (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    Complex.normSq (A i j) ≤ RHLinalg.frobSq A := by
  rw [frob_rows]
  exact (single_le_sum (fun k _ => Complex.normSq_nonneg _) (mem_univ j)).trans
    (single_le_sum (fun k _ => sum_nonneg (fun l _ => Complex.normSq_nonneg _)) (mem_univ i))

private theorem entry_norm_le_of_frob (A : Matrix (Fin n) (Fin n) ℂ) (e : ℝ) (he : 0 ≤ e)
    (hA : RHLinalg.frobSq A ≤ e ^ 2) (i j : Fin n) : ‖A i j‖ ≤ e := by
  have h := (entry_sq_le_frob A i j).trans hA
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (A i j)]

private theorem entry_norm_le_one (A : Matrix (Fin n) (Fin n) ℂ) (hA : RHLinalg.frobSq A ≤ 1)
    (i j : Fin n) : ‖A i j‖ ≤ 1 := by
  exact entry_norm_le_of_frob A 1 (by norm_num) (by simpa only [one_pow] using hA) i j

private theorem frob_sub_hermitian (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RHLinalg.frobSq (A-B) = RHLinalg.frobSq A + RHLinalg.frobSq B - 2 * RHLinalg.rtrace (A*B) := by
  rw [sub_eq_add_neg, RHLinalg.frobSq_add_hermitian hA hB.neg]
  simp [RHLinalg.frobSq, RHLinalg.rtrace]
  ring

private theorem rowSq_hermitian (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (i : Fin n) :
    (∑ j, Complex.normSq (A i j)) = ((A*A) i i).re := by
  simp only [Matrix.mul_apply, Complex.re_sum]
  apply sum_congr rfl
  intro j _
  have hji : A j i = star (A i j) := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M j i) hA.eq
    simpa only [Matrix.conjTranspose_apply] using h.symm
  rw [hji]
  simp [Complex.mul_conj]

private theorem local_row_bound (A : Matrix (Fin n) (Fin n) ℂ)
    (htr : ∑ i, (A i i).re = 1)
    (hl : ∀ i j, Complex.normSq (A i j) ≤ (A i i).re * (A j j).re) :
    (∀ i, (∑ j, Complex.normSq (A i j)) ≤ (A i i).re) ∧ RHLinalg.frobSq A ≤ 1 := by
  have hr : ∀ i, (∑ j, Complex.normSq (A i j)) ≤ (A i i).re := by
    intro i
    calc
      (∑ j, Complex.normSq (A i j)) ≤ ∑ j, (A i i).re * (A j j).re := sum_le_sum (fun j _ => hl i j)
      _ = (A i i).re := by rw [← mul_sum, htr, mul_one]
  exact ⟨hr, by rw [frob_rows]; exact (sum_le_sum (fun i _ => hr i)).trans_eq htr⟩

private theorem row_difference_le (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : RHLinalg.frobSq A ≤ 1) (hB : RHLinalg.frobSq B ≤ 1)
    (e : ℝ) (he : 0 ≤ e) (hD : RHLinalg.frobSq (A-B) ≤ e^2) (i : Fin n) :
    |(∑ j, Complex.normSq (A i j)) - (∑ j, Complex.normSq (B i j))| ≤ (n : ℝ) * 2 * e := by
  have hd : ∀ j, |Complex.normSq (A i j) - Complex.normSq (B i j)| ≤ 2 * e := by
    intro j
    have hp := D5.S3.Quantum.Measurement.AntidistinguishabilityOverlapNonTight.squared_modulus_lipschitz (A i j) (B i j) (entry_norm_le_one A hA i j) (entry_norm_le_one B hB i j)
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq] at hp
    have hentry := entry_norm_le_of_frob (A-B) e he hD i j
    change ‖A i j - B i j‖ ≤ e at hentry
    linarith
  calc
    |(∑ j, Complex.normSq (A i j)) - (∑ j, Complex.normSq (B i j))| = |∑ j, (Complex.normSq (A i j) - Complex.normSq (B i j))| := by
      rw [sum_sub_distrib]
    _ ≤ ∑ j, |Complex.normSq (A i j) - Complex.normSq (B i j)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, 2 * e := sum_le_sum (fun j _ => hd j)
    _ = (n : ℝ) * 2 * e := by simp; ring

open D5.S3.Quantum.Matrix.CartesianVariance

private def alpha : ℝ := 15 / (2*r)
private def p : ℝ := 1-a-b
private def s : ℝ := a+b

private theorem parameter_identities :
    alpha ^ 2 = 75 / 8 ∧ alpha * (a-b) = 5 / 2 ∧
    alpha * (1/5-b) = 1 ∧ a*b = -p/5 ∧ 1/4 < p ∧ 0 < s ∧ s < 1 := by
  have hr : r ≠ 0 := by linarith [r_bounds.1]
  have hsq := r_sq
  have hb := r_bounds
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · unfold alpha
    field_simp [hr]
    nlinarith
  · unfold alpha a b
    field_simp [hr]
    ring
  · unfold alpha b
    field_simp [hr]
    ring
  · dsimp [p,a,b]
    nlinarith
  · dsimp [p,a,b]
    linarith
  · dsimp [s,a,b]
    linarith
  · dsimp [s,a,b]
    linarith

private theorem B5_hermitian : B5.IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  simp [isSelfAdjoint_iff]

private theorem B5_frob : RHLinalg.frobSq B5 = 1 := by
  rw [RHLinalg.frobSq, B5_hermitian.eq]
  simp only [B5,Matrix.diagonal_mul_diagonal,Matrix.trace_diagonal,Complex.re_sum,
    ← Complex.ofReal_mul,Complex.ofReal_re]
  norm_num [Fin.sum_univ_succ,beta]
  nlinarith [spectral_square]

private theorem B5_polynomial : B5*B5 = s • B5 - (a*b) • (1 : Matrix (Fin 5) (Fin 5) ℂ) := by
  ext i j
  by_cases hij : i=j
  · subst j
    simp [B5,Matrix.diagonal_mul_diagonal,Matrix.smul_apply,Complex.real_smul,
      s,beta]
    split_ifs <;> push_cast <;> ring
  · simp [B5,Matrix.diagonal_mul_diagonal,Matrix.smul_apply,hij]

private theorem orbit_hermitian (U : Matrix (Fin 5) (Fin 5) ℂ) : (unitaryEvolution U B5).IsHermitian := by
  exact Matrix.isHermitian_mul_mul_conjTranspose U B5_hermitian

private theorem orbit_frob (U : Matrix (Fin 5) (Fin 5) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 5) ℂ) : RHLinalg.frobSq (unitaryEvolution U B5) = 1 := by
  let u : Matrix.unitaryGroup (Fin 5) ℂ := ⟨U,hU⟩
  have hR := D5.S3.Quantum.Matrix.CommutatorGap.frobSq_unitary_right (U*B5) (star u)
  have hL := D5.S3.Quantum.Matrix.CommutatorGap.frobSq_unitary_left B5 u
  change RHLinalg.frobSq (U*B5*Uᴴ) = RHLinalg.frobSq (U*B5) at hR
  change RHLinalg.frobSq (U*B5) = RHLinalg.frobSq B5 at hL
  exact hR.trans (hL.trans B5_frob)

private theorem orbit_polynomial (U : Matrix (Fin 5) (Fin 5) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 5) ℂ) :
    unitaryEvolution U B5 * unitaryEvolution U B5 = s • unitaryEvolution U B5 - (a*b) • (1 : Matrix (Fin 5) (Fin 5) ℂ) := by
  have hUU : Uᴴ*U=1 := Unitary.star_mul_self_of_mem hU
  have hUU' : U*Uᴴ=1 := Unitary.mul_star_self_of_mem hU
  unfold unitaryEvolution
  simp only [Matrix.star_eq_conjTranspose]
  calc
    U*B5*Uᴴ*(U*B5*Uᴴ) = U*(B5*B5)*Uᴴ := by
      calc
        _ = U*B5*(Uᴴ*U)*B5*Uᴴ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hUU]; simp only [Matrix.mul_one,Matrix.mul_assoc]
    _ = _ := by rw [B5_polynomial]; simp [Matrix.mul_sub,Matrix.sub_mul,
      Matrix.mul_smul,Matrix.smul_mul,hUU',Matrix.mul_assoc]

private def P5 : Matrix (Fin 5) (Fin 5) ℂ := diagonal (fun i => if i.val < 2 then 1 else 0)
private def V (U : Matrix (Fin 5) (Fin 5) ℂ) : Matrix (Fin 5) (Fin 2) ℂ :=
  Real.sqrt (5/2 : ℝ) • (U.submatrix id (Fin.castLE (by decide : 2 ≤ 5)))

private theorem B5_split : B5 = b • (1 : Matrix (Fin 5) (Fin 5) ℂ) + (a-b) • P5 := by
  ext i j
  by_cases hij : i=j
  · subst j
    simp [B5,P5,beta,Matrix.smul_apply]
    split_ifs <;> push_cast <;> ring
  · simp [B5,P5,Matrix.smul_apply,hij]

private theorem columns_product (U : Matrix (Fin 5) (Fin 5) ℂ) :
    (U.submatrix id (Fin.castLE (by decide : 2 ≤ 5))) * ((U.submatrix id (Fin.castLE (by decide : 2 ≤ 5))))ᴴ = U*P5*Uᴴ := by
  ext i j
  simp [Matrix.submatrix_apply,P5,Matrix.mul_diagonal,Matrix.mul_apply,
    Matrix.conjTranspose_apply,Fin.sum_univ_succ]

private theorem shifted_gram (U : Matrix (Fin 5) (Fin 5) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 5) ℂ) :
    alpha • (unitaryEvolution U B5 - b • (1 : Matrix (Fin 5) (Fin 5) ℂ)) = V U * (V U)ᴴ := by
  have hUU' : U*Uᴴ=1 := Unitary.mul_star_self_of_mem hU
  have hc : Real.sqrt (5/2 : ℝ) * Real.sqrt (5/2 : ℝ) = 5/2 := Real.mul_self_sqrt (by norm_num)
  have hV : V U * (V U)ᴴ = (5/2 : ℝ) • (U*P5*Uᴴ) := by
    simp only [V,Matrix.conjTranspose_smul,star_trivial,Matrix.smul_mul,Matrix.mul_smul,
      smul_smul,hc,columns_product]
  rw [hV]
  have hO : unitaryEvolution U B5 = b • (1 : Matrix (Fin 5) (Fin 5) ℂ) + (a-b) • (U*P5*Uᴴ) := by
    unfold unitaryEvolution
    simp only [Matrix.star_eq_conjTranspose]
    rw [B5_split]
    simp [Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,
      Matrix.mul_assoc,hUU']
  rw [hO,add_sub_cancel_left,smul_smul,parameter_identities.2.1]

private def H (U : Matrix (Fin 5) (Fin 5) ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  (RHLinalg.normSqMatrix (V U * (V U)ᴴ)).map (algebraMap ℝ ℂ)

private theorem H_rank (U : Matrix (Fin 5) (Fin 5) ℂ) : (H U).rank ≤ 4 := by
  rw [H, D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.rank_map_algebraMap]
  exact D5.S3.Quantum.Measurement.AntidistinguishabilityOverlapNonTight.norm_square_gram_rank (V U)

private theorem H_psd (U : Matrix (Fin 5) (Fin 5) ℂ) : (H U).PosSemidef := by
  rw [H, D5.S3.Quantum.Measurement.AntidistinguishabilityOverlapNonTight.norm_square_gram_factor]
  exact Matrix.posSemidef_self_mul_conjTranspose _

private theorem H_distance_lower (U : Matrix (Fin 5) (Fin 5) ℂ) :
    25/64 ≤ RHLinalg.frobSq
      (D5.S3.Quantum.Measurement.OverlapLowRankDistance.equalOverlap 5 (3/8) - H U) := by
  have h := D5.S3.Quantum.Measurement.OverlapLowRankDistance.equalOverlap_low_rank_distance
    5 4 (3/8) (by norm_num) (by norm_num) (H U) (H_psd U).isHermitian (H_rank U)
  norm_num at h ⊢
  exact h

private def epsilon : ℝ := 1 / 100000000
private def gapConst : ℝ := epsilon ^ 2 / 2

private theorem near_saturation_data (A : Matrix (Fin 5) (Fin 5) ℂ) (hA : IsLocally2 A)
    (htr : RHLinalg.rtrace A = 1) (U : Matrix (Fin 5) (Fin 5) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 5) ℂ)
    (hgap : 1 - RHLinalg.rtrace (A * unitaryEvolution U B5) < gapConst) :
    RHLinalg.frobSq (A - unitaryEvolution U B5) ≤ epsilon^2 ∧
    (∀ i, |(A i i).re - 1/5| ≤ 48*epsilon) ∧
    (∀ i j, 0 ≤ (A i i).re * (A j j).re - Complex.normSq (A i j) ∧
      (A i i).re * (A j j).re - Complex.normSq (A i j) ≤ epsilon) := by
  let B := unitaryEvolution U B5
  have hB : B.IsHermitian := orbit_hermitian U
  have hBF : RHLinalg.frobSq B = 1 := orbit_frob U hU
  have hl := local2_minor A hA
  have htr' : ∑ i, (A i i).re = 1 := by
    simpa [RHLinalg.rtrace,Matrix.trace,Complex.re_sum] using htr
  have hr := local_row_bound A htr' hl
  have hD := frob_sub_hermitian A B hA.1 hB
  rw [hBF] at hD
  have hg : 1 - RHLinalg.rtrace (A*B) < gapConst := hgap
  have hclose : RHLinalg.frobSq (A-B) ≤ epsilon^2 := by
    dsimp only [gapConst] at hg
    linarith [hr.2]
  let delta (i : Fin 5) := (A i i).re - (∑ j, Complex.normSq (A i j))
  have hd0 : ∀ i, 0 ≤ delta i := fun i => sub_nonneg.mpr (hr.1 i)
  have hdsum : ∑ i, delta i = 1 - RHLinalg.frobSq A := by
    dsimp only [delta]
    rw [sum_sub_distrib,← frob_rows,htr']
  have hdsumle : ∑ i, delta i ≤ epsilon := by
    rw [hdsum]
    have he : 2*gapConst ≤ epsilon := by norm_num [gapConst,epsilon]
    have hf0 := D5.S3.Quantum.Matrix.CartesianVariance.frobSq_nonneg (A-B)
    linarith
  have hdle : ∀ i, delta i ≤ epsilon := by
    intro i
    exact (single_le_sum (fun j _ => hd0 j) (mem_univ i)).trans hdsumle
  have hE : ∀ i j, 0 ≤ (A i i).re*(A j j).re - Complex.normSq (A i j) ∧
      (A i i).re*(A j j).re - Complex.normSq (A i j) ≤ epsilon := by
    intro i j
    refine ⟨sub_nonneg.mpr (hl i j),?_⟩
    have hs : ∑ k, ((A i i).re * (A k k).re - Complex.normSq (A i k)) = delta i := by
      rw [sum_sub_distrib,← mul_sum,htr',mul_one]
    have hk : (A i i).re*(A j j).re - Complex.normSq (A i j) ≤ delta i := by
      rw [← hs]
      exact single_le_sum (fun k _ => sub_nonneg.mpr (hl i k)) (mem_univ j)
    exact hk.trans (hdle i)
  refine ⟨hclose,?_,hE⟩
  intro i
  have hrow : |(∑ j, Complex.normSq (A i j)) - (∑ j, Complex.normSq (B i j))| ≤ 10*epsilon := by
    simpa only [Nat.cast_ofNat, show (5:ℝ)*2=10 by norm_num] using row_difference_le A B hr.2 hBF.le epsilon (by norm_num [epsilon]) hclose i
  have hentry := entry_norm_le_of_frob (A-B) epsilon (by norm_num [epsilon]) hclose i i
  have hdiag : |(B i i).re - (A i i).re| ≤ epsilon := by
    rw [abs_sub_comm]
    exact (Complex.abs_re_le_norm (A i i-B i i)).trans hentry
  have hpoly : (∑ j, Complex.normSq (B i j)) = s*(B i i).re - a*b := by
    have hh := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℂ => (M i i).re) (orbit_polynomial U hU)
    rw [← rowSq_hermitian B hB i] at hh
    simpa [Matrix.smul_apply,Complex.real_smul] using hh
  have hs0 : 0 ≤ s := parameter_identities.2.2.2.2.2.1.le
  have hs1 : s ≤ 1 := parameter_identities.2.2.2.2.2.2.le
  have hprod : |s*((B i i).re-(A i i).re)| ≤ epsilon := by
    rw [abs_mul,abs_of_nonneg hs0]
    calc
      s * |(B i i).re-(A i i).re| ≤ 1*epsilon :=
        mul_le_mul hs1 hdiag (abs_nonneg _) (by norm_num)
      _ = epsilon := one_mul _
  have hab : a*b = -p/5 := parameter_identities.2.2.2.1
  have heq : p*((A i i).re-1/5) = (∑ j, Complex.normSq (A i j)) - (∑ j, Complex.normSq (B i j)) +
      s*((B i i).re-(A i i).re) + delta i := by
    rw [hpoly,hab]
    dsimp only [delta,p,s]
    ring
  have hpsum : |p*((A i i).re-1/5)| ≤ 12*epsilon := by
    rw [heq]
    calc
      |(∑ j, Complex.normSq (A i j))-(∑ j, Complex.normSq (B i j))+s*((B i i).re-(A i i).re)+delta i| ≤
          |(∑ j, Complex.normSq (A i j))-(∑ j, Complex.normSq (B i j))+s*((B i i).re-(A i i).re)|+|delta i| := abs_add_le _ _
      _ ≤ (|(∑ j, Complex.normSq (A i j))-(∑ j, Complex.normSq (B i j))|+|s*((B i i).re-(A i i).re)|)+|delta i| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ ≤ 12*epsilon := by rw [abs_of_nonneg (hd0 i)]; linarith [hdle i]
  rw [abs_mul,abs_of_pos (lt_trans (by norm_num) parameter_identities.2.2.2.2.1)] at hpsum
  have hmul : 0 ≤ (p-1/4)*|(A i i).re-1/5| :=
    mul_nonneg (by linarith [parameter_identities.2.2.2.2.1]) (abs_nonneg _)
  nlinarith

open D5.S3.Quantum.Measurement.OverlapLowRankDistance

private theorem H_entry_formula (U : Matrix (Fin 5) (Fin 5) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 5) ℂ) (i j : Fin 5) :
    (H U i j).re = (75/8 : ℝ) * Complex.normSq ((unitaryEvolution U B5 - b • (1 : Matrix (Fin 5) (Fin 5) ℂ)) i j) := by
  unfold H
  rw [← shifted_gram U hU]
  simp [RHLinalg.normSqMatrix,Matrix.map_apply,Matrix.smul_apply,norm_smul,
    mul_pow,Real.norm_eq_abs,sq_abs,parameter_identities.1,Complex.normSq_eq_norm_sq,← Complex.ofReal_pow,Complex.ofReal_re]

private theorem H_entry_diagonal (U : Matrix (Fin 5) (Fin 5) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 5) ℂ) (i : Fin 5) :
    (H U i i).re = (75/8 : ℝ) * ((unitaryEvolution U B5 i i).re - b)^2 := by
  rw [H_entry_formula U hU]
  have hi := congrArg Complex.im ((orbit_hermitian U).apply i i)
  have him : (unitaryEvolution U B5 i i).im = 0 := by
    have hneg : -(unitaryEvolution U B5 i i).im = (unitaryEvolution U B5 i i).im := by simpa using hi
    linarith
  simp [Matrix.sub_apply,Matrix.smul_apply,Complex.normSq_apply,him]
  ring

private theorem scaled_center : (75/8 : ℝ) * (1/5-b)^2 = 1 := by
  have h := congrArg (fun x : ℝ => x^2) parameter_identities.2.2.1
  rw [mul_pow,parameter_identities.1] at h
  norm_num at h
  exact h

private theorem H_entry_close (A : Matrix (Fin 5) (Fin 5) ℂ) (hA : IsLocally2 A)
    (htr : RHLinalg.rtrace A = 1) (U : Matrix (Fin 5) (Fin 5) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 5) ℂ)
    (hgap : 1-RHLinalg.rtrace (A*unitaryEvolution U B5) < gapConst) (i j : Fin 5) :
    |(H U i j).re - (equalOverlap 5 (3/8) i j).re| ≤ 2600*epsilon := by
  obtain ⟨hclose,hflat,hE⟩ := near_saturation_data A hA htr U hU hgap
  let B := unitaryEvolution U B5
  have hd := local2_diagonal A hA
  have htr' : ∑ i, (A i i).re = 1 := by simpa [RHLinalg.rtrace,Matrix.trace,Complex.re_sum] using htr
  have hfa := (local_row_bound A htr' (local2_minor A hA)).2
  have hfb : RHLinalg.frobSq B ≤ 1 := (orbit_frob U hU).le
  have hdiag : ∀ k, |(B k k).re-(A k k).re| ≤ epsilon := by
    intro k
    rw [abs_sub_comm]
    exact (Complex.abs_re_le_norm (A k k-B k k)).trans
      (entry_norm_le_of_frob (A-B) epsilon (by norm_num [epsilon]) hclose k k)
  by_cases hij : i=j
  · subst j
    rw [H_entry_diagonal U hU]
    have hc : (equalOverlap 5 (3/8) i i).re = 1 := by simp [equalOverlap,Matrix.smul_apply]
    rw [hc,← scaled_center,← mul_sub,abs_mul]
    norm_num only [abs_of_pos (by norm_num : (0:ℝ)<75/8)]
    have hbi : |(B i i).re| ≤ 1 := (Complex.abs_re_le_norm _).trans (entry_norm_le_one B hfb i i)
    have hfac : |(B i i).re+1/5-2*b| ≤ 4 := by
      rcases abs_le.mp hbi with ⟨hl,hu⟩
      apply abs_le.mpr
      constructor <;> linarith [spectral_bounds.2.2.1,spectral_bounds.2.2.2]
    have hdist : |(B i i).re-1/5| ≤ 49*epsilon := by
      calc
        |(B i i).re-1/5| = |((B i i).re-(A i i).re)+((A i i).re-1/5)| := by congr 1; ring
        _ ≤ |(B i i).re-(A i i).re|+|(A i i).re-1/5| := abs_add_le _ _
        _ ≤ 49*epsilon := by linarith [hdiag i,hflat i]
    have he : ((B i i).re-b)^2-(1/5-b)^2 =
        ((B i i).re-1/5)*((B i i).re+1/5-2*b) := by ring
    change (75/8 : ℝ)*|((B i i).re-b)^2-(1/5-b)^2| ≤ _
    rw [he,abs_mul]
    have hm := mul_le_mul hdist hfac (abs_nonneg _) (by norm_num [epsilon] : 0 ≤ 49*epsilon)
    nlinarith [show 0 ≤ epsilon by norm_num [epsilon]]
  · have hc : (equalOverlap 5 (3/8) i j).re = 3/8 := by simp [equalOverlap,Matrix.smul_apply,hij]
    have hH : (H U i j).re = (75/8 : ℝ)*Complex.normSq (B i j) := by
      rw [H_entry_formula U hU]
      simp [Matrix.sub_apply,Matrix.smul_apply,hij,B]
    rw [hc,hH]
    have hdi : (A i i).re ≤ 1 := by
      rw [← htr']
      exact single_le_sum (fun k _ => hd k) (mem_univ i)
    have hprod : |(A i i).re*(A j j).re-1/25| ≤ 96*epsilon := by
      have he : (A i i).re*(A j j).re-1/25 =
          (A i i).re*((A j j).re-1/5)+(1/5)*((A i i).re-1/5) := by ring
      rw [he]
      calc
        _ ≤ |(A i i).re*((A j j).re-1/5)|+|(1/5:ℝ)*((A i i).re-1/5)| := abs_add_le _ _
        _ = (A i i).re*|(A j j).re-1/5|+(1/5)*|(A i i).re-1/5| := by
          rw [abs_mul,abs_mul,abs_of_nonneg (hd i)]; norm_num
        _ ≤ 96*epsilon := by
          have hm := mul_le_mul hdi (hflat j) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
          nlinarith [hflat i,show 0 ≤ epsilon by norm_num [epsilon]]
    have hsq : |Complex.normSq (B i j)-Complex.normSq (A i j)| ≤ 2*epsilon := by
      have hp := D5.S3.Quantum.Measurement.AntidistinguishabilityOverlapNonTight.squared_modulus_lipschitz (A i j) (B i j) (entry_norm_le_one A hfa i j) (entry_norm_le_one B hfb i j)
      rw [← Complex.normSq_eq_norm_sq,← Complex.normSq_eq_norm_sq] at hp
      rw [abs_sub_comm]
      exact hp.trans (mul_le_mul_of_nonneg_left
        (entry_norm_le_of_frob (A-B) epsilon (by norm_num [epsilon]) hclose i j) (by norm_num))
    have he : |Complex.normSq (A i j)-(A i i).re*(A j j).re| ≤ epsilon := by
      rw [abs_sub_comm,abs_of_nonneg (hE i j).1]
      exact (hE i j).2
    have htot : |Complex.normSq (B i j)-1/25| ≤ 99*epsilon := by
      calc
        |Complex.normSq (B i j)-1/25| =
          |(Complex.normSq (B i j)-Complex.normSq (A i j))+
            (Complex.normSq (A i j)-(A i i).re*(A j j).re)+
            ((A i i).re*(A j j).re-1/25)| := by congr 1; ring
        _ ≤ |(Complex.normSq (B i j)-Complex.normSq (A i j))+
            (Complex.normSq (A i j)-(A i i).re*(A j j).re)|+
            |(A i i).re*(A j j).re-1/25| := abs_add_le _ _
        _ ≤ (|Complex.normSq (B i j)-Complex.normSq (A i j)|+
            |Complex.normSq (A i j)-(A i i).re*(A j j).re|)+
            |(A i i).re*(A j j).re-1/25| := add_le_add (abs_add_le _ _) le_rfl
        _ ≤ 99*epsilon := by linarith
    have heq : (75/8:ℝ)*Complex.normSq (B i j)-3/8 = (75/8)*(Complex.normSq (B i j)-1/25) := by ring
    rw [heq,abs_mul]
    norm_num only [abs_of_pos (by norm_num : (0:ℝ)<75/8)]
    nlinarith [show 0 ≤ epsilon by norm_num [epsilon]]

private theorem H_distance_upper (A : Matrix (Fin 5) (Fin 5) ℂ) (hA : IsLocally2 A)
    (htr : RHLinalg.rtrace A = 1) (U : Matrix (Fin 5) (Fin 5) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 5) ℂ)
    (hgap : 1-RHLinalg.rtrace (A*unitaryEvolution U B5) < gapConst) :
    RHLinalg.frobSq (equalOverlap 5 (3/8)-H U) ≤ 1/1000000 := by
  have hb : ∀ i j, Complex.normSq ((equalOverlap 5 (3/8)-H U) i j) ≤ (2600*epsilon)^2 := by
    intro i j
    have hc := H_entry_close A hA htr U hU hgap i j
    have hh : (H U i j).im = 0 := by simp [H,Matrix.map_apply]
    have hcim : (equalOverlap 5 (3/8) i j).im = 0 := by
      by_cases hij : i=j <;> simp [equalOverlap,Matrix.smul_apply,hij]
    have hsq := (sq_le_sq₀ (abs_nonneg _) (by norm_num [epsilon] : 0≤2600*epsilon)).mpr hc
    simp only [Matrix.sub_apply,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,hh,hcim]
    nlinarith [sq_abs ((H U i j).re-(equalOverlap 5 (3/8) i j).re)]
  rw [D5.S3.Quantum.Matrix.CartesianVariance.frobSq_eq_sum]
  calc
    _ ≤ ∑ _i : Fin 5, ∑ _j : Fin 5, (2600*epsilon)^2 :=
      sum_le_sum (fun i _ => sum_le_sum (fun j _ => hb j i))
    _ ≤ 1/1000000 := by norm_num [epsilon]

private theorem gap_n5 (A : Matrix (Fin 5) (Fin 5) ℂ) (hA : IsLocally2 A)
    (htr : RHLinalg.rtrace A = 1) (U : Matrix (Fin 5) (Fin 5) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 5) ℂ) :
    RHLinalg.rtrace (A*unitaryEvolution U B5) ≤ 1-gapConst := by
  by_contra hn
  have hg : 1-RHLinalg.rtrace (A*unitaryEvolution U B5) < gapConst := by linarith
  have hu := H_distance_upper A hA htr U hU hg
  have hl := H_distance_lower U
  linarith

private def finalT : ℝ := 1 / 1000000000000000000

private theorem rho_orbit (t : ℝ) (U : Matrix (Fin 5) (Fin 5) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 5) ℂ) :
    U * rho t * Uᴴ = ((1+t)/4 : ℝ) • (1 - unitaryEvolution U B5) - (t/5 : ℝ) • 1 := by
  have hUU : U*Uᴴ = 1 := Unitary.mul_star_self_of_mem hU
  simp [rho,AffineMap.lineMap_apply_module,rho0,unitaryEvolution,Matrix.star_eq_conjTranspose,Matrix.mul_add,Matrix.add_mul,
    Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,sub_eq_add_neg,
    Matrix.smul_mul,smul_smul,Matrix.mul_assoc,hUU,div_eq_mul_inv]

private theorem rho_pair (t : ℝ) (A U : Matrix (Fin 5) (Fin 5) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 5) ℂ) :
    RHLinalg.rtrace (A * (U*rho t*Uᴴ)) =
      (1+t)/4 * (RHLinalg.rtrace A - RHLinalg.rtrace (A*unitaryEvolution U B5)) -
        t/5 * RHLinalg.rtrace A := by
  rw [rho_orbit t U hU]
  simp [Matrix.mul_sub,Matrix.mul_smul,RHLinalg.rtrace,Matrix.trace_sub,
    Matrix.trace_smul,Complex.real_smul]

private theorem rho_pair_normalized (A U : Matrix (Fin 5) (Fin 5) ℂ)
    (hA : IsLocally2 A) (ht : RHLinalg.rtrace A = 1)
    (hU : U ∈ Matrix.unitaryGroup (Fin 5) ℂ) :
    0 ≤ RHLinalg.rtrace (A * (U*rho finalT*Uᴴ)) := by
  rw [rho_pair finalT A U hU,ht]
  have hg := gap_n5 A hA ht U hU
  have hs : 0 ≤ (1+finalT)/4 := by norm_num [finalT]
  have hm := mul_le_mul_of_nonneg_left (show gapConst ≤ 1-RHLinalg.rtrace (A*unitaryEvolution U B5) by linarith) hs
  have hnum : 0 ≤ (1+finalT)/4*gapConst-finalT/5 := by norm_num [finalT,gapConst,epsilon]
  linarith

private theorem witness_absolute : IsAbsolutelyKIncoherent 2 (rho finalT) := by
  refine ⟨rho_density finalT (by norm_num [finalT]) (by norm_num [finalT]), ?_⟩
  intro U hU
  apply fw2_duality (U*rho finalT*star U)
  · exact Matrix.isHermitian_mul_mul_conjTranspose U
      (rho_density finalT (by norm_num [finalT]) (by norm_num [finalT])).1.isHermitian
  intro A hA
  rw [RHLinalg.rtrace,Matrix.trace_mul_comm]
  change 0 ≤ RHLinalg.rtrace (A*(U*rho finalT*Uᴴ))
  rcases (local2_trace_nonneg A hA).eq_or_lt with ht | ht
  · have hz := local2_trace_zero A hA ht.symm
    simp [hz,RHLinalg.rtrace]
  · let c := (RHLinalg.rtrace A)⁻¹
    have hc : 0 < c := inv_pos.mpr ht
    have hnorm : RHLinalg.rtrace (c • A) = 1 := by
      simp [RHLinalg.rtrace,Matrix.trace_smul,Complex.real_smul,c]
      exact inv_mul_cancel₀ (show A.trace.re ≠ 0 from ne_of_gt ht)
    have hn := rho_pair_normalized (c • A) U (local2_smul A hA c hc.le) hnorm hU
    have he : RHLinalg.rtrace ((c • A)*(U*rho finalT*Uᴴ)) =
        c * RHLinalg.rtrace (A*(U*rho finalT*Uᴴ)) := by
      simp [Matrix.smul_mul,RHLinalg.rtrace,Matrix.trace_smul,Complex.real_smul]
    rw [he] at hn
    exact nonneg_of_mul_nonneg_right hn hc

theorem result : ¬ claim := by
  intro h
  have hb := h 5 (by norm_num) (rho finalT) witness_absolute
  have hp : 1/4 < ((rho finalT)*(rho finalT)).trace.re := by
    rw [rho_purity]
    norm_num [finalT]
  norm_num at hb
  linarith

end D5.S3.Quantum.Measurement.AbsoluteTwoIncoherencePurityRefutation
end
