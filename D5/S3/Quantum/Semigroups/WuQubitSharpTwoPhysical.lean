/- GID: D5/S3/Quantum/Semigroups/WuQubitSharpTwoPhysical
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuQubitSharpTwoPhysical
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordinary-trace one-mode qubit energy and entropy identities, equality, and tracial affinity stability. -/

import D5.S3.Quantum.Semigroups.WuModularEdgeSpectral
import D5.S3.Quantum.Divergence.SpectralCeilingRelativeEntropy
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import D5.S3.Quantum.Recovery.BKMFlagRefinementPetz
import D5.S3.Quantum.Semigroups.WuQubitSharpTwoRigidity

/-!
# Wu's physical one-mode deficit at exponent two

Wu, arXiv:2610.33686v1, §3.1, equations (3.1), (3.2), and (3.6)–(3.10).
The generator is the positive Heisenberg generator of the unital semigroup.
Its trace dual is the generator in the CPTP evolution of densities.
The square-root embedding uses ordinary trace with a trace-one input density.
-/

noncomputable section

open Set _root_.Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Semigroups.WuQubitSharpTwoPhysical

set_option autoImplicit false

open WuModularEdgeSpectral
open WuQubitSharpTwoRigidity
open D5.S3.Quantum.Matrix.SpectralPower (mpow mpow_one)
open D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity (cfc_log_diagonal)
open D5.S3.Quantum.Divergence.SpectralCeilingRelativeEntropy (trace_self_cfc)
open D5.S3.Quantum.Recovery.BKMFlagRefinement (relativeEntropyOfMatrices)

abbrev Qubit := Matrix (Fin 2) (Fin 2) ℂ

def ratePlus (h : ℝ) : ℝ := Real.exp h / (2 * Real.cosh h)

def rateMinus (h : ℝ) : ℝ := Real.exp (-h) / (2 * Real.cosh h)

private def gibbsWeight (h : ℝ) (i : Fin 2) : ℝ :=
  if i = 0 then ratePlus h else rateMinus h

def gibbs (h : ℝ) : Qubit := diagonal (fun i => (gibbsWeight h i : ℂ))

/-- The positive generator in (3.2), in the order (s₊, s₋) of (3.1). -/
def generator (h : ℝ) (X : Qubit) : Qubit :=
  !![2 * (rateMinus h : ℂ) * (X 0 0 - X 1 1), X 0 1;
    X 1 0, 2 * (ratePlus h : ℂ) * (X 1 1 - X 0 0)]

def embeddedObservable (h : ℝ) (ρ : Qubit) : Qubit :=
  mpow (gibbs h) (-(1 / 4)) * mpow ρ (1 / 2) * mpow (gibbs h) (-(1 / 4))

/-- At p = p' = 2 the factor 4/(pp') in (3.7) is one. -/
def energy (h : ℝ) (ρ : Qubit) : ℝ :=
  (mpow ρ (1 / 2) *
    (mpow (gibbs h) (1 / 4) * generator h (embeddedObservable h ρ) *
      mpow (gibbs h) (1 / 4))).trace.re

def entropy (h : ℝ) (ρ : Qubit) : ℝ :=
  relativeEntropyOfMatrices ρ (gibbs h)

private def jump : Qubit := !![0, 1; 0, 0]

private theorem jump_adjoint : jumpᴴ = !![0, 0; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jump, Matrix.conjTranspose_apply]

private theorem ratePlus_pos (h : ℝ) : 0 < ratePlus h :=
  div_pos (Real.exp_pos h) (mul_pos (by norm_num) (Real.cosh_pos h))

private theorem rateMinus_pos (h : ℝ) : 0 < rateMinus h :=
  div_pos (Real.exp_pos _) (mul_pos (by norm_num) (Real.cosh_pos h))

private theorem gibbs_posDef (h : ℝ) : (gibbs h).PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  apply Complex.zero_lt_real.mpr
  by_cases hi : i = 0
  · simpa only [gibbsWeight, ite_eq_left hi] using ratePlus_pos h
  · simpa only [gibbsWeight, ite_eq_right hi] using rateMinus_pos h

private theorem rate_sum (h : ℝ) : ratePlus h + rateMinus h = 1 := by
  unfold ratePlus rateMinus
  rw [← add_div, Real.cosh_eq]
  have hp : 0 < Real.exp h + Real.exp (-h) := add_pos (Real.exp_pos _) (Real.exp_pos _)
  rw [show 2 * ((Real.exp h + Real.exp (-h)) / 2) =
    Real.exp h + Real.exp (-h) by ring, div_self hp.ne']

private theorem rate_difference (h : ℝ) : ratePlus h - rateMinus h = Real.tanh h := by
  rw [ratePlus, rateMinus, ← sub_div, Real.tanh_eq_sinh_div_cosh, Real.sinh_eq]
  field_simp [(Real.cosh_pos h).ne']

private theorem rate_roots (h : ℝ) :
    Real.sqrt (rateMinus h) * Real.sqrt (ratePlus h) = 1 / (2 * Real.cosh h) := by
  have hc : 0 ≤ 1 / (2 * Real.cosh h) := by positivity
  rw [← Real.sqrt_mul (rateMinus_pos h).le]
  have he : rateMinus h * ratePlus h = (1 / (2 * Real.cosh h)) ^ 2 := by
    rw [rateMinus, ratePlus, div_mul_div_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
    field_simp [(Real.cosh_pos h).ne']
  rw [he, Real.sqrt_sq hc]

private theorem paired_eq_generator (h : ℝ) (X : Qubit) :
    pairedGenerator (ratePlus h) (rateMinus h) jump X = generator h X := by
  have hab : (ratePlus h : ℂ) + (rateMinus h : ℂ) = 1 := by
    exact_mod_cast rate_sum h
  change (2 * ratePlus h) •
      ((1 / 2 : ℝ) • ((jumpᴴ * jump) * X + X * (jumpᴴ * jump)) - jumpᴴ * X * jump) +
    (2 * rateMinus h) •
      ((1 / 2 : ℝ) • ((jumpᴴᴴ * jumpᴴ) * X + X * (jumpᴴᴴ * jumpᴴ)) -
        jumpᴴᴴ * X * jumpᴴ) = _
  rw [Matrix.conjTranspose_conjTranspose, jump_adjoint]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [generator, jump, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    push_cast <;> ring_nf
  · linear_combination X 0 1 * hab
  · linear_combination X 1 0 * hab

private theorem jump_modular (h : ℝ) :
    gibbs h * jump * (gibbs h)⁻¹ = (ratePlus h / rateMinus h) • jump := by
  have hrate : (ratePlus h : ℂ) / (rateMinus h : ℂ) * (rateMinus h : ℂ) =
      (ratePlus h : ℂ) :=
    div_mul_cancel₀ _ (by exact_mod_cast (rateMinus_pos h).ne')
  have hcomm : gibbs h * jump = (ratePlus h / rateMinus h) • (jump * gibbs h) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [gibbs, jump, Matrix.diagonal_mul, Matrix.mul_diagonal, gibbsWeight,
        Matrix.smul_apply, Complex.real_smul, Matrix.of_apply] <;>
      norm_num [hrate]
  have hd : IsUnit (gibbs h).det :=
    (gibbs h).isUnit_iff_isUnit_det.mp (gibbs_posDef h).isUnit
  rw [hcomm, Matrix.smul_mul, Matrix.mul_nonsing_inv_cancel_right _ _ hd]

private def frameWeight {ρ : Qubit} (hρ : ρ.IsHermitian) (i j : Fin 2) : ℝ :=
  Complex.normSq ((hρ.eigenvectorUnitary : Qubit) i j)

/-- The magnitude of the difference between the two eigenvalues. -/
def polarization {ρ : Qubit} (hρ : ρ.IsHermitian) : ℝ :=
  |hρ.eigenvalues 0 - hρ.eigenvalues 1|

private def largerIndex {ρ : Qubit} (hρ : ρ.IsHermitian) : Fin 2 :=
  if hρ.eigenvalues 1 ≤ hρ.eigenvalues 0 then 0 else 1

/-- Expectation of diag(1, -1) in the eigenvector of the larger eigenvalue.
At a repeated eigenvalue column zero of the chosen frame is used. -/
def gibbsAlignment {ρ : Qubit} (hρ : ρ.IsHermitian) : ℝ :=
  frameWeight hρ 0 (largerIndex hρ) - frameWeight hρ 1 (largerIndex hρ)

private theorem frame_complements {ρ : Qubit} (hρ : ρ.IsHermitian) :
    frameWeight hρ 0 1 = 1 - frameWeight hρ 0 0 ∧
    frameWeight hρ 1 0 = 1 - frameWeight hρ 0 0 ∧
    frameWeight hρ 1 1 = frameWeight hρ 0 0 := by
  let U : Qubit := hρ.eigenvectorUnitary
  have row (W : Qubit) (hW : W * Wᴴ = 1) (i : Fin 2) :
      Complex.normSq (W i 0) + Complex.normSq (W i 1) = 1 := by
    have hi := congrArg (fun M : Qubit => (M i i).re) hW
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
      Complex.mul_conj, Complex.add_re, Complex.ofReal_re, Fin.sum_univ_two,
      Matrix.one_apply_eq, Complex.one_re] using hi
  have hrow : U * Uᴴ = 1 := Unitary.coe_mul_star_self hρ.eigenvectorUnitary
  have hcol : Uᴴ * U = 1 := Unitary.coe_star_mul_self hρ.eigenvectorUnitary
  have h0 := row U hrow 0
  have h1 := row U hrow 1
  have hc : Complex.normSq (U 0 0) + Complex.normSq (U 1 0) = 1 := by
    simpa only [Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj] using
      row Uᴴ (by rwa [Matrix.conjTranspose_conjTranspose]) 0
  change Complex.normSq (U 0 1) = 1 - Complex.normSq (U 0 0) ∧
    Complex.normSq (U 1 0) = 1 - Complex.normSq (U 0 0) ∧
    Complex.normSq (U 1 1) = Complex.normSq (U 0 0)
  exact ⟨by linarith only [h0], by linarith only [hc], by linarith only [hc, h1]⟩

private theorem weight_jump {ρ : Qubit} (hρ : ρ.IsHermitian) (i j : Fin 2) :
    edgeWeight hρ jump i j = frameWeight hρ 0 i * frameWeight hρ 1 j := by
  let U : Qubit := hρ.eigenvectorUnitary
  have h0 : (jump * U) 0 j = U 1 j := by simp [jump, Matrix.mul_apply, Fin.sum_univ_two]
  have h1 : (jump * U) 1 j = 0 := by simp [jump, Matrix.mul_apply, Fin.sum_univ_two]
  change Complex.normSq
    (((Unitary.conjStarAlgAut ℂ Qubit hρ.eigenvectorUnitary).symm jump) i j) = _
  rw [Unitary.conjStarAlgAut_symm_apply, Matrix.mul_assoc]
  change Complex.normSq ((Uᴴ * (jump * U)) i j) =
    Complex.normSq (U 0 i) * Complex.normSq (U 1 j)
  simp only [Matrix.mul_apply (N := jump * U), Fin.sum_univ_two, h0, h1,
    Matrix.conjTranspose_apply, mul_zero, add_zero, Complex.star_def, Complex.normSq_mul,
    Complex.normSq_conj]

private theorem kernel_two {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    coshEdgeKernel (1 / 2) u v = (u + v) / 2 - Real.sqrt u * Real.sqrt v := by
  rw [← edgeKernel_eq_cosh (p := 1 / 2) (by norm_num) (by norm_num) hu hv]
  change (u + v - (v ^ (1 - 1 / 2 : ℝ) * u ^ (1 / 2 : ℝ) +
    u ^ (1 - 1 / 2 : ℝ) * v ^ (1 / 2 : ℝ))) / 2 = _
  simp only [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  ring

private theorem energy_edges (h : ℝ) {ρ : Qubit} (hρ : ρ.PosSemidef) :
    energy h ρ = 4 * ∑ i, ∑ j, frameWeight hρ.isHermitian 0 i *
      frameWeight hρ.isHermitian 1 j *
      ((rateMinus h * hρ.isHermitian.eigenvalues i +
        ratePlus h * hρ.isHermitian.eigenvalues j) / 2 -
        (1 / (2 * Real.cosh h)) *
          (Real.sqrt (hρ.isHermitian.eigenvalues i) *
            Real.sqrt (hρ.isHermitian.eigenvalues j))) := by
  have hM : (mpow ρ (1 / 2)).IsHermitian := cfc_predicate _ _
  have he := generatorTrace_eq_cosh (gibbs_posDef h) hρ
    (fun _ : Unit => ratePlus h) (fun _ : Unit => rateMinus h) (fun _ : Unit => jump)
    (s := 2) (by norm_num) (fun _ => ratePlus_pos h) (fun _ => rateMinus_pos h)
    (fun _ => jump_modular h)
  have ht : (1 / 4 : ℝ) * energy h ρ =
      ∑ i, ∑ j, edgeWeight hρ.isHermitian jump i j *
        coshEdgeKernel (1 / 2) (rateMinus h * hρ.isHermitian.eigenvalues i)
          (ratePlus h * hρ.isHermitian.eigenvalues j) := by
    simpa only [Fintype.sum_unique, show (1 / (2 * 2) : ℝ) = 1 / 4 by norm_num,
      show (2 - 1 : ℝ) = 1 by norm_num, mpow_one hM, paired_eq_generator,
      energy, embeddedObservable] using he
  calc
    energy h ρ = 4 * ((1 / 4 : ℝ) * energy h ρ) := by ring
    _ = _ := by
      rw [ht]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [weight_jump, kernel_two (mul_nonneg (rateMinus_pos h).le (hρ.eigenvalues_nonneg i))
          (mul_nonneg (ratePlus_pos h).le (hρ.eigenvalues_nonneg j)),
        Real.sqrt_mul (rateMinus_pos h).le, Real.sqrt_mul (ratePlus_pos h).le, ← rate_roots h]
      ring

private theorem eigenvalue_sum {ρ : Qubit} (hρ : ρ.IsHermitian) (htr : ρ.trace = 1) :
    hρ.eigenvalues 0 + hρ.eigenvalues 1 = 1 := by
  have ht := congrArg Complex.re hρ.trace_eq_sum_eigenvalues
  rw [htr] at ht
  simpa only [Fin.sum_univ_two, Complex.add_re, RCLike.ofReal_eq_complex_ofReal,
    Complex.ofReal_re, Complex.one_re] using ht.symm

private theorem sqrt_product {x y : ℝ} (hx : 0 ≤ x) (hsum : x + y = 1) :
    Real.sqrt x * Real.sqrt y = spectralRoot (x - y) / 2 := by
  have hprod : 1 - (x - y) ^ 2 = 4 * (x * y) := by
    calc
      _ = (x + y) ^ 2 - (x - y) ^ 2 := by rw [hsum, one_pow]
      _ = _ := by ring
  unfold spectralRoot
  rw [hprod, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_mul hx]
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  ring

private theorem energy_eq_unsorted (h : ℝ) {ρ : Qubit} (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) :
    energy h ρ = normalizedEnergy h
      (hρ.isHermitian.eigenvalues 0 - hρ.isHermitian.eigenvalues 1)
      (2 * frameWeight hρ.isHermitian 0 0 - 1) := by
  let x := hρ.isHermitian.eigenvalues 0
  let y := hρ.isHermitian.eigenvalues 1
  let q := frameWeight hρ.isHermitian 0 0
  have hx : 0 ≤ x := hρ.eigenvalues_nonneg 0
  have hy : 0 ≤ y := hρ.eigenvalues_nonneg 1
  have hsum : x + y = 1 := eigenvalue_sum hρ.isHermitian htr
  obtain ⟨h01, h10, h11⟩ := frame_complements hρ.isHermitian
  have hlinear :
      2 * (rateMinus h * (q * x + (1 - q) * y) +
        ratePlus h * ((1 - q) * x + q * y)) =
      1 - Real.tanh h * (x - y) * (2 * q - 1) := by
    calc
      _ = (ratePlus h + rateMinus h) * (x + y) -
          (ratePlus h - rateMinus h) * (x - y) * (2 * q - 1) := by ring
      _ = _ := by rw [rate_sum, rate_difference, hsum, mul_one]
  calc
    energy h ρ =
        2 * (rateMinus h * (q * x + (1 - q) * y) +
          ratePlus h * ((1 - q) * x + q * y)) -
        4 * (1 / (2 * Real.cosh h)) *
          (q * (1 - q) * (Real.sqrt x ^ 2 + Real.sqrt y ^ 2) +
            (q ^ 2 + (1 - q) ^ 2) * (Real.sqrt x * Real.sqrt y)) := by
      rw [energy_edges h hρ]
      simp only [Fin.sum_univ_two, h01, h10, h11]
      dsimp only [q, x, y]
      ring
    _ = _ := by
      rw [hlinear, Real.sq_sqrt hx, Real.sq_sqrt hy, hsum, sqrt_product hx hsum, normalizedEnergy]
      ring

private theorem entropy_eq_unsorted (h : ℝ) {ρ : Qubit} (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) :
    entropy h ρ = normalizedEntropy h
      (hρ.isHermitian.eigenvalues 0 - hρ.isHermitian.eigenvalues 1)
      (2 * frameWeight hρ.isHermitian 0 0 - 1) := by
  let eigenvalue := hρ.isHermitian.eigenvalues
  let U : Qubit := hρ.isHermitian.eigenvectorUnitary
  let x := eigenvalue 0
  let y := eigenvalue 1
  let q := frameWeight hρ.isHermitian 0 0
  let c := Real.log 2 + Real.log (Real.cosh h)
  have hsum : x + y = 1 := eigenvalue_sum hρ.isHermitian htr
  have hs : (ρ * CFC.log ρ).trace.re = x * Real.log x + y * Real.log y := by
    simpa only [CFC.log, Fin.sum_univ_two, x, y, eigenvalue] using
      trace_self_cfc ρ hρ.isHermitian Real.log
  have hlog : CFC.log (gibbs h) = diagonal (fun i => (Real.log (gibbsWeight h i) : ℂ)) :=
    cfc_log_diagonal _
  have hspec : ρ = U * diagonal (fun j => (eigenvalue j : ℂ)) * Uᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, Function.comp_def,
      RCLike.ofReal_eq_complex_ofReal, Matrix.star_eq_conjTranspose] using
      hρ.isHermitian.spectral_theorem
  have hc : (ρ * CFC.log (gibbs h)).trace.re =
      ∑ i, ∑ j, Real.log (gibbsWeight h i) * eigenvalue j * frameWeight hρ.isHermitian i j := by
    rw [Matrix.trace_mul_comm, hlog]
    calc
      _ = (diagonal (fun i => (Real.log (gibbsWeight h i) : ℂ)) *
          (U * diagonal (fun j => (eigenvalue j : ℂ)) * Uᴴ)).trace.re :=
        congrArg (fun A : Qubit =>
          (diagonal (fun i => (Real.log (gibbsWeight h i) : ℂ)) * A).trace.re) hspec
      _ = _ := by
        simp only [← Matrix.mul_assoc]
        exact WuCubicConditionalTensorization.trace_diagonal_overlap
          (fun i => Real.log (gibbsWeight h i)) eigenvalue U
  have hlog_rate (t : ℝ) : Real.log (Real.exp t / (2 * Real.cosh h)) = t - c := by
    rw [Real.log_div (Real.exp_pos t).ne' (by positivity), Real.log_exp,
      Real.log_mul (by norm_num) (Real.cosh_pos h).ne']
  have hlog0 : Real.log (gibbsWeight h 0) = h - c := by
    simpa [gibbsWeight, ratePlus] using hlog_rate h
  have hlog1 : Real.log (gibbsWeight h 1) = -h - c := by
    simpa [gibbsWeight, rateMinus] using hlog_rate (-h)
  obtain ⟨h01, h10, h11⟩ := frame_complements hρ.isHermitian
  have hcross : (ρ * CFC.log (gibbs h)).trace.re = h * (x - y) * (2 * q - 1) - c := by
    rw [hc]
    simp only [Fin.sum_univ_two, hlog0, hlog1, h01, h10, h11]
    change (h - c) * x * q + (h - c) * y * (1 - q) +
      ((-h - c) * x * (1 - q) + (-h - c) * y * q) = _
    linear_combination (-c) * hsum
  have hmass (t : ℝ) :
      (2 * t) * Real.log (2 * t) = 2 * (t * Real.log t) + 2 * t * Real.log 2 := by
    by_cases hz : t = 0
    · simp [hz]
    · rw [Real.log_mul (by norm_num) hz]
      ring
  have hself : x * Real.log x + y * Real.log y =
      polarizationEntropy (x - y) - Real.log 2 := by
    have hp : 1 + (x - y) = 2 * x := by linarith only [hsum]
    have hm : 1 - (x - y) = 2 * y := by linarith only [hsum]
    rw [polarizationEntropy, hp, hm, hmass x, hmass y]
    linear_combination (-Real.log 2) * hsum
  unfold entropy relativeEntropyOfMatrices
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, hs, hself, hcross, normalizedEntropy]
  dsimp only [c, x, y, eigenvalue, q]
  ring

private theorem ordered_eigenvalues {ρ : Qubit} (hρ : ρ.IsHermitian) (htr : ρ.trace = 1) :
    hρ.eigenvalues (largerIndex hρ) = (1 + polarization hρ) / 2 ∧
    hρ.eigenvalues (1 - largerIndex hρ) = (1 - polarization hρ) / 2 := by
  have hs := eigenvalue_sum hρ htr
  by_cases hle : hρ.eigenvalues 1 ≤ hρ.eigenvalues 0
  · simp only [largerIndex, ite_eq_left hle, show (1 - 0 : Fin 2) = 1 by decide,
      polarization, abs_of_nonneg (sub_nonneg.mpr hle)]
    exact ⟨by linarith only [hs], by linarith only [hs]⟩
  · simp only [largerIndex, ite_eq_right hle, show (1 - 1 : Fin 2) = 0 by decide,
      polarization, abs_of_neg (sub_neg.mpr (lt_of_not_ge hle))]
    exact ⟨by linarith only [hs], by linarith only [hs]⟩

private theorem polarization_mem {ρ : Qubit} (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    polarization hρ.isHermitian ∈ Icc (0 : ℝ) 1 := by
  have hlo := hρ.eigenvalues_nonneg (1 - largerIndex hρ.isHermitian)
  rw [(ordered_eigenvalues hρ.isHermitian htr).2] at hlo
  exact ⟨abs_nonneg _, by linarith only [hlo]⟩

/-- The ordinary Dirichlet trace and the faithful-reference Umegaki trace
are Wu's two normalized expressions on the closed PSD trace-one slice. -/
theorem energy_entropy_eq (h : ℝ) {ρ : Qubit} (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    energy h ρ = normalizedEnergy h (polarization hρ.isHermitian)
      (gibbsAlignment hρ.isHermitian) ∧
    entropy h ρ = normalizedEntropy h (polarization hρ.isHermitian)
      (gibbsAlignment hρ.isHermitian) := by
  let x := hρ.isHermitian.eigenvalues 0
  let y := hρ.isHermitian.eigenvalues 1
  let q := frameWeight hρ.isHermitian 0 0
  obtain ⟨h01, h10, h11⟩ := frame_complements hρ.isHermitian
  have he : energy h ρ = normalizedEnergy h (x - y) (2 * q - 1) :=
    energy_eq_unsorted h hρ htr
  have hs : entropy h ρ = normalizedEntropy h (x - y) (2 * q - 1) :=
    entropy_eq_unsorted h hρ htr
  by_cases hyx : y ≤ x
  · have hv : polarization hρ.isHermitian = x - y := abs_of_nonneg (sub_nonneg.mpr hyx)
    have hz : gibbsAlignment hρ.isHermitian = 2 * q - 1 := by
      rw [gibbsAlignment, largerIndex, ite_eq_left hyx, h10]
      change q - (1 - q) = _
      ring
    rw [hv, hz]
    exact ⟨he, hs⟩
  · have hv : polarization hρ.isHermitian = -(x - y) :=
      abs_of_neg (sub_neg.mpr (lt_of_not_ge hyx))
    have hz : gibbsAlignment hρ.isHermitian = -(2 * q - 1) := by
      rw [gibbsAlignment, largerIndex, ite_eq_right hyx, h01, h11]
      change 1 - q - q = _
      ring
    rw [hv, hz]
    constructor
    · rw [he]
      simp only [normalizedEnergy, spectralRoot, neg_sq]
      ring
    · rw [hs]
      have heven : polarizationEntropy (-(x - y)) = polarizationEntropy (x - y) := by
        unfold polarizationEntropy
        rw [show 1 + -(x - y) = 1 - (x - y) by ring,
          show 1 - -(x - y) = 1 + (x - y) by ring]
        ring
      simp only [normalizedEntropy, heven]
      ring

/-- The sharp two-deficit of the physical observable is nonnegative.
Its equality conditions are expressed in the Gibbs-axis Bloch coordinates. -/
theorem sharp_physical_deficit {h : ℝ} (hh : 0 ≤ h) {ρ : Qubit}
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    0 ≤ energy h ρ - sharpCoefficient h * entropy h ρ ∧
    (energy h ρ - sharpCoefficient h * entropy h ρ = 0 ↔
      polarization hρ.isHermitian = Real.tanh h ∧
      (h = 0 ∨ gibbsAlignment hρ.isHermitian = 1)) := by
  obtain ⟨hE, hS⟩ := energy_entropy_eq h hρ htr
  rw [hE, hS]
  have hv := polarization_mem hρ htr
  exact ⟨normalizedDeficit_nonneg hh hv _, normalizedDeficit_eq_zero_iff hh hv _⟩

private theorem trace_sqrt_eq_affinity {ρ : Qubit} (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    (mpow ρ (1 / 2)).trace.re / Real.sqrt 2 =
      Real.sqrt ((1 + spectralRoot (polarization hρ.isHermitian)) / 2) := by
  let x := hρ.isHermitian.eigenvalues 0
  let y := hρ.isHermitian.eigenvalues 1
  have hx : 0 ≤ x := hρ.eigenvalues_nonneg 0
  have hy : 0 ≤ y := hρ.eigenvalues_nonneg 1
  have hsum : x + y = 1 := eigenvalue_sum hρ.isHermitian htr
  have htrace : (mpow ρ (1 / 2)).trace.re = Real.sqrt x + Real.sqrt y := by
    simpa only [mpow, ← Real.sqrt_eq_rpow, Fin.sum_univ_two, x, y] using
      D5.S3.Resource.LogDet.PathSpectralClassical.trace_cfc_eq_sum ρ hρ.isHermitian Real.sqrt
  have hroot : spectralRoot (polarization hρ.isHermitian) = spectralRoot (x - y) := by
    simp only [polarization, spectralRoot, sq_abs, x, y]
  rw [htrace, hroot, ← Real.sqrt_sq
    (by positivity : 0 ≤ (Real.sqrt x + Real.sqrt y) / Real.sqrt 2)]
  congr 1
  rw [div_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ)),
    show (Real.sqrt x + Real.sqrt y) ^ 2 =
      Real.sqrt x ^ 2 + Real.sqrt y ^ 2 + 2 * (Real.sqrt x * Real.sqrt y) by ring,
    Real.sq_sqrt hx, Real.sq_sqrt hy, hsum, sqrt_product hx hsum]
  ring

/-- At zero inverse temperature, the physical sharp deficit controls the
squared loss of affinity with the tracial Gibbs state. -/
theorem tracial_stability {ρ : Qubit} (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    (4 / 3) * (1 - (mpow ρ (1 / 2)).trace.re / Real.sqrt 2) ^ 2 ≤
      energy 0 ρ - (1 / 2) * entropy 0 ρ := by
  obtain ⟨hE, hS⟩ := energy_entropy_eq 0 hρ htr
  rw [hE, hS, trace_sqrt_eq_affinity hρ htr]
  simpa only [normalizedDeficit, show sharpCoefficient 0 = 1 / 2 by simp [sharpCoefficient]] using
    normalizedDeficit_tracial_stability (polarization_mem hρ htr) (gibbsAlignment hρ.isHermitian)

/-- The physical tracial bound is strict for a density with distinct eigenvalues. -/
theorem tracial_stability_strict {ρ : Qubit} (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hv : 0 < polarization hρ.isHermitian) :
    (4 / 3) * (1 - (mpow ρ (1 / 2)).trace.re / Real.sqrt 2) ^ 2 <
      energy 0 ρ - (1 / 2) * entropy 0 ρ := by
  obtain ⟨hE, hS⟩ := energy_entropy_eq 0 hρ htr
  rw [hE, hS, trace_sqrt_eq_affinity hρ htr]
  simpa only [normalizedDeficit, show sharpCoefficient 0 = 1 / 2 by simp [sharpCoefficient]] using
    normalizedDeficit_tracial_stability_strict (polarization_mem hρ htr) hv
      (gibbsAlignment hρ.isHermitian)

end D5.S3.Quantum.Semigroups.WuQubitSharpTwoPhysical
