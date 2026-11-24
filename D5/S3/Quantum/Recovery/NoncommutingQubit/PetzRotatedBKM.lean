/- GID: D5/S3/Quantum/Recovery/NoncommutingQubit/PetzRotatedBKM
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/NoncommutingQubit/PetzRotatedBKM
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact rotated BKM energy and its weighted bound for a qubit partial-trace Petz pencil. -/

import D5.S3.Divergence.MeanKernels.LogarithmicMeanSandwich
import D5.S3.Quantum.Divergence.UmegakiRareFlagBKM
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Unitary
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Isometry
import D5.S3.Quantum.Recovery.BKMFlagRefinementPetz
import D5.S3.Quantum.Recovery.BKMSpectralVariance
import Mathlib.Tactic

/-!
# Rotated BKM energy of a directed Petz perturbation

The environment has arbitrary finite dimension. An active frequency band orients
the links and makes the two adjoint contributions disjoint entrywise. In the
retained eigenbasis, the two opposite-index weights and the combined equal-index
weight give three logarithmic means for each link.
-/

noncomputable section

open Matrix MeasureTheory
open Complex (normSq)
open scoped BigOperators ComplexOrder Kronecker Matrix MatrixOrder Matrix.Norms.L2Operator

open D5.S3.Divergence.LogDerivTrace (logDeriv logDeriv_integrable)
open D5.S3.Divergence.MeanKernels.LogarithmicMeanSandwich (logMean_kernel_sandwich)
open D5.S3.Quantum.Divergence.UmegakiRareFlagBKM (pair_kernel_eval trace_cross_spectral)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceRight partialTraceRight_add partialTraceRight_kronecker)
open D5.S3.Quantum.Matrix.SpectralPower (mpow)
open D5.S3.Quantum.Recovery.BKMFlagRefinement (lift partialTracePetz)
open D5.S3.Quantum.Recovery.BKMRelativeDensity (omega continuous_mpow)

open private logMean logMean_self logMean_comm logMean_mul_logRatio from
  D5.S3.Quantum.Recovery.BKMSpectralVariance

set_option autoImplicit false

namespace D5.S3.Quantum.Recovery.NoncommutingQubit.PetzRotatedBKM

abbrev Qubit := Matrix (Fin 2) (Fin 2) ℂ
abbrev Joint (ι : Type*) := Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ

local notation "Λ" => logMean

private def diagonalReal {n : Type*} [DecidableEq n] (d : n → ℝ) : Matrix n n ℂ :=
  diagonal fun k => (d k : ℂ)

def population (p : ℝ) (a : Fin 2) : ℝ := if a = 0 then p else 1 - p

@[simp] private theorem population_zero (p : ℝ) : population p 0 = p := rfl
@[simp] private theorem population_one (p : ℝ) : population p 1 = 1 - p := by
  simp [population]

private theorem population_pos {p : ℝ} (hp : 0 < p) (hp' : p < 1) (a : Fin 2) :
    0 < population p a := by
  unfold population
  split_ifs
  · exact hp
  · exact sub_pos.mpr hp'

private def eigenvalue {ι : Type*} (p : ℝ) (g : ι → ℝ) (x : Fin 2 × ι) : ℝ :=
  population p x.1 * g x.2

def frequency {ι : Type*} (q : ℝ) (g : ι → ℝ) (i j : ι) : ℝ :=
  q * g j / ((1 - q) * g i)

/-- An active link strictly descends in the environmental populations. -/
private theorem active_link_ratio {ι : Type*} {q rmin : ℝ} {g : ι → ℝ}
    (hq' : q < 1) (hr : 0 < rmin) (hg : ∀ i, 0 < g i) {i j : ι}
    (hfreq : rmin ≤ frequency q g i j)
    (hsmall : q / ((1 - q) * rmin) < 1) :
    g i / g j ≤ q / ((1 - q) * rmin) ∧ g i < g j := by
  have hq1 : 0 < 1 - q := sub_pos.mpr hq'
  have hmul := (le_div_iff₀ (mul_pos hq1 (hg i))).mp hfreq
  have hratio : g i / g j ≤ q / ((1 - q) * rmin) := by
    apply (div_le_div_iff₀ (hg j) (mul_pos hq1 hr)).mpr
    convert hmul using 1 <;> ring
  exact ⟨hratio, by
    simpa only [one_mul] using (div_lt_iff₀ (hg j)).mp (hratio.trans_lt hsmall)⟩

/-- The true frequency condition rules out both a loop and a reverse active link. -/
private theorem directed_support {ι : Type*} {q rmin : ℝ} {g : ι → ℝ}
    (H : Matrix ι ι ℂ) (hq' : q < 1) (hr : 0 < rmin) (hg : ∀ i, 0 < g i)
    (hband : ∀ i j, H i j ≠ 0 → rmin ≤ frequency q g i j)
    (hsmall : q / ((1 - q) * rmin) < 1) :
    (∀ i, H i i = 0) ∧ (∀ i j, H i j = 0 ∨ H j i = 0) := by
  have hlt (i j : ι) (h : H i j ≠ 0) : g i < g j :=
    (active_link_ratio hq' hr hg (hband i j h) hsmall).2
  constructor
  · intro i
    by_contra h
    exact (lt_irrefl _ (hlt i i h))
  · intro i j
    by_cases h : H i j = 0
    · exact Or.inl h
    · right
      by_contra hrev
      exact (hlt i j h).not_gt (hlt j i hrev)

private theorem mean_scale (c x y : ℝ) (hc : 0 < c) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Λ (c * x) (c * y) = c * Λ x y := by
  have h (t : ℝ) : (c * x) ^ t * (c * y) ^ (1 - t) = c * (x ^ t * y ^ (1 - t)) := by
    rw [Real.mul_rpow hc.le hx, Real.mul_rpow hc.le hy]
    calc
      c ^ t * x ^ t * (c ^ (1 - t) * y ^ (1 - t)) =
          (c ^ t * c ^ (1 - t)) * (x ^ t * y ^ (1 - t)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hc, show t + (1 - t) = 1 by ring, Real.rpow_one]
  simp only [logMean, h, intervalIntegral.integral_const_mul]

private theorem mean_inv_kernel {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (Λ x y)⁻¹ =
      if x = y then 1 / x else (Real.log x - Real.log y) / (x - y) := by
  by_cases hxy : x = y
  · subst y
    simp [logMean_self hx, one_div]
  have hratio : x / y ≠ 1 := by
    intro h
    exact hxy (by simpa using (div_eq_iff hy.ne').mp h)
  have hlog : Real.log (x / y) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (div_pos hx hy) hratio
  have hmean := (eq_div_iff hlog).mpr (logMean_mul_logRatio hx hy)
  rw [hmean, inv_div, Real.log_div hx.ne' hy.ne', if_neg hxy]

/-- The lower retained block of the physical integral logarithmic derivative.
Here `Λ(r,1)` is the logarithmic-mean function `F(r)`, including resonance. -/
def logBlock {ι : Type*} (q : ℝ) (g : ι → ℝ) (H : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => ((Real.sqrt (frequency q g i j) / Λ (frequency q g i j) 1 : ℝ) : ℂ) * H i j

private def raise : Qubit := Matrix.single 1 0 1

private def blocks {ι : Type*} (A : Qubit) (C : Matrix ι ι ℂ) : Joint ι :=
  A ⊗ₖ C + (A ⊗ₖ C)ᴴ

private theorem blocks_hermitian {ι : Type*} (A : Qubit) (C : Matrix ι ι ℂ) :
    (blocks A C).IsHermitian := by
  change (blocks A C)ᴴ = blocks A C
  simp only [blocks, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]

section SpectralTrace

variable {n : Type*} [Fintype n] [DecidableEq n]

private def spectralMatrix (W : Matrix.unitaryGroup n ℂ) (d : n → ℝ) : Matrix n n ℂ :=
  W.val * diagonalReal d * W.valᴴ

private theorem spectralMatrix_posDef (W : Matrix.unitaryGroup n ℂ)
    {d : n → ℝ} (hd : ∀ i, 0 < d i) : (spectralMatrix W d).PosDef := by
  have hdiag : (diagonalReal d).PosDef := Matrix.PosDef.diagonal fun i => by
    exact_mod_cast hd i
  exact (Unitary.isUnit_coe (U := W)).posDef_star_right_conjugate_iff.mpr hdiag

private theorem mpow_spectralMatrix (W : Matrix.unitaryGroup n ℂ)
    {d : n → ℝ} (hd : ∀ i, 0 < d i) (t : ℝ) :
    mpow (spectralMatrix W d) t = spectralMatrix W (fun i => d i ^ t) := by
  have hA := (spectralMatrix_posDef W hd).isHermitian
  rw [mpow, hA.cfc_eq]
  exact hA.cfc_eq_any_unitary (U := W) (D := d) rfl (fun x : ℝ => x ^ t)

private theorem mpow_diagonalReal {d : n → ℝ} (hd : ∀ i, 0 < d i) (t : ℝ) :
    mpow (diagonalReal d) t = diagonalReal (fun i => d i ^ t) := by
  simpa [spectralMatrix] using mpow_spectralMatrix (1 : Matrix.unitaryGroup n ℂ) hd t

/-- The actual BKM trace in any chosen unitary diagonalization. -/
private theorem omega_trace_spectral (W : Matrix.unitaryGroup n ℂ)
    {d : n → ℝ} (hd : ∀ i, 0 < d i) (L : Matrix n n ℂ) (hL : L.IsHermitian) :
    (L * omega (spectralMatrix W d) L).trace.re =
      ∑ i, ∑ j, Λ (d i) (d j) * normSq ((W.valᴴ * L * W.val) i j) := by
  let D := spectralMatrix W d
  let Z := W.valᴴ * L * W.val
  let f : ℝ → Matrix n n ℂ := fun t => mpow D t * L * mpow D (1 - t)
  let T : Matrix n n ℂ →L[ℂ] ℂ :=
    (Matrix.traceLinearMap n ℂ ℂ).toContinuousLinearMap.comp
      (Matrix.mulLeftLinearMap n ℂ L).toContinuousLinearMap
  let term (i j : n) (t : ℝ) : ℂ :=
    ((d i ^ t * d j ^ (1 - t) : ℝ) : ℂ) * (normSq (Z i j) : ℂ)
  have hpow := continuous_mpow D (spectralMatrix_posDef W hd)
  have hsub : Continuous (fun t : ℝ => 1 - t) := continuous_const.sub continuous_id
  have hf : IntervalIntegrable f volume 0 1 :=
    ((hpow.mul continuous_const).mul (hpow.comp hsub)).intervalIntegrable 0 1
  have hpoint (t : ℝ) : T (f t) = ∑ i, ∑ j, term i j t := by
    change (L * (mpow D t * L * mpow D (1 - t))).trace = _
    have hcyc : (L * (mpow D t * L * mpow D (1 - t))).trace =
        (L * mpow D (1 - t) * Lᴴ * mpow D t).trace := by
      rw [show Lᴴ = L from hL]
      simpa only [Matrix.mul_assoc] using
        Matrix.trace_mul_comm (L * mpow D t) (L * mpow D (1 - t))
    rw [hcyc]
    dsimp only [D]
    rw [mpow_spectralMatrix W hd, mpow_spectralMatrix W hd]
    simpa only [term, spectralMatrix, diagonalReal, Complex.ofReal_mul, Z] using
      trace_cross_spectral L W.val W.val
        (fun i => (d i ^ t : ℝ)) (fun j => (d j ^ (1 - t) : ℝ))
  have hterm (i j : n) : Continuous (term i j) := by
    have hi := Real.continuous_const_rpow (hd i).ne'
    have hj := (Real.continuous_const_rpow (hd j).ne').comp hsub
    exact (Complex.continuous_ofReal.comp (hi.mul hj)).mul continuous_const
  have hsum (i : n) :
      (∫ t : ℝ in 0..1, ∑ j, term i j t) = ∑ j, ∫ t : ℝ in 0..1, term i j t :=
    intervalIntegral.integral_finsetSum fun j _ => (hterm i j).intervalIntegrable 0 1
  have houter :
      (∫ t : ℝ in 0..1, ∑ i, ∑ j, term i j t) =
        ∑ i, ∫ t : ℝ in 0..1, ∑ j, term i j t :=
    intervalIntegral.integral_finsetSum fun i _ =>
      (continuous_finsetSum _ fun j _ => hterm i j).intervalIntegrable 0 1
  have hscalar (i j : n) :
      (∫ t : ℝ in 0..1, term i j t) = ((Λ (d i) (d j) * normSq (Z i j) : ℝ) : ℂ) := by
    simp only [term, intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
      ← Complex.ofReal_mul, logMean]
  change (T (∫ t : ℝ in 0..1, f t)).re = _
  rw [← T.intervalIntegral_comp_comm hf]
  simp only [hpoint, houter, hsum, hscalar, Complex.re_sum, Complex.ofReal_re, Z]

end SpectralTrace

section PhysicalLog

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The physical reference `Σ = Q ⊗ γ`. -/
def reference (q : ℝ) (g : ι → ℝ) : Joint ι := diagonalReal (eigenvalue q g)

/-- The tangent of `√Σ (1 + s U) √Σ`, with `U = E₁₀ ⊗ H + (E₁₀ ⊗ H)ᴴ`. -/
def pencilTangent (q : ℝ) (g : ι → ℝ) (H : Matrix ι ι ℂ) : Joint ι :=
  blocks raise fun i j =>
    ((Real.sqrt ((1 - q) * g i) * Real.sqrt (q * g j) : ℝ) : ℂ) * H i j

private theorem pencilTangent_eq_physical {q : ℝ} {g : ι → ℝ}
    (hq : 0 < q) (hq' : q < 1) (hg : ∀ i, 0 < g i) (H : Matrix ι ι ℂ) :
    pencilTangent q g H =
      mpow (reference q g) (1 / 2) * blocks raise H * mpow (reference q g) (1 / 2) := by
  have hd (x : Fin 2 × ι) : 0 < eigenvalue q g x :=
    mul_pos (population_pos hq hq' x.1) (hg x.2)
  have hsqrt : mpow (reference q g) (1 / 2) =
      diagonalReal (fun x => Real.sqrt (eigenvalue q g x)) := by
    simpa only [reference, Real.sqrt_eq_rpow] using mpow_diagonalReal hd (1 / 2)
  rw [hsqrt]
  apply Matrix.ext
  rintro ⟨a, i⟩ ⟨b, j⟩
  fin_cases a <;> fin_cases b <;>
    simp [pencilTangent, blocks, raise, Matrix.single, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.kronecker_apply, Matrix.conjTranspose_apply, diagonalReal, eigenvalue,
      Complex.star_def, Complex.ofReal_mul] <;>
    ring

/-- The pencil `Σ + s • pencilTangent` has physical marginal `Q` at every s. -/
private theorem pencil_marginal_of_band {q rmin : ℝ} {g : ι → ℝ}
    (H : Matrix ι ι ℂ) (hq' : q < 1) (hr : 0 < rmin) (hg : ∀ i, 0 < g i)
    (hnorm : ∑ i, g i = 1)
    (hband : ∀ i j, H i j ≠ 0 → rmin ≤ frequency q g i j)
    (hsmall : q / ((1 - q) * rmin) < 1) (s : ℝ) :
    partialTraceRight (reference q g + s • pencilTangent q g H) =
      diagonalReal (population q) := by
  have hdiag := (directed_support H hq' hr hg hband hsmall).1
  have hprod : reference q g = diagonalReal (population q) ⊗ₖ diagonalReal g := by
    simp only [reference, diagonalReal, Matrix.diagonal_kronecker_diagonal, eigenvalue,
      Complex.ofReal_mul]
  have ht : (diagonalReal g).trace = 1 := by
    simp only [diagonalReal, Matrix.trace_diagonal]
    exact_mod_cast hnorm
  rw [partialTraceRight_add, hprod, partialTraceRight_kronecker, ht, one_smul]
  have hz : partialTraceRight (s • pencilTangent q g H) = 0 := by
    apply Matrix.ext
    intro a b
    simp [partialTraceRight, pencilTangent, blocks, Matrix.kronecker_apply,
      Matrix.conjTranspose_apply, hdiag]
  rw [hz, add_zero]

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private theorem logDeriv_diagonal_apply (d : Fin 2 × ι → ℝ) (hd : ∀ x, 0 < d x)
    (X : Joint ι) (i j : Fin 2 × ι) :
    logDeriv (diagonalReal d) X i j = (((Λ (d i) (d j))⁻¹ : ℝ) : ℂ) * X i j := by
  let A := diagonalReal d
  let E : Joint ι →L[ℂ] ℂ :=
    (Matrix.entryLinearMap ℂ ℂ i j).toContinuousLinearMap
  have hA : A.PosDef := Matrix.PosDef.diagonal fun k => by exact_mod_cast hd k
  have hres (t : ℝ) (ht : 0 < t) : (A + t • 1)⁻¹ =
      diagonal fun k => (((d k + t : ℝ) : ℂ)⁻¹) := by
    have hdiag : A + t • 1 = diagonalReal (fun k => d k + t) := by
      apply Matrix.ext
      intro k l
      by_cases h : k = l <;>
        simp [A, diagonalReal, h, Matrix.one_apply, Complex.real_smul, Complex.ofReal_add]
    rw [hdiag]
    apply Matrix.inv_eq_right_inv
    rw [diagonalReal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    exact mul_inv_cancel₀ (by exact_mod_cast (add_pos (hd k) ht).ne')
  have hpoint (t : ℝ) (ht : 0 < t) :
      E ((A + t • 1)⁻¹ * X * (A + t • 1)⁻¹) =
        ((1 / ((d i + t) * (d j + t)) : ℝ) : ℂ) * X i j := by
    change ((A + t • 1)⁻¹ * X * (A + t • 1)⁻¹) i j = _
    rw [hres t ht, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [one_div, Complex.ofReal_inv, Complex.ofReal_mul, mul_inv_rev]
    ac_rfl
  change E (∫ t in Set.Ioi (0 : ℝ), (A + t • 1)⁻¹ * X * (A + t • 1)⁻¹) = _
  rw [← E.integral_comp_comm (logDeriv_integrable A X hA)]
  calc
    _ = ∫ t in Set.Ioi (0 : ℝ), ((1 / ((d i + t) * (d j + t)) : ℝ) : ℂ) * X i j := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hpoint t ht
    _ = _ := by
      rw [integral_mul_const, integral_complex_ofReal, pair_kernel_eval _ _ (hd i) (hd j),
        mean_inv_kernel (hd i) (hd j)]

private theorem lower_log_coefficient {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (Λ x y)⁻¹ * (Real.sqrt x * Real.sqrt y) = Real.sqrt (y / x) / Λ (y / x) 1 := by
  have hprod : x * (y / x) = y := by field_simp [hx.ne']
  have hmean := mean_scale x (y / x) 1 hx (div_nonneg hy.le hx.le) zero_le_one
  rw [hprod, mul_one, logMean_comm y x] at hmean
  have hcancel : x⁻¹ * Real.sqrt x = (Real.sqrt x)⁻¹ := by
    field_simp [hx.ne', (Real.sqrt_pos.2 hx).ne']
    nlinarith only [Real.sq_sqrt hx.le]
  calc
    _ = (x⁻¹ * Real.sqrt x) * Real.sqrt y * (Λ (y / x) 1)⁻¹ := by
      rw [hmean, mul_inv_rev]
      ring
    _ = _ := by
      rw [hcancel, Real.sqrt_div hy.le]
      ring

/-- The spectral block is obtained from the actual resolvent logarithmic derivative
of the physical square-root pencil. -/
private theorem logDeriv_pencilTangent {q : ℝ} {g : ι → ℝ} (H : Matrix ι ι ℂ)
    (hq : 0 < q) (hq' : q < 1) (hg : ∀ i, 0 < g i) :
    logDeriv (reference q g) (pencilTangent q g H) = blocks raise (logBlock q g H) := by
  have hd (x : Fin 2 × ι) : 0 < eigenvalue q g x :=
    mul_pos (population_pos hq hq' x.1) (hg x.2)
  have hscale (i j : ι) :
      (Λ ((1 - q) * g i) (q * g j))⁻¹ *
        (Real.sqrt ((1 - q) * g i) * Real.sqrt (q * g j)) =
      Real.sqrt (frequency q g i j) / Λ (frequency q g i j) 1 :=
    lower_log_coefficient (mul_pos (sub_pos.mpr hq') (hg i)) (mul_pos hq (hg j))
  have hcast (i j : ι) :
      (((Λ ((1 - q) * g i) (q * g j))⁻¹ : ℝ) : ℂ) *
        ((Real.sqrt ((1 - q) * g i) * Real.sqrt (q * g j) : ℝ) : ℂ) =
      ((Real.sqrt (frequency q g i j) / Λ (frequency q g i j) 1 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, hscale]
  apply Matrix.ext
  rintro ⟨a, i⟩ ⟨b, j⟩
  rw [reference, logDeriv_diagonal_apply _ hd]
  fin_cases a <;> fin_cases b <;>
    simp [pencilTangent, logBlock, blocks, raise, Matrix.single, Matrix.kronecker_apply,
      Matrix.conjTranspose_apply, eigenvalue, Complex.star_def,
      -Complex.ofReal_mul, -Complex.ofReal_inv, -Complex.ofReal_div,
      ← mul_assoc, hcast, logMean_comm (q * g i) ((1 - q) * g j)]

end PhysicalLog

section Rotation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The retained input density tensored with the diagonal environment. -/
def retainedDensity (V : Matrix.unitaryGroup (Fin 2) ℂ) (p : ℝ) (g : ι → ℝ) : Joint ι :=
  (V.val * diagonalReal (population p) * V.valᴴ) ⊗ₖ diagonalReal g

/-- For the same pencil, the physical partial-trace Petz output is the
square-root sandwich with the input `D = τ ⊗ γ` from the BKM identity. -/
private theorem partialTracePetz_pencil_of_band (V : Matrix.unitaryGroup (Fin 2) ℂ)
    {q rmin : ℝ} {g : ι → ℝ} (H : Matrix ι ι ℂ) (p s : ℝ)
    (hq : 0 < q) (hq' : q < 1) (hr : 0 < rmin) (hg : ∀ i, 0 < g i)
    (hnorm : ∑ i, g i = 1)
    (hband : ∀ i j, H i j ≠ 0 → rmin ≤ frequency q g i j)
    (hsmall : q / ((1 - q) * rmin) < 1) :
    let τ := V.val * diagonalReal (population p) * V.valᴴ
    let σ := reference q g + s • pencilTangent q g H
    let S := mpow σ (1 / 2)
    let R := mpow (reference q g) (-(1 / 2))
    partialTracePetz σ τ = S * (R * retainedDensity V p g * R) * S := by
  let t : ℝ := -(1 / 2)
  let G := diagonalReal (fun i => g i ^ t)
  let A := diagonalReal (fun a => population q a ^ t)
  have hd (x : Fin 2 × ι) : 0 < eigenvalue q g x :=
    mul_pos (population_pos hq hq' x.1) (hg x.2)
  have hR : mpow (reference q g) t = A ⊗ₖ G := by
    rw [reference, mpow_diagonalReal hd t]
    simp only [A, G, diagonalReal, Matrix.diagonal_kronecker_diagonal]
    congr 1
    funext x
    simp only [eigenvalue, Real.mul_rpow (population_pos hq hq' x.1).le (hg x.2).le,
      Complex.ofReal_mul]
  have hG : G * diagonalReal g * G = 1 := by
    unfold G diagonalReal
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext i
    have hi : g i ^ t * g i * g i ^ t = 1 := by
      calc
        _ = g i ^ t * g i ^ (1 : ℝ) * g i ^ t := by rw [Real.rpow_one]
        _ = _ := by
          rw [← Real.rpow_add (hg i), ← Real.rpow_add (hg i),
            show t + 1 + t = 0 by norm_num [t], Real.rpow_zero]
    exact_mod_cast hi
  dsimp only
  rw [partialTracePetz, pencil_marginal_of_band H hq' hr hg hnorm hband hsmall s]
  change _ * lift (ι := ι) (mpow (diagonalReal (population q)) t * _ *
    mpow (diagonalReal (population q)) t) * _ =
      _ * (mpow (reference q g) t * retainedDensity V p g * mpow (reference q g) t) * _
  rw [mpow_diagonalReal (population_pos hq hq') t, hR, retainedDensity, lift,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hG]

private def jointRotation (V : Matrix.unitaryGroup (Fin 2) ℂ) (ι : Type*)
    [Fintype ι] [DecidableEq ι] : Matrix.unitaryGroup (Fin 2 × ι) ℂ :=
  Matrix.unitary_kron V (1 : Matrix.unitaryGroup ι ℂ)

private theorem jointRotation_val (V : Matrix.unitaryGroup (Fin 2) ℂ) :
    (jointRotation V ι).val = V.val ⊗ₖ (1 : Matrix ι ι ℂ) := rfl

private theorem retainedDensity_eq_spectral (V : Matrix.unitaryGroup (Fin 2) ℂ)
    (p : ℝ) (g : ι → ℝ) :
    retainedDensity V p g = spectralMatrix (jointRotation V ι) (eigenvalue p g) := by
  have hdiag : diagonalReal (eigenvalue p g) = diagonalReal (population p) ⊗ₖ diagonalReal g := by
    simp only [diagonalReal, Matrix.diagonal_kronecker_diagonal, eigenvalue, Complex.ofReal_mul]
  rw [retainedDensity, spectralMatrix, jointRotation_val, hdiag, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one]

private theorem rotate_blocks (V : Matrix.unitaryGroup (Fin 2) ℂ) (A : Qubit)
    (C : Matrix ι ι ℂ) :
    (jointRotation V ι).valᴴ * blocks A C * (jointRotation V ι).val =
      blocks (V.valᴴ * A * V.val) C := by
  let W := (jointRotation V ι).val
  have hone : Wᴴ * (A ⊗ₖ C) * W = (V.valᴴ * A * V.val) ⊗ₖ C := by
    dsimp only [W]
    rw [jointRotation_val, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  have hadj : Wᴴ * (A ⊗ₖ C)ᴴ * W = (Wᴴ * (A ⊗ₖ C) * W)ᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  change Wᴴ * blocks A C * W = _
  unfold blocks
  rw [Matrix.mul_add, Matrix.add_mul, hone, hadj, hone]

/-- The squared overlap defect of the designated first eigenvector. -/
def rotationWeight (V : Matrix.unitaryGroup (Fin 2) ℂ) : ℝ :=
  1 - normSq (V.val 0 0)

private theorem rotated_raise_entry (V : Matrix.unitaryGroup (Fin 2) ℂ) (a b : Fin 2) :
    (V.valᴴ * raise * V.val) a b = star (V.val 1 a) * V.val 0 b := by
  simp [raise, Matrix.single, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_two]

private theorem retained_sum (V : Matrix.unitaryGroup (Fin 2) ℂ) {p x y : ℝ}
    (hp : 0 < p) (hp' : p < 1) (hx : 0 < x) (hy : 0 < y) :
    (∑ a : Fin 2, ∑ b : Fin 2, Λ (population p a * x) (population p b * y) *
      normSq ((V.valᴴ * raise * V.val) a b)) =
      (1 - rotationWeight V) ^ 2 * Λ ((1 - p) * x) (p * y) +
      rotationWeight V ^ 2 * Λ (p * x) ((1 - p) * y) +
      rotationWeight V * (1 - rotationWeight V) * Λ x y := by
  have hrow := Matrix.unitary_row_sum_norm_sq V.val (Unitary.coe_mul_star_self V) 0
  have hcol0 := Matrix.unitary_col_sum_norm_sq V.val (Unitary.coe_star_mul_self V) 0
  have hcol1 := Matrix.unitary_col_sum_norm_sq V.val (Unitary.coe_star_mul_self V) 1
  simp only [Fin.sum_univ_two, Complex.sq_norm] at hrow hcol0 hcol1
  have h00 : normSq (V.val 0 0) = 1 - rotationWeight V := by unfold rotationWeight; ring
  have h01 : normSq (V.val 0 1) = rotationWeight V := by unfold rotationWeight; linarith
  have h10 : normSq (V.val 1 0) = rotationWeight V := by unfold rotationWeight; linarith
  have h11 : normSq (V.val 1 1) = 1 - rotationWeight V := by linarith only [hcol1, h01]
  simp only [Fin.sum_univ_two, population_zero, population_one, rotated_raise_entry,
    Complex.normSq_mul, Complex.star_def, Complex.normSq_conj, h00, h01, h10, h11,
    mean_scale p x y hp hx.le hy.le, mean_scale (1 - p) x y (sub_pos.mpr hp') hx.le hy.le]
  ring

/-- The reversed orientation doubles the same weighted sum. The disjointness
hypothesis is used at the level of each complex joint entry. -/
private theorem directed_spectral_sum (d : Fin 2 × ι → ℝ) (A : Qubit) (C : Matrix ι ι ℂ)
    (hs : ∀ i j, C i j = 0 ∨ C j i = 0) :
    (∑ x : Fin 2 × ι, ∑ y : Fin 2 × ι, Λ (d x) (d y) * normSq (blocks A C x y)) / 2 =
      ∑ i : ι, ∑ j : ι, normSq (C i j) *
        (∑ a : Fin 2, ∑ b : Fin 2, Λ (d (a, i)) (d (b, j)) * normSq (A a b)) := by
  let term (x y : Fin 2 × ι) : ℝ :=
    Λ (d x) (d y) * (normSq (A x.1 y.1) * normSq (C x.2 y.2))
  have hentry (x y : Fin 2 × ι) :
      Λ (d x) (d y) * normSq (blocks A C x y) = term x y + term y x := by
    rcases x with ⟨a, i⟩
    rcases y with ⟨b, j⟩
    simp only [term, blocks, Matrix.kronecker_apply, Matrix.add_apply, Matrix.conjTranspose_apply]
    rw [logMean_comm (d (b, j)) (d (a, i))]
    rcases hs i j with h | h <;>
      simp [h, Complex.star_def, Complex.normSq_conj, Complex.normSq_mul]
  simp_rw [hentry, Finset.sum_add_distrib]
  have hreverse : (∑ x, ∑ y, term y x) = ∑ x, ∑ y, term x y := Finset.sum_comm
  rw [hreverse, ← two_mul, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [Fintype.sum_prod_type_right, term, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Exact rotated BKM trace of the physical logarithmic tangent. The first two
means couple opposite retained indices. Homogeneity combines the equal-retained
terms into the single environmental logarithmic mean. -/
private theorem rotated_bkm_of_band (V : Matrix.unitaryGroup (Fin 2) ℂ)
    {p q rmin : ℝ} {g : ι → ℝ} (H : Matrix ι ι ℂ)
    (hp : 0 < p) (hp' : p < 1) (hq : 0 < q) (hq' : q < 1)
    (hr : 0 < rmin) (hg : ∀ i, 0 < g i)
    (hband : ∀ i j, H i j ≠ 0 → rmin ≤ frequency q g i j)
    (hsmall : q / ((1 - q) * rmin) < 1) :
    let w := rotationWeight V
    let L := logDeriv (reference q g) (pencilTangent q g H)
    (L * omega (retainedDensity V p g) L).trace.re / 2 =
      ∑ i, ∑ j, normSq (logBlock q g H i j) *
        ((1 - w) ^ 2 * Λ ((1 - p) * g i) (p * g j) +
          w ^ 2 * Λ (p * g i) ((1 - p) * g j) +
          w * (1 - w) * Λ (g i) (g j)) := by
  dsimp only
  have hd (x : Fin 2 × ι) : 0 < eigenvalue p g x :=
    mul_pos (population_pos hp hp' x.1) (hg x.2)
  let C := logBlock q g H
  have hs (i j : ι) : C i j = 0 ∨ C j i = 0 := by
    rcases (directed_support H hq' hr hg hband hsmall).2 i j with hij | hji
    · exact Or.inl (by simp [C, logBlock, hij])
    · exact Or.inr (by simp [C, logBlock, hji])
  rw [logDeriv_pencilTangent H hq hq' hg, retainedDensity_eq_spectral,
    omega_trace_spectral _ hd _ (blocks_hermitian raise C), rotate_blocks,
    directed_spectral_sum _ _ _ hs]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show (∑ a : Fin 2, ∑ b : Fin 2, Λ (eigenvalue p g (a, i)) (eigenvalue p g (b, j)) *
      normSq ((V.valᴴ * raise * V.val) a b)) = _ from retained_sum V hp hp' (hg i) (hg j)]

private theorem mean_le_arith {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Λ x y ≤ (x + y) / 2 := by
  by_cases hxy : x = y
  · subst y
    rw [logMean_self hx]
    linarith
  have hkernel := (logMean_kernel_sandwich hx hy hxy).1
  have hpos : 0 < 2 / (x + y) := div_pos (by norm_num) (add_pos hx hy)
  have h := inv_anti₀ hpos hkernel
  have hmean := mean_inv_kernel hx hy
  rw [if_neg hxy] at hmean
  rw [← hmean, inv_inv, inv_div] at h
  exact h

/-- Arithmetic upper bound for the finite weighted sum, with the physical
retained populations. The population of the physical `|0⟩` is
`P = p(1-w)+(1-p)w`. -/
private theorem rotated_bkm_le_weighted_sum (V : Matrix.unitaryGroup (Fin 2) ℂ)
    {p q rmin : ℝ} {g : ι → ℝ} (H : Matrix ι ι ℂ)
    (hp : 0 < p) (hp' : p < 1) (hq : 0 < q) (hq' : q < 1)
    (hr : 0 < rmin) (hg : ∀ i, 0 < g i)
    (hband : ∀ i j, H i j ≠ 0 → rmin ≤ frequency q g i j)
    (hsmall : q / ((1 - q) * rmin) < 1) :
    let w := rotationWeight V
    let P := p * (1 - w) + (1 - p) * w
    let L := logDeriv (reference q g) (pencilTangent q g H)
    (L * omega (retainedDensity V p g) L).trace.re / 2 ≤
      ∑ i, ∑ j, normSq (logBlock q g H i j) * (((1 - P) * g i + P * g j) / 2) := by
  dsimp only
  rw [rotated_bkm_of_band V H hp hp' hq hq' hr hg hband hsmall]
  let w := rotationWeight V
  let P := p * (1 - w) + (1 - p) * w
  have hrow := Matrix.unitary_row_sum_norm_sq V.val (Unitary.coe_mul_star_self V) 0
  simp only [Fin.sum_univ_two, Complex.sq_norm] at hrow
  have hw : 0 ≤ w := by
    dsimp [w, rotationWeight]
    linarith only [hrow, Complex.normSq_nonneg (V.val 0 1)]
  have hw' : 0 ≤ 1 - w := by
    dsimp [w, rotationWeight]
    linarith only [Complex.normSq_nonneg (V.val 0 0)]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_left ?_ (Complex.normSq_nonneg _)
  have ha := mul_le_mul_of_nonneg_left
    (mean_le_arith (mul_pos (sub_pos.mpr hp') (hg i)) (mul_pos hp (hg j))) (sq_nonneg (1 - w))
  have hb := mul_le_mul_of_nonneg_left
    (mean_le_arith (mul_pos hp (hg i)) (mul_pos (sub_pos.mpr hp') (hg j))) (sq_nonneg w)
  have hc := mul_le_mul_of_nonneg_left (mean_le_arith (hg i) (hg j)) (mul_nonneg hw hw')
  calc
    _ ≤ (1 - w) ^ 2 * (((1 - p) * g i + p * g j) / 2) +
        w ^ 2 * ((p * g i + (1 - p) * g j) / 2) +
        w * (1 - w) * ((g i + g j) / 2) := add_le_add (add_le_add ha hb) hc
    _ = ((1 - P) * g i + P * g j) / 2 := by dsimp only [P]; ring

end Rotation

end D5.S3.Quantum.Recovery.NoncommutingQubit.PetzRotatedBKM
