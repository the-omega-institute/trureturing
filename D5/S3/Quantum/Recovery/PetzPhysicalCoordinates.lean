import D5.S3.Quantum.Recovery.PetzPhysicalAmplitude
import D5.S3.Quantum.Recovery.PetzExponentialBoundaryEvaluation
import Mathlib.Data.Matrix.Basis

/-!
# Physical coordinates for the Petz boundary

The mixed basis uses the eigenvectors of the full reference state on the left
and those of the full input state on the right. Each coordinate has outer
modular ratio `σᵢ / ρⱼ`. Each pair of retained eigenvectors contributes through
the ordered product of its two rank-one projectors. Equal eigenvalues and
equal ratios are allowed throughout.
-/

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory
open scoped BigOperators ComplexOrder Kronecker MatrixOrder Matrix.Norms.Frobenius
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open D5.S3.Quantum.Divergence.UmegakiReferenceTransport (partialTraceRight_posDef)
open D5.S3.Quantum.GNSMatrix (frobenius_norm_sq_eq_trace)
open PetzPhysicalAmplitude PetzExponentialBoundaryEvaluation

namespace PetzPhysicalCoordinates

section Spectral

variable {n : Type*} [Fintype n] [DecidableEq n] {X Y : Matrix n n ℂ}

/-- Project onto one column of the eigenvector unitary used by the physical power. -/
def rankOneProjector (hX : X.PosDef) (i : n) : Matrix n n ℂ :=
  Unitary.conjStarAlgAut ℂ _ hX.isHermitian.eigenvectorUnitary (Matrix.single i i 1)

/-- The projector is the outer product of the chosen unit eigenvector with itself. -/
theorem rankOneProjector_apply (hX : X.PosDef) (i a b : n) :
    rankOneProjector hX i a b =
      hX.isHermitian.eigenvectorUnitary a i * star (hX.isHermitian.eigenvectorUnitary b i) := by
  simp only [rankOneProjector, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc]
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [Matrix.single_mul_apply_same, one_mul, Matrix.star_apply]
  · intro j _ hj
    rw [Matrix.single_mul_apply_of_ne _ i i j b hj, mul_zero]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

theorem rankOneProjector_isHermitian (hX : X.PosDef) (i : n) :
    (rankOneProjector hX i).IsHermitian := by
  change star (rankOneProjector hX i) = rankOneProjector hX i
  unfold rankOneProjector
  rw [← map_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, star_one]

theorem rankOneProjector_mul (hX : X.PosDef) (i j : n) :
    rankOneProjector hX i * rankOneProjector hX j =
      if i = j then rankOneProjector hX i else 0 := by
  by_cases hij : i = j
  · rw [ite_eq_left hij]
    subst j
    simp only [rankOneProjector, ← map_mul, Matrix.single_mul_single_same, one_mul]
  · rw [ite_eq_right hij]
    have hZero : Matrix.single i i (1 : ℂ) * Matrix.single j j 1 = 0 :=
      Matrix.single_mul_single_of_ne (1 : ℂ) i i j hij (1 : ℂ)
    simp only [rankOneProjector, ← map_mul, hZero, map_zero]

theorem spectralCPow_eq_sum_rankOneProjector (hX : X.PosDef) (z : ℂ) :
    spectralCPow hX z =
      ∑ i : n, ((hX.isHermitian.eigenvalues i : ℂ) ^ z) • rankOneProjector hX i := by
  unfold spectralCPow rankOneProjector
  rw [← Matrix.sum_single_eq_diagonal, map_sum]
  simp only [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

theorem sum_rankOneProjector (hX : X.PosDef) : (∑ i : n, rankOneProjector hX i) = 1 := by
  simpa only [spectralCPow_zero, Complex.cpow_zero, one_smul] using
    (spectralCPow_eq_sum_rankOneProjector hX 0).symm

/-- Expand two powers in their separate eigenbases, preserving the order of the
projector product even when the matrices fail to commute. -/
theorem spectralCPow_mul_eq_sum_rankOneProjector (hX : X.PosDef) (hY : Y.PosDef) (z w : ℂ) :
    spectralCPow hX z * spectralCPow hY w =
      ∑ k : n × n,
        ((hX.isHermitian.eigenvalues k.1 : ℂ) ^ z * (hY.isHermitian.eigenvalues k.2 : ℂ) ^ w) •
          (rankOneProjector hX k.1 * rankOneProjector hY k.2) := by
  rw [spectralCPow_eq_sum_rankOneProjector hX z, spectralCPow_eq_sum_rankOneProjector hY w,
    Fintype.sum_prod_type, Matrix.sum_mul]
  simp only [Matrix.smul_mul, Matrix.mul_sum, Matrix.mul_smul, smul_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [_root_.mul_comm ((hY.isHermitian.eigenvalues j : ℂ) ^ w)
    ((hX.isHermitian.eigenvalues i : ℂ) ^ z)]

/-- Mixed orthonormal coordinates `Uσᴴ * M * Uρ`. -/
def mixedCoordinates (hρ : X.PosDef) (hσ : Y.PosDef) (M : Matrix n n ℂ) : Matrix n n ℂ :=
  star (hσ.isHermitian.eigenvectorUnitary : Matrix n n ℂ) * M *
    (hρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)

private theorem mixedCoordinates_sub (hρ : X.PosDef) (hσ : Y.PosDef) (M N : Matrix n n ℂ) :
    mixedCoordinates hρ hσ (M - N) = mixedCoordinates hρ hσ M - mixedCoordinates hρ hσ N := by
  simp only [mixedCoordinates, Matrix.mul_sub, Matrix.sub_mul]

/-- Left and right powers become independent diagonal powers in the mixed basis. -/
theorem mixedCoordinates_mul_spectralCPow (hρ : X.PosDef) (hσ : Y.PosDef)
    (M : Matrix n n ℂ) (z w : ℂ) :
    mixedCoordinates hρ hσ (spectralCPow hσ z * M * spectralCPow hρ w) =
      diagonal (fun i => (hσ.isHermitian.eigenvalues i : ℂ) ^ z) * mixedCoordinates hρ hσ M *
        diagonal (fun j => (hρ.isHermitian.eigenvalues j : ℂ) ^ w) := by
  let Uσ := hσ.isHermitian.eigenvectorUnitary
  let Uρ := hρ.isHermitian.eigenvectorUnitary
  have hLeft :
      star (Uσ : Matrix n n ℂ) * spectralCPow hσ z =
        diagonal (fun i => (hσ.isHermitian.eigenvalues i : ℂ) ^ z) * star (Uσ : Matrix n n ℂ) := by
    change star (Uσ : Matrix n n ℂ) *
      Unitary.conjStarAlgAut ℂ _ Uσ (diagonal (fun i => (hσ.isHermitian.eigenvalues i : ℂ) ^ z)) =
        _
    rw [Unitary.conjStarAlgAut_apply, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Unitary.coe_star_mul_self, Matrix.one_mul]
  have hRight :
      spectralCPow hρ w * (Uρ : Matrix n n ℂ) =
        (Uρ : Matrix n n ℂ) * diagonal (fun j => (hρ.isHermitian.eigenvalues j : ℂ) ^ w) := by
    change Unitary.conjStarAlgAut ℂ _ Uρ
      (diagonal (fun j => (hρ.isHermitian.eigenvalues j : ℂ) ^ w)) * (Uρ : Matrix n n ℂ) = _
    rw [Unitary.conjStarAlgAut_apply, Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.mul_one]
  calc
    _ = (star (Uσ : Matrix n n ℂ) * spectralCPow hσ z) * M *
        (spectralCPow hρ w * (Uρ : Matrix n n ℂ)) := by
      simp only [mixedCoordinates, Uσ, Uρ, Matrix.mul_assoc]
    _ = _ := by
      rw [hLeft, hRight]
      simp only [mixedCoordinates, Uσ, Uρ, Matrix.mul_assoc]

/-- The mixed change of basis preserves the physical Hilbert–Schmidt norm. -/
theorem mixedCoordinates_frobenius_norm (hρ : X.PosDef) (hσ : Y.PosDef) (M : Matrix n n ℂ) :
    ‖mixedCoordinates hρ hσ M‖ = ‖M‖ := by
  let U : Matrix n n ℂ := hσ.isHermitian.eigenvectorUnitary
  let V : Matrix n n ℂ := hρ.isHermitian.eigenvectorUnitary
  have hU : U * star U = 1 := Unitary.coe_mul_star_self hσ.isHermitian.eigenvectorUnitary
  have hV : V * star V = 1 := Unitary.coe_mul_star_self hρ.isHermitian.eigenvectorUnitary
  have hTrace : (star (star U * M * V) * (star U * M * V)).trace = (star M * M).trace := by
    calc
      _ = (star V * (star M * (U * star U) * M) * V).trace := by
        simp only [star_mul, star_star, Matrix.mul_assoc]
      _ = (star V * (star M * M) * V).trace := by rw [hU, Matrix.mul_one]
      _ = (V * star V * (star M * M)).trace := Matrix.trace_mul_cycle _ _ _
      _ = _ := by rw [hV, Matrix.one_mul]
  have hSq : ((‖mixedCoordinates hρ hσ M‖ ^ 2 : ℝ) : ℂ) = ((‖M‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [frobenius_norm_sq_eq_trace, ← Matrix.star_eq_conjTranspose, mixedCoordinates,
      U, V] using hTrace
  have hReal := congrArg Complex.re hSq
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by
    simpa only [Complex.ofReal_re] using hReal)

end Spectral

section Scalars

/-- The four scalar powers combine into the quotient of the full and retained modular ratios. -/
theorem modular_ratio_cpow {x y q p : ℝ} (hx : 0 < x) (hy : 0 < y) (hq : 0 < q) (hp : 0 < p)
    (z : ℂ) :
    (x : ℂ) ^ z * ((q : ℂ) ^ (-z) * (p : ℂ) ^ z) * (y : ℂ) ^ (-z) =
      (((x / y) / (q / p) : ℝ) : ℂ) ^ z := by
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg (div_nonneg hx.le hy.le)
    (div_nonneg hq.le hp.le), Complex.ofReal_div, Complex.ofReal_div,
    Complex.div_cpow_ofReal_nonneg hx.le hy.le, Complex.div_cpow_ofReal_nonneg hq.le hp.le]
  simp only [Complex.cpow_neg, div_eq_mul_inv, _root_.mul_inv_rev, inv_inv]
  ac_rfl

/-- A positive base contributes its positive square root and the upper-boundary phase. -/
theorem positive_cpow_upper {x : ℝ} (hx : 0 < x) (s : ℝ) :
    (x : ℂ) ^ upperExponent s =
      (Real.sqrt x : ℂ) * Complex.exp (Complex.I * (Real.log x : ℂ) * (s : ℂ)) := by
  have hx' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hPhase : (x : ℂ) ^ ((s : ℂ) * Complex.I) =
      Complex.exp (Complex.I * (Real.log x : ℂ) * (s : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hx', ← Complex.ofReal_log hx.le]
    apply congrArg Complex.exp
    ring
  rw [upperExponent, Complex.cpow_add _ _ hx', ← Complex.ofReal_cpow hx.le,
    ← Real.sqrt_eq_rpow, hPhase]

end Scalars

section PartialTrace

universe u

variable {A B : Type u} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Nonempty B]
variable {ρ σ τ : Matrix (A × B) (A × B) ℂ}

private theorem marginalPosDef (hτ : τ.PosDef) : (partialTraceRight τ).PosDef :=
  partialTraceRight_posDef (R := A) (a := B) τ hτ

/-- The full modular ratio indexed by the reference row and input column. -/
def outerSpectrum (hρ : ρ.PosDef) (hσ : σ.PosDef) : (A × B) × (A × B) → ℝ :=
  fun k => hσ.isHermitian.eigenvalues k.1 / hρ.isHermitian.eigenvalues k.2

theorem outerSpectrum_pos (hρ : ρ.PosDef) (hσ : σ.PosDef) (k : (A × B) × (A × B)) :
    0 < outerSpectrum hρ hσ k :=
  div_pos (hσ.eigenvalues_pos k.1) (hρ.eigenvalues_pos k.2)

/-- Eigenvalues of the actual retained marginal, with their eigenvector indices. -/
def retainedSpectrum (hτ : τ.PosDef) : A → ℝ :=
  (marginalPosDef hτ).isHermitian.eigenvalues

theorem retainedSpectrum_pos (hτ : τ.PosDef) (i : A) : 0 < retainedSpectrum hτ i :=
  (marginalPosDef hτ).eigenvalues_pos i

/-- The physical `A` in the boundary evaluator. -/
def rootCoordinates (hρ : ρ.PosDef) (hσ : σ.PosDef) : Matrix (A × B) (A × B) ℂ :=
  mixedCoordinates hρ hσ (cfc Real.sqrt ρ)

/-- The physical `C` for one pair, with the reference marginal projector on the left. -/
def retainedCoordinates (hρ : ρ.PosDef) (hσ : σ.PosDef) (k : A × A) :
    Matrix (A × B) (A × B) ℂ :=
  mixedCoordinates hρ hσ (lift (rankOneProjector (marginalPosDef hσ) k.1 *
    rankOneProjector (marginalPosDef hρ) k.2) * cfc Real.sqrt ρ)

private theorem lift_sum_smul {ι : Type*} [Fintype ι] (a : ι → ℂ) (M : ι → Matrix A A ℂ) :
    lift (B := B) (∑ k, a k • M k) = ∑ k, a k • lift (B := B) (M k) := by
  apply Matrix.ext
  rintro ⟨i, b⟩ ⟨j, c⟩
  simp only [lift, Matrix.kronecker_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_mul, mul_assoc]

/-- The actual amplitude has an entrywise expansion at every complex exponent. -/
theorem gamma_coordinate (hρ : ρ.PosDef) (hσ : σ.PosDef) (z : ℂ) (i j : A × B) :
    mixedCoordinates hρ hσ (gamma hρ hσ z) i j =
      ∑ k : A × A,
        ((outerSpectrum hρ hσ (i, j) / (retainedSpectrum hσ k.1 / retainedSpectrum hρ k.2) :
          ℝ) : ℂ) ^ z * retainedCoordinates hρ hσ k i j := by
  let hp := marginalPosDef hρ
  let hq := marginalPosDef hσ
  let M := lift (B := B) (spectralCPow hq (-z) * spectralCPow hp z) * cfc Real.sqrt ρ
  have hGamma : gamma hρ hσ z = spectralCPow hσ z * M * spectralCPow hρ (-z) := by
    unfold gamma
    rw [sub_eq_add_neg, ← spectralCPow_mul, spectralCPow_half]
    simp only [M, hp, hq, Matrix.mul_assoc]
  let coeff (k : A × A) : ℂ :=
    (hq.isHermitian.eigenvalues k.1 : ℂ) ^ (-z) * (hp.isHermitian.eigenvalues k.2 : ℂ) ^ z
  have hRetained : M =
      ∑ k : A × A, coeff k •
        (lift (rankOneProjector hq k.1 * rankOneProjector hp k.2) * cfc Real.sqrt ρ) := by
    dsimp only [M, coeff]
    rw [spectralCPow_mul_eq_sum_rankOneProjector, lift_sum_smul, Matrix.sum_mul]
    simp only [Matrix.smul_mul]
  have hCoords : mixedCoordinates hρ hσ M =
      ∑ k : A × A, coeff k • retainedCoordinates hρ hσ k := by
    rw [hRetained]
    simp only [mixedCoordinates, retainedCoordinates, hp, hq, Matrix.mul_sum, Matrix.sum_mul,
      Matrix.mul_smul, Matrix.smul_mul]
  rw [hGamma, mixedCoordinates_mul_spectralCPow, hCoords]
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  have hCoeff := modular_ratio_cpow (hσ.eigenvalues_pos i) (hρ.eigenvalues_pos j)
    (hq.eigenvalues_pos k.1) (hp.eigenvalues_pos k.2) z
  change _ =
    (((hσ.isHermitian.eigenvalues i / hρ.isHermitian.eigenvalues j) /
      (hq.isHermitian.eigenvalues k.1 / hp.isHermitian.eigenvalues k.2) : ℝ) : ℂ) ^ z *
      retainedCoordinates hρ hσ k i j
  rw [← hCoeff]
  dsimp only [coeff]
  ring

/-- The boundary evaluator is exactly the physical amplitude error in mixed coordinates. -/
theorem mixedCoordinates_error_eq_petzBoundary (hρ : ρ.PosDef) (hσ : σ.PosDef) (s : ℝ) :
    mixedCoordinates hρ hσ (cfc Real.sqrt ρ - gamma hρ hσ (upperExponent s)) =
      petzBoundary Prod.mk (outerSpectrum hρ hσ) (retainedSpectrum hσ) (retainedSpectrum hρ)
        (rootCoordinates hρ hσ) (retainedCoordinates hρ hσ) s := by
  apply Matrix.ext
  intro i j
  rw [mixedCoordinates_sub]
  simp only [Matrix.sub_apply, petzBoundary, Matrix.of_apply, rootCoordinates, retainedFrequency]
  rw [gamma_coordinate]
  apply congrArg (fun value : ℂ => mixedCoordinates hρ hσ (cfc Real.sqrt ρ) i j - value)
  apply Finset.sum_congr rfl
  intro k _
  rw [positive_cpow_upper (div_pos (outerSpectrum_pos hρ hσ (i, j))
    (div_pos (retainedSpectrum_pos hσ k.1) (retainedSpectrum_pos hρ k.2))) s]
  ring

/-- The retained-dimension estimate applied to the physical Hilbert–Schmidt error. -/
theorem weighted_evaluation_physical_boundary (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    Integrable (fun s : ℝ => petzWeight s * ‖cfc Real.sqrt ρ - gamma hρ hσ (upperExponent s)‖ ^ 2) ∧
      ‖cfc Real.sqrt ρ - gamma hρ hσ (upperExponent 0)‖ ^ 2 ≤
        (2 * ((1 + Fintype.card A ^ 2 : ℕ) : ℝ)) *
        (∫ s : ℝ, petzWeight s * ‖cfc Real.sqrt ρ - gamma hρ hσ (upperExponent s)‖ ^ 2) := by
  simpa only [← mixedCoordinates_error_eq_petzBoundary hρ hσ, mixedCoordinates_frobenius_norm,
    pow_two] using weighted_evaluation_petz_boundary Prod.mk (outerSpectrum hρ hσ)
      (retainedSpectrum hσ) (retainedSpectrum hρ) (rootCoordinates hρ hσ)
      (retainedCoordinates hρ hσ)

end PartialTrace

end PetzPhysicalCoordinates
