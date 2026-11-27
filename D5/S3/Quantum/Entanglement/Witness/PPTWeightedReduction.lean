/- GID: D5/S3/Quantum/Entanglement/Witness/PPTWeightedReduction
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/PPTWeightedReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounds the least tomography singular value using the inverse marginal trace. -/

import D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Matrix.LinPsiMap.ReductionBlock
import D5.S3.Quantum.Matrix.PartialTransposeTrace
import D5.S3.Weil.ZetaLinear.RankTrace
import Mathlib.Analysis.Matrix.Order

/-!
# Marginal-dependent converse for square quantum probes

The Bob rows of the tomography matrix are obtained by transposing the
repository's Alice-first realignment. The weights are the reciprocals of
the positive eigenvalues of the Bob marginal, in its eigenbasis.
-/

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder InnerProductSpace Kronecker MatrixOrder
  Matrix.Norms.L2Operator

set_option autoImplicit false

namespace D5.S3.Quantum.Entanglement.Witness.PPTWeightedReduction

open RealignmentSchurBound (realign singularVector singularVector_eq_sqrt_rowGram)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceLeft trace_partialTraceLeft)
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)
open D5.S3.Quantum.Matrix.LinPsiMap (skew skew_sum)

private lemma quadratic_sub {n : Type*} [Fintype n]
    (M N : Matrix n n ℂ) (u : n → ℂ) :
    (star u ⬝ᵥ ((M - N) *ᵥ u)).re =
      (star u ⬝ᵥ (M *ᵥ u)).re - (star u ⬝ᵥ (N *ᵥ u)).re := by
  rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]

/-- A unit vector captures at most the trace of a PSD matrix. The rank-one
projection complement supplies the PSD test in the trace pairing. -/
theorem quadratic_le_trace {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.PosSemidef) (u : n → ℂ)
    (hu : star u ⬝ᵥ u = 1) :
    (star u ⬝ᵥ (H *ᵥ u)).re ≤ H.trace.re := by
  let P := vecMulVec u (star u)
  have hPstar : Pᴴ = P := by simp [P]
  have hPmul : P * P = P := by
    simp [P, Matrix.vecMulVec_mul_vecMulVec, hu]
  have hcomp : (1 - P).PosSemidef := by
    have h := (1 - P).posSemidef_conjTranspose_mul_self
    simpa only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPstar,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPmul,
      sub_self, sub_zero] using h
  have hpair : (H * P).trace = star u ⬝ᵥ (H *ᵥ u) := by
    dsimp only [P]
    rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]
  have h := RHLinalg.trace_mul_nonneg_of_posSemidef hH hcomp
  change 0 ≤ (H * (1 - P)).trace.re at h
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Complex.sub_re, hpair] at h
  exact sub_nonneg.mp h

/-- The Loewner slack above a scalar multiple of a weight matrix has at
least the trace detected by a single unit vector. -/
theorem weighted_trace_lower {n : Type*} [Fintype n] [DecidableEq n]
    {M D : Matrix n n ℂ} (g c : ℝ) (u : n → ℂ)
    (hu : star u ⬝ᵥ u = 1) (hMD : (g : ℂ) • D ≤ M)
    (hc : c ≤ (star u ⬝ᵥ (M *ᵥ u)).re) :
    c + g * (D.trace.re - (star u ⬝ᵥ (D *ᵥ u)).re) ≤ M.trace.re := by
  have h := quadratic_le_trace (Matrix.le_iff.mp hMD) u hu
  rw [quadratic_sub, Matrix.trace_sub, Complex.sub_re, Matrix.smul_mulVec,
    dotProduct_smul, Matrix.trace_smul] at h
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at h
  rw [mul_sub]
  linarith only [hc, h]

private lemma gram_quadratic_lower {ι κ : Type*} [Fintype ι] [Fintype κ]
    (T : Matrix ι κ ℂ) (u : ι → ℂ) (x : κ → ℂ) (d : ℝ) (hd : 0 < d)
    (hx : star x ⬝ᵥ x = (d : ℂ)) (hux : star u ⬝ᵥ (T *ᵥ x) = 1) :
    1 / d ≤ (star u ⬝ᵥ ((T * Tᴴ) *ᵥ u)).re := by
  let z := Tᴴ *ᵥ u
  let X : EuclideanSpace ℂ κ := WithLp.toLp 2 x
  let Z : EuclideanSpace ℂ κ := WithLp.toLp 2 z
  have hi : ⟪Z, X⟫_ℂ = 1 := by
    change ⟪WithLp.toLp 2 z, WithLp.toLp 2 x⟫_ℂ = 1
    dsimp only [z]
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, Matrix.star_mulVec,
      Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec]
    exact hux
  have hX : ‖X‖ ^ 2 = d := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), EuclideanSpace.inner_eq_star_dotProduct]
    change (x ⬝ᵥ star x).re = d
    rw [dotProduct_comm, hx, Complex.ofReal_re]
  have hZ : ‖Z‖ ^ 2 = (star u ⬝ᵥ ((T * Tᴴ) *ᵥ u)).re := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), EuclideanSpace.inner_eq_star_dotProduct]
    change (z ⬝ᵥ star z).re = _
    dsimp only [z]
    rw [dotProduct_comm, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose,
      ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  have hcs : 1 ≤ ‖Z‖ * ‖X‖ := by simpa only [hi, norm_one] using norm_inner_le_norm (𝕜 := ℂ) Z X
  have hsq := (sq_le_sq₀ zero_le_one (mul_nonneg (norm_nonneg Z) (norm_nonneg X))).2 hcs
  rw [one_pow, mul_pow, hX, hZ] at hsq
  exact (div_le_iff₀ hd).2 hsq

private lemma scalar_le_rowGram {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (T : Matrix ι κ ℂ) (g : ℝ)
    (hg : ∀ i, g ≤ singularVector T i ^ 2) :
    (g : ℂ) • (1 : Matrix ι ι ℂ) ≤ T * Tᴴ := by
  let hG := T.posSemidef_self_mul_conjTranspose
  let U := hG.isHermitian.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  let eigenvalues := hG.isHermitian.eigenvalues
  have hEigenvalue i : g ≤ eigenvalues i := by
    let j := (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).symm i
    have hn : 0 ≤ hG.isHermitian.eigenvalues₀ j := hG.eigenvalues_nonneg i
    have h := hg j
    rw [singularVector_eq_sqrt_rowGram, Real.sq_sqrt hn] at h
    exact h
  let E : Matrix ι ι ℂ := diagonal (fun i => (eigenvalues i : ℂ))
  have hE : (E - (g : ℂ) • (1 : Matrix ι ι ℂ)).PosSemidef := by
    have he : E - (g : ℂ) • (1 : Matrix ι ι ℂ) =
        diagonal (fun i => ((eigenvalues i - g : ℝ) : ℂ)) := by
      apply Matrix.ext
      intro i j
      by_cases hij : i = j
      · subst j
        simp [E, Complex.ofReal_sub, smul_eq_mul]
      · simp [E, Matrix.diagonal, Matrix.one_apply, hij]
    rw [he, Matrix.posSemidef_diagonal_iff]
    exact fun i => Complex.zero_le_real.mpr (sub_nonneg.mpr (hEigenvalue i))
  have hspec : T * Tᴴ = φ E := hG.isHermitian.spectral_theorem
  have hfix : φ ((g : ℂ) • (1 : Matrix ι ι ℂ)) = (g : ℂ) • 1 := by
    rw [map_smul, map_one]
  apply Matrix.le_iff.mpr
  rw [hspec, ← hfix, ← map_sub]
  simpa only [φ, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
    hE.mul_mul_conjTranspose_same (↑U : Matrix ι ι ℂ)

private lemma diagonal_real_adjoint {ι : Type*} [DecidableEq ι] (f : ι → ℝ) :
    (diagonal (fun i => (f i : ℂ)))ᴴ = diagonal (fun i => (f i : ℂ)) := by
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  exact Complex.conj_ofReal (f i)

private lemma diagonal_reduction_trace_upper {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Matrix ι ι ℂ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hρ : ρ.PosSemidef) (hred : ρ ≤ diagonal (fun i => (r i : ℂ))) :
    ((diagonal (fun i => (↑((r i)⁻¹ : ℝ) : ℂ)) * ρ) * ρ).trace.re ≤ ρ.trace.re := by
  let B : Matrix ι ι ℂ := diagonal (fun i => (r i : ℂ))
  let V : Matrix ι ι ℂ := diagonal (fun i => (Real.sqrt (r i) : ℂ))
  let S : Matrix ι ι ℂ := diagonal (fun i => (((Real.sqrt (r i))⁻¹ : ℝ) : ℂ))
  have hV : Vᴴ = V := diagonal_real_adjoint (fun i => Real.sqrt (r i))
  have hS : Sᴴ = S := diagonal_real_adjoint (fun i => (Real.sqrt (r i))⁻¹)
  have hvv : V * V = B := by
    dsimp only [V, B]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt (hr i).le]
  have hss : S * S = diagonal (fun i => (↑((r i)⁻¹ : ℝ) : ℂ)) := by
    dsimp only [S]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← Complex.ofReal_mul, ← _root_.mul_inv_rev, ← pow_two, Real.sq_sqrt (hr i).le]
  have hsv : S * V = 1 := by
    dsimp only [S, V]
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (Real.sqrt_pos.2 (hr i)).ne',
      Complex.ofReal_one]
  have hvs : V * S = 1 := by
    dsimp only [V, S]
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (Real.sqrt_pos.2 (hr i)).ne',
      Complex.ofReal_one]
  have hsbs : S * B * S = 1 := by
    calc
      S * B * S = (S * V) * (V * S) := by rw [← hvv]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hsv, hvs, mul_one]
  let C := S * ρ * S
  have hc : C.PosSemidef := by
    simpa only [C, hS] using hρ.mul_mul_conjTranspose_same S
  have hc₁ : (1 - C).PosSemidef := by
    have h := (Matrix.le_iff.mp (show ρ ≤ B from hred)).mul_mul_conjTranspose_same S
    simpa only [hS, Matrix.mul_sub, Matrix.sub_mul, hsbs, C] using h
  have hcomm : Commute C (1 - C) := by
    change C * (1 - C) = (1 - C) * C
    rw [Matrix.mul_sub, Matrix.sub_mul, mul_one, one_mul]
  have hsq : (C - C * C).PosSemidef :=
    (by simpa only [Matrix.mul_sub, mul_one] using
      (Commute.mul_nonneg hc.nonneg hc₁.nonneg hcomm) :
        0 ≤ C - C * C).posSemidef
  have hVCV : V * C * V = ρ := by
    calc
      V * C * V = (V * S) * ρ * (S * V) := by simp only [C, Matrix.mul_assoc]
      _ = ρ := by rw [hvs, hsv, one_mul, mul_one]
  have hVC2V : V * (C * C) * V = ρ * (S * S) * ρ := by
    calc
      _ = (V * S) * ρ * (S * S) * ρ * (S * V) := by simp only [C, Matrix.mul_assoc]
      _ = _ := by rw [hvs, hsv, one_mul, mul_one]
  have hp := hsq.mul_mul_conjTranspose_same V
  rw [hV, Matrix.mul_sub, Matrix.sub_mul, hVCV, hVC2V, hss] at hp
  have h := Complex.nonneg_iff.mp hp.trace_nonneg
  have ht := h.1
  rw [Matrix.trace_sub, Complex.sub_re, ← Matrix.trace_mul_cycle] at ht
  exact sub_nonneg.mp ht

variable {d : ℕ}

private def leftWeight (r : Fin d → ℝ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  diagonal (fun p => (r p.1 : ℂ))

private def diagonalVector (r : Fin d → ℝ) : Fin d × Fin d → ℂ :=
  fun p => if p.1 = p.2 then (r p.1 : ℂ) else 0

private lemma diagonalVector_pair (a b : Fin d → ℝ) :
    star (diagonalVector a) ⬝ᵥ diagonalVector b = ∑ i, (↑(a i * b i) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∑ j : Fin d, if i = j then (↑(a i * b i) : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i = j <;>
        simp [diagonalVector, hij, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul]
    _ = _ := by simp

private lemma leftWeight_mulVec_diagonalVector (t r : Fin d → ℝ) :
    leftWeight t *ᵥ diagonalVector r = diagonalVector (fun i => t i * r i) := by
  funext p
  rw [leftWeight, Matrix.mulVec_diagonal]
  by_cases he : p.1 = p.2 <;> simp [diagonalVector, he, Complex.ofReal_mul]

private lemma realign_mulVec_identity
    (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    (realign ρ)ᵀ *ᵥ diagonalVector (fun _ => 1) =
      fun p => partialTraceLeft ρ p.1 p.2 := by
  funext p
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fintype.sum_prod_type]
  change (∑ a : Fin d, ∑ c : Fin d, ρ (a, p.1) (c, p.2) *
    (if a = c then (↑(1 : ℝ) : ℂ) else 0)) = ∑ a : Fin d, ρ (a, p.1) (a, p.2)
  simp [mul_ite]

/-- The weighted row Gram trace is the inverse-marginal quadratic trace of
the original Hermitian probe. The weight uses the first Bob row index. -/
private lemma weighted_rowGram_trace
    (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hρ : ρ.IsHermitian) (s : Fin d → ℝ) :
    let W := leftWeight s * (realign ρ)ᵀ
    (W * Wᴴ).trace =
      ((diagonal (fun p : Fin d × Fin d => (↑(s p.2 * s p.2) : ℂ)) * ρ) * ρ).trace := by
  dsimp only
  let W := leftWeight s * (realign ρ)ᵀ
  let Q := diagonal (fun p : Fin d × Fin d => (↑(s p.2 * s p.2) : ℂ))
  change (W * Wᴴ).trace = ((Q * ρ) * ρ).trace
  have hW (p q : Fin d × Fin d) : W p q = (s p.1 : ℂ) * ρ (q.1, p.1) (q.2, p.2) :=
    Matrix.diagonal_mul _ _ _ _
  have hQ (p q : Fin d × Fin d) : (Q * ρ) p q = (↑(s p.2 * s p.2) : ℂ) * ρ p q :=
    Matrix.diagonal_mul _ _ _ _
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply (M := W) (N := Wᴴ),
    Matrix.mul_apply (M := Q * ρ) (N := ρ), Matrix.conjTranspose_apply, hW, hQ]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  let e : ((Fin d × Fin d) × (Fin d × Fin d)) ≃ ((Fin d × Fin d) × (Fin d × Fin d)) :=
    { toFun := fun p => ((p.2.1, p.1.1), (p.2.2, p.1.2))
      invFun := fun p => ((p.1.2, p.2.2), (p.1.1, p.2.1))
      left_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
      right_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl }
  apply Fintype.sum_equiv e
  rintro ⟨⟨i, j⟩, ⟨a, c⟩⟩
  have hstar : star (ρ (a, i) (c, j)) = ρ (c, j) (a, i) :=
    congrArg (fun M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ => M (c, j) (a, i)) hρ.eq
  change ((s i : ℂ) * ρ (a, i) (c, j)) * star ((s i : ℂ) * ρ (a, i) (c, j)) =
    ((↑(s i * s i) : ℂ) * ρ (a, i) (c, j)) * ρ (c, j) (a, i)
  rw [star_mul, hstar, Complex.ofReal_mul]
  simp only [Complex.star_def, Complex.conj_ofReal]
  ring

private def lastRow (hd : 2 ≤ d) : Fin (Fintype.card (Fin d × Fin d)) :=
  ⟨Fintype.card (Fin d × Fin d) - 1, by
    have h : 0 < d * d := Nat.mul_pos (by omega) (by omega)
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega⟩

/-- The smallest row-side singular value of the Bob-first tomography matrix. -/
def leastRealignmentSV (hd : 2 ≤ d)
    (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : ℝ :=
  singularVector (realign ρ)ᵀ (lastRow hd)

private lemma leastRealignmentSV_sq_le_gram (hd : 2 ≤ d)
    (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    ((leastRealignmentSV hd ρ ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ≤
      (realign ρ)ᵀ * ((realign ρ)ᵀ)ᴴ := by
  apply scalar_le_rowGram
  intro j
  have hj : (j : ℕ) ≤ (lastRow hd : ℕ) := by
    have h := j.isLt
    change (j : ℕ) ≤ Fintype.card (Fin d × Fin d) - 1
    omega
  let L := ((realign ρ)ᵀ)ᴴ.toEuclideanLin
  exact (sq_le_sq₀ (L.singularValues_nonneg _) (L.singularValues_nonneg _)).2
    (L.singularValues_antitone hj)

/-- The weighted converse before division. The Bob marginal is expressed in
its eigenbasis, with positive eigenvalues. The Loewner hypothesis is the
reduction criterion across Alice. -/
theorem weighted_converse_of_reduction (hd : 2 ≤ d)
    (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hρ : ρ.PosSemidef)
    (ht : ρ.trace = 1) (r : Fin d → ℝ) (hr : ∀ i, 0 < r i)
    (hb : partialTraceLeft ρ = diagonal (fun i => (r i : ℂ)))
    (hred : ρ ≤ (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ partialTraceLeft ρ) :
    1 / (d : ℝ) + leastRealignmentSV hd ρ ^ 2 *
      ((d : ℝ) * ((∑ i, (r i)⁻¹) - 1)) ≤ 1 := by
  let T := (realign ρ)ᵀ
  let s (i : Fin d) := (Real.sqrt (r i))⁻¹
  let S := leftWeight s
  let D := leftWeight (fun i => (r i)⁻¹)
  let W := S * T
  let g := leastRealignmentSV hd ρ ^ 2
  let u := diagonalVector (fun i => Real.sqrt (r i))
  let x := diagonalVector (fun _ : Fin d => (1 : ℝ))
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hsum : (∑ i, (r i : ℂ)) = 1 := by
    have h := trace_partialTraceLeft ρ
    rw [hb, Matrix.trace_diagonal, ht] at h
    exact h
  have hu : star u ⬝ᵥ u = 1 := by
    dsimp only [u]
    rw [diagonalVector_pair]
    have he (i : Fin d) : Real.sqrt (r i) * Real.sqrt (r i) = r i := by
      rw [← pow_two, Real.sq_sqrt (hr i).le]
    simpa only [he] using hsum
  have hx : star x ⬝ᵥ x = ((d : ℝ) : ℂ) := by
    dsimp only [x]
    rw [diagonalVector_pair]
    simp
  have hs₁ (i : Fin d) : s i * r i = Real.sqrt (r i) := by
    have hsi := (Real.sqrt_pos.2 (hr i)).ne'
    calc
      s i * r i = s i * (Real.sqrt (r i) ^ 2) := by rw [Real.sq_sqrt (hr i).le]
      _ = Real.sqrt (r i) := by
        dsimp only [s]
        rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hsi, one_mul]
  have hs₂ (i : Fin d) : s i * s i = (r i)⁻¹ := by
    dsimp only [s]
    rw [← _root_.mul_inv_rev, ← pow_two, Real.sq_sqrt (hr i).le]
  have hTx : T *ᵥ x = diagonalVector r := by
    dsimp only [T, x]
    rw [realign_mulVec_identity, hb]
    funext p
    by_cases he : p.1 = p.2 <;> simp [diagonalVector, Matrix.diagonal, he]
  have hWx : W *ᵥ x = u := by
    dsimp only [W]
    rw [← Matrix.mulVec_mulVec, hTx]
    dsimp only [S]
    rw [leftWeight_mulVec_diagonalVector]
    simp only [hs₁, u]
  have hux : star u ⬝ᵥ (W *ᵥ x) = 1 := by rw [hWx]; exact hu
  have hquad := gram_quadratic_lower W u x (d : ℝ) hdpos hx hux
  have hDquad : (star u ⬝ᵥ (D *ᵥ u)).re = (d : ℝ) := by
    dsimp only [D, u]
    rw [leftWeight_mulVec_diagonalVector, diagonalVector_pair]
    have he (i : Fin d) : Real.sqrt (r i) * ((r i)⁻¹ * Real.sqrt (r i)) = 1 := by
      calc
        _ = (r i)⁻¹ * (Real.sqrt (r i) ^ 2) := by ring
        _ = 1 := by rw [Real.sq_sqrt (hr i).le, inv_mul_cancel₀ (hr i).ne']
    simp [he]
  have hDtrace : D.trace.re = (d : ℝ) * ∑ i, (r i)⁻¹ := by
    simp only [D, leftWeight, Matrix.trace_diagonal, Fintype.sum_prod_type, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum,
      ← Complex.ofReal_natCast, ← Complex.ofReal_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hG : (g : ℂ) • (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ≤ T * Tᴴ :=
    leastRealignmentSV_sq_le_gram hd ρ
  have hSstar : Sᴴ = S := diagonal_real_adjoint (fun p : Fin d × Fin d => s p.1)
  have hSD : S * S = D := by
    simp only [S, D, leftWeight, Matrix.diagonal_mul_diagonal, ← Complex.ofReal_mul, hs₂]
  have hSI : S * ((g : ℂ) • 1) * S = (g : ℂ) • D := by
    rw [Matrix.mul_smul, mul_one, Matrix.smul_mul, hSD]
  have hSW : S * (T * Tᴴ) * S = W * Wᴴ := by
    simp only [W, Matrix.conjTranspose_mul, hSstar, Matrix.mul_assoc]
  have hMD : (g : ℂ) • D ≤ W * Wᴴ := by
    have h := (Matrix.le_iff.mp hG).mul_mul_conjTranspose_same S
    rw [hSstar, Matrix.mul_sub, Matrix.sub_mul, hSI, hSW] at h
    exact Matrix.le_iff.mpr h
  have hlower := weighted_trace_lower g (1 / (d : ℝ)) u hu hMD hquad
  rw [hDquad, hDtrace] at hlower
  have hupper : (W * Wᴴ).trace.re ≤ 1 := by
    have he : (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ partialTraceLeft ρ =
        diagonal (fun p : Fin d × Fin d => (r p.2 : ℂ)) := by
      rw [hb, ← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal]
      simp
    have hred' := hred
    rw [he] at hred'
    have h := diagonal_reduction_trace_upper ρ (fun p => r p.2) (fun p => hr p.2) hρ hred'
    rw [ht, Complex.one_re] at h
    have htrace := weighted_rowGram_trace ρ hρ.isHermitian s
    change (W * Wᴴ).trace = _ at htrace
    rw [htrace]
    simpa only [hs₂] using h
  have hfactor : (d : ℝ) * ((∑ i, (r i)⁻¹) - 1) =
      (d : ℝ) * (∑ i, (r i)⁻¹) - (d : ℝ) := by ring
  rw [hfactor]
  exact hlower.trans hupper

private lemma alice_congruence_apply {B : Type*} [Fintype B] [DecidableEq B]
    (K : Matrix (Fin d) (Fin d) ℂ) (C : Matrix (Fin d × B) (Fin d × B) ℂ)
    (b e : B) (i j : Fin d) :
    ((K ⊗ₖ (1 : Matrix B B ℂ)) * C * (K ⊗ₖ (1 : Matrix B B ℂ))ᴴ) (i, b) (j, e) =
      (K * (Matrix.of (fun a c : Fin d => C (a, b) (c, e))) * Kᴴ) i j := by
  simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    Matrix.mul_apply, Matrix.kronecker_apply, Fintype.sum_prod_type, Matrix.one_apply,
    mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Matrix.of_apply]

/-- Positivity under the second-factor partial transpose implies reduction
across Alice, for any finite Bob dimension. -/
theorem le_alice_identity_kron_marginal_of_ppt {B : Type*} [Fintype B] [DecidableEq B]
    (ρ : Matrix (Fin d × B) (Fin d × B) ℂ)
    (hppt : (partialTranspose ρ).PosSemidef) :
    ρ ≤ (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ partialTraceLeft ρ := by
  let C := (partialTranspose ρ)ᵀ
  let K (k l : Fin d) := skew k l ⊗ₖ (1 : Matrix B B ℂ)
  have hC : C.PosSemidef := hppt.transpose
  have hpos : (((1 / 2 : ℝ) : ℂ) •
      (∑ k : Fin d, ∑ l : Fin d, K k l * C * (K k l)ᴴ)).PosSemidef :=
    (Matrix.posSemidef_sum _ fun k _ => Matrix.posSemidef_sum _ fun l _ =>
      hC.mul_mul_conjTranspose_same (K k l)).smul
      (Complex.zero_le_real.mpr (by norm_num))
  have heq : (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ partialTraceLeft ρ - ρ =
      ((1 / 2 : ℝ) : ℂ) • (∑ k : Fin d, ∑ l : Fin d, K k l * C * (K k l)ᴴ) := by
    apply Matrix.ext
    rintro ⟨i, b⟩ ⟨j, e⟩
    let R : Matrix (Fin d) (Fin d) ℂ := fun a c => ρ (a, b) (c, e)
    have hs := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i j) (skew_sum Rᵀ)
    simp only [Matrix.transpose_transpose, Matrix.trace_transpose] at hs
    simp only [K, Matrix.smul_apply, Matrix.sum_apply, alice_congruence_apply,
      Matrix.sub_apply, Matrix.kronecker_apply]
    change (1 : Matrix (Fin d) (Fin d) ℂ) i j * R.trace - R i j =
      ((1 / 2 : ℝ) : ℂ) • (∑ k : Fin d, ∑ l : Fin d, (skew k l * Rᵀ * (skew k l)ᴴ) i j)
    simpa only [Matrix.smul_apply, Matrix.sum_apply, Matrix.sub_apply, smul_eq_mul,
      mul_comm R.trace] using hs.symm
  exact Matrix.le_iff.mpr (heq.symm ▸ hpos)

private lemma inverse_weight_sum_ge (r : Fin d → ℝ) (hr : ∀ i, 0 < r i)
    (hsum : ∑ i, r i = 1) :
    (d : ℝ) ^ 2 ≤ ∑ i, (r i)⁻¹ := by
  simpa [hsum, one_div] using
    Finset.sq_sum_div_le_sum_sq_div Finset.univ (fun _ : Fin d => (1 : ℝ))
      (g := r) (fun i _ => hr i)

/-- The squared least singular value bound for a trace-one PPT probe
in a basis where the Bob marginal has positive diagonal entries. -/
theorem weighted_converse_of_ppt (hd : 2 ≤ d)
    (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hρ : ρ.PosSemidef)
    (ht : ρ.trace = 1) (hppt : (partialTranspose ρ).PosSemidef)
    (r : Fin d → ℝ) (hr : ∀ i, 0 < r i)
    (hb : partialTraceLeft ρ = diagonal (fun i => (r i : ℂ))) :
    leastRealignmentSV hd ρ ^ 2 ≤
      ((d : ℝ) - 1) / ((d : ℝ) ^ 2 * ((∑ i, (r i)⁻¹) - 1)) := by
  have hw := weighted_converse_of_reduction hd ρ hρ ht r hr hb
    (le_alice_identity_kron_marginal_of_ppt ρ hppt)
  have hsum := trace_partialTraceLeft ρ
  rw [hb, Matrix.trace_diagonal, ht] at hsum
  have hs : ∑ i, r i = 1 := by
    have h := congrArg Complex.re hsum
    simpa only [← Complex.ofReal_sum, Complex.ofReal_re, Complex.one_re] using h
  have hd₂ : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hq : 0 < (∑ i, (r i)⁻¹) - 1 := by
    have hinv := inverse_weight_sum_ge r hr hs
    nlinarith [sq_nonneg ((d : ℝ) - 2)]
  apply (le_div_iff₀ (mul_pos (sq_pos_of_pos hdpos) hq)).2
  have hmul := mul_le_mul_of_nonneg_left hw hdpos.le
  have hone : (d : ℝ) * (1 / (d : ℝ)) = 1 := by field_simp [hdpos.ne']
  rw [mul_add, hone, mul_one] at hmul
  nlinarith only [hmul]

/-- A vanishing marginal diagonal entry kills a row of the Bob-first
realignment and forces its least singular value to vanish. -/
theorem leastRealignmentSV_eq_zero_of_marginal_entry_eq_zero (hd : 2 ≤ d)
    (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hρ : ρ.PosSemidef)
    (b : Fin d) (hb : partialTraceLeft ρ b b = 0) :
    leastRealignmentSV hd ρ = 0 := by
  have hnonneg (a : Fin d) : 0 ≤ (ρ (a, b) (a, b)).re :=
    (Complex.nonneg_iff.mp hρ.diag_nonneg).1
  have hsum : ∑ a : Fin d, (ρ (a, b) (a, b)).re = 0 := by
    have h := congrArg Complex.re hb
    simpa only [partialTraceLeft, Complex.re_sum, Complex.zero_re] using h
  have hzero (a : Fin d) : ρ (a, b) (a, b) = 0 := by
    have hle : (ρ (a, b) (a, b)).re ≤ ∑ c : Fin d, (ρ (c, b) (c, b)).re :=
      Finset.single_le_sum (fun c _ => hnonneg c) (Finset.mem_univ a)
    rw [hsum] at hle
    apply Complex.ext
    · simpa only [Complex.zero_re] using le_antisymm hle (hnonneg a)
    · simpa only [Complex.zero_im] using (Complex.nonneg_iff.mp hρ.diag_nonneg).2.symm
  have hcol (a : Fin d) (p : Fin d × Fin d) : ρ p (a, b) = 0 := by
    let v : Fin d × Fin d → ℂ := Pi.single (a, b) 1
    have hz : star v ⬝ᵥ (ρ *ᵥ v) = 0 := by
      dsimp only [v]
      rw [Matrix.mulVec_single_one]
      simp [Matrix.col_apply, hzero, ← Pi.single_star]
    have h := (hρ.dotProduct_mulVec_zero_iff (x := v)).mp hz
    simpa only [v, Matrix.mulVec_single_one, Matrix.col_apply, Pi.zero_apply] using congrFun h p
  let T := (realign ρ)ᵀ
  let m := leastRealignmentSV hd ρ
  have hrow (p : Fin d × Fin d) : T (b, b) p = 0 := by
    change ρ (p.1, b) (p.2, b) = 0
    exact hcol p.2 (p.1, b)
  have hG : ((m ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ≤ T * Tᴴ :=
    leastRealignmentSV_sq_le_gram hd ρ
  have hz : (T * Tᴴ) (b, b) (b, b) = 0 := by
    simp [Matrix.mul_apply, hrow]
  have h := (Complex.nonneg_iff.mp ((Matrix.le_iff.mp hG).diag_nonneg
    (i := (b, b)))).1
  simp only [Matrix.sub_apply, hz, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
    mul_one, Complex.sub_re, Complex.zero_re, Complex.ofReal_re] at h
  change m = 0
  nlinarith [sq_nonneg m]

end D5.S3.Quantum.Entanglement.Witness.PPTWeightedReduction
