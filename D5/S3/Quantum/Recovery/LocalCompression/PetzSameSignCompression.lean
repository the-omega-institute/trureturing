/- GID: D5/S3/Quantum/Recovery/LocalCompression/PetzSameSignCompression
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/LocalCompression/PetzSameSignCompression
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Both physical same-sign Petz compressions retain a uniform Hilbert–Schmidt floor. -/

import D5.S3.Quantum.GNSMatrix
import OmegaBuild.Commands

/-! The same-sign transitions for a two-block Hermitian involution have a
uniform Hilbert–Schmidt lower bound, including on arbitrary complex matrix inputs. -/

compile_only_with_mathlib

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Recovery.LocalCompression.PetzSameSignCompression

open _root_.Matrix
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius
open D5.S3.Quantum.GNSMatrix (frobenius_norm_sq_eq_trace)

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
private theorem trace_gram_mono (X A B : Matrix n n ℂ) (h : A ≤ B) :
    (Xᴴ * A * X).trace.re ≤ (Xᴴ * B * X).trace.re := by
  classical
  have htrace := ((Matrix.le_iff.mp h).conjTranspose_mul_mul_same X).trace_nonneg
  have hre := (Complex.nonneg_iff.mp htrace).1
  simpa only [Matrix.mul_sub, sub_mul, Matrix.trace_sub, Complex.sub_re,
    sub_nonneg] using hre

private theorem trace_gram_scalar (X : Matrix n n ℂ) (r : ℝ) :
    (Xᴴ * (r • (1 : Matrix n n ℂ)) * X).trace.re = r * ‖X‖ ^ 2 := by
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.trace_smul,
    ← frobenius_norm_sq_eq_trace]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]

private theorem norm_sq_mul_left (A X : Matrix n n ℂ) :
    ‖A * X‖ ^ 2 = (Xᴴ * (Aᴴ * A) * X).trace.re := by
  rw [← Complex.ofReal_re (‖A * X‖ ^ 2), frobenius_norm_sq_eq_trace]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

private theorem sandwich_lower (A X : Matrix n n ℂ) (hA : A.IsHermitian)
    (r : ℝ) (hr : 0 ≤ r) (h : r • (1 : Matrix n n ℂ) ≤ A * A) :
    r * ‖X‖ ≤ ‖A * X * A‖ := by
  have left (Y : Matrix n n ℂ) : r * ‖Y‖ ^ 2 ≤ ‖A * Y‖ ^ 2 := by
    simpa only [trace_gram_scalar, norm_sq_mul_left, hA.eq] using trace_gram_mono Y _ _ h
  have hAdj : (A * X * A)ᴴ = A * (A * X)ᴴ := by
    rw [Matrix.conjTranspose_mul, hA.eq]
  have right : r * ‖A * X‖ ^ 2 ≤ ‖A * X * A‖ ^ 2 := by
    simpa only [← hAdj, Matrix.frobenius_norm_conjTranspose] using left (A * X)ᴴ
  apply (sq_le_sq₀ (mul_nonneg hr (norm_nonneg _)) (norm_nonneg _)).mp
  calc
    (r * ‖X‖) ^ 2 = r * (r * ‖X‖ ^ 2) := by ring
    _ ≤ r * ‖A * X‖ ^ 2 := mul_le_mul_of_nonneg_left (left X) hr
    _ ≤ ‖A * X * A‖ ^ 2 := right

private theorem sandwich_upper (A X : Matrix n n ℂ) (hA : A.IsHermitian)
    (r : ℝ) (hr : 0 ≤ r) (h : A * A ≤ r • (1 : Matrix n n ℂ)) :
    ‖A * X * A‖ ≤ r * ‖X‖ := by
  have left (Y : Matrix n n ℂ) : ‖A * Y‖ ^ 2 ≤ r * ‖Y‖ ^ 2 := by
    simpa only [trace_gram_scalar, norm_sq_mul_left, hA.eq] using trace_gram_mono Y _ _ h
  have hAdj : (A * X * A)ᴴ = A * (A * X)ᴴ := by
    rw [Matrix.conjTranspose_mul, hA.eq]
  have right : ‖A * X * A‖ ^ 2 ≤ r * ‖A * X‖ ^ 2 := by
    simpa only [← hAdj, Matrix.frobenius_norm_conjTranspose] using left (A * X)ᴴ
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hr (norm_nonneg _))).mp
  calc
    ‖A * X * A‖ ^ 2 ≤ r * ‖A * X‖ ^ 2 := right
    _ ≤ r * (r * ‖X‖ ^ 2) := mul_le_mul_of_nonneg_left (left X) hr
    _ = (r * ‖X‖) ^ 2 := by ring

private theorem norm_isometric_conj {m : Type*} [Fintype m]
    (V : Matrix m n ℂ) (hV : Vᴴ * V = 1) (X : Matrix n n ℂ) :
    ‖V * X * Vᴴ‖ = ‖X‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  apply Complex.ofReal_injective
  rw [frobenius_norm_sq_eq_trace, frobenius_norm_sq_eq_trace]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc
    (V * (Xᴴ * Vᴴ) * (V * X * Vᴴ)).trace =
        (V * (Xᴴ * (Vᴴ * V) * X * Vᴴ)).trace := by simp only [Matrix.mul_assoc]
    _ = (V * (Xᴴ * X * Vᴴ)).trace := by rw [hV, Matrix.mul_one]
    _ = (Xᴴ * X).trace := by
      rw [Matrix.trace_mul_comm, Matrix.mul_assoc (Xᴴ * X), hV, Matrix.mul_one]

/-- The positive square root of `(I + a) / 2`. -/
def plusRoot (a : Matrix n n ℂ) : Matrix n n ℂ :=
  CFC.sqrt ((1 / 2 : ℝ) • (1 + a))

/-- The positive square root of `(I - a) / 2`. -/
def minusRoot (a : Matrix n n ℂ) : Matrix n n ℂ :=
  CFC.sqrt ((1 / 2 : ℝ) • (1 - a))

omit [Fintype n] in
private theorem scalar_identity_mono {r s : ℝ} (h : r ≤ s) :
    r • (1 : Matrix n n ℂ) ≤ s • (1 : Matrix n n ℂ) := by
  rw [Matrix.le_iff, ← sub_smul]
  exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr h)

private theorem root_squares {a : Matrix n n ℂ}
    (ha₁ : (1 / 4 : ℝ) • (1 : Matrix n n ℂ) ≤ a)
    (ha₂ : a ≤ (3 / 4 : ℝ) • (1 : Matrix n n ℂ)) :
    plusRoot a * plusRoot a = (1 / 2 : ℝ) • (1 + a) ∧
    minusRoot a * minusRoot a = (1 / 2 : ℝ) • (1 - a) := by
  have hquarter : 0 ≤ (1 / 4 : ℝ) • (1 : Matrix n n ℂ) := by
    simpa only [zero_smul] using
      (scalar_identity_mono (n := n) (show (0 : ℝ) ≤ 1 / 4 by norm_num))
  have ha₀ : 0 ≤ a := hquarter.trans ha₁
  have ha : a ≤ 1 := ha₂.trans (by simpa only [one_smul] using
    (scalar_identity_mono (n := n) (show (3 / 4 : ℝ) ≤ 1 by norm_num)))
  have half_nonneg (A : Matrix n n ℂ) (hA : 0 ≤ A) :
      0 ≤ (1 / 2 : ℝ) • A :=
    (hA.posSemidef.smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)).nonneg
  exact ⟨CFC.sqrt_mul_sqrt_self _ (half_nonneg _ (add_nonneg (by exact PosSemidef.one.nonneg) ha₀)),
    CFC.sqrt_mul_sqrt_self _ (half_nonneg _ (sub_nonneg.mpr ha))⟩

/-- The two same-sign compressions each retain at least a quarter of the
Hilbert–Schmidt norm of an arbitrary complex matrix. -/
theorem same_sign_compression_lower (a q : Matrix n n ℂ) (U : Matrix.unitaryGroup n ℂ)
    (ha₁ : (1 / 4 : ℝ) • (1 : Matrix n n ℂ) ≤ a)
    (ha₂ : a ≤ (3 / 4 : ℝ) • (1 : Matrix n n ℂ)) :
    ‖q‖ / 4 ≤ ‖plusRoot a * q * plusRoot a +
      minusRoot a * ((U : Matrix n n ℂ) * q * (U : Matrix n n ℂ)ᴴ) * minusRoot a‖ ∧
    ‖q‖ / 4 ≤ ‖minusRoot a * q * minusRoot a +
      plusRoot a * ((U : Matrix n n ℂ) * q * (U : Matrix n n ℂ)ᴴ) * plusRoot a‖ := by
  obtain ⟨hc, hd⟩ := root_squares ha₁ ha₂
  have hcHerm : (plusRoot a).IsHermitian := (CFC.sqrt_nonneg _).posSemidef.isHermitian
  have hdHerm : (minusRoot a).IsHermitian := (CFC.sqrt_nonneg _).posSemidef.isHermitian
  have hfloor : (5 / 8 : ℝ) • (1 : Matrix n n ℂ) ≤ plusRoot a * plusRoot a := by
    rw [hc, Matrix.le_iff]
    convert (Matrix.le_iff.mp ha₁).smul (show (0 : ℝ) ≤ 1 / 2 by norm_num) using 1
    module
  have hceiling : minusRoot a * minusRoot a ≤ (3 / 8 : ℝ) • (1 : Matrix n n ℂ) := by
    rw [hd, Matrix.le_iff]
    convert (Matrix.le_iff.mp ha₁).smul (show (0 : ℝ) ≤ 1 / 2 by norm_num) using 1
    module
  have bound (X Y : Matrix n n ℂ) (hXY : ‖X‖ = ‖Y‖) :
      ‖X‖ / 4 ≤ ‖plusRoot a * X * plusRoot a + minusRoot a * Y * minusRoot a‖ := by
    have hl := sandwich_lower _ X hcHerm _ (by norm_num) hfloor
    have hu := sandwich_upper _ Y hdHerm _ (by norm_num) hceiling
    have ht := norm_sub_norm_le (plusRoot a * X * plusRoot a) (-(minusRoot a * Y * minusRoot a))
    rw [norm_neg, sub_neg_eq_add] at ht
    linarith
  have hq := norm_isometric_conj (U : Matrix n n ℂ) (Unitary.coe_star_mul_self U) q
  exact ⟨bound _ _ hq.symm, by simpa only [hq, add_comm] using bound _ _ hq⟩

/-- The positive spectral column in the two-block physical representation. -/
def plusIsometry (a : Matrix n n ℂ) (U : Matrix.unitaryGroup n ℂ) :
    Matrix (n ⊕ n) n ℂ :=
  fromRows (plusRoot a) ((U : Matrix n n ℂ)ᴴ * minusRoot a)

/-- The negative spectral column in the two-block physical representation. -/
def minusIsometry (a : Matrix n n ℂ) (U : Matrix.unitaryGroup n ℂ) :
    Matrix (n ⊕ n) n ℂ :=
  fromRows (-minusRoot a) ((U : Matrix n n ℂ)ᴴ * plusRoot a)

/-- The physical involution before attaching the two environment flags. -/
def physicalInvolution (a : Matrix n n ℂ) (U : Matrix.unitaryGroup n ℂ) :
    Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  let u : Matrix n n ℂ := U
  let s := CFC.sqrt (1 - a ^ 2)
  fromBlocks a (s * u) (uᴴ * s) (-(uᴴ * a * u))

private theorem roots_commute (a : Matrix n n ℂ) :
    Commute (plusRoot a) (minusRoot a) := by
  have h : Commute (1 + a) (1 - a) :=
    (Commute.one_right (1 + a)).sub_right ((Commute.one_left a).add_left (Commute.refl a))
  have hs : Commute ((1 / 2 : ℝ) • (1 + a)) ((1 / 2 : ℝ) • (1 - a)) := by
    exact (h.smul_left _).smul_right _
  rw [plusRoot, minusRoot, CFC.sqrt_eq_cfc, CFC.sqrt_eq_cfc]
  exact ((hs.cfc_nnreal _).symm.cfc_nnreal _).symm

private theorem twice_roots {a : Matrix n n ℂ}
    (hc : plusRoot a * plusRoot a = (1 / 2 : ℝ) • (1 + a))
    (hd : minusRoot a * minusRoot a = (1 / 2 : ℝ) • (1 - a)) :
    CFC.sqrt (1 - a ^ 2) = (2 : ℝ) • (plusRoot a * minusRoot a) := by
  have h := roots_commute a
  have hprod : (plusRoot a * minusRoot a) * (plusRoot a * minusRoot a) =
      (plusRoot a * plusRoot a) * (minusRoot a * minusRoot a) := by
    calc
      _ = plusRoot a * (minusRoot a * plusRoot a) * minusRoot a := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [← h.eq]; simp only [Matrix.mul_assoc]
  apply CFC.sqrt_unique _ (smul_nonneg (by norm_num) (h.mul_nonneg
    (CFC.sqrt_nonneg _) (CFC.sqrt_nonneg _)))
  have hsq :
      ((2 : ℝ) • (plusRoot a * minusRoot a)) *
          ((2 : ℝ) • (plusRoot a * minusRoot a)) =
        1 - a ^ 2 := by
    calc
      _ = (4 : ℝ) • ((plusRoot a * minusRoot a) *
          (plusRoot a * minusRoot a)) := by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        norm_num
      _ = (4 : ℝ) • ((plusRoot a * plusRoot a) *
          (minusRoot a * minusRoot a)) := by rw [hprod]
      _ = (1 + a) * (1 - a) := by
        rw [hc, hd, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul]
        norm_num
      _ = 1 - a ^ 2 := by noncomm_ring
  exact hsq

/-- The two block columns are orthogonal isometries and their range
projections are the positive and negative spectral projections of the physical involution. -/
theorem spectral_isometries (a : Matrix n n ℂ) (U : Matrix.unitaryGroup n ℂ)
    (ha₁ : (1 / 4 : ℝ) • (1 : Matrix n n ℂ) ≤ a)
    (ha₂ : a ≤ (3 / 4 : ℝ) • (1 : Matrix n n ℂ)) :
    let Vplus := plusIsometry a U
    let Vminus := minusIsometry a U
    let H := physicalInvolution a U
    Vplusᴴ * Vplus = 1 ∧ Vminusᴴ * Vminus = 1 ∧ Vplusᴴ * Vminus = 0 ∧
      Vplus * Vplusᴴ = (1 / 2 : ℝ) • (1 + H) ∧
      Vminus * Vminusᴴ = (1 / 2 : ℝ) • (1 - H) := by
  dsimp only
  obtain ⟨hc, hd⟩ := root_squares ha₁ ha₂
  have hcHerm : (plusRoot a).IsHermitian := (CFC.sqrt_nonneg _).posSemidef.isHermitian
  have hdHerm : (minusRoot a).IsHermitian := (CFC.sqrt_nonneg _).posSemidef.isHermitian
  have hcd := (roots_commute a).eq
  have hU : (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ = 1 := Unitary.coe_mul_star_self U
  have hU' : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self U
  have cancel_unitary (X : Matrix n n ℂ) :
      (U : Matrix n n ℂ) * ((U : Matrix n n ℂ)ᴴ * X) = X := by
    rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  have hsum : plusRoot a * plusRoot a + minusRoot a * minusRoot a = 1 := by
    rw [hc, hd]
    module
  have hdiff : plusRoot a * plusRoot a - minusRoot a * minusRoot a = a := by
    rw [hc, hd]
    module
  have hdiff' : minusRoot a * minusRoot a - plusRoot a * plusRoot a = -a := by
    rw [← neg_sub, hdiff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [plusIsometry, conjTranspose_fromRows_eq_fromCols_conjTranspose,
      fromCols_mul_fromRows, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hcHerm.eq, hdHerm.eq, Matrix.mul_assoc, cancel_unitary, hsum]
  · simp only [minusIsometry, conjTranspose_fromRows_eq_fromCols_conjTranspose,
      fromCols_mul_fromRows, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_neg, hcHerm.eq, hdHerm.eq, neg_mul_neg, Matrix.mul_assoc, cancel_unitary,
      add_comm (minusRoot a * minusRoot a), hsum]
  · simp only [plusIsometry, minusIsometry, conjTranspose_fromRows_eq_fromCols_conjTranspose,
      fromCols_mul_fromRows, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hcHerm.eq, hdHerm.eq, mul_neg, Matrix.mul_assoc, cancel_unitary, ← hcd, neg_add_cancel]
  have hPsum : plusIsometry a U * (plusIsometry a U)ᴴ +
      minusIsometry a U * (minusIsometry a U)ᴴ = 1 := by
    rw [← fromBlocks_one (l := n) (m := n) (α := ℂ)]
    simp only [plusIsometry, minusIsometry, conjTranspose_fromRows_eq_fromCols_conjTranspose,
      fromRows_mul_fromCols, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_neg, hcHerm.eq, hdHerm.eq]
    rw [fromBlocks_add, fromBlocks_inj]
    refine ⟨by simpa only [neg_mul_neg] using hsum, ?_, ?_, ?_⟩
    · rw [neg_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hcd, add_neg_cancel]
    · rw [mul_neg, Matrix.mul_assoc, Matrix.mul_assoc, hcd, add_neg_cancel]
    · calc
        _ = (U : Matrix n n ℂ)ᴴ * ((plusRoot a * plusRoot a +
            minusRoot a * minusRoot a) * (U : Matrix n n ℂ)) := by
          rw [Matrix.add_mul, Matrix.mul_add, add_comm]
          simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hsum, Matrix.one_mul, hU']
  have hPdiff : plusIsometry a U * (plusIsometry a U)ᴴ -
      minusIsometry a U * (minusIsometry a U)ᴴ = physicalInvolution a U := by
    rw [sub_eq_add_neg]
    simp only [plusIsometry, minusIsometry, physicalInvolution,
      conjTranspose_fromRows_eq_fromCols_conjTranspose, fromRows_mul_fromCols,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_neg,
      hcHerm.eq, hdHerm.eq, fromBlocks_neg]
    rw [fromBlocks_add, fromBlocks_inj]
    refine ⟨by simpa only [neg_mul_neg, ← sub_eq_add_neg] using hdiff, ?_, ?_, ?_⟩
    · rw [twice_roots hc hd, neg_mul, neg_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        ← hcd, Matrix.smul_mul, two_smul]
    · rw [twice_roots hc hd, mul_neg, neg_neg, Matrix.mul_assoc, Matrix.mul_assoc,
        ← hcd, Matrix.mul_smul, two_smul]
    · calc
        _ = (U : Matrix n n ℂ)ᴴ * ((minusRoot a * minusRoot a -
            plusRoot a * plusRoot a) * (U : Matrix n n ℂ)) := by
          rw [sub_mul, Matrix.mul_sub, sub_eq_add_neg]
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [hdiff', neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  constructor
  · rw [← hPsum, ← hPdiff]
    module
  · rw [← hPsum, ← hPdiff]
    module

omit [DecidableEq n] in
private theorem block_compression (c d q : Matrix n n ℂ) :
    (fromRows c d)ᴴ * fromBlocks q 0 0 q * fromRows c d =
      cᴴ * q * c + dᴴ * q * d := by
  rw [conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks]
  simp only [Matrix.mul_zero, add_zero, zero_add, fromCols_mul_fromRows]

/-- Compressing the two copies of `q` to either physical spectral column
gives the corresponding same-sign matrix expression. -/
theorem spectral_compressions (a q : Matrix n n ℂ) (U : Matrix.unitaryGroup n ℂ) :
    let Vplus := plusIsometry a U
    let Vminus := minusIsometry a U
    let u : Matrix n n ℂ := U
    Vplusᴴ * fromBlocks q 0 0 q * Vplus =
      plusRoot a * q * plusRoot a + minusRoot a * (u * q * uᴴ) * minusRoot a ∧
    Vminusᴴ * fromBlocks q 0 0 q * Vminus =
      minusRoot a * q * minusRoot a + plusRoot a * (u * q * uᴴ) * plusRoot a := by
  have hc : (plusRoot a).IsHermitian := (CFC.sqrt_nonneg _).posSemidef.isHermitian
  have hd : (minusRoot a).IsHermitian := (CFC.sqrt_nonneg _).posSemidef.isHermitian
  constructor
  · rw [plusIsometry, block_compression]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hc.eq, hd.eq, Matrix.mul_assoc]
  · rw [minusIsometry, block_compression]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_neg, hc.eq, hd.eq, neg_mul, mul_neg, neg_neg, Matrix.mul_assoc]

private theorem norm_range_compression {m : Type*} [Fintype m]
    (V : Matrix m n ℂ) (hV : Vᴴ * V = 1) (Q : Matrix m m ℂ) :
    ‖(V * Vᴴ) * Q * (V * Vᴴ)‖ = ‖Vᴴ * Q * V‖ := by
  simpa only [Matrix.mul_assoc] using norm_isometric_conj V hV (Vᴴ * Q * V)

/-- The quadratic forms of the two physical same-sign transition effects
have floor `‖q‖² / 32` in the Hilbert–Schmidt norm. -/
theorem same_sign_transition_lower (a q : Matrix n n ℂ) (U : Matrix.unitaryGroup n ℂ)
    (ha₁ : (1 / 4 : ℝ) • (1 : Matrix n n ℂ) ≤ a)
    (ha₂ : a ≤ (3 / 4 : ℝ) • (1 : Matrix n n ℂ)) :
    let H := physicalInvolution a U
    let Pplus := (1 / 2 : ℝ) • (1 + H)
    let Pminus := (1 / 2 : ℝ) • (1 - H)
    let Q := fromBlocks q 0 0 q
    ‖q‖ ^ 2 / 32 ≤ ‖Pplus * Q * Pplus‖ ^ 2 / 2 ∧
    ‖q‖ ^ 2 / 32 ≤ ‖Pminus * Q * Pminus‖ ^ 2 / 2 := by
  dsimp only
  obtain ⟨hVplus, hVminus, _, hPplus, hPminus⟩ := spectral_isometries a U ha₁ ha₂
  obtain ⟨hCplus, hCminus⟩ := spectral_compressions a q U
  obtain ⟨hplus, hminus⟩ := same_sign_compression_lower a q U ha₁ ha₂
  have sq_bound (x : ℝ) (hx : ‖q‖ / 4 ≤ x) : ‖q‖ ^ 2 / 32 ≤ x ^ 2 / 2 := by
    have hs := (sq_le_sq₀ (by positivity : 0 ≤ ‖q‖ / 4)
      ((by positivity : 0 ≤ ‖q‖ / 4).trans hx)).mpr hx
    nlinarith only [hs]
  constructor
  · rw [← hPplus, norm_range_compression _ hVplus, hCplus]
    exact sq_bound _ hplus
  · rw [← hPminus, norm_range_compression _ hVminus, hCminus]
    exact sq_bound _ hminus

#print axioms same_sign_compression_lower
#print axioms spectral_isometries
#print axioms spectral_compressions
#print axioms same_sign_transition_lower

end D5.S3.Quantum.Recovery.LocalCompression.PetzSameSignCompression
