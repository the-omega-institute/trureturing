/- GID: D5/S3/Quantum/PureState/PhaseMemorySaturatedFrame
   generality: G
   mirror-B: D5/B/S3/Quantum/PureState/PhaseMemorySaturatedFrame
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Saturated phase-memory equality forces independent decoder effects and a projector Gram at the dimension threshold. -/

import D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction
import D5.S3.Quantum.PureState.PhaseRecordSpectralMemory
import Mathlib.LinearAlgebra.Matrix.Bilinear
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Order

/-!
Equality obstructions for finite phase-record compression with one channel and
one POVM. The structural argument follows the host rank-obstruction note and
GPT 6 Pro broker task 61e91fd2-572a-45a5-8e2f-f01efe2b009d, equations (12)–(14).
-/

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker Matrix
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality (channel_kraus_stinespring)

open JointRecordDecoding (phaseVector)
open PhaseRecordMemory

namespace PhaseMemorySaturatedFrame

noncomputable section

variable {ι μ κ J : Type*} [Fintype ι] [DecidableEq ι] [Fintype μ] [DecidableEq μ]
  [Fintype κ] [DecidableEq κ] [Fintype J]

private abbrev gram {a : Type*} [Fintype a] (x y : a → ℂ) : ℂ := star x ⬝ᵥ y

private lemma gram_def {a : Type*} [Fintype a] (x y : a → ℂ) :
    gram x y = star x ⬝ᵥ y := rfl

private lemma gram_mulVec {a b : Type*} [Fintype a] [Fintype b]
    (A : Matrix b a ℂ) (x : a → ℂ) (y : b → ℂ) :
    gram (A *ᵥ x) y = gram x (Aᴴ *ᵥ y) := by
  unfold gram
  rw [star_mulVec, dotProduct_comm, dotProduct_mulVec, dotProduct_comm]

private lemma gram_iso (V : Matrix (κ × μ) ι ℂ) (hV : Vᴴ * V = 1) (x y : ι → ℂ) :
    gram (V *ᵥ x) (V *ᵥ y) = gram x y := by
  rw [gram_mulVec, mulVec_mulVec, hV, one_mulVec]

/-- The operator on the dilation space obtained by acting on the output factor. -/
private def liftOutput (A : Matrix μ μ ℂ) : Matrix (κ × μ) (κ × μ) ℂ :=
  (1 : Matrix κ κ ℂ) ⊗ₖ A

private lemma lift_mul (A B : Matrix μ μ ℂ) :
    liftOutput (κ := κ) (A * B) = liftOutput A * liftOutput B := by
  simp [liftOutput, ← mul_kronecker_mul]

private lemma lift_star (A : Matrix μ μ ℂ) :
    (liftOutput (κ := κ) A)ᴴ = liftOutput Aᴴ := by
  simp [liftOutput, conjTranspose_kronecker]

private lemma lift_one : liftOutput (κ := κ) (1 : Matrix μ μ ℂ) = 1 :=
  one_kronecker_one

private lemma lift_psd {A : Matrix μ μ ℂ} (hA : A.PosSemidef) :
    (liftOutput (κ := κ) A).PosSemidef :=
  Matrix.PosSemidef.one.kronecker hA

/-- The complex-linear trace dual in a finite dilation. -/
def dilationAdjoint (V : Matrix (κ × μ) ι ℂ) : Matrix μ μ ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun A := V.conjTranspose * liftOutput (κ := κ) A * V
  map_add' A B := by simp only [liftOutput, kronecker_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' c A := by simp only [liftOutput, kronecker_smul, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

@[simp] lemma dilationAdjoint_apply (V : Matrix (κ × μ) ι ℂ) (A : Matrix μ μ ℂ) :
    dilationAdjoint V A = V.conjTranspose * liftOutput (κ := κ) A * V := rfl

private lemma adjoint_psd (V : Matrix (κ × μ) ι ℂ) {A : Matrix μ μ ℂ} (hA : A.PosSemidef) :
    (dilationAdjoint V A).PosSemidef := (lift_psd hA).conjTranspose_mul_mul_same V

private lemma adjoint_one (V : Matrix (κ × μ) ι ℂ) (hV : Vᴴ * V = 1) :
    dilationAdjoint V (1 : Matrix μ μ ℂ) = 1 := by
  rw [dilationAdjoint_apply, lift_one, Matrix.mul_one, hV]

/-- Positivity propagates a zero diagonal to the entire column. -/
private theorem column_eq_zero_of_diag_eq_zero {A : Matrix ι ι ℂ} (hA : A.PosSemidef)
    {k : ι} (hk : A k k = 0) : ∀ i, A i k = 0 := by
  let e : ι → ℂ := Pi.single k 1
  have hm : A *ᵥ e = 0 := hA.dotProduct_mulVec_zero_iff.mp (by
    simpa [e, Matrix.mulVec_single, Pi.star_single] using hk)
  intro i
  simpa [e, Matrix.mulVec_single] using congrFun hm i

private lemma evalColumn_eq_mulVec (A : Matrix ι ι ℂ) (k : ι) :
    (fun i => A i k) = A *ᵥ Pi.single k (1 : ℂ) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite]

/-- Independent columns in a complex-linear pullback force independent decoder effects. -/
private theorem independent_decoder_of_independent_columns
    (T : Matrix μ μ ℂ →ₗ[ℂ] Matrix ι ι ℂ) (D : J → Matrix μ μ ℂ) (k : ι)
    (h : LinearIndependent ℂ (fun j i => T (D j) i k)) :
    LinearIndependent ℂ D := by
  let L : Matrix μ μ ℂ →ₗ[ℂ] (ι → ℂ) :=
    ((Matrix.mulVecBilin ℂ ℂ : Matrix ι ι ℂ →ₗ[ℂ] (ι → ℂ) →ₗ[ℂ] (ι → ℂ)).flip
      (Pi.single k 1)).comp T
  apply LinearIndependent.of_comp L
  simp only [Function.comp_def, LinearMap.comp_apply, LinearMap.flip_apply, Matrix.mulVecBilin_apply, L]
  rw [show (fun j => T (D j) *ᵥ Pi.single k 1) = (fun j i => T (D j) i k) from
    funext fun j => (evalColumn_eq_mulVec (T (D j)) k).symm]
  exact h

/-- This dimension obstruction uses only complex linearity of the channel adjoint. -/
private theorem card_le_memory_sq_of_independent_columns
    (T : Matrix μ μ ℂ →ₗ[ℂ] Matrix ι ι ℂ) (D : J → Matrix μ μ ℂ) (k : ι)
    (h : LinearIndependent ℂ (fun j i => T (D j) i k)) :
    Fintype.card J ≤ Fintype.card μ ^ 2 := by
  simpa [Module.finrank_matrix, pow_two] using
    (independent_decoder_of_independent_columns T D k h).fintype_card_le_finrank

private lemma expectation (x : ι → ℂ) (A : Matrix ι ι ℂ) :
    gram x (A *ᵥ x) = trace (A * rankOneDensity x) := by
  simp only [gram, rankOneDensity, mul_vecMulVec, trace_vecMulVec, dotProduct_comm]

private lemma gram_adjoint (V : Matrix (κ × μ) ι ℂ) (A : Matrix μ μ ℂ) (x y : ι → ℂ) :
    gram (V *ᵥ x) (liftOutput A *ᵥ (V *ᵥ y)) = gram x (dilationAdjoint V A *ᵥ y) := by
  rw [gram_mulVec, dilationAdjoint_apply, ← mulVec_mulVec, ← mulVec_mulVec]

/-- The dilation pullback is dual to the channel on every matrix, including pure inputs. -/
private theorem dilationAdjoint_trace (V : Matrix (κ × μ) ι ℂ) (A : Matrix μ μ ℂ)
    (X : Matrix ι ι ℂ) :
    trace (dilationAdjoint V A * X) = trace (A * partialTraceLeft (V * X * Vᴴ)) := by
  rw [dilationAdjoint_apply]
  calc
    _ = trace (liftOutput A * (V * X * Vᴴ)) := by
      rw [Matrix.mul_assoc Vᴴ, Matrix.mul_assoc Vᴴ, trace_mul_comm Vᴴ]
      simp only [Matrix.mul_assoc]
    _ = _ := by
      simp only [liftOutput, trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
        kroneckerMap_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel,
        Finset.sum_ite_eq, Finset.mem_univ, Finset.sum_const_zero, ite_true, partialTraceLeft,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

private lemma output_trace_cap {A : Matrix μ μ ℂ} (hA : A.PosSemidef) :
    A ≤ (A.trace : ℂ) • 1 := by
  let B : HermitianMat μ ℂ := ⟨A, hA.isHermitian⟩
  have h := HermitianMat.le_trace_smul_one (HermitianMat.zero_le_iff.mpr hA : 0 ≤ B)
  change A ≤ A.trace.re • (1 : Matrix μ μ ℂ) at h
  have he : (A.trace.re : ℂ) = A.trace :=
    Complex.ext rfl (Complex.nonneg_iff.mp hA.trace_nonneg).2
  exact (show A.trace.re • (1 : Matrix μ μ ℂ) = A.trace • 1 by
    ext i j; simp only [Matrix.smul_apply, Complex.real_smul, he, smul_eq_mul]) ▸ h

private lemma rankOne_of_eigenvalue_trace {A : Matrix μ μ ℂ} (hA : A.PosSemidef)
    {x : μ → ℂ} (hx : gram x x = 1) (heig : A *ᵥ x = A.trace • x) :
    A = A.trace • rankOneDensity x := by
  let P := rankOneDensity x
  have hP : P.PosSemidef := posSemidef_vecMulVec_self_star _
  have htr : trace P = 1 := by simpa [P, rankOneDensity, trace_vecMulVec, dotProduct_comm] using hx
  have hPP : P * P = P := (pure_state_handshake x hx A).1
  have hAP : A * P = A.trace • P := by simp [P, rankOneDensity, mul_vecMulVec, heig, smul_vecMulVec]
  have hPA : P * A = A.trace • P := by
    have h := congrArg Matrix.conjTranspose hAP
    have hs : star A.trace = A.trace := by
      rw [Complex.star_def, Complex.conj_eq_iff_im]
      exact (Complex.nonneg_iff.mp hA.trace_nonneg).2.symm
    simpa only [conjTranspose_mul, hA.isHermitian.eq, hP.isHermitian.eq,
      conjTranspose_smul, hs] using h
  have hR : (A - A.trace • P).PosSemidef := by
    have h := hA.conjTranspose_mul_mul_same (1 - P)
    rw [(isHermitian_one.sub hP.isHermitian).eq] at h
    rw [show (1 - P) * A * (1 - P) = A - A.trace • P by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
        hPA, hAP, Matrix.smul_mul, hPP, sub_self, sub_zero]] at h
    exact h
  exact sub_eq_zero.mp (hR.trace_eq_zero_iff.mp (by rw [trace_sub, trace_smul, htr]; simp))

private lemma eigen_of_lift_eigen {A : Matrix μ μ ℂ}
    {z : κ × μ → ℂ} (hz : z ≠ 0) (a : ℂ) (h : liftOutput A *ᵥ z = a • z) :
    ∃ x : μ → ℂ, gram x x = 1 ∧ A *ᵥ x = a • x := by
  have hex : ∃ p, z p ≠ 0 := by
    by_contra! hzero
    exact hz (funext hzero)
  obtain ⟨⟨k, m⟩, hm⟩ := hex
  let y : μ → ℂ := fun n => z (k, n)
  have hy : y ≠ 0 := fun he => hm (congrFun he m)
  have heig : A *ᵥ y = a • y := by
    funext i
    have hi := congrFun h (k, i)
    simpa [liftOutput, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.one_apply, y] using hi
  have hypos : 0 < (gram y y).re := (Complex.pos_iff.mp (dotProduct_star_self_pos_iff.mpr hy)).1
  let r := Real.sqrt (gram y y).re
  have hr : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 hypos))
  have hrsq : (r : ℂ) * (r : ℂ) = gram y y := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hypos.le]
    exact Complex.ext rfl (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg y)).2
  refine ⟨(r : ℂ)⁻¹ • y, ?_, ?_⟩
  · rw [gram_def, star_smul, smul_dotProduct, dotProduct_smul]
    change _ • (_ • gram y y) = 1
    rw [← hrsq]
    simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
    field_simp
  · rw [mulVec_smul, heig, smul_comm]

private lemma projection_image (V : Matrix (κ × μ) ι ℂ) (hV : Vᴴ * V = 1)
    (Q : Matrix μ μ ℂ) (hQ : Q.IsHermitian) (hQQ : Q * Q = Q)
    (e v : ι → ℂ) (c : ℂ) (hc : star c = c)
    (hv : gram v v = 1) (hev : gram e v = c)
    (hcol : dilationAdjoint V Q *ᵥ e = c • v) :
    liftOutput Q *ᵥ (V *ᵥ e) = c • (V *ᵥ v) := by
  let B := liftOutput (κ := κ) Q
  let w := V *ᵥ e
  let z := B *ᵥ w
  let p := V *ᵥ v
  have hB : Bᴴ = B := by rw [show Bᴴ = liftOutput Qᴴ from lift_star Q, hQ.eq]
  have hBB : B * B = B := by rw [← lift_mul, hQQ]
  have hzz : gram z z = c * c := by
    change gram (B *ᵥ w) (B *ᵥ w) = _
    rw [gram_mulVec, mulVec_mulVec, hB, hBB]
    change gram (V *ᵥ e) (liftOutput Q *ᵥ (V *ᵥ e)) = _
    rw [gram_adjoint, hcol]
    simp [gram, dotProduct_smul, hev]
  have hpz : gram p z = c := by
    change gram (V *ᵥ v) (liftOutput Q *ᵥ (V *ᵥ e)) = _
    rw [gram_adjoint, hcol]
    simp [gram, dotProduct_smul, hv]
  have hzp : gram z p = c := by
    have h := congrArg star hpz
    rwa [show star (gram p z) = gram z p by exact (star_dotProduct z p).symm, hc] at h
  have hpp : gram p p = 1 := (gram_iso V hV _ _).trans hv
  apply sub_eq_zero.mp
  apply dotProduct_star_self_eq_zero.mp
  change gram (z - c • p) (z - c • p) = 0
  simp only [gram_def, star_sub, star_smul, dotProduct_sub, sub_dotProduct, smul_dotProduct,
    dotProduct_smul, ← gram_def, hzz, hpz, hzp, hpp, hc, smul_eq_mul]
  ring

private lemma trace_pair_im_zero {A B : Matrix μ μ ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) : (trace (A * B)).im = 0 := by
  have h : star (trace (A * B)) = trace (A * B) := by
    rw [← trace_conjTranspose, conjTranspose_mul, hA.eq, hB.eq, trace_mul_comm]
  have := congrArg Complex.im h
  simp [Complex.star_def] at this
  linarith

/-- At the dimension threshold, canonical pulled columns and local domination
force a tight rank-one frame and the projector Gram identity. The normalized
virtual directions have a common real coordinate at the chosen index. -/
theorem threshold_projector_gram [Nonempty μ]
    (V : Matrix (κ × μ) ι ℂ) (hV : Vᴴ * V = 1)
    (D : J → Matrix μ μ ℂ) (hD : ∀ j, (D j).PosSemidef) (hsD : ∑ j, D j = 1)
    (v : J → ι → ℂ) (hv : ∀ j, gram (v j) (v j) = 1) (hli : LinearIndependent ℂ v)
    (k : ι) (c b : ℝ) (hb : 0 < b) (hc : c ^ 2 = (Fintype.card μ : ℝ)⁻¹)
    (hcoord : ∀ j, v j k = (c : ℂ))
    (hdom : ∀ j, (b : ℂ) • rankOneDensity (v j) ≤ dilationAdjoint V (D j))
    (hcol : ∀ j i, dilationAdjoint V (D j) i k = ((b * c : ℝ) : ℂ) * v j i)
    (hbudget : (Fintype.card J : ℝ) * b = Fintype.card μ)
    (hcard : Fintype.card J = Fintype.card μ ^ 2) :
    ∃ d : J → μ → ℂ, (∀ j, gram (d j) (d j) = 1) ∧
      (∀ j, D j = (b : ℂ) • rankOneDensity (d j)) ∧
      (∑ j, rankOneDensity (d j)) = ((b : ℂ)⁻¹) • 1 ∧
      ∀ j l, gram (v j) (v l) = trace (rankOneDensity (d j) * rankOneDensity (d l)) := by
  classical
  let e : ι → ℂ := Pi.single k 1
  let E := dilationAdjoint V
  have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have hcC : (c : ℂ) ^ 2 = (Fintype.card μ : ℂ)⁻¹ := by
    simpa only [Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_natCast] using
      congrArg Complex.ofReal hc
  have hc0 : (c : ℂ) ≠ 0 := by
    intro he
    have hM : (Fintype.card μ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    exact (inv_ne_zero hM) (by simpa only [he, zero_pow (by decide : 2 ≠ 0)] using hcC.symm)
  have hcol' (j : J) : E (D j) *ᵥ e = ((b * c : ℝ) : ℂ) • v j := by
    rw [← evalColumn_eq_mulVec]
    exact funext (hcol j)
  have hcap (j : J) : E (D j) ≤ (D j).trace • 1 := by
    have h := adjoint_psd V (Matrix.le_iff.mp (output_trace_cap (hD j)))
    rw [map_sub, map_smul, adjoint_one V hV] at h
    exact Matrix.le_iff.mpr h
  have htr_ge (j : J) : b ≤ (D j).trace.re := by
    have h := (Matrix.le_iff.mp ((hdom j).trans (hcap j))).re_dotProduct_nonneg (v j)
    have hp : rankOneDensity (v j) *ᵥ v j = v j := by
      simp [rankOneDensity, vecMulVec_mulVec, hv j]
    change 0 ≤ (star (v j) ⬝ᵥ (((D j).trace • (1 : Matrix ι ι ℂ) -
      (b : ℂ) • rankOneDensity (v j)) *ᵥ v j)).re at h
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, one_mulVec, hp,
      dotProduct_sub, dotProduct_smul, dotProduct_smul, ← gram_def, hv j] at h
    simpa only [smul_eq_mul, mul_one, Complex.sub_re, Complex.ofReal_re, sub_nonneg] using h
  have htr (j : J) : (D j).trace = (b : ℂ) := by
    have hn (l : J) : 0 ≤ (D l).trace.re - b := sub_nonneg.mpr (htr_ge l)
    have hs : ∑ l, ((D l).trace.re - b) = 0 := by
      rw [Finset.sum_sub_distrib, ← Complex.re_sum, ← trace_sum, hsD, trace_one]
      simp [hbudget]
    have he := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => hn l)).mp hs j (Finset.mem_univ _)
    exact Complex.ext (sub_eq_zero.mp he) (Complex.nonneg_iff.mp (hD j).trace_nonneg).2.symm
  have hDpure (j : J) : ∃ x : μ → ℂ, gram x x = 1 ∧ D j = (b : ℂ) • rankOneDensity x := by
    let y := V *ᵥ v j
    have hy : gram y y = 1 := (gram_iso V hV _ _).trans (hv j)
    have hlower := (Matrix.le_iff.mp (hdom j)).re_dotProduct_nonneg (v j)
    have hp : rankOneDensity (v j) *ᵥ v j = v j := by
      simp [rankOneDensity, vecMulVec_mulVec, hv j]
    have hlower' : b ≤ (gram (v j) (E (D j) *ᵥ v j)).re := by
      change 0 ≤ (star (v j) ⬝ᵥ ((E (D j) -
        (b : ℂ) • rankOneDensity (v j)) *ᵥ v j)).re at hlower
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hp, dotProduct_sub,
        dotProduct_smul, ← gram_def, ← gram_def, hv j] at hlower
      simpa only [smul_eq_mul, mul_one, Complex.sub_re, Complex.ofReal_re, sub_nonneg] using hlower
    have hcap' : ((b : ℂ) • (1 : Matrix μ μ ℂ) - D j).PosSemidef := by
      simpa [htr j] using Matrix.le_iff.mp (output_trace_cap (hD j))
    have hR : ((b : ℂ) • (1 : Matrix (κ × μ) (κ × μ) ℂ) - liftOutput (D j)).PosSemidef := by
      have h := lift_psd (κ := κ) hcap'
      have he : liftOutput (κ := κ) ((b : ℂ) • (1 : Matrix μ μ ℂ) - D j) =
          (b : ℂ) • 1 - liftOutput (D j) := by
        simp only [liftOutput, sub_eq_add_neg, kronecker_add, kronecker_smul, one_kronecker_one]
        rw [← neg_one_smul ℂ (D j), kronecker_smul, neg_one_smul]
      rwa [he] at h
    have hezero : gram y (((b : ℂ) • 1 - liftOutput (D j)) *ᵥ y) = 0 := by
      have hn := hR.dotProduct_mulVec_nonneg y
      apply Complex.ext
      · have hh := (Complex.nonneg_iff.mp hn).1
        have heq : gram y (((b : ℂ) • 1 - liftOutput (D j)) *ᵥ y) =
            (b : ℂ) - gram (v j) (E (D j) *ᵥ v j) := by
          rw [gram_def, Matrix.sub_mulVec, Matrix.smul_mulVec, one_mulVec, dotProduct_sub,
            dotProduct_smul, ← gram_def, ← gram_def, hy, smul_eq_mul, mul_one]
          exact congrArg ((b : ℂ) - ·) (gram_adjoint V (D j) (v j) (v j))
        rw [heq, Complex.sub_re, Complex.ofReal_re, Complex.zero_re]
        change 0 ≤ (gram y (((b : ℂ) • 1 - liftOutput (D j)) *ᵥ y)).re at hh
        rw [heq, Complex.sub_re, Complex.ofReal_re] at hh
        linarith
      · exact (Complex.nonneg_iff.mp hn).2.symm
    have heig : liftOutput (D j) *ᵥ y = (b : ℂ) • y := by
      have hz := hR.dotProduct_mulVec_zero_iff.mp hezero
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, one_mulVec] at hz
      exact (sub_eq_zero.mp hz).symm
    have hy0 : y ≠ 0 := by intro h; simp [h, gram] at hy
    obtain ⟨x, hx, hxe⟩ := eigen_of_lift_eigen hy0 _ heig
    refine ⟨x, hx, ?_⟩
    have hh := rankOne_of_eigenvalue_trace (hD j) hx (by rw [htr j]; exact hxe)
    simpa [htr j] using hh
  choose d hd hDeq using hDpure
  let Q := fun j => rankOneDensity (d j)
  have hQ (j : J) : (Q j).IsHermitian := (posSemidef_vecMulVec_self_star _).isHermitian
  have hQQ (j : J) : Q j * Q j = Q j := (pure_state_handshake (d j) (hd j) 1).1
  have hQtr (j : J) : trace (Q j) = 1 := by
    rw [show trace (Q j) = gram (d j) (d j) by simp [Q, gram, rankOneDensity, trace_vecMulVec, dotProduct_comm], hd]
  have hQcol (j : J) : E (Q j) *ᵥ e = (c : ℂ) • v j := by
    have h := hcol' j
    rw [hDeq j, map_smul, smul_mulVec, Complex.ofReal_mul, ← smul_smul] at h
    exact smul_right_injective _ hbC h
  have hTI : LinearIndependent ℂ (fun j => E (Q j) *ᵥ e) := by
    simp only [hQcol]
    exact hli.units_smul (fun _ => Units.mk0 (c : ℂ) hc0)
  have hLI : LinearIndependent ℂ Q := by
    apply independent_decoder_of_independent_columns E Q k
    rw [show (fun j i => E (Q j) i k) = (fun j => E (Q j) *ᵥ e) from
      funext fun j => evalColumn_eq_mulVec (E (Q j)) k]
    exact hTI
  let f : Matrix μ μ ℂ →ₗ[ℂ] ℂ :=
    (Matrix.traceLinearMap ι ℂ ℂ).comp
      ((LinearMap.mulRight ℂ (rankOneDensity e)).comp E)
  have hf (A : Matrix μ μ ℂ) : f A = gram e (E A *ᵥ e) := (expectation e (E A)).symm
  have hev (j : J) : gram e (v j) = (c : ℂ) := by
    simp [gram, e, Pi.star_single, hcoord]
  have hfeq : f = (Fintype.card μ : ℂ)⁻¹ • Matrix.traceLinearMap μ ℂ ℂ := by
    let B := basisOfLinearIndependentOfCardEqFinrank' Q hLI (by simpa [Module.finrank_matrix, pow_two] using hcard)
    refine B.ext (fun j => ?_)
    have hB : B j = Q j := by simp [B]
    rw [hB, hf, hQcol]
    rw [show gram e ((c : ℂ) • v j) = (c : ℂ) ^ 2 by
      simp [gram, dotProduct_smul, hev, pow_two], hcC]
    change _ = (Fintype.card μ : ℂ)⁻¹ * trace (Q j)
    rw [hQtr, mul_one]
  refine ⟨d, hd, hDeq, ?_, ?_⟩
  · rw [show (∑ j, Q j) = (b : ℂ)⁻¹ • ∑ j, D j by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [hDeq j, smul_smul, inv_mul_cancel₀ hbC, one_smul], hsD]
  · intro j l
    have himg (m : J) := projection_image V hV (Q m) (hQ m) (hQQ m) e (v m)
      (c : ℂ) (by simp) (hv m) (hev m) (hQcol m)
    have hcross := gram_adjoint V (Q j * Q l) e e
    rw [lift_mul, ← mulVec_mulVec, ← (hQ j).eq, ← lift_star, ← gram_mulVec] at hcross
    rw [himg j, himg l] at hcross
    have hs : gram ((c : ℂ) • (V *ᵥ v j)) ((c : ℂ) • (V *ᵥ v l)) =
        (Fintype.card μ : ℂ)⁻¹ * gram (v j) (v l) := by
      simp only [gram_def, star_smul, Complex.star_def, Complex.conj_ofReal, smul_dotProduct,
        dotProduct_smul, smul_eq_mul, ← gram_def, gram_iso V hV]
      rw [← mul_assoc, ← pow_two, hcC]
    rw [hs, ← hf, hfeq] at hcross
    have hM : (Fintype.card μ : ℂ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card μ ≠ 0)
    apply mul_left_cancel₀ (inv_ne_zero hM)
    simpa only [(hQ j).eq, LinearMap.smul_apply, smul_eq_mul, traceLinearMap_apply, Q] using hcross

private lemma star_mul_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : star z * z = 1 := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hz]
  norm_num

private lemma gram_phase (u : ι → ι → ℂ) (hu : ∀ j i, ‖u j i‖ = 1)
    (v : ι → ℝ) (j : ι) : gram (phaseVector u v j) (phaseVector u v j) =
    ((∑ i, (v i) ^ 2 : ℝ) : ℂ) := by
  rw [gram_def, dotProduct, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [phaseVector, Pi.star_apply, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_pow]
  have h := star_mul_of_norm_one (hu j i)
  change (star (u j i) * u j i) = 1 at h
  calc
    _ = (v i : ℂ) ^ 2 * (star (u j i) * u j i) := by rw [Complex.star_def]; ring
    _ = _ := by rw [h, mul_one]

private lemma normalized_top_eigen {A : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (x : ι → ℂ) (hx : gram x x = 1) :
    (gram x (A *ᵥ x)).re ≤ A.trace.re ∧
    ((gram x (A *ᵥ x)).re = A.trace.re → A = A.trace • rankOneDensity x) := by
  have h := Matrix.le_iff.mp (output_trace_cap hA)
  have he : gram x ((A.trace • (1 : Matrix ι ι ℂ) - A) *ᵥ x) =
      A.trace - gram x (A *ᵥ x) := by
    rw [gram_def, Matrix.sub_mulVec, Matrix.smul_mulVec, one_mulVec, dotProduct_sub,
      dotProduct_smul, ← gram_def, ← gram_def, hx, smul_eq_mul, mul_one]
  have hp := h.dotProduct_mulVec_nonneg x
  change 0 ≤ gram x ((A.trace • (1 : Matrix ι ι ℂ) - A) *ᵥ x) at hp
  refine ⟨?_, fun heq => ?_⟩
  · have hh := (Complex.nonneg_iff.mp hp).1
    rwa [he, Complex.sub_re, sub_nonneg] at hh
  · have hz : gram x ((A.trace • (1 : Matrix ι ι ℂ) - A) *ᵥ x) = 0 := by
      apply Complex.ext
      · rw [he, Complex.sub_re, heq, sub_self, Complex.zero_re]
      · exact (Complex.nonneg_iff.mp hp).2.symm
    have heig := h.dotProduct_mulVec_zero_iff.mp hz
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, one_mulVec] at heig
    exact rankOne_of_eigenvalue_trace hA hx (sub_eq_zero.mp heig).symm

private lemma weighted_local_effect (u : ι → ι → ℂ) (hu : ∀ j i, ‖u j i‖ = 1)
    (a r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (L : ℝ) (hL : 0 < L) (hLsum : ∑ i, r i * a i ^ 2 = L)
    (j : ι) (F : Matrix ι ι ℂ) (hF : F.PosSemidef) :
    let t := fun i => r i * a i
    let s := (trace (F * rankOneDensity (phaseVector u t j))).re
    let g := ∑ i, r i * (F i i).re
    s ≤ L * g ∧ (s = L * g → F = (((g / L : ℝ) : ℂ)) • rankOneDensity (phaseVector u a j)) := by
  dsimp only
  let W : Matrix ι ι ℂ := diagonal fun i => (Real.sqrt (r i) : ℂ)
  let G := W * F * W
  let b : ι → ℝ := fun i => Real.sqrt (r i) * a i / Real.sqrt L
  let x := phaseVector u b j
  have hW : Wᴴ = W := by simp [W, diagonal_conjTranspose]
  have hG : G.PosSemidef := by simpa [G, hW] using hF.conjTranspose_mul_mul_same W
  have hsqrt (i : ι) : Real.sqrt (r i) * Real.sqrt (r i) = r i :=
    Real.mul_self_sqrt (hr i).le
  have hLsqrt : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL.le
  have hx : gram x x = 1 := by
    rw [show gram x x = _ from gram_phase u hu b j]
    have hb : ∑ i, b i ^ 2 = 1 := by
      simp only [b, div_pow, mul_pow, Real.sq_sqrt (hr _).le, Real.sq_sqrt hL.le]
      rw [← Finset.sum_div, hLsum, div_self hL.ne']
    rw [hb, Complex.ofReal_one]
  have hGentry (i l : ι) : G i l = (Real.sqrt (r i) : ℂ) * F i l * (Real.sqrt (r l) : ℂ) := by
    simp [G, W, diagonal_mul, mul_diagonal]
  have htrace : G.trace = ((∑ i, r i * (F i i).re : ℝ) : ℂ) := by
    rw [trace, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hFi : ((F i i).re : ℂ) = F i i :=
      Complex.ext rfl (Complex.nonneg_iff.mp (hF.diag_nonneg (i := i))).2
    rw [diag_apply, hGentry, Complex.ofReal_mul, hFi]
    calc _ = ((Real.sqrt (r i) * Real.sqrt (r i) : ℝ) : ℂ) * F i i := by push_cast; ring
         _ = _ := by rw [hsqrt]
  let ψ := phaseVector u (fun i => r i * a i) j
  have hWx : W *ᵥ x = ((Real.sqrt L : ℂ)⁻¹) • ψ := by
    funext i
    simp only [W, mulVec_diagonal, phaseVector, x, b, ψ, Pi.smul_apply, smul_eq_mul,
      Complex.ofReal_div, Complex.ofReal_mul]
    have hh := congrArg Complex.ofReal (hsqrt i)
    push_cast at hh
    rw [div_eq_mul_inv]
    calc _ = (Real.sqrt L : ℂ)⁻¹ *
        (((Real.sqrt (r i) : ℂ) * (Real.sqrt (r i) : ℂ)) * (a i : ℂ) * u j i) := by ring
         _ = _ := by rw [hh]
  have hscore : (trace (F * rankOneDensity ψ)).re =
      L * (gram x (G *ᵥ x)).re := by
    have hv : gram x (G *ᵥ x) = gram (W *ᵥ x) (F *ᵥ (W *ᵥ x)) := by
      rw [gram_mulVec, hW]
      simp only [G, mulVec_mulVec, Matrix.mul_assoc]
    have hnorm : star ((Real.sqrt L : ℂ)⁻¹) * (Real.sqrt L : ℂ)⁻¹ = (L : ℂ)⁻¹ := by
      rw [star_inv₀, Complex.star_def, Complex.conj_ofReal, ← _root_.mul_inv_rev,
        ← Complex.ofReal_mul, hLsqrt]
    rw [hv, hWx, Matrix.mulVec_smul, gram_def, star_smul, smul_dotProduct, dotProduct_smul]
    change _ = L * (star ((Real.sqrt L : ℂ)⁻¹) * ((Real.sqrt L : ℂ)⁻¹ * gram ψ (F *ᵥ ψ))).re
    rw [← mul_assoc, hnorm, expectation, ← Complex.ofReal_inv, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, ← mul_assoc,
      mul_inv_cancel₀ hL.ne', one_mul]
  obtain ⟨hle, heq⟩ := normalized_top_eigen hG x hx
  rw [htrace, Complex.ofReal_re] at hle heq
  change (trace (F * rankOneDensity ψ)).re ≤ _ ∧ (_ → _)
  rw [hscore]
  refine ⟨mul_le_mul_of_nonneg_left hle hL.le, fun hs => ?_⟩
  have hGeq := heq (mul_left_cancel₀ hL.ne' hs)
  ext i l
  have hi : (Real.sqrt (r i) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (hr i)).ne'
  have hl : (Real.sqrt (r l) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (hr l)).ne'
  apply mul_left_cancel₀ hi
  apply mul_right_cancel₀ hl
  rw [← hGentry, hGeq]
  simp only [rankOneDensity, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, x, phaseVector, b,
    Complex.ofReal_mul, Complex.ofReal_div, star_mul, star_div₀, Complex.star_def,
    Complex.conj_ofReal, smul_eq_mul]
  have hL0 : (Real.sqrt L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hL).ne'
  have HH := congrArg Complex.ofReal hLsqrt
  push_cast at HH
  field_simp [hL0, show (L : ℂ) ≠ 0 from Complex.ofReal_ne_zero.mpr hL.ne']
  rw [show (↑(Real.sqrt L) : ℂ) ^ 2 = (L : ℂ) by simpa [pow_two] using HH]
  ring

/-- Pointwise score-preserving local effects of total trace at most the memory
dimension. This interface permits the upper-bound proof to provide the effects. -/
def LocalEffects (E : ι → Matrix ι ι ℂ) (ψ : ι → ι → ℂ)
    (M : ℝ) (F : ι → Matrix ι ι ℂ) : Prop :=
  (∀ j, (F j).PosSemidef) ∧ (∀ j, F j ≤ E j) ∧
  (∀ j, trace (F j * rankOneDensity (ψ j)) = trace (E j * rankOneDensity (ψ j))) ∧
  (∑ j, (trace (F j)).re) ≤ M

/-- A positive clipped profile has strictly positive coordinates. The slope
can exceed the common tail slope only on coordinates of amplitude one. -/
def PositiveClippedProfile (a r : ι → ℝ) (M τ : ℝ) : Prop :=
  (∀ i, 0 < a i) ∧ (∀ i, a i ≤ 1) ∧ (∑ i, a i ^ 2) = M ∧
    0 < τ ∧ (∀ i, τ ≤ r i) ∧ (∀ i, r i ≠ τ → a i = 1)

/-- Active local effects at equality are the uniform canonical phase effects.
Their columns at a saturated coordinate coincide with the physical pullbacks. -/
theorem saturated_local_effects_canonical [Nonempty ι]
    (u : ι → ι → ℂ) (hu : ∀ j i, ‖u j i‖ = 1)
    (a r : ι → ℝ) (M τ : ℝ) (hp : PositiveClippedProfile a r M τ)
    (k : ι) (hk : a k = 1) (hu0 : ∀ j, u j k = 1)
    (hsumu : ∀ i, ∑ j, u j i = if i = k then (Fintype.card ι : ℂ) else 0)
    (hli : LinearIndependent ℂ (phaseVector u a))
    (E F : ι → Matrix ι ι ℂ) (hE : ∑ j, E j = 1)
    (hF : LocalEffects E (phaseVector u fun i => r i * a i) M F)
    (hscore : ∑ j, (trace (E j * rankOneDensity (phaseVector u (fun i => r i * a i) j))).re =
      (∑ i, r i * a i ^ 2) ^ 2) :
    (∀ j, F j = (Fintype.card ι : ℂ)⁻¹ • rankOneDensity (phaseVector u a j)) ∧
    ∀ j i, E j i k = F j i k := by
  classical
  obtain ⟨ha, ha1, ham, hτ, hrτ, hrsat⟩ := hp
  obtain ⟨hFpos, hFE, hFs, hFt⟩ := hF
  let L := ∑ i, r i * a i ^ 2
  let f : ι → ℝ := fun i => ((∑ j, F j) i i).re
  let g : ι → ℝ := fun j => ∑ i, r i * (F j i i).re
  let s : ι → ℝ := fun j =>
    (trace (F j * rankOneDensity (phaseVector u (fun i => r i * a i) j))).re
  have hr (i : ι) : 0 < r i := hτ.trans_le (hrτ i)
  have hL : 0 < L := Finset.sum_pos (fun i _ => mul_pos (hr i) (pow_pos (ha i) _))
    Finset.univ_nonempty
  have hFs1 : (∑ j, F j) ≤ 1 := hE ▸ Finset.sum_le_sum (fun j _ => hFE j)
  have hf1 (i : ι) : f i ≤ 1 := by
    have h := (Matrix.le_iff.mp hFs1).diag_nonneg (i := i)
    have hh := (Complex.nonneg_iff.mp h).1
    change 0 ≤ (((1 : Matrix ι ι ℂ) - ∑ j, F j) i i).re at hh
    simpa [f, Matrix.sub_apply, Complex.sub_re, Matrix.one_apply, sub_nonneg] using hh
  have hfsum : ∑ i, f i ≤ M := by
    calc
      _ = (trace (∑ j, F j)).re := by simp [f, trace, Complex.re_sum]
      _ ≤ M := by simpa only [trace_sum, Complex.re_sum] using hFt
  have hg : ∑ j, g j ≤ L := by
    have hform : ∑ j, g j = ∑ i, r i * f i := by
      dsimp only [g, f]
      rw [Finset.sum_comm]
      simp only [Matrix.sum_apply, Complex.re_sum, Finset.mul_sum]
    rw [hform]
    have hδ (i : ι) : (r i - τ) * f i ≤ (r i - τ) * a i ^ 2 := by
      by_cases hh : r i = τ
      · simp [hh]
      · simpa [hrsat i hh] using mul_le_mul_of_nonneg_left (hf1 i) (sub_nonneg.mpr (hrτ i))
    have hsplit (x : ι → ℝ) :
        ∑ i, r i * x i = τ * (∑ i, x i) + ∑ i, (r i - τ) * x i := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    change ∑ i, r i * f i ≤ ∑ i, r i * a i ^ 2
    rw [hsplit, hsplit, ham]
    exact add_le_add (mul_le_mul_of_nonneg_left hfsum hτ.le)
      (Finset.sum_le_sum (fun i _ => hδ i))
  have hs_eq : ∑ j, s j = L ^ 2 := by simpa only [s, hFs, L] using hscore
  have hloc (j : ι) := weighted_local_effect u hu a r hr L hL rfl j (F j) (hFpos j)
  have hineq (j : ι) : s j ≤ L * g j := (hloc j).1
  have htot : ∑ j, g j = L := by
    have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hineq j)
    rw [hs_eq, ← Finset.mul_sum] at h
    exact le_antisymm hg (le_of_mul_le_mul_left (by simpa only [pow_two] using h) hL)
  have heq (j : ι) : s j = L * g j := by
    have hz : ∑ j, (L * g j - s j) = 0 := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, htot, hs_eq, pow_two, sub_self]
    exact (sub_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => sub_nonneg.mpr (hineq j))).mp hz j (Finset.mem_univ _))).symm
  let w : ι → ℂ := fun j => ((g j / L : ℝ) : ℂ)
  have hw : ∑ j, w j = 1 := by
    rw [show (∑ j, w j) = ((∑ j, g j / L : ℝ) : ℂ) by simp only [w, Complex.ofReal_sum],
      ← Finset.sum_div, htot, div_self hL.ne', Complex.ofReal_one]
  have hcanon (j : ι) : F j = w j • rankOneDensity (phaseVector u a j) := (hloc j).2 (heq j)
  have hkF (j i : ι) : F j i k = w j * phaseVector u a j i := by
    rw [hcanon j]
    simp [rankOneDensity, vecMulVec_apply, phaseVector, hu0, hk]
  have hdiag : (∑ j, F j) k k = 1 := by
    simpa [Matrix.sum_apply, hkF, phaseVector, hu0, hk] using hw
  have hscol (i : ι) : ∑ j, F j i k = (1 : Matrix ι ι ℂ) i k := by
    have hzero := column_eq_zero_of_diag_eq_zero (Matrix.le_iff.mp hFs1)
      (show ((1 : Matrix ι ι ℂ) - ∑ j, F j) k k = 0 by simp [Matrix.sub_apply, hdiag])
    exact (sub_eq_zero.mp (by simpa only [Matrix.sub_apply, Matrix.sum_apply] using hzero i)).symm
  have hucol (i : ι) :
      ∑ j, (Fintype.card ι : ℂ)⁻¹ * phaseVector u a j i = (1 : Matrix ι ι ℂ) i k := by
    have hn : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp only [phaseVector, ← mul_assoc, ← Finset.mul_sum, hsumu, Matrix.one_apply]
    split <;> rename_i h
    · subst i
      simp [hk, hn]
    · simp
  have hcomb : ∑ j, (w j - (Fintype.card ι : ℂ)⁻¹) • phaseVector u a j = 0 := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
      ← hkF, hscol, hucol, sub_self, Pi.zero_apply]
  have hw_uniform (j : ι) : w j = (Fintype.card ι : ℂ)⁻¹ :=
    sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ hcomb j)
  refine ⟨fun j => (hcanon j).trans (by rw [hw_uniform]), ?_⟩
  intro j i
  have hDiff (l : ι) : (E l - F l).PosSemidef := Matrix.le_iff.mp (hFE l)
  have hDiffSum : ∑ l, ((E l - F l) k k).re = 0 := by
    rw [← Complex.re_sum, ← Matrix.sum_apply, Finset.sum_sub_distrib, hE, Matrix.sub_apply, hdiag]
    simp
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ =>
    (Complex.nonneg_iff.mp ((hDiff l).diag_nonneg (i := k))).1)).mp hDiffSum j (Finset.mem_univ _)
  have hdiagzero : (E j - F j) k k = 0 :=
    Complex.ext hzero (Complex.nonneg_iff.mp ((hDiff j).diag_nonneg (i := k))).2.symm
  exact sub_eq_zero.mp (column_eq_zero_of_diag_eq_zero (hDiff j) hdiagzero i)

/-- With score-preserving local effects, equality at a saturated coordinate
already forces the label-count bound for a complex-linear unital adjoint. -/
private theorem saturated_equality_card_le_memory_sq [Nonempty ι]
    (u : ι → ι → ℂ) (hu : ∀ j i, ‖u j i‖ = 1)
    (a r : ι → ℝ) (τ : ℝ) (hp : PositiveClippedProfile a r (Fintype.card μ) τ)
    (k : ι) (hk : a k = 1) (hu0 : ∀ j, u j k = 1)
    (hsumu : ∀ i, ∑ j, u j i = if i = k then (Fintype.card ι : ℂ) else 0)
    (hli : LinearIndependent ℂ (phaseVector u a))
    (T : Matrix μ μ ℂ →ₗ[ℂ] Matrix ι ι ℂ) (hT : T 1 = 1)
    (D : ι → Matrix μ μ ℂ) (hsD : ∑ j, D j = 1)
    (F : ι → Matrix ι ι ℂ)
    (hF : LocalEffects (fun j => T (D j)) (phaseVector u fun i => r i * a i) (Fintype.card μ) F)
    (hscore : ∑ j, (trace (T (D j) * rankOneDensity (phaseVector u (fun i => r i * a i) j))).re =
      (∑ i, r i * a i ^ 2) ^ 2) :
    Fintype.card ι ≤ Fintype.card μ ^ 2 := by
  have hsE : ∑ j, T (D j) = 1 := by rw [← map_sum, hsD, hT]
  obtain ⟨hcan, hcol⟩ := saturated_local_effects_canonical u hu a r (Fintype.card μ) τ hp
    k hk hu0 hsumu hli (fun j => T (D j)) F hsE hF hscore
  apply card_le_memory_sq_of_independent_columns T D k
  have hN : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
  have hfun : (fun j i => T (D j) i k) =
      fun j => (Fintype.card ι : ℂ)⁻¹ • phaseVector u a j := by
    funext j i
    rw [hcol j i, hcan j]
    simp [rankOneDensity, vecMulVec_apply, phaseVector, hk, hu0]
  rw [hfun]
  exact hli.units_smul (fun _ => Units.mk0 _ (inv_ne_zero hN))

/-- Score-preserving local effects for a single channel and decoder. The trace
pairing lets callers use their existing adjoint representation. -/
private def ChannelLocalEffects (Φ : QuantumChannel ι μ) (D : ι → Matrix μ μ ℂ)
    (ψ : ι → ι → ℂ) : Prop :=
  ∃ E F : ι → Matrix ι ι ℂ,
    (∀ j (X : Matrix ι ι ℂ), trace (E j * X) =
      trace (D j * CStarMatrix.ofMatrix.symm (Φ.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)))) ∧
    LocalEffects E ψ (Fintype.card μ) F

private theorem channelLocalEffects_of_povm
    (ψ : ι → ι → ℂ) (hψ : ∀ j, star (ψ j) ⬝ᵥ ψ j = 1)
    (Φ : QuantumChannel ι μ) (D : ι → Matrix μ μ ℂ)
    (hD : ∀ j, (D j).PosSemidef) (hsD : ∑ j, D j = 1) :
    ChannelLocalEffects Φ D ψ := by
  obtain ⟨F, hF, hle, hscore, htrace⟩ :=
    PhaseRecordSpectralMemory.exists_memory_effect_family ψ hψ Φ D hD
  refine ⟨fun j => pullEffect Φ (D j), F, fun j X => pullEffect_trace Φ X (D j),
    fun j => (hF j).posSemidef, hle, hscore, ?_⟩
  calc
    ∑ j, (trace (F j)).re ≤ ∑ j, (trace (D j)).re :=
      Finset.sum_le_sum fun j _ => htrace j
    _ = (Fintype.card μ : ℝ) := by
      rw [← Complex.re_sum, ← trace_sum, hsD, trace_one]
      simp

private theorem channelLocalEffects_dilation (Φ : QuantumChannel ι μ)
    (D : ι → Matrix μ μ ℂ) (ψ : ι → ι → ℂ)
    (h : ChannelLocalEffects Φ D ψ) (V : Matrix (κ × μ) ι ℂ)
    (hact : ∀ X : Matrix ι ι ℂ, partialTraceLeft (V * X * Vᴴ) =
      CStarMatrix.ofMatrix.symm (Φ.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))) :
    ∃ F, LocalEffects (fun j => dilationAdjoint V (D j)) ψ (Fintype.card μ) F := by
  obtain ⟨E, F, he, hF⟩ := h
  have heq : E = fun j => dilationAdjoint V (D j) := by
    funext j
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro X
    rw [he, dilationAdjoint_trace, hact]
  exact ⟨F, heq ▸ hF⟩

/-- Strictly positive coordinate weights preserve independence of orthogonal phase rows. -/
private theorem phaseVector_independent_of_orthogonal_rows [Nonempty ι]
    (u : ι → ι → ℂ)
    (horth : ∀ j l, ∑ i, star (u j i) * u l i =
      if j = l then (Fintype.card ι : ℂ) else 0)
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    LinearIndependent ℂ (phaseVector u a) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro w h j
  have he (i : ι) : ∑ l, w l * u l i = 0 := by
    have hh := congrFun h i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, phaseVector] at hh
    have h0 : (a i : ℂ) * (∑ l, w l * u l i) = 0 := by
      rw [Finset.mul_sum, ← hh]
      exact Finset.sum_congr rfl fun _ _ => by ring
    exact (mul_eq_zero.mp h0).resolve_left (Complex.ofReal_ne_zero.mpr (ha i).ne')
  have hz : ∑ i, star (u j i) * (∑ l, w l * u l i) = 0 := by
    simp [he]
  have ht :
      (∑ i, star (u j i) * (∑ l, w l * u l i)) =
      ∑ l, w l * (∑ i, star (u j i) * u l i) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [ht] at hz
  simp_rw [horth, mul_ite, mul_zero] at hz
  rw [Finset.sum_eq_single j] at hz
  · have hn : (Fintype.card ι : ℂ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
    exact (mul_eq_zero.mp (by simpa using hz)).resolve_right hn
  · intro l _ hlj
    simp [Ne.symm hlj]
  · simp

/-- Four Fourier phase rows, in the convention (u_{ji}=i^{ji}). -/
def fourier4 : Fin 4 → Fin 4 → ℂ :=
  ![![1, 1, 1, 1], ![1, Complex.I, -1, -Complex.I],
    ![1, -1, 1, -1], ![1, -Complex.I, -1, Complex.I]]

theorem fourier4_norm (j i : Fin 4) : ‖fourier4 j i‖ = 1 := by
  fin_cases j <;> fin_cases i <;> simp [fourier4, Complex.norm_I]

private lemma fourier4_zero (j : Fin 4) : fourier4 j 0 = 1 := by
  fin_cases j <;> rfl

private lemma fourier4_sum (i : Fin 4) :
    ∑ j, fourier4 j i = if i = 0 then (Fintype.card (Fin 4) : ℂ) else 0 := by
  fin_cases i <;> norm_num [fourier4, Fin.sum_univ_succ]

private lemma fourier4_orth (j l : Fin 4) :
    ∑ i, star (fourier4 j i) * fourier4 l i = if j = l then (4 : ℂ) else 0 := by
  fin_cases j <;> fin_cases l <;>
    norm_num [fourier4, Fin.sum_univ_succ, Complex.star_def, Complex.conj_I, ← pow_two,
      Complex.I_sq]

private lemma gram_fourier4_im (a : Fin 4 → ℝ) :
    (gram (phaseVector fourier4 a 0) (phaseVector fourier4 a 1)).im =
      a 1 ^ 2 - a 3 ^ 2 := by
  simp only [gram_def, dotProduct, Fin.sum_univ_succ, phaseVector, fourier4]
  norm_num [phaseVector, Complex.star_def, Complex.mul_im, Complex.mul_re, pow_two, sub_eq_add_neg]

/-- Equality for a positive asymmetric Fourier profile contradicts the reality
of the projector Gram matrix. The score uses one CPTP encoder and one arbitrary
four-outcome POVM. The explicit local-effect premise is the only compression
input from the score upper-bound argument. -/
private theorem fourier4_profile_ne_upper_of_local_effects
    (a r : Fin 4 → ℝ) (τ : ℝ) (hp : PositiveClippedProfile a r 2 τ)
    (ha0 : a 0 = 1) (hasym : a 1 ≠ a 3)
    (Φ : QuantumChannel (Fin 4) (Fin 2))
    (D : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ)
    (hD : ∀ j, (D j).PosSemidef) (hsD : ∑ j, D j = 1)
    (local_effects : ChannelLocalEffects Φ D (phaseVector fourier4 fun i => r i * a i)) :
    (∑ j, (trace (D j * CStarMatrix.ofMatrix.symm (Φ.toCompletelyPositiveMap
      (CStarMatrix.ofMatrix (rankOneDensity (phaseVector fourier4 (fun i => r i * a i) j)))))).re)
      ≠ (∑ i, r i * a i ^ 2) ^ 2 := by
  intro heq
  obtain ⟨V, hV, hact⟩ := channel_kraus_stinespring.2 Φ
  obtain ⟨F, hF⟩ := channelLocalEffects_dilation Φ D _ local_effects V hact
  let E := fun j => dilationAdjoint V (D j)
  have hEs : ∑ j, E j = 1 := by
    simp only [E, ← map_sum, hsD, adjoint_one V hV]
  have he : ∑ j, (trace (E j * rankOneDensity (phaseVector fourier4 (fun i => r i * a i) j))).re =
      (∑ i, r i * a i ^ 2) ^ 2 := by
    simpa only [E, dilationAdjoint_trace, hact] using heq
  have hpLI := phaseVector_independent_of_orthogonal_rows fourier4
    (by simpa using fourier4_orth) a hp.1
  obtain ⟨hcan, hcol⟩ := saturated_local_effects_canonical fourier4 fourier4_norm a r 2 τ hp
    0 ha0 fourier4_zero fourier4_sum hpLI E F hEs hF he
  let c : ℝ := (Real.sqrt 2)⁻¹
  have hc : c ^ 2 = (2 : ℝ)⁻¹ := by simp [c, inv_pow]
  have hcc : (c : ℂ) * (c : ℂ) = (2 : ℂ)⁻¹ := by
    simpa only [Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_ofNat, pow_two, Complex.ofReal_mul] using
      congrArg Complex.ofReal hc
  have hc0 : (c : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by norm_num))))
  let v : Fin 4 → Fin 4 → ℂ := fun j => (c : ℂ) • phaseVector fourier4 a j
  have hv (j : Fin 4) : gram (v j) (v j) = 1 := by
    rw [show gram (v j) (v j) = (c : ℂ) * ((c : ℂ) *
        gram (phaseVector fourier4 a j) (phaseVector fourier4 a j)) by
      simp [v, gram, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]]
    rw [← mul_assoc, hcc, gram_phase fourier4 fourier4_norm, hp.2.2.1]
    norm_num
  have hvLI : LinearIndependent ℂ v := hpLI.units_smul (fun _ => Units.mk0 (c : ℂ) hc0)
  have hcoord (j : Fin 4) : v j 0 = (c : ℂ) := by simp [v, phaseVector, ha0, fourier4_zero]
  have hf (j : Fin 4) : F j = ((1 / 2 : ℝ) : ℂ) • rankOneDensity (v j) := by
    rw [hcan]
    ext i l
    simp only [rankOneDensity, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, v,
      Pi.smul_apply, smul_eq_mul, star_mul, Complex.star_def, Complex.conj_ofReal]
    rw [show Complex.ofReal (1 / 2 : ℝ) = (2 : ℂ)⁻¹ by norm_num]
    calc
      _ = (2 : ℂ)⁻¹ * ((c : ℂ) * (c : ℂ)) *
          (phaseVector fourier4 a j i * (starRingEnd ℂ) (phaseVector fourier4 a j l)) := by
            rw [hcc]
            norm_num [Fintype.card_fin]
      _ = _ := by ring
  have hdom (j : Fin 4) : ((1 / 2 : ℝ) : ℂ) • rankOneDensity (v j) ≤ E j := hf j ▸ hF.2.1 j
  have hcol' (j i : Fin 4) : E j i 0 = (((1 / 2 : ℝ) * c : ℝ) : ℂ) * v j i := by
    rw [hcol j i, hf]
    simp only [rankOneDensity, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, hcoord,
      smul_eq_mul, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul]
    ring
  obtain ⟨d, _, _, _, hGram⟩ := threshold_projector_gram V hV D hD hsD v hv hvLI 0 c (1 / 2)
    (by norm_num) (by simpa using hc) hcoord hdom hcol' (by norm_num) (by norm_num)
  have hreal := trace_pair_im_zero
    (posSemidef_vecMulVec_self_star (d 0)).isHermitian
    (posSemidef_vecMulVec_self_star (d 1)).isHermitian
  change (trace (rankOneDensity (d 0) * rankOneDensity (d 1))).im = 0 at hreal
  rw [← hGram 0 1] at hreal
  have him : (gram (v 0) (v 1)).im = (1 / 2 : ℝ) * (a 1 ^ 2 - a 3 ^ 2) := by
    have h : gram (v 0) (v 1) = (2 : ℂ)⁻¹ *
        gram (phaseVector fourier4 a 0) (phaseVector fourier4 a 1) := by
      simp only [v, gram_def, star_smul, Complex.star_def, Complex.conj_ofReal,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, ← mul_assoc, hcc]
    rw [h, show (2 : ℂ)⁻¹ = ((1 / 2 : ℝ) : ℂ) by norm_num,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, gram_fourier4_im]
  rw [him] at hreal
  have hsquare : a 1 ^ 2 = a 3 ^ 2 := by linarith
  exact hasym (mul_self_inj_of_nonneg (hp.1 1).le (hp.1 3).le |>.mp (by
    simpa only [pow_two] using hsquare))

/-- Tail norm for the positive four-state Fourier family. -/
def fourierTail (t : Fin 4 → ℝ) : ℝ :=
  Real.sqrt (t 1 ^ 2 + t 2 ^ 2 + t 3 ^ 2)

def dominantProfile (t : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  if i = 0 then 1 else t i / fourierTail t

def dominantSlope (t : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  if i = 0 then t 0 else fourierTail t

lemma dominantProfile_data (t : Fin 4 → ℝ) (ht : ∀ i, 0 < t i)
    (hn : ∑ i, t i ^ 2 = 1) (hdom : (1 / 2 : ℝ) ≤ t 0 ^ 2) :
    PositiveClippedProfile (dominantProfile t) (dominantSlope t) 2 (fourierTail t) ∧
    (∀ i, dominantSlope t i * dominantProfile t i = t i) ∧
    ∑ i, dominantSlope t i * dominantProfile t i ^ 2 = t 0 + fourierTail t := by
  have hR : 0 < fourierTail t := Real.sqrt_pos.2
    (by nlinarith [pow_pos (ht 1) 2, sq_nonneg (t 2), sq_nonneg (t 3)])
  have hR2 : fourierTail t ^ 2 = t 1 ^ 2 + t 2 ^ 2 + t 3 ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hT : t 0 ^ 2 + t 1 ^ 2 + t 2 ^ 2 + t 3 ^ 2 = 1 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hn
  have hRle : fourierTail t ≤ t 0 := (sq_le_sq₀ hR.le (ht 0).le).mp (by linarith)
  have ha (i : Fin 4) : 0 < dominantProfile t i := by
    by_cases hi : i = 0
    · simp [dominantProfile, hi]
    · simpa [dominantProfile, hi] using div_pos (ht i) hR
  have ha1 (i : Fin 4) : dominantProfile t i ≤ 1 := by
    fin_cases i <;> norm_num [dominantProfile]
    all_goals try apply (div_le_iff₀ hR).2
    all_goals nlinarith [ht (1 : Fin 4), ht (2 : Fin 4), ht (3 : Fin 4),
      sq_nonneg (t 1), sq_nonneg (t 2), sq_nonneg (t 3), hR2]
  have htail : (t 1 / fourierTail t) ^ 2 + (t 2 / fourierTail t) ^ 2 +
      (t 3 / fourierTail t) ^ 2 = 1 := by
    rw [div_pow, div_pow, div_pow, ← add_div, ← add_div, ← hR2, div_self (pow_ne_zero _ hR.ne')]
  have ham : ∑ i, dominantProfile t i ^ 2 = 2 := by
    simp [Fin.sum_univ_succ, dominantProfile]
    linarith
  have hr (i : Fin 4) : fourierTail t ≤ dominantSlope t i := by
    by_cases hi : i = 0 <;> simp [dominantSlope, hi, hRle]
  have hrs (i : Fin 4) (hi : dominantSlope t i ≠ fourierTail t) : dominantProfile t i = 1 := by
    by_cases hz : i = 0
    · simp [dominantProfile, hz]
    · exact (hi (by simp [dominantSlope, hz])).elim
  have htform (i : Fin 4) : dominantSlope t i * dominantProfile t i = t i := by
    by_cases hi : i = 0
    · subst i
      simp [dominantSlope, dominantProfile]
    · simp [dominantSlope, dominantProfile, hi, div_eq_mul_inv, mul_left_comm, hR.ne']
  refine ⟨⟨ha, ha1, ham, hR, hr, hrs⟩, htform, ?_⟩
  norm_num [Fin.sum_univ_succ, dominantSlope, dominantProfile]
  linear_combination fourierTail t * htail

/-- Exact nonattainment for positive normalized Fourier amplitudes with
(t_0^2 ge 1/2) and (t_1 
e t_3). The unaveraged equality in the statement
corresponds to success probability ((t_0+|t_{mathrm{tail}}|)^2/4). -/
private theorem fourier4_dominant_ne_upper_of_local_effects
    (t : Fin 4 → ℝ) (ht : ∀ i, 0 < t i) (hn : ∑ i, t i ^ 2 = 1)
    (hdominant : (1 / 2 : ℝ) ≤ t 0 ^ 2) (hasym : t 1 ≠ t 3)
    (Φ : QuantumChannel (Fin 4) (Fin 2)) (D : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ)
    (hD : ∀ j, (D j).PosSemidef) (hsD : ∑ j, D j = 1)
    (local_effects : ChannelLocalEffects Φ D (phaseVector fourier4 t)) :
    (∑ j, (trace (D j * CStarMatrix.ofMatrix.symm (Φ.toCompletelyPositiveMap
      (CStarMatrix.ofMatrix (rankOneDensity (phaseVector fourier4 t j)))))).re)
      ≠ (t 0 + fourierTail t) ^ 2 := by
  obtain ⟨hp, htform, hsum⟩ := dominantProfile_data t ht hn hdominant
  have hprofile : dominantProfile t 1 ≠ dominantProfile t 3 := by
    intro heq
    have hR := hp.2.2.2.1
    apply hasym
    apply (div_left_inj' hR.ne').mp
    simpa [dominantProfile] using heq
  have hfun : (fun i => dominantSlope t i * dominantProfile t i) = t := funext htform
  have h := fourier4_profile_ne_upper_of_local_effects (dominantProfile t) (dominantSlope t)
    (fourierTail t) hp (by simp [dominantProfile]) hprofile Φ D hD hsD (by
      simpa only [hfun] using local_effects)
  simpa only [hfun, hsum] using h

/-- The environment-free count applies directly to physical strategies once
the score-preserving effects are supplied by the finite compression theorem. -/
theorem saturated_channel_equality_card_le_memory_sq [Nonempty ι]
    (u : ι → ι → ℂ) (hu : ∀ j i, ‖u j i‖ = 1)
    (a r : ι → ℝ) (τ : ℝ) (hp : PositiveClippedProfile a r (Fintype.card μ) τ)
    (k : ι) (hk : a k = 1) (hu0 : ∀ j, u j k = 1)
    (hsumu : ∀ i, ∑ j, u j i = if i = k then (Fintype.card ι : ℂ) else 0)
    (hli : LinearIndependent ℂ (phaseVector u a))
    (hψ : ∀ j, star (phaseVector u (fun i => r i * a i) j) ⬝ᵥ
      phaseVector u (fun i => r i * a i) j = 1)
    (Φ : QuantumChannel ι μ) (D : ι → Matrix μ μ ℂ)
    (hD : ∀ j, (D j).PosSemidef) (hsD : ∑ j, D j = 1)
    (hscore : ∑ j, (trace (D j * channelMatrix Φ
      (rankOneDensity (phaseVector u (fun i => r i * a i) j)))).re =
        (∑ i, r i * a i ^ 2) ^ 2) :
    Fintype.card ι ≤ Fintype.card μ ^ 2 := by
  obtain ⟨E, F, hpair, hF⟩ := channelLocalEffects_of_povm _ hψ Φ D hD hsD
  have hE : E = fun j => pullEffect Φ (D j) := by
    funext j
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro X
    rw [hpair, pullEffect_trace]
    rfl
  refine saturated_equality_card_le_memory_sq u hu a r τ hp k hk hu0 hsumu hli
    (pullEffect Φ) (pullEffect_one Φ) D hsD F (hE ▸ hF) ?_
  simpa only [pullEffect_trace] using hscore

/-- Exact nonattainment for a single arbitrary encoder and arbitrary POVM
on the positive dominant-coordinate asymmetric four-state Fourier family. -/
theorem fourier4_dominant_ne_upper
    (t : Fin 4 → ℝ) (ht : ∀ i, 0 < t i) (hn : ∑ i, t i ^ 2 = 1)
    (hdominant : (1 / 2 : ℝ) ≤ t 0 ^ 2) (hasym : t 1 ≠ t 3)
    (Φ : QuantumChannel (Fin 4) (Fin 2)) (D : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ)
    (hD : ∀ j, (D j).PosSemidef) (hsD : ∑ j, D j = 1) :
    (∑ j, (trace (D j * CStarMatrix.ofMatrix.symm (Φ.toCompletelyPositiveMap
      (CStarMatrix.ofMatrix (rankOneDensity (phaseVector fourier4 t j)))))).re)
      ≠ (t 0 + fourierTail t) ^ 2 := by
  apply fourier4_dominant_ne_upper_of_local_effects t ht hn hdominant hasym Φ D hD hsD
  exact channelLocalEffects_of_povm (phaseVector fourier4 t)
    (fun j => JointRecordDecoding.phaseVector_norm fourier4 t fourier4_norm hn j) Φ D hD hsD

end

end PhaseMemorySaturatedFrame
