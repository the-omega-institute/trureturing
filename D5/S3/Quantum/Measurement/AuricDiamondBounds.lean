import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks
import D5.S3.Quantum.Measurement.AuricRootTrace
import D5.S3.Weil.ZetaLinear.RankTrace

/-! # Trace-norm bounds from an effect and a positive majorant -/

namespace D5.S3.Quantum.Measurement.AuricDiamondBounds

open _root_.Matrix D5.S3.Quantum.Foundation
open D5.S3.Quantum.Foundation.FiniteTraceDistance (trace_norm_jordan_mass)
open scoped ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- A positive majorant bounds the unhalved norm of a trace-zero
difference by twice the majorant's mass. -/
theorem traceNorm_le_twice_trace_of_majorant (D H : Matrix n n ℂ) (hD : D.trace = 0)
    (hH : H.PosSemidef) (hmajor : (H - D).PosSemidef) :
    FiniteTraceDistance.traceNorm D ≤ 2 * H.trace.re := by
  classical
  have h := FiniteTraceDistance.traceNorm_add_le H (-(H - D))
  rw [FiniteTraceDistance.traceNorm_neg] at h
  have hrewrite : H + -(H - D) = D := by abel
  have hnorm (X : Matrix n n ℂ) (hX : X.PosSemidef) :
      FiniteTraceDistance.traceNorm X = X.trace.re := by
    unfold FiniteTraceDistance.traceNorm
    rw [show Xᴴ * X = X ^ 2 by rw [hX.1.eq, pow_two], CFC.sqrt_sq X]
    exact RCLike.re_to_complex
  rw [hrewrite, hnorm H hH, hnorm (H-D) hmajor] at h
  simpa [Matrix.trace_sub, hD, two_mul] using h

/-- Any effect lower-bounds the unhalved trace-norm error on a trace-zero
Hermitian difference by twice its observed output probability difference. -/
theorem twice_effect_trace_le_traceNorm (D E : Matrix n n ℂ) (hD : D.IsHermitian)
    (htrace : D.trace = 0) (hE : E.PosSemidef) (hle : (1 - E).PosSemidef) :
    2 * (E * D).trace.re ≤ FiniteTraceDistance.traceNorm D := by
  let P : Matrix n n ℂ := posPart D
  let N : Matrix n n ℂ := negPart D
  have hP : P.PosSemidef := (CFC.posPart_nonneg D).posSemidef
  have hN : N.PosSemidef := (CFC.negPart_nonneg D).posSemidef
  have hdecomp : P - N = D := CFC.posPart_sub_negPart D hD
  have heN := RHLinalg.trace_mul_nonneg_of_posSemidef hE hN
  have heP := RHLinalg.trace_mul_nonneg_of_posSemidef hle hP
  change 0 ≤ (E * N).trace.re at heN
  change 0 ≤ ((1 - E) * P).trace.re at heP
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at heP
  have htr := congrArg (fun X : Matrix n n ℂ => X.trace.re) hdecomp
  rw [Matrix.trace_sub, Complex.sub_re, htrace, Complex.zero_re] at htr
  have hpair : (E * D).trace.re = (E * P).trace.re - (E * N).trace.re := by
    rw [← hdecomp, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  have hnorm : FiniteTraceDistance.traceNorm D = P.trace.re + N.trace.re :=
    trace_norm_jordan_mass D hD
  linarith

section Amplification

open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance
open D5.S3.Quantum.Measurement.AuricRootTrace

variable {a b r : Type*} [Fintype a] [DecidableEq a] [Fintype b]
  [Fintype r] [DecidableEq r]

private noncomputable def referenceLift (F : MatrixMap a b ℂ) : MatrixMap (a × r) (b × r) ℂ :=
  MatrixMap.kron F LinearMap.id

private theorem referenceLift_apply (F : MatrixMap a b ℂ)
    (X : Matrix (a × r) (a × r) ℂ) (i j : b) (s t : r) :
    referenceLift F X (i, s) (j, t) = F (fun u v => X (u, s) (v, t)) i j := by
  rw [referenceLift, MatrixMap.kron_def]
  calc
    _ = ∑ u, ∑ v, X (u, s) (v, t) * F (Matrix.single u v 1) i j := by
      congr! 2 with u v
      simp [Matrix.single, ite_and, Finset.sum_ite_irrel, mul_comm]
    _ = _ := by
      classical
      have h := congrArg (fun G : MatrixMap a b ℂ =>
        G (fun u v => X (u, s) (v, t)) i j) (MatrixMap.choi_map_inv F)
      exact h

private theorem referenceLift_sub (F G : MatrixMap a b ℂ) :
    (referenceLift (r := r) (F - G)) = referenceLift F - referenceLift G := by
  ext X ⟨i, s⟩ ⟨j, t⟩
  simp only [LinearMap.sub_apply, Matrix.sub_apply, referenceLift_apply]
  rfl

private theorem trace_referenceLift (F : MatrixMap a b ℂ) (c : ℂ)
    (hF : ∀ X, (F X).trace = c * X.trace) (X : Matrix (a × r) (a × r) ℂ) :
    (referenceLift F X).trace = c * X.trace := by
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, referenceLift_apply]
  rw [Finset.sum_comm]
  change (∑ s : r, (F (fun u v => X (u, s) (v, s))).trace) =
    c * ∑ u : a, ∑ s : r, X (u, s) (u, s)
  calc
    _ = ∑ s : r, c * ∑ u : a, X (u, s) (u, s) := by
      apply Finset.sum_congr rfl
      intro s _
      exact hF (fun u v => X (u, s) (v, s))
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

/-- The reference amplitudes in a weighted maximally correlated input
scale the corresponding rows and columns of the Choi matrix. -/
theorem weighted_purification_output [DecidableEq b] (F : MatrixMap a b ℂ) (w : a → ℂ) :
    let v : a × a → ℂ := fun x => if x.1 = x.2 then w x.2 else 0
    let D : Matrix (b × a) (b × a) ℂ := diagonal fun x => w x.2
    MatrixMap.kron F (LinearMap.id : MatrixMap a a ℂ) (vecMulVec v (star v)) =
      D * F.choi_matrix * Dᴴ := by
  classical
  dsimp only
  change referenceLift F _ = _
  ext ⟨i, s⟩ ⟨j, t⟩
  rw [referenceLift_apply, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  let X : Matrix a a ℂ := Matrix.of fun u v : a => vecMulVec
      (fun x : a × a => if x.1 = x.2 then w x.2 else 0)
      (star (fun x : a × a => if x.1 = x.2 then w x.2 else 0)) (u, s) (v, t)
  have hp : X = (w s * star (w t)) • Matrix.single s t 1 := by
    ext u v
    by_cases hs : u = s <;> by_cases ht : v = t <;>
      simp [X, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec, Matrix.single,
        Pi.star_apply, hs, ht, Ne.symm, eq_comm]
  change F X i j = _
  rw [hp, F.map_smul]
  simp [MatrixMap.choi_matrix, Matrix.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]

/-- A completely positive majorant with a fixed trace factor controls the error
on every reference-extended positive input, via complete positivity of its
difference from the error map. -/
theorem amplified_positive_traceNorm_le_of_completelyPositive_majorant
    (F H : MatrixMap a b ℂ) (c : ℝ)
    (hH : H.IsCompletelyPositive) (hmajor : (H - F).IsCompletelyPositive)
    (htrace : ∀ X, (F X).trace = 0)
    (htraceH : ∀ X, (H X).trace = (c : ℂ) * X.trace)
    (ρ : Matrix (a × r) (a × r) ℂ) (hρ : ρ.PosSemidef) :
    FiniteTraceDistance.traceNorm (MatrixMap.kron F (LinearMap.id : MatrixMap r r ℂ) ρ) ≤
      2 * c * ρ.trace.re := by
  classical
  change FiniteTraceDistance.traceNorm (referenceLift F ρ) ≤ _
  have hDtrace : (referenceLift F ρ).trace = 0 := by
    simpa using trace_referenceLift F 0 (fun X => by simpa using htrace X) ρ
  have hHpsd : (referenceLift H ρ).PosSemidef := hH.of_Fintype r hρ
  have hmajorpsd : (referenceLift H ρ - referenceLift F ρ).PosSemidef := by
    rw [← LinearMap.sub_apply, ← referenceLift_sub]
    exact MatrixMap.IsCompletelyPositive.of_Fintype (M := H - F) hmajor r hρ
  have h := traceNorm_le_twice_trace_of_majorant _ _ hDtrace hHpsd hmajorpsd
  rw [trace_referenceLift H (c : ℂ) htraceH, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, ← mul_assoc] at h
  exact h

omit [DecidableEq n] [DecidableEq r] in
private theorem traceNorm_le_of_positive_inputs (T : Matrix n n ℂ →ₗ[ℂ] Matrix (b × r) (b × r) ℂ)
    (c : ℝ) (hT : ∀ P, P.PosSemidef → FiniteTraceDistance.traceNorm (T P) ≤ c * P.trace.re)
    (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    FiniteTraceDistance.traceNorm (T X) ≤ c * FiniteTraceDistance.traceNorm X := by
  classical
  let P : Matrix n n ℂ := posPart X
  let N : Matrix n n ℂ := negPart X
  have hP : P.PosSemidef := (CFC.posPart_nonneg X).posSemidef
  have hN : N.PosSemidef := (CFC.negPart_nonneg X).posSemidef
  have hdecomp : P - N = X := CFC.posPart_sub_negPart X hX
  have hnorm : FiniteTraceDistance.traceNorm X = P.trace.re + N.trace.re :=
    trace_norm_jordan_mass X hX
  rw [hnorm, ← hdecomp, map_sub, sub_eq_add_neg, mul_add]
  apply (FiniteTraceDistance.traceNorm_add_le _ _).trans
  rw [FiniteTraceDistance.traceNorm_neg]
  exact add_le_add (hT P hP) (hT N hN)

private def hermitianBlock (X : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  Matrix.fromBlocks 0 X Xᴴ 0

omit [Fintype n] [DecidableEq n] in
private theorem hermitianBlock_isHermitian (X : Matrix n n ℂ) :
    (hermitianBlock X).IsHermitian := by
  unfold IsHermitian hermitianBlock
  simp [fromBlocks_conjTranspose]

omit [DecidableEq n] in
private theorem traceNorm_hermitianBlock (X : Matrix n n ℂ) :
    FiniteTraceDistance.traceNorm (hermitianBlock X) = 2 * FiniteTraceDistance.traceNorm X := by
  classical
  have h₁ : 0 ≤ X * Xᴴ := (Matrix.posSemidef_self_mul_conjTranspose X).nonneg
  have h₂ : 0 ≤ Xᴴ * X := (Matrix.posSemidef_conjTranspose_mul_self X).nonneg
  unfold FiniteTraceDistance.traceNorm at ⊢
  rw [(hermitianBlock_isHermitian X).eq]
  have hblock : hermitianBlock X * hermitianBlock X =
      fromBlocks (X * Xᴴ) 0 0 (Xᴴ * X) := by
    simp [hermitianBlock, fromBlocks_multiply]
  rw [hblock, sqrt_direct_sum _ _ h₁ h₂]
  have hsum : (fromBlocks (CFC.sqrt (X * Xᴴ)) 0 0 (CFC.sqrt (Xᴴ * X))).trace.re =
      (CFC.sqrt (X * Xᴴ)).trace.re + (CFC.sqrt (Xᴴ * X)).trace.re := by
    simp [Matrix.trace, Fintype.sum_sum_type]
  change (fromBlocks (CFC.sqrt (X * Xᴴ)) 0 0 (CFC.sqrt (Xᴴ * X))).trace.re =
    2 * FiniteTraceDistance.traceNorm X
  have heq : (CFC.sqrt (X * Xᴴ)).trace.re = FiniteTraceDistance.traceNorm X := by
    have h := traceNorm_conjTranspose X
    unfold FiniteTraceDistance.traceNorm at h
    rwa [conjTranspose_conjTranspose] at h
  rw [hsum, heq, two_mul]
  rfl

private theorem referenceLift_maps_hermitian (T : MatrixMap a b ℂ)
    (hT : T.IsCompletelyPositive) (X : Matrix (a × r) (a × r) ℂ) (hX : X.IsHermitian) :
    (referenceLift T X).IsHermitian := by
  classical
  have hP : (posPart X).PosSemidef := (CFC.posPart_nonneg X).posSemidef
  have hN : (negPart X).PosSemidef := (CFC.negPart_nonneg X).posSemidef
  have hP' : (referenceLift T (posPart X)).PosSemidef := hT.of_Fintype r hP
  have hN' : (referenceLift T (negPart X)).PosSemidef := hT.of_Fintype r hN
  rw [← CFC.posPart_sub_negPart X hX, map_sub]
  exact hP'.isHermitian.sub hN'.isHermitian

/-- An orthonormal output test on a weighted purification gives a trace-norm
lower bound in terms of the same weighted Choi matrix. -/
theorem weighted_choi_trace_le_amplified_traceNorm [DecidableEq b]
    {k : Type*} [Fintype k] [DecidableEq k] (F G : MatrixMap a b ℂ)
    (hF : F.IsCompletelyPositive) (hG : G.IsCompletelyPositive)
    (htrace : ∀ X, (F X).trace = (G X).trace)
    (w : a → ℂ) (V : Matrix (b × a) k ℂ) (hV : Vᴴ * V = 1) :
    let v : a × a → ℂ := fun x => if x.1 = x.2 then w x.2 else 0
    let D : Matrix (b × a) (b × a) ℂ := diagonal fun x => w x.2
    2 * (Vᴴ * D * (F - G).choi_matrix * Dᴴ * V).trace.re ≤
      FiniteTraceDistance.traceNorm
        (MatrixMap.kron (F - G) (LinearMap.id : MatrixMap a a ℂ) (vecMulVec v (star v))) := by
  dsimp only
  let v : a × a → ℂ := fun x => if x.1 = x.2 then w x.2 else 0
  let D : Matrix (b × a) (b × a) ℂ := diagonal fun x => w x.2
  let X := vecMulVec v (star v)
  let Y := referenceLift (F - G) X
  let E := V * Vᴴ
  have hYtrace : Y.trace = 0 := by
    change (referenceLift (F - G) X).trace = 0
    have hT := trace_referenceLift (F - G) 0 (fun A => by
      rw [LinearMap.sub_apply, Matrix.trace_sub, htrace, sub_self, zero_mul]) X
    simpa using hT
  have hX : X.PosSemidef := Matrix.posSemidef_vecMulVec_self_star v
  have hY : Y.IsHermitian := by
    change (referenceLift (F - G) X).IsHermitian
    rw [referenceLift_sub, LinearMap.sub_apply]
    exact (referenceLift_maps_hermitian F hF X hX.isHermitian).sub
      (referenceLift_maps_hermitian G hG X hX.isHermitian)
  have hE : E.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose V
  have hcomp : (1 - E).PosSemidef := by
    have hEid : E * E = E := by
      dsimp [E]
      rw [Matrix.mul_assoc V, ← Matrix.mul_assoc Vᴴ, hV, Matrix.one_mul]
    have heq : (1 - E)ᴴ * (1 - E) = 1 - E := by
      rw [conjTranspose_sub, conjTranspose_one, hE.isHermitian.eq, Matrix.sub_mul,
        Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hEid, sub_self, sub_zero]
    rw [← heq]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  have h := twice_effect_trace_le_traceNorm Y E hY hYtrace hE hcomp
  have htraceEq : (E * Y).trace = (Vᴴ * Y * V).trace := by
    rw [Matrix.mul_assoc V, Matrix.trace_mul_comm]
  have hchoi : Y = D * (F - G).choi_matrix * Dᴴ :=
    weighted_purification_output (F - G) w
  rw [htraceEq] at h
  rw [show (Vᴴ * D * (F - G).choi_matrix * Dᴴ * V) = Vᴴ * Y * V by
    rw [hchoi]
    simp only [Matrix.mul_assoc]]
  exact h

/-- The majorant bounds the unhalved reference-stabilized trace norm on
all complex operators, including non-Hermitian inputs. -/
theorem amplified_traceNorm_le_of_completelyPositive_majorant
    (F H : MatrixMap a b ℂ) (c : ℝ)
    (hH : H.IsCompletelyPositive) (hmajor : (H - F).IsCompletelyPositive)
    (htrace : ∀ X, (F X).trace = 0)
    (htraceH : ∀ X, (H X).trace = (c : ℂ) * X.trace)
    (X : Matrix (a × r) (a × r) ℂ) :
    FiniteTraceDistance.traceNorm (MatrixMap.kron F (LinearMap.id : MatrixMap r r ℂ) X) ≤
      2 * c * FiniteTraceDistance.traceNorm X := by
  classical
  let eA := Equiv.prodSumDistrib a r r
  let eB := Equiv.prodSumDistrib b r r
  let Y := (hermitianBlock X).submatrix eA eA
  let Z := referenceLift F Y
  let W := referenceLift F X
  have hY : Y.IsHermitian := (hermitianBlock_isHermitian X).submatrix eA
  have hZ : Z.IsHermitian := by
    have h₁ := referenceLift_maps_hermitian H hH Y hY
    have h₂ := referenceLift_maps_hermitian (H - F) hmajor Y hY
    rw [referenceLift_sub, LinearMap.sub_apply] at h₂
    have h := h₁.sub h₂
    rwa [sub_sub_cancel] at h
  have hblock : Z.submatrix eB.symm eB.symm = hermitianBlock W := by
    have hTopLeft (i j : b) (s t : r) :
        Z (i, Sum.inl s) (j, Sum.inl t) = 0 := by
      change referenceLift F Y (i, Sum.inl s) (j, Sum.inl t) = 0
      rw [referenceLift_apply]
      change F (0 : Matrix a a ℂ) i j = 0
      rw [map_zero]
      rfl
    have hTopRight (i j : b) (s t : r) :
        Z (i, Sum.inl s) (j, Sum.inr t) = W (i, s) (j, t) := by
      change referenceLift F Y (i, Sum.inl s) (j, Sum.inr t) =
        referenceLift F X (i, s) (j, t)
      rw [referenceLift_apply, referenceLift_apply]
      rfl
    have hBottomRight (i j : b) (s t : r) :
        Z (i, Sum.inr s) (j, Sum.inr t) = 0 := by
      change referenceLift F Y (i, Sum.inr s) (j, Sum.inr t) = 0
      rw [referenceLift_apply]
      change F (0 : Matrix a a ℂ) i j = 0
      rw [map_zero]
      rfl
    ext x y
    rcases x with ⟨i, s⟩ | ⟨i, s⟩ <;> rcases y with ⟨j, t⟩ | ⟨j, t⟩
    · exact hTopLeft i j s t
    · exact hTopRight i j s t
    · change Z (i, Sum.inr s) (j, Sum.inl t) = star (W (j, t) (i, s))
      rw [← hTopRight j i t s]
      exact (congrFun (congrFun hZ.eq (i, Sum.inr s)) (j, Sum.inl t)).symm
    · exact hBottomRight i j s t
  have h :=
    traceNorm_le_of_positive_inputs (referenceLift (r := r ⊕ r) F) (2 * c)
      (amplified_positive_traceNorm_le_of_completelyPositive_majorant F H c hH hmajor htrace htraceH)
      Y hY
  change FiniteTraceDistance.traceNorm Z ≤ 2 * c * FiniteTraceDistance.traceNorm Y at h
  have hnY : FiniteTraceDistance.traceNorm Y = 2 * FiniteTraceDistance.traceNorm X :=
    (traceNorm_submatrix_equiv _ eA eA).trans (traceNorm_hermitianBlock X)
  rw [hnY] at h
  have hn : FiniteTraceDistance.traceNorm Z = 2 * FiniteTraceDistance.traceNorm W :=
    (traceNorm_submatrix_equiv Z eB.symm eB.symm).symm.trans
      (congrArg FiniteTraceDistance.traceNorm hblock |>.trans (traceNorm_hermitianBlock W))
  rw [hn] at h
  change FiniteTraceDistance.traceNorm W ≤ _
  linarith only [h]

end Amplification

end D5.S3.Quantum.Measurement.AuricDiamondBounds
