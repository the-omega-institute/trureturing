/- GID: D5/S3/Quantum/Recovery/ActualChannelAlgebra
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/ActualChannelAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual Choi and spectral channel helpers consumed by whole ST37. -/

/-
These declarations are consumed on the live proof path of
Original8340Global.whole_original_ST37. They retain actual complex matrices,
canonical Euclidean/tensor structures and the original natural-number cases.
They receive no independent new-content credit: their retention is as consumed
helpers for the whole original theorem. The associated public-declaration
escape audit is separate from Lean acceptance; no declared_validated result is
claimed without a successful source-bound native registration report.
-/

import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import D5.S3.Quantum.Recovery.PointwiseTensorRecovery
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-! Actual input-first Choi matrix and its specified redundant root columns. -/

noncomputable section
open scoped Matrix MatrixOrder ComplexOrder BigOperators Matrix.Norms.Elementwise
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery

set_option backward.isDefEq.respectTransparency false

namespace Original8340Global
open PhyslibLeaf

def inputChoi {d n : Type*} [Fintype d] [DecidableEq d] [Fintype n] [DecidableEq n]
    (N : MatrixMap d n ℂ) : Matrix (d × n) (d × n) ℂ :=
  fun p q => N (Matrix.single p.1 q.1 1) p.2 q.2

def sqrtColumn {d n : Type*} [Fintype d] [DecidableEq d] [Fintype n] [DecidableEq n]
    (N : MatrixMap d n ℂ) (mu : d × n) : Matrix n d ℂ :=
  fun a i => CFC.sqrt (inputChoi N) (i, a) mu

set_option maxHeartbeats 3000000 in
-- Finite Choi and trace identities are checked on their actual matrix entries.
theorem inputChoi_index_swap {d n : Type*} [Fintype d] [DecidableEq d]
    [Fintype n] [DecidableEq n] (N : MatrixMap d n ℂ) :
    inputChoi N = N.choi_matrix.submatrix Prod.swap Prod.swap := rfl

set_option maxHeartbeats 3000000 in
-- Finite Choi and trace identities are checked on their actual matrix entries.
theorem inputChoi_posSemidef {d n : Type*} [Fintype d] [DecidableEq d]
    [Fintype n] [DecidableEq n] (N : MatrixMap d n ℂ) (hN : N.IsCompletelyPositive) :
    (inputChoi N).PosSemidef := by
  rw [inputChoi_index_swap]
  exact ((MatrixMap.choi_PSD_iff_CP_map N).mp hN).submatrix Prod.swap

set_option maxHeartbeats 3000000 in
-- Finite Choi and trace identities are checked on their actual matrix entries.
theorem kraus_normalization_from_actual_trace {s n d : Type*}
    [Fintype s] [Fintype n] [DecidableEq n] [Fintype d] [DecidableEq d]
    (K : s → Matrix n d ℂ)
    (hTP : ∀ X : Matrix d d ℂ, Matrix.trace (∑ a, K a * X * (K a)ᴴ) = Matrix.trace X) :
    ∑ a, (K a)ᴴ * K a = 1 := by
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro X
  rw [Matrix.mul_one, Matrix.mul_sum, Matrix.trace_sum]
  calc
    _ = Matrix.trace (∑ a, K a * X * (K a)ᴴ) := by
      rw [Matrix.trace_sum]
      apply Finset.sum_congr rfl
      intro a ha
      symm
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
    _ = Matrix.trace X := hTP X

set_option maxHeartbeats 3000000 in
-- Finite Choi and trace identities are checked on their actual matrix entries.
theorem actual_sqrt_columns_kraus {d n : Type*} [Fintype d] [DecidableEq d]
    [Fintype n] [DecidableEq n] (N : MatrixMap d n ℂ)
    (hCP : N.IsCompletelyPositive)
    (hTP : ∀ X, Matrix.trace (N X) = Matrix.trace X) :
    (∀ X : Matrix d d ℂ,
      N X = ∑ mu, sqrtColumn N mu * X * (sqrtColumn N mu)ᴴ) ∧
    (∑ mu, (sqrtColumn N mu)ᴴ * sqrtColumn N mu) = 1 := by
  classical
  have hJ := inputChoi_posSemidef N hCP
  have hS : (CFC.sqrt (inputChoi N))ᴴ = CFC.sqrt (inputChoi N) :=
    (Matrix.LE.le.posSemidef (CFC.sqrt_nonneg (inputChoi N))).isHermitian.eq
  have hSquare : CFC.sqrt (inputChoi N) * (CFC.sqrt (inputChoi N))ᴴ = inputChoi N := by
    rw [hS]
    exact CFC.sqrt_mul_sqrt_self (inputChoi N) hJ.nonneg
  have heq : N.choi_matrix = (MatrixMap.of_kraus (sqrtColumn N) (sqrtColumn N)).choi_matrix := by
    rw [MatrixMap.choi_of_kraus]
    ext ⟨a, i⟩ ⟨b, j⟩
    have h := congrFun (congrFun hSquare (i, a)) (j, b)
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
      Matrix.vecMulVec_apply, inputChoi, MatrixMap.choi_matrix, sqrtColumn] using h.symm
  have hN : N = MatrixMap.of_kraus (sqrtColumn N) (sqrtColumn N) :=
    MatrixMap.choi_matrix_inj heq
  have hAction (X : Matrix d d ℂ) : N X = ∑ mu, sqrtColumn N mu * X * (sqrtColumn N mu)ᴴ := by
    simpa only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk] using
      congrArg (fun f : MatrixMap d n ℂ => f X) hN
  refine ⟨hAction, kraus_normalization_from_actual_trace (sqrtColumn N) ?_⟩
  intro X
  rw [← hAction X]
  exact hTP X

set_option maxHeartbeats 3000000 in
-- Actual CP data are represented once; no smooth Kraus choice is assumed.
theorem actual_cptp_left_inverse_spectral_algebra
    {d n : ℕ} (hd : 0 < d)
    (N : MatrixMap (Fin d) (Fin n) ℂ)
    (hCP : N.IsCompletelyPositive)
    (hTP : ∀ T, Matrix.trace (N T) = Matrix.trace T)
    (hLeft : ∃ R : MatrixMap (Fin n) (Fin d) ℂ,
      R.IsCompletelyPositive ∧ (∀ T, Matrix.trace (R T) = Matrix.trace T) ∧
      ∀ T, R (N T) = T) :
      let Q := N 1
      let P := spectralSupport Q
      let W := spectralInverseSqrt Q
      let pi := fun T => W * N T * W
      pi 1 = P ∧ (∀ T, (pi T)ᴴ = pi Tᴴ) ∧
      (∀ T U, pi T * pi U = pi (T * U)) ∧
      (∀ T, Q * pi T = pi T * Q) ∧ (∀ T, N T = Q * pi T) := by
  classical
  let v : Fin d := ⟨0, hd⟩
  obtain ⟨R, hRCP, hRTP, hRL⟩ := hLeft
  let E := sqrtColumn N
  let A := sqrtColumn R
  obtain ⟨hNE, hETP⟩ := actual_sqrt_columns_kraus N hCP hTP
  obtain ⟨hRA, hATP⟩ := actual_sqrt_columns_kraus R hRCP hRTP
  have hleft (T : Matrix (Fin d) (Fin d) ℂ) :
      (∑ b, A b * (∑ a, E a * T * (E a)ᴴ) * (A b)ᴴ) = T := by
    rw [← hNE T, ← hRA]
    exact hRL T
  let Q := ∑ a, E a * (E a)ᴴ
  let P := spectralSupport Q
  let W := spectralInverseSqrt Q
  let Y := fun T : Matrix (Fin d) (Fin d) ℂ => D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.leftInverseObservable A T
  let NX := fun T : Matrix (Fin d) (Fin d) ℂ => ∑ a, E a * T * (E a)ᴴ
  let pi := fun T : Matrix (Fin d) (Fin d) ℂ => W * NX T * W
  have hQeq : Q = N 1 := by simpa only [Q, Matrix.mul_one] using (hNE 1).symm
  have hNX (T) : NX T = N T := (hNE T).symm
  obtain ⟨hYE, hEY, hQY, hYQ, hWY, hSandwich, hWN, hPE, hPN⟩ :=
    D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness.kraus_left_inverse_spectral_relations
      E A hATP hleft v
  obtain ⟨hWs, hPs, hPP, hNorm⟩ := spectral_decoder_normalization E
  have hWself : Wᴴ = W := hWs
  have hPself : Pᴴ = P := hPs
  have hcomm (T) : Commute Q (Y T) := (hQY T).trans (hYQ T).symm
  have hpY (T) : P * Y T = Y T * P :=
    ((hcomm T).cfc_real (fun t : ℝ => if t = 0 then 0 else 1)).eq
  have hpi (T) : pi T = P * Y T := hWN T
  have hpiP (T) : pi T * P = pi T := by
    rw [hpi]
    calc
      P * Y T * P = P * (Y T * P) := Matrix.mul_assoc _ _ _
      _ = P * (P * Y T) := by rw [← hpY T]
      _ = P * Y T := by rw [← Matrix.mul_assoc, hPP]
  have hNY (T U) : NX T * Y U = NX (T * U) := by
    simp only [NX, Matrix.sum_mul, Matrix.mul_assoc]
    apply Finset.sum_congr rfl
    intro a ha
    exact congrArg (fun M => E a * (T * M)) (hEY U a)
  have hpiY (T U) : pi (T * U) = pi T * Y U := by
    change W * NX (T * U) * W = (W * NX T * W) * Y U
    rw [← hNY]
    calc
      W * (NX T * Y U) * W = W * NX T * (Y U * W) := by
        simp only [Matrix.mul_assoc]
      _ = W * NX T * (W * Y U) := by rw [← hWY U]
      _ = (W * NX T * W) * Y U := by simp only [Matrix.mul_assoc]
  have hmul (T U) : pi T * pi U = pi (T * U) := by
    rw [hpi U, ← Matrix.mul_assoc, hpiP T, ← hpiY T U]
  have hstar (T) : (pi T)ᴴ = pi Tᴴ := by
    simp only [pi, NX, Matrix.conjTranspose_mul, Matrix.conjTranspose_sum,
      Matrix.conjTranspose_conjTranspose, hWself, Matrix.mul_assoc]
  have hPQ : P * Q = Q := by
    simp only [Q, Matrix.mul_sum, ← Matrix.mul_assoc]
    apply Finset.sum_congr rfl
    intro a ha
    exact congrArg (fun M => M * (E a)ᴴ) (hPE a)
  have hQh : Q.IsHermitian := (show Q.PosSemidef from Matrix.nonneg_iff_posSemidef.mp
    (Finset.sum_nonneg fun a _ => (Matrix.posSemidef_self_mul_conjTranspose (E a)).nonneg)).isHermitian
  have hQP : Q * P = Q := by
    have hh := congrArg Matrix.conjTranspose hPQ
    simpa only [Matrix.conjTranspose_mul, hQh.eq, hPself] using hh
  have hQpi (T) : Q * pi T = NX T := by
    rw [hpi, ← Matrix.mul_assoc, hQP, hQY]
  have hpiQ (T) : pi T * Q = NX T := by
    rw [hpi, Matrix.mul_assoc, hYQ, hPN]
  have hOne : pi 1 = P := by
    simpa only [pi, NX, Matrix.mul_one] using hSandwich
  have hh : pi 1 = P ∧ (∀ T, (pi T)ᴴ = pi Tᴴ) ∧
      (∀ T U, pi T * pi U = pi (T * U)) ∧
      (∀ T, Q * pi T = pi T * Q) ∧ (∀ T, NX T = Q * pi T) :=
    ⟨hOne, hstar, hmul, fun T => (hQpi T).trans (hpiQ T).symm,
      fun T => (hQpi T).symm⟩
  simpa only [pi, P, W, hNX, hQeq] using hh

set_option maxHeartbeats 3000000 in
-- The dimension calculation consumes the accepted actual pointwise tensor map.
theorem actual_cptp_left_inverse_syndrome_rank
    {d n k : ℕ} (hd : 0 < d)
    (N : MatrixMap (Fin d) (Fin n) ℂ)
    (hCP : N.IsCompletelyPositive)
    (hTP : ∀ T, Matrix.trace (N T) = Matrix.trace T)
    (hLeft : ∃ R : MatrixMap (Fin n) (Fin d) ℂ,
      R.IsCompletelyPositive ∧ (∀ T, Matrix.trace (R T) = Matrix.trace T) ∧
      ∀ T, R (N T) = T)
    (hRankP : (spectralSupport (N 1)).rank = k * d) :
    let v : Fin d := ⟨0, hd⟩
    let W := spectralInverseSqrt (N 1)
    (W * N (Matrix.single v v 1) * W).rank = k := by
  classical
  let v : Fin d := ⟨0, hd⟩
  obtain ⟨R, hRC, hRT, hRL⟩ := hLeft
  let E := sqrtColumn N
  let A := sqrtColumn R
  obtain ⟨hNE, hETP⟩ := actual_sqrt_columns_kraus N hCP hTP
  obtain ⟨hRA, hATP⟩ := actual_sqrt_columns_kraus R hRC hRT
  have hleft (T : Matrix (Fin d) (Fin d) ℂ) :
      (∑ b, A b * (∑ a, E a * T * (E a)ᴴ) * (A b)ᴴ) = T := by
    rw [← hNE T, ← hRA]
    exact hRL T
  have hn : Nonempty (Fin n) := by
    by_contra hz
    letI : IsEmpty (Fin n) := not_nonempty_iff.mp hz
    have hh := hTP (1 : Matrix (Fin d) (Fin d) ℂ)
    have hd0 : (d : ℂ) = 0 := by simpa using hh.symm
    exact (Nat.ne_of_gt hd) (Nat.cast_eq_zero.mp hd0)
  letI : Nonempty (Fin n) := hn
  obtain ⟨Theta, back, sigma, sigmaInv, hpoint⟩ :=
    Original8340InheritedCoreAttempt.whole_pointwise_core_attempt E hETP A hATP hleft v v
  have hq : (∑ a, E a * (E a)ᴴ) = N 1 := by
    simpa only [Matrix.mul_one] using (hNE 1).symm
  have hnx (T : Matrix (Fin d) (Fin d) ℂ) :
      (∑ a, E a * T * (E a)ᴴ) = N T := (hNE T).symm
  have ht := Theta.toLinearEquiv.finrank_eq
  simp only [Module.finrank_tensorProduct, finrank_euclideanSpace, Fintype.card_fin,
    hq, hnx] at ht
  have hr (T : Matrix (Fin n) (Fin n) ℂ) :
      T.rank = Module.finrank ℂ (LinearMap.range T.toEuclideanLin) := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    exact Matrix.rank_eq_finrank_range_toLin T _ _
  simp only [← hr] at ht
  rw [hq, hnx] at ht
  have ht' : (spectralInverseSqrt (N 1) * N (Matrix.single v v 1) *
      spectralInverseSqrt (N 1)).rank * d = k * d := by
    simpa only [hRankP] using ht
  exact Nat.eq_of_mul_eq_mul_right hd ht'

set_option maxHeartbeats 3000000 in
-- The actual Choi matrix factors through its distinguished diagonal block.
theorem actual_inputChoi_rank
    {d n k : ℕ} (hd : 0 < d)
    (N : MatrixMap (Fin d) (Fin n) ℂ)
    (hCP : N.IsCompletelyPositive)
    (hTP : ∀ T, Matrix.trace (N T) = Matrix.trace T)
    (hLeft : ∃ R : MatrixMap (Fin n) (Fin d) ℂ,
      R.IsCompletelyPositive ∧ (∀ T, Matrix.trace (R T) = Matrix.trace T) ∧
      ∀ T, R (N T) = T)
    (hRankP : (spectralSupport (N 1)).rank = k * d) :
    (inputChoi N).rank = k := by
  classical
  let v : Fin d := ⟨0, hd⟩
  let Q := N 1
  let W := spectralInverseSqrt Q
  let pi := fun T => W * N T * W
  let F := fun i j : Fin d => pi (Matrix.single i j 1)
  obtain ⟨hOne, hstar, hmul, hcomm, hfactor⟩ :=
    actual_cptp_left_inverse_spectral_algebra hd N hCP hTP hLeft
  have hFmul (i j a b : Fin d) :
      F i j * F a b = if j = a then F i b else 0 := by
    have hh := hmul (Matrix.single i j 1) (Matrix.single a b 1)
    by_cases hj : j = a
    · subst a
      simpa only [F, pi, Matrix.single_mul_single_same, one_mul, ite_true] using hh
    · have hz : Matrix.single i j (1 : ℂ) * Matrix.single a b (1 : ℂ) = 0 :=
        Matrix.single_mul_single_of_ne (c := (1 : ℂ)) (i := i) (j := j)
          (k := a) (h := hj) (d := (1 : ℂ))
      simpa only [F, pi, hz, map_zero, Matrix.mul_zero,
        Matrix.zero_mul, if_neg hj] using hh
  have hQF (i j : Fin d) : Q * F i j = F i j * Q :=
    hcomm (Matrix.single i j 1)
  have hNF (i j : Fin d) : N (Matrix.single i j 1) = Q * F i j :=
    hfactor (Matrix.single i j 1)
  have hblock (i j : Fin d) :
      F i v * N (Matrix.single v v 1) * F v j = N (Matrix.single i j 1) := by
    calc
      _ = (F i v * (Q * F v v)) * F v j := by rw [hNF v v]
      _ = ((F i v * Q) * F v v) * F v j :=
        congrArg (fun M => M * F v j) (Matrix.mul_assoc (F i v) Q (F v v)).symm
      _ = ((Q * F i v) * F v v) * F v j := by rw [← hQF i v]
      _ = Q * ((F i v * F v v) * F v j) := by
        simp only [Matrix.mul_assoc]
      _ = Q * F i j := by simp only [hFmul, ite_true]
      _ = N (Matrix.single i j 1) := (hNF i j).symm
  let L : Matrix (Fin d × Fin n) (Fin n) ℂ := fun p b => F p.1 v p.2 b
  let R : Matrix (Fin n) (Fin d × Fin n) ℂ := fun a p => F v p.1 a p.2
  have hJ : inputChoi N = L * N (Matrix.single v v 1) * R := by
    ext ⟨i,a⟩ ⟨j,b⟩
    exact (congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M a b) (hblock i j)).symm
  have hNrank : (N (Matrix.single v v 1)).rank = k := by
    have hF := actual_cptp_left_inverse_syndrome_rank hd N hCP hTP hLeft hRankP
    change (F v v).rank = k at hF
    apply le_antisymm
    · rw [hNF v v]
      exact (Matrix.rank_mul_le_right Q (F v v)).trans_eq hF
    · rw [← hF]
      exact (Matrix.rank_mul_le_left (W * N (Matrix.single v v 1)) W).trans
        (Matrix.rank_mul_le_right W (N (Matrix.single v v 1)))
  apply le_antisymm
  · rw [hJ]
    exact ((Matrix.rank_mul_le_left (L * N (Matrix.single v v 1)) R).trans
      (Matrix.rank_mul_le_right L (N (Matrix.single v v 1)))).trans_eq hNrank
  · rw [← hNrank]
    exact Matrix.rank_submatrix_le (inputChoi N) (fun a => (v,a)) (fun b => (v,b))


end Original8340Global
