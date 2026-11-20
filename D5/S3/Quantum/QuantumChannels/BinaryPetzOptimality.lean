/- GID: D5/S3/Quantum/QuantumChannels/BinaryPetzOptimality
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/BinaryPetzOptimality
   mirror-E: none(waiver:finite-spectral-proof)
   anchors: [lake/module/D5.S3.Quantum.Foundation.FiniteTraceDistance, lake/module/D5.S3.Quantum.Lieb.SupportPerspectiveTransport, lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.Records.PrimitiveFiniteCrossCommutator]
   utility: none
   digest: Exact binary Petz and Helstrom equality for finite records. -/
import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Quantum.Lieb.SupportPerspectiveTransport
import D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity
import D5.S3.Quantum.QuantumChannels.PositiveFilterTransposeRefutation
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Records.PrimitiveFiniteCrossCommutator
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
The equality argument follows the singular-Gram proof in
`../binary-complementary-decoder/proof.txt`. The finite-ring instance uses the
literal normalized flattenings and the existing finite cross commutator.
-/

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder

namespace BinaryPetzOptimality

open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity (zero_trace_mul_eq_zero)

variable {ι κ ε : Type*}
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype ε] [DecidableEq ε]

private theorem trace_pair_eq_zero {X Y : Matrix ι ι ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (ht : (X * Y).trace.re = 0) :
    X * Y = 0 := by
  have hz : (X * Y).trace = 0 :=
    Complex.ext (by simpa using ht)
      (by simpa using (Complex.nonneg_iff.mp (hX.trace_mul_nonneg hY)).2.symm)
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have ht' : (X.submatrix e e * Y.submatrix e e).trace = 0 := by
    rw [Matrix.submatrix_mul_equiv X Y e e e]
    exact (e.sum_comp (fun i => (X * Y) i i)).trans hz
  have h := zero_trace_mul_eq_zero (X.submatrix e e) (Y.submatrix e e)
    (hX.submatrix _) (hY.submatrix _) ht'
  rw [Matrix.submatrix_mul_equiv X Y e e e] at h
  apply Matrix.ext
  intro i j
  simpa [Matrix.submatrix_apply] using
    congrArg (fun M : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ =>
      M (e.symm i) (e.symm j)) h

private theorem one_add_posSemidef {J : Matrix ι ι ℂ}
    (hJ : Jᴴ = J) (hJJ : J * J = 1) : (1 + J).PosSemidef := by
  have hsq : (1 + J)ᴴ * (1 + J) = (1 + J) + (1 + J) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, hJ]
    noncomm_ring [hJJ]
  have hh : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have h := (Matrix.posSemidef_conjTranspose_mul_self (1 + J)).smul hh
  rwa [hsq, smul_add, ← add_smul, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, one_smul] at h

private theorem commute_of_traceNorm_eq {J H : Matrix ι ι ℂ}
    (hJ : Jᴴ = J) (hJJ : J * J = 1) (hH : H.IsHermitian)
    (heq : (J * H).trace.re = traceNorm H) : Commute J H := by
  let P := posPart H
  let N := negPart H
  have hP : P.PosSemidef := (CFC.posPart_nonneg H).posSemidef
  have hN : N.PosSemidef := (CFC.negPart_nonneg H).posSemidef
  have hPN : P - N = H := CFC.posPart_sub_negPart H hH.isSelfAdjoint
  have hmass : traceNorm H = P.trace.re + N.trace.re := trace_norm_jordan_mass H hH
  have hplus : (1 + J).PosSemidef := one_add_posSemidef hJ hJJ
  have hminus : (1 - J).PosSemidef := by
    rw [sub_eq_add_neg]
    exact one_add_posSemidef (J := -J) (by rw [Matrix.conjTranspose_neg, hJ])
      (by rw [neg_mul_neg, hJJ])
  have hp : 0 ≤ ((1 - J) * P).trace.re := (Complex.nonneg_iff.mp (hminus.trace_mul_nonneg hP)).1
  have hn : 0 ≤ ((1 + J) * N).trace.re := (Complex.nonneg_iff.mp (hplus.trace_mul_nonneg hN)).1
  have hsum : ((1 - J) * P).trace.re + ((1 + J) * N).trace.re = 0 := by
    have hread : (J * (P - N)).trace.re = P.trace.re + N.trace.re := by
      rw [hPN, heq, hmass]
    rw [mul_sub, Matrix.trace_sub, Complex.sub_re] at hread
    simp only [sub_mul, add_mul, one_mul, Matrix.trace_sub, Matrix.trace_add,
      Complex.sub_re, Complex.add_re]
    linarith
  have hJP : J * P = P := by
    have h := trace_pair_eq_zero hminus hP (show ((1 - J) * P).trace.re = 0 by linarith)
    exact (sub_eq_zero.mp (by simpa only [sub_mul, one_mul] using h)).symm
  have hJN : J * N = -N := by
    have h := trace_pair_eq_zero hplus hN (show ((1 + J) * N).trace.re = 0 by linarith)
    exact eq_neg_of_add_eq_zero_right (by simpa only [add_mul, one_mul] using h)
  have hPH : P * J = P := by
    simpa only [Matrix.conjTranspose_mul, hP.isHermitian.eq, hJ] using
      congrArg Matrix.conjTranspose hJP
  have hNH : N * J = -N := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_neg, hN.isHermitian.eq, hJ] using
      congrArg Matrix.conjTranspose hJN
  change J * H = H * J
  rw [← hPN, mul_sub, sub_mul, hJP, hJN, hPH, hNH]

private theorem traceNorm_involution_mul (J H : Matrix ι ι ℂ)
    (hJ : Jᴴ = J) (hJJ : J * J = 1) : traceNorm (J * H) = traceNorm H := by
  have h : (J * H)ᴴ * (J * H) = Hᴴ * H := by
    rw [Matrix.conjTranspose_mul, hJ]
    calc
      (Hᴴ * J) * (J * H) = Hᴴ * ((J * J) * H) := by simp only [mul_assoc]
      _ = Hᴴ * H := by rw [hJJ, one_mul]
  simp only [traceNorm, h]

/-- The trace-norm pairing with a selfadjoint involution saturates precisely
when the Gram commutes with its conjugate by the involution. -/
theorem trace_pair_eq_traceNorm_iff {G J : Matrix ι ι ℂ}
    (hG : G.PosSemidef) (hJ : J.IsHermitian) (hJJ : J * J = 1) :
    let F := CFC.sqrt G
    (J * F * J * F).trace = (traceNorm (F * J * F) : ℂ) ↔ Commute (J * G * J) G := by
  let F := CFC.sqrt G
  let H := F * J * F
  let K := J * F * J
  change (J * F * J * F).trace = (traceNorm H : ℂ) ↔ Commute (J * G * J) G
  have hF : F.PosSemidef := (CFC.sqrt_nonneg G).posSemidef
  have hFF : F * F = G := CFC.sqrt_mul_sqrt_self G hG.nonneg
  have hH : H.IsHermitian := by
    change (F * J * F)ᴴ = F * J * F
    simp only [Matrix.conjTranspose_mul, hF.isHermitian.eq, hJ.eq, mul_assoc]
  have hK : K.PosSemidef := by
    simpa only [K, hJ.eq] using hF.conjTranspose_mul_mul_same J
  have hKK : K * K = J * G * J := by
    calc
      K * K = J * (F * (J * J) * F) * J := by simp only [K, mul_assoc]
      _ = J * G * J := by rw [hJJ, mul_one, hFF]
  have hJH : J * H = K * F := by simp only [H, K, mul_assoc]
  constructor
  · intro heq
    have hJh : (J * H).trace.re = traceNorm H := by
      have h := congrArg Complex.re heq
      simpa only [H, mul_assoc, Complex.ofReal_re] using h
    have hcomm := commute_of_traceNorm_eq hJ.eq hJJ hH hJh
    have hKF : Commute K F := by
      change K * F = F * K
      rw [← hJH, hcomm.eq]
      simp only [H, K, mul_assoc]
    rw [← hKK, ← hFF]
    exact (hKF.mul_left hKF).mul_right (hKF.mul_left hKF)
  · intro hcomm
    have hKsqrt : CFC.sqrt (J * G * J) = K := CFC.sqrt_unique hKK hK.nonneg
    have hKF : Commute K F := by
      have hleft : Commute (CFC.sqrt (J * G * J)) G := hcomm.cfcₙ_nnreal NNReal.sqrt
      have hboth : Commute (CFC.sqrt G) (CFC.sqrt (J * G * J)) :=
        hleft.symm.cfcₙ_nnreal NNReal.sqrt
      rw [hKsqrt] at hboth
      exact hboth.symm
    have hpos : (J * H).PosSemidef := by
      rw [hJH]
      exact (hKF.mul_nonneg hK.nonneg hF.nonneg).posSemidef
    calc
      (J * F * J * F).trace = (J * H).trace := by simp only [H, mul_assoc]
      _ = (traceNorm (J * H) : ℂ) := (traceNorm_of_posSemidef hpos).symm
      _ = (traceNorm H : ℂ) := by rw [traceNorm_involution_mul J H hJ.eq hJJ]

/-- The sign of the two coordinate projections. -/
def blockSign (ι κ : Type*) [DecidableEq ι] [DecidableEq κ] : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ :=
  fromBlocks 1 0 0 (-1)

private theorem blockSign_hermitian : (blockSign ι κ).IsHermitian := by
  change (blockSign ι κ)ᴴ = blockSign ι κ
  simp [blockSign, Matrix.fromBlocks_conjTranspose]

private theorem blockSign_sq : blockSign ι κ * blockSign ι κ = 1 := by
  simp [blockSign, Matrix.fromBlocks_multiply]

private theorem signed_blocks (A : Matrix ι ι ℂ) (B : Matrix ι κ ℂ) (C : Matrix κ κ ℂ) :
    blockSign ι κ * fromBlocks A B Bᴴ C * blockSign ι κ = fromBlocks A (-B) (-Bᴴ) C := by
  simp [blockSign, Matrix.fromBlocks_multiply]

/-- In a Hermitian two-block Gram the upper-right block controls the whole
commutator. The opposite block follows by taking adjoints. -/
theorem signed_gram_commute_iff (A : Matrix ι ι ℂ) (B : Matrix ι κ ℂ) (C : Matrix κ κ ℂ)
    (hA : A.IsHermitian) (hC : C.IsHermitian) :
    let G := fromBlocks A B Bᴴ C
    Commute (blockSign ι κ * G * blockSign ι κ) G ↔ A * B = B * C := by
  dsimp only
  rw [signed_blocks]
  change fromBlocks A (-B) (-Bᴴ) C * fromBlocks A B Bᴴ C =
    fromBlocks A B Bᴴ C * fromBlocks A (-B) (-Bᴴ) C ↔ _
  simp only [Matrix.fromBlocks_multiply, Matrix.neg_mul, Matrix.mul_neg]
  constructor
  · intro h
    apply Matrix.ext
    intro i j
    have hh := congrArg (fun M : Matrix ι κ ℂ => M i j) (Matrix.fromBlocks_inj.mp h).2.1
    simp only [Matrix.add_apply, Matrix.neg_apply] at hh
    linear_combination hh / 2
  · intro h
    have ht : Bᴴ * A = C * Bᴴ := by
      simpa only [Matrix.conjTranspose_mul, hA.eq, hC.eq] using
        congrArg Matrix.conjTranspose h
    apply Matrix.fromBlocks_inj.mpr
    exact ⟨rfl, by rw [h]; exact add_comm _ _, by rw [ht]; exact add_comm _ _, rfl⟩

/-- For the signed two-block Gram the norm equality is precisely the
intertwining equation of the cross block. -/
theorem block_trace_pair_eq_traceNorm_iff
    (A : Matrix ι ι ℂ) (B : Matrix ι κ ℂ) (C : Matrix κ κ ℂ)
    (hG : (fromBlocks A B Bᴴ C).PosSemidef) :
    let J := blockSign ι κ
    let F := CFC.sqrt (fromBlocks A B Bᴴ C)
    (J * F * J * F).trace = (traceNorm (F * J * F) : ℂ) ↔ A * B = B * C := by
  have hA : A.IsHermitian := by
    change Aᴴ = A
    simpa only [Matrix.fromBlocks_conjTranspose, Matrix.toBlocks_fromBlocks₁₁] using
      congrArg Matrix.toBlocks₁₁ hG.isHermitian.eq
  have hC : C.IsHermitian := by
    change Cᴴ = C
    simpa only [Matrix.fromBlocks_conjTranspose, Matrix.toBlocks_fromBlocks₂₂] using
      congrArg Matrix.toBlocks₂₂ hG.isHermitian.eq
  exact (trace_pair_eq_traceNorm_iff hG blockSign_hermitian blockSign_sq).trans
    (signed_gram_commute_iff A B C hA hC)

/-- Concatenate the adjoints of the visible-by-hidden amplitude matrices after
absorbing the square roots of the priors into those matrices. -/
def amplitudeColumns (X : Matrix ι ε ℂ) (Z : Matrix κ ε ℂ) : Matrix ε (ι ⊕ κ) ℂ :=
  fromCols Xᴴ Zᴴ

theorem amplitude_gram_blocks (X : Matrix ι ε ℂ) (Z : Matrix κ ε ℂ) :
    (amplitudeColumns X Z)ᴴ * amplitudeColumns X Z =
      fromBlocks (X * Xᴴ) (X * Zᴴ) (X * Zᴴ)ᴴ (Z * Zᴴ) := by
  simp [amplitudeColumns, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromRows_mul_fromCols, Matrix.conjTranspose_mul]

/-- Applies to arbitrary priors through the weighted amplitude matrices.
No invertibility is needed for the amplitude or Gram matrices. -/
theorem amplitude_trace_pair_eq_traceNorm_iff (X : Matrix ι ε ℂ) (Z : Matrix κ ε ℂ) :
    let J := blockSign ι κ
    let Y := amplitudeColumns X Z
    let F := CFC.sqrt (Yᴴ * Y)
    (J * F * J * F).trace = (traceNorm (F * J * F) : ℂ) ↔
      (X * Xᴴ) * (X * Zᴴ) = (X * Zᴴ) * (Z * Zᴴ) := by
  dsimp only
  rw [amplitude_gram_blocks]
  apply block_trace_pair_eq_traceNorm_iff
  rw [← amplitude_gram_blocks]
  exact Matrix.posSemidef_conjTranspose_mul_self _

open D5.S3.Quantum.Recovery.SpectralTransposeRecovery (spectralInverseSqrt spectralSupport)
open D5.S3.Quantum.Lieb.SupportPerspectiveTransport
  (spectral_sqrt_normalization support_of_nonneg_le_smul)
open D5.S3.Quantum.Lieb.PositiveMapJensen (cfc_intertwining)

private theorem spectral_support_mul_amplitude (Y : Matrix ε ι ℂ)
    (h : spectralSupport (Y * Yᴴ) * (Y * Yᴴ) = Y * Yᴴ) :
    spectralSupport (Y * Yᴴ) * Y = Y := by
  let P := spectralSupport (Y * Yᴴ)
  have hz : (1 - P) * (Y * Yᴴ) = 0 := by rw [sub_mul, one_mul, h, sub_self]
  have hy := (Matrix.mul_self_mul_conjTranspose_eq_zero Y (1 - P)).mp hz
  rw [Matrix.sub_mul, Matrix.one_mul] at hy
  exact (sub_eq_zero.mp hy).symm

/-- The rectangular Moore–Penrose sandwich is the positive Gram square root. -/
theorem support_sandwich_eq_gram_sqrt (Y : Matrix ε ι ℂ) :
    let W := spectralInverseSqrt (Y * Yᴴ)
    Yᴴ * W * Y = CFC.sqrt (Yᴴ * Y) := by
  let Q := Y * Yᴴ
  let W := spectralInverseSqrt Q
  let P := spectralSupport Q
  change Yᴴ * W * Y = CFC.sqrt (Yᴴ * Y)
  obtain ⟨_, _, _, _, _, _, hPQ, hWQW⟩ :=
    spectral_sqrt_normalization Q (Matrix.posSemidef_self_mul_conjTranspose Y)
  have hPY : P * Y = Y := spectral_support_mul_amplitude Y hPQ
  have hW : W.PosSemidef := by
    apply Matrix.nonneg_iff_posSemidef.mp
    change 0 ≤ cfc (fun x : ℝ => (Real.sqrt x)⁻¹) Q
    exact cfc_nonneg (fun x _ => inv_nonneg.mpr (Real.sqrt_nonneg x))
  have hsq : (Yᴴ * W * Y) * (Yᴴ * W * Y) = Yᴴ * Y := by
    calc
      _ = Yᴴ * ((W * Q * W) * Y) := by simp only [Q, Matrix.mul_assoc]
      _ = _ := by rw [hWQW, hPY]
  exact (CFC.sqrt_unique hsq (hW.conjTranspose_mul_mul_same Y).nonneg).symm

/-- The signed support inverse-root readout has the trace pairing of the
actual Gram. For the binary block sign the signed effect is the difference
of the two support Petz effects. -/
theorem support_petz_contrast_eq_gram_pairing (Y : Matrix ε ι ℂ) (J : Matrix ι ι ℂ) :
    let W := spectralInverseSqrt (Y * Yᴴ)
    let D := Y * J * Yᴴ
    let F := CFC.sqrt (Yᴴ * Y)
    (W * D * W * D).trace = (J * F * J * F).trace := by
  let W := spectralInverseSqrt (Y * Yᴴ)
  let D := Y * J * Yᴴ
  let F := CFC.sqrt (Yᴴ * Y)
  change (W * D * W * D).trace = (J * F * J * F).trace
  have hF : Yᴴ * W * Y = F := support_sandwich_eq_gram_sqrt Y
  calc
    _ = (W * Y * (J * F * J) * Yᴴ).trace := by
      rw [← hF]
      simp only [D, Matrix.mul_assoc]
    _ = (F * (J * F * J)).trace := by
      rw [Matrix.trace_mul_comm _ Yᴴ, ← hF]
      simp only [Matrix.mul_assoc]
    _ = _ := Matrix.trace_mul_comm _ _

private theorem support_sandwich_traceNorm (U : Matrix ε ι ℂ) (H : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (hUH : (Uᴴ * U) * H = H) :
    traceNorm (U * H * Uᴴ) = traceNorm H := by
  let T := Uᴴ * U
  let R := CFC.sqrt (Hᴴ * H)
  have hR : R.PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have hRR : R * R = Hᴴ * H :=
    CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_conjTranspose_mul_self H).nonneg
  have hTR : T * R = R := by
    have hz : (1 - T) * (R * Rᴴ) = 0 := by
      rw [hR.isHermitian.eq, hRR, hH.eq, ← Matrix.mul_assoc]
      simp only [Matrix.sub_mul, Matrix.one_mul, T, hUH, sub_self, Matrix.zero_mul]
    have h := (Matrix.mul_self_mul_conjTranspose_eq_zero R (1 - T)).mp hz
    rw [Matrix.sub_mul, Matrix.one_mul] at h
    exact (sub_eq_zero.mp h).symm
  have hmul (A : Matrix ι ι ℂ) (hA : T * A = A) :
      (U * A * Uᴴ) * (U * A * Uᴴ) = U * (A * A) * Uᴴ := by
    calc
      _ = U * A * (T * A) * Uᴴ := by simp only [T, Matrix.mul_assoc]
      _ = _ := by rw [hA, Matrix.mul_assoc U A A]
  have hsq : (U * R * Uᴴ) * (U * R * Uᴴ) = (U * H * Uᴴ)ᴴ * (U * H * Uᴴ) := by
    rw [hmul R hTR, hRR, hH.eq]
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hH.eq, Matrix.mul_assoc] using (hmul H hUH).symm
  have hroot := CFC.sqrt_unique hsq (hR.mul_mul_conjTranspose_same U).nonneg
  unfold traceNorm
  rw [hroot, Matrix.trace_mul_cycle, hTR]

/-- The weighted hidden difference and its signed Gram have equal trace norms. -/
theorem hidden_traceNorm_eq_gram_traceNorm (Y : Matrix ε ι ℂ) (J : Matrix ι ι ℂ)
    (hJ : J.IsHermitian) :
    let F := CFC.sqrt (Yᴴ * Y)
    traceNorm (Y * J * Yᴴ) = traceNorm (F * J * F) := by
  let F := CFC.sqrt (Yᴴ * Y)
  let W := spectralInverseSqrt (Y * Yᴴ)
  let P := spectralSupport (Y * Yᴴ)
  let U := W * Y
  change traceNorm (Y * J * Yᴴ) = traceNorm (F * J * F)
  obtain ⟨_, hW, _, _, _, _, hPQ, hWQW⟩ :=
    spectral_sqrt_normalization (Y * Yᴴ) (Matrix.posSemidef_self_mul_conjTranspose Y)
  have hPY : P * Y = Y := spectral_support_mul_amplitude Y hPQ
  have hF : Yᴴ * W * Y = F := support_sandwich_eq_gram_sqrt Y
  have hFh : Fᴴ = F := (CFC.sqrt_nonneg (Yᴴ * Y)).posSemidef.isHermitian.eq
  have hUF : U * F = Y := by
    rw [← hF]
    calc
      _ = (W * (Y * Yᴴ) * W) * Y := by simp only [U, Matrix.mul_assoc]
      _ = _ := by rw [hWQW, hPY]
  change Wᴴ = W at hW
  have hUY : Uᴴ * Y = F := by
    simpa only [U, Matrix.conjTranspose_mul, hW] using hF
  have hTF : (Uᴴ * U) * F = F := by rw [Matrix.mul_assoc, hUF, hUY]
  have hTFH : (Uᴴ * U) * (F * J * F) = F * J * F := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hTF]
  have hH : (F * J * F).IsHermitian := by
    change (F * J * F)ᴴ = F * J * F
    simp only [Matrix.conjTranspose_mul, hFh, hJ.eq, Matrix.mul_assoc]
  have hFU : F * Uᴴ = Yᴴ := by
    simpa only [Matrix.conjTranspose_mul, hFh] using congrArg Matrix.conjTranspose hUF
  have hD : U * (F * J * F) * Uᴴ = Y * J * Yᴴ := by
    rw [← Matrix.mul_assoc U (F * J) F, ← Matrix.mul_assoc U F J, hUF,
      Matrix.mul_assoc (Y * J) F Uᴴ, hFU]
  rw [← hD]
  exact support_sandwich_traceNorm U _ hH hTFH

/-- For an actual weighted amplitude matrix and a selfadjoint sign, the Petz
contrast saturates the trace norm of the weighted hidden difference exactly
when the positive Gram commutes with its signed conjugate. -/
theorem support_petz_contrast_eq_traceNorm_iff (Y : Matrix ε ι ℂ) (J : Matrix ι ι ℂ)
    (hJ : J.IsHermitian) (hJJ : J * J = 1) :
    let W := spectralInverseSqrt (Y * Yᴴ)
    let D := Y * J * Yᴴ
    (W * D * W * D).trace = (traceNorm D : ℂ) ↔ Commute (J * (Yᴴ * Y) * J) (Yᴴ * Y) := by
  dsimp only
  rw [support_petz_contrast_eq_gram_pairing, hidden_traceNorm_eq_gram_traceNorm Y J hJ]
  exact trace_pair_eq_traceNorm_iff (Matrix.posSemidef_conjTranspose_mul_self Y) hJ hJJ

private theorem amplitude_hidden_sum (X : Matrix ι ε ℂ) (Z : Matrix κ ε ℂ) :
    amplitudeColumns X Z * (amplitudeColumns X Z)ᴴ = Xᴴ * X + Zᴴ * Z := by
  simp [amplitudeColumns, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromCols_mul_fromRows]

private theorem amplitude_hidden_difference (X : Matrix ι ε ℂ) (Z : Matrix κ ε ℂ) :
    amplitudeColumns X Z * blockSign ι κ * (amplitudeColumns X Z)ᴴ = Xᴴ * X - Zᴴ * Z := by
  simp [amplitudeColumns, blockSign, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows, sub_eq_add_neg]

/-- The two actual support Petz effects have optimal signed trace contrast
precisely when the two visible diagonal Gram blocks intertwine the cross block. -/
theorem binary_support_petz_contrast_eq_traceNorm_iff (X : Matrix ι ε ℂ) (Z : Matrix κ ε ℂ) :
    let σ₀ := Xᴴ * X
    let σ₁ := Zᴴ * Z
    let W := spectralInverseSqrt (σ₀ + σ₁)
    let E₀ := W * σ₀ * W
    let E₁ := W * σ₁ * W
    ((E₀ - E₁) * (σ₀ - σ₁)).trace = (traceNorm (σ₀ - σ₁) : ℂ) ↔
      (X * Xᴴ) * (X * Zᴴ) = (X * Zᴴ) * (Z * Zᴴ) := by
  let W := spectralInverseSqrt (Xᴴ * X + Zᴴ * Z)
  have heffects : W * (Xᴴ * X) * W - W * (Zᴴ * Z) * W = W * (Xᴴ * X - Zᴴ * Z) * W := by
    rw [mul_sub, sub_mul]
  change ((W * (Xᴴ * X) * W - W * (Zᴴ * Z) * W) * (Xᴴ * X - Zᴴ * Z)).trace =
    (traceNorm (Xᴴ * X - Zᴴ * Z) : ℂ) ↔ _
  rw [heffects]
  have h := support_petz_contrast_eq_traceNorm_iff (amplitudeColumns X Z) (blockSign ι κ)
    blockSign_hermitian blockSign_sq
  dsimp only at h
  rw [amplitude_hidden_sum, amplitude_hidden_difference, amplitude_gram_blocks] at h
  refine h.trans (signed_gram_commute_iff _ _ _ ?_ ?_)
  · exact (Matrix.posSemidef_self_mul_conjTranspose X).isHermitian
  · exact (Matrix.posSemidef_self_mul_conjTranspose Z).isHermitian

/-- Possible signed contrasts for a binary test with first effect `E` and
second effect `1 - E`. Maximizing this contrast minimizes the Bayes error. -/
def binaryContrasts (D : Matrix ε ε ℂ) : Set ℝ :=
  {x | ∃ E : Matrix ε ε ℂ, E.PosSemidef ∧ (1 - E).PosSemidef ∧
    ((E - (1 - E)) * D).trace.re = x}

/-- The Helstrom bound is attained by the support of the positive Jordan part. -/
theorem helstrom_contrast (D : Matrix ε ε ℂ) (hD : D.IsHermitian) :
    IsGreatest (binaryContrasts D) (traceNorm D) := by
  let P := posPart D
  let N := negPart D
  have hP : P.PosSemidef := (CFC.posPart_nonneg D).posSemidef
  have hN : N.PosSemidef := (CFC.negPart_nonneg D).posSemidef
  have hsub : P - N = D := CFC.posPart_sub_negPart D hD.isSelfAdjoint
  have hmass : traceNorm D = P.trace.re + N.trace.re := trace_norm_jordan_mass D hD
  have hread (E : Matrix ε ε ℂ) : ((E - (1 - E)) * D).trace.re = traceNorm D -
      2 * (((1 - E) * P).trace.re + (E * N).trace.re) := by
    rw [hmass, ← hsub]
    simp only [sub_mul, mul_sub, one_mul, Matrix.trace_sub, Complex.sub_re]
    ring
  let E := spectralSupport P
  obtain ⟨_, _, hEh, hEE, _, _, hEP, _⟩ := spectral_sqrt_normalization P hP
  have hproj : IsStarProjection E := ⟨hEE, hEh⟩
  have hEN : E * N = 0 := by
    have hPN : P * N = 0 := CFC.posPart_mul_negPart D
    have hint := cfc_intertwining P (0 : Matrix ε ε ℂ) hP.isHermitian Matrix.isHermitian_zero N
      (by rw [Matrix.mul_zero, hPN]) (fun x => if x = 0 then 0 else 1)
    have hzero : cfc (fun x : ℝ => if x = 0 then 0 else 1) (0 : Matrix ε ε ℂ) = 0 := by
      rw [cfc_apply_zero]
      simp
    simpa only [E, spectralSupport, hzero, Matrix.mul_zero] using hint
  refine ⟨⟨E, hproj.nonneg.posSemidef, hproj.one_sub_nonneg.posSemidef, ?_⟩, ?_⟩
  · rw [hread, sub_mul, one_mul, hEP, sub_self, hEN]
    simp
  · rintro _ ⟨M, hM, hMc, rfl⟩
    have hp := (Complex.nonneg_iff.mp (hMc.trace_mul_nonneg hP)).1
    have hn := (Complex.nonneg_iff.mp (hM.trace_mul_nonneg hN)).1
    rw [hread]
    linarith

private theorem completed_petz_effect {σ₀ σ₁ : Matrix ε ε ℂ}
    (h₀ : σ₀.PosSemidef) (h₁ : σ₁.PosSemidef) :
    let W := spectralInverseSqrt (σ₀ + σ₁)
    let E₀ := W * σ₀ * W
    let E₁ := W * σ₁ * W
    E₀.PosSemidef ∧ (1 - E₀).PosSemidef ∧ E₁.PosSemidef ∧
      ((E₀ - (1 - E₀)) * (σ₀ - σ₁)).trace = ((E₀ - E₁) * (σ₀ - σ₁)).trace := by
  let Q := σ₀ + σ₁
  let W := spectralInverseSqrt Q
  let P := spectralSupport Q
  let E₀ := W * σ₀ * W
  let E₁ := W * σ₁ * W
  change E₀.PosSemidef ∧ (1 - E₀).PosSemidef ∧ E₁.PosSemidef ∧ _
  obtain ⟨_, hW, hP, hPP, _, _, hPQ, hWQW⟩ := spectral_sqrt_normalization Q (h₀.add h₁)
  have hproj : IsStarProjection P := ⟨hPP, hP⟩
  change Wᴴ = W at hW
  have hE₀ : E₀.PosSemidef := by simpa only [E₀, hW] using h₀.conjTranspose_mul_mul_same W
  have hE₁ : E₁.PosSemidef := by simpa only [E₁, hW] using h₁.conjTranspose_mul_mul_same W
  have hsum : E₀ + E₁ = P := by
    simpa only [Q, mul_add, add_mul, E₀, E₁] using hWQW
  have hcomplement : 1 - E₀ = E₁ + (1 - P) := by rw [← hsum]; abel
  have hP0 : P * σ₀ = σ₀ := (support_of_nonneg_le_smul Q σ₀ P hP hPQ h₀ 1
    (by simpa only [one_smul] using (le_add_of_nonneg_right h₁.nonneg : σ₀ ≤ Q))).1
  have hP1 : P * σ₁ = σ₁ := (support_of_nonneg_le_smul Q σ₁ P hP hPQ h₁ 1
    (by simpa only [one_smul] using (le_add_of_nonneg_left h₀.nonneg : σ₁ ≤ Q))).1
  have hz : (1 - P) * (σ₀ - σ₁) = 0 := by
    rw [sub_mul, one_mul, mul_sub P, hP0, hP1, sub_self]
  refine ⟨hE₀, hcomplement.symm ▸ hE₁.add hproj.one_sub_nonneg.posSemidef, hE₁, ?_⟩
  rw [hcomplement, sub_add_eq_sub_sub, sub_mul, hz, sub_zero]

private theorem trace_hermitian_product_im_zero {U V : Matrix ε ε ℂ}
    (hU : U.IsHermitian) (hV : V.IsHermitian) : (U * V).trace.im = 0 := by
  have h : star (U * V).trace = (U * V).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hU.eq, hV.eq, Matrix.trace_mul_comm]
  have him := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at him
  linarith

/-- The completed Petz measurement attains the Helstrom contrast exactly when
the weighted visible blocks satisfy `A * B = B * C`. -/
theorem binary_petz_is_optimal_iff (X : Matrix ι ε ℂ) (Z : Matrix κ ε ℂ) :
    let σ₀ := Xᴴ * X
    let σ₁ := Zᴴ * Z
    let W := spectralInverseSqrt (σ₀ + σ₁)
    let E := W * σ₀ * W
    let D := σ₀ - σ₁
    IsGreatest (binaryContrasts D) (((E - (1 - E)) * D).trace.re) ↔
      (X * Xᴴ) * (X * Zᴴ) = (X * Zᴴ) * (Z * Zᴴ) := by
  let σ₀ := Xᴴ * X
  let σ₁ := Zᴴ * Z
  let W := spectralInverseSqrt (σ₀ + σ₁)
  let E := W * σ₀ * W
  let E₁ := W * σ₁ * W
  let D := σ₀ - σ₁
  change IsGreatest (binaryContrasts D) (((E - (1 - E)) * D).trace.re) ↔ _
  have h₀ : σ₀.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self X
  have h₁ : σ₁.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self Z
  have hD : D.IsHermitian := h₀.isHermitian.sub h₁.isHermitian
  obtain ⟨hE, _, hE₁, hread⟩ := completed_petz_effect h₀ h₁
  change ((E - (1 - E)) * D).trace = ((E - E₁) * D).trace at hread
  have hmax := helstrom_contrast D hD
  have hopt : IsGreatest (binaryContrasts D) (((E - (1 - E)) * D).trace.re) ↔
      ((E - E₁) * D).trace = (traceNorm D : ℂ) := by
    rw [hread]
    constructor
    · intro h
      have hre := le_antisymm (hmax.2 h.1) (h.2 hmax.1)
      exact Complex.ext (by simpa only [Complex.ofReal_re] using hre)
        (by simpa only [Complex.ofReal_im] using
          trace_hermitian_product_im_zero (hE.isHermitian.sub hE₁.isHermitian) hD)
    · intro h
      rw [h, Complex.ofReal_re]
      exact hmax
  exact hopt.trans (binary_support_petz_contrast_eq_traceNorm_iff X Z)

open D5.S3.Quantum.TensorNetworks.ComplementaryRecordRate (collisionFlattening
  collisionFlattening_common_visible environmentGram IsEffect isEffect_transpose_iff
  physicalError physicalError_transpose fairError)
open D5.S3.Quantum.TensorNetworks.PeriodicMPSPrimitiveCollision (collisionMarginal)
open D5.S3.Quantum.TensorNetworks.PrimitiveFiniteCrossCommutator
  (collision_flattening_cross_commute_iff)
open D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection (Word)
open D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreMarginalWitness (Pair)

private theorem weighted_ring_block_criterion (m : ℕ) (hm : 5 ≤ m) :
    let w : ℂ := (Real.sqrt (1 / 2 : ℝ) : ℂ)
    let X := w • collisionFlattening false m
    let Z := w • collisionFlattening true m
    (X * Xᴴ) * (X * Zᴴ) = (X * Zᴴ) * (Z * Zᴴ) ↔ (m + 2) % 4 = 0 := by
  let w : ℂ := (Real.sqrt (1 / 2 : ℝ) : ℂ)
  change ((w • collisionFlattening false m) * (w • collisionFlattening false m)ᴴ) *
    ((w • collisionFlattening false m) * (w • collisionFlattening true m)ᴴ) =
    ((w • collisionFlattening false m) * (w • collisionFlattening true m)ᴴ) *
      ((w • collisionFlattening true m) * (w • collisionFlattening true m)ᴴ) ↔ _
  have hw : w ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by norm_num)).ne'
  have hstar : star w = w := Complex.conj_ofReal _
  have hweighted (X Z : Matrix Pair (Word m) ℂ) :
      (w • X) * (w • Z)ᴴ = (w * w) • (X * Zᴴ) := by
    simp only [Matrix.conjTranspose_smul, hstar, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [hweighted, collisionFlattening_common_visible _ m hm,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hs : (w * w) * (w * w) ≠ 0 := mul_ne_zero (mul_ne_zero hw hw) (mul_ne_zero hw hw)
  rw [smul_right_inj hs]
  exact collision_flattening_cross_commute_iff m

/-- On the actual fair-prior ring Gram, saturation occurs exactly at lengths
divisible by four, from the common-marginal range `7 ≤ m + 2`. -/
theorem ring_trace_pair_eq_traceNorm_iff (m : ℕ) (hm : 5 ≤ m) :
    let w : ℂ := (Real.sqrt (1 / 2 : ℝ) : ℂ)
    let Y := amplitudeColumns (w • collisionFlattening false m) (w • collisionFlattening true m)
    let J := blockSign _ _
    let F := CFC.sqrt (Yᴴ * Y)
    (J * F * J * F).trace = (traceNorm (F * J * F) : ℂ) ↔ (m + 2) % 4 = 0 := by
  exact (amplitude_trace_pair_eq_traceNorm_iff _ _).trans (weighted_ring_block_criterion m hm)

/-- The signed contrast of the actual support Petz effects on the two fair
ring records saturates the hidden trace norm exactly at multiples of four. -/
theorem ring_support_petz_contrast_eq_traceNorm_iff (m : ℕ) (hm : 5 ≤ m) :
    let w : ℂ := (Real.sqrt (1 / 2 : ℝ) : ℂ)
    let X := w • collisionFlattening false m
    let Z := w • collisionFlattening true m
    let σ₀ := Xᴴ * X
    let σ₁ := Zᴴ * Z
    let W := spectralInverseSqrt (σ₀ + σ₁)
    let E₀ := W * σ₀ * W
    let E₁ := W * σ₁ * W
    ((E₀ - E₁) * (σ₀ - σ₁)).trace = (traceNorm (σ₀ - σ₁) : ℂ) ↔ (m + 2) % 4 = 0 := by
  exact (binary_support_petz_contrast_eq_traceNorm_iff _ _).trans (weighted_ring_block_criterion m hm)

/-- The actual fair-prior Petz measurement attains the best binary contrast
exactly at finite-ring lengths divisible by four. -/
theorem ring_petz_is_optimal_iff (m : ℕ) (hm : 5 ≤ m) :
    let w : ℂ := (Real.sqrt (1 / 2 : ℝ) : ℂ)
    let X := w • collisionFlattening false m
    let Z := w • collisionFlattening true m
    let σ₀ := Xᴴ * X
    let σ₁ := Zᴴ * Z
    let W := spectralInverseSqrt (σ₀ + σ₁)
    let E := W * σ₀ * W
    let D := σ₀ - σ₁
    IsGreatest (binaryContrasts D) (((E - (1 - E)) * D).trace.re) ↔ (m + 2) % 4 = 0 := by
  exact (binary_petz_is_optimal_iff _ _).trans (weighted_ring_block_criterion m hm)

set_option maxHeartbeats 800000 in
/-- In the literal partial-trace convention, the transposed fair-prior
Petz effect minimizes the physical error exactly at the same ring lengths. -/
theorem ring_physical_petz_is_optimal_iff (m : ℕ) (hm : 5 ≤ m) :
    let W₀ := collisionFlattening false m
    let W₁ := collisionFlattening true m
    let w : ℂ := (Real.sqrt (1 / 2 : ℝ) : ℂ)
    let X := w • W₀
    let Z := w • W₁
    let σ₀ := Xᴴ * X
    let σ₁ := Zᴴ * Z
    let W := spectralInverseSqrt (σ₀ + σ₁)
    let E := W * σ₀ * W
    IsLeast {x | ∃ Q, IsEffect Q ∧ physicalError W₀ W₁ Q = x}
      (physicalError W₀ W₁ Eᵀ) ↔ (m + 2) % 4 = 0 := by
  let W₀ := collisionFlattening false m
  let W₁ := collisionFlattening true m
  let w : ℂ := (Real.sqrt (1 / 2 : ℝ) : ℂ)
  let X := w • W₀
  let Z := w • W₁
  let σ₀ := Xᴴ * X
  let σ₁ := Zᴴ * Z
  let W := spectralInverseSqrt (σ₀ + σ₁)
  let E := W * σ₀ * W
  let D := σ₀ - σ₁
  let t := ((environmentGram W₀).trace.re + (environmentGram W₁).trace.re) / 2
  let score := fun Q : Matrix (Word m) (Word m) ℂ => ((Q - (1 - Q)) * D).trace.re
  let errors := {x | ∃ Q, IsEffect Q ∧ physicalError W₀ W₁ Q = x}
  change IsLeast errors (physicalError W₀ W₁ Eᵀ) ↔ _
  have hwstar : star w = w := Complex.conj_ofReal _
  have hww : w * w = ((1 / 2 : ℝ) : ℂ) := by
    change (Real.sqrt (1 / 2 : ℝ) : ℂ) * (Real.sqrt (1 / 2 : ℝ) : ℂ) = _
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hweighted (M : Matrix Pair (Word m) ℂ) :
      (w • M)ᴴ * (w • M) = (1 / 2 : ℝ) • environmentGram M := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.conjTranspose_smul, hwstar, Matrix.smul_mul, Matrix.mul_smul,
      environmentGram, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
    rw [← mul_assoc, hww]
  have hscore (Q : Matrix (Word m) (Word m) ℂ) :
      score Q = t - 2 * physicalError W₀ W₁ Qᵀ := by
    rw [physicalError_transpose]
    change (((Q - (1 - Q)) * ((w • W₀)ᴴ * (w • W₀) - (w • W₁)ᴴ * (w • W₁))).trace).re =
      ((environmentGram W₀).trace.re + (environmentGram W₁).trace.re) / 2 -
        2 * fairError W₀ W₁ Q
    simp only [hweighted, fairError, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul, Complex.sub_re, Complex.real_smul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  have horder (P Q : Matrix (Word m) (Word m) ℂ) :
      physicalError W₀ W₁ Pᵀ ≤ physicalError W₀ W₁ Qᵀ ↔ score Q ≤ score P := by
    rw [hscore P, hscore Q]
    constructor <;> intro h <;> linarith
  have h₀ : σ₀.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self X
  have h₁ : σ₁.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self Z
  obtain ⟨hE, hEc, _, _⟩ := completed_petz_effect h₀ h₁
  have hEffect : IsEffect E := ⟨hE, hEc⟩
  have hopt : IsLeast errors (physicalError W₀ W₁ Eᵀ) ↔ IsGreatest (binaryContrasts D) (score E) := by
    constructor
    · intro h
      refine ⟨⟨E, hE, hEc, rfl⟩, ?_⟩
      rintro _ ⟨M, hM, hMc, rfl⟩
      exact (horder E M).mp (h.2 ⟨Mᵀ, (isEffect_transpose_iff M).mpr ⟨hM, hMc⟩, rfl⟩)
    · intro h
      refine ⟨⟨Eᵀ, (isEffect_transpose_iff E).mpr hEffect, rfl⟩, ?_⟩
      rintro _ ⟨Q, hQ, rfl⟩
      have hQt : IsEffect Qᵀ := (isEffect_transpose_iff Q).mpr hQ
      have hle := (horder E Qᵀ).mpr (h.2 ⟨Qᵀ, hQt.1, hQt.2, rfl⟩)
      simpa only [Matrix.transpose_transpose] using hle
  exact hopt.trans (ring_petz_is_optimal_iff m hm)

end BinaryPetzOptimality

#print axioms BinaryPetzOptimality.trace_pair_eq_traceNorm_iff
#print axioms BinaryPetzOptimality.block_trace_pair_eq_traceNorm_iff
#print axioms BinaryPetzOptimality.ring_trace_pair_eq_traceNorm_iff
#print axioms BinaryPetzOptimality.ring_support_petz_contrast_eq_traceNorm_iff
#print axioms BinaryPetzOptimality.ring_petz_is_optimal_iff
#print axioms BinaryPetzOptimality.ring_physical_petz_is_optimal_iff
