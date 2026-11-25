/- GID: D5/S3/Quantum/Recovery/LocalCompression/QutritPure
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/LocalCompression/QutritPure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact plane compression and a strict qubit-memory bound for the qutrit Bell source. -/

import D5.S3.Quantum.ProcessReconstruction.LiuWildChoiObstruction
import D5.S3.Weil.ZetaLinear.RankTrace

/-! Joint trace-distance comparison for a maximally entangled qutrit. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder CStarAlgebra
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Information.PartialTraceMutualInformation (density_posSemidef)
open UnitaryReconstruction.LiuWildChoiObstruction
  (bell bell_norm normalizedChoi normalizedChoi_entry)

namespace D5.S3.Quantum.Recovery.LocalCompression.QutritPure

abbrev Qutrit := Fin 3
abbrev Qubit := Fin 2
private abbrev Joint := Qutrit × Qutrit
private abbrev JointMatrix := Matrix Joint Joint ℂ

def source : DensityState Joint := pureState (bell Qutrit) bell_norm

def error (C : QuantumChannel Qutrit Qutrit) : ℝ :=
  traceDistance source (normalizedChoi C)

private abbrev joint (ρ : DensityState Joint) : JointMatrix := CStarMatrix.ofMatrix.symm ρ.1
private abbrev outer (v : Joint → ℂ) : JointMatrix := vecMulVec v (star v)
private def correlated (v : Qutrit → ℂ) (x : Joint) : ℂ := if x.1 = x.2 then v x.1 else 0
private def ket (i j : Qutrit) (x : Joint) : ℂ := if x = (i, j) then 1 else 0

private theorem source_matrix : joint source = (1 / 3 : ℂ) • outer (correlated ![1, 1, 1]) := by
  have hs : ((Real.sqrt (Fintype.card Qutrit) : ℝ) : ℂ) ^ 2 = 3 := by
    exact_mod_cast (show Real.sqrt (Fintype.card Qutrit) ^ 2 = (3 : ℝ) by norm_num)
  have hmul : (Real.sqrt 3 : ℂ)⁻¹ * (Real.sqrt 3 : ℂ)⁻¹ = (3 : ℂ)⁻¹ := by
    have hsq : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by simpa using hs
    rw [← pow_two, inv_pow, hsq]
  have hv (k : Qutrit) : (![1, 1, 1] : Qutrit → ℂ) k = 1 := by fin_cases k <;> rfl
  change outer (bell Qutrit) = _
  ext ⟨i, u⟩ ⟨j, v⟩
  by_cases hi : i = u <;> by_cases hj : j = v <;>
    simp [bell, UnitaryReconstruction.LiuWildChoiObstruction.diagonalVector, correlated,
      vecMulVec_apply, hi, hj, hmul, hv, Pi.smul_apply, smul_eq_mul]

private theorem trace_difference (C : QuantumChannel Qutrit Qutrit) :
    (joint source - joint (normalizedChoi C)).trace = 0 := by
  rw [Matrix.trace_sub]
  exact sub_eq_zero.mpr (source.2.2.trans (normalizedChoi C).2.2.symm)

/-- All outputs are supported on the plane spanned by the first two basis vectors. -/
def Supported (C : QuantumChannel Qutrit Qutrit) : Prop :=
  ∀ (X : CStarMatrix Qutrit Qutrit ℂ) (i j : Qutrit), i = 2 ∨ j = 2 →
    C.toCompletelyPositiveMap X i j = 0

private def scaled (r : ℝ) (v : Joint → ℂ) : JointMatrix := (r : ℂ) • outer v

private def effect : JointMatrix := scaled (1 / 6) (correlated ![1, 1, 2])

private theorem scaled_outer_psd (r : ℝ) (hr : 0 ≤ r) (v : Joint → ℂ) :
    (scaled r v).PosSemidef :=
  (posSemidef_vecMulVec_self_star v).smul (by exact_mod_cast hr)

private theorem effect_psd : effect.PosSemidef := by
  exact scaled_outer_psd (1 / 6) (by norm_num) _

private theorem effect_idempotent : effect * effect = effect := by
  unfold effect scaled
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec]
  have h : star (correlated ![1, 1, 2]) ⬝ᵥ correlated ![1, 1, 2] = 6 := by
    norm_num [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ, correlated, map_ofNat]
  rw [h, vecMulVec_smul, smul_smul, smul_smul]
  norm_num

-- The reflection at the Bell ray is a unitary test for the trace norm.
private theorem effect_bound (D : JointMatrix) (htrace : D.trace = 0) :
    2 * (effect * D).trace.re ≤ traceNorm D := by
  let R : JointMatrix := (2 : ℂ) • effect - 1
  have hR : R ∈ Matrix.unitaryGroup Joint ℂ := by
    apply Matrix.mem_unitaryGroup_iff.mpr
    have hherm : Rᴴ = R := by
      simp [R, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, effect_psd.isHermitian.eq]
    change R * Rᴴ = 1
    rw [hherm]
    dsimp only [R]
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.smul_mul,
      Matrix.mul_smul, effect_idempotent, Matrix.mul_one, Matrix.one_mul,
      Matrix.one_mul, smul_smul]
    module
  have hm : (R * D).trace.re ∈
      {x : ℝ | ∃ U : unitaryGroup Joint ℂ, (U.val * D).trace.re = x} :=
    ⟨⟨R, hR⟩, rfl⟩
  obtain ⟨_, hmax⟩ := traceNorm_eq_max_re_tr_U D
  have hb := hmax hm
  simpa [R, Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul,
    htrace, Complex.sub_re, Complex.mul_re] using hb

private theorem majorant_bound (D H : JointMatrix) (htrace : D.trace = 0)
    (hH : H.PosSemidef) (hgap : (H - D).PosSemidef) :
    traceNorm D ≤ 2 * H.trace.re := by
  have h := traceNorm_add_le H (-(H - D))
  have hnorm (A : JointMatrix) (ha : A.PosSemidef) : traceNorm A = A.trace.re := by
    simpa using congrArg Complex.re (traceNorm_of_posSemidef ha)
  rw [show H + -(H - D) = D by abel, traceNorm_neg, hnorm H hH, hnorm _ hgap,
    Matrix.trace_sub, htrace, sub_zero] at h
  exact h.trans_eq (two_mul _).symm

private theorem marginal_diagonal (C : QuantumChannel Qutrit Qutrit) (i : Qutrit) :
    ∑ u : Qutrit, joint (normalizedChoi C) (i, u) (i, u) = 1 / 3 := by
  simp only [normalizedChoi_entry, Fintype.card_fin, ← Finset.mul_sum]
  change (3 : ℂ)⁻¹ * (C.toCompletelyPositiveMap
    (CStarMatrix.ofMatrix (Matrix.single i i 1))).trace = 1 / 3
  rw [C.trace_preserving]
  change (3 : ℂ)⁻¹ * (Matrix.single i i 1).trace = 1 / 3
  simp [one_div]

set_option maxHeartbeats 2000000 in
-- The Bell effect is evaluated by expanding the nine joint coordinates.
/-- The two Bell rays give a lower bound for every CPTP map into the coordinate plane. -/
private theorem supported_lower_bound (C : QuantumChannel Qutrit Qutrit) (hC : Supported C) :
    (2 / 3 : ℝ) ≤ error C := by
  let X := joint (normalizedChoi C)
  have hX : X.PosSemidef := density_posSemidef _
  have hz (i j u v : Qutrit) (h : u = 2 ∨ v = 2) : X (i, u) (j, v) = 0 := by
    simp [X, normalizedChoi_entry, hC _ u v h]
  have hsource : (effect * joint source).trace.re = 8 / 9 := by
    rw [source_matrix]
    norm_num [effect, scaled, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_succ, vecMulVec_apply, correlated, Complex.mul_re, Complex.mul_im]
  let F : JointMatrix := scaled (1 / 6) (correlated ![1, -1, 0])
  have hF : F.PosSemidef := scaled_outer_psd (1 / 6) (by norm_num) _
  have hpair : (effect * X).trace + (F * X).trace =
      (1 / 3 : ℂ) * (X (0, 0) (0, 0) + X (1, 1) (1, 1)) := by
    simp only [effect, F, scaled, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_succ, Matrix.smul_apply, smul_eq_mul,
      vecMulVec_apply, Pi.star_apply]
    norm_num [correlated, hz]; ring
  have hpos : 0 ≤ (F * X).trace.re := RHLinalg.trace_mul_nonneg_of_posSemidef hF hX
  have hdiag (i u : Qutrit) : 0 ≤ (X (i, u) (i, u)).re :=
    (Complex.nonneg_iff.mp (hX.diag_nonneg (i := (i, u)))).1
  have hb (i : Qutrit) : (X (i, 0) (i, 0)).re + (X (i, 1) (i, 1)).re = 1 / 3 := by
    have h : (∑ u : Qutrit, X (i, u) (i, u)) = 1 / 3 := marginal_diagonal C i
    rw [Fin.sum_univ_three, hz i i 2 2 (Or.inl rfl), add_zero] at h
    simpa using congrArg Complex.re h
  have htrace : (effect * X).trace.re ≤ 2 / 9 := by
    have h := congrArg Complex.re hpair
    simp only [Complex.add_re, Complex.mul_re, Complex.div_re] at h
    norm_num at h
    linarith [hb 0, hb 1, hdiag 0 1, hdiag 1 0]
  have h := effect_bound (joint source - X) (trace_difference C)
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, hsource] at h
  change (2 / 3 : ℝ) ≤ traceNorm (joint source - X) / 2
  linarith

private def encodeKraus : Fin 2 → Matrix Qubit Qutrit ℂ :=
  ![!![1, 0, 0; 0, 1, 0], !![0, 0, 0; 0, 0, 1]]

private theorem encode_complete : ∑ k, (encodeKraus k)ᴴ * encodeKraus k = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [encodeKraus, Matrix.sum_apply, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.conjTranspose_apply, Matrix.one_apply]

/-- Preserve the first two levels and reset the third to qubit level 1. -/
def encoder : QuantumChannel Qutrit Qubit :=
  (finite_kraus_quantum_channel encodeKraus encode_complete).choose

private def decodeKraus (b c : ℝ) : Fin 2 → Matrix Qutrit Qubit ℂ :=
  ![!![1, 0; 0, (b : ℂ); 0, 0], !![0, 0; 0, 0; 0, (c : ℂ)]]

private theorem decode_complete (b c : ℝ) (h : b ^ 2 + c ^ 2 = 1) :
    ∑ k, (decodeKraus b c k)ᴴ * decodeKraus b c k = 1 := by
  have hc : (b : ℂ) * b + (c : ℂ) * c = 1 := by exact_mod_cast (by simpa [pow_two] using h)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [decodeKraus, Matrix.sum_apply, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.conjTranspose_apply, Matrix.one_apply, hc]

/-- Its first Kraus operator embeds levels 0 and 1 with amplitudes 1 and b.
The second transfers qubit level 1 to qutrit level 2 with amplitude c. -/
def decoder (b c : ℝ) (h : b ^ 2 + c ^ 2 = 1) : QuantumChannel Qubit Qutrit :=
  (finite_kraus_quantum_channel (decodeKraus b c) (decode_complete b c h)).choose

private theorem encoder_apply (X : Matrix Qutrit Qutrit ℂ) :
    CStarMatrix.ofMatrix.symm (encoder.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
      !![X 0 0, X 0 1; X 1 0, X 1 1 + X 2 2] := by
  unfold encoder
  rw [(finite_kraus_quantum_channel encodeKraus encode_complete).choose_spec]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [encodeKraus, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ]

private theorem decoder_apply (b c : ℝ) (h : b ^ 2 + c ^ 2 = 1) (X : Matrix Qubit Qubit ℂ) :
    CStarMatrix.ofMatrix.symm ((decoder b c h).toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
      !![X 0 0, X 0 1 * (b : ℂ), 0;
         (b : ℂ) * X 1 0, (b : ℂ) ^ 2 * X 1 1, 0;
         0, 0, (c : ℂ) ^ 2 * X 1 1] := by
  unfold decoder
  rw [(finite_kraus_quantum_channel (decodeKraus b c) (decode_complete b c h)).choose_spec]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [decodeKraus, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ] <;> ring

private def recovered (b c : ℝ) (h : b ^ 2 + c ^ 2 = 1) : QuantumChannel Qutrit Qutrit :=
  (decoder b c h).comp encoder

set_option maxHeartbeats 4000000 in
-- The joint Choi matrix is checked on each pair of product-basis coordinates.
private theorem recovered_matrix (b c : ℝ) (h : b ^ 2 + c ^ 2 = 1) :
    joint (normalizedChoi (recovered b c h)) = (1 / 3 : ℂ) •
      (outer (correlated ![1, (b : ℂ), 0]) + (c : ℂ) ^ 2 • outer (ket 1 2) +
        (b : ℂ) ^ 2 • outer (ket 2 1) + (c : ℂ) ^ 2 • outer (ket 2 2)) := by
  have action (X : Matrix Qutrit Qutrit ℂ) :
      CStarMatrix.ofMatrix.symm
        ((recovered b c h).toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        !![X 0 0, X 0 1 * (b : ℂ), 0;
           (b : ℂ) * X 1 0, (b : ℂ) ^ 2 * (X 1 1 + X 2 2), 0;
           0, 0, (c : ℂ) ^ 2 * (X 1 1 + X 2 2)] := by
    unfold recovered
    rw [QuantumChannel.comp_apply, ← CStarMatrix.ofMatrix.apply_symm_apply
      (encoder.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)), encoder_apply, decoder_apply]
    rfl
  ext ⟨i, u⟩ ⟨j, v⟩
  change UnitaryReconstruction.LiuWildChoiObstruction.pairMatrix
    (normalizedChoi (recovered b c h)) (i, u) (j, v) = _
  rw [normalizedChoi_entry]
  change (Fintype.card Qutrit : ℂ)⁻¹ *
    (CStarMatrix.ofMatrix.symm ((recovered b c h).toCompletelyPositiveMap
      (CStarMatrix.ofMatrix (Matrix.single i j 1)))) u v = _
  rw [action]
  fin_cases i <;> fin_cases j <;> fin_cases u <;> fin_cases v <;>
    norm_num [Matrix.single, correlated, ket, vecMulVec_apply, Prod.mk.injEq, one_div]; ring

/-- Projection to the coordinate plane followed by reset into level 1. -/
def projectionReset : QuantumChannel Qutrit Qutrit := recovered 1 0 (by norm_num)

private theorem reset_supported : Supported projectionReset := by
  intro X i j hij
  have h := decoder_apply 1 0 (by norm_num)
    (CStarMatrix.ofMatrix.symm (encoder.toCompletelyPositiveMap X))
  have he := congrFun (congrFun h i) j
  change (projectionReset.toCompletelyPositiveMap X) i j = _ at he
  rcases hij with rfl | rfl
  · fin_cases j <;> simpa using he
  · fin_cases i <;> simpa using he

private theorem outer_trace (v : Joint → ℂ) : (outer v).trace = star v ⬝ᵥ v := by
  rw [Matrix.trace_vecMulVec, dotProduct_comm]

set_option maxHeartbeats 3500000 in
-- The rank-one decomposition is checked on each pair of product-basis coordinates.
private theorem reset_upper : error projectionReset ≤ 2 / 3 := by
  let H : JointMatrix := scaled (1 / 9) (correlated ![1, 1, 2])
  have hH : H.PosSemidef := scaled_outer_psd (1 / 9) (by norm_num) _
  let X := joint source - joint (normalizedChoi projectionReset)
  have heq : H - X = scaled (1 / 9) (correlated ![1, 1, -1]) +
      scaled (1 / 3) (ket 2 1) := by
    dsimp only [X]
    rw [source_matrix, projectionReset, recovered_matrix]
    ext ⟨i, u⟩ ⟨j, v⟩
    fin_cases i <;> fin_cases j <;> fin_cases u <;> fin_cases v <;>
      norm_num [H, scaled, correlated, ket, vecMulVec_apply, Prod.mk.injEq]
  have hmajor : (H - X).PosSemidef := by
    rw [heq]
    exact (scaled_outer_psd (1 / 9) (by norm_num) _).add (scaled_outer_psd (1 / 3) (by norm_num) _)
  have htrace : H.trace.re = 2 / 3 := by
    norm_num [H, scaled, Matrix.trace_smul, outer_trace, dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_succ, correlated, Complex.mul_re, Complex.mul_im]
  have h := majorant_bound X H (trace_difference _) hH hmajor
  change traceNorm X / 2 ≤ _
  linarith

/-- The minimum over arbitrary CPTP maps supported on the coordinate plane is 2 / 3. -/
private theorem supported_optimum :
    IsLeast {d : ℝ | ∃ C : QuantumChannel Qutrit Qutrit, Supported C ∧ error C = d} (2 / 3) := by
  refine ⟨⟨projectionReset, reset_supported,
    le_antisymm reset_upper (supported_lower_bound _ reset_supported)⟩, ?_⟩
  rintro d ⟨C, hC, rfl⟩
  exact supported_lower_bound C hC

set_option maxHeartbeats 4000000 in
-- The rational certificate is an equality of full joint matrices.
/-- Actual qubit-memory encoder and decoder with joint trace-distance error below 13 / 20. -/
theorem qubit_memory_witness :
    error ((decoder (4 / 5) (3 / 5) (by norm_num)).comp encoder) ≤ (10189 / 15750 : ℝ) ∧
      (10189 / 15750 : ℝ) < 13 / 20 := by
  refine ⟨?_, by norm_num⟩
  let C := recovered (4 / 5) (3 / 5) (by norm_num)
  let X := joint source - joint (normalizedChoi C)
  let H : JointMatrix := scaled (1 / 31500) (correlated ![60, 73, 107])
  have hH : H.PosSemidef := scaled_outer_psd (1 / 31500) (by norm_num) _
  have heq : H - X =
      scaled (1 / 31500) (correlated ![60, 38, -68]) +
      scaled (1 / 300) (correlated ![0, 1, -1]) +
      scaled (3 / 25) (ket 1 2) + scaled (16 / 75) (ket 2 1) := by
    dsimp only [X, C]
    rw [source_matrix, recovered_matrix]
    ext ⟨i, u⟩ ⟨j, v⟩
    fin_cases i <;> fin_cases j <;> fin_cases u <;> fin_cases v <;>
      norm_num [H, scaled, correlated, ket, vecMulVec_apply, Prod.mk.injEq]
  have hmajor : (H - X).PosSemidef := by
    rw [heq]
    exact (((scaled_outer_psd (1 / 31500) (by norm_num) _).add
      (scaled_outer_psd (1 / 300) (by norm_num) _)).add
      (scaled_outer_psd (3 / 25) (by norm_num) _)).add (scaled_outer_psd (16 / 75) (by norm_num) _)
  have htrace : H.trace.re = 10189 / 15750 := by
    norm_num [H, scaled, Matrix.trace_smul, outer_trace, dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_succ, correlated, Complex.mul_re, Complex.mul_im]
  have h := majorant_bound X H (trace_difference C) hH hmajor
  change traceNorm X / 2 ≤ _
  linarith

open scoped Kronecker
open UnitaryReconstruction (conjugation conjugation_apply referenceMatrix
  referenceMatrix_apply referenceMatrix_comp referenceMatrix_conjugation
  referenceUnitary channel_ext)

private def leftLift (V : Matrix Qutrit Qutrit ℂ) : JointMatrix :=
  V ⊗ₖ (1 : Matrix Qutrit Qutrit ℂ)

private theorem leftLift_congruence (V : Matrix Qutrit Qutrit ℂ) (X : JointMatrix)
    (i u j v : Qutrit) :
    (leftLift V * X * (leftLift V)ᴴ) (i, u) (j, v) =
      ∑ s : Qutrit, ∑ t : Qutrit, (V i s * star (V j t)) * X (s, u) (t, v) := by
  simp only [leftLift, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Finset.sum_mul, Finset.mul_sum, apply_ite,
    mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul, star_zero, star_one,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring

private theorem reference_commutes_leftLift (C : QuantumChannel Qutrit Qutrit)
    (V : Matrix Qutrit Qutrit ℂ) (X : JointMatrix) :
    referenceMatrix C (leftLift V * X * (leftLift V)ᴴ) =
      leftLift V * referenceMatrix C X * (leftLift V)ᴴ := by
  ext ⟨i, u⟩ ⟨j, v⟩
  rw [leftLift_congruence, referenceMatrix_apply]
  have h : CStarMatrix.ofMatrix (fun x y =>
      (leftLift V * X * (leftLift V)ᴴ) (i, x) (j, y)) =
      ∑ s : Qutrit, ∑ t : Qutrit, (V i s * star (V j t)) •
        CStarMatrix.ofMatrix (fun x y => X (s, x) (t, y)) := by
    ext x y
    have hsum (f : Qutrit → CStarMatrix Qutrit Qutrit ℂ) :
        (∑ k, f k) x y = ∑ k, f k x y := Matrix.sum_apply x y Finset.univ f
    simp_rw [hsum]
    simp only [CStarMatrix.smul_apply, smul_eq_mul, CStarMatrix.ofMatrix_apply]
    exact leftLift_congruence V X i x j y
  rw [h]
  simp only [map_sum, map_smul]
  change (∑ s, ∑ t, (V i s * star (V j t)) •
    CStarMatrix.ofMatrix.symm (C.toCompletelyPositiveMap
      (CStarMatrix.ofMatrix fun x y => X (s, x) (t, y))) : Matrix Qutrit Qutrit ℂ) u v = _
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, referenceMatrix_apply]
  rfl

private theorem source_entry (i u j v : Qutrit) :
    joint source (i, u) (j, v) = (1 / 3 : ℂ) * (if u = i ∧ v = j then 1 else 0) := by
  rw [source_matrix]
  have h (k : Qutrit) : (![1, 1, 1] : Qutrit → ℂ) k = 1 := by fin_cases k <;> rfl
  by_cases hi : i = u <;> by_cases hj : j = v <;>
    simp [correlated, vecMulVec_apply, h, hi, hj, eq_comm (a := u), eq_comm (a := v)]

private theorem conjugate_source (U : unitaryGroup Qutrit ℂ) :
    referenceMatrix (conjugation (star U)) (joint source) =
      leftLift (U.valᴴ)ᵀ * joint source * (leftLift (U.valᴴ)ᵀ)ᴴ := by
  ext ⟨i, u⟩ ⟨j, v⟩
  rw [leftLift_congruence, referenceMatrix_apply]
  have h : (fun x y => joint source (i, x) (j, y)) = (1 / 3 : ℂ) • Matrix.single i j 1 := by
    ext x y
    change joint source (i, x) (j, y) = (1 / 3 : ℂ) * Matrix.single i j 1 x y
    simp [source_entry, Matrix.single, eq_comm (a := x), eq_comm (a := y)]
  rw [h]
  have hc := congrArg (fun M : Matrix Qutrit Qutrit ℂ => M u v)
    (conjugation_apply (star U) ((1 / 3 : ℂ) • Matrix.single i j 1))
  change (CStarMatrix.ofMatrix.symm ((conjugation (star U)).toCompletelyPositiveMap
    (CStarMatrix.ofMatrix ((1 / 3 : ℂ) • Matrix.single i j 1)))) u v = _
  rw [hc]
  simp [source_entry, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_apply,
    Matrix.single, Matrix.conjTranspose_apply, Matrix.transpose_apply, ite_and,
    mul_ite, ite_mul, Finset.sum_mul, ← Matrix.star_eq_conjTranspose,
    ← Unitary.coe_star, mul_assoc, mul_left_comm, mul_comm]
  have hj : star ((star U).val v j) = U.val j v := by
    change star (star (U.val j v)) = U.val j v
    exact star_star _
  change U.val j v * (star U).val u i = (star U).val u i * star ((star U).val v j)
  rw [hj, mul_comm]

private def rotate (U : unitaryGroup Qutrit ℂ) (C : QuantumChannel Qutrit Qutrit) :=
  (conjugation U).comp (C.comp (conjugation (star U)))

private theorem trace_norm_congruence (A V : JointMatrix) (hV : Vᴴ * V = 1) :
    traceNorm (V * A * Vᴴ) = traceNorm A := by
  let S := CFC.sqrt (Aᴴ * A)
  have hsquare : S * S = Aᴴ * A :=
    CFC.sqrt_mul_sqrt_self _ (posSemidef_conjTranspose_mul_self A).nonneg
  have hp : (V * S * Vᴴ).PosSemidef :=
    (Matrix.LE.le.posSemidef (CFC.sqrt_nonneg (Aᴴ * A))).mul_mul_conjTranspose_same V
  have hprod : (V * S * Vᴴ) * (V * S * Vᴴ) =
      (V * A * Vᴴ)ᴴ * (V * A * Vᴴ) := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = V * (S * (Vᴴ * V) * S) * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = V * (Aᴴ * A) * Vᴴ := by rw [hV, Matrix.mul_one, hsquare]
      _ = V * (Aᴴ * (Vᴴ * V) * A) * Vᴴ := by rw [hV, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  change (CFC.sqrt ((V * A * Vᴴ)ᴴ * (V * A * Vᴴ))).trace.re = S.trace.re
  rw [CFC.sqrt_unique hprod hp.nonneg, Matrix.trace_mul_comm]
  simp [← Matrix.mul_assoc, hV]

private theorem rotate_error (U : unitaryGroup Qutrit ℂ) (C : QuantumChannel Qutrit Qutrit) :
    error (rotate U C) = error C := by
  let L := leftLift (U.valᴴ)ᵀ
  let R := (referenceUnitary Qutrit U).val
  have hL : Lᴴ * L = 1 := by
    dsimp [L, leftLift]
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul,
      Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,
      ← Matrix.transpose_mul, Matrix.conjTranspose_conjTranspose]
    rw [show U.valᴴ * U.val = 1 from Unitary.star_mul_self_of_mem U.prop,
      Matrix.transpose_one, Matrix.one_kronecker_one]
  have hR : Rᴴ * R = 1 := Unitary.star_mul_self_of_mem (referenceUnitary Qutrit U).prop
  have hChoi : joint (normalizedChoi (rotate U C)) =
      R * (L * joint (normalizedChoi C) * Lᴴ) * Rᴴ := by
    change referenceMatrix (rotate U C) (joint source) = _
    rw [rotate, referenceMatrix_comp, referenceMatrix_comp, conjugate_source,
      reference_commutes_leftLift, referenceMatrix_conjugation]
    rfl
  have hcancel (X : JointMatrix) :
      referenceMatrix (conjugation U) (referenceMatrix (conjugation (star U)) X) = X := by
    rw [← referenceMatrix_comp]
    have he : (conjugation U).comp (conjugation (star U)) = conjugation 1 := by
      apply channel_ext
      intro Y
      apply CStarMatrix.ofMatrix.symm.injective
      rw [QuantumChannel.comp_apply]
      obtain ⟨Y, rfl⟩ := CStarMatrix.ofMatrix.surjective Y
      rw [← CStarMatrix.ofMatrix.apply_symm_apply
        ((conjugation (star U)).toCompletelyPositiveMap (CStarMatrix.ofMatrix Y)),
        conjugation_apply, conjugation_apply, conjugation_apply]
      have hu : U.val * U.valᴴ = 1 := Unitary.mul_star_self_of_mem U.prop
      change U.val * (U.valᴴ * Y * U.valᴴᴴ) * U.valᴴ = 1 * Y * (1 : Matrix Qutrit Qutrit ℂ)ᴴ
      simp only [conjTranspose_conjTranspose, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
      calc
        _ = (U.val * U.valᴴ) * Y * (U.val * U.valᴴ) := by simp only [Matrix.mul_assoc]
        _ = Y := by simp [hu]
    rw [he, referenceMatrix_conjugation]
    simp [referenceUnitary]
  have hSource : R * (L * joint source * Lᴴ) * Rᴴ = joint source := by
    have h := hcancel (joint source)
    rwa [conjugate_source, referenceMatrix_conjugation] at h
  change traceNorm (joint source - joint (normalizedChoi (rotate U C))) / 2 = _
  rw [hChoi]
  conv_lhs => rw [← hSource]
  -- Distribute the two unitary congruences over the state difference.
  have hsub : R * (L * joint source * Lᴴ) * Rᴴ -
      R * (L * joint (normalizedChoi C) * Lᴴ) * Rᴴ =
      R * (L * (joint source - joint (normalizedChoi C)) * Lᴴ) * Rᴴ := by
    simp [Matrix.mul_sub, Matrix.sub_mul]
  -- `hSource` rewrites only the source on the left of the distance comparison.
  change _ = traceNorm (joint source - joint (normalizedChoi C)) / 2
  rw [hsub, trace_norm_congruence _ R hR, trace_norm_congruence _ L hL]

/-- The output lies in the span of the first two columns of the unitary frame. -/
def PlaneSupported (U : unitaryGroup Qutrit ℂ) (C : QuantumChannel Qutrit Qutrit) : Prop :=
  Supported ((conjugation (star U)).comp C)

/-- The exact minimum holds in every unitary frame, hence for any prescribed output plane. -/
theorem plane_optimum (U : unitaryGroup Qutrit ℂ) :
    IsLeast {d : ℝ | ∃ C : QuantumChannel Qutrit Qutrit,
      PlaneSupported U C ∧ error C = d} (2 / 3) := by
  obtain ⟨⟨C, hC, he⟩, _⟩ := supported_optimum
  refine ⟨⟨rotate U C, ?_, (rotate_error U C).trans he⟩, ?_⟩
  · intro X i j hij
    have hu : U.valᴴ * U.val = 1 := Unitary.star_mul_self_of_mem U.prop
    have hh (Y : CStarMatrix Qutrit Qutrit ℂ) :
        (conjugation (star U)).toCompletelyPositiveMap
          ((conjugation U).toCompletelyPositiveMap Y) = Y := by
      apply CStarMatrix.ofMatrix.symm.injective
      obtain ⟨Y, rfl⟩ := CStarMatrix.ofMatrix.surjective Y
      rw [← CStarMatrix.ofMatrix.apply_symm_apply
        ((conjugation U).toCompletelyPositiveMap (CStarMatrix.ofMatrix Y)),
        conjugation_apply, conjugation_apply]
      change U.valᴴ * (U.val * Y * U.valᴴ) * U.valᴴᴴ = Y
      rw [conjTranspose_conjTranspose]
      calc
        _ = (U.valᴴ * U.val) * Y * (U.valᴴ * U.val) := by simp only [Matrix.mul_assoc]
        _ = Y := by simp [hu]
    simp only [rotate, QuantumChannel.comp_apply, hh]
    exact hC ((conjugation (star U)).toCompletelyPositiveMap X) i j hij
  · rintro d ⟨C, hC, rfl⟩
    have h := supported_lower_bound (rotate (star U) C) (by
      intro X i j hij
      exact hC ((conjugation (star (star U))).toCompletelyPositiveMap X) i j hij)
    rwa [rotate_error] at h

/-- The witness decoder takes a pure memory state to a mixture on two output levels. -/
theorem witness_decoder_not_isometric :
    ¬ ∃ V : Matrix Qutrit Qubit ℂ, ∀ X : Matrix Qubit Qubit ℂ,
      CStarMatrix.ofMatrix.symm
        ((decoder (4 / 5) (3 / 5) (by norm_num)).toCompletelyPositiveMap
          (CStarMatrix.ofMatrix X)) = V * X * Vᴴ := by
  rintro ⟨V, hV⟩
  have h := hV !![0, 0; 0, 1]
  rw [decoder_apply] at h
  have hentry (i j : Qutrit) :
      (!![0, 0, 0; 0, (16 / 25 : ℂ), 0; 0, 0, 9 / 25] : Matrix Qutrit Qutrit ℂ) i j =
        V i 1 * star (V j 1) := by
    have hij := congrFun (congrFun h i) j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two] at hij ⊢ <;>
      exact hij
  have h11 : (16 / 25 : ℂ) = V 1 1 * star (V 1 1) := hentry 1 1
  have h22 : (9 / 25 : ℂ) = V 2 1 * star (V 2 1) := hentry 2 2
  have h12 : (0 : ℂ) = V 1 1 * star (V 2 1) := hentry 1 2
  have h21 : (0 : ℂ) = V 2 1 * star (V 1 1) := hentry 2 1
  have hne : (16 / 25 : ℂ) * (9 / 25) = 0 := calc
    _ = (V 1 1 * star (V 1 1)) * (V 2 1 * star (V 2 1)) := by rw [← h11, ← h22]
    _ = (V 1 1 * star (V 2 1)) * (V 2 1 * star (V 1 1)) := by ring
    _ = 0 := by rw [← h12, ← h21, mul_zero]
  norm_num at hne

end D5.S3.Quantum.Recovery.LocalCompression.QutritPure
