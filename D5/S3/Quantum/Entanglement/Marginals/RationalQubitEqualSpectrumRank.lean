/- GID: D5/S3/Quantum/Entanglement/Marginals/RationalQubitEqualSpectrumRank
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Marginals/RationalQubitEqualSpectrumRank
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Equal-spectrum rational qubit marginals admit a rational rank-two bound. -/

import D5.S3.Quantum.Entanglement.Marginals.RationalQubitPurity
import D5.S3.Quantum.Information.PartialTraceMutualInformation

/-! A spectral alignment projector for rational qubit marginals. -/

open Matrix Complex
open scoped ComplexConjugate ComplexOrder Kronecker Matrix
open D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension
open D5.S3.Quantum.Entanglement.Marginals.RationalQubitPurity (square_eq_trace_sub_det)
open D5.S3.Quantum.Information.PartialTraceMutualInformation

set_option autoImplicit false

namespace D5.S3.Quantum.Entanglement.Marginals.RationalQubitEqualSpectrumRank

private abbrev Qubit := Matrix Bool Bool ℂ
private abbrev Joint := Matrix (Bool × Bool) (Bool × Bool) ℂ

private theorem rational_one {n : Type*} [DecidableEq n] (i j : n) :
    RationalEntry ((1 : Matrix n n ℂ) i j) := by
  by_cases h : i = j
  · rw [Matrix.one_apply, ite_eq_left h]
    exact rationalComplex.one_mem
  · rw [Matrix.one_apply, ite_eq_right h]
    exact rationalComplex.zero_mem

private theorem projection_rank (P : Joint) (hP : P * P = P) (ht : P.trace = 2) :
    P.rank = 2 := by
  have hi : IsIdempotentElem P := hP
  have hi' : IsIdempotentElem P.toLin' := hi.map Matrix.toLinAlgEquiv'
  have hProj := (LinearMap.isProj_range_iff_isIdempotentElem _ |>.mpr hi').trace
  rw [Matrix.trace_toLin'_eq, ht] at hProj
  rw [Matrix.rank_eq_finrank_range_toLin P (Pi.basisFun ℂ _) (Pi.basisFun ℂ _)]
  exact_mod_cast hProj.symm

private theorem centered_square (A : Qubit) (ht : A.trace = 1) :
    (A - (1 / 2 : ℂ) • 1) * (A - (1 / 2 : ℂ) • 1) = (1 / 4 - A.det) • 1 := by
  rw [sub_mul, mul_sub, mul_sub, square_eq_trace_sub_det, ht]
  simp only [Matrix.mul_smul, Matrix.smul_mul, one_mul, mul_one, one_smul, smul_smul]
  module

private theorem scalar_of_centered_square_zero {P : Qubit} (hP : P.IsHermitian)
    (h : P * P = 0) : P = 0 :=
  Matrix.conjTranspose_mul_self_eq_zero.mp (by rwa [hP.eq])

private theorem projector_extension (A B H K : Qubit) (s : ℂ) (hs : s ≠ 0)
    (hsR : conj s = s) (hsQ : RationalEntry s)
    (hA : A.PosSemidef) (htA : A.trace = 1)
    (hAQ : ∀ i j, RationalEntry (A i j))
    (hH : H.IsHermitian) (hK : K.IsHermitian)
    (hHQ : ∀ i j, RationalEntry (H i j)) (hKQ : ∀ i j, RationalEntry (K i j))
    (hHs : H * H = s • 1) (hKs : K * K = s • 1)
    (htH : H.trace = 0) (htK : K.trace = 0)
    (hcomm : A * H = H * A)
    (hRight : (A * H).trace • K = (2 * s) • (B - (1 / 2 : ℂ) • 1)) :
    ∃ S : Joint, S.PosSemidef ∧ partialTraceRight S = A ∧ partialTraceLeft S = B ∧
      S.rank ≤ 2 ∧ ∀ i j, RationalEntry (S i j) := by
  let X : Joint := A ⊗ₖ (1 : Qubit)
  let T : Joint := s⁻¹ • (H ⊗ₖ K)
  let P : Joint := (1 / 2 : ℂ) • (1 + T)
  have hT2 : T * T = 1 := by
    dsimp only [T]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.mul_kronecker_mul,
      hHs, hKs, Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul,
      Matrix.one_kronecker_one, smul_smul]
    rw [show s⁻¹ * s⁻¹ * s * s = 1 by field_simp, one_smul]
  have hTt : T.trace = 0 := by simp [T, Matrix.trace_smul, Matrix.trace_kronecker, htH]
  have hP2 : P * P = P := by
    dsimp only [P]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, add_mul, mul_add, mul_add, hT2]
    simp only [one_mul, mul_one]
    module
  have hPt : P.trace = 2 := by
    norm_num [P, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one, hTt, Fintype.card_prod]
  have hPh : Pᴴ = P := by
    simp [P, T, Matrix.conjTranspose_kronecker, hH.eq, hK.eq, hsR]
  have hPX : P * X = X * P := by
    dsimp only [X, P, T]
    simp only [Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, one_mul, mul_one,
      ← Matrix.mul_kronecker_mul, hcomm]
  have hXP : X * P =
      (1 / 2 : ℂ) • ((A ⊗ₖ (1 : Qubit)) + s⁻¹ • ((A * H) ⊗ₖ K)) := by
    simp [X, P, T, mul_add, ← Matrix.mul_kronecker_mul]
  refine ⟨X * P, ?_, ?_, ?_, ?_, ?_⟩
  · have hp := (hA.kronecker (Matrix.PosSemidef.one : (1 : Qubit).PosSemidef))
        |>.conjTranspose_mul_mul_same P
    change (Pᴴ * X * P).PosSemidef at hp
    rwa [hPh, hPX, mul_assoc, hP2] at hp
  · rw [hXP]
    rw [smul_add, smul_smul, ← Matrix.smul_kronecker, ← Matrix.smul_kronecker,
      partialTraceRight_add]
    change partialTraceRight (Matrix.kronecker ((1 / 2 : ℂ) • A) (1 : Qubit)) +
      partialTraceRight (Matrix.kronecker (((1 / 2 : ℂ) * s⁻¹) • (A * H)) K) = A
    rw [partialTraceRight_kronecker, partialTraceRight_kronecker,
      Matrix.trace_one, htK, zero_smul, add_zero, smul_smul]
    norm_num
  · rw [hXP]
    rw [smul_add, smul_smul, ← Matrix.kronecker_smul, ← Matrix.kronecker_smul,
      partialTraceLeft_add]
    change partialTraceLeft (Matrix.kronecker A ((1 / 2 : ℂ) • (1 : Qubit))) +
      partialTraceLeft (Matrix.kronecker (A * H) (((1 / 2 : ℂ) * s⁻¹) • K)) = B
    rw [partialTraceLeft_kronecker, partialTraceLeft_kronecker, htA, one_smul,
      smul_comm ((A * H).trace)]
    rw [hRight]
    rw [smul_smul, show (1 / 2 : ℂ) * s⁻¹ * (2 * s) = 1 by field_simp, one_smul]
    module
  · exact (Matrix.rank_mul_le_right _ _).trans (by rw [projection_rank _ hP2 hPt])
  · intro i j
    rw [hXP]
    refine rationalComplex.mul_mem ?_ (rationalComplex.add_mem
        (rationalComplex.mul_mem (hAQ _ _) (rational_one _ _))
        (rationalComplex.mul_mem (rationalComplex.inv_mem hsQ)
          (rationalComplex.mul_mem ?_ (hKQ _ _))))
    · exact rationalComplex.div_mem rationalComplex.one_mem
        (ofNat_mem rationalComplex 2)
    · exact rationalComplex.sum_mem fun k _ => rationalComplex.mul_mem (hAQ _ k) (hHQ k _)

/-- Trace-one positive qubit marginals with rational entries and equal determinants admit
a joint state with rational entries and rank at most two. -/
theorem rational_endpoint_rank_le_two_of_equal_det (A B : Matrix Bool Bool ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (htA : A.trace = 1) (htB : B.trace = 1)
    (hd : A.det = B.det) (hAQ : ∀ i j, RationalEntry (A i j))
    (hBQ : ∀ i j, RationalEntry (B i j)) :
    ∃ S : Joint, S.PosSemidef ∧ partialTraceRight S = A ∧ partialTraceLeft S = B ∧
      S.rank ≤ 2 ∧ ∀ i j, RationalEntry (S i j) := by
  let H : Qubit := A - (1 / 2 : ℂ) • 1
  let K : Qubit := B - (1 / 2 : ℂ) • 1
  let s : ℂ := 1 / 4 - A.det
  have hH : H.IsHermitian := hA.isHermitian.sub (by simp [Matrix.IsHermitian])
  have hK : K.IsHermitian := hB.isHermitian.sub (by simp [Matrix.IsHermitian])
  have hHs : H * H = s • 1 := centered_square A htA
  have hKs : K * K = s • 1 := by simpa [K, s, hd] using centered_square B htB
  have hhalf : RationalEntry (1 / 2 : ℂ) :=
    rationalComplex.div_mem rationalComplex.one_mem (ofNat_mem rationalComplex 2)
  have htH : H.trace = 0 := by norm_num [H, Matrix.trace_smul, htA, Matrix.trace_one]
  have htK : K.trace = 0 := by norm_num [K, Matrix.trace_smul, htB, Matrix.trace_one]
  by_cases hs : s = 0
  · have hH0 : H = 0 := scalar_of_centered_square_zero hH (by simpa [hs] using hHs)
    have hK0 : K = 0 := scalar_of_centered_square_zero hK (by simpa [hs] using hKs)
    have hAs : A = (1 / 2 : ℂ) • 1 := sub_eq_zero.mp hH0
    have hBs : B = (1 / 2 : ℂ) • 1 := sub_eq_zero.mp hK0
    let D : Qubit := diagonal (fun i => if i then -1 else 1)
    have hD : D.IsHermitian := by
      ext i j : 1
      cases i <;> cases j <;> simp [D, Matrix.conjTranspose_apply]
    have hDs : D * D = (1 : Qubit) := by
      dsimp only [D]
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      cases i <;> norm_num
    have hDt : D.trace = 0 := by norm_num [D, Matrix.trace, Fintype.sum_bool]
    have hDQ (i j : Bool) : RationalEntry (D i j) := by
      cases i <;> cases j
      · exact rationalComplex.one_mem
      · exact rationalComplex.zero_mem
      · exact rationalComplex.zero_mem
      · exact rationalComplex.neg_mem rationalComplex.one_mem
    refine projector_extension A B D D 1 one_ne_zero (map_one _) rationalComplex.one_mem
      hA htA hAQ hD hD hDQ hDQ (by simpa using hDs) (by simpa using hDs) hDt hDt ?_ ?_
    · rw [hAs]; simp
    · rw [hAs, hBs]; simp [Matrix.trace_smul, hDt]
  · have hsR : conj s = s := by
      have he := congrArg (fun M : Qubit => M false false)
        (show (H * H)ᴴ = H * H by simp [hH.eq])
      rw [hHs, Matrix.conjTranspose_smul, Matrix.conjTranspose_one] at he
      simpa [Matrix.smul_apply] using he
    have hsQ : RationalEntry s := by
      have hdet : RationalEntry A.det := by
        rw [← Matrix.det_submatrix_equiv_self finTwoEquiv A, Matrix.det_fin_two]
        exact rationalComplex.sub_mem (rationalComplex.mul_mem (hAQ _ _) (hAQ _ _))
          (rationalComplex.mul_mem (hAQ _ _) (hAQ _ _))
      exact rationalComplex.sub_mem
        (rationalComplex.div_mem rationalComplex.one_mem (ofNat_mem rationalComplex 4)) hdet
    have hcomm : A * H = H * A := by simp [H, mul_sub, sub_mul]
    have htAH : (A * H).trace = 2 * s := by
      rw [show A * H = H * H + (1 / 2 : ℂ) • H by
        rw [show A = H + (1 / 2 : ℂ) • 1 by simp [H], add_mul, Matrix.smul_mul, one_mul]]
      norm_num [hHs, Matrix.trace_add, Matrix.trace_smul, htH, Matrix.trace_one, mul_comm]
    refine projector_extension A B H K s hs hsR hsQ hA htA hAQ hH hK ?_ ?_ hHs hKs
      htH htK hcomm ?_
    · intro i j
      exact rationalComplex.sub_mem (hAQ i j) (rationalComplex.mul_mem hhalf (rational_one i j))
    · intro i j
      exact rationalComplex.sub_mem (hBQ i j) (rationalComplex.mul_mem hhalf (rational_one i j))
    · rw [htAH]

end D5.S3.Quantum.Entanglement.Marginals.RationalQubitEqualSpectrumRank
