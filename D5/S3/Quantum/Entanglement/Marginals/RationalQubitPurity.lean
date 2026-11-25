/- GID: D5/S3/Quantum/Entanglement/Marginals/RationalQubitPurity
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Marginals/RationalQubitPurity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A common Gaussian norm characterizes rational pure extensions of qubit marginals. -/

import D5.S0.Observation.MatrixTracePowerSum
import D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension

/-! Gaussian norm obstruction and construction for rational pure two-qubit densities. -/

open Matrix Complex
open scoped ComplexConjugate ComplexOrder Matrix
open D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)

set_option autoImplicit false

namespace D5.S3.Quantum.Entanglement.Marginals.RationalQubitPurity

theorem square_eq_trace_sub_det (A : Matrix Bool Bool ℂ) :
    A * A = A.trace • A - A.det • (1 : Matrix Bool Bool ℂ) := by
  let e := finTwoEquiv
  let B := A.submatrix e e
  have htrace : B.trace = A.trace := Fintype.sum_equiv e _ _ fun _ => rfl
  have h := D5.S0.Observation.MatrixTracePowerSum.pow_add_two B 0
  simp only [Nat.zero_add, pow_two, pow_one, pow_zero, htrace, B,
    Matrix.det_submatrix_equiv_self] at h
  apply Matrix.submatrix_injective e.surjective e.surjective
  change (A * A).submatrix e e = (A.trace • A - A.det • 1).submatrix e e
  rw [← Matrix.submatrix_mul_equiv A A e e e]
  change B * B = A.trace • B - A.det • (1 : Matrix Bool Bool ℂ).submatrix e e
  rw [Matrix.submatrix_one_equiv]
  exact h

private theorem traceless_sq (U : Matrix Bool Bool ℂ) (h : U.trace = 0) :
    U * U = (-U.det) • (1 : Matrix Bool Bool ℂ) := by
  rw [square_eq_trace_sub_det, h, zero_smul, zero_sub, neg_smul]

private theorem square_trace_one (A : Matrix Bool Bool ℂ) (h : A.trace = 1) :
    A * A = A - A.det • (1 : Matrix Bool Bool ℂ) := by
  rw [square_eq_trace_sub_det, h, one_smul]

private theorem shifted_gram (A : Matrix Bool Bool ℂ) (s : ℂ)
    (hA : A.IsHermitian)
    (hCH : A * A = A - A.det • (1 : Matrix Bool Bool ℂ))
    (hN : s * conj s = A.det) :
    (A + s • 1) * (A + s • 1)ᴴ = (1 + s + conj s) • A := by
  rw [Matrix.conjTranspose_add, hA.eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  simp only [Complex.star_def, add_mul, mul_add, Matrix.mul_smul,
    Matrix.smul_mul, mul_one, one_mul, smul_smul]
  rw [hCH, mul_comm (conj s) s, hN, add_smul, add_smul, one_smul]
  abel

private theorem scalar_intertwiner (A B : Matrix Bool Bool ℂ)
    (hA : A * A = A - A.det • (1 : Matrix Bool Bool ℂ))
    (hB : B * B = B - B.det • (1 : Matrix Bool Bool ℂ))
    (hD : A.det = B.det) :
    A * (A + B - 1) = (A + B - 1) * B := by
  rw [mul_sub, sub_mul, mul_add, add_mul, hA, hB, mul_one, one_mul, hD]
  abel

theorem rational_det (A : Matrix Bool Bool ℂ)
    (hA : ∀ i j, A i j ∈ rationalComplex) : A.det ∈ rationalComplex := by
  have hdet := Matrix.det_fin_two (A.submatrix finTwoEquiv finTwoEquiv)
  rw [Matrix.det_submatrix_equiv_self] at hdet
  rw [hdet]
  exact rationalComplex.sub_mem (rationalComplex.mul_mem (hA _ _) (hA _ _))
    (rationalComplex.mul_mem (hA _ _) (hA _ _))

private theorem norm_det_of_rational_ray (M : Matrix Bool Bool ℂ)
    (hM : M ≠ 0)
    (hQ : ∀ i j : Bool × Bool, RationalEntry
      (rankOneDensity (Function.uncurry M) i j)) :
    ∃ z, RationalEntry z ∧ (normSq z : ℂ) = (M * Mᴴ).det := by
  obtain ⟨i, j, hij⟩ : ∃ i j, M i j ≠ 0 := by
    by_contra! h
    exact hM (Matrix.ext fun i j => h i j)
  let c : ℂ := conj (M i j)
  have hc : c ≠ 0 := by simpa [c] using hij
  let N := c • M
  have hN (a b : Bool) : N a b ∈ rationalComplex := by
    have h := hQ (a,b) (i,j)
    change RationalEntry (M a b * c) at h
    change c * M a b ∈ rationalComplex
    rw [mul_comm]
    exact h
  have hsQ : M i j * c ∈ rationalComplex := hQ (i,j) (i,j)
  have hs0 : M i j * c ≠ 0 := mul_ne_zero hij hc
  have hDN := rational_det N hN
  refine ⟨N.det / (M i j * c), rationalComplex.div_mem hDN hsQ, ?_⟩
  rw [← Complex.mul_conj, map_div₀, Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def]
  have hc' : conj c = M i j := by simp [c]
  have hs : conj (M i j * c) = M i j * c := by
    rw [map_mul, hc']
    exact mul_comm _ _
  rw [hs]
  change (c • M).det / (M i j * c) * (conj ((c • M).det) / (M i j * c)) =
    M.det * conj M.det
  have hcard : Fintype.card Bool = 2 := by decide
  rw [Matrix.det_smul, hcard, map_mul, map_pow, hc']
  field_simp

private theorem scalar_sq_normalization (U : Matrix Bool Bool ℂ) (hU : U.IsHermitian)
    (ht : U.trace = 0) (h0 : U ≠ 0) :
    0 < (-U.det).re ∧ (↑(-U.det).re : ℂ) = -U.det := by
  have hp := Matrix.posSemidef_conjTranspose_mul_self U
  rw [hU.eq, traceless_sq U ht] at hp
  have hq := Complex.nonneg_iff.mp (hp.diag_nonneg (i := false))
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at hq
  have hzero : -U.det ≠ 0 := by
    intro h
    have hs : Uᴴ * U = 0 := by rw [hU.eq, traceless_sq U ht, h, zero_smul]
    exact h0 ((Matrix.conjTranspose_mul_self_eq_zero.mp hs))
  refine ⟨lt_of_le_of_ne hq.1 ?_, ?_⟩
  · intro h
    apply hzero
    apply Complex.ext <;> simp [← h, ← hq.2]
  · exact Complex.ext rfl (by simp [← hq.2])

theorem rational_product {A B : Matrix Bool Bool ℂ}
    (ha : ∀ i j, A i j ∈ rationalComplex)
    (hb : ∀ i j, B i j ∈ rationalComplex) :
    ∀ i j, (A * B) i j ∈ rationalComplex := by
  intro i j
  exact rationalComplex.sum_mem fun k _ => rationalComplex.mul_mem (ha i k) (hb k j)

private theorem explicit_rational_congruence
    (A B : Matrix Bool Bool ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (htA : A.trace = 1) (htB : B.trace = 1) (hd : A.det = B.det)
    (hAQ : ∀ i j, A i j ∈ rationalComplex) (hBQ : ∀ i j, B i j ∈ rationalComplex)
    (hU : A + B - 1 ≠ 0) :
    ∃ (U : Matrix Bool Bool ℂ) (q : ℝ), U.IsHermitian ∧ U * U = (q : ℂ) • 1 ∧
      A * U = U * B ∧ 0 < q ∧ (q : ℂ) ∈ rationalComplex ∧
      ∀ i j, U i j ∈ rationalComplex := by
  let U := A + B - 1
  have hUh : U.IsHermitian := (hA.add hB).sub Matrix.isHermitian_one
  have hUt : U.trace = 0 := by
    simp [U, trace_sub, trace_add, htA, htB]
    norm_num
  have hUQ : ∀ i j, U i j ∈ rationalComplex := by
    intro i j
    have hI : (1 : Matrix Bool Bool ℂ) i j ∈ rationalComplex := by
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    exact rationalComplex.sub_mem (rationalComplex.add_mem (hAQ i j) (hBQ i j)) hI
  obtain ⟨hq, hqC⟩ := scalar_sq_normalization U hUh hUt hU
  refine ⟨U, (-U.det).re, hUh, ?_, ?_, hq, ?_, hUQ⟩
  · rw [hqC, traceless_sq U hUt]
  · exact scalar_intertwiner A B (square_trace_one A htA) (square_trace_one B htB) hd
  · rw [hqC]
    exact rationalComplex.neg_mem (rational_det U hUQ)

private def offDiagonal (w : ℂ) : Matrix Bool Bool ℂ
  | false, false => 0
  | false, true => w
  | true, false => conj w
  | true, true => 0

private theorem opposite_rational_congruence
    (A B : Matrix Bool Bool ℂ) (hA : A.IsHermitian) (htA : A.trace = 1)
    (hAQ : ∀ i j, A i j ∈ rationalComplex) (hAB : A + B - 1 = 0) :
    ∃ (U : Matrix Bool Bool ℂ) (q : ℝ), U.IsHermitian ∧ U * U = (q : ℂ) • 1 ∧
      A * U = U * B ∧ 0 < q ∧ (q : ℂ) ∈ rationalComplex ∧
      ∀ i j, U i j ∈ rationalComplex := by
  let z := A false true
  let w := if z = 0 then 1 else Complex.I * z
  have hw : w ≠ 0 := by
    by_cases hz : z = 0
    · simp [w, hz]
    · simp [w, hz, Complex.I_ne_zero]
  have hwQ : w ∈ rationalComplex := by
    have hIQ : Complex.I ∈ rationalComplex := ⟨0, 1, by simp, by simp⟩
    by_cases hz : z = 0
    · rw [show w = 1 from ite_eq_left hz]; exact rationalComplex.one_mem
    · rw [show w = Complex.I * z from ite_eq_right hz]; exact rationalComplex.mul_mem hIQ (hAQ false true)
  let U := offDiagonal w
  have hUh : U.IsHermitian := by
    ext i j : 1
    cases i <;> cases j <;> simp [U, offDiagonal]
  have hUt : U.trace = 0 := by simp [U, Matrix.trace, offDiagonal]
  have hU0 : U ≠ 0 := by
    intro h
    exact hw (congrFun (congrFun h false) true)
  have hUQ (i j : Bool) : U i j ∈ rationalComplex := by
    cases i <;> cases j
    · exact rationalComplex.zero_mem
    · exact hwQ
    · exact (rationalConjugate ⟨w, hwQ⟩).property
    · exact rationalComplex.zero_mem
  obtain ⟨hq, hqC⟩ := scalar_sq_normalization U hUh hUt hU0
  refine ⟨U, (-U.det).re, hUh, ?_, ?_, hq, ?_, hUQ⟩
  · rw [hqC, traceless_sq U hUt]
  · have hB : B = 1 - A := by
      have hs := sub_eq_zero.mp hAB
      rwa [eq_sub_iff_add_eq, add_comm]
    rw [hB, mul_sub, mul_one, eq_sub_iff_add_eq]
    have hd : A false false + A true true = 1 := by
      simpa [Matrix.trace, Fintype.sum_bool, add_comm] using htA
    have hc : A true false = conj z := (hA.apply true false).symm
    have hx : z * conj w + w * conj z = 0 := by
      by_cases hz : z = 0
      · simp [hz]
      · rw [show w = Complex.I * z from ite_eq_right hz, map_mul, Complex.conj_I]
        ring
    ext i j : 1
    cases i <;> cases j <;>
      simp only [Matrix.add_apply, Matrix.mul_apply, Fintype.sum_bool, U, offDiagonal, hc,
        show A false true = z from rfl, mul_zero, zero_mul, add_zero, zero_add]
    · linear_combination hx
    · linear_combination w * hd
    · linear_combination conj w * hd
    · linear_combination hx
  · rw [hqC]
    exact rationalComplex.neg_mem (rational_det U hUQ)

private theorem rational_gram_pair
    (A B : Matrix Bool Bool ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (htA : A.trace = 1) (htB : B.trace = 1) (hd : A.det = B.det)
    (hAQ : ∀ i j, A i j ∈ rationalComplex) (hBQ : ∀ i j, B i j ∈ rationalComplex)
    (s : ℂ) (hsQ : s ∈ rationalComplex) (hs : 0 ≤ s.re) (hN : s * conj s = A.det) :
    ∃ (M : Matrix Bool Bool ℂ) (c : ℝ),
      0 < c ∧ (c : ℂ) ∈ rationalComplex ∧
      M * Mᴴ = (c : ℂ) • A ∧ Mᴴ * M = (c : ℂ) • B ∧
      ∀ i j, M i j ∈ rationalComplex := by
  have hU :
      ∃ (U : Matrix Bool Bool ℂ) (q : ℝ), U.IsHermitian ∧ U * U = (q : ℂ) • 1 ∧
        A * U = U * B ∧ 0 < q ∧ (q : ℂ) ∈ rationalComplex ∧
        ∀ i j, U i j ∈ rationalComplex := by
    by_cases h : A + B - 1 = 0
    · exact opposite_rational_congruence A B hA htA hAQ h
    · exact explicit_rational_congruence A B hA hB htA htB hd hAQ hBQ h
  obtain ⟨U, q, hUh, hU2, hUA, hq, hqQ, hUQ⟩ := hU
  let n : ℝ := 1 + 2 * s.re
  have hn : 0 < n := by dsimp [n]; linarith
  have hnC : (n : ℂ) = 1 + s + conj s := by
    apply Complex.ext <;> simp [n, Complex.add_re, Complex.add_im, Complex.mul_re] <;> ring
  have hnQ : (n : ℂ) ∈ rationalComplex := by
    rw [hnC]
    exact rationalComplex.add_mem (rationalComplex.add_mem rationalComplex.one_mem hsQ)
      (rationalConjugate ⟨s, hsQ⟩).property
  let V := A + s • (1 : Matrix Bool Bool ℂ)
  let M := V * U
  have hV : V * Vᴴ = (n : ℂ) • A := by
    rw [hnC]
    exact shifted_gram A s hA (square_trace_one A htA) hN
  have hV' : Vᴴ * V = (n : ℂ) • A := by
    have hc0 : (conj s) * conj (conj s) = A.det := by rw [Complex.conj_conj, mul_comm, hN]
    have hvA := shifted_gram A (conj s) hA (square_trace_one A htA) hc0
    have hvC : Vᴴ = A + (conj s) • 1 := by simp [V, hA.eq]
    rw [← hvC, Matrix.conjTranspose_conjTranspose, Complex.conj_conj] at hvA
    simpa only [hnC, add_assoc, add_comm s (conj s)] using hvA
  refine ⟨M, q*n, mul_pos hq hn, by rw [Complex.ofReal_mul]; exact rationalComplex.mul_mem hqQ hnQ,
    ?_, ?_, rational_product ?_ hUQ⟩
  · dsimp only [M]
    rw [Matrix.conjTranspose_mul, hUh.eq]
    calc
      _ = V * (U * U) * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = (q : ℂ) • (V * Vᴴ) := by rw [hU2]; simp
      _ = ((q*n : ℝ) : ℂ) • A := by rw [hV, smul_smul, Complex.ofReal_mul]
  · dsimp only [M]
    rw [Matrix.conjTranspose_mul, hUh.eq]
    calc
      _ = U * ((Vᴴ * V) * U) := by simp only [Matrix.mul_assoc]
      _ = (n : ℂ) • (U * (A * U)) := by rw [hV', Matrix.smul_mul, Matrix.mul_smul]
      _ = (n : ℂ) • ((U * U) * B) := by rw [hUA, Matrix.mul_assoc]
      _ = ((q*n : ℝ) : ℂ) • B := by
        rw [hU2, Matrix.smul_mul, one_mul, smul_smul, Complex.ofReal_mul, mul_comm]
  · intro i j
    have hI : (1 : Matrix Bool Bool ℂ) i j ∈ rationalComplex := by
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    exact rationalComplex.add_mem (hAQ i j) (rationalComplex.mul_mem hsQ hI)

/-- Two qubit marginals admit a rational pure joint density exactly when their trace,
positivity, rationality, common determinant, and Gaussian norm conditions hold. -/
theorem rational_qubit_purity_iff (L R : Matrix Bool Bool ℂ) :
    (∃ M : Matrix Bool Bool ℂ, L.trace = 1 ∧ M * Mᴴ = L ∧ (Mᴴ * M)ᵀ = R ∧
      ∀ i j, RationalEntry (rankOneDensity (Function.uncurry M) i j)) ↔
      L.PosSemidef ∧ R.PosSemidef ∧ L.trace = 1 ∧ R.trace = 1 ∧ L.det = R.det ∧
        (∀ i j, RationalEntry (L i j)) ∧ (∀ i j, RationalEntry (R i j)) ∧
        ∃ s : ℂ, RationalEntry s ∧ (normSq s : ℂ) = L.det := by
  constructor
  · rintro ⟨M, ht, rfl, rfl, hQ⟩
    have hM : M ≠ 0 := by
      intro h
      simp [h] at ht
    have hR : ((Mᴴ * M)ᵀ).PosSemidef := (Matrix.posSemidef_conjTranspose_mul_self M).transpose
    refine ⟨Matrix.posSemidef_self_mul_conjTranspose M, hR, ht, ?_, ?_, ?_, ?_,
      norm_det_of_rational_ray M hM hQ⟩
    · rw [Matrix.trace_transpose, Matrix.trace_mul_comm, ht]
    · rw [Matrix.det_transpose, Matrix.det_mul, Matrix.det_mul, mul_comm]
    · intro i j
      change (M * Mᴴ) i j ∈ rationalComplex
      rw [Matrix.mul_apply]
      exact rationalComplex.sum_mem fun k _ => hQ (i, k) (j, k)
    · intro i j
      change (Mᴴ * M) j i ∈ rationalComplex
      rw [Matrix.mul_apply]
      refine rationalComplex.sum_mem fun k _ => ?_
      rw [mul_comm]
      exact hQ (k, i) (k, j)
  · rintro ⟨hL, hR, htL, htR, hd, hLQ, hRQ, s, hsQ, hsN⟩
    have hs : ∃ t : ℂ, t ∈ rationalComplex ∧ 0 ≤ t.re ∧ t * conj t = L.det := by
      by_cases h : 0 ≤ s.re
      · exact ⟨s, hsQ, h, by rw [Complex.mul_conj, hsN]⟩
      · refine ⟨-s, rationalComplex.neg_mem hsQ, ?_, ?_⟩
        · rw [Complex.neg_re]
          linarith
        · rw [Complex.mul_conj, Complex.normSq_neg, hsN]
    obtain ⟨s', hsQ', hsre, hsN'⟩ := hs
    have hRtQ : ∀ i j, Rᵀ i j ∈ rationalComplex := fun i j => hRQ j i
    obtain ⟨M, c, hc, hcQ, hML, hMR, hMQ⟩ :=
      rational_gram_pair L Rᵀ hL.isHermitian hR.isHermitian.transpose htL
        (by rw [Matrix.trace_transpose, htR]) (by rwa [Matrix.det_transpose]) hLQ hRtQ
        s' hsQ' hsre hsN'
    let t : ℂ := (↑((Real.sqrt c)⁻¹) : ℂ)
    have ht : t * conj t = (c : ℂ)⁻¹ := by
      dsimp [t]
      rw [Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hc.le,
        Complex.ofReal_inv]
    let N := t • M
    have ht' : conj t * t = (c : ℂ)⁻¹ := by rw [mul_comm, ht]
    have hNL : N * Nᴴ = L := by
      rw [show N = t • M from rfl, Matrix.conjTranspose_smul, Complex.star_def,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul, ht, hML, smul_smul,
        inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hc.ne'), one_smul]
    have hNR : Nᴴ * N = Rᵀ := by
      rw [show N = t • M from rfl, Matrix.conjTranspose_smul, Complex.star_def,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul, ht', hMR, smul_smul,
        inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hc.ne'), one_smul]
    refine ⟨N, htL, hNL, by rw [hNR, transpose_transpose], ?_⟩
    rintro ⟨i, j⟩ ⟨a, b⟩
    change RationalEntry ((t * M i j) * conj (t * M a b))
    rw [map_mul, show (t * M i j) * (conj t * conj (M a b)) =
        (t * conj t) * (M i j * conj (M a b)) by ring, ht]
    exact rationalComplex.mul_mem (rationalComplex.inv_mem hcQ) (rationalComplex.mul_mem
      (hMQ i j) (rationalConjugate ⟨M a b, hMQ a b⟩).property)

end D5.S3.Quantum.Entanglement.Marginals.RationalQubitPurity
