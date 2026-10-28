/- GID: D5/S3/Quantum/Entanglement/TwoQubitBinegativityLowerBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/TwoQubitBinegativityLowerBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The sharp lower bound on two-qubit binegativity at fixed negativity. -/

import D5.S3.Quantum.Entanglement.TwoQubitBinegativityUpperBoundRefutation
import D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation
import D5.S3.Quantum.Entanglement.SeparableNumericalRangeRatio
import D5.S3.Quantum.PureState.PureStateHandshake

/-! The fixed-negativity boundary for the spectral binegativity of two-qubit states. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.TwoQubitBinegativityLowerBound

open Matrix
open scoped MatrixOrder ComplexOrder
open D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation
  (partialTransposeB IsDensity)
open D5.S3.Quantum.Entanglement.TwoQubitBinegativityUpperBoundRefutation (binegativity vec4)
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation
  (partialTransposeB_kronecker_conj)

/-- Girard–Gour's fixed-negativity lower bound, arXiv:1701.02724, Eq. (8). -/
def claim : Prop :=
  ∀ σ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ, IsDensity σ →
    let ν := 2 * ((partialTransposeB σ)⁻).trace.re
    let c := Real.sqrt (2 * ν * (ν + 1)) - ν
    ν / 2 * (1 + c / Real.sqrt ((1 - c) ^ 2 + c ^ 2)) ≤ binegativity σ

/-- The principal-minor constraint forces the sharp lower bound on the Schmidt product. -/
private theorem scalar_bound (ν x s : ℝ) (hν : 0 < ν) (hx : 0 ≤ x)
    (hx1 : x ≤ 1) (hs : 0 ≤ s)
    (hminor : ν * (2 * x + ν) ≤ (1 - x) ^ 2)
    (hschmidt : ν * (2 * x + ν) ≤ s ^ 2 * (x + ν) ^ 2) :
    let c := Real.sqrt (2 * ν * (ν + 1)) - ν
    c / Real.sqrt ((1 - c) ^ 2 + c ^ 2) ≤ s := by
  dsimp only
  let r := Real.sqrt (2 * ν * (ν + 1))
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = 2 * ν * (ν + 1) := Real.sq_sqrt (by positivity)
  have hν1 : ν ≤ 1 := by nlinarith [sq_nonneg x, mul_nonneg hν.le hx]
  have hνr : ν < r := by nlinarith
  have hr1 : r ≤ 1 + ν := by nlinarith
  have hxq : x ≤ 1 + ν - r := by
    have hsq : r ^ 2 ≤ (1 + ν - x) ^ 2 := by nlinarith
    have hright : 0 ≤ 1 + ν - x := by linarith
    nlinarith
  have hden : Real.sqrt ((1 - (r - ν)) ^ 2 + (r - ν) ^ 2) = 1 + 2 * ν - r := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by linarith)).mpr
    nlinarith only [hrsq]
  change (r - ν) / Real.sqrt ((1 - (r - ν)) ^ 2 + (r - ν) ^ 2) ≤ s
  rw [hden]
  have hD : 0 < 1 + 2 * ν - r := by linarith
  have hX : 0 < x + ν := by positivity
  have hfrac : x / (x + ν) ≤ (1 + ν - r) / (1 + 2 * ν - r) := by
    apply (div_le_div_iff₀ hX hD).mpr
    nlinarith
  have hfrac0 : 0 ≤ x / (x + ν) := div_nonneg hx hX.le
  have hfrac1 : 0 ≤ (1 + ν - r) / (1 + 2 * ν - r) :=
    div_nonneg (by linarith) hD.le
  have hfrac_sq := (sq_le_sq₀ hfrac0 hfrac1).mpr hfrac
  have hleft : 1 - (x / (x + ν)) ^ 2 ≤ s ^ 2 := by
    apply (le_of_mul_le_mul_right ?_ (sq_pos_of_pos hX))
    calc
      (1 - (x / (x + ν)) ^ 2) * (x + ν) ^ 2 = ν * (2 * x + ν) := by
        field_simp [ne_of_gt hX]
        ring
      _ ≤ s ^ 2 * (x + ν) ^ 2 := hschmidt
  have hright : ((r - ν) / (1 + 2 * ν - r)) ^ 2 =
      1 - ((1 + ν - r) / (1 + 2 * ν - r)) ^ 2 := by
    rw [eq_sub_iff_add_eq, div_pow, div_pow, ← add_div]
    apply (div_eq_one_iff_eq (pow_ne_zero 2 (ne_of_gt hD))).mpr
    nlinarith only [hrsq]
  have hquot0 : 0 ≤ (r - ν) / (1 + 2 * ν - r) :=
    div_nonneg (by linarith) hD.le
  apply (sq_le_sq₀ hquot0 hs).mp
  rw [hright]
  linarith

private theorem nonnegative_trace_negPart
    (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : 0 ≤ (A⁻).trace.re :=
  (RCLike.nonneg_iff.mp
    (Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg A)).trace_nonneg).1

/-- A positive partial transpose gives the zero endpoint of the bound. -/
private theorem zero_case (σ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hzero : 2 * ((partialTransposeB σ)⁻).trace.re = 0) :
    let ν := 2 * ((partialTransposeB σ)⁻).trace.re
    let c := Real.sqrt (2 * ν * (ν + 1)) - ν
    ν / 2 * (1 + c / Real.sqrt ((1 - c) ^ 2 + c ^ 2)) ≤ binegativity σ := by
  dsimp only
  rw [hzero]
  simp only [zero_mul, zero_div, mul_zero]
  unfold binegativity
  have hfirst := nonnegative_trace_negPart (partialTransposeB σ)
  have hsecond := nonnegative_trace_negPart (partialTransposeB ((partialTransposeB σ)⁻))
  linarith

/-- The negative partial-transpose trace of a vector in Schmidt coordinates. -/
private theorem schmidt_negative_trace (l α β : ℝ) (hl : 0 ≤ l)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    ((partialTransposeB ((l : ℂ) • rankOneDensity (vec4 α 0 0 β)))⁻).trace.re =
      l * α * β := by
  let P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
    ((l * α ^ 2 : ℝ) : ℂ) • rankOneDensity (vec4 1 0 0 0) +
    ((l * β ^ 2 : ℝ) : ℂ) • rankOneDensity (vec4 0 0 0 1) +
    ((l * α * β / 2 : ℝ) : ℂ) • rankOneDensity (vec4 0 1 1 0)
  let Q : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
    ((l * α * β / 2 : ℝ) : ℂ) • rankOneDensity (vec4 0 1 (-1) 0)
  have hpsd (v : Fin 2 × Fin 2 → ℂ) (r : ℝ) (hr : 0 ≤ r) :
      ((r : ℂ) • rankOneDensity v).PosSemidef := by
    exact (posSemidef_vecMulVec_self_star v).smul (Complex.zero_le_real.mpr hr)
  have hP : 0 ≤ P := by
    apply Matrix.nonneg_iff_posSemidef.mpr
    exact ((hpsd _ _ (mul_nonneg hl (sq_nonneg α))).add
      (hpsd _ _ (mul_nonneg hl (sq_nonneg β)))).add
        (hpsd _ _ (by positivity))
  have hQ : 0 ≤ Q := by
    apply Matrix.nonneg_iff_posSemidef.mpr
    exact hpsd _ _ (by positivity)
  have hsplit : partialTransposeB ((l : ℂ) • rankOneDensity (vec4 α 0 0 β)) = P - Q := by
    ext ⟨i, j⟩ ⟨k, l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [partialTransposeB.eq_1, P, Q, rankOneDensity, vec4, vecMulVec_apply,
        Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_div] <;> ring
    all_goals simp
  have horth : P * Q = 0 := by
    ext ⟨i, j⟩ ⟨k, l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [P, Q, rankOneDensity, vec4, vecMulVec_apply, Matrix.mul_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two]
  rw [(CFC.posPart_negPart_unique hsplit horth hP hQ).2]
  simp [Q, rankOneDensity, vec4, vecMulVec_apply, Matrix.trace,
    Fintype.sum_prod_type, Fin.sum_univ_two, Complex.mul_re]

/-- Positivity and the negative-eigenvector equations in Schmidt coordinates. -/
private theorem schmidt_constraints
    (τ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hτ : IsDensity τ)
    (l α β : ℝ) (hl : 0 < l) (hα : 0 < α) (hβ : 0 < β)
    (hnorm : α ^ 2 + β ^ 2 = 1)
    (heigen : partialTransposeB τ *ᵥ vec4 α 0 0 β =
      (-l : ℂ) • vec4 α 0 0 β) :
    ∃ x : ℝ, 0 ≤ x ∧ x ≤ 1 ∧
      (2 * l) * (2 * x + 2 * l) ≤ (1 - x) ^ 2 ∧
      (2 * l) * (2 * x + 2 * l) ≤ (2 * α * β) ^ 2 * (x + 2 * l) ^ 2 := by
  let a := (τ (0, 0) (0, 0)).re
  let b := (τ (0, 1) (0, 1)).re
  let e := (τ (1, 0) (1, 0)).re
  let d := (τ (1, 1) (1, 1)).re
  let u := -(τ (0, 1) (1, 0)).re
  have ha : 0 ≤ a := (Complex.nonneg_iff.mp hτ.1.diag_nonneg).1
  have hb : 0 ≤ b := (Complex.nonneg_iff.mp hτ.1.diag_nonneg).1
  have he : 0 ≤ e := (Complex.nonneg_iff.mp hτ.1.diag_nonneg).1
  have hd : 0 ≤ d := (Complex.nonneg_iff.mp hτ.1.diag_nonneg).1
  have htrace : a + b + e + d = 1 := by
    have ht := congrArg Complex.re hτ.2
    simpa [Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.diag, a, b, e, d, add_assoc] using ht
  have hsym : (τ (1, 0) (0, 1)).re = (τ (0, 1) (1, 0)).re := by
    have ht := congrArg Complex.re (hτ.1.isHermitian.apply (0, 1) (1, 0))
    simpa using ht
  have hA : (a + l) * α = u * β := by
    have ht := congrArg Complex.re (congrFun heigen (0, 0))
    simp [partialTransposeB.eq_1, Matrix.mulVec, dotProduct, vec4,
      Fintype.sum_prod_type, Fin.sum_univ_two, Complex.mul_re] at ht
    dsimp [a, u]
    nlinarith only [ht]
  have hD : (d + l) * β = u * α := by
    have ht := congrArg Complex.re (congrFun heigen (1, 1))
    simp [partialTransposeB.eq_1, Matrix.mulVec, dotProduct, vec4,
      Fintype.sum_prod_type, Fin.sum_univ_two, hsym] at ht
    dsimp [d, u]
    nlinarith only [ht]
  have hu : 0 < u := by nlinarith [mul_pos (by linarith : 0 < a + l) hα]
  have hupper : 2 * u ≤ 1 - (a + d) := by
    have ht := (Complex.nonneg_iff.mp
      (hτ.1.dotProduct_mulVec_nonneg (vec4 0 1 1 0))).1
    simp [Matrix.mulVec, dotProduct, vec4, Fintype.sum_prod_type, Fin.sum_univ_two,
      hsym] at ht
    dsimp [u, a, b, e, d] at *
    linarith
  have hprod : u ^ 2 = (a + l) * (d + l) := by
    have hz : ((a + l) * (d + l) - u ^ 2) * (α * β) = 0 := by
      calc
        _ = ((a + l) * α) * ((d + l) * β) - (u * β) * (u * α) := by ring
        _ = 0 := by rw [hA, hD]; ring
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (ne_of_gt (mul_pos hα hβ)))).symm
  have hsum : (2 * α * β) * (a + d + 2 * l) = 2 * u := by
    calc
      _ = 2 * (((a + l) * α) * β + ((d + l) * β) * α) := by ring
      _ = 2 * u * (α ^ 2 + β ^ 2) := by rw [hA, hD]; ring
      _ = 2 * u := by rw [hnorm]; ring
  have hsq : (2 * α * β) ^ 2 * (a + d + 2 * l) ^ 2 = 4 * u ^ 2 := by
    nlinarith only [congrArg (fun t : ℝ => t ^ 2) hsum]
  refine ⟨a + d, by positivity, by linarith, ?_, ?_⟩
  · nlinarith [mul_nonneg ha hd]
  · nlinarith [mul_nonneg ha hd]

/-- Partial transposition is nonnegative on product vectors. -/
private theorem product_nonnegative
    (σ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hσ : σ.PosSemidef)
    (a b : Fin 2 → ℂ) :
    0 ≤ (star (fun p : Fin 2 × Fin 2 => a p.1 * b p.2) ⬝ᵥ
      (partialTransposeB σ *ᵥ (fun p => a p.1 * b p.2))).re := by
  have heq : star (fun p : Fin 2 × Fin 2 => a p.1 * b p.2) ⬝ᵥ
      (partialTransposeB σ *ᵥ (fun p => a p.1 * b p.2)) =
      star (fun p : Fin 2 × Fin 2 => a p.1 * star (b p.2)) ⬝ᵥ
        (σ *ᵥ (fun p => a p.1 * star (b p.2))) := by
    simp [partialTransposeB.eq_1, dotProduct, Matrix.mulVec, Fintype.sum_prod_type,
      Fin.sum_univ_two]
    ring
  rw [heq]
  exact hσ.re_dotProduct_nonneg _

/-- A complex determinant pencil supplies a product vector in any two-vector span. -/
private theorem product_in_span (v w : Fin 2 × Fin 2 → ℂ) (hw : w ≠ 0)
    (hv : ∀ t : ℂ, v + t • w ≠ 0) :
    ∃ (a b : Fin 2 → ℂ), (fun p : Fin 2 × Fin 2 => a p.1 * b p.2) ≠ 0 ∧
      ((fun p : Fin 2 × Fin 2 => a p.1 * b p.2) = w ∨
        ∃ t : ℂ, (fun p : Fin 2 × Fin 2 => a p.1 * b p.2) = v + t • w) := by
  by_cases hd : w (0, 0) * w (1, 1) - w (0, 1) * w (1, 0) = 0
  · obtain ⟨a, b, hab⟩ :=
      SeparableNumericalRangeRatio.zero_determinant_factorization w (sub_eq_zero.mp hd)
    have heq : w = fun p => a p.1 * b p.2 := funext fun p => hab p.1 p.2
    exact ⟨a, b, heq ▸ hw, Or.inl heq.symm⟩
  · let p : Polynomial ℂ :=
      Polynomial.C (w (0, 0) * w (1, 1) - w (0, 1) * w (1, 0)) * Polynomial.X ^ 2 +
      Polynomial.C (v (0, 0) * w (1, 1) + w (0, 0) * v (1, 1) -
        v (0, 1) * w (1, 0) - w (0, 1) * v (1, 0)) * Polynomial.X +
      Polynomial.C (v (0, 0) * v (1, 1) - v (0, 1) * v (1, 0))
    have hp : p.degree ≠ 0 := by
      rw [Polynomial.degree_quadratic hd]
      norm_num
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_root p hp
    have hsing : (v + t • w) (0, 0) * (v + t • w) (1, 1) -
        (v + t • w) (0, 1) * (v + t • w) (1, 0) = 0 := by
      have hroot : p.eval t = 0 := ht
      simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X] at hroot
      change (v (0, 0) + t * w (0, 0)) * (v (1, 1) + t * w (1, 1)) -
        (v (0, 1) + t * w (0, 1)) * (v (1, 0) + t * w (1, 0)) = 0
      linear_combination hroot
    obtain ⟨a, b, hab⟩ :=
      SeparableNumericalRangeRatio.zero_determinant_factorization (v + t • w)
        (sub_eq_zero.mp hsing)
    have heq : v + t • w = fun p => a p.1 * b p.2 := funext fun p => hab p.1 p.2
    exact ⟨a, b, heq ▸ hv t, Or.inr ⟨t, heq.symm⟩⟩

/-- Two distinct orthonormal eigenvectors cannot both have negative eigenvalues. -/
private theorem negative_eigenvalue_unique
    (σ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hσ : σ.PosSemidef)
    (hA : (partialTransposeB σ).IsHermitian) (i j : Fin 2 × Fin 2)
    (hi : hA.eigenvalues i < 0) (hj : hA.eigenvalues j < 0) : i = j := by
  by_contra hij
  let v : Fin 2 × Fin 2 → ℂ := hA.eigenvectorBasis i
  let w : Fin 2 × Fin 2 → ℂ := hA.eigenvectorBasis j
  have hinner (k l : Fin 2 × Fin 2) :
      star (hA.eigenvectorBasis k : Fin 2 × Fin 2 → ℂ) ⬝ᵥ
        (hA.eigenvectorBasis l : Fin 2 × Fin 2 → ℂ) = if k = l then 1 else 0 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
    exact orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal k l
  have hvv : star v ⬝ᵥ v = 1 := by simpa [v] using hinner i i
  have hww : star w ⬝ᵥ w = 1 := by simpa [w] using hinner j j
  have hvw : star v ⬝ᵥ w = 0 := by simpa [v, w, hij] using hinner i j
  have hwv : star w ⬝ᵥ v = 0 := by simpa [v, w, Ne.symm hij] using hinner j i
  have hw : w ≠ 0 := by intro hz; simp [hz] at hww
  have hv (t : ℂ) : v + t • w ≠ 0 := by
    intro hz
    have ht := congrArg (fun z => star v ⬝ᵥ z) hz
    simp [dotProduct_add, dotProduct_smul, hvv, hvw] at ht
  obtain ⟨a, b, hab, hspan⟩ := product_in_span v w hw hv
  have hnonneg := product_nonnegative σ hσ a b
  rcases hspan with heq | ⟨t, heq⟩
  · rw [heq] at hnonneg
    have heig : partialTransposeB σ *ᵥ w = (hA.eigenvalues j : ℂ) • w := by
      funext k
      simpa [w, Pi.smul_apply, Complex.real_smul, smul_eq_mul] using
        congrFun (hA.mulVec_eigenvectorBasis j) k
    rw [heig, dotProduct_smul, hww] at hnonneg
    exact (not_le_of_gt hj) (by simpa [smul_eq_mul] using hnonneg)
  · rw [heq] at hnonneg
    have heigv : partialTransposeB σ *ᵥ v = (hA.eigenvalues i : ℂ) • v := by
      funext k
      simpa [v, Pi.smul_apply, Complex.real_smul, smul_eq_mul] using
        congrFun (hA.mulVec_eigenvectorBasis i) k
    have heigw : partialTransposeB σ *ᵥ w = (hA.eigenvalues j : ℂ) • w := by
      funext k
      simpa [w, Pi.smul_apply, Complex.real_smul, smul_eq_mul] using
        congrFun (hA.mulVec_eigenvectorBasis j) k
    have hform : star (v + t • w) ⬝ᵥ (partialTransposeB σ *ᵥ (v + t • w)) =
        (hA.eigenvalues i : ℂ) + (hA.eigenvalues j : ℂ) * (star t * t) := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, heigv, heigw]
      simp [star_add, star_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
        smul_dotProduct, hvv, hww, hvw, hwv, smul_eq_mul]
      ring
    have hstar : star t * t = (Complex.normSq t : ℂ) := by
      exact (Complex.normSq_eq_conj_mul_self (z := t)).symm
    rw [hform, hstar] at hnonneg
    simp [Complex.mul_re] at hnonneg
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hj.le (Complex.normSq_nonneg t)]

/-- Spectral negative parts commute with unitary conjugation. -/
private theorem negPart_conjugate
    (A U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hA : A.IsHermitian) (hU : Uᴴ * U = 1) :
    (U * A * Uᴴ)⁻ = U * A⁻ * Uᴴ := by
  have hsplit : U * A * Uᴴ = U * A⁺ * Uᴴ - U * A⁻ * Uᴴ := by
    rw [← sub_mul, ← mul_sub, CFC.posPart_sub_negPart A hA]
  have horth : (U * A⁺ * Uᴴ) * (U * A⁻ * Uᴴ) = 0 := by
    calc
      _ = U * A⁺ * (Uᴴ * U) * A⁻ * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = U * (A⁺ * A⁻) * Uᴴ := by
        rw [hU]
        simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 0 := by rw [CFC.posPart_mul_negPart]; simp
  exact (CFC.posPart_negPart_unique hsplit horth
    ((Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg A)).mul_mul_conjTranspose_same U).nonneg
    ((Matrix.nonneg_iff_posSemidef.mp
      (CFC.negPart_nonneg A)).mul_mul_conjTranspose_same U).nonneg).2

private theorem trace_conjugate (A U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hU : Uᴴ * U = 1) : (U * A * Uᴴ).trace = A.trace := by
  rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]

/-- Both traces defining binegativity are invariant under local unitaries. -/
private theorem local_invariance
    (σ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hσ : σ.IsHermitian)
    (U V : Matrix.unitaryGroup (Fin 2) ℂ) :
    let K := Matrix.kronecker (U : Matrix (Fin 2) (Fin 2) ℂ)
      (V : Matrix (Fin 2) (Fin 2) ℂ)
    ((partialTransposeB (K * σ * Kᴴ))⁻).trace.re = ((partialTransposeB σ)⁻).trace.re ∧
      binegativity (K * σ * Kᴴ) = binegativity σ := by
  let K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
    Matrix.kronecker (U : Matrix (Fin 2) (Fin 2) ℂ) (V : Matrix (Fin 2) (Fin 2) ℂ)
  let L : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
    Matrix.kronecker (U : Matrix (Fin 2) (Fin 2) ℂ)
      ((V : Matrix (Fin 2) (Fin 2) ℂ).map star)
  have hK : Kᴴ * K = 1 := by
    exact Matrix.mem_unitaryGroup_iff'.mp (Matrix.kronecker_mem_unitary U.property V.property)
  have hL : Lᴴ * L = 1 := by
    exact Matrix.mem_unitaryGroup_iff'.mp (Matrix.kronecker_mem_unitary U.property
      (Matrix.map_star_mem_unitaryGroup_iff.mpr V.property))
  have hpt : partialTransposeB (K * σ * Kᴴ) = L * partialTransposeB σ * Lᴴ :=
    partialTransposeB_kronecker_conj σ U V
  have hneg : (partialTransposeB (K * σ * Kᴴ))⁻ = L * (partialTransposeB σ)⁻ * Lᴴ := by
    rw [hpt, negPart_conjugate _ L (by ext ⟨i, j⟩ ⟨k, l⟩; exact hσ.apply (i, l) (k, j)) hL]
  have hptneg : partialTransposeB (L * (partialTransposeB σ)⁻ * Lᴴ) =
      K * partialTransposeB (partialTransposeB σ)⁻ * Kᴴ := by
    have hbar : ((V : Matrix (Fin 2) (Fin 2) ℂ).map star).map star =
        (V : Matrix (Fin 2) (Fin 2) ℂ) := by ext i j; simp
    simpa only [L, K, Matrix.kronecker, hbar] using
      partialTransposeB_kronecker_conj (partialTransposeB σ)⁻ U
        ((V : Matrix (Fin 2) (Fin 2) ℂ).map star)
  have hdouble : (partialTransposeB (L * (partialTransposeB σ)⁻ * Lᴴ))⁻ =
      K * (partialTransposeB (partialTransposeB σ)⁻)⁻ * Kᴴ := by
    rw [hptneg, negPart_conjugate _ K
      (by
        ext ⟨i, j⟩ ⟨k, l⟩
        exact (Matrix.nonneg_iff_posSemidef.mp
          (CFC.negPart_nonneg (partialTransposeB σ))).isHermitian.apply (i, l) (k, j)) hK]
  change ((partialTransposeB (K * σ * Kᴴ))⁻).trace.re = _ ∧
    binegativity (K * σ * Kᴴ) = _
  constructor
  · rw [hneg, trace_conjugate _ L hL]
  · unfold binegativity
    rw [hneg, hdouble, trace_conjugate _ L hL, trace_conjugate _ K hK]

/-- The negative component of an entangled two-qubit partial transpose has rank one. -/
private theorem negative_component
    (σ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hσ : IsDensity σ)
    (hν : 0 < 2 * ((partialTransposeB σ)⁻).trace.re) :
    ∃ (l : ℝ) (v : Fin 2 × Fin 2 → ℂ), 0 < l ∧ star v ⬝ᵥ v = 1 ∧
      partialTransposeB σ *ᵥ v = (-l : ℂ) • v ∧
      (partialTransposeB σ)⁻ = (l : ℂ) • rankOneDensity v ∧
      ((partialTransposeB σ)⁻).trace.re = l := by
  classical
  let hA : (partialTransposeB σ).IsHermitian := by
    ext ⟨i, j⟩ ⟨k, l⟩
    exact hσ.1.isHermitian.apply (i, l) (k, j)
  obtain ⟨i, hi⟩ : ∃ i, hA.eigenvalues i < 0 := by
    by_contra hall
    push Not at hall
    have hpositive := hA.posSemidef_iff_eigenvalues_nonneg.mpr hall
    have hz := (CFC.negPart_eq_zero_iff (partialTransposeB σ) hA).mpr hpositive.nonneg
    simp [hz] at hν
  let v : Fin 2 × Fin 2 → ℂ := hA.eigenvectorBasis i
  have hv : star v ⬝ᵥ v = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
    simp
  have hparts (j : Fin 2 × Fin 2) : (hA.eigenvalues j)⁻ =
      if j = i then -hA.eigenvalues i else 0 := by
    by_cases hji : j = i
    · subst j
      simp [negPart_eq_neg.mpr hi.le]
    · have hj : 0 ≤ hA.eigenvalues j := by
        by_contra hn
        exact hji (negative_eigenvalue_unique σ hσ.1 hA j i (lt_of_not_ge hn) hi)
      simp [hji, negPart_eq_zero.mpr hj]
  have hneg : (partialTransposeB σ)⁻ = (-hA.eigenvalues i : ℂ) • rankOneDensity v := by
    rw [CFC.negPart_def, cfcₙ_eq_cfc, hA.cfc_eq]
    ext a b
    simp [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.mul_apply,
      Matrix.diagonal, Function.comp_def, hparts, apply_ite, ite_mul,
      rankOneDensity, Matrix.vecMulVec_apply, v, mul_assoc]
    ring
  refine ⟨-hA.eigenvalues i, v, by linarith, hv, ?_, ?_, ?_⟩
  · funext k
    simpa [v, Pi.smul_apply, Complex.real_smul, smul_eq_mul] using
      congrFun (hA.mulVec_eigenvectorBasis i) k
  · simpa only [Complex.ofReal_neg] using hneg
  · rw [hneg, Matrix.trace_smul, rankOneDensity, Matrix.trace_vecMulVec, dotProduct_comm, hv]
    simp [smul_eq_mul]

/-- The negative component can be transported to a unit Schmidt vector. -/
private theorem schmidt_reduction
    (σ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hσ : IsDensity σ)
    (hν : 0 < 2 * ((partialTransposeB σ)⁻).trace.re) :
    ∃ (τ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (l α β : ℝ),
      IsDensity τ ∧ 0 < l ∧ 0 < α ∧ 0 < β ∧ α ^ 2 + β ^ 2 = 1 ∧
      partialTransposeB τ *ᵥ vec4 α 0 0 β = (-l : ℂ) • vec4 α 0 0 β ∧
      (partialTransposeB τ)⁻ = (l : ℂ) • rankOneDensity (vec4 α 0 0 β) ∧
      ((partialTransposeB σ)⁻).trace.re = l ∧ binegativity σ = binegativity τ := by
  obtain ⟨l, v, hl, hv, heig, hneg, htrace⟩ := negative_component σ hσ hν
  let A : Matrix (Fin 2) (Fin 2) ℂ := fun i j => v (i, j)
  let H : (Aᴴ * A).IsHermitian := by
    simpa using Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose
  obtain ⟨U, W, hsvd⟩ :=
    D5.S3.Quantum.Foundation.FiniteTraceDistance.exists_svd_sqrt_eigenvalues A
  let α := Real.sqrt (H.eigenvalues 0)
  let β := Real.sqrt (H.eigenvalues 1)
  let ψ := vec4 (α : ℂ) 0 0 β
  let K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
    Matrix.kronecker (U : Matrix (Fin 2) (Fin 2) ℂ) (W : Matrix (Fin 2) (Fin 2) ℂ)
  let L : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
    Matrix.kronecker (U : Matrix (Fin 2) (Fin 2) ℂ)
      ((W : Matrix (Fin 2) (Fin 2) ℂ).map star)
  have hKmem : K ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ :=
    Matrix.kronecker_mem_unitary U.property W.property
  have hLmem : L ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ :=
    Matrix.kronecker_mem_unitary U.property
      (Matrix.map_star_mem_unitaryGroup_iff.mpr W.property)
  have hKright : K * Kᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hKmem
  have hLleft : Lᴴ * L = 1 := Matrix.mem_unitaryGroup_iff'.mp hLmem
  have hLright : L * Lᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hLmem
  have hdiag : (fun i => (Real.sqrt (H.eigenvalues i) : ℂ)) = ![(α : ℂ), (β : ℂ)] := by
    funext i
    fin_cases i <;> rfl
  change A = (U : Matrix (Fin 2) (Fin 2) ℂ) *
    diagonal (fun i => (Real.sqrt (H.eigenvalues i) : ℂ)) *
    (W : Matrix (Fin 2) (Fin 2) ℂ)ᴴ at hsvd
  rw [hdiag] at hsvd
  have hvsch : v = L *ᵥ ψ := by
    funext ⟨i, j⟩
    have ht := congrFun (congrFun hsvd i) j
    simp [Matrix.mul_apply, Matrix.diagonal, Fin.sum_univ_two,
      Matrix.conjTranspose_apply] at ht
    change v (i, j) = _ at ht
    simp [L, ψ, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_two, vec4]
    linear_combination ht
  have hLv : Lᴴ *ᵥ v = ψ := by
    rw [hvsch, Matrix.mulVec_mulVec, hLleft, Matrix.one_mulVec]
  have hψnorm : star ψ ⬝ᵥ ψ = 1 := by
    calc
      _ = star (L *ᵥ ψ) ⬝ᵥ (L *ᵥ ψ) := by
        rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
          hLleft, Matrix.one_mulVec]
      _ = 1 := by rw [← hvsch]; exact hv
  have hn : α ^ 2 + β ^ 2 = 1 := by
    have ht := congrArg Complex.re hψnorm
    simp [ψ, vec4, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two] at ht
    nlinarith only [ht]
  let τ := Kᴴ * σ * K
  have hτ : IsDensity τ := by
    constructor
    · simpa only [τ, Matrix.conjTranspose_conjTranspose] using
        hσ.1.mul_mul_conjTranspose_same Kᴴ
    · simpa only [τ, Matrix.conjTranspose_conjTranspose, hσ.2] using
        trace_conjugate σ Kᴴ (by simpa using hKright)
  have hbar : ((W : Matrix (Fin 2) (Fin 2) ℂ)ᴴ).map star =
      (((W : Matrix (Fin 2) (Fin 2) ℂ).map star)ᴴ) := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  have hpt : partialTransposeB τ = Lᴴ * partialTransposeB σ * L := by
    have ht := partialTransposeB_kronecker_conj σ
      ((U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) ((W : Matrix (Fin 2) (Fin 2) ℂ)ᴴ)
    simpa only [τ, K, L, Matrix.kronecker, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_conjTranspose, hbar] using ht
  have hψeig : partialTransposeB τ *ᵥ ψ = (-l : ℂ) • ψ := by
    rw [hpt, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hvsch,
      heig, Matrix.mulVec_smul, hLv]
  have hrow : star v ᵥ* L = star ψ := by
    have ht := Matrix.vecMul_conjTranspose Lᴴ (star v)
    simpa only [Matrix.conjTranspose_conjTranspose, star_star, hLv] using ht
  have houter : Lᴴ * rankOneDensity v * L = rankOneDensity ψ := by
    rw [rankOneDensity, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hLv, hrow,
      rankOneDensity]
  have hτneg : (partialTransposeB τ)⁻ = (l : ℂ) • rankOneDensity ψ := by
    have ht := negPart_conjugate (partialTransposeB σ) Lᴴ
      (by ext ⟨i, j⟩ ⟨k, l⟩; exact hσ.1.isHermitian.apply (i, l) (k, j)) (by simpa using hLright)
    simp only [Matrix.conjTranspose_conjTranspose] at ht
    rw [hpt, ht, hneg, Matrix.mul_smul, Matrix.smul_mul, houter]
  have hbineg : binegativity σ = binegativity τ := by
    have ht := (local_invariance σ hσ.1.isHermitian (star U) (star W)).2
    simpa only [τ, K, Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.kronecker,
      Matrix.conjTranspose_kronecker, Matrix.conjTranspose_conjTranspose] using ht.symm
  have hα : 0 ≤ α := Real.sqrt_nonneg _
  have hβ : 0 ≤ β := Real.sqrt_nonneg _
  have hαpos : 0 < α := by
    by_contra h
    have hz : α = 0 := le_antisymm (le_of_not_gt h) hα
    have hb : 0 < β := by nlinarith only [hn, hβ, hz]
    have ht := congrArg Complex.re (congrFun hψeig (1, 1))
    simp [ψ, vec4, partialTransposeB.eq_1, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_two, hz, Complex.mul_re] at ht
    have hd : 0 ≤ (τ (1, 1) (1, 1)).re :=
      (Complex.nonneg_iff.mp hτ.1.diag_nonneg).1
    nlinarith [mul_pos (by linarith : 0 < (τ (1, 1) (1, 1)).re + l) hb]
  have hβpos : 0 < β := by
    by_contra h
    have hz : β = 0 := le_antisymm (le_of_not_gt h) hβ
    have ha : 0 < α := by nlinarith only [hn, hα, hz]
    have ht := congrArg Complex.re (congrFun hψeig (0, 0))
    simp [ψ, vec4, partialTransposeB.eq_1, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_two, hz, Complex.mul_re] at ht
    have hd : 0 ≤ (τ (0, 0) (0, 0)).re :=
      (Complex.nonneg_iff.mp hτ.1.diag_nonneg).1
    nlinarith [mul_pos (by linarith : 0 < (τ (0, 0) (0, 0)).re + l) ha]
  exact ⟨τ, l, α, β, hτ, hl, hαpos, hβpos, hn, hψeig, hτneg, htrace, hbineg⟩

private theorem positive_case
    (σ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hσ : IsDensity σ)
    (hν : 0 < 2 * ((partialTransposeB σ)⁻).trace.re) :
    ∃ x s : ℝ, 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ s ∧
      (2 * ((partialTransposeB σ)⁻).trace.re) *
        (2 * x + 2 * ((partialTransposeB σ)⁻).trace.re) ≤ (1 - x) ^ 2 ∧
      (2 * ((partialTransposeB σ)⁻).trace.re) *
        (2 * x + 2 * ((partialTransposeB σ)⁻).trace.re) ≤
          s ^ 2 * (x + 2 * ((partialTransposeB σ)⁻).trace.re) ^ 2 ∧
      binegativity σ = ((partialTransposeB σ)⁻).trace.re * (1 + s) := by
  obtain ⟨τ, l, α, β, hτ, hl, hα, hβ, hn, hev, hneg, htrace, hbineg⟩ :=
    schmidt_reduction σ hσ hν
  obtain ⟨x, hx, hx1, hm, hs⟩ := schmidt_constraints τ hτ l α β hl hα hβ hn hev
  refine ⟨x, 2 * α * β, hx, hx1, by positivity, ?_, ?_, ?_⟩
  · simpa only [htrace] using hm
  · simpa only [htrace] using hs
  · rw [htrace, hbineg, binegativity, hneg,
      schmidt_negative_trace l α β hl.le hα.le hβ.le]
    have ht : (((l : ℂ) • rankOneDensity (vec4 α 0 0 β)).trace).re = l := by
      simp [rankOneDensity, vec4, Matrix.trace, vecMulVec_apply, Fintype.sum_prod_type,
        Fin.sum_univ_two, Complex.mul_re]
      nlinarith only [congrArg (fun t : ℝ => l * t) hn]
    rw [ht]
    ring

/-- The two-qubit binegativity is bounded below by the Girard–Gour curve. -/
theorem result : claim := by
  intro σ hσ
  by_cases hzero : 2 * ((partialTransposeB σ)⁻).trace.re = 0
  · exact zero_case σ hzero
  · have hν : 0 < 2 * ((partialTransposeB σ)⁻).trace.re :=
      lt_of_le_of_ne (mul_nonneg (by norm_num) (nonnegative_trace_negPart _))
        (Ne.symm hzero)
    obtain ⟨x, s, hx, hx1, hs, hminor, hschmidt, hbineg⟩ := positive_case σ hσ hν
    have hbound := scalar_bound _ x s hν hx hx1 hs hminor hschmidt
    dsimp only at hbound ⊢
    rw [hbineg]
    nlinarith

end D5.S3.Quantum.Entanglement.TwoQubitBinegativityLowerBound
