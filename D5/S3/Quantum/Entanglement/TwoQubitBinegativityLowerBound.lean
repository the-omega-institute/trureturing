/- GID: D5/S3/Quantum/Entanglement/TwoQubitBinegativityLowerBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/TwoQubitBinegativityLowerBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The sharp lower bound on two-qubit binegativity at fixed negativity. -/

import D5.S3.Quantum.Entanglement.TwoQubitBinegativityUpperBoundRefutation
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
        Fintype.sum_prod_type, Fin.sum_univ_two] <;>
      ring
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
      Fin.sum_univ_two, map_add, map_mul]
    ring
  rw [heq]
  exact hσ.re_dotProduct_nonneg _

/-- A singular two-by-two coefficient array factors into two vectors. -/
private theorem singular_product (v : Fin 2 × Fin 2 → ℂ)
    (hv : v (0, 0) * v (1, 1) - v (0, 1) * v (1, 0) = 0) :
    ∃ a b : Fin 2 → ℂ, v = fun p => a p.1 * b p.2 := by
  by_cases h00 : v (0, 0) = 0
  · by_cases h01 : v (0, 1) = 0
    · refine ⟨![0, 1], ![v (1, 0), v (1, 1)], ?_⟩
      funext ⟨i, j⟩
      fin_cases i <;> fin_cases j <;> simp [h00, h01]
    · have h10 : v (1, 0) = 0 := by
        simpa only [h00, zero_mul, zero_sub, neg_eq_zero, mul_eq_zero, h01, false_or] using hv
      refine ⟨![v (0, 1), v (1, 1)], ![0, 1], ?_⟩
      funext ⟨i, j⟩
      fin_cases i <;> fin_cases j <;> simp [h00, h10]
  · refine ⟨![v (0, 0), v (1, 0)], ![1, v (0, 1) / v (0, 0)], ?_⟩
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [h00]
    apply (eq_div_iff h00).mpr
    linear_combination hv

/-- A complex determinant pencil supplies a product vector in any two-vector span. -/
private theorem product_in_span (v w : Fin 2 × Fin 2 → ℂ) (hw : w ≠ 0)
    (hv : ∀ t : ℂ, v + t • w ≠ 0) :
    ∃ (a b : Fin 2 → ℂ), (fun p : Fin 2 × Fin 2 => a p.1 * b p.2) ≠ 0 ∧
      ((fun p : Fin 2 × Fin 2 => a p.1 * b p.2) = w ∨
        ∃ t : ℂ, (fun p : Fin 2 × Fin 2 => a p.1 * b p.2) = v + t • w) := by
  by_cases hd : w (0, 0) * w (1, 1) - w (0, 1) * w (1, 0) = 0
  · obtain ⟨a, b, heq⟩ := singular_product w hd
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
    obtain ⟨a, b, heq⟩ := singular_product (v + t • w) hsing
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
    rw [← EuclideanSpace.inner_eq_star_dotProduct]
    exact orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal k l
  have hvv : star v ⬝ᵥ v = 1 := by simpa [v] using hinner i i
  have hww : star w ⬝ᵥ w = 1 := by simpa [w] using hinner j j
  have hvw : star v ⬝ᵥ w = 0 := by simpa [v, w, hij] using hinner i j
  have hwv : star w ⬝ᵥ v = 0 := by simpa [v, w, hij.symm] using hinner j i
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
      simpa only [w, RCLike.real_smul_eq_coe_smul] using hA.mulVec_eigenvectorBasis j
    rw [heig, dotProduct_smul, hww] at hnonneg
    simpa using (not_le_of_gt hj) hnonneg
  · rw [heq] at hnonneg
    have heigv : partialTransposeB σ *ᵥ v = (hA.eigenvalues i : ℂ) • v := by
      simpa only [v, RCLike.real_smul_eq_coe_smul] using hA.mulVec_eigenvectorBasis i
    have heigw : partialTransposeB σ *ᵥ w = (hA.eigenvalues j : ℂ) • w := by
      simpa only [w, RCLike.real_smul_eq_coe_smul] using hA.mulVec_eigenvectorBasis j
    have hform : star (v + t • w) ⬝ᵥ (partialTransposeB σ *ᵥ (v + t • w)) =
        (hA.eigenvalues i : ℂ) + (hA.eigenvalues j : ℂ) * (star t * t) := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, heigv, heigw]
      simp [star_add, star_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
        smul_dotProduct, hvv, hww, hvw, hwv, smul_eq_mul]
      ring
    rw [hform, ← Complex.normSq_eq_conj_mul_self] at hnonneg
    simp only [Complex.add_re, Complex.ofReal_mul, Complex.ofReal_re] at hnonneg
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hj.le (Complex.normSq_nonneg t)]

/-- The negative component can be transported to a unit Schmidt vector. -/
private theorem schmidt_reduction
    (σ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hσ : IsDensity σ)
    (hν : 0 < 2 * ((partialTransposeB σ)⁻).trace.re) :
    ∃ (τ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (l α β : ℝ),
      IsDensity τ ∧ 0 < l ∧ 0 < α ∧ 0 < β ∧ α ^ 2 + β ^ 2 = 1 ∧
      partialTransposeB τ *ᵥ vec4 α 0 0 β = (-l : ℂ) • vec4 α 0 0 β ∧
      (partialTransposeB τ)⁻ = (l : ℂ) • rankOneDensity (vec4 α 0 0 β) ∧
      ((partialTransposeB σ)⁻).trace.re = l ∧ binegativity σ = binegativity τ := by
  sorry

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
