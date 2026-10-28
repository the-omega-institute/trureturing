/- GID: D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricQubitWitnessSpectrum
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricQubitWitnessSpectrum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Exact spectra of symmetric two-qubit entanglement witnesses. -/

import D5.S3.Quantum.Divergence.CanonicalRelativeModularModel
import D5.S3.Zeros.PochhammerDeformation.QuadraticRadii

set_option linter.style.longLine false

open Matrix
open scoped BigOperators

namespace D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricQubitWitnessSpectrum

noncomputable def coherent (v : Fin 2 → ℂ) : Fin 3 → ℂ :=
  ![v 0 ^ 2, (Real.sqrt 2 : ℂ) * v 0 * v 1, v 1 ^ 2]

def IsSymmetricWitness (W : Matrix (Fin 3) (Fin 3) ℂ) : Prop :=
  W.IsHermitian ∧ ∀ v : Fin 2 → ℂ, 0 ≤ (star (coherent v) ⬝ᵥ (W *ᵥ coherent v)).re

def claim : Prop :=
  ∀ μ₁ μ₂ μ₃ : ℝ, μ₂ ≤ μ₁ → μ₃ ≤ μ₂ →
    ((∃ W : Matrix (Fin 3) (Fin 3) ℂ, IsSymmetricWitness W ∧
        W.charpoly = (Polynomial.X - Polynomial.C (μ₁ : ℂ)) * (Polynomial.X - Polynomial.C (μ₂ : ℂ)) *
          (Polynomial.X - Polynomial.C (μ₃ : ℂ))) ↔
      (0 ≤ μ₂ ∧ -Real.sqrt (μ₁ * μ₂) ≤ μ₃))

private def qform {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) : ℂ :=
  x ⬝ᵥ (A *ᵥ x)

private def energy (p q : ℝ) (x : Fin 2 → ℂ) : ℝ :=
  p * Complex.normSq (x 0) + q * Complex.normSq (x 1)

private def corner (G : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  G.submatrix Fin.castSucc Fin.castSucc

private def J : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, -1; 0, 1, 0; -1, 0, 0]

private theorem coherent_iff_null (x : Fin 3 → ℂ) :
    (∃ v : Fin 2 → ℂ, coherent v = x) ↔ qform J x = 0 := by
  have hj : qform J x = x 1 ^ 2 - 2 * x 0 * x 2 := by
    simp [qform.eq_1, J.eq_1, mulVec, dotProduct, Fin.sum_univ_three]
    ring
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [hj]
  constructor
  · rintro ⟨v, rfl⟩
    change ((Real.sqrt 2 : ℂ) * v 0 * v 1) ^ 2 - 2 * v 0 ^ 2 * v 1 ^ 2 = 0
    linear_combination (v 0 * v 1) ^ 2 * hs
  · intro hx
    by_cases h0 : x 0 = 0
    · have h1 : x 1 = 0 := by
        have : x 1 ^ 2 = 0 := by simpa [h0] using hx
        exact (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp this
      obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (x 2) (by norm_num : 0 < 2)
      refine ⟨![0, b], ?_⟩
      rw [coherent.eq_1]
      ext i
      fin_cases i
      · change (0 : ℂ) ^ 2 = x 0
        rw [h0]
        ring
      · change (Real.sqrt 2 : ℂ) * 0 * b = x 1
        rw [h1]
        ring
      · exact hb
    · obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (x 0) (by norm_num : 0 < 2)
      have ha0 : a ≠ 0 := by intro h; simp [h] at ha; exact h0 ha.symm
      have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)))
      refine ⟨![a, x 1 / ((Real.sqrt 2 : ℂ) * a)], ?_⟩
      ext i
      fin_cases i
      · simpa [coherent.eq_1] using ha
      · change (Real.sqrt 2 : ℂ) * a * (x 1 / ((Real.sqrt 2 : ℂ) * a)) = x 1
        exact mul_div_cancel₀ _ (mul_ne_zero hs0 ha0)
      · change (x 1 / ((Real.sqrt 2 : ℂ) * a)) ^ 2 = x 2
        rw [div_pow, div_eq_iff (pow_ne_zero 2 (mul_ne_zero hs0 ha0)),
          mul_pow, hs, ha]
        linear_combination hx

private theorem quadratic_pair (a b d : ℂ) (ha : a ≠ 0) :
    ∃ r s : ℂ, a * r ^ 2 + 2 * b * r + d = 0 ∧
      a * s ^ 2 + 2 * b * s + d = 0 ∧ a * r * s = d := by
  obtain ⟨r, s, _, hf⟩ :=
    D5.S3.Zeros.PochhammerDeformation.QuadraticRadii.quadratic_factors a (2*b) d ha
  refine ⟨r, s, ?_, ?_, ?_⟩
  · have hh := congrArg (fun f : Polynomial ℂ => f.eval r) hf
    simpa using hh
  · have hh := congrArg (fun f : Polynomial ℂ => f.eval s) hf
    simpa using hh
  · have hh := congrArg (fun f : Polynomial ℂ => f.coeff 0) hf
    simpa [mul_assoc] using hh.symm

private theorem two_root_bound (a b d : ℂ) (ha : a ≠ 0) (c L : ℝ) (hc : 0 < c)
    (h : ∀ z : ℂ, a * z ^ 2 + 2 * b * z + d = 0 → c * Complex.normSq z ≤ L) :
    c * ‖d‖ ≤ ‖a‖ * L := by
  obtain ⟨r, s, hr, hs, hrs⟩ := quadratic_pair a b d ha
  have h1 := h r hr
  have h2 := h s hs
  rw [Complex.normSq_eq_norm_sq] at h1 h2
  have hprod : c * (‖r‖ * ‖s‖) ≤ L := by nlinarith [sq_nonneg (‖r‖ - ‖s‖)]
  have hn := congrArg norm hrs
  simp only [norm_mul] at hn
  nlinarith [norm_nonneg a]

private theorem bilinear_sq_le (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : Aᵀ = A)
    (p q : ℝ) (h : ∀ u : Fin 2 → ℂ, ‖qform A u‖ ≤ energy p q u)
    (x y : Fin 2 → ℂ) :
    ‖x ⬝ᵥ (A *ᵥ y)‖ ^ 2 ≤ energy p q x * energy p q y := by
  let B := A.toBilin'
  have hB : B.IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr hA
  have pol (v w : Fin 2 → ℂ) :
      4 * (v ⬝ᵥ (A *ᵥ w)) = qform A (v + w) - qform A (v - w) := by
    have hp := hB.polarization v w
    have hm := hB.polarization v (-w)
    simp only [map_neg, LinearMap.neg_apply, neg_neg, ← sub_eq_add_neg] at hm
    change B v w = (B (v + w) (v + w) - B v v - B w w) / 2 at hp
    change -B v w = (B (v - w) (v - w) - B v v - B w w) / 2 at hm
    simp only [B, Matrix.toBilin'_apply'] at hp hm
    unfold qform
    linear_combination 2 * hp - 2 * hm
  have half (v w : Fin 2 → ℂ) :
      2 * ‖v ⬝ᵥ (A *ᵥ w)‖ ≤ energy p q v + energy p q w := by
    have hn := norm_sub_le (qform A (v+w)) (qform A (v-w))
    rw [← pol, norm_mul] at hn
    norm_num only [Complex.norm_ofNat] at hn
    have he : energy p q (v+w) + energy p q (v-w) =
        2 * (energy p q v + energy p q w) := by
      simp only [energy.eq_1, Pi.add_apply, Pi.sub_apply, Complex.normSq_add, Complex.normSq_sub]
      ring
    linarith [h (v+w), h (v-w)]
  have scale (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
      2 * s * t * ‖x ⬝ᵥ (A *ᵥ y)‖ ≤
        s ^ 2 * energy p q x + t ^ 2 * energy p q y := by
    have hh := half ((s : ℂ) • x) ((t : ℂ) • y)
    simp only [mulVec_smul, smul_dotProduct, dotProduct_smul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs, abs_of_nonneg ht,
      energy.eq_1, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Complex.normSq_ofReal,
      ← pow_two, norm_mul] at hh
    dsimp [energy]
    nlinarith only [hh]
  have hP : 0 ≤ energy p q x := le_trans (norm_nonneg _) (h x)
  have hR : 0 ≤ energy p q y := le_trans (norm_nonneg _) (h y)
  by_cases h0 : energy p q x = 0
  · have hh := scale (energy p q y + 1) ‖x ⬝ᵥ (A *ᵥ y)‖ (by linarith) (norm_nonneg _)
    rw [h0] at hh ⊢
    nlinarith [sq_nonneg ‖x ⬝ᵥ (A *ᵥ y)‖]
  · have hh := scale ‖x ⬝ᵥ (A *ᵥ y)‖ (energy p q x) (norm_nonneg _) hP
    have hPpos : 0 < energy p q x := lt_of_le_of_ne hP (Ne.symm h0)
    nlinarith

private theorem det_bound (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : Aᵀ = A)
    (p q : ℝ) (h : ∀ u : Fin 2 → ℂ, ‖qform A u‖ ≤ energy p q u) :
    0 ≤ p ∧ 0 ≤ q ∧ ‖A.det‖ ≤ p * q := by
  have h10 : A 1 0 = A 0 1 := congrFun (congrFun hA 0) 1
  have hp' : ‖A 0 0‖ ≤ p := by
    simpa [qform.eq_1, energy.eq_1, mulVec, dotProduct, Fin.sum_univ_two] using h ![1, 0]
  have hq' : ‖A 1 1‖ ≤ q := by
    simpa [qform.eq_1, energy.eq_1, mulVec, dotProduct, Fin.sum_univ_two] using h ![0, 1]
  have hp : 0 ≤ p := le_trans (norm_nonneg _) hp'
  have hq : 0 ≤ q := le_trans (norm_nonneg _) hq'
  refine ⟨hp, hq, ?_⟩
  let a := A 0 0
  let b := A 0 1
  let S := q * Complex.normSq a + p * Complex.normSq b
  have hS : 0 ≤ S := add_nonneg (mul_nonneg hq (Complex.normSq_nonneg _))
    (mul_nonneg hp (Complex.normSq_nonneg _))
  have hb1 : (![1, 0] : Fin 2 → ℂ) ⬝ᵥ
      (A *ᵥ ![(q : ℂ) * star a, (p : ℂ) * star b]) = (S : ℂ) := by
    simp only [mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, one_mul, zero_mul, add_zero]
    change a * (↑q * star a) + b * (↑p * star b) = ↑S
    rw [show a * (↑q * star a) + b * (↑p * star b) =
      ↑q * (a * star a) + ↑p * (b * star b) by ring]
    simp only [Complex.star_def, Complex.mul_conj, S, Complex.ofReal_add, Complex.ofReal_mul]
  have h1 := bilinear_sq_le A hA p q h ![1, 0]
    ![(q : ℂ) * star a, (p : ℂ) * star b]
  rw [hb1] at h1
  simp only [energy.eq_1, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.normSq_one,
    Complex.normSq_zero, mul_one, mul_zero, add_zero, Complex.normSq_mul,
    Complex.normSq_ofReal, Complex.star_def, Complex.normSq_conj, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hS] at h1
  have hSb : S ≤ p ^ 2 * q := by
    have hfac : S * S ≤ p ^ 2 * q * S := by dsimp [S] at *; nlinarith only [h1]
    by_cases hz : S = 0
    · rw [hz]; positivity
    · have : 0 < S := lt_of_le_of_ne hS (Ne.symm hz)
      exact le_of_mul_le_mul_right hfac this
  have h2 := bilinear_sq_le A hA p q h ![0, 1] ![b, -a]
  have hb2 : (![0, 1] : Fin 2 → ℂ) ⬝ᵥ (A *ᵥ ![b, -a]) = -A.det := by
    simp [mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two, h10, a, b]
    ring
  rw [hb2, norm_neg] at h2
  simp only [energy.eq_1, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.normSq_one,
    Complex.normSq_zero, mul_one, mul_zero, zero_add, Complex.normSq_neg] at h2
  have hdet : ‖A.det‖ ^ 2 ≤ (p * q) ^ 2 := by
    have h3 := mul_le_mul_of_nonneg_left hSb hq
    dsimp [S] at h3
    nlinarith only [h2, h3]
  nlinarith [norm_nonneg A.det, mul_nonneg hp hq]

private theorem cone_model (W : Matrix (Fin 3) (Fin 3) ℂ) (hW : IsSymmetricWitness W)
    (d : Fin 3 → ℝ)
    (hχ : W.charpoly = ∏ i : Fin 3, (Polynomial.X - Polynomial.C (d i : ℂ))) :
    ∃ G : Matrix (Fin 3) (Fin 3) ℂ, Gᵀ = G ∧ Gᴴ * G = 1 ∧
      ∀ z : Fin 3 → ℂ, qform G z = 0 → 0 ≤ ∑ i : Fin 3, d i * Complex.normSq (z i) := by
  let D := Matrix.diagonal (fun i => (d i : ℂ))
  have hD : D.IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    simp [IsSelfAdjoint]
  have he := (hW.1.eigenvalues_eq_eigenvalues_iff hD).mpr
    (hχ.trans (Matrix.charpoly_diagonal _).symm)
  let U := hW.1.eigenvectorUnitary * star hD.eigenvectorUnitary
  have hspec : W = (U : Matrix (Fin 3) (Fin 3) ℂ) * D * star U := by
    have hw := hW.1.spectral_theorem
    have hd := hD.conjStarAlgAut_star_eigenvectorUnitary
    simp only [Unitary.conjStarAlgAut_apply] at hw hd
    rw [he, ← hd] at hw
    dsimp only [U]
    simpa only [Submonoid.coe_mul, Unitary.coe_star, star_mul, star_star, mul_assoc] using hw
  have hJt : Jᵀ = J := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hJ : J ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [J.eq_1, mul_apply, Fin.sum_univ_succ]
  let G := (U : Matrix (Fin 3) (Fin 3) ℂ)ᵀ * J * U
  have hGU : G ∈ Matrix.unitaryGroup (Fin 3) ℂ :=
    mul_mem (mul_mem (Matrix.transpose_mem_unitaryGroup_iff.mpr U.prop) hJ) U.prop
  refine ⟨G, ?_, Matrix.mem_unitaryGroup_iff'.mp hGU, ?_⟩
  · dsimp only [G]
    simp only [transpose_mul, transpose_transpose, hJt, mul_assoc]
  · intro z hz
    have hnull : qform J ((U : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ z) = 0 := by
      have hh : qform G z = qform J ((U : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ z) := by
        simpa only [qform, G, LinearMap.BilinForm.comp_apply, Matrix.toBilin'_apply',
          Matrix.toLin'_apply] using
          congrArg (fun B : LinearMap.BilinForm ℂ (Fin 3 → ℂ) => B z z)
            (Matrix.toBilin'_comp J (U : Matrix (Fin 3) (Fin 3) ℂ) U).symm
      exact hh ▸ hz
    obtain ⟨v, hv⟩ := (coherent_iff_null _).mpr hnull
    have hpos := hW.2 v
    rw [hv] at hpos
    have hxW : W *ᵥ ((U : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ z) =
        (U : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ (D *ᵥ z) := by
      rw [hspec]
      simp only [Unitary.coe_star, ← mulVec_mulVec]
      rw [mulVec_mulVec z (star (U : Matrix (Fin 3) (Fin 3) ℂ)) U,
        Unitary.coe_star_mul_self, one_mulVec]
    have hexp : star ((U : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ z) ⬝ᵥ
        (W *ᵥ ((U : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ z)) = star z ⬝ᵥ (D *ᵥ z) := by
      rw [hxW, star_mulVec, dotProduct_mulVec, vecMul_vecMul]
      change (star z ᵥ* (star (U : Matrix (Fin 3) (Fin 3) ℂ) *
        (U : Matrix (Fin 3) (Fin 3) ℂ))) ⬝ᵥ (D *ᵥ z) = _
      rw [Unitary.coe_star_mul_self, vecMul_one]
    rw [hexp] at hpos
    rw [D5.S3.Quantum.Divergence.CanonicalChannelDPI.diagonal_quadratic_form] at hpos
    simpa only [Complex.normSq_eq_norm_sq] using hpos

private theorem unitary_corner (G : Matrix (Fin 3) (Fin 3) ℂ) (hG : Gᴴ * G = 1) :
    ‖(corner G).det‖ = ‖G 2 2‖ ∧ ‖G 2 2‖ ≤ 1 := by
  have hGG : G * Gᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp
    (Matrix.mem_unitaryGroup_iff'.mpr hG)
  have hd : ‖G.det‖ = 1 := CStarRing.norm_of_mem_unitary
    (Matrix.det_of_mem_unitary (Matrix.mem_unitaryGroup_iff'.mpr hG))
  have hadj : G.adjugate = G.det • Gᴴ := by
    calc
      G.adjugate = G.adjugate * (G * Gᴴ) := by rw [hGG, mul_one]
      _ = (G.adjugate * G) * Gᴴ := (mul_assoc _ _ _).symm
      _ = G.det • Gᴴ := by rw [Matrix.adjugate_mul, smul_mul_assoc, one_mul]
  have he := congrFun (congrFun hadj 2) 2
  have he' : (corner G).det = G.det * star (G 2 2) := by
    simpa [corner.eq_1, Matrix.det_fin_two, Matrix.adjugate_fin_three] using he
  constructor
  · rw [he', norm_mul, norm_star, hd, one_mul]
  · exact entry_norm_bound_of_unitary (Matrix.mem_unitaryGroup_iff'.mpr hG) 2 2

private theorem cone_spectral_bound (G : Matrix (Fin 3) (Fin 3) ℂ)
    (hS : Gᵀ = G) (hU : Gᴴ * G = 1) (p q c : ℝ) (hc : 0 < c)
    (h : ∀ z : Fin 3 → ℂ, qform G z = 0 →
      0 ≤ p * Complex.normSq (z 0) + q * Complex.normSq (z 1) - c * Complex.normSq (z 2)) :
    0 ≤ p ∧ 0 ≤ q ∧ c ^ 2 ≤ p * q := by
  have h20 : G 2 0 = G 0 2 := congrFun (congrFun hS 0) 2
  have h21 : G 2 1 = G 1 2 := congrFun (congrFun hS 1) 2
  have hg : G 2 2 ≠ 0 := by
    intro hg
    have hz : qform G ![0, 0, 1] = 0 := by
      simp [qform.eq_1, mulVec, dotProduct, Fin.sum_univ_three, hg]
    have hh := h ![0, 0, 1] hz
    simp at hh
    linarith
  let t := ‖G 2 2‖
  have ht : 0 < t := norm_pos_iff.mpr hg
  obtain ⟨hdet, ht1⟩ := unitary_corner G hU
  have hA : (corner G)ᵀ = corner G := Matrix.IsSymm.submatrix hS Fin.castSucc
  have hroot (u : Fin 2 → ℂ) : c * ‖qform (corner G) u‖ ≤ t * energy p q u := by
    apply two_root_bound (G 2 2) (G 0 2 * u 0 + G 1 2 * u 1)
      (qform (corner G) u) hg c (energy p q u) hc
    intro z hz
    have hz' : qform G ![u 0, u 1, z] = 0 := by
      simp only [qform.eq_1, corner.eq_1, mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        submatrix_apply, Fin.castSucc_zero, Fin.castSucc_one, h20, h21] at hz ⊢
      linear_combination hz
    have hh := h ![u 0, u 1, z] hz'
    change 0 ≤ p * Complex.normSq (u 0) + q * Complex.normSq (u 1) -
      c * Complex.normSq z at hh
    dsimp [energy]
    linarith
  have hscaled : ∀ u : Fin 2 → ℂ,
      ‖qform ((c : ℂ) • corner G) u‖ ≤ energy (t*p) (t*q) u := by
    intro u
    have hh := hroot u
    simp only [qform.eq_1, smul_mulVec, dotProduct_smul, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hc]
    dsimp [qform, energy] at hh ⊢
    nlinarith only [hh]
  have hscaledS : ((c : ℂ) • corner G)ᵀ = (c : ℂ) • corner G :=
    Matrix.IsSymm.smul hA (c : ℂ)
  obtain ⟨hp', hq', hd⟩ := det_bound ((c : ℂ) • corner G) hscaledS (t*p) (t*q) hscaled
  have hp : 0 ≤ p := nonneg_of_mul_nonneg_right hp' ht
  have hq : 0 ≤ q := nonneg_of_mul_nonneg_right hq' ht
  refine ⟨hp, hq, ?_⟩
  have hd' : c ^ 2 * t ≤ t ^ 2 * (p * q) := by
    simp only [Matrix.det_smul, Fintype.card_fin, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hc, hdet] at hd
    nlinarith only [hd]
  have hd'' : c ^ 2 ≤ t * (p * q) := by
    apply le_of_mul_le_mul_right (a := t) _ ht
    nlinarith only [hd']
  exact hd''.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ht1 (mul_nonneg hp hq))

private theorem diagonal_witness (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hr : -Real.sqrt (p * q) ≤ r) :
    IsSymmetricWitness (Matrix.diagonal ![(p : ℂ), (r : ℂ), (q : ℂ)]) := by
  constructor
  · apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    fin_cases i <;> simp [IsSelfAdjoint]
  · intro v
    change 0 ≤ (star (coherent v) ⬝ᵥ
      ((Matrix.diagonal (fun i => ((![p,r,q] : Fin 3 → ℝ) i : ℂ))) *ᵥ coherent v)).re
    rw [D5.S3.Quantum.Divergence.CanonicalChannelDPI.diagonal_quadratic_form]
    simp only [← Complex.normSq_eq_norm_sq]
    simp only [Fin.sum_univ_three, coherent.eq_1, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, map_pow, Complex.normSq_mul, Complex.normSq_ofReal,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hx := Complex.normSq_nonneg (v 0)
    have hy := Complex.normSq_nonneg (v 1)
    have hs : Real.sqrt p * Real.sqrt q = Real.sqrt (p*q) := (Real.sqrt_mul hp q).symm
    have hi : p * Complex.normSq (v 0) ^ 2 + r * (2 * Complex.normSq (v 0) *
        Complex.normSq (v 1)) + q * Complex.normSq (v 1) ^ 2 =
        (Real.sqrt p * Complex.normSq (v 0) - Real.sqrt q * Complex.normSq (v 1)) ^ 2 +
          2 * (r + Real.sqrt (p*q)) * Complex.normSq (v 0) * Complex.normSq (v 1) := by
      rw [← hs]
      nlinarith only [Real.sq_sqrt hp, Real.sq_sqrt hq]
    rw [hi]
    exact add_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg
      (mul_nonneg (by norm_num) (by linarith)) hx) hy)

theorem result : claim := by
  intro μ₁ μ₂ μ₃ h12 h23
  constructor
  · rintro ⟨W, hW, hχ⟩
    by_cases h3 : 0 ≤ μ₃
    · exact ⟨h3.trans h23, le_trans (neg_nonpos.mpr (Real.sqrt_nonneg _)) h3⟩
    · have hc : 0 < -μ₃ := by linarith
      have hχ' : W.charpoly = ∏ i : Fin 3,
          (Polynomial.X - Polynomial.C ((![μ₁, μ₂, μ₃] : Fin 3 → ℝ) i : ℂ)) := by
        simpa [Fin.prod_univ_three, mul_assoc] using hχ
      obtain ⟨G, hS, hU, hG⟩ := cone_model W hW ![μ₁, μ₂, μ₃] hχ'
      have hpos : ∀ z : Fin 3 → ℂ, qform G z = 0 →
          0 ≤ μ₁ * Complex.normSq (z 0) + μ₂ * Complex.normSq (z 1) -
            (-μ₃) * Complex.normSq (z 2) := by
        intro z hz
        have hh := hG z hz
        simpa [Fin.sum_univ_three, sub_eq_add_neg, add_assoc] using hh
      obtain ⟨_, h2, hb⟩ := cone_spectral_bound G hS hU μ₁ μ₂ (-μ₃) hc hpos
      exact ⟨h2, Real.neg_sqrt_le_of_sq_le (by simpa using hb)⟩
  · rintro ⟨h2, hb⟩
    refine ⟨Matrix.diagonal ![(μ₁ : ℂ), (μ₃ : ℂ), (μ₂ : ℂ)],
      diagonal_witness μ₁ μ₂ μ₃ (h2.trans h12) h2 hb, ?_⟩
    simp only [Matrix.charpoly_diagonal, Fin.prod_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val]
    ring

end D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricQubitWitnessSpectrum
