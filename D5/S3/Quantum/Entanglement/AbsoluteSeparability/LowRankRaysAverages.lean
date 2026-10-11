/- GID: D5/S3/Quantum/Entanglement/AbsoluteSeparability/LowRankRaysAverages
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsoluteSeparability/LowRankRaysAverages
   mirror-E: none(waiver:formal-unit-only)
   anchors: []
   utility: none
   digest: Finite product-vector moments give separable rank-one and projected averages. -/

import D5.S3.Quantum.Entanglement.AbsoluteSeparability.ContractionBlocks
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Resource.SeparableConeResidualWitness

namespace D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRaysAverages

open scoped BigOperators Kronecker ComplexOrder
open Matrix
open D5.S3.Resource.CompositeCones
open D5.S3.Resource.EntanglementWitness

private noncomputable def omega8 (q : Fin 8) : ℂ :=
  ![0, 0, 0, 0, (Real.sqrt 2 : ℂ), -(Real.sqrt 2 : ℂ),
    Complex.I * (Real.sqrt 2 : ℂ), -Complex.I * (Real.sqrt 2 : ℂ)] q

private def flip8 : Fin 8 ≃ Fin 8 :=
  (Equiv.swap 4 5).trans (Equiv.swap 6 7)

private def chooseStar (b : Bool) (z : ℂ) : ℂ := if b then star z else z

private noncomputable def signedOmega (b : Bool) (q : Fin 8) : ℂ :=
  chooseStar b (omega8 q)

private theorem expectation_product {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → Fin 8 → ℂ) :
    (𝔼 g : ι → Fin 8, ∏ i, f i (g i)) = ∏ i, (𝔼 q : Fin 8, f i q) := by
  simp only [Fintype.expect_eq_sum_div_card, Fintype.card_pi, Fintype.card_fin]
  rw [← Fintype.prod_sum, Finset.prod_div_distrib]
  simp

private theorem omega_moments {ι : Type} [Fintype ι] [DecidableEq ι] :
    (∀ (i : ι) (s : Bool), (𝔼 g : ι → Fin 8, signedOmega s (g i)) = 0) ∧
    (∀ (i j : ι) (s t : Bool),
      (𝔼 g : ι → Fin 8, signedOmega s (g i) * signedOmega t (g j)) =
        if s = t then 0 else if i = j then 1 else 0) ∧
    (∀ (i j k : ι) (s t u : Bool),
      (𝔼 g : ι → Fin 8,
        signedOmega s (g i) * signedOmega t (g j) * signedOmega u (g k)) = 0) ∧
    (∀ (i j k l : ι),
      (𝔼 g : ι → Fin 8, omega8 (g i) * star (omega8 (g j)) *
        omega8 (g k) * star (omega8 (g l))) =
      (if i = j then 1 else 0) * (if k = l then 1 else 0) +
        (if i = l then 1 else 0) * (if k = j then 1 else 0)) := by
  have scalar_moments (a b : Fin 3) :
      (𝔼 q : Fin 8, omega8 q ^ a.val * star (omega8 q) ^ b.val) =
      if a = b then (if a = 0 then 1 else if a = 1 then 1 else 2) else 0 := by
    have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by
      exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have hs4 : (Real.sqrt 2 : ℂ)^4 = 4 := by
      calc (Real.sqrt 2 : ℂ)^4 = ((Real.sqrt 2 : ℂ)^2)^2 := by ring
           _ = 4 := by rw [hs]; norm_num
    fin_cases a <;> fin_cases b <;>
      simp [Fintype.expect_eq_sum_div_card, omega8, Fin.sum_univ_succ, map_mul, map_neg,
        Complex.conj_ofReal, Complex.conj_I, ← pow_two] <;>
      ring_nf <;> simp_all <;> norm_num
  have omega_fourth
      (i j k l : ι) :
      (𝔼 g : ι → Fin 8, omega8 (g i) * star (omega8 (g j)) *
        omega8 (g k) * star (omega8 (g l))) =
      (if i = j then 1 else 0) * (if k = l then 1 else 0) +
        (if i = l then 1 else 0) * (if k = j then 1 else 0) := by
    let f (t : ι) (q : Fin 8) : ℂ :=
      (if t = i then omega8 q else 1) * (if t = j then star (omega8 q) else 1) *
        (if t = k then omega8 q else 1) * (if t = l then star (omega8 q) else 1)
    have hp (g : ι → Fin 8) : (∏ t, f t (g t)) =
        omega8 (g i) * star (omega8 (g j)) * omega8 (g k) * star (omega8 (g l)) := by
      simp only [f, Finset.prod_mul_distrib, Fintype.prod_ite_eq']
    simp_rw [← hp]
    rw [expectation_product]
    have h10 : (𝔼 q : Fin 8, omega8 q) = 0 := by
      simpa using scalar_moments 1 0
    have h20 : (𝔼 q : Fin 8, omega8 q ^ 2) = 0 := by
      simpa using scalar_moments 2 0
    have h21 : (𝔼 q : Fin 8, omega8 q ^ 2 * star (omega8 q)) = 0 := by
      simpa using scalar_moments 2 1
    have h11 : (𝔼 q : Fin 8, omega8 q * star (omega8 q)) = 1 := by
      simpa using scalar_moments 1 1
    have h22 : (𝔼 q : Fin 8, omega8 q ^ 2 * star (omega8 q)^2) = 2 := by
      simpa using scalar_moments 2 2
    have hpair (a b : ι) :
        (∏ t, 𝔼 q : Fin 8,
          (if t = a then omega8 q else 1) * (if t = a then star (omega8 q) else 1) *
            (if t = b then omega8 q else 1) * (if t = b then star (omega8 q) else 1)) =
        if a = b then 2 else 1 := by
      by_cases hab : a = b
      · subst b
        have ht (t : ι) :
            (𝔼 q : Fin 8,
              (if t = a then omega8 q else 1) * (if t = a then star (omega8 q) else 1) *
                (if t = a then omega8 q else 1) * (if t = a then star (omega8 q) else 1)) =
            if t = a then 2 else 1 := by
          by_cases hta : t = a
          · simp only [hta, if_true]
            convert h22 using 1
            congr 1
            ext q
            ring
          · simp [hta]
        simp_rw [ht]
        simp
      · have ht (t : ι) :
            (𝔼 q : Fin 8,
              (if t = a then omega8 q else 1) * (if t = a then star (omega8 q) else 1) *
                (if t = b then omega8 q else 1) * (if t = b then star (omega8 q) else 1)) = 1 := by
          by_cases hta : t = a
          · subst t
            simpa [hab] using h11
          · by_cases htb : t = b
            · subst t
              simpa [hta] using h11
            · simp [hta, htb]
        simp_rw [ht]
        simp [hab]
    by_cases hij : i = j
    · subst j
      by_cases hkl : k = l
      · subst l
        dsimp only [f]
        rw [hpair]
        by_cases hik : i = k
        · norm_num [hik]
        · simp [hik, Ne.symm hik]
      · have hz : (∏ t, 𝔼 q : Fin 8, f t q) = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_univ k)
          by_cases hki : k = i
          · subst k
            simp only [f, if_true, if_neg hkl]
            convert h21 using 1
            congr 1
            ext q
            ring
          · simpa [f, hki, hkl] using h10
        rw [hz]
        by_cases hil : i = l <;> simp_all
    · by_cases hil : i = l
      · subst l
        by_cases hkj : k = j
        · subst k
          have heq : (∏ t, 𝔼 q : Fin 8, f t q) =
              (∏ t, 𝔼 q : Fin 8,
                (if t = i then omega8 q else 1) * (if t = i then star (omega8 q) else 1) *
                  (if t = j then omega8 q else 1) * (if t = j then star (omega8 q) else 1)) := by
            congr 1; ext t; congr 1; ext q; dsimp [f]; ring
          rw [heq, hpair]
          simp [hij, Ne.symm hij]
        · have hz : (∏ t, 𝔼 q : Fin 8, f t q) = 0 := by
            apply Finset.prod_eq_zero (Finset.mem_univ k)
            by_cases hki : k = i
            · subst k
              simp only [f, if_true, if_neg hij]
              convert h21 using 1
              congr 1
              ext q
              ring
            · simpa [f, hki, hkj] using h10
          simp [hz, hij, hkj]
      · have hz : (∏ t, 𝔼 q : Fin 8, f t q) = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_univ i)
          by_cases hik : i = k
          · subst k
            simpa [f, hij, hil, ← pow_two] using h20
          · simpa [f, hij, hil, hik] using h10
        simp [hz, hij, hil]
  have omega_second (i j : ι) :
      (𝔼 g : ι → Fin 8, omega8 (g i) * star (omega8 (g j))) =
        if i = j then 1 else 0 := by
    let f (t : ι) (q : Fin 8) : ℂ :=
      (if t = i then omega8 q else 1) * (if t = j then star (omega8 q) else 1)
    have hp (g : ι → Fin 8) : (∏ t, f t (g t)) =
        omega8 (g i) * star (omega8 (g j)) := by
      simp only [f, Finset.prod_mul_distrib, Fintype.prod_ite_eq']
    simp_rw [← hp]
    rw [expectation_product]
    by_cases hij : i = j
    · subst j
      have ht (t : ι) : (𝔼 q : Fin 8, f t q) = 1 := by
        by_cases hti : t = i
        · simpa [f, hti] using scalar_moments 1 1
        · simp [f, hti]
      simp [ht]
    · have hz : (∏ t, 𝔼 q : Fin 8, f t q) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simpa [f, hij] using scalar_moments 1 0
      simp [hz, hij]
  have omega_pseudoSecond (i j : ι) :
      (𝔼 g : ι → Fin 8, omega8 (g i) * omega8 (g j)) = 0 := by
    let f (t : ι) (q : Fin 8) : ℂ :=
      (if t = i then omega8 q else 1) * (if t = j then omega8 q else 1)
    have hp (g : ι → Fin 8) : (∏ t, f t (g t)) = omega8 (g i) * omega8 (g j) := by
      simp only [f, Finset.prod_mul_distrib, Fintype.prod_ite_eq']
    simp_rw [← hp]
    rw [expectation_product]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_cases hij : i = j
    · subst j
      simpa [f, ← pow_two] using scalar_moments 2 0
    · simpa [f, hij] using scalar_moments 1 0
  have omega_flip8 (q : Fin 8) : omega8 (flip8 q) = -omega8 q := by
    fin_cases q <;> simp [flip8, omega8, Equiv.swap_apply_def]
  have signedOmega_flip8 (b : Bool) (q : Fin 8) :
      signedOmega b (flip8 q) = -signedOmega b q := by
    cases b <;> simp [signedOmega, chooseStar, omega_flip8]
  have omega_mean (i : ι) (b : Bool) :
      (𝔼 g : ι → Fin 8, signedOmega b (g i)) = 0 := by
    let e : (ι → Fin 8) ≃ (ι → Fin 8) := Equiv.piCongrRight (fun _ => flip8)
    have he : (𝔼 g : ι → Fin 8, signedOmega b (g i)) =
        (𝔼 g : ι → Fin 8, -signedOmega b (g i)) := by
      apply Fintype.expect_equiv e
      intro g
      simp [e, signedOmega_flip8]
    rw [Finset.expect_neg_distrib] at he
    exact CharZero.eq_neg_self_iff.mp he
  have omega_third
      (i j k : ι) (a b c : Bool) :
      (𝔼 g : ι → Fin 8,
        signedOmega a (g i) * signedOmega b (g j) * signedOmega c (g k)) = 0 := by
    let e : (ι → Fin 8) ≃ (ι → Fin 8) := Equiv.piCongrRight (fun _ => flip8)
    have he : (𝔼 g : ι → Fin 8,
        signedOmega a (g i) * signedOmega b (g j) * signedOmega c (g k)) =
        (𝔼 g : ι → Fin 8,
          -(signedOmega a (g i) * signedOmega b (g j) * signedOmega c (g k))) := by
      apply Fintype.expect_equiv e
      intro g
      simp [e, signedOmega_flip8]
    rw [Finset.expect_neg_distrib] at he
    exact CharZero.eq_neg_self_iff.mp he
  have omega_second_signed
      (i j : ι) (s t : Bool) :
      (𝔼 g : ι → Fin 8, signedOmega s (g i) * signedOmega t (g j)) =
        if s = t then 0 else if i = j then 1 else 0 := by
    have hstar : (𝔼 g : ι → Fin 8, star (omega8 (g i)) * star (omega8 (g j))) = 0 := by
      have h := congrArg star (omega_pseudoSecond i j)
      simpa [Fintype.expect_eq_sum_div_card, star_div₀, map_sum, star_mul, mul_comm] using h
    cases s <;> cases t
    · simpa [signedOmega, chooseStar] using omega_pseudoSecond i j
    · simpa [signedOmega, chooseStar] using omega_second i j
    · simpa [signedOmega, chooseStar, mul_comm, eq_comm] using omega_second j i
    · simpa [signedOmega, chooseStar] using hstar
  exact ⟨omega_mean, omega_second_signed, omega_third, omega_fourth⟩

private theorem affine_wick {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [Nonempty Ω] (x : Ω → ι → ℂ)
    (h1 : ∀ (i : ι) (s : Bool), (𝔼 w, chooseStar s (x w i)) = 0)
    (h2 : ∀ (i j : ι) (s t : Bool),
      (𝔼 w, chooseStar s (x w i) * chooseStar t (x w j)) =
        if s = t then 0 else if i = j then 1 else 0)
    (h3 : ∀ (i j k : ι) (s t u : Bool),
      (𝔼 w, chooseStar s (x w i) * chooseStar t (x w j) * chooseStar u (x w k)) = 0)
    (h4 : ∀ (i j k l : ι),
      (𝔼 w, x w i * star (x w j) * star (x w k) * x w l) =
        (if i = j then 1 else 0) * (if k = l then 1 else 0) +
          (if i = k then 1 else 0) * (if j = l then 1 else 0))
    (a b c d : ℂ) (A B C D : ι → ℂ) :
    (𝔼 w,
      (a + ∑ i, A i * x w i) * (b + ∑ i, B i * star (x w i)) *
        (c + ∑ i, C i * star (x w i)) * (d + ∑ i, D i * x w i)) =
    (a*b + ∑ i, A i*B i) * (c*d + ∑ i, C i*D i) +
      a*c*(∑ i, B i*D i) + b*d*(∑ i, A i*C i) +
      (∑ i, A i*C i)*(∑ i, B i*D i) := by
  let L (A : ι → ℂ) (s : Bool) (w : Ω) : ℂ := ∑ i, A i * chooseStar s (x w i)
  have hscale (r : ℂ) (f : Ω → ℂ) :
      (𝔼 w, r * f w) = r * (𝔼 w, f w) := (Finset.mul_expect _ _ _).symm
  have hlin (A : ι → ℂ) (s : Bool) : (𝔼 w, L A s w) = 0 := by
    dsimp [L]
    simp_rw [Finset.expect_sum_comm, hscale, h1]
    simp
  have hquad (A B : ι → ℂ) (s t : Bool) :
      (𝔼 w, L A s w * L B t w) = if s = t then 0 else ∑ i, A i*B i := by
    have hp (w : Ω) : L A s w * L B t w =
        ∑ i, ∑ j, (A i*B j)*(chooseStar s (x w i)*chooseStar t (x w j)) := by
      dsimp [L]
      rw [Fintype.sum_mul_sum]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      ring
    simp_rw [hp, Finset.expect_sum_comm, hscale, h2]
    by_cases hst : s = t <;> simp [hst, mul_ite]
  have htri (A B C : ι → ℂ) (s t u : Bool) :
      (𝔼 w, L A s w * L B t w * L C u w) = 0 := by
    have hp (w : Ω) : L A s w * L B t w * L C u w =
        ∑ i, ∑ j, ∑ k, (A i*B j*C k)*
          (chooseStar s (x w i)*chooseStar t (x w j)*chooseStar u (x w k)) := by
      dsimp [L]
      rw [Fintype.sum_mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro i _
      rw [Fintype.sum_mul_sum]
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro k _
      ring
    simp_rw [hp, Finset.expect_sum_comm, hscale, h3]
    simp
  have hfour : (𝔼 w, L A false w * L B true w * L C true w * L D false w) =
      (∑ i, A i*B i)*(∑ i, C i*D i) + (∑ i, A i*C i)*(∑ i, B i*D i) := by
    have hp (w : Ω) : L A false w * L B true w * L C true w * L D false w =
        ∑ i, ∑ j, ∑ k, ∑ l, (A i*B j*C k*D l)*
          (x w i * star (x w j) * star (x w k) * x w l) := by
      dsimp [L, chooseStar]
      rw [Fintype.sum_mul_sum, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro i _
      rw [Fintype.sum_mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j _
      rw [Fintype.sum_mul_sum]
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro l _
      ring
    simp_rw [hp, Finset.expect_sum_comm, hscale, h4]
    simp_rw [mul_add, Finset.sum_add_distrib]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte, Finset.sum_ite_irrel, Finset.sum_const_zero]
    congr 1
    · rw [Fintype.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    · rw [Fintype.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
  have hp (w : Ω) :
      (a+L A false w)*(b+L B true w)*(c+L C true w)*(d+L D false w) =
      a*b*c*d + (b*c*d)*L A false w + (a*c*d)*L B true w +
        (a*b*d)*L C true w + (a*b*c)*L D false w +
        (c*d)*(L A false w*L B true w) + (b*d)*(L A false w*L C true w) +
        (b*c)*(L A false w*L D false w) + (a*d)*(L B true w*L C true w) +
        (a*c)*(L B true w*L D false w) + (a*b)*(L C true w*L D false w) +
        d*(L A false w*L B true w*L C true w) +
        c*(L A false w*L B true w*L D false w) +
        b*(L A false w*L C true w*L D false w) +
        a*(L B true w*L C true w*L D false w) +
        L A false w*L B true w*L C true w*L D false w := by ring
  change (𝔼 w, (a+L A false w)*(b+L B true w)*(c+L C true w)*(d+L D false w)) = _
  simp_rw [hp, Finset.expect_add_distrib, hscale, hlin, hquad, htri, hfour]
  simp
  ring
variable {m n : ℕ} {Ω : Type*} [Fintype Ω] [Nonempty Ω]

noncomputable def reduced (ψ : Fin m × Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft
    (vecMulVec ψ (star ψ))

private noncomputable def contracted (ψ : Fin m × Fin n → ℂ)
    (g : Fin m → ℂ) : Fin n → ℂ :=
  (star g) ᵥ* (fun i j => ψ (i,j))

omit [Nonempty Ω] in
private lemma average_projector (g : Ω → Fin m → ℂ)
    (h4 : ∀ i j k l, (𝔼 s, g s i * star (g s j) * g s k * star (g s l)) =
      (if i = j then 1 else 0) * (if k = l then 1 else 0) +
      (if i = l then 1 else 0) * (if k = j then 1 else 0))
    (ψ : Fin m × Fin n → ℂ) :
    (𝔼 s, vecMulVec (fun ij : Fin m × Fin n => g s ij.1 * contracted ψ (g s) ij.2)
      (star (fun ij : Fin m × Fin n => g s ij.1 * contracted ψ (g s) ij.2))) =
      vecMulVec ψ (star ψ) + (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ reduced ψ := by
  classical
  ext ⟨i,j⟩ ⟨k,l⟩
  have hentry (s : Ω) :
      (vecMulVec (fun ij : Fin m × Fin n => g s ij.1 * contracted ψ (g s) ij.2)
        (star (fun ij : Fin m × Fin n => g s ij.1 * contracted ψ (g s) ij.2)))
        (i,j) (k,l) = g s i * (∑ a, star (g s a) * ψ (a,j)) *
          (star (g s k) * ∑ b, g s b * star (ψ (b,l))) := by
    simp only [vecMulVec_apply, Pi.star_apply, contracted, Matrix.vecMul, dotProduct,
      star_sum, star_mul, star_star,
      mul_assoc, mul_left_comm, mul_comm]
  have hev (f : Ω → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
      (𝔼 s, f s) (i,j) (k,l) = 𝔼 s, f s (i,j) (k,l) := by
    simp only [Finset.expect, Matrix.smul_apply, Matrix.sum_apply]
  rw [hev]
  simp only [hentry, Matrix.add_apply, vecMulVec_apply, Pi.star_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, reduced,
    D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft]
  have hexpand (s : Ω) :
      g s i * (∑ a, star (g s a) * ψ (a,j)) *
        (star (g s k) * ∑ b, g s b * star (ψ (b,l))) =
      ∑ a, ∑ b, (g s i * star (g s a) * g s b * star (g s k)) *
        (ψ (a,j) * star (ψ (b,l))) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp_rw [hexpand, Finset.expect_sum_comm, ← Finset.expect_mul, h4]
  simp [add_mul, Finset.sum_add_distrib]

private lemma separable_expect (a : Ω → Fin m → ℂ) (b : Ω → Fin n → ℂ) :
    separableCone (𝔼 s, vecMulVec (fun ij : Fin m × Fin n => a s ij.1 * b s ij.2)
      (star (fun ij : Fin m × Fin n => a s ij.1 * b s ij.2))) := by
  have hs : separableCone (∑ s, vecMulVec (fun ij : Fin m × Fin n => a s ij.1 * b s ij.2)
      (star (fun ij : Fin m × Fin n => a s ij.1 * b s ij.2))) := by
    apply ContractionBlocks.separableCone_sum
    intro s
    rw [← D5.S3.Resource.CompositeConeDuality.kronecker_rank_one]
    exact D5.S3.Resource.SeparableConeResidualWitness.generator_separable
      ⟨vecMulVec (a s) (star (a s)), vecMulVec (b s) (star (b s)),
        posSemidef_vecMulVec_self_star _, posSemidef_vecMulVec_self_star _, rfl⟩
  convert separableCone_smul (c := (Fintype.card Ω : ℝ)⁻¹) (by positivity) hs using 1
  ext i j
  simp [Finset.expect, NNRat.smul_def, Complex.real_smul]

set_option maxHeartbeats 12000000 in
-- The entrywise fourth-moment expansion needs a larger elaboration budget.
private lemma high_average
    (g : Ω → Fin m → ℂ)
    (h1 : ∀ i s, (𝔼 w, chooseStar s (g w i)) = 0)
    (h2 : ∀ i j s t, (𝔼 w, chooseStar s (g w i) * chooseStar t (g w j)) =
      if s = t then 0 else if i = j then 1 else 0)
    (h3 : ∀ i j k s t u,
      (𝔼 w, chooseStar s (g w i) * chooseStar t (g w j) *
        chooseStar u (g w k)) = 0)
    (h4 : ∀ i j k l, (𝔼 w, g w i * star (g w j) * star (g w k) * g w l) =
      (if i = j then 1 else 0) * (if k = l then 1 else 0) +
      (if i = k then 1 else 0) * (if j = l then 1 else 0))
    (χ : Fin m × Fin n → ℂ) (u : Fin m → ℂ) (v : Fin n → ℂ) (a : ℝ)
    (P : Matrix (Fin m) (Fin m) ℂ) (hP : P.IsHermitian) (hPP : P * P = P)
    (hχ : ∀ j, P *ᵥ (fun i => χ (i, j)) = fun i => χ (i, j)) :
    let ψ : Fin m × Fin n → ℂ := fun ij => (a : ℂ) * u ij.1 * v ij.2 + χ ij
    let z (s : Ω) : Fin m × Fin n → ℂ := fun ij =>
      ((Real.sqrt 2 : ℂ) * (a : ℂ) * u ij.1 + (P *ᵥ g s) ij.1) *
        ((Real.sqrt 2 : ℂ)⁻¹ * v ij.2 + contracted χ (g s) ij.2)
    (𝔼 s, vecMulVec (z s) (star (z s))) = vecMulVec ψ (star ψ) +
      (P + ((2 * a ^ 2 : ℝ) : ℂ) • vecMulVec u (star u)) ⊗ₖ reduced χ +
      (1 / 2 : ℂ) • (P ⊗ₖ vecMulVec v (star v)) := by
  classical
  dsimp only
  let r : ℂ := (Real.sqrt 2 : ℂ)
  have hr : r ^ 2 = 2 := by
    dsimp [r]
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hr0 : r ≠ 0 := by intro h; rw [h] at hr; norm_num at hr
  have hrstar : star r = r := Complex.conj_ofReal _
  have hastar : star (a : ℂ) = (a : ℂ) := Complex.conj_ofReal a
  ext ⟨i,j⟩ ⟨k,l⟩
  have hev (f : Ω → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
      (𝔼 s, f s) (i,j) (k,l) = 𝔼 s, f s (i,j) (k,l) := by
    simp only [Finset.expect, Matrix.smul_apply, Matrix.sum_apply]
  rw [hev]
  have hentry (s : Ω) :
      vecMulVec (fun ij : Fin m × Fin n =>
        (r * (a : ℂ) * u ij.1 + (P *ᵥ g s) ij.1) *
          (r⁻¹ * v ij.2 + contracted χ (g s) ij.2))
        (star (fun ij : Fin m × Fin n =>
          (r * (a : ℂ) * u ij.1 + (P *ᵥ g s) ij.1) *
            (r⁻¹ * v ij.2 + contracted χ (g s) ij.2))) (i,j) (k,l) =
      (r * (a : ℂ) * u i + ∑ t, P i t * g s t) *
        (r⁻¹ * v j + ∑ t, χ (t,j) * star (g s t)) *
        (r * (a : ℂ) * star (u k) + ∑ t, star (P k t) * star (g s t)) *
        (r⁻¹ * star (v l) + ∑ t, star (χ (t,l)) * g s t) := by
    simp only [vecMulVec_apply, Pi.star_apply, contracted, Matrix.vecMul, Matrix.mulVec, dotProduct,
      star_add, star_mul, star_sum, star_star, star_inv₀, hrstar, hastar,
      mul_assoc, mul_comm]
  change (𝔼 s, vecMulVec (fun ij : Fin m × Fin n =>
        (r * (a : ℂ) * u ij.1 + (P *ᵥ g s) ij.1) *
          (r⁻¹ * v ij.2 + contracted χ (g s) ij.2))
        (star (fun ij : Fin m × Fin n =>
          (r * (a : ℂ) * u ij.1 + (P *ᵥ g s) ij.1) *
            (r⁻¹ * v ij.2 + contracted χ (g s) ij.2))) (i,j) (k,l)) = _
  have hentry_all := congrArg (fun f : Ω → ℂ => (𝔼 s, f s)) (funext hentry)
  rw [hentry_all]
  have hav := affine_wick (ι := Fin m) (Ω := Ω) g h1 h2 h3 h4
    (r * (a : ℂ) * u i) (r⁻¹ * v j)
    (r * (a : ℂ) * star (u k)) (r⁻¹ * star (v l))
    (fun t => P i t) (fun t => χ (t,j))
    (fun t => star (P k t)) (fun t => star (χ (t,l)))
  rw [hav]
  have hsχ : ∑ t, P i t * χ (t,j) = χ (i,j) := congrFun (hχ j) i
  have hsχstar : ∑ t, star (P k t) * star (χ (t,l)) = star (χ (k,l)) := by
    simpa only [Matrix.mulVec, dotProduct, star_sum, star_mul, mul_comm]
      using congrArg star (congrFun (hχ l) k)
  have hsP : ∑ t, P i t * star (P k t) = P i k := by
    calc
      _ = ∑ t, P i t * P t k := by
        apply Finset.sum_congr rfl
        intro t _
        rw [hP.apply t k]
      _ = P i k := by simpa only [Matrix.mul_apply] using congrFun (congrFun hPP i) k
  have hsrho : ∑ t, χ (t,j) * star (χ (t,l)) = reduced χ j l := rfl
  rw [hsχ, hsχstar, hsP, hsrho]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
    vecMulVec_apply, Pi.star_apply, star_add, star_mul, hastar,
    smul_eq_mul]
  have hri : r⁻¹ ^ 2 = (1 / 2 : ℂ) := by rw [inv_pow, hr]; norm_num
  have hab (x y : ℂ) : r * (a : ℂ) * x * (r⁻¹ * y) = (a : ℂ) * x * y := by
    calc _ = (r * r⁻¹) * ((a : ℂ) * x * y) := by ring
         _ = _ := by rw [mul_inv_cancel₀ hr0, one_mul]
  have hac (x y : ℂ) : r * (a : ℂ) * x * (r * (a : ℂ) * y) =
      ((2 * a ^ 2 : ℝ) : ℂ) * (x * y) := by
    calc _ = r ^ 2 * ((a : ℂ) ^ 2 * (x * y)) := by ring
         _ = _ := by rw [hr]; push_cast; ring
  have hbd (x y : ℂ) : r⁻¹ * x * (r⁻¹ * y) = (1 / 2 : ℂ) * (x * y) := by
    calc _ = r⁻¹ ^ 2 * (x * y) := by ring
         _ = _ := by rw [hri]
  rw [hab, hab, hac, hbd]
  ring


/-- Finite product-vector averaging separates a rank-one matrix plus its reduced matrix. -/
theorem separable_rankOne_add_reduced (ψ : Fin m × Fin n → ℂ) :
    separableCone
      (vecMulVec ψ (star ψ) + (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ reduced ψ) := by
  let g : (Fin m → Fin 8) → Fin m → ℂ := fun s i => omega8 (s i)
  obtain ⟨_,_,_,h4⟩ := omega_moments (ι := Fin m)
  have hi := average_projector g h4 ψ
  rw [← hi]
  exact separable_expect g (fun s => contracted ψ (g s))

/-- A projected finite product-vector average includes a prescribed product component. -/
theorem separable_projected_rankOne
    (χ : Fin m × Fin n → ℂ) (u : Fin m → ℂ) (v : Fin n → ℂ) (a : ℝ)
    (P : Matrix (Fin m) (Fin m) ℂ) (hP : P.IsHermitian) (hPP : P * P = P)
    (hχ : ∀ j, P *ᵥ (fun i => χ (i, j)) = fun i => χ (i, j)) :
    let ψ : Fin m × Fin n → ℂ := fun ij => (a : ℂ) * u ij.1 * v ij.2 + χ ij
    separableCone (vecMulVec ψ (star ψ) +
      (P + ((2 * a ^ 2 : ℝ) : ℂ) • vecMulVec u (star u)) ⊗ₖ reduced χ +
      (1 / 2 : ℂ) • (P ⊗ₖ vecMulVec v (star v))) := by
  let g : (Fin m → Fin 8) → Fin m → ℂ := fun s i => omega8 (s i)
  obtain ⟨h1,h2,h3,h4⟩ := omega_moments (ι := Fin m)
  have h1' : ∀ i s, (𝔼 w, chooseStar s (g w i)) = 0 := by
    simpa only [g, signedOmega] using h1
  have h2' : ∀ i j s t, (𝔼 w, chooseStar s (g w i) * chooseStar t (g w j)) =
      if s = t then 0 else if i = j then 1 else 0 := by
    simpa only [g, signedOmega] using h2
  have h3' : ∀ i j k s t u,
      (𝔼 w, chooseStar s (g w i) * chooseStar t (g w j) *
        chooseStar u (g w k)) = 0 := by
    simpa only [g, signedOmega] using h3
  have h4' : ∀ i j k l, (𝔼 w, g w i * star (g w j) * star (g w k) * g w l) =
      (if i = j then 1 else 0) * (if k = l then 1 else 0) +
      (if i = k then 1 else 0) * (if j = l then 1 else 0) := by
    intro i j k l
    convert h4 i j l k using 1
    · congr 1; ext s; dsimp [g]; ring
    · simp only [eq_comm]
  have hi := high_average g h1' h2' h3' h4' χ u v a P hP hPP hχ
  dsimp only at hi ⊢
  rw [← hi]
  exact separable_expect
    (fun s i => (Real.sqrt 2 : ℂ) * (a : ℂ) * u i + (P *ᵥ g s) i)
    (fun s j => (Real.sqrt 2 : ℂ)⁻¹ * v j + contracted χ (g s) j)

#print axioms separable_rankOne_add_reduced
#print axioms separable_projected_rankOne

end D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRaysAverages
