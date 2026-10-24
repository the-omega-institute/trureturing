/- GID: D5/S3/Quantum/Information/CommutingEncodingReflectionClass
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/CommutingEncodingReflectionClass
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Commuting product and reflection encodings give the same qubit state class. -/

import D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm

/-! Commuting qubit product encodings and their local-reflection replacements. -/

open scoped BigOperators
open Matrix
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm (tensor_adj tensor_unitary)

namespace D5.S3.Quantum.Information.CommutingEncodingReflectionClass

/-- A complete orthonormal orbit under pairwise commuting product unitaries. -/
def IsCommutingProductEncoding {n : ℕ} (ψ : (Fin n → Fin 2) → ℂ)
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  (∀ a j, U a j ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧
  (∀ a b, tensorOp (U a) * tensorOp (U b) = tensorOp (U b) * tensorOp (U a)) ∧
  (∀ a b, ∑ x, star ((tensorOp (U a) *ᵥ ψ) x) * (tensorOp (U b) *ᵥ ψ) x =
    if a = b then 1 else 0)

/-- A commuting product encoding whose individual qubit factors are Hermitian involutions. -/
def IsCommutingReflectionEncoding {n : ℕ} (ψ : (Fin n → Fin 2) → ℂ)
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  IsCommutingProductEncoding ψ U ∧
  (∀ a j, (U a j).IsHermitian ∧ U a j * U a j = 1)

/-- Arbitrary local unitary factors give the same commuting encoding class as reflections. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ ψ : (Fin n → Fin 2) → ℂ,
    (∑ x, ‖ψ x‖ ^ 2 = 1) →
    ((∃ U, IsCommutingProductEncoding ψ U) ↔
      (∃ U, IsCommutingReflectionEncoding ψ U))

private lemma tensor_factors_proportional {n : ℕ}
    (X Y : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (h : tensorOp X = tensorOp Y) (hne : tensorOp X ≠ 0) :
    ∀ j, ∃ c : ℂ, Y j = c • X j := by
  classical
  obtain ⟨x, y, hxy⟩ : ∃ x y, tensorOp X x y ≠ 0 := by
    by_contra! hz
    apply hne
    ext x y
    exact hz x y
  have hY : (∏ i, Y i (x i) (y i)) ≠ 0 := by
    change tensorOp Y x y ≠ 0
    rwa [← h]
  intro j
  have hrest : (∏ i ∈ Finset.univ.erase j, Y i (x i) (y i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ =>
      Finset.prod_ne_zero_iff.mp hY i (Finset.mem_univ i)
  have entry (Z : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (r t : Fin 2) :
      tensorOp Z (Function.update x j r) (Function.update y j t) =
        Z j r t * ∏ i ∈ Finset.univ.erase j, Z i (x i) (y i) := by
    dsimp only [tensorOp, Matrix.of_apply]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    simp only [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi),
      Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  refine ⟨(∏ i ∈ Finset.univ.erase j, X i (x i) (y i)) /
    (∏ i ∈ Finset.univ.erase j, Y i (x i) (y i)), ?_⟩
  ext r t
  have he := congrFun (congrFun h (Function.update x j r)) (Function.update y j t)
  rw [entry, entry] at he
  change Y j r t = _ * X j r t
  rw [div_mul_eq_mul_div, eq_div_iff hrest, mul_comm _ (X j r t)]
  exact he.symm

private lemma local_commutation_signs {n : ℕ}
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ a j, U a j ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hc : ∀ a b, tensorOp (U a) * tensorOp (U b) =
      tensorOp (U b) * tensorOp (U a)) :
    ∀ a b j, U a j * U b j = U b j * U a j ∨
      U a j * U b j = -(U b j * U a j) := by
  classical
  intro a b j
  have hunit : tensorOp (fun i => U a i * U b i) ∈
      Matrix.unitaryGroup (Fin n → Fin 2) ℂ :=
    tensor_unitary _ fun i => (Matrix.unitaryGroup (Fin 2) ℂ).mul_mem (hU a i) (hU b i)
  have hne : tensorOp (fun i => U a i * U b i) ≠ 0 := by
    intro hz
    have hi := hunit.1
    rw [hz, star_zero, zero_mul] at hi
    exact zero_ne_one hi
  have heq : tensorOp (fun i => U a i * U b i) =
      tensorOp (fun i => U b i * U a i) := by
    simpa only [tensor_mul] using hc a b
  obtain ⟨c, he⟩ := tensor_factors_proportional _ _ heq hne j
  have hdet : (U a j * U b j).det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero (Matrix.det_ne_zero_of_left_inverse (hU a j).1)
      (Matrix.det_ne_zero_of_left_inverse (hU b j).1)
  have hc2 : c ^ 2 = 1 := by
    have hd := congrArg Matrix.det he
    rw [Matrix.det_smul, Fintype.card_fin, Matrix.det_mul_comm (U b j)] at hd
    apply mul_right_cancel₀ hdet
    simpa only [one_mul] using hd.symm
  rcases sq_eq_one_iff.mp hc2 with rfl | rfl
  · left
    simpa using he.symm
  · right
    simpa using (congrArg Neg.neg he).symm

private lemma spectral_frame_of_local_signs {n : ℕ} (hn : 1 ≤ n)
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ a j, U a j ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hc : ∀ a b, tensorOp (U a) * tensorOp (U b) =
      tensorOp (U b) * tensorOp (U a))
    (hs : ∀ a b j, U a j * U b j = U b j * U a j ∨
      U a j * U b j = -(U b j * U a j)) :
    ∃ (F : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
      (eig : Fin (2 ^ n) → (Fin n → Fin 2) → ℂ)
      (R : (Fin n → Fin 2) → Fin n → Matrix (Fin 2) (Fin 2) ℂ),
      F ∈ Matrix.unitaryGroup (Fin n → Fin 2) ℂ ∧
      (∀ a x, star (eig a x) * eig a x = 1) ∧
      (∀ a, Fᴴ * tensorOp (U a) * F = diagonal (eig a)) ∧
      (∀ a j, (R a j).IsHermitian ∧ R a j * R a j = 1) ∧
      (∀ a, Fᴴ * tensorOp (R a) * F =
        diagonal (fun x => ∏ j, (-1 : ℂ) ^ ((a j).val * (x j).val))) := by
  sorry

private lemma uniform_weights {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℂ) (eig : ι → ι → ℂ)
    (heig : ∀ a x, star (eig a x) * eig a x = 1)
    (ho : ∀ a b, ∑ x, star (c x * eig a x) * (c x * eig b x) =
      if a = b then 1 else 0) :
    ∀ x, (Fintype.card ι : ℂ) * (star (c x) * c x) = 1 := by
  classical
  let M : Matrix ι ι ℂ := fun x a => c x * eig a x
  have hcol : Mᴴ * M = 1 := by
    ext a b
    exact ho a b
  have hrow : M * Mᴴ = 1 := mul_eq_one_comm.mp hcol
  intro x
  have hx := congrFun (congrFun hrow x) x
  rw [Matrix.one_apply_eq] at hx
  change (∑ a, (c x * eig a x) * star (c x * eig a x)) = 1 at hx
  have he (a : ι) : (c x * eig a x) * star (c x * eig a x) = star (c x) * c x := by
    rw [star_mul]
    calc
      _ = (star (c x) * c x) * (star (eig a x) * eig a x) := by ring
      _ = _ := by rw [heig a x, mul_one]
  simpa only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hx

private lemma flat_of_diagonal_encoding {n : ℕ}
    (ψ : (Fin n → Fin 2) → ℂ)
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : IsCommutingProductEncoding ψ U)
    (F : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (hF : F ∈ Matrix.unitaryGroup (Fin n → Fin 2) ℂ)
    (eig : Fin (2 ^ n) → (Fin n → Fin 2) → ℂ)
    (heig : ∀ a x, star (eig a x) * eig a x = 1)
    (hd : ∀ a, Fᴴ * tensorOp (U a) * F = diagonal (eig a)) :
    ∀ x, (2 ^ n : ℂ) * (star ((Fᴴ *ᵥ ψ) x) * (Fᴴ *ᵥ ψ) x) = 1 := by
  classical
  let e : (Fin n → Fin 2) ≃ Fin (2 ^ n) :=
    Fintype.equivFinOfCardEq (by simp [Fintype.card_fun])
  let c := Fᴴ *ᵥ ψ
  have hFF : F * Fᴴ = 1 := hF.2
  have he (a : Fin (2 ^ n)) :
      Fᴴ *ᵥ (tensorOp (U a) *ᵥ ψ) = fun x => c x * eig a x := by
    calc
      _ = (Fᴴ * tensorOp (U a) * F) *ᵥ c := by
        dsimp only [c]
        simp only [← Matrix.mulVec_mulVec]
        rw [Matrix.mulVec_mulVec ψ F Fᴴ, hFF, Matrix.one_mulVec]
      _ = _ := by
        rw [hd a]
        ext x
        simp [Matrix.mulVec, dotProduct, Matrix.diagonal, mul_comm]
  have hp (v w : (Fin n → Fin 2) → ℂ) :
      (∑ x, star ((Fᴴ *ᵥ v) x) * (Fᴴ *ᵥ w) x) = ∑ x, star (v x) * w x := by
    change star (Fᴴ *ᵥ v) ⬝ᵥ (Fᴴ *ᵥ w) = star v ⬝ᵥ w
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      Matrix.conjTranspose_conjTranspose, hFF, Matrix.vecMul_one]
  have hw := uniform_weights c (fun a => eig (e a)) (fun a x => heig (e a) x) (by
    intro a b
    calc
      _ = ∑ x, star ((Fᴴ *ᵥ (tensorOp (U (e a)) *ᵥ ψ)) x) *
          (Fᴴ *ᵥ (tensorOp (U (e b)) *ᵥ ψ)) x := by rw [he, he]
      _ = if e a = e b then 1 else 0 := (hp _ _).trans (hU.2.2 (e a) (e b))
      _ = _ := by simp only [e.injective.eq_iff])
  simpa [c, Fintype.card_fun] using hw

private lemma character_orthogonality {n : ℕ} (a b : Fin n → Fin 2) :
    (∑ x : Fin n → Fin 2,
      (∏ j, (-1 : ℂ) ^ ((a j).val * (x j).val)) *
        (∏ j, (-1 : ℂ) ^ ((b j).val * (x j).val))) =
      if a = b then (2 ^ n : ℂ) else 0 := by
  classical
  have one_site (r t : Fin 2) :
      (∑ z : Fin 2, (-1 : ℂ) ^ (r.val * z.val) * (-1 : ℂ) ^ (t.val * z.val)) =
        if r = t then 2 else 0 := by
    fin_cases r <;> fin_cases t <;> norm_num [Fin.sum_univ_two]
  calc
    _ = ∏ j, ∑ z : Fin 2,
        (-1 : ℂ) ^ ((a j).val * z.val) * (-1 : ℂ) ^ ((b j).val * z.val) := by
      rw [Fintype.prod_sum]
      simp_rw [Finset.prod_mul_distrib]
    _ = ∏ j, if a j = b j then (2 : ℂ) else 0 := by simp_rw [one_site]
    _ = _ := by
      by_cases hab : a = b
      · subst b
        simp
      · rw [if_neg hab]
        obtain ⟨j, hj⟩ := Function.ne_iff.mp hab
        exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

private lemma reflection_encoding_of_flat_frame {n : ℕ}
    (ψ : (Fin n → Fin 2) → ℂ)
    (F : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (hF : F ∈ Matrix.unitaryGroup (Fin n → Fin 2) ℂ)
    (R : (Fin n → Fin 2) → Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hR : ∀ a j, (R a j).IsHermitian ∧ R a j * R a j = 1)
    (hd : ∀ a, Fᴴ * tensorOp (R a) * F =
      diagonal (fun x => ∏ j, (-1 : ℂ) ^ ((a j).val * (x j).val)))
    (hf : ∀ x, (2 ^ n : ℂ) * (star ((Fᴴ *ᵥ ψ) x) * (Fᴴ *ᵥ ψ) x) = 1) :
    ∃ U, IsCommutingReflectionEncoding ψ U := by
  classical
  let e : Fin (2 ^ n) ≃ (Fin n → Fin 2) :=
    (Fintype.equivFinOfCardEq (by simp [Fintype.card_fun])).symm
  let c := Fᴴ *ᵥ ψ
  let χ (a x : Fin n → Fin 2) : ℂ := ∏ j, (-1 : ℂ) ^ ((a j).val * (x j).val)
  have hFF : F * Fᴴ = 1 := hF.2
  have hFtF : Fᴴ * F = 1 := hF.1
  have hN : (2 ^ n : ℂ) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hw (x) : star (c x) * c x = 1 / (2 ^ n : ℂ) := by
    apply (eq_div_iff hN).mpr
    simpa [c, mul_comm] using hf x
  have hs (a x) : star (χ a x) = χ a x := by simp [χ]
  have he (a : Fin n → Fin 2) :
      Fᴴ *ᵥ (tensorOp (R a) *ᵥ ψ) = fun x => c x * χ a x := by
    calc
      _ = (Fᴴ * tensorOp (R a) * F) *ᵥ c := by
        dsimp only [c]
        simp only [← Matrix.mulVec_mulVec]
        rw [Matrix.mulVec_mulVec ψ F Fᴴ, hFF, Matrix.one_mulVec]
      _ = _ := by
        rw [hd a]
        ext x
        simp [Matrix.mulVec, dotProduct, Matrix.diagonal, χ, mul_comm]
  have hp (v w : (Fin n → Fin 2) → ℂ) :
      (∑ x, star ((Fᴴ *ᵥ v) x) * (Fᴴ *ᵥ w) x) = ∑ x, star (v x) * w x := by
    change star (Fᴴ *ᵥ v) ⬝ᵥ (Fᴴ *ᵥ w) = star v ⬝ᵥ w
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      Matrix.conjTranspose_conjTranspose, hFF, Matrix.vecMul_one]
  have horth (a b : Fin n → Fin 2) :
      (∑ x, star ((tensorOp (R a) *ᵥ ψ) x) * (tensorOp (R b) *ᵥ ψ) x) =
        if a = b then 1 else 0 := by
    rw [← hp, he, he]
    have hm (x) : star (c x * χ a x) * (c x * χ b x) =
        (1 / (2 ^ n : ℂ)) * (χ a x * χ b x) := by
      rw [star_mul, hs]
      calc
        _ = (star (c x) * c x) * (χ a x * χ b x) := by ring
        _ = _ := by rw [hw]
    simp_rw [hm]
    rw [← Finset.mul_sum]
    have hsum : (∑ x : Fin n → Fin 2, χ a x * χ b x) =
        if a = b then (2 ^ n : ℂ) else 0 := character_orthogonality a b
    rw [hsum]
    by_cases hab : a = b <;> simp [hab, hN]
  have hi (a : Fin n → Fin 2) : tensorOp (R a) = F * diagonal (χ a) * Fᴴ := by
    have h := congrArg (fun A => F * A * Fᴴ) (hd a)
    have hu (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
        F * (Fᴴ * A * F) * Fᴴ = A := by
      calc
        _ = (F * Fᴴ) * A * (F * Fᴴ) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hFF, Matrix.one_mul, Matrix.mul_one]
    rw [hu] at h
    exact h
  have hprod (d g : (Fin n → Fin 2) → ℂ) :
      (F * diagonal d * Fᴴ) * (F * diagonal g * Fᴴ) =
        F * (diagonal d * diagonal g) * Fᴴ := by
    calc
      _ = F * diagonal d * (Fᴴ * F) * diagonal g * Fᴴ := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hFtF, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  refine ⟨fun a => R (e a), ⟨?_, ?_, ?_⟩, fun a j => hR (e a) j⟩
  · intro a j
    apply Matrix.mem_unitaryGroup_iff'.mpr
    change (R (e a) j)ᴴ * R (e a) j = 1
    rw [(hR (e a) j).1.eq]
    exact (hR (e a) j).2
  · intro a b
    rw [hi, hi, hprod, hprod, (Matrix.commute_diagonal (χ (e a)) (χ (e b))).eq]
  · intro a b
    simpa only [e.injective.eq_iff] using horth (e a) (e b)

private lemma product_encoding_to_reflections {n : ℕ} (hn : 1 ≤ n)
    (ψ : (Fin n → Fin 2) → ℂ)
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : IsCommutingProductEncoding ψ U) :
    ∃ R, IsCommutingReflectionEncoding ψ R := by
  obtain ⟨F, eig, R, hF, heig, hd, hR, hRd⟩ :=
    spectral_frame_of_local_signs hn U hU.1 hU.2.1
      (local_commutation_signs U hU.1 hU.2.1)
  exact reflection_encoding_of_flat_frame ψ F hF R hR hRd
    (flat_of_diagonal_encoding ψ U hU F hF eig heig hd)

private lemma reflection_encoding_to_product {n : ℕ}
    (ψ : (Fin n → Fin 2) → ℂ)
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : IsCommutingReflectionEncoding ψ U) : IsCommutingProductEncoding ψ U :=
  hU.1

/-- Commuting product encodings admit commuting local-reflection replacements. -/
theorem result : claim := by
  intro n hn ψ _hψ
  constructor
  · rintro ⟨U, hU⟩
    exact product_encoding_to_reflections hn ψ U hU
  · rintro ⟨U, hU⟩
    exact ⟨U, reflection_encoding_to_product ψ U hU⟩

end D5.S3.Quantum.Information.CommutingEncodingReflectionClass
