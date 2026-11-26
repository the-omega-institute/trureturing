import GRH.New.TwistedHecke.TwistingData
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Dimension bounds mod p from flags and a cone volume (see New.TwistedHecke.Counting).

This file: A form deep in every frame has a monomial of large cost. -/

open Finset Finsupp Fintype Ideal MatMul Matrix MvPolynomial

variable {N k W K} [NeZero N] [CommRing W] [IsLocalRing W] [Field K] (T : TwistingData N W K)

/-- For every r and every index b, the variable (b,s) is deep for exactly half of the letters s
in ℤ/N: the sum over s of `TwistingData.deepIndicator` at (b,s) is N/2. -/
lemma TwistingData.sum_deepIndicator r (b : Fin k) : ∑ s, T.deepIndicator r (b, s) = N / 2 :=
  Nat.eq_div_of_mul_eq_right
  nofun (by nth_rw 1 [two_mul, ← sum_translate (-1), ← sum_add_distrib, sum_const_nat,
  mul_one] <;> simp; grind [deepIndicator, isEven_succ])

/-- Let char K = p, 2r ≤ k, 2r < N. A non-zero F in `TwistingData.deepForms` has a monomial of
weight ≥ τ, deep variables (b,s) weighing P^{−2r} if b ≥ 2r (b from 0), 1/P otherwise, the others
0. -/
lemma TwistingData.exists_le_weight_of_mem_deepForms [CharP K T.p] {n r τ F} (hk : 2 * r ≤
  k) (hN : 2 * r < N) (hF : F ∈ T.deepForms k n r τ) (F0 : F ≠ 0) : ∃ β, F β ≠ 0 ∧ τ ≤
  (exponentOf β).weight fun x ↦ (T.deepIndicator r x / T.P ^ ite (2 * r ≤ x.1) (2 * r) 1 : ℝ) := by
  choose J hJ using fun i b ↦ show ∃ j : ℕ, j / 2 = b ∧ T.isEven (i - j) by by_contra! h; grind
    [T.isEven_succ (i - 2 * b - 1), sub_add_cancel, sub_sub, h (2 * b), h (2 * b + 1)]
  obtain ⟨p, _, _, m, e⟩ := T.prime.pos, @ofFinite _ T.finite_residueField, Fact.mk T.prime, hk.dest
  -- `x` maps to the field of rational functions; the variable `v` costs `1 / κ v` there.
  let R := MvPolynomial (Fin k × ZMod N) K
  let x := algebraMap R (FractionRing R)
  let κ v := T.P ^ (T.deepIndicator (k := k) r v * ite (2 * r ≤ v.1) (2 * r) 1)
  -- Points: the entries of `A` sit at the places `(ρ t, σ t)`, and `z y` is the point of `A = y`.
  let I := Fin r ×ₗ Fin (m + 1)
  let ρ (t : I) : Fin k := ⟨t.1, by lia⟩
  let σ (t : I) : Fin k := ⟨ite (t.2 = 0) (t.1 + r) (k - t.2), by lia⟩
  let c v t : R := ite (T.rootVar (ρ t) (σ t) v.2 =
    v) (X (T.rootVar (σ t) (ρ t) v.2)) 0 * ite (T.isEven v.2) 1 (-1)
  let a i (y : I → IsLocalRing.ResidueField W) t := x (C (T.ι i (y t).out))
  let z y v := a v.2 y ⬝ᵥ x ∘ c v
  have hz v (j : ℕ) y : x ∘ c v ^ T.P ^ j ⬝ᵥ a (v.2 + j) y = z y v ^ T.P ^ j := by
    erw [dotProduct_comm, ← pow_mul, sum_pow_char_pow]; simp [a, dotProduct, pow_mul, mul_pow,
      by simpa [CharP.cast_eq_zero] using T.frobenius_pow_congr j v.2]
  -- Equations: each linear form in `A` is the value of a polynomial with terms of cost below `1`.
  have entry i u : ∃ g, (∀ α ∈ g.support, weight (κ · : _ → ℝ)⁻¹ α < 1) ∧
      ∀ y, eval (z y) g = u ⬝ᵥ a i y := by
    let j (t : I) := ite (t.2 = 0) 0 (J i t.1)
    let v t := T.rootVar (ρ t) (σ t) (i - j t)
    -- the system is invertible, as a specialisation makes it triangular
    obtain ⟨w, rfl⟩ := (x.mapMatrix (of fun t ↦ c (v t) ^ T.P ^ j t)).vecMul_surjective_iff_isUnit.2
      (by clear * - p hJ hN
          simp [↓isUnit_iff_isUnit_det, ↓← x.map_det, x, R]
          apply ne_of_apply_ne (eval fun v ↦ 0 ^ ((i - v.2).val / 2 - v.1))
          rw [RingHom.map_det, det_of_isUpperTriangular fun _ _ ↦ ?_ ∘ Prod.lex_def.1] <;> simp [c,
            v, rootVar, univ.prod_eq_zero_iff, apply_ite (eval _),
            @Nat.mod_eq_of_lt (j _) N (by grind)] <;> grind [pow_eq_zero_iff']) u
    use ∑ t, w t • X (v t) ^ T.P ^ j t, fun α h ↦ ?_, fun y ↦ by
      simpa [← hz, v, Matrix.map] using! dotProduct_mulVec ..
    obtain ⟨t, rfl, -⟩ := by simpa [coeff_X_pow] using support_sum h
    simp [weight_single, field, κ, -mul_ite]; clear * - hJ; gcongr <;> grind [rootVar,
      deepIndicator, one_lt_P]
  -- Read the forms over that field, as polynomials in the deep variables.
  let ι := eval₂Hom (C.comp (x.comp C)) fun v ↦ ite (T.deepIndicator r v = 0) (C (x (X v))) (X v)
  have ⟨α, h, H⟩ := exists_le_cost_of_vanishing κ (by bound) z (fun y y' h ↦ funext fun t ↦
    (entry 0 (Pi.single t 1)).elim fun _ hf ↦ (y t).out_eq ▸ (y' t).out_eq ▸ Ideal.Quotient.eq.2
    (mt (·.map (T.ι 0)) (by simpa [← h, hf, a, x, R] using hf.2 y'))) ?_ (fun _ ↦ by simp only [κ,
    ← hz, entry]) τ (ι (polyOfCoeffs F)) (fun h ↦
    F0 (by ext β; simpa [polyOfCoeffs, coeff_sum] using congrArg (·.coeff (exponentOf β)) (by
           simpa [h, x] using congr(($(show x = .comp (eval (x ∘ X)) ι by
           ext <;> simp [ι, apply_ite])) (polyOfCoeffs F)) : polyOfCoeffs F = 0))) fun y ↦ ?_
  -- A costly monomial of `ι F` comes from a costly monomial of `F`.
  simp [polyOfCoeffs, coeff_sum, ι, prod_fintype, prod_ite, ← map_pow, ← map_prod,
    coeff_prod_X_pow] at h
  obtain ⟨β, rfl, h, -⟩ := by simpa [x] using exists_ne_zero_of_sum_ne_zero h
  use β, h, H.trans (by simp [weight_eq_sum, κ, deepIndicator]; bound)
  -- The number of points.
  subst e
  grw [card_fun, card_eq_nat_card, T.card_residueField, ← pow_mul, ← N.div_mul_le_self 2,
    prod_pow_eq_pow_sum, pow_le_pow_right₀] <;> simp [I, ↓sum_prod_type, ← univ.sum_mul,
    sum_deepIndicator, Fin.sum_univ_add, ← Nat.not_lt, -not_lt] <;> lia
  -- The order of vanishing: `F` is the translate of `g F` by `g⁻¹ = 1 - A`.
  let A := ∑ t, Matrix.single (ρ t) (σ t) (y t).out
  let g : GL _ W := by use 1 + A, 1 + -A <;> simp (disch := lia) [A, univ.sum_mul_sum]
  rw [show F = T.letterRep n g⁻¹ *ᵥ T.letterRep n g *ᵥ F by simp [← map_mul],
    ← polyAction_polyOfCoeffs]
  simp [polyOfCoeffs, monomial_eq]
  refine sum_mem fun β _ ↦ (le_or_gt ..).elim
    (pow_le_pow_right · (mul_mem_left _ _ ?_)) (hF g nofun β · ▸ by simp)
  simp [depth, weight_eq_sum, ← prod_pow_eq_pow_sum, pow_mul']
  refine prod_mem_prod fun v _ ↦ pow_mem_pow ?_ _
  by_cases T.isEven v.2 <;> by_cases r ≤ v.1 <;> simp [polyAction_X, letterMatrix_apply, g, A, c,
    rootVar, ι, z, a, add_mul, univ.sum_mul, Matrix.sum_apply, Matrix.single, ite_and,
    @Finset.sum_comm I, deepIndicator, *, dotProduct,
    apply_ite (DFunLike.coe _), -coe_eval₂Hom, show ∀ t, ¬r ≤ ρ t ∧ r ≤ σ t by lia, Prod.ext_iff]
