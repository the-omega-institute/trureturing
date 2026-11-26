import GRH.Lib.CM.Genus.QuadraticZeta
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Heights of families indexed by ℓ-adic embeddings; product formula. A height bound is defined,
through one auxiliary nonzero number, for families of complex numbers indexed by the isomorphisms of
C with an algebraic closure of Q_ℓ; bounds add in products and any bound for the constant family 1
is nonnegative (product formula). The product formula through a
norm and adelic norms changed place by place are standard. Related work: Gaudron, Pentes des fibrés
vectoriels adéliques, 2006; Bombieri–Gubler, Heights in Diophantine Geometry, ch. 1, 2006; K.
Conrad, Zorn's lemma and some applications II, notes.

This file: Heights of families indexed by ℓ-adic embeddings: additivity and product formula. -/

open Filter Finset IntermediateField Module Real AdjoinSimple

/-- The pairs of a prime l and a field isomorphism ι from ℂ to the algebraic closure of ℚ_l;
families of complex numbers are indexed by them. -/
abbrev PrimePadicIso := Σ l : Nat.Primes, ℂ ≃+* PadicAlgCl l

/-- The family y has height at most c: some H ≠ 0 and reals α, e_l have |σH| ≤ exp α for σ ∈ Aut
ℂ, |ι(H·y_ι)| ≤ exp e_l for ι : ℂ ≅ ℚ̄_l, and α + Σ_{primes l<M} e_l ≤ c for all large M. -/
def HeightLe c (y : _ → ℂ) := ∃ᵉ (H) (α) (e : ℕ → ℝ), H ≠ 0 ∧ (∀ σ : ℂ ≃+* ℂ, ‖σ H‖ ≤ α.exp) ∧
  (∀ ι : PrimePadicIso, ‖ι.2 (H * y ι)‖ ≤ (e ι.1).exp) ∧ ∀ᶠ M in atTop,
  α + ∑ l ∈ range M with l.Prime, e l ≤ c

/-- The product formula for ℚ, in logarithms: for a rational q ≠ 0 whose numerator (in absolute
value) and denominator are less than M, log |q| plus the sum of log |q|_p over the primes p
< M is zero. -/
lemma log_product_formula {M} {q : ℚ} (h : q.num.natAbs ⊔ q.den < M) : log q + ∑ p ∈ range M with
  p.Prime, log (padicNorm p q) = 0 := have := (congr(log $(Nat.prod_pow_prime_padicValNat · · M ·)))
  by by_cases q = 0 <;> simp_all [log_prod, padicValRat, padicValInt, sub_mul, q.cast_def, log_div]

variable {c c' : ℝ} {y y' : PrimePadicIso → ℂ}

/-- Monotonicity of the height: if the family y has height at most c, c ≤ c', and |ι(y'_ι)| ≤
|ι(y_ι)| for every prime l and ι : ℂ ≅ ℚ̄_l, then y' has height at most c'. -/
lemma HeightLe.mono (h : HeightLe c y) (hc : c ≤ c') (hy : ∀ ι :
  PrimePadicIso, ‖ι.2 (y' ι)‖ ≤ ‖ι.2 (y ι)‖) : HeightLe c' y' := h.imp fun _ ↦ by gcongr; aesop

/-- If reals e_l have sum at most c over every finite set of primes, and |ι(y_ι)| ≤ exp(e_l) for
every prime l and isomorphism ι of ℂ with the algebraic closure of ℚ_l, then the family y
has height at most c. -/
lemma HeightLe.of_le {e : ℕ → ℝ} (he : ∀ T, (∀ l ∈ T, l.Prime) → ∑ l ∈ T, e l ≤ c)
    (h : ∀ ι : PrimePadicIso, ‖ι.2 (y ι)‖ ≤ exp (e ι.1)) : HeightLe c y := ⟨1, 0, e, by aesop⟩

/-- Subadditivity of the height: if the families y and y' have heights at most c and c', then their
pointwise product yy' has height at most c + c'. -/
lemma HeightLe.mul : HeightLe c y → HeightLe c' y' → HeightLe (c + c') (y * y') :=
  fun ⟨H, α, e, a⟩ ⟨K, β, f, b⟩ ↦
  ⟨H * K, α + β, e + f, by simp_all [exp_add, mul_le_mul, exp_nonneg, mul_mul_mul_comm H K]
                           use a.2.2.2.choose + b.2.2.2.choose; grind⟩

/-- Height bounds add in finite products: if y_i has height at most c_i for each i in a finite
set s, then ∏_{i∈s} y_i has height at most ∑_{i∈s} c_i. -/
lemma HeightLe.prod {ι s} {c y : ι → _} (h : ∀ i ∈ s, HeightLe (c i) (y i)) : HeightLe (∑ i ∈ s,
  c i) (∏ i ∈ s, y i) := by induction s using cons_induction <;> simp_all [mul, @of_le _ _ 0]

/-- If the family y has height at most c, then for every natural number n the family yⁿ, with
terms y_ι^n, has height at most n·c. -/
lemma HeightLe.pow (h : HeightLe c y) (n : ℕ) : HeightLe (n * c) (y ^ n) := by
  simpa using prod (s := Iio n) fun _ _ ↦ h

/-- Product formula: if the constant family 1 has height at most c, then c ≥ 0.

Heights of families indexed by ℓ-adic embeddings; product formula. -/
lemma HeightLe.nonneg (h : HeightLe c 1) : 0 ≤ c := by
  choose H _ _ d _ f _ g using by simpa [HeightLe] using h
  have := @NumberField.mk _ _ _ (adjoin.finiteDimensional (isAlgebraic_of_padic
    (by simpa using f ⟨default, ·⟩)).isIntegral)
  have k {F c} [NormedField F] [CharZero F] [IsAlgClosed F] (e : _ = _) (h : ∀ ι : _ ≃+* F, ‖ι H‖ ≤
      exp c) := show ‖algebraMap ℚ F (Algebra.norm ℚ (gen ℚ H))‖.log / finrank ℚ ℚ⟮H⟯ ≤ c by grw [
    Algebra.norm_eq_prod_embeddings, norm_prod, prod_le_prod₀ _ fun σ _ ↦
    (exists_ringEquiv_extend e ℚ⟮H⟯.val
    σ.1).choose_spec ⟨H, _⟩ ▸ h _] <;> simp_all [finrank_pos.ne', prod_pos, Subtype.ext_iff]
  grw [← g _ le_self_add, ← k rfl d, ← sum_le_sum fun l h ↦ @Padic.eq_padicNorm l .. ▸
    @PadicAlgCl.norm_extends .. ▸ k (@mk_complex_eq_mk_padicAlgCl ..)
    (f ⟨⟨l, (mem_filter.1 h).2⟩, ·⟩)]
  simp [← sum_div, field]; rw [log_product_formula (Nat.le_add_left ..), zero_div]
