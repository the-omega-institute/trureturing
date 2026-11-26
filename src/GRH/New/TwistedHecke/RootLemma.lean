import GRH.New.TwistedHecke.ClassMeans
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! A term least in all frames obeys Frobenius inequalities. When a Levi group acts on polynomials
in a circle of variable sets by Frobenius twists and inverse transposes in turn, a term least for
valuation plus a suitable weight among all translates has exponents obeying linear inequalities
(Stepanov's count of zeros against degree), which are used to bound the Hecke operator's divisors.
Twisted Dickson forms on Frobenius twists of symmetric powers, weight inequalities via the Lang map
and counts of zeros against degree are known. Related work: Ghate–Jana, Modular representations of
GL2(F_q) using calculus, 2025; Imai–Koskivirta, Automorphic vector bundles on the stack of G-zips,
2021; Bombieri, Counting points on curves over finite fields, Sém. Bourbaki 430, 1973.

General lemmas of commutative and general algebra (textbook or folklore).

This file: Root lemma: a term least in all frames obeys Frobenius inequalities; Gauss
filtrations. -/

attribute [-instance] IsAddTorsionFree.of_isDomain_charZero instCharZeroOfIsSemireal


variable {σ R A N k W} [CommRing R] [CommRing A] [Algebra R A] (F : ℝ → AddSubgroup R) (c : σ → ℝ)
  (w : R) (t : ℝ) (χ : MvPolynomial σ R →ₐ[R] A) [NeZero N] [CommRing W] [IsLocalRing W]
  (T : TwistingData N W R)

open Polynomial IsLocalRing Function in
/-- Stepanov's count. Let W be local with q residue classes and ι: W → R a ring map. If a
non-zero polynomial Φ over R is divisible by (X − ι(x))^E for every x in W, then Eq ≤ deg Φ. -/
lemma stepanov_count (ι : W →+* R) {Φ} E (h0 : Φ ≠ 0) (h : ∀ x, X ^ E ∣ taylor (ι x) Φ) :
    E * .card (ResidueField W) ≤ Φ.natDegree := by
  cases fintypeOrInfinite (ResidueField W) <;> simp [Nat.card]
  simpa [Nontrivial.of_polynomial_ne h0, Monic.natDegree_pow, monic_prod_X_sub_C, Finset.prod_pow,
    Monic.pow] using (Monic.not_dvd_of_natDegree_lt · h0 · (Fintype.prod_dvd_of_coprime
    (fun x y h ↦ .pow (isCoprime_X_sub_C_of_isUnit_sub (map_sub ι .. ▸ .map ι (by simpa
    [← residue_ne_zero_iff_isUnit, surjInv_eq]))))
    (X_sub_C_pow_dvd_iff.2 <| h <| surjInv residue_surjective ·)))

/-- A decreasing multiplicative filtration of a commutative ring by additive subgroups F_t, t
real: 1 ∈ F_0, F_s·F_t ⊆ F_{s+t}, and F_t ⊆ F_s for s ≤ t. -/
class IsRealFiltration extends SetLike.GradedMonoid F where antitone : Antitone F

open MvPolynomial Matrix Finsupp SetLike Nat Ideal.Quotient IsRealFiltration AddSubgroup

/-- For a ring element w and real t, the additive subgroup of elements divisible by w to the
power max(⌈t⌉,0). -/
@[simp] def adicFiltration := mk ⟨⟨{x | w ^ ⌈t⌉₊ ∣ x}, .add⟩, by simp⟩ .neg_right

instance : IsRealFiltration (adicFiltration w) where
  one_mem := by simp
  mul_mem _ _ _ _ a b := by simp_all; grw [ceil_add_le, pow_add, a, b]
  antitone _ _ _ _ := .trans (by gcongr)

/-- The Gauss filtration: for subgroups F_t of R and variable weights c, the additive group of
polynomials whose coefficient at each x^α lies in F_{t − c·α}. -/
def gaussFiltration := mk ⟨⟨{f : MvPolynomial σ R | ∀ α, f.coeff α ∈ F (t - weight c α)},
  by aesop⟩, by simp⟩ (by simp)

variable {c t F w} {a a' : Fin k}

lemma mem_adicFiltration_of_nonpos {x} (h : x ≠ 0 → t ≤ 0) : x ∈ adicFiltration w t := by
  by_cases x = 0 <;> simp_all [ceil_eq_zero.2]

lemma monomial_mem_gaussFiltration {α x} : x ∈ F (t - weight c α) →
  monomial α x ∈ gaussFiltration F c t := fun _ _ ↦ by aesop

instance [IsRealFiltration F] : IsRealFiltration (gaussFiltration F c) where
  one_mem := monomial_mem_gaussFiltration (by simp [one_mem_graded])
  mul_mem _ _ f _ h h' _ := f.coeff_mul .. ▸ sum_mem fun (a, b) ↦ by
    simp; grind [mul_mem_graded (h a) (h' b)]
  antitone _ _ _ _ := (antitone (by grind) <| · ·)

lemma aeval_sub_mem_of_gaussFiltration G [IsRealFiltration G] {f} (h :
  f ∈ gaussFiltration F c t) (u : ∀ i, χ (X i) ∈ G (c i)) (ψ := χ) (v :
  ∀ i, ψ (X i) - χ (X i) ∈ G (c i + 20⁻¹) := by simp) (y : ∀ {t x}, x ∈ F t → algebraMap R A x ∈ G
  t := by intros; (repeat apply monomial_mem_gaussFiltration); simpa) : ψ f ∈ G t ∧
  ψ f - χ f ∈ G (t + 20⁻¹) := by
  induction' f using induction_on'' with _ α x f e _ _ _ p i I generalizing t
  simpa using y (h 0)
  simp_all [add_sub_add_comm, add_mem_cancel_left,
    monomial_mem_gaussFiltration (by simpa [f.notMem_support_iff.1 e] using h α)]
  have ⟨a, b⟩ := @I (t - c i) (by grind [weight_single, coeff_mul_X, h <| · + single i 1])
  grind [mul_mem_graded a (add_mem (u i) (antitone (by simp) (v i))),
    add_mem (mul_mem_graded b (u i)) (antitone (by grind) (mul_mem_graded a (v i)))]

/-- Root lemma. Let a ≠ a', τ(a) = τ(a'), and c(u_s) − c(ū_s) ∈ [2/5, 8/5] for all s, with u_s, ū_s
as in `TwistingData.excessWeight`. If all terms of all τ-Levi translates of f have w-order plus
c-weight ≥ l + c·α and w^{l+1} ∤ f_α, then α has excess ≤ 0 at letter i.

A term least in all frames obeys Frobenius inequalities. -/
lemma TwistingData.root_lemma i (ha : a ≠ a') τ c {f α} (l : ℕ) (h : ∀ g ∈ levi W τ,
  T.polyAction g⁻¹ f ∈ gaussFiltration (adicFiltration T.w)
  c (l + weight c α)) (h0 : ¬T.w ^ (l + 1) ∣ f.coeff α) (hτ : τ a = τ a') (hc : ∀ s, c (T.rootVar a
  a' s) - c (T.rootVar a' a s) ∈ Set.Icc 0.4 1.6) : weight (T.excessWeight i a a') α ≤ 0 := by
  set y := T.rootVar a _; set x := T.rootVar _ a; let π z := ite (z = y i) (x i) z
  have hm β : mapDomain π β + single (y i) (β (y i) : ℕ) = β + single (x i) (β (y i)) := by
    induction β using induction_linear <;> simp [mapDomain_add] <;> grind
  let g r := .swap W a a' * transvectionGL ha (ite (T.isEven i) (-r) r)
  let σ z := Equiv.swap (x z.2) (y z.2) z
  obtain ⟨_, f1, _, hs, ω, _⟩ := T.one_lt_q, h 1, hc i, T.five_mul_P_pow_le_q,
    mul_left_surjective₀ (one_pos.trans T.one_lt_q).ne' (c (y i) - c (x i))
  simp at *; have : 0 < ω := by nlinarith
  have _ s t : y s ≠ x t ∧ x s ≠ y t := by grind [rootVar]
  let ε z := ite (z = y z.2) (ite (T.isEven z.2 = T.isEven i) (-1) 1) 0
  have cs z : ∃ s, (s = i ∨ s ≠ i ∧ y s ≠ y i ∧ 5 ≤ T.P ^ (s - i).val) ∧ (z = y s ∨ z = x s ∨
    ∀ t, z ≠ y t ∧ z ≠ x t) := by grind [TwistingData, le_pow, ZMod.val_pos, rootVar]
  rify at cs hs
  let m z := ite (z = x z.2) (T.P ^ (z.2 - i).val) 0 * T.q
  let e z := ite (z = y z.2) (T.P ^ (1 + (z.2 - 1 - i).val)) 0
  let χ z := monomial (single (π z) 1) (monomial (single () (m z)) (1 : R))
  let η z := monomial (single (σ z) 1)
    (monomial (single () (e (σ z))) (ite (z.2 = i) 0 (ε z + ε (σ z)) : R))
  let d u (v : _ → ℕ) z := c z - v z * u
  let G u v := gaussFiltration (gaussFiltration (adicFiltration T.w) fun () ↦ u) (d u v)
  have ag r z : T.polyAction (g r) (X z) = X (σ z) + C (ε z * T.ι z.2 r) * X z := by
    simp +zetaDelta [polyAction_X, letterMatrix_apply, transvectionGL, swap,
      GeneralLinearGroup.swap, Equiv.swap_apply_eq_iff]
    split <;> simp [transvection, Matrix.single, add_mul, ite_and,
      apply_ite (DFunLike.coe _)] <;> grind [rootVar]
  have ⟨A, D⟩ :=
    aeval_sub_mem_of_gaussFiltration (aeval χ) (G (-ω) m) f1 ?_ (aeval (χ - η)) ?_ <;> intros
  have l2 z r (m : ℕ) : monomial (single z 1) (C (T.ι (i + m) r) + X () ^ T.P ^ m - (X () + C (T.ι i
      r)) ^ T.P ^ m) ∈ G ω e (d ω e z + 2) := monomial_mem_gaussFiltration
    (.trans (pow_dvd_pow _ (by simp [↓weight_single, weight_eq_sum, *])) <|
    (C_dvd_iff_dvd_coeff (_ ^ 2) _).1 (by simpa [w_sq, prime, ← pow_mul, add_pow_prime_pow_eq',
    ← sub_sub, dvd_sub_left] using (map_dvd C (T.frobenius_pow_congr ..))) ·)
  let u := uniqueAlgEquiv R Unit
  have S {r} := aeval_sub_mem_of_gaussFiltration ((mapAlgHom ((u.arrowCongr u).symm
    (Polynomial.taylorAlgHom (T.ι i r)))).comp (.comp (aeval (χ - η)) (T.polyAction (g r)))) _
    (h (g r) (by apply mul_mem <;> simp [levi, swap, transvection] <;> grind)) fun z ↦
    Eq.subst ?_ (sub_mem (?_ : (χ - η) (σ z) ∈ _) (sub_mem (antitone ?_ (l2 (σ z) (|ε z| * r)
    (N + (z.2 - i).val))) (zsmul_mem (antitone ?_ (l2 z r (z.2 - i).val)) (ε z))))
  any_goals simp [*]
  any_goals apply_rules only [sub_mem, monomial_mem_gaussFiltration, mem_adicFiltration_of_nonpos]
  any_goals obtain ⟨s, _ | _, rfl | rfl | _⟩ := cs ‹_› <;> simp +zetaDelta [*, ↓weight_single,
    monomial_eq, Equiv.swap_apply_def] <;> (try split <;> simp) <;> intros <;>
    first | ring1 | nlinarith [hc s, hs (s - i)]
  have V {t v s g} (j : ℕ) (h : g ∈ G t v s) (K : ∀ z, d t v (π z) = d t v z := by simp +zetaDelta
    [↓apply_ite (d _ _), *]) (hj : l < s - (weight c α - weight v α * t) - j * t := by
    rify at *; nlinarith) := ((u _).coeff_map _ j).trans ((eq_zero_iff_dvd ..).2 (trans
    ((pow_dvd_pow _ (by simpa [lt_ceil, weight_apply, ↓sum_mapDomain_index, add_smul, ↓K, d,
    mul_sub, sum_mul, mul_assoc] using hj : l < _)).trans (h (mapDomain π α) _))
    (coeff_uniqueAlgEquiv ..).symm))
  have : _ ≤ weight m α := (stepanov_count (.comp ..) (weight e α) (fun H ↦ h0 ?_) fun r ↦
    Polynomial.X_pow_dvd_iff.2 fun _ _ ↦ by simpa [← AlgHom.mul_apply, ← map_mul, -map_aeval,
    coeff_map] using (V _ S.1)).trans (Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun _ _ ↦ V _ A)
  simpa +zetaDelta [weight_eq_sum, excessWeight, div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul,
    mul_sub, field, T.card_residueField, ← @cast_le ℝ, -ite_mul]
  convert by simpa [H, eq_zero_iff_dvd] using V (weight m α) D
  exact f.induction_on' (fun β r ↦ by
    simp [χ, aeval_monomial, monomial_pow, u, Finsupp.prod, ← monomial_sum_prod, ← single_finsetSum,
      ↓coeff_uniqueAlgEquiv, apply_ite AddMonoidAlgebra.coeff,
      DFunLike.ite_apply, ← ite_and, -single_mul]; congr!
    use by bound, fun _ : mapDomain .. = _ ∧ weight m β = _ ↦ by
      simpa +zetaDelta [*, by
        simpa +zetaDelta [*, add_comm, weight_single, T.prime.ne_zero,
        -ite_mul] using congr(($(hm α) + $((hm β).symm)).weight m)] using (hm β).symm) (by simp_all)
