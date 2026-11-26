import OmegaMath.NumberTheory.GRH.New.TwistedHecke.DeepFormCost
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of commutative and general algebra (textbook or folklore).

Part of: An approximate projector from averages over generic matrices (see
New.TwistedHecke.ElementaryDivisors).

This file: Integral conjugation-invariant means on generic Levi matrices splitting evaluation at 1
by weight. -/

open IsLocalRing Module Nat Finset Finsupp LinearMap Matrix MvPolynomial Submodule

attribute [-simp] coe_units_inv mulVec_single

attribute [local simp] Finset.mul_sum Fintype.sum_prod_type LinearMap.ext_iff restrict_apply mulVec
  Matrix.mul_apply Matrix.trace coeff_sum eval_monomial map_eval RingHom.map_det _root_.funext_iff

variable {k D : ℕ} {W O σ : Type} [CommRing W] [IsLocalRing W] [CommRing O] (τ : Fin k → ℕ)
  (ι : W →+* O) [Fintype σ]

/-- For ι: W → O and a in GL_k(W), the O-algebra endomorphism of polynomials in the entries of a
generic k×k matrix x given by substituting ι(a⁻¹) x ι(a) for x. -/
noncomputable def ClassMean.conjSubst (a : GL (Fin k) W) :=
  linSubst (a⁻¹.1ᵀ.kroneckerMap (ι · * ι ·) a.1)

lemma ClassMean.map_C_mul_mul_C {ν} (A B : Matrix σ σ O) (X : Matrix σ σ (MvPolynomial ν O))
    (l : Dual O _) : (A.map C * X * B.map C).map l = A * X.map l * B := ext
    (by simp [mul_comm (∑ _, _), C_mul', mul_left_comm])

attribute [local simp ←] ClassMean.map_C_mul_mul_C Matrix.map_map Matrix.map_mul monomial_sum_prod
  cast_prod cast_sum kroneckerPi_map kroneckerPi_mul mul_assoc

/-- Zariski density: if n + e ≤ #(residue field of W) (0 if infinite) and a form d of degree e
takes a unit value, the vectors (ι(b^γ)) over monomials γ of degree n, for b with d(b) a
unit, span everything over O. -/
lemma ClassMean.eq_top_of_eval_monomial n {e d} (hd : d.IsHomogeneous e) (hW : n + e ≤ .card
    (ResidueField W)) {b} (hb : IsUnit (eval b d)) {p : Submodule O (Monomials σ n → O)}
    (hp : ∀ b, IsUnit (eval b d) → (ι <| eval b <| monomial ·.1 1) ∈ p) : p = ⊤ := by
  let q := p.comap (σ₁₂ := ι) ⟨⟨(ι ∘ ·), by simp⟩, by simp⟩
  simpa [q, Pi.single, Function.comp_update, eq_top_iff_forall_basis_mem (Pi.basisFun ..)] using
    subsingleton_tensorProduct.1
    ((subsingleton_dual_iff _).1 ((liftBaseChangeEquiv _).subsingleton_congr.1
    (subsingleton_of_forall_eq 0 fun e ↦ (by ext γ; simpa using congrArg (·.coeff γ) ·)
    ((mul_eq_zero_iff_right (by simpa [·] using hb.map (residue W))).1 (((IsHomogeneous.sum univ _ _
    fun γ _ ↦ isHomogeneous_monomial (e (q.mkQ (Pi.single γ 1))) γ.degree_eq).mul (hd.map
    (residue W))).eq_zero_of_forall_eval_eq_zero_of_le_card (by
    simpa [residue_surjective.comp_left.forall, mul_comm (e _),
      Algebra.smul_def _ (e _), or_iff_not_imp_right, ← residue_ne_zero_iff_isUnit] using
      fun b h ↦ congr(e $(q.ker_mkQ.ge ((pi_eq_sum_univ' _).subst (hp b h)))))
    ((Cardinal.natCast_toNat_le _).trans' (mod_cast hW)))))))

variable (σ) [IsDomain O] [CharZero O] [ValuationRing O]

/-- Let k be a prime, non-unit in a valuation domain O of characteristic zero. There are q_γ in O
with multinomial(γ)·q_γ = k^{|σ|f} when deg γ < k^f, and coeff_α(A·x^β)q_α = q_β·coeff_β(Aᵀ·x^α) for
all square matrices A acting by `linSubst`. -/
lemma ClassMean.exists_invariant_diagonal_form (pp : k.Prime) (hp : ¬IsUnit (k : O)) f : ∃ q :
    _ → O, (∀ γ : σ →₀ ℕ, γ.degree < k ^ f → k ^ (Fintype.card σ * f) = γ.multinomial * q γ) ∧ ∀ A α
    β, (linSubst A (monomial β 1)).coeff α * q α = q β * (linSubst Aᵀ (monomial α 1)).coeff β := by
  have M s α (h : s.sum α < k ^ f) : (@multinomial σ s α : O) ∣ k ^ (#s * f) := by
    induction s using cons_induction <;> simp_all [multinomial_insert, pow_mul', _root_.pow_succ']
    gcongr
    grw [← (Nat.choose ..).ordProj_mul_ordCompl_eq_self, cast_mul, cast_pow, (notMem_maximalIdeal.1
      (Ideal.IsPrime.notMem_of_isCoprime_of_mem (coprime_ordCompl pp (choose_ne_zero
      le_self_add)).cast hp)).mul_right_dvd, factorization_choose_le_log, h, log_pow pp.one_lt]; lia
  choose q hq using fun γ ↦ iteInduction (M univ γ) fun _ ↦ dvd_zero _
  use (q ·), by grind [multinomial_eq_of_support_subset, degree_eq_sum], fun A α β ↦
    nsmul_right_injective α.degree.factorial_ne_zero
    (by grind [degree_eq_sum, by simpa [fockPairing, jet_eq_sum, prod_fintype, -coe_monomial] using
    (fockPairing_linSubst A (monomial α 1) (monomial β 1)), !congr(($(multinomial_spec ..) : O)),
    (Monomials.isHomogeneous_linSubst _ ⟨α, by aesop⟩).coeff_eq_zero])

/-- Let O be a valuation domain of characteristic 0, the prime p a non-unit, W local, D < p^f,
D + k < #residue field of W. For any property P of x-weights, some Levi-conjugation invariant linear
form κ on polynomials in a generic matrix kills monomials with row weight ≠ column weight, sends
monomials with row weight in P to p^{k²f}·(value at 1) (0 in degree > D), and is a combination of
Levi conjugates of forms killing the monomials with row weight outside P.

An approximate projector from averages over generic matrices. -/
lemma ClassMean.exists_mean {p : ℕ} (pp : p.Prime) (hp : ¬IsUnit (p : O)) f (hD : D < p ^ f)
    (hW : D + k < .card (ResidueField W)) (x : _ → ℝ) (P : ℝ → _) : ∃ κ : Dual O _,
  (∀ a ∈ levi W τ, ∀ g, κ (conjSubst ι a g) = κ g) ∧ (∀ α, weight (x ·.1) α ≠ weight (x ·.2) α
  → κ (monomial α 1) = 0) ∧ (∀ α, P (weight (x ·.1) α) → κ (monomial α 1) = if degree α ≤ D then p ^
  (k ^ 2 * f) • eval (vec 1) (monomial α 1) else 0) ∧ κ ∈ span O {l ∘ₗ (conjSubst ι u).toLinearMap |
  (u ∈ levi W τ) (l : Dual O _) (_ : ∀ α, ¬P (weight (x ·.1) α) → l (monomial α 1) = 0)} := by
  simp_rw [le_iff_lt_add_one]
  refine Fin.val_last (D + 1) ▸ (Fin.last _).induction ⟨0, by simp⟩ fun d ⟨κ, _, _, u, w⟩ ↦ ?_
  let Y := of fun i j ↦ C (@ite W (τ i = τ j) _ 1 0) * X (j, i)
  let g := kroneckerPi fun _ : Fin d ↦ Y.map (·.map ι)
  have H m t α w : (g m t).coeff α ≠ 0 → α.weight w = ∑ l, (w (t l, m l) : ℝ) := by simp +contextual
    [g, Y, kroneckerPi, ↓C_mul_X_eq_monomial, weight, eq_comm]
  let S := (Pi.basisFun O (Monomials _ d)).constr O fun γ ↦ g.map (·.coeff γ.1)
  have E (l : Dual ..) : S (l <| monomial · 1) = g.map l := ext fun m t ↦ by simp [Matrix.sum_apply,
    S, mul_comm,
    ← congr(l $(sum_monomials_eq_of_isHomogeneous (by simpa [weight_eq_sum] using H m t · 1)))]
  have hv b : _ = kroneckerPi fun _ ↦ (Y.map (eval b)).map ι :=
    (E (aeval (ι ∘ b)).toLinearMap).trans (ext (by simp [g, kroneckerPi]))
  have L (a : levi W τ) : Y.map (eval (vec a.1)) = a.1 :=
    ext (by simp_all [Y, apply_ite, ite_apply, a.2 _])
  choose ev he using (mem_range.2 ⟨_, L · ▸ hv _⟩)
  have sp p (hp' : ∀ {c} a, S c = S (ev a) → c ∈ p) := eq_top_of_eval_monomial ι d (Y.det_apply' ▸
    IsHomogeneous.sum _ _ _ fun _ _ ↦ .C_mul
      (.prod _ _ 1 (by solve_by_elim [isHomogeneous_C_mul_X]))
    _) (by simp; lia) (by simpa using L 1 ▸ isUnits_det_units 1) (by simpa using! fun b h ↦ (hp' _
    ((hv b).trans (he ⟨.mk'' _ h, by clear * -; simp_all [Y, levi]⟩).symm)))
  let N := ⨆ t, (toLin'.1.flip (Pi.single t (ite (P (∑ l, x (t l))) 1 0)) ∘ₗ S).range
  obtain ⟨m, _, q, _, hq'⟩ := iSup_le_iff.1 (le_refl N), @free_of_flat_of_isLocalRing O N _ _ _ _ _
    (Flat.flat_iff_torsion_eq_bot_of_isBezout.2 (isTorsionFree_iff_torsion_eq_bot.1 inferInstance)),
    exists_invariant_diagonal_form (Fin k × Fin k) pp hp f
  let K := pi fun γ : Monomials _ d ↦ (lcoeff O γ.1).smulRight (q γ.1)
  have hK α : S (K (monomial α 1)) = _ := congr(S $(by simp [K]; lia)).trans (E (q α • lcoeff O α))
  have adj := by simpa using fun a ↦ (linearMap_ext fun α ↦ ext_ring (by
    erw [congrArg S (funext (hq' _ · α)), E ((q α • lcoeff O α) ∘ₗ (linSubst _).toLinearMap)]
    simp [*, g, -LinearMap.coe_smul]; congr!
    simp [← ext_iff, -prod_mul_distrib, univ.sum_mul, Y, linSubst, ← C_mul', kroneckerPi, -ite_mul]
    congr! 3; grind [a.2 _, inv_mem a.2 _]) :
    S ∘ₗ K ∘ₗ conjSubst ι a.1 = mulLeftRight O (S (ev a), S (ev a⁻¹)) ∘ₗ S ∘ₗ K)
  let ρ : _ →ₗ[O] End O N := ⟨⟨(S · |>.toLin'.restrict (id ((sp ((N.compatibleMaps N).comap
    (toLin'.1 ∘ₗ S)) fun a _ ↦ iSup_le fun v ↦ range_le_iff_comap.2 (sp _ fun b _ ↦
    m v ⟨ev (a * b), by simp [*]⟩)).ge ⟨⟩))), by simp⟩, by simp⟩
  let b := finBasis O N
  use κ + trace O N ∘ₗ ρ ∘ₗ K, fun a h f ↦ by simp [*]; convert ((ρ (ev ⟨a, h⟩)).trace_mul_cycle O
    (ρ (K f)) (ρ (ev ⟨a, h⟩⁻¹))) <;> simp [*, ρ], fun α h ↦ by simpa [*, ρ] using
    (LinearMap.isNilpotent_trace_of_isNilpotent (End.isNilpotent.restrict _ (.map ⟨2, (sq _).trans
    (ext fun _ _ ↦ sum_eq_zero (by simp; grind))⟩ toLinAlgEquiv'))).eq_zero, fun α h ↦
    congr($(u α h) + $((trace_comp_comm' _ (codRestrict N _ ((range_toLin' _).trans_le (span_le.2
    (Set.range_subset_iff.2 (m · ⟨K (monomial α 1), by simp [*]; grind⟩))) ⟨·, rfl⟩))).trans
      (.trans (by simp [*, g, Y, kroneckerPi, sum_pow']; congr!) congr(_ *
    $(coeff_linearCombination_X_pow_of_fintype
    (vec 1) α d))))).trans (by simp [sum] at *; grind [degree_apply])
  convert add_mem w (sum_mem (t := univ) fun j ↦ by
    simpa using (iSup_le fun v ↦ range_le_iff_comap.2 (sp _ fun {c} a _ ↦ by
      exists ⟨_, m v ⟨c, rfl⟩⟩, subset_span ⟨_, a⁻¹.2, (b.coord j ∘ₗ ρ c) ∘ₗ codRestrict N _
      (m v ⟨·, rfl⟩) ∘ₗ K, fun α h ↦ ker_le_ker_comp _ _ (by simp [*]; grind), by simp [ρ, *]⟩) :
      N ≤ (comap ((ρ ∘ₗ K).flip.compr₂ (b.coord j)) _).map N.subtype) (b j).2)
  simp [trace_eq_matrix_trace O b, toMatrix_apply]
