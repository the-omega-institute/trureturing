import GRH.Lib.DiscreteSeries.Rigidity.HighestVectors
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: Lowest K-type and Casimir value determine a discrete series coefficient; analytic
vectors. The statement here is for U(p,q) and parameters with large gaps, assumes no irreducibility,
and concludes with the matrix coefficient of the highest vector. The proof is a growth estimate for
the compact Casimir operator along the filtration, with explicit norm bounds. Source: R.
Parthasarathy, Classification of discrete series by minimal K-type, Represent. Theory 19 (2015)
167-185, Thm 1.1; earlier Hotta-Parthasarathy, Invent. Math. 26 (1974) 133-178; Schmid, Ann. of
Math. 102 (1975) 535-564; Vogan-Zuckerman, Compositio 53 (1984) Prop 6.1; Nelson, Analytic vectors,
Ann. of Math. 70 (1959) 572-615.

This file: Casimir bounds and linear growth of the Lie algebra action along the filtration. Compact
Casimir grows along the filtration, so the lowest K-type occurs once. -/

open Int Calc Complex ComplexOrder Finset Fintype GlModule InnerProductSpace Module Sgn Submodule

variable {n} [Fintype n] {H I} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype I] (ε : n →
  ℤˣ) (ρ : GlModule n H) (J : I → End ℂ H) {ν : n → ℤ} {l : HCParam ε} {x : H} {y s A} [hg :
  l.HasGap A]

/-- For finitely many endomorphisms J_i of H: some operator D commuting with all E_cd, ε_c =
ε_d, has Σ_i⟨J_i u, J_i v⟩ = ⟨u, Dv⟩ for all u, v. -/
def IsKInvariantForm := ∃ D, (∀ c d, ε c = ε d → Commute (ρ.E c d) D) ∧ ∀ u v, ∑ i, ⟪J i u,
  J i v⟫_ℂ = ⟪u, D v⟫_ℂ

variable {ε} {ρ : GlModule n H} {J : I → End ℂ H} {x : H} {y : _} {s : ℕ} {A : ℝ}

lemma IsKInvariantForm.mul_E (h : IsUnitaryCasimirGe l ρ) : IsKInvariantForm ε ρ J →
  IsKInvariantForm ε ρ fun (p, q, i) ↦ J i * ρ.E q p := fun ⟨_, k, i⟩ ↦ ⟨_,
  (ρ.commute_E_sum_E_mul_mul_E (· * ·) ‹_› <| k · · ·), by simp_all [sum_prod_type, h.1, mul_comm]⟩

lemma IsKInvariantForm.sum_inner_casimirK (h : IsUnitaryCasimirGe l ρ) : IsKInvariantForm ε ρ J →
  ∀ u v, ∑ i, ⟪J i u, J i (ρ.casimirK ε v)⟫_ℂ = ∑ i, ∑ c, ∑ d with
  ε c = ε d, ⟪J i (ρ.E d c u), J i (ρ.E d c v)⟫_ℂ := fun ⟨D, k, i⟩ ↦ by
  simp [@sum_comm _ _ I, GlModule.casimir]; congr! 2; simp_all [h.1, ← (k ..).eq, ← D.mul_apply]

/-- Assume a gap, `IsUnitaryCasimirGe`, `IsKInvariantForm`, x K-highest, U ⊆ M_s finite-dimensional,
𝔨-stable. If β ≤ α·`HCParam.casimirKValue`(weight of wx) for words w of length ≤ s with wx not
orthogonal to some K-highest z ∈ U of that weight, then βΣ‖J_i y‖² ≤ α·ReΣ⟨J_i y, J_iΩ_K y⟩ on U. -/
lemma HCParam.IsKHighest.casimirK_bound_of_highest {J : I → End ℂ H} (hx : l.IsKHighest ρ ν x) (h :
  IsUnitaryCasimirGe l ρ) [hg : l.HasGap A] (α β : ℝ) {U} (hs : U ≤ ρ.filtration ε x s)
  [Module.Finite ℂ U] (hU : ∀ a b, ε a = ε b → U ∈ (ρ.E a b).invtSubmodule) (hJ :
  IsKInvariantForm ε ρ J) (hy : y ∈ U) (H : ∀ w, (∃ z ∈ U, l.IsKHighest ρ (wordWeight ν w)
  z ∧ ⟪ρ.word w x, z⟫_ℂ ≠ 0) → w.length ≤ s → β ≤ α * l.casimirKValue (wordWeight ν w)) :
  β * ∑ i, ‖J i y‖ ^ 2 ≤ α * re (∑ i, ⟪J i y, J i (ρ.casimirK ε y)⟫_ℂ) := hJ.elim fun D ⟨k, i⟩ ↦ by
  let A := α • D * ρ.casimirK ε - β • D
  let B := U.orthogonalProjectionOnto.1 ∘ₗ A.domRestrict U
  have S : B.IsSymmetric :=
    fun _ ↦ by simp [B, A, ← inner_conj_symm (D _), ← i, hJ.sum_inner_casimirK h]
  suffices B.IsPositive by simpa [B, A, ← i, sq] using this.re_inner_nonneg_right ⟨_, hy⟩
  simp [← B.posSemidef_toMatrix_iff (S.eigenvectorBasis rfl), S.toMatrix_eigenvectorBasis]; intro t
  obtain ⟨μ, z, ⟨u, f⟩, o, _, T⟩ := l.exists_highest_vector (U ⊓ Uᗮ.comap (A - ofReal _ • 1))
    ((S.hasEigenvalue_eigenvalues rfl t).imp bot_unique fun u ↦ by
    simpa [B, ← orthogonalProjectionOnto_eq_zero_iff] using ·.le (x := u))
    fun a b f y ↦ .imp (by tauto) fun t u v ↦ by simpa [A, h.1, ← End.mul_apply, (k ..).eq,
    f, ((k ..).mul_right (commute_E_casimirK ..)).eq] using t _ (hU b a f.symm v)
  have ⟨w, hw, e⟩ := not_forall₂.1 (inner_self_ne_zero.2 o <| hx.filtration_le_of_word_mem
    (innerSLFlip ℂ z).ker (by simp_all [h.1]) · (hs u))
  have p : l.IsKHighest ρ (wordWeight ν w) z := ⟨fun a ↦ by
    have := h.1 a a (ρ.word w x) z; simp_all [field, hx.E_word_eq_wordWeight_smul], T⟩
  nlinarith [H w (by tauto) hw, pow_pos (norm_pos_iff.2 o) 2, univ.sum_nonneg'
    (mul_self_nonneg ‖J · z‖), by simpa [A, p.casimirK_eq_smul, sq, ← i] using congr(re $(f z u))]

open Matrix.Norms.L2Operator in
/-- Let l have some gap, `IsUnitaryCasimirGe` hold, x be K-highest of weight ν, |ν_a| ≤ L. For y in
M_s (`GlModule.filtration`) and any matrix X: Xy ∈ M_{s+1} and ‖Xy‖ ≤ (n+1)⁴(L+1+s)‖X‖‖y‖, with ‖X‖
the operator norm. -/
lemma HCParam.IsKHighest.norm_apply_le_of_mem_filtration {L : ℕ} (hx : l.IsKHighest ρ ν x) (h :
  IsUnitaryCasimirGe l ρ) [hg : l.HasGap A] (hR : ∀ a, |ν a| ≤ L) (hy : y ∈ ρ.filtration ε x s) X :
  ρ X y ∈ ρ.filtration ε x (s + 1) ∧ ‖ρ X y‖ ≤ (card n + 1) ^ 4 * (L + 1 + s) * ‖X‖ * ‖y‖ := by
  have := hx.finite_filtration h
  have f := hx.casimirK_bound_of_highest h (-1) _ le_rfl (by grind [E_mem_filtration]) (J := ![1])
    ⟨1, by simp⟩ hy fun w _ _ ↦ antitone_mul_left (by simp) (cast_mono (sum_mono fun a ↦ by
    apply @mul_le_mul_of_natAbs_le _ _ (L + s) (L + s + card n) <;> grind [twoRho,
      hx.E_word_eq_wordWeight_smul w a]))
  simp [ρ.apply_eq_sum X, ← sum_product', sum_smul_mem, E_mem_filtration_succ hy] at *
  grw [← sq_le_sq₀ ?_ (by bound), norm_sum_le, norm_smul_le, norm_apply_le_l2_opNorm, ← mul_sum,
    mul_pow, sq_sum_le_card_mul_sum_sq,
    le_trans (a := ∑ _, _) ?_ (add_le_add_three f f (_root_.neg_le_neg
    (h.2 y)))] <;> simp [h.inner_casimir, sq, sum_filter, sum_prod_type_right, ← sum_add_distrib]
  grw [casimirValue, (sq_abs _).ge, cast_abs.ge, abs_twoRho_le, ← sub_nonneg]
  simp [sub_div, -sub_nonneg]; ring_nf; positivity
  congr! 2; split <;> simp_all [← cast_mul]

attribute [-simp] Module.End.ofNat_apply

attribute [local simp ←] ofReal_pow mul_sum

attribute [local simp] sum_prod_type E_mem_filtration Ring.lie_def add_mul mul_add mul_sub

/-- Let λ have gap 500n³+A, `IsUnitaryCasimirGe` hold, x be K-highest of weight Λ, M_s =
`GlModule.filtration`. If Ω_K a = θa with real θ ≤ |Λ+ρ_c|²−|ρ_c|²+s and a is orthogonal to M_s,
then a is orthogonal to every M_t. -/
lemma mem_orthogonal_filtration_of_casimirK {n} [Fintype n] {H} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {ε A} {l : HCParam ε} {ρ : GlModule n H} {x θ} (s : ℕ) [hg :
  l.HasLargeGap A] (h : IsUnitaryCasimirGe l ρ) (hx : l.IsKHighest ρ l.lowestKType x) a
  (ha : ρ.casimirK ε a = ofReal θ • a) (hs : θ - l.casimirKValue l.lowestKType ≤ s) (h0 :
  a ∈ (ρ.filtration ε x s)ᗮ) t : a ∈ (ρ.filtration ε x t)ᗮ := by
  let F := ρ.filtration ε x
  have r {s a X} : a ∈ (F (s + 1))ᗮ → ρ X a ∈ (F s)ᗮ := by simp_all [F, ρ.apply_eq_sum X,
    mem_orthogonal', h.1, E_mem_filtration_succ]
  have := hx.finite_filtration h; let P := (F 0).starProjection.1
  have pc c d (e : ε c = ε d) v : P (ρ.E c d v) = ρ.E c d (P v) := by
    apply eq_starProjection_of_mem_of_inner_eq_zero <;>
      simp_all [P, F, ← map_sub, h.1, ↓starProjection_inner_eq_zero]
  have pk {a} : P a = 0 ↔ _ := starProjection_apply_eq_zero_iff _
  have hj : IsKInvariantForm ε ρ ![P] := ⟨P * P, by
    simp_all [commute_iff_eq, DFunLike.ext_iff, P, inner_starProjection_left_eq_right]⟩
  have g a := by simpa +contextual [h.inner_casimir, sum_filter, -Units.val_mul] using (congr(re
    ⟪P a, $(casimirK_eq_smul_of_mem_filtration (y := P a) (coe_mem _) hx.casimirK_eq_smul)⟫_ℂ))
  have w k : ∃ I, ∃ _ : Fintype I, ∃ J : I → _, IsKInvariantForm ε ρ J ∧ (∀ a ∈ (F k)ᗮ, ∀ i,
    J i a = 0 ∧ ∑ p, ∑ q, 2 * ‖J i (ρ.E q p a)‖ ^ 2 ≤ ∑ p, ∑ q, ∑ c, ∑ d with ε c = ε d, 2 * re ⟪ρ.E
    d c (J i (ρ.E q p a)), J i (⁅ρ.E q p, ρ.E d c⁆ a)⟫_ℂ) ∧ ∀ a, (∀ m < k, a ∈ (F m)ᗮ) → (¬0 <
    ∑ i, ‖J i a‖ ^ 2 → a ∈ (F k)ᗮ) ∧ (l.casimirKValue l.lowestKType + 2 * k) * ∑ i, ‖J i a‖ ^ 2 ≤
    ∑ i, ∑ c, ∑ d with ε c = ε d, (‖J i (ρ.E d c a)‖ ^ 2 - ‖⁅ρ.E d c, J i⁆ a‖ ^ 2)
  refine k.rec ⟨_, _, _, hj, fun a h0 0 ↦ ⟨pk.2 h0, ?_⟩, by simp_all [sum_filter]⟩ fun k ⟨I, _, J,
    h1, h2, h3⟩ ↦ ⟨_, _, _, h1.mul_E h,
    fun a o (p, q, i) ↦ by simpa [r o, ρ.apply_apply_eq_swap_add_bracket (.single q p 1), h2,
    ← map_bracket] using (h2 _ (r o) i), fun a o ↦ have v p q := h3 (ρ.E q p a) (by bound); ⟨by
      simp! +contextual [o, h.1, (v ..).1 _ _, F, ← inf_orthogonal, ← iInf_orthogonal,
        mem_orthogonal,
      ↓Finset.sum_pos_iff_of_nonneg], by simpa [↓@sum_comm I, add_assoc, @norm_sub_sq ℂ] using (
      add_le_add (sum_mono fun p ↦ sum_mono (v p · |>.2)) (sum_mono (h2 a (by tauto) · |>.2)))⟩⟩
  obtain ⟨y, u, z, q, rfl⟩ := (F 1).exists_add_mem_mem_orthogonal a
  simp [-map_sub, ← map_bracket, pk.2, r q]
  have := hx.casimirK_bound_of_highest h 1 (l.casimirKValue l.lowestKType + 4 * card n + 2)
    inf_le_left (by simp_all [← pk])
    (hj.mul_E h) ⟨u, (add_mem_cancel_right (orthogonal_le le_sup_left q)).1 h0⟩ ?_
  have := show ∑ p, ∑ q, ∑ c, ∑ d with ε c = ε d, ‖P (⁅ρ.E d c, ρ.E q p⁆ y)‖ ^ 2 ≤ _ by
    simp [← map_bracket, map_single_mul_single]; grw [filter_subset, norm_sub_le, add_sq_le]
  rw [(hj.mul_E h).sum_inner_casimirK h] at *; simp +contextual [pc, g, ↓re_sum, @norm_sub_sq ℂ,
    map_bracket, sum_filter, DFunLike.ite_apply, apply_ite (‖P ·‖)] at *
  rw [sum_comm] at *; linarith
  rintro (_ | ⟨⟨a, b⟩, ⟨⟩⟩) ⟨z, ⟨_, v⟩, hν, k⟩ (_ | ⟨⟨⟩⟩)
  cases k (v _ self_mem_filtration)
  obtain ⟨e, t⟩ := hg.gap a b (k ∘ v _ ∘ E_mem_filtration self_mem_filtration),
    hν.casimir_bound h (by bound)
  simp [HCParam.casimirKValue, sub_mul, wordWeight] at *
  norm_cast at *; grind [two_mul_lowestKType, twoRho, card_pos_iff.2 ⟨a⟩, le_self_pow₀]
  refine t.strongRec fun t hm ↦ have ⟨_, _, W, h2, _, h4⟩ := w t; have ⟨q, p⟩ := h4 a hm
      by_cases (fun n ↦ orthogonal_le (filtration_mono ?_) h0) q
  rify; grw [sub_le_self] at p <;> nlinarith
    [by simpa [ha] using congr(re $(h2.sum_inner_casimirK h a a))]
