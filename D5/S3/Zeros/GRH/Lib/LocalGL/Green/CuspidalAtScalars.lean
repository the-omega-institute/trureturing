/- GID: D5/S3/Zeros/GRH/Lib/LocalGL/Green/CuspidalAtScalars
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/LocalGL/Green/CuspidalAtScalars
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.LocalGL.Green.CuspidalAtScalars. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/LocalGL/Green/CuspidalAtScalars.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.LocalGL.Green.CuspidalSupport
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Green's characters of GL_n(F_q) and the parabolic-induction ring (known result; see
Lib.LocalGL.Green.LabelDegree).

This file: Values of Steinberg and cuspidal class functions at field elements, by generating
series. -/

open Module Algebra Finset Fint Hall Lagrange Matrix Polynomial Submodule minpoly

variable {k K F V} [Field k] [Finite k] [Field K] [Algebra k K] [Field F] [Finite F] [Algebra k F]
  (z : PowerBasis k F) [AddCommGroup V] [Module k V] [Module F V] [IsScalarTower k F V]
  [Module.Finite k V] [Module.Finite F V]

/-- For a finite field k with q elements, the order of GL_n(k) is the product of q^i(q^{i+1} −
1) over 0 ≤ i < n, as an identity in any field R. -/
lemma card_GL_eq_prod {n R} [Fintype n] [Field R] : Nat.card (GL n k) =
  ∏ i ∈ range (Fintype.card n), (Nat.card k ^ i * (Nat.card k ^ (i + 1) - 1) : R) := by open Calc in
  simp [↓Nat.card_congr (Units.mapEquiv (reindexRingEquiv k (Fintype.equivFin n)).toMulEquiv).1,
    ↓card_GL_field, Nat.pow_le_pow_right Fintype.card_pos]; induction Fintype.card n <;> simp_all
    [Fin.prod_univ_succ, prod_range_succ, pow_succ, ← sub_mul] <;> ring

attribute [local simp] mul_simClassOf finrank_zero_iff eval_finsetSum mul_smul add_smul

/-- Let F = k[z] have Q elements, g be multiplication by z on an F-space V of dimension m, and N
= ∏_{i<m}(X − Q^i). Then 𝟙⁻¹(g) = N(0), and C_η(g) (`Hall.greenCuspidal`) is −N'(1) times the
sum of η over the roots in K of the minimal polynomial of z. -/
lemma moebius_and_greenCuspidal_lsmul η : let N : ℂ[X] := nodal (range (finrank F V)) fun x ↦
    ↑(Nat.card F ^ x)
  let g := lsmul k k V z.gen; moebius (simClassOf g) = N.eval 0 ∧ greenCuspidal k η (simClassOf g) =
  -(((minpoly k z.gen).aroots K).map η).sum * N.derivative.eval 1 := by
  intro N g; have := @finite_of_finite k V
  let S (W : StableSubspace g) : Submodule F V := ⟨W.1.1, fun c _ ↦ (z.exists_eq_aeval'
    c).choose_spec ▸ (aeval_apply_smul_mem_of_le_comap' · _ _ W.2)⟩
  rw [← one_mul moebius, (eq_of_degree_sub_lt_of_eval_index_eq _ (Nat.cast_injective.comp
    (Nat.pow_right_injective Finite.one_lt_card)).injOn ((degree_lt_iff_coeff_zero ..).2
    fun n h ↦ ?_) fun j h ↦ (eval_nodal_at_node h).trans ?_ : N = ∑ W, monomial (finrank F (S W))
    (moebius (simClassOf W.endOnQuot)))]
  simp [(by grind [mu_mul_constOne, greenCuspidal_mul_constOne η] : greenCuspidal k η = -brauerLift
    k η * moebius), z.finrank, ← finrank_mul_finrank k F, z.dim_pos.ne', zero_pow_eq, mul_sum,
    derivative_monomial, fun W ↦ show simClassOf W.endOnSub = simClassOf
    (lsmul k k (S W) z.gen) from rfl, monic z.isIntegral_gen, charpoly_eq_pow_of_isNilpotent
    (irreducible z.isIntegral_gen), Multiset.map_nsmul, Multiset.sum_nsmul]; ac_rfl
  erw [coeff_sub, ← (isMonicOfDegree_monomial_one _).coeff_eq ⟨by simp, nodal_monic⟩ h,
    finsetSum_coeff, Fintype.sum_eq_single ⟨⊤, by simp⟩, finrank_top] <;> simp_all
    [coeff_monomial]; intro a b n; bound [(S ⟨a, b⟩).finrank_lt (n <| top_unique ·.ge)]
  simp; simp_rw [pow_right_comm _ j, ← Nat.cast_pow, ← card_eq_pow_finrank, Nat.cast_pow,
    Fintype.card_subtype, ← sum_boole, Fintype.sum_pow, Fintype.prod_boole, mul_sum,
    ← SetLike.mem_coe, ← Set.range_subset_iff, ← span_le]; rw [sum_comm, sum_eq_zero]
  intro v _; let U : StableSubspace g := ⟨(span F (.range v)).restrictScalars k, by aesop⟩
  simpa [sum_filter, U, mt finrank_le_of_span_eq_top, mem_range.1 h, sum_inverse_constOne] using!
    ((StableSubspace.sum_comap U.1.mkQ (g' := U.endOnQuot) (by bound) _).trans
    (by simp)).trans congr($(mul_comm constOne moebius) (simClassOf U.endOnQuot))

lemma mulMu_greenCuspidal_lsmul η [Nontrivial V] : (greenCuspidal k η).mulMu (simClassOf
  (lsmul k k V z.gen)) * (.card V - 1 : ℕ) = (((minpoly k z.gen).aroots K).map η).sum * Nat.card
  {e : V ≃ₗ[k] V // ∀ x, e (z.gen • x) = z.gen • e x} := by
  simp_rw [mulMu, moebius_and_greenCuspidal_lsmul z η]; rw [@natCard_eq_pow_finrank F V, eq_comm,
    ← Nat.card_congr ((GeneralLinearGroup.toLin' (finBasis F V)).1.trans ?_), card_GL_eq_prod,
    ← Nat.sub_add_cancel finrank_pos, nodal, prod_range_succ']; simp [eval_prod, pow_succ,
    prod_range_succ, ← neg_sub (1 : ℂ), -neg_sub, -Nat.card_eq_fintype_card, prod_neg]; ring
  exact .mk (⟨·.toLinearEquiv.restrictScalars k, by simp⟩) fun ⟨f, _⟩ ↦ .ofLinearEquiv {f with
    map_smul' c := by induction eq_top_iff.1 z.adjoin_gen_eq_top c using adjoin_induction <;> aesop}
