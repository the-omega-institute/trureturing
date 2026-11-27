/- GID: D5/S3/Zeros/GRH/Lib/GLn/SchurModule/MinorBasis
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/GLn/SchurModule/MinorBasis
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.GLn.SchurModule.MinorBasis. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/GLn/SchurModule/MinorBasis.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.GLn.SchurModule.Interlacing
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Standard basis theorem for Schur (dual Weyl) modules over any ring, with
character. The module here consists of the polynomials on matrices semi-invariant under a triangular
group, for several places at once. The basis is a set of products of minors built one row at a time,
not the semistandard tableaux, and its character is Weyl's quotient of alternants. Source: De
Concini, Eisenbud, Procesi, Young diagrams and determinantal varieties, Invent. Math. 56 (1980);
Akin, Buchsbaum, Weyman, Schur functors and Schur complexes, Adv. Math. 44 (1982), II.2.16, II.4.11.

This file: Products of minors form a basis over every ring, with character identity. -/

open MvPolynomial Finset MonomialOrder Submodule Finsupp Nat
attribute [local simp] zero_lt_iff single_apply sub_mem sum_smul_mem

/-- For finitely many coloured rows and finitely many columns of colours τ and heights h, there
is one family of minor products that, over every commutative ring R, is linearly independent
and whose span contains the semi-invariant module of the corresponding weight.

Known result: Standard basis theorem for Schur (dual Weyl) modules over any ring, with character. -/
lemma PolyRep.exists_minorProduct_basis {Φ J m} [Fintype m] [Fintype J] c τ h :
  ∃ (ι : Type) (_ : Fintype ι) (I : ι → @ColouredTableau Φ J m c τ h), (∀ R [CommRing R],
  LinearIndependent R (fun i ↦ minorProduct R (I i)) ∧ nabla R c (columnWeight τ h) ≤ span R
  (.range fun i ↦ minorProduct R (I i))) ∧ ∀ [Subsingleton Φ] t N (e : Fin N ≃ m) (x : m → ℂ), (∑ i,
  ∏ j, ∏ s, x (I i j s)) * alternant (x ∘ e) 0 = alternant (x ∘ e) (columnWeight τ h ⟨t, ·⟩) := by
  obtain ⟨_, _ | ⟨⟨y⟩⟩⟩ := columnOrder.toSyn.injective, isEmpty_or_nonempty m
  obtain ⟨⟨⟩⟩ := eq_or_ne h 0 <;> [use Unit; use Empty] <;> use .ofFinite _, nofun, fun R ↦ ⟨?_,
    (·.eq_C_of_isEmpty ▸ ?_ ∘ (mem_nabla.1 · R 0 0))⟩, fun _ ↦ rec ?_ fun _ _ ↦ (·.isEmpty.elim
    0) <;> simp_all [univ_eq_empty, Fintype.linearIndependent_iff, minorProduct, minor, alternant,
    ← C_mul', columnWeight,
    ← one_eq_span, pow_add, ← prod_finsetSum_index, funext_iff, prod_pow_eq_pow_sum, nontriviality]
  choose k K B L V using (exists_bordering h <| Subtype.prop ·)
  choose ι _ I hI W using (exists_minorProduct_basis (m := {a // a ≠ y}) _ τ <| k ·)
  use Sigma ι, inferInstance, (B _ <| I _ ·.2), fun R ↦
    have L γ a : HasLeadingTerm (rowExpansion y (sum a fun i (r : R) ↦ r • minorProduct R
      (B γ (I γ i)))) γ (a.sum fun i ↦ (· • minorProduct R (I γ i))) := by simp_all [HasLeadingTerm,
      sum, coeff_sum, degree_le_iff, not_imp_comm]
    ⟨.of_ker _ fun a _ ↦ by_contra fun H ↦ ?_, wellFounded_lt.onFun (f := columnOrder.toSyn ∘
    columnOrder.degree ∘ rowExpansion y).fix fun f ih hf ↦ ?_⟩, @fun S t ↦
    rec (nomatch ·.2 y) fun N _ f x ↦ ?_
  have ⟨x, hx⟩ := a.splitSupport.exists_max_image (columnOrder.toSyn ·) (by simpa [splitSupport])
  simp_all [← (HasLeadingTerm.sum (L · _) _ (by grind) (absurd hx.1)).2, ← map_sum, sigma_sum,
    linearIndependent_iff, mem_splitSupport_iff_nonzero, linearCombination_apply]
  exact (mem_span_range_iff_exists_finsupp.1 ((hI ..).2 (HasLeadingTerm.leadingCoeff_mem_nabla
    (K ⟨_, degree_rowExpansion_mem_interlacing hf⟩ ▸ hf)))).elim fun a ha ↦
    (sub_mem_iff_left _ (sum_smul_mem _ a fun i (_ : i ∈ a.support) ↦ subset_span (by use ⟨_,
    i⟩))).1 (by_cases (ih _ · (by simp [*, minorProduct_mem_nabla])) (by
    have H := L ⟨_, degree_rowExpansion_mem_interlacing hf⟩ a
    rw [ha, sum] at H; revert H
    generalize ∑ i ∈ a.support, a i • minorProduct R (B _ _) = g; intro H
    have : (rowExpansion y (f - g)).coeff (columnOrder.degree (rowExpansion y f)) = 0 := by
      simp [H.2, leadingCoeff]
    grind [degree_sub_le, coeff_degree_eq_zero_iff, zero_mem, EmbeddingLike.map_eq_zero_iff]))
  erw [S.1 t, alternant_succ (.curry _ _) _ (f.2 y), ← (interlacing _).sum_coe_sort,
    alternant_succ 0, mul_left_comm, Fintype.sum_sigma, univ.sum_mul]; congr with γ
  simpa [K γ, Pi.sub_def, V, interlacing, ← univ.mul_sum, mul_assoc, Prod.mk_right_injective] using
    .inl (W γ _ _ (.optionSubtype _ ⟨(finSuccEquiv' _).symm.trans f, f.4 _⟩) (x ·))
  repeat simp [Antitone, columnWeight, ite_and] <;> bound
termination_by Nat.card m
