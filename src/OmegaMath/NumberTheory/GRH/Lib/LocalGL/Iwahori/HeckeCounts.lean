import OmegaMath.NumberTheory.GRH.Lib.LocalGL.Iwahori.IwahoriInjective
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Exponents, U-operators and spherical vectors at pro-p Iwahori level; conjugacy in I t I
(known result; see Lib.LocalGL.Tadic.ChainLemma).

This file: Degree of I t I; spherical T_j acts on exponents by elementary symmetric functions. -/

open Fin Module Nat Pi DoubleCoset Finset Matrix Valued WithZero Function.HasFiniteSupport
  Ideal.Quotient

attribute [-simp] coe_units_inv

attribute [local simp] mulSingle_apply Set.indicator transposeGL ite_apply

variable {E V} [Field E] [NumberField E] {w : FinPlace E} [AddCommGroup V] [Module ℂ V] {N j}
  {ρ : Representation ℂ (GL (Fin N) (LocField w)) V} {ϖ : (LocField w)ˣ} (hϖ : v ϖ.1 =
  exp (-1)) {g k m x} (hx : x ∈ levelSpace ρ (Kw ..)) (r : Fin N) (t : Fin N → (LocField w)ˣ)

attribute [-simp] WithZero.inv_exp
attribute [local simp] WithZero.exp_neg

/-- The number ∏_{i<j} ‖t_j/t_i‖ for a family t of units of E_w; for dominant t it is the factor
in `hecke_dominant_eq_iwahoriDegree_smul`. -/
@[simp] noncomputable def iwahoriDegree : ℂ := ∏ p with Prod.fst p < p.2, ‖(t p.2 / t p.1).1‖

/-- For ρ a smooth representation of GL_N(E_w), t dominant and x fixed by the pro-p Iwahori
subgroup I₁, the Hecke operator of the double coset I₁tI₁ sends x to ∏_{i<j} |t_j/t_i| · U_t
x. -/
@[simp↓] lemma hecke_dominant_eq_iwahoriDegree_smul [IsSmoothRep ρ] {t} (ht :
  t ∈ dominantTorus) (hx : x ∈ levelSpace ρ proIwahori) : heckeFun ρ proIwahori ((iwahoriDoubleCoset
  t).indicator 1) x = iwahoriDegree t • compactMean ρ proIwahori (ρ (diagGL t) x) := by
  let C := ∀ i (j : Ioi i), _ ⧸ Ideal.span {(⟨(t i / t j).1, by
    simp [v.mem_integer_iff, ht (mem_Ioi.1 _).le, div_le_one_of_le₀]⟩ : 𝒪[_])}
  have c : iwahoriDegree t = (Nat.card C : ℝ) := by simp_rw [C, Nat.card_pi, cast_prod]; simp
             [↓genIndex_eq_inv_norm, ↓← genIndex_eq_card (isOpen_integer _) (isCompact_LocInt _),
    prod_finset_product _ univ Ioi, ← prod_attach (Ioi _)]
  cases fintypeOrInfinite C <;> simp [prod_eq_zero_iff, card_eq_zero_of_infinite] at c
  choose r n a using fun c : C ↦ exists_proIwahori_coe_eq (of _) (fun i j ↦ (if h :
    _ then (c i ⟨j, h⟩).out else diagonal 1 i j).2) (by simp_all [lt_asymm, ne_of_gt])
  suffices ∀ k ∈ proIwahori, ∃! c, (k * diagGL t)⁻¹ * (r c * diagGL t) ∈ proIwahori by
    rw [← compactMean_eq_self _ ((isBiInvariant_doubleCoset isOpen_proIwahori _).heckeFun_mem hx),
      (heckeFun_eq_sum (s := ⊤) (r := (r · * diagGL t)) ..).2] <;> simp +contextual [*,
      mem_doubleCoset, ↓mem_doubleCoset_self, Set.InjOn, isBiInvariant_doubleCoset
      isOpen_proIwahori, cast_smul_eq_nsmul, -Set.indicator] <;> grind [ExistsUnique,
      QuotientGroup.eq]
  intro k hk
  have ⟨u, hu, h⟩ := exists_unipotent_conj_mem_proIwahori ht hk
  convert ((@Finite.injective_iff_bijective C _ fun c i j ↦ (⟨_, (proIwahori.mul_mem (inv_mem hu.2)
    (n c)).1.isIntMatrix i j⟩ : 𝒪[_])).1 fun c d e ↦ funext₂ fun i _ ↦ ?_).existsUnique 0
  · cases mul_mem (inv_mem hu) ⟨by simp_all [apply_ite]; grind, n ‹_›⟩
    rw [← mul_mem_cancel_left h]; group
    rw [mul_assoc _ (u ^ _), mem_proIwahori_iff_of_unitriangular] <;> simp_all [C, funext_iff,
      eq_zero_iff_dvd, diagGL, le_div_iff₀, mul_assoc (v _)⁻¹, inv_mul_le_one₀,
      (Valuation.integer.integers v).dvd_iff_le, zero_lt_iff, Algebra.algebraMap_ofSubring]
  induction' i using WellFoundedGT.induction with i
  refine Quotient.out_equiv_out.1 ((Submodule.quotientRel_def _).2 ((Subtype.ext ?_).subst
    (Ideal.Quotient.eq.1 congr($e _ _))))
  simp_all [Matrix.mul_apply, ← sum_sub_distrib]
  grind [sum_eq_single i, mem_agreeWithOneOn.1 (inv_mem hu.1), Matrix.one_apply]

lemma coe_normAbsChar_locField (x : (LocField w)ˣ) :
  (normAbsChar x).1 = ‖x.1‖ := by simp [normAbsChar, norm_locField_eq_q_zpow, ← card_ResField]; rfl

lemma heckeCoset_mulSingle_zero_eq (hϖ : v ϖ.1 = exp (-1)) [IsSmoothRep ρ] [NeZero N] (h :
  x ∈ levelSpace ρ proIwahori) : let t := mulSingle 0 ϖ; t ∈ dominantTorus ∧ heckeCoset ρ proIwahori
    (diagGL t) x = (w.q : ℂ) ^ (N - 1) • compactMean ρ proIwahori (ρ (diagGL t) x) := by
  cases N <;> simp_all +decide [heckeCoset, dominantTorus, Monotone, norm_locField_eq_q_zpow,
    prod_filter, forall_fin_succ, Fintype.prod_prod_type, prod_univ_succ, univ_eq_empty]

/-- The g in `basicDoubleCoset` (the double coset of the j-th Hecke operator) whose lattice g𝒪^N
contains the first r basis vectors, i.e. the first r columns of g⁻¹ are integral. -/
def partialCosets r j := {g ∈ basicDoubleCoset (Fin N) w j | ∀ b a, b.1 < r → v (g⁻¹ a b) ≤ 1}

variable (ρ) in
/-- The sum of ρ(g) over the lattices g𝒪^N of `partialCosets` r j: the operator T^r_j. -/
noncomputable def partialHecke r j := heckeFun ρ (Kw ..) ((partialCosets r j).indicator 1)

@[simp] lemma mul_mem_partialCosets_iff : (k ∈ blockParahoric (· + 1 - m) →
  (k * g ∈ partialCosets m j ↔ g ∈ partialCosets m j)) ∧
  (k ∈ Kw (Fin N) w → (g * k ∈ partialCosets m j ↔ g ∈ partialCosets m j)) := by
  have H g k l o (p : k ∈ blockParahoric (· + 1 - m)) (h : g ∈ @partialCosets _ _ _ w N m j) :
    _ * l ∈ partialCosets m j := ⟨mul_mul_mem_basicDoubleCoset h.1 p.1 o, fun b a c ↦
    sum_mem fun i _ ↦ mul_mem (o.isIntMatrix_inv ..)
    (sum_mem fun l _ ↦ (map_mul ..).trans_le (if e : _ then mul_le_one' (h.2 l i e)
    (p.1.isIntMatrix_inv ..) else by grw [h.1.2.1]; simp [← lt_mul_exp_iff_le]; grind [inv_mem p]))⟩
  obtain _ := H (k * g) k⁻¹ 1, H (g * k) 1 k⁻¹, H g k 1, H g 1; aesop

lemma hasFiniteCosets_partialCosets : HasFiniteCosets (A := ℂ) (Kw (Fin N) w)
  ((partialCosets m j).indicator 1) := (isBiInvariant_basicDoubleCoset (A := ℂ) j).1.subset
  (by simp; grind [partialCosets])

/-- T⁰_j = T_j: with no condition on basis vectors (r = 0), the operator summing ρ over the
cosets of `partialCosets` is the j-th Hecke operator of GL_N(E_w). -/
lemma partialHecke_zero_eq_heckeGL : partialHecke ρ 0 j =
  heckeGL ρ j := by simp [partialHecke, partialCosets, heckeGL]

@[simp] lemma partialHecke_top_eq_zero : partialHecke ρ N (j + 1) = 0 :=
  finsum_eq_zero_of_forall_eq_zero (by
  simpa using fun _ ⟨a, b⟩ ↦ nomatch a.2.2 ▸ (mem_intGL_iff_det.1 (mem_intGL.2 ⟨a.1, by bound⟩)).2)

include hx

lemma partialHecke_mem_levelSpace : partialHecke ρ m j x ∈ levelSpace ρ (blockParahoric
  (· + 1 - m)) := by simp_all [partialHecke, heckeFun_mem_levelSpace hasFiniteCosets_partialCosets]

lemma partialHecke_zero_right : partialHecke ρ m 0 x =
  x := by erw [partialHecke, partialCosets, Set.sep_eq_self_iff_mem_true.2 fun _ h ↦ by
  bound [(mem_intGL_iff_det.2 ⟨h.1, h.2.2⟩).isIntMatrix_inv], heckeGL_zero hx]

include hϖ

/-- Let T^r_j be the Hecke operator of `partialCosets` r j, x fixed by GL_N(𝒪_w), b diagonal with ϖ
at index r (from 0), 1 elsewhere, and ψ linear, invariant under the k⁻¹ ∈ I₁ with k diagonal off row
r. Then q^(N−1−r) ψ(ρ(b)T^(r+1)_j x) = q^j ψ(T^r_(j+1) x − T^(r+1)_(j+1) x). -/
lemma partialHecke_hyperplane_count {W} [AddCommGroup W] [Module ℂ W] {ψ : V →ₗ[ℂ] W} (hψ : ∀ k,
  (∀ i ≠ r, ∀ l ≠ i, k.1 i l = 0) → k⁻¹ ∈ proIwahori → ∀ z, ψ (ρ k⁻¹ z) = ψ z) j :
  (w.q ^ r.rev.1 : ℂ) • ψ (ρ (diagGL (mulSingle r ϖ)) (partialHecke ρ (r + 1) j x)) =
  ψ ((w.q : ℂ) ^ j • (partialHecke ρ r (j + 1) x - partialHecke ρ (r + 1) (j + 1) x)) := by
  have I g : (diagGL (mulSingle r ϖ))⁻¹ * g ∈ partialCosets (r + 1) j ↔ g ∈ partialCosets r (j + 1)
    ∧ g.1.map residueOrZero r = 0 := by simp [partialCosets, basicDoubleCoset, diagGL, apply_ite,
                                          funext_iff, *, field, ← @lt_mul_exp_iff_le (exp 1 * _)]
                                        grind [@exp_le_exp ℤ _ 1 2]
  let S := Fintype.piFinset fun i ↦ ite (r < i) (@univ (ResField w) (.ofFinite _)) {ite (r = i) 1 0}
  choose n m b using fun u : _ → ResField w ↦ exists_proIwahori_coe_eq (of _) (fun i k ↦
    (ite (k ≤ i ∨ i ≠ r) (diagonal 1 i k) (u k).out).2) (by simp_all [le_of_lt, ne_of_gt])
  have A := apply_heckeFun (hasFiniteCosets_partialCosets (j := j) (m := r + 1)) (by simp) hx
  convert ← congr(ψ (∑ u ∈ S, $((A ((n u)⁻¹ * diagGL (mulSingle r ϖ))).2))).symm
  · simp +contextual [S, partialHecke, apply_ite card, prod_ite, card_ResField, filter_lt_eq_Ioi, *,
      eq_comm, tsub_add_eq_tsub_tsub_swap, ← cast_smul_eq_nsmul ℂ, Fintype.card_eq_nat_card]
  simp only [partialHecke, heckeFun, ← End.smul_def, finsum_smul', smul_assoc, ← sum_smul,
    ← finsum_sum_comm, smul_finsum, ← finsum_sub_distrib,
    fun_smul_left hasFiniteCosets_partialCosets, fun_smul_left (A _).1, implies_true]
  congr with g
  by_cases! h : g.out ∉ partialCosets r (j + 1) <;> simp [mul_assoc, mul_mem_partialCosets_iff.1
    (proIwahori_le_blockParahoric (by lia) (m _)), I, h]; grind [partialCosets]
  have M r := v_mul_inv_le_one_iff (z :=
    diagonal (if ·.1 < r then 1 else 0)) (transposeGL_mem_basicDoubleCoset.2 h.1)
  set L := residueKer (transposeGL g.out).1
  simp [IsConcreteLE.le_iff, funext_iff, apply_ite, diagonal_apply] at M
  rw [partialCosets, Set.mem_ofPred_eq, M, filter_congr (q := (· ∈ L)) fun u _ ↦ by
    simp [map_residueOrZero_mul (m u).1.isIntMatrix h.1.1, mul_apply_eq_vecMul, transpose_map, L]
    congr!; ext; simp [residueOrZero_coe, b, apply_ite (IsLocalRing.residue _)]
    split; exacts [show ite _ 1 0 = _ by grind, (u _).out_eq]] at *
  let p := L.dualRestrict (.proj r)
  simp_all [le_iff_lt_or_eq, or_imp, Fin.val_inj]
  split <;> simp; grind
  have F : p ≠ 0 := by simp [*, p, DFunLike.ext_iff]
  erw [← card_subtype, (subtype_card _ fun u ↦ by simp [p]; grind [h.2
    u.2]).symm.trans (card_congr (p.toAddMonoidHom.fiberEquivKerOfSurjective (p.surjective F)
    1)), @natCard_eq_pow_finrank (ResField w) p.ker, card_ResField]
  grind [finrank_residueKer (transposeGL_mem_basicDoubleCoset.2 h.1) ▸
    p.finrank_ker_add_one_of_ne_zero F]

open Multiset

/-- Satake's formula, in stages: for an exponent (ξ, l), ξ = `torusChar` θ, y_i = θ_i(ϖ), x fixed by
GL_N(𝒪_w), r ≤ N, and T^r_j the Hecke operator of `partialCosets` r j, l(T^r_j x) =
q^(−j(j−1)/2) e_j(y_r, …, y_(N−1)) l(x). -/
lemma IsExponent.apply_partialHecke [IsSmoothRep ρ] {θ l} (hl :
  IsExponent (.of ρ) (torusChar θ) l) {r} (h : r ≤ N) : ∀ j, l (_root_.partialHecke
  ρ r j x) = esymm ((List.ofFn fun i ↦ (θ i ϖ).1).drop r) j / w.q ^ j.choose 2 * l x := by
  induction' h using
    decreasingInduction with r h <;> rintro (_ | j) <;> simp [partialHecke_zero_right hx, esymm]
  obtain _ := partialHecke_hyperplane_count hϖ hx ⟨r, h⟩ (by bound [hl.apply_proIwahori]) j,
    hl.apply_monomial_translate hϖ (partialHecke_mem_levelSpace hx (m := r + 1)
    (j := j)) (·.1) 1 (t := mulSingle ⟨_, h⟩ ϖ) (by simp +decide [apply_ite, *]; lia)
  simp_all [List.drop_eq_getElem_cons, coe_normAbsChar_locField, norm_locField_eq_q_zpow, esymm,
    sum_map_mul_left, Nat.choose, ← cons_coe]; grind [pow_ne_zero, cast_ne_zero, w.q_bounds]

/-- Duality of lattices. Let T^r_j sum over the cosets in `partialCosets` r j, x be GL_N(𝒪_w)-fixed,
r + i + j = N. Then T^r_j for the representation g ↦ ρ((gᵀ)⁻¹) sends x to ρ(diag(1_r,
ϖ⁻¹1_{N−r})) T^r_i x, with T^r_i taken for ρ. -/
lemma partialHecke_dual i (e : m + (i + j) = N) : partialHecke (ρ.comp invTransposeGL.toMonoidHom) m
  j x = ρ (diagGL (if ·.1 < m then 1 else ϖ⁻¹)) (partialHecke ρ m i x) :=
  (heckeFun_comp _ (by simp [← mul_assoc]) hx hasFiniteCosets_partialCosets
  invTransposeGL.surjective invTransposeGL_mem_intGL (by tauto) fun g ↦ by
  subst e; have := g.det_ne_zero; simp [invTransposeGL, partialCosets, basicDoubleCoset, diagGL,
  apply_ite, *, prod_univ_add, field, ← g⁻¹.val_det_apply]; grind [le_of_lt, lt_mul_exp_iff_le
  one_ne_zero]).trans (apply_heckeFun hasFiniteCosets_partialCosets (by simp) hx _).2
