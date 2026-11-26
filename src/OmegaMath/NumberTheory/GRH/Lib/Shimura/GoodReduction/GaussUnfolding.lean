import OmegaMath.NumberTheory.GRH.Lib.Shimura.GoodReduction.HermitianAction
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of algebraic number theory (textbook or folklore).

Part of: Good reduction of unitary PEL abelian varieties, in analytic form (no toric degeneration)
(known result; see Lib.Shimura.GoodReduction.ArcReduction).

This file: Mean of the theta kernel as Gauss sum times Gaussian integral; real fourth power. -/

namespace IsHermitianAction

open Complex ComplexConjugate Matrix Module MeasureTheory ComplexOrder QuotientAddGroup Fintype
variable {V R} [FinComplexSpace V] [CommRing R] [StarRing R] {L : Submodule ℤ V} {B F} {β :
  R} (h : IsHermitianAction L B F β) {x y}

/-- Let κ ≠ 0 and r lie in R, and let q be a function on κ⁻¹L/L with q(z) = exp B(x, rx) for
every lift x of z. Then the fourth power of the Gauss sum ∑ q(z) is real. -/
lemma gauss_sum_pow_four_real [IsFullRankLattice L] [IsDomain R] [Module.Finite ℤ R]
    {κ r} [NeZero κ] (q : h.MulKernel κ → ℂ) (H : ∀ x : h.divLattice κ,
  q x = exp (B x (F r x))) : (∑ z, conj (q z)) ^ 4 = (∑ z, q z) ^ 4 := by
  choose a b c d e using (card (h.MulKernel κ) ^ 2 - 1).sum_four_squares
  let M := !![(a : ℤ), b, c, d; -b, a, -d, c; -c, d, a, -b; -d, -c, b, a]
  have T : ∀ {z}, 1 = q z ^ card (h.MulKernel κ) ^ 2 := by simpa [forall_mk, H, ← mk_zero,
          ← exp_nsmul, pow_mul, sq] using (H <| card (h.MulKernel κ) • ·)
  simp [sum_pow, inv_eq_of_mul_eq_one_left (T ▸ pow_sub_one_mul ..), ← inv_eq_conj,
    norm_eq_one_of_pow_eq_one T.symm]
  refine Finset.sum_bijective (M • ·) (Finite.surjective_iff_bijective.1 fun p ↦ ⟨-Mᵀ • p, by
    linear_combination (norm := (ext j; fin_cases j <;> simp [M, Fin.sum_univ_four, sq, sub_nsmul,
    NeZero.one_le, mul_smul] <;> module)) -e • p⟩) (by simp) (mk_surjective.comp_left.forall.2 ?_)
  simp [← mk_zsmul, ← mk_add, H, ← e, ← exp_nsmul, ← exp_sum, M, Fin.sum_univ_four]
  grind

include h

lemma exp_eq_of_mem_lattice {s t} : x ∈ L → y ∈ L → s = t + B x y - B y x → exp s = exp t := by
  grind [exp_eq_exp_iff_exists_int, IsHermitianAction, h.isAppellHumbert.sub_eq_riemannForm,
    ofReal_intCast]

lemma poincareSeries_add l (hl : l ∈ L) : h.isAppellHumbert.poincareSeries (x + l) y =
  (h.multiplier l)⁻¹ * exp (-(B l x + B l l / 2)) * h.isAppellHumbert.poincareSeries x y :=
  ((Equiv.addRight ⟨l, hl⟩).tsum_eq _).symm.trans ((tsum_congr (by
  simp [IsAppellHumbert.poincareTerm, h.isAppellHumbert.3, *, ← exp_add,
    field]; grind [h.isAppellHumbert.sub_eq_riemannForm])).trans tsum_mul_left)

variable [IsFullRankLattice L]

lemma isContPeriodic_poincareSeries a w : IsContPeriodic L.toAddSubgroup fun x ↦
  h.isAppellHumbert.poincareSeries (F (star a) (x + w)) (F a (x + w)) :=
  (h.isAppellHumbert.poincareSeries_spec h.3).2.elim fun _ A ↦
  ⟨by fun_prop, by simp_all [add_rotate _ _ w, poincareSeries_add,
  (A.1 _).2, multiplier_eq_exp, action_comm, h.4, h.1, exp_neg, exp_add, field]⟩

/-- If c − c̄ acts invertibly on V, the mean over V/L of x ↦ K(c̄x, cx), times the complex
conjugate of det(c̄ | V), has real fourth power; K is the Poincaré series
`IsAppellHumbert.poincareSeries` for B and the canonical multiplier of β. -/
lemma isSelfAdjoint_quotMean_pow [IsDomain R] [Module.Finite ℤ R]
    c {κ} [NeZero κ] (k : κ = c - star c) :
  IsSelfAdjoint ((quotMean L.toAddSubgroup (fun x ↦
  h.isAppellHumbert.poincareSeries (F (star c) x) (F c x)) * conj (F (star c)).det) ^ 4) := by
  borelize V
  obtain ⟨b, _⟩ := finBasis ℂ V, ‹IsFullRankLattice L›.1
  let e := b.equivFun.symm.toContinuousLinearEquiv
  let M a := (.pi (B <| b ·) ∘ₗ (F a).1 ∘ₗ e.1.1).toMatrix'
  have Mt a : (M a)ᴴ = M (star a) := ext (by simp [M, e, ← h.2, h.4])
  have X a x : star x ⬝ᵥ M a *ᵥ x = conj (B (F a (e x)) (e x)) := by simp [M, e, dotProduct, ← h.2]
  have P := PosDef.of_dotProduct_mulVec_pos (M (κ * star c))ᴴ.isHermitian_add_transpose_self fun x
    _ ↦ (zero_lt_real.2 (h.3 (F κ (e x)) (by simpa [map_eq_zero_iff, action_injective]))).trans_eq
    (by simp [re_eq_add_conj, h.4, ← h.2, *]; ring)
  let g a x := (B x (F (κ * a) x)).exp
  have I : ∫ x, g c x ∂(realMeasure _).map e = _ := .trans
    (by simp (disch := fun_prop) [integral_map, g, ← h.2, *]) (integral_gauss P 0)
  let a := star β * κ - c
  obtain ⟨n, _, D⟩ := IsAccretive.det_ne_zero P, isFiniteMeasure_addOrbitMeasure
    ((realMeasure _).map e) (isCocompact_of_isFullRankLattice (L := L)),
    congr(($((ext (by simp [↓Mt, M, k]) : (M κ)ᴴ = -M κ)) ^ 4).det)
  norm_num [(.trans (ext (by simp [M, e])) (LinearMap.toMatrix'_mul ..) :
    M (κ * star c) = M κ * (F (star c)).toMatrix b b)] at n D I; have i z :=
    ((Integrable.of_integral_ne_zero (I.trans_ne (by simp_all))).comp_add_right z).const_mul
  have H (x : h.divLattice κ) y (l : x.1 - y ∈ L) : g a x = g a y := h.exp_eq_of_mem_lattice l (h.1
    a _ (sub_mem x.2 (h.1 (β * κ) _ l))) (by simp [a, k, h.4, action_comm, h.6]; ring)
  erw [IsSelfAdjoint, quotMean_tsum_eq_integral _ _ (integrable_finsetSum _ fun z _ ↦ i z.out (g a
    z.out)) (by simpa using! h.isContPeriodic_poincareSeries c 0) fun x ↦
    ((((preimageMkEquivAddSubgroupProdSet ..).trans (.prodCongr (AddSubgroup.addSubgroupOfEquivOfLe
    (h.1 κ)).1 (Equiv.Set.univ _))).symm.trans ((Equiv.Set.univ _).trans
    (LinearEquiv.ofInjectiveEndo _ (action_injective κ)).subtypeEquivOfSubtype) : _ × h.MulKernel
    κ ≃ L).hasSum_iff.2 ((h.isAppellHumbert.poincareSeries_spec h.3).1 ..).hasSum).prod_fiberwise
    fun l ↦ (hasSum_fintype _).congr_fun fun z ↦ show h.isAppellHumbert.poincareTerm _ _
    ⟨F κ (_ + l), _⟩ = _ by simp [↓H _ (z.out + l), g, a, action_comm, exp_add, multiplier_eq_exp,
    exp_sub, *, h.4, IsAppellHumbert.poincareTerm, AddSubgroup.vadd_def, field]]
  simp [integral_finsetSum, integral_add_right_eq_self, ← Finset.sum_mul, *, -k, field,
    h.gauss_sum_pow_four_real (g a ·.out) (H _ · (eq_iff_sub_mem.1 (out_eq' (_ : h.MulKernel κ))))]
