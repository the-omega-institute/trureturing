import GRH.Lib.Shimura.GoodReduction.GaussUnfolding
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Good reduction of unitary PEL abelian varieties, in analytic form (no toric
degeneration) (known result; see Lib.Shimura.GoodReduction.ArcReduction).

This file: Theta identity by Schur, kernel of c keeps peaks, descent and contraction of defects. -/

namespace IsHermitianAction

open MeasureTheory Complex NNReal Function Finset LinearMap Ideal Filter FiniteDimensional
variable {V R} [FinComplexSpace V] [CommRing R] [StarRing R] {L :
  Submodule ℤ V} {B F f} {β c d : R} (h :
  IsHermitianAction L B F β) {v} [NeZero c] [NeZero d] {A : LatticeForm L}

/-- For a in R and x torsion modulo L, the vector ax (the action F a applied to x), again
torsion modulo L because F a preserves L. -/
abbrev torsionAction (a : R) (x : torsionPoints L) : torsionPoints L :=
  ⟨F a x, x.2.imp (by grind [IsHermitianAction])⟩

include h

lemma normShift_comm x y : h.normShift x (h.normShift y f) = B.riemannPhase x y • h.normShift y
  (h.normShift x f) := by simp [normalizedShift, h.isAppellHumbert.thetaShift_comm x]; module

lemma multiplier_sq l (k : l ∈ L) : h.multiplier l ^ 2 = 1 :=
  h.isAppellHumbert.exp_riemannForm_pow_eq_one (nsmul_mem (h.1 _ l k) 1) (nsmul_mem k 1)

lemma isAmpleType : IsAmpleType B h.multiplier :=
  ⟨h.isAppellHumbert, isPosRiemann_of_re_pos h.3, 2, nofun, h.multiplier_sq⟩

attribute [local simp] funLeft canonicalMultiplier out_mem_iff_eq_zero thetaShift_apply mul_smul
  add_mem

lemma sizeAt_add x w : B.sizeAt v f (x + w) = v (h.normShift x (h.normShift w f) 0) := by
  simp [↓← h.isAppellHumbert.sizeAt_thetaShift, normalizedShift, LatticeForm.sizeAt,
    h.isAppellHumbert.valuation_exp_riemannForm (h.torsionAction ..)]

lemma sizeAt_eq_normShift x : B.sizeAt v f x =
  v (h.normShift x f 0) := by simpa [normalizedShift] using h.sizeAt_add x 0

variable [IsDomain R] [IsFullRankLattice L] [Module.Finite ℤ R]

lemma mem_torsionPoints (a : h.divLattice c) : ↑a ∈ torsionPoints L :=
  ⟨_, Nat.card_pos.ne', L.toAddSubgroup.nsmul_relIndex_mem a.2⟩

lemma torsionAction_surjective c [NeZero c] :
  Surjective (h.torsionAction c) | ⟨y, n, _⟩ => ⟨⟨(F c).inverse y, (h.mem_torsionPoints (c :=
  c) ⟨n • (F c).inverse y, by simp_all [divLattice]⟩).imp' (· * n) (by aesop)⟩, by aesop⟩

variable {w : torsionPoints L} (hd : star c = d) (h1 : ∀ a ∈ B.dualLattice, F c a - a ∈ L ∧
  F d a - a ∈ L)

omit [NeZero d] [IsFullRankLattice L] in
include hd in lemma normShift_map_eq_map_star w f : h.normShift (F d w) (f ∘ F c ∘ (F d).inverse) =
    h.normShift (F c w) f ∘ F c ∘ (F d).inverse := by ext; simp [normalizedShift, riemannForm, h.4,
  action_comm, ← hd]

include hd h1

/-- Let c, d = c̄ be non-zero and the identity on L^∨/L. Every theta function t with canonical
multiplier χ has ∑_{z ∈ (V/L)[d]} χ(cz)⁻¹(U_{cz}t)(cx) = μ·t(dx), U the twisted translation,
μ = #(V/L)[d] times the mean of `IsAppellHumbert.poincareSeries`(dx, cx). -/
lemma exists_sum_normShift_eq_smul : ∃ μ, ∑ _ : h.MulKernel d, quotMean L.toAddSubgroup (fun x ↦
  h.isAppellHumbert.poincareSeries (F d x) (F c x)) = μ ∧ ∀ t ∈ B.thetaSpace h.multiplier,
  (∑ z : h.MulKernel d, h.normShift (F d z.out)) (t ∘ F c ∘ (F d).inverse) = μ • t := by
  let Q := (∑ z : h.MulKernel d, h.normShift (F d z.out)) ∘ₗ funLeft ℂ ℂ (F c ∘ (F d).inverse)
  obtain ⟨rfl, _, _, μ, H⟩ := hd, h.isAppellHumbert.poincareSeries_spec h.3,
    quotMean_comp L.toAddSubgroup (F d) (h.isContPeriodic_poincareSeries 1 0) (h.1 d)
    (action_isInvertible d).surjective, h.isAppellHumbert.schur_lemma (hp := h.isAmpleType.2) (Q :=
    Q.restrict fun t ⟨_, _⟩ ↦ mem_thetaSpace_iff_normalizedShift.2
    ⟨by simp [Q, normalizedShift]; fun_prop, (action_isInvertible d).surjective.forall.2 (by
    simpa [Q] using h.normShift_sum_eq_char_smul d (by grind [mem_thetaSpace_iff_normalizedShift,
      map_mem, normShift_map_eq_map_star]) 1 ⟨·, ·⟩ rfl)⟩) fun ⟨a, ha⟩ ↦ by
    have o y (e : y - a ∈ L) (f : B.thetaSpace h.multiplier) := by
      simpa [h.isAppellHumbert.normalizedShift_normalizedShift h.riemannForm_beta,
        h.riemannPhase_eq_one, h.1, *, -map_sub] using
        congr(h.normShift a $((mem_thetaSpace_iff_normalizedShift.1 f.2).2 _ e))
    exact ext fun f ↦ Subtype.ext (smul_right_injective _ (by simp) (map_smul Q .. ▸ (by simp [Q,
      normShift_comm, h.normShift_map_eq_map_star hd a, h.riemannPhase_eq_one, h.1, *] :
      Q (h.normShift a f) = _).trans (o _ (h1 a ha).2 _))).symm
  have K t ht x := by simpa [Q] using congr(($H ⟨t, ht⟩).1 (F (star c) x))
  exact ⟨_, ((integral_finsetSum _ fun z _ ↦ (h.isContPeriodic_poincareSeries c
    z.out).integrable_out).trans (sum_congr rfl fun _ _ ↦ quotMean_translate (by
    simpa using h.isContPeriodic_poincareSeries c 0) _)).symm.trans (by simp_all [normalizedShift,
    poincareSeries_add, mul_assoc, quotMean]), fun t ht ↦ congr(($H ⟨t, ht⟩))⟩

/-- For B, L as in `IsHermitianAction`, let c, c̄ be non-zero, distinct, coprime, identity on L^∨/L;
p prime, v(p) < 1, v(det c̄) = 1, B − A Riemann-positive. If cw, pⁿw ∈ L, every φ in
`LatticeForm.sizes` for A has φ(y)² ≤ sup_x φ(x)φ(x + w). -/
lemma hasShiftBound_one_of_ker [NeZero (c - d)] {p n : ℕ} (pp : p.Prime) (hv : v p < 1) (N :
  v (F d).1.det = 1) (o : IsPosRiemann (B + -A)) (b : F c w ∈ L) : IsCoprime c d → p ^ n • w.1 ∈ L →
  A.HasShiftBound v w 1 := fun ⟨_, γ, s⟩ T ↦ .of_isPosRiemann_sub h.isAmpleType o fun f hf _ ↦ by
  obtain ⟨rfl, ⟨μ, M, H⟩, ⟨_, rfl, G⟩, ⟨t, ht, x, X⟩, R, D, P, a, hφ⟩ := hd,
    h.exists_sum_normShift_eq_smul hd h1, h.exists_sum_normShift_eq_smul (hd ▸ star_star c)
    (by aesop), by simpa [funext_iff] using h.isAppellHumbert.exists_theta_ne_zero (hp :=
    h.isAmpleType.2), (h.isSelfAdjoint_quotMean_pow c (by rw [hd])).star_eq, h.card_mulKernel d,
    pow_ne_zero n pp.ne_zero, fun {z : h.MulKernel d} ↦ action_comm
    c _ z.out.1 ▸ h.1 c _ z.out.2, LatticeForm.sizes.of_mem_thetaSpace (v := v) h.isAmpleType hf
  have r {ζ : ℂ} (k : ζ ^ p ^ n = 1) := by simpa [k, Algebra.algebraMap_ofSubring] using
    (Valuation.integer.integers v).le_of_dvd ⟨_, sub_eq_of_eq_add' (add_pow_prime_pow_eq' pp 1
    (⟨ζ, (valuation_eq_one_of_pow_eq_one P k).le⟩ - 1 : v.integer) n)⟩
  have E := by simpa [↓smul_smul, ← H _ ht,
    h.normShift_map_eq_map_star] using congr($(G _ (Submodule.smul_mem _ μ ht)) x)
  erw [sum_comm, Fintype.sum_eq_single 0 fun z ↦ (by_contra fun k ↦ · ?_), funext fun x ↦
    (tsum_congr fun l ↦ ?_).trans
    (tsum_comp_neg (star (h.isAppellHumbert.poincareTerm (F (star c) x) (F c x))))] at E
  simp [mem_thetaSpace_iff_normalizedShift.1 ht, h.1, quotMean, ← integral_conj,
    IsAppellHumbert.poincareSeries, conj_tsum, field] at E R D M
  grw [size_le_iSup hφ, one_mul, ← le_sqrt_iff_sq_le, le_of_not_gt fun o ↦ (max_lt o
    (mul_lt_of_lt_one_left o.pos ((powOrderIso _ P).symm_apply_lt.2 ((one_pow _).trans_gt hv)))
    ).not_ge (ciSup_le ((h.torsionAction_surjective (star c)).forall.2 fun q ↦ ?_))]
  have k := sub_eq_iff_comm.1 congr((h.normShift (F (star c) q) * h.normShift (F (star c) (F γ w)) -
    h.normShift (F (star c) q)) $(H f hf) 0).symm ▸ v.map_sub ..
  simp [h.normShift_map_eq_map_star, h.normShift_comm (F γ _),
    mem_thetaSpace_iff_normalizedShift.1 hf, ← sub_one_mul, action_comm c, h.1, b,
    by simpa [N] using congrArg v (by grind : μ ^ 8 = (F (star c)).det ^ 8)] at k
  grw [le_max_iff, le_sqrt_iff_sq_le, ← size_le_iSup (mul_shift_mem_sizes hφ hφ w) (h.torsionAction
    (star c) q), sq, factorsThrough_mkQ_of_mem_sizes hφ (a := _ + w) (b :=
    h.torsionAction (star c) q + h.torsionAction _ (h.torsionAction γ w)) (SModEq.sub_mem.2 (by
    simpa [b, action_comm γ, h.1] using congr(F $(eq_sub_of_add_eq s) w ∈ L))), h.sizeAt_add,
    h.sizeAt_eq_normShift]
  exact k.imp (mul_le_mul_right · _) (.trans' (v.map_sum_le fun z _ ↦ map_mul v .. ▸ mul_le_mul'
    ((OrderIso.le_symm_apply _).2 (r (by simpa [action_comm c, ← exp_nsmul, mul_left_comm] using
    (h.riemannPhase_eq_one (h.5 _ (h.1 γ _ T)) a)))) (h.sizeAt_add (h.torsionAction ..) ⟨_,
    h.mem_torsionPoints ⟨_, a⟩⟩ ▸ size_le_iSup hφ _)))
  simp [IsAppellHumbert.poincareTerm, ↓h.multiplier_eq_exp, ← exp_sub,
    ← exp_conj]; grind [h.exp_eq_of_mem_lattice l.2 (h.1 β _ l.2), action_comm, adjoint, conj_symm]
  -- the pairing of the two kernels is nondegenerate
  simpa [h.1, (L.sub_mem_iff_right a).1 (h1 (F c z.out) fun l hl ↦ by
    have := h.normShift_sum_eq_char_smul c (fun l k ↦ by rw [normShift_comm,
      h.riemannPhase_eq_one (h.5 l k) (@a z), one_smul, (mem_thetaSpace_iff_normalizedShift.1 ht).2
      _ (h.1 _ _ k)]) 1 ⟨(F c).inverse l, by simpa [divLattice]⟩ rfl
    simp [← sum_mul, funext_iff, h.normShift_comm, mem_thetaSpace_iff_normalizedShift.1 ht, *] at *
    simpa [k, riemannForm_swap l, exp_neg, ← fourierChar_eq_one, Circle.ext_iff] using this x).2]
    using congr(F $s z.out ∈ L)

omit hd h1

/-- Descent along c ≠ 0: assume `LatticeForm.HasShiftBound` with constant 1 in all degrees at all y
with cy ∈ L, and c^*B − A Riemann-positive. Then constant D for B at cw gives constant
D·v(#(c⁻¹L/L))⁻² for A at w. -/
lemma hasShiftBound_descent (G : ∀ (A : LatticeForm L) y, F c y.1 ∈ L → A.HasShiftBound v y 1) (p :
  IsPosRiemann (pullForm (F c) B + -A)) {D} : B.HasShiftBound v (h.torsionAction c w) D →
  A.HasShiftBound v w (D * (v (Nat.card (h.MulKernel c)))⁻¹ ^ 2) :=
  have H : IsHermitianAction L _ F β := by grind [IsHermitianAction, pullForm_apply_apply,
    action_comm, riemannForm_def, (action_injective c).ne]
  fun I ↦ .of_isPosRiemann_sub H.isAmpleType p fun t ht@⟨_, _⟩ x ↦ by
  have T a t : h.normShift (F c a) (t ∘ (F c).inverse) = H.normShift a t ∘ (F c).inverse := by
    ext; simp [normalizedShift, riemannForm, action_comm]
  let s (ξ : AddChar (h.MulKernel c) ℂ) := ∑ k, ξ (-k) • h.normShift (F c k.out) (t ∘ (F c).inverse)
  grw [← le_sqrt_iff_sq_le, mul_right_comm, sqrt_mul, sqrt_sq,
    ← (v.map_sum_le fun ξ _ ↦ ?_ : v (∑ ξ, h.normShift (h.torsionAction c x) (s ξ) 0) ≤ .sqrt _)]
  simp [s, sum_comm, ← sum_mul, T, mem_thetaSpace_iff_normalizedShift.1 ht,
    AddChar.sum_apply_eq_ite, field, H.sizeAt_eq_normShift]
  grw [← sizeAt_eq_normShift, le_sqrt_iff_sq_le, fun ξ ↦
    I _ (.of_mem_thetaSpace (f := s ξ) (χ := h.multiplier * fun l ↦ if hl : l ∈ L then
    ξ ⟦⟨(F c).inverse l, by simpa [divLattice]⟩⟧ else 1) ⟨add_zero B ▸ h.isAppellHumbert.add
    (by simp_all [isAppellHumbert_iff, ← ξ.map_add_eq_mul]; tauto), h.isAmpleType.2, 2 * .card
    (h.MulKernel c), by simp_all [mul_pow, pow_mul, multiplier_sq, -canonicalMultiplier,
    ← ξ.map_nsmul_eq_pow]⟩ ⟨by simp [s, normalizedShift]; fun_prop, fun l hl ↦ by
    simpa [normalizedShift, ← neg_add_rev, exp_neg, field, mul_right_comm _ (ξ _), funext_iff, *]
      using h.normShift_sum_eq_char_smul c (by grind [mem_thetaSpace_iff_normalizedShift.1 ht]) ξ
      ⟨(F c).inverse l, by simpa [divLattice]⟩ (refl (s ξ))⟩),
    ← (h.torsionAction_surjective c).iSup_comp, ciSup_le']
  simpa only [h.sizeAt_eq_normShift, ← map_mul, s, map_sum, univ.sum_apply, sum_mul_sum] using
    fun x ↦ v.map_sum_le fun i _ ↦ v.map_sum_le fun j _ ↦
    (mul_le_iSup_of_hasShiftBound ⟨H.isAmpleType, ht⟩ ⟨H.isAmpleType, ht⟩ (x := x + ⟨_,
    h.mem_torsionPoints i.out⟩) (y := x + w + ⟨_, h.mem_torsionPoints j.out⟩)
    (G _ _ (by simp [sub_sub, add_right_comm, sub_mem]))).trans_eq' (by simp [← map_add, T,
    H.sizeAt_add, valuation_eq_one_of_pow_eq_one (orderOf_pos ξ).ne', ← ξ.pow_apply])

variable (G : ∃ᶠ d : V →L[ℂ] V in nhds 0, ∃ c, ∃ _ : NeZero c, (∀ x, F c (d x) = x) ∧
  ∀ (A : LatticeForm L) y, F c y.1 ∈ L → A.HasShiftBound v y 1)
include G

/-- Suppose there are non-zero c with c⁻¹ arbitrarily small on V such that
`LatticeForm.HasShiftBound` holds with C = 1 in every degree for all y with cy ∈ L. Then each
torsion point w satisfies `LatticeForm.HasShiftBound` in degree B for all large C. -/
lemma eventually_hasShiftBound : ∀ᶠ C in atTop, B.HasShiftBound v w C :=
  h.isAmpleType.rec fun A _ _ ↦ by
  have := of_finrank_pos (A.nsmul 2).finrank_sq_eq_relIndex.2.2
  let e x := proj 0 ∘ₗ ((2 • B).thetaShift x).domRestrict ((2 • B).thetaSpace (h.multiplier ^ 2))
  have ⟨g, D⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (mem_span_of_iInf_ker_le_ker (K := e
    0) (L := fun y : {y // (B + B).HasShiftBound v (y + y - w) 1} ↦ e y) fun f hf ↦ by
    simp [e] at hf ⊢; simpa using congr($(eq_zero_of_small_mesh (f.2.1.continuous.comp (f :=
      midpoint ℝ ↑w)
      (by fun_prop [midpoint])) (G.mono fun _ ⟨c, _, e, K⟩ ↦ ⟨_, e, fun z k ↦ hf _ ((add_mem w.2
      (h.mem_torsionPoints ⟨z, k⟩)).imp' (· * 2) (by simp [two_smul])) (K _ _ (by simpa))⟩)) (-w)))
  filter_upwards [mem_atTop (g.support.sup (v ∘ g))] with K o _ (.of_mem_thetaSpace (f := f) H k@⟨_,
    T⟩) x
  have E y : v (e y.1 ⟨fun y ↦ (-B x x).exp * f (x - y) * f (x + y), by fun_prop, fun l hl z ↦ by
      simp [← add_assoc, ← sub_sub, sub_add_cancel _ l ▸ T l hl (x - z - l), exp_add, exp_sub,
      two_mul, field, ↓multiplier_sq, *]⟩) = B.sizeAt v f (x - y) * B.sizeAt v f (x + y) := by
    simp [LatticeForm.sizeAt, e, ← map_mul, mul_mul_mul_comm _ (f _), ← exp_add, ← mul_assoc]; ring
  simpa [sq] using (E 0).ge.trans (D ▸ congr(v $(LinearMap.sum_apply ..)).trans_le (v.map_sum_le fun
    y h ↦ map_mul v .. ▸ mul_le_mul' ((le_sup h).trans o) (E _ ▸ mul_le_iSup_of_hasShiftBound ⟨H,
    k⟩ ⟨H, k⟩ (by aesop))))

/-- Contraction: under `IsHermitianAction`, if there are nonzero c in R with arbitrarily small
inverse on V such that all y with cy in L satisfy `LatticeForm.HasShiftBound` with C = 1 in every
degree, then sup norms of sizes are multiplicative. -/
lemma hasMultiplicativeNorm_of_frequently : HasMultiplicativeNorm v L := fun _ _ _ _ s t ↦
  (G.and_eventually ((by simp [continuous_clm_apply]; fun_prop : Continuous
  (pullForm · (B + B))).tendsto' 0 _ (by aesop) h.isAmpleType.eventually_add_neg)).exists.elim fun _
  ⟨⟨c, _, e, K⟩, P⟩ ↦ (ciSup_mul_le_ciSup_mul_ciSup (bddAbove_of_mem_sizes s)
  (bddAbove_of_mem_sizes t)).antisymm (iSup_mul_iSup_le fun x y ↦ (mul_le_iSup_of_hasShiftBound s t
  ((y - x - 0).2.elim fun n o ↦ .of_doubling id (const _ _) ⟨(v (Nat.card (h.MulKernel c)))⁻¹ ^ 2,
  fun A ↦ have ⟨a, m, Q⟩ := (h.isAmpleType.eventually_isPosRiemann_smul_sub A).exists
  have k := h.nsmul m
  .of_isPosRiemann_sub k.isAmpleType Q fun _ q ↦
    LatticeForm.HasShiftBound.of_doubling (const _ _) Subtype.val ((nonempty_of_mem ((sInter_mem
  (finite_range_nsmul_torsion o.1 (p := LatticeForm.HasShiftBound v _) fun _ _ e ↦ by
    delta LatticeForm.HasShiftBound; congr! 9; apply factorsThrough_mkQ_of_mem_sizes <;> aesop)
  ).2 (Set.forall_mem_range.2 fun _ ↦ k.eventually_hasShiftBound G))).elim (⟨·, Set.mem_iInter.1
    ·⟩)) (fun D I w ↦ k.hasShiftBound_descent K ⟨(by simpa [riemannForm, action_injective c (e _),
    map_eq_zero_iff, action_injective] using (P.nsmul m).1 <| F c ·)⟩ (I
  ⟨_, by simpa using h.1 c _ w.2⟩)) ⟨_, o.2⟩ _ ⟨k.isAmpleType, q⟩⟩ (by aesop) _)).trans (by simp))

omit G

/-- Good reduction: on a polarised torus V/L with adjoint action of an order, β + β̄ = 1, nL^∨ ⊆ L,
p ∤ n, v(p) < 1, sup norms of sizes multiply if non-units c ∣ p^k coprime to c̄ with v(det c̄) = 1
have arbitrarily small inverses on V.

Known result: Good reduction of unitary PEL abelian varieties, in analytic form (no toric
degeneration). -/
lemma _root_.hasMultiplicativeNorm_of_expanding [CharZero R] {n p : ℕ} (hn : ¬p ∣ n) (tor :
  ∀ a ∈ B.dualLattice, n • a ∈ L) (pp : p.Prime) (hv : v p < 1) (hc : ∃ᶠ d : V →L[ℂ] V in nhds 0,
  ∃ c k, (∀ x, F c (d x) = x) ∧ ¬IsUnit c ∧ IsCoprime c (star c) ∧ c ∣ p ^ k ∧
  v (F (star c)).det = 1) : HasMultiplicativeNorm v L := h.hasMultiplicativeNorm_of_frequently
  (hc.mono fun _ ⟨c, k, e, _, co, cp@⟨_, _⟩, _⟩ ↦ have : NeZero c := ⟨by aesop⟩
  ⟨c, ‹_›, e, fun A y _ ↦ by
  have ⟨i, hi, i0, P⟩ := ((Nat.frequently_modEq pp.ne_zero n).and_eventually
    (h.isAmpleType.eventually_isPosRiemann_smul_sub A)).exists
  have := (span {(n * i : R)}).finiteQuotientOfFreeOfNeBot (by aesop)
  have ⟨j + 1, _, e⟩ := ((((pp.coprime_iff_not_dvd.2 (pp.not_dvd_mul hn ((hi.dvd_iff dvd_rfl).1.mt
    hn))).cast.pow_left.mono cp dvd_rfl).map (Ideal.Quotient.mk (span {↑n * ↑i}))
    ).isUnit_of_dvd (by simp)).isOfFinOrder.exists_pow_eq_one
  obtain ⟨co, t, e⟩ := star_pow c _ ▸ co.pow (m := j + 1), mk_span_eq_iff_dvd_sub.1 e
  have := NeZero.mk (sub_ne_zero.2 (by simpa [*] using co.isUnit_of_dvd ·.dvd))
  exact (h.nsmul i0).hasShiftBound_one_of_ker rfl (fun a ha ↦ by simp [eq_add_of_sub_eq e,
    (by simpa using h.1 · _ (tor _ (mem_dualLattice_nsmul.1 ha)))]) pp hv (by simp [*]) P (by grind
    [map_mem]) co (map_natCast F _ ▸ (by grind [action_comm, map_mem] : F ↑(p ^ k) y ∈ L))⟩)
