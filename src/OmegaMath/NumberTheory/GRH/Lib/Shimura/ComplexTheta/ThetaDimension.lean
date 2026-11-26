import OmegaMath.NumberTheory.GRH.Lib.Adelic.Adeles.AdditiveCharDefs
import OmegaMath.NumberTheory.GRH.Lib.Shimura.Uniformisation.LieExponential
import OmegaMath.NumberTheory.GRH.Lib.General.Analysis.FundamentalDomain
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: Frobenius' dimension formula and irreducibility of the theta group. The form here
is basis-free and says that the square of the dimension is the index of the lattice in its dual. It
is proved together with irreducibility from a theta kernel on the torus, with no symplectic basis,
and the orthogonality relation and absence of base points follow. Source: G. Frobenius, Über die
Grundlagen der Theorie der Jacobischen Functionen, Crelle 97 (1884); Birkenhake–Lange, Complex
Abelian Varieties, 3.2.7, 4.1.5, 6.4; survey of proofs in D. Bump, A. Pekker, Proc. AMS 130 (2002)
3473–3481.

This file: Theta series converge; Frobenius dimension formula, irreducibility and Schur's lemma for
the theta group. -/


open FourierTransform Complex Module MeasureTheory QuotientAddGroup Fintype Quotient
  LinearMap.BilinForm Submodule Finset ComplexConjugate IsZLattice
variable {V : Type} [FinComplexSpace V] {L : Submodule ℤ V} [IsFullRankLattice L] {B :
  LatticeForm L} {χ f} [hB : IsAppellHumbert B χ] [hp : IsPosRiemann B] (hf : f ∈ B.thetaSpace χ)
attribute [local simp] funext_iff neg_div fieldLe mul_add Real.pi_pos pr_iff isAppellHumbert_iff
  finrank_linearMap sq conj_mul' norm_smul conj_ofNat add_smul mk_eq_add_mul_I
attribute [local simp ←] exp_add mul_sum integral_conj Real.exp_add zsmul_eq_mul' map_zsmul

/-- Let f have no zero and f(l + z)/f(z) have constant logarithmic derivative for each l in the
lattice L. Then f(z + l) = f(z)·exp(B(l,z))·f(l)/f(0) for some real-bilinear B, complex-linear in z,
with Re B symmetric. -/
lemma exists_factor_of_automorphy (h0 : ∀ z, f z ≠ 0) (D : ∀ l : L, let g := (f <| l + ·) / f
  ∃ a : V →L[ℂ] ℂ, ∀ z, HasFDerivAt g (g z • a) z) : ∃ B : RealComplexForm V, (∀ᵉ (l ∈ L) (z),
    f (z + l) = f z * (B l z).exp * f l / f 0) ∧ ∀ u v, (B u v).re = (B v u).re := by
  choose a D using D
  obtain ⟨B, rfl⟩ : ∃ B : V →L[ℝ] _, (B ·.1) = a := let F := AddMonoidHom.mk' a (fun l m ↦
   (smul_right_inj (by aesop)).1 ((D _ 0).unique (by convert (D m 0).mul ((hasFDerivAt_comp_add_left
      ↑m).2 (D l _)) <;> ext <;> simp <;> grind))); ⟨((finBasis ..).ofZLatticeBasis
    ..).constrL (F ∘ finBasis ..), by simp [Int.cast_smul_eq_zsmul, ← map_sum]; tauto⟩
  exact (⟨B, ·, fun u v ↦ have t := eq_top_iff'.1 ‹IsFullRankLattice L›.2.1
    by induction t u, t v using span_induction₂ <;> simp_all; grind⟩)
    (by simpa [exp_neg,
    add_comm, field, *] using fun l ↦ have k z := (D l z).mul (-B l).hasFDerivAt.cexp
    (is_const_of_fderiv_eq_zero (⟨_, k ·⟩) (k · |>.fderiv.trans (by module)) · 0))

instance : CompactSpace (V ⧸ L.toAddSubgroup) :=
  ⟨range_mk.subst (isCompact_range_of_periodic L _ continuous_mk (by simp))⟩

omit [IsFullRankLattice L] in
lemma IsPosRiemann.nondegenerate : B.riemannForm.Nondegenerate := .ofSeparatingLeft fun u ↦
  (by simpa [·] using hp.1 u)

omit [IsFullRankLattice L] in
/-- Positivity of the Riemann form is an open condition on B: if `IsPosRiemann` holds for B, it
holds for every B' near B. -/
lemma IsPosRiemann.eventually_add_neg : ∀ᶠ A in nhds 0, IsPosRiemann (B + -A) :=
  ((isCompact_sphere 0 1).eventually_forall_mem (fun A u ↦ (B - A).riemannForm u (I • u)) _
  (by aesop (add safe Ioi_mem_nhds)) (by simp [riemannForm]; fun_prop)).mono fun A H ↦ ⟨fun
  u ↦ (by simpa [smul_comm I, ·] using H (‖u‖⁻¹ • u))⟩

scoped instance IsAppellHumbert.isFullRankLattice_dualLattice :
  IsFullRankLattice B.dualLattice := by rw [RealComplexForm.dualLattice, copy_eq,
  ← (finBasis _ L).ofZLatticeBasis_span ℝ, dualSubmodule_span_of_basis _ hp.nondegenerate]; exact {}

lemma IsPosRiemann.isDualFamily :
  IsDualFamily L.toAddSubgroup fun (a : B.dualLattice) x ↦ 𝐞 (B.riemannForm x a) := by
  use fun a ↦ ⟨by continuity, (a.2 · · |>.rec ?_)⟩, ?_, ?_, ?_, fun x h ↦ ?_,
    fun a h ↦ a.ext (hp.nondegenerate.flip.ker_eq_bot.le (eq_zero_of_exp_eq_one _ h))
  iterate 4 simp_all [riemannForm_swap (_ : B.dualLattice).1, exp_add, exp_neg]
  rw [← (finBasis ℤ L).ofZLatticeBasis_span ℝ, RealComplexForm.dualLattice, copy_eq] at *
  exact (dualSubmodule_flip_dualSubmodule_of_basis _ nondegenerate _).le (by
    simpa [↓Circle.coe_eq_one, ↓fourierChar_eq_one, riemannForm_swap x, eq_comm] using h ⟨·, ·⟩)

include hB hf
omit hp

/-- For a theta function f of Appell–Humbert data (B, χ), the set of the absolute values
|exp(−B(a, a)/2)·f(a)|, a in V, is compact. -/
lemma IsAppellHumbert.isCompact_range_norm_thetaShift : IsCompact (.range (‖B.thetaShift · f 0‖)) :=
  isCompact_range_of_periodic L _
  (.norm (.mul (by fun_prop) (by simp [hf.1.continuous]))) (by simp_all [thetaShift_add_mem hf])

/-- Let f be a theta function for Appell–Humbert data (B, χ) on a lattice L in V, with Riemann
form E. If E(u, iu) ≤ 0, then f(tu) = exp(t²B(u, u)/2)·f(0) for all complex t. -/
lemma IsAppellHumbert.apply_smul_of_nonpos u (h : B.riemannForm u (I • u) ≤ 0) t : f (t • u) =
  (t * t * B u u / 2).exp * f 0 := by
  simpa [field, exp_neg] using liouville_theorem_aux (f := fun t ↦ exp (-t * t * _ / 2) * f (t • u))
    (by cases hf; fun_prop) (isBounded_iff_forall_norm_le.2 (.imp (by
    simp [upperBounds, thetaShift]; rintro C H ⟨⟩; grw [← H]; gcongr
    simp [mul_smul, hB.1, riemannForm] at *; nlinarith)
    (isCompact_range_norm_thetaShift hf).bddAbove)) t 0

/-- If a theta function f for Appell–Humbert data (B, χ) on a lattice L in V vanishes nowhere,
then the Riemann form of B is zero, χ = 1 on L, and f(z) = exp(B(z, z)/2)·f(0) for all z. -/
lemma IsAppellHumbert.eq_exp_of_ne_zero (h0 : ∀ z, f z ≠ 0) : B.riemannForm = 0 ∧
  (∀ l ∈ L, χ l = 1) ∧ ∀ z, f z = (B z z / 2).exp * f 0 :=
  have h z := (le_total ..).elim (apply_smul_of_nonpos hf z) fun _ t ↦ by simpa [exp_neg,
    field, *] using (hB.neg.apply_smul_of_nonpos ⟨hf.1.inv h0, by simp_all [hf.2, exp_add, exp_neg,
    field]⟩ z (by simpa) t).symm
  have q z := by simpa [*] using congr(‖$(h (I • z) 1)‖)
  ⟨LinearMap.ext₂ (have := q <| · + I • ·; by simp_all [riemannForm, smul_smul]; linarith), fun l ↦
    (by simpa [h0, by simpa using h l 1] using hf.2 l · 0), by simpa using (h · 1)⟩

omit hf

/-- For Appell–Humbert data (B, χ) on the lattice L, real-linear T_c analytic near c = b, and Re
B(x, T_b x) > 0 for x ≠ 0, the series ∑_{l ∈ L} exp(ξ(u + T_c l) − B(l,z) − B(l,T_c
l)/2)/χ(l) converges and is analytic in (c, ξ, u, z) at c = b. -/
lemma IsAppellHumbert.summable_and_analyticAt_tsum {P b} [FinComplexSpace P] {T : P → V →L[ℝ] V}
  (h : ∀ᶠ b in nhds b, ∀ x, AnalyticAt ℂ (T · x) b) (k : ∀ x ≠ 0, 0 < (B x (T b x)).re) p :
  let X := fun (c, (ξ : StrongDual ℂ V), u, z) l ↦ ξ (u + T c l) - B l z - B l (T c l) / 2
  let t q (l : L) := (X q l).exp / χ l
  Summable (t (b, p)) ∧ AnalyticAt ℂ (tsum <| t ·) (b, p) := by
  intro X t; borelize V; have := continuousAt_clm_apply.2 (h.self_of_nhds · |>.continuousAt)
  have ⟨c, k, G⟩ := ((isCompact_sphere (0 : ℝ × _) 1).eventually_forall_of_forall_eventually (x₀ :=
    (0, b, p)) (P := fun (c, q) (s, l) ↦ (X (q.1, (s * c) • q.2) l).re + s * c * ‖l‖ < s ^ 2)
    fun (s, x) m ↦ ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by
      simp_all [X]; grind [sq_nonneg, norm_zero, sq_abs, zero_re])).curry_nhds.exists_gt
  have s := (summable_of_isBigO (ZLattice.summable_norm_rpow _ _ (sub_one_lt _)) (.comp_tendsto
    (isLittleO_exp_neg_mul_rpow_atTop one_pos _).isBigO (tendsto_norm_cocompact_atTop.comp
    (L.toAddSubgroup.tendsto_coe_cofinite_of_isDiscrete ⟨‹IsFullRankLattice _›.1⟩)))).mul_left
    (c⁻¹ ^ 2).exp
  exact (fun n ↦ ⟨s.of_norm_bounded (n.self_of_nhds · |>.2), funext (integral_count_eq_tsum <| t ·)
    ▸ analyticAt_of_eventually_differentiable (eventually_differentiableAt_integral
    (integrable_count_iff.2 s.abs) (by fun_prop) n)⟩) (G.mp ((h.prod_inl_nhds p).mono fun q _ G l ↦
    ⟨by fun_prop, by simpa [t, hB.2, X, -Prod.norm_mk, k.ne'] using
    (G (NormedSpace.normalize (c⁻¹, l)) (by aesop)).le⟩))

/-- If Re B(x,x) > 0 for x ≠ 0, the Poincaré series K(x, y) converges, is continuous, and is a
theta function of type (B, χ) in y; K(x, x) has mean χ(0)⁻¹ over V/L and is not identically
zero. -/
lemma IsAppellHumbert.poincareSeries_spec (h : ∀ x ≠ 0, 0 < (B x x).re) : (∀ x y, Summable
  (hB.poincareTerm x y)) ∧ Continuous ↿hB.poincareSeries ∧ (∀ x, hB.poincareSeries x ∈ B.thetaSpace
  χ) ∧ (quotMean L.toAddSubgroup fun x ↦ hB.poincareSeries x x) = (χ 0)⁻¹ ∧ ∃ w, hB.poincareSeries w
  w ≠ 0 := have A := summable_and_analyticAt_tsum (T := 1) (by simp [analyticAt_const]) h
  (fun k ↦ ⟨fun _ _ ↦ (A (_, _, _)).1, .of_at fun _ ↦ (A _
    ).2.continuousAt.comp (f := (I, _, _, Prod.snd ·)) (by fun_prop), fun x ↦ ⟨(.comp (f :=
              (I, _, _, ·)) · (A _).2.differentiableAt (by fun_prop)), fun m hm z ↦ (tsum_congr (by
    have := @hB.ne_zero; simp [poincareTerm, hB.3, *, field]; grind [sub_eq_riemannForm])).trans
    (((Equiv.addLeft ⟨m, hm⟩).tsum_eq _).trans tsum_mul_left)⟩, k, by contrapose! k; simp [k,
    hB.ne_zero, eq_comm]⟩) (by delta poincareSeries; convert ((isPosRiemann_of_re_pos
    h).isDualFamily.tsum_coeff_eq_quotMean (⟨_, hB.le_dualLattice ·.2⟩) (S :=
    {0}) (by simp) (A 0).1).symm <;> simp [poincareTerm, exp_sub, ← hB.sub_eq_riemannForm, field])

include hp

/-- For Appell–Humbert data with positive Riemann form, the twisted translations by the dual
lattice span the endomorphisms of the space of theta functions, whose dimension is positive
and has square the index of L in the dual lattice.

Known result: Frobenius' dimension formula and irreducibility of the theta group. -/
lemma IsAppellHumbert.finrank_sq_eq_relIndex : span ℂ (Set.range hB.thetaShiftEnd) = ⊤ ∧
  finrank ℂ (B.thetaSpace χ) ^ 2 = L.toAddSubgroup.relIndex B.dualLattice.toAddSubgroup ∧ 0 <
  finrank ℂ (B.thetaSpace χ) := let T := (I / 2) • (B ∘L .lsmul ℝ ℂ I + I • B)
  have {u v} : T u v = T v u := by
    simpa [T, Complex.ext_iff, hB.1, add_comm] using hB.1 (I • u) (I • v)
  have A : IsAppellHumbert (B + T) χ := by simp_all [riemannForm]
  have ⟨_, _, h, _, w, k⟩ :=
    A.poincareSeries_spec (by clear this A; simp_all [T, riemannForm]; grind)
  let N := (L.submoduleOf _).toAddSubgroup
  have up {n s} (hs : LinearIndependent ℂ s) : ∃ ψ : _ →ₗ[ℂ] _ ⧸ N → ℂ, (⇑ψ).Injective :=
    let P s t b x := (T b b / 2).exp * ∑ i, conj (B.thetaShift x (s i) 0) * B.thetaShift x (t i) b
    have (f : B.thetaSpace χ) : Continuous ↿(B.thetaShift · f) :=
      .mul (by fun_prop) (f.2.1.continuous.comp (by fun_prop))
    have p {s t b} : IsContPeriodic _ (P s t b) := ⟨by fun_prop, (by
      simp_all [add_comm ·, P, hB.thetaShift_add_mem, mul_mul_mul_comm _ (conj _)])⟩
    let m s t b := quotMean L.toAddSubgroup (P s t b)
    have d s t : Differentiable ℂ (m s t) := fun b ↦
      ((isAnalyticFamily_of_differentiable (.of_forall fun _ _ ↦
      ⟨((isQuotientMap_mk _).continuous_lift_prod_right (by simp [p.apply_out_mk]; fun_prop)
      ).continuousAt, by have := (t · |>.2.1); fun_prop⟩)).analyticAt_integral _).differentiableAt
    have k s t b : m t s (-b) = conj (m s t b) := (quotMean_translate p b).symm.trans (by
   simp [m, P, T, quotMean, mul_sum, thetaShift, ← exp_conj, ← mul_assoc, mul_right_comm _ (conj _),
    add_comm b]; congr! 6; simp [Complex.ext_iff, hB.1]; bound)
    have Z {s t} (h : m s t 0 = 0) b := by simpa [*] using congrArg (‖·‖) ((((d s t).comp
      differentiable_id.neg).neg.mul (d t s)).cexp.apply_eq_apply_of_bounded
      (isBounded_iff_forall_norm_le.2 ⟨1, by simp [k, mul_nonneg]⟩) b 0)
    ⟨.pi fun q ↦ ⟨⟨(m (thetaShiftEnd q.out ∘ s) · 0), by intros; erw [← integral_add] <;> simp [m,
      quotMean, P, ↓p.integrable_out]⟩, by simp [m, P, mul_left_comm]⟩, .of_ker _
    fun t ht ↦ by ext i y; simpa using linearIndependent_iff.1 hs (conj <| t · |>.1 y) (by
      ext x; simpa [P, thetaShift, mul_mul_mul_comm] using
        hp.isDualFamily.eq_zero_of_coeff (@p t s (x - y)) (fun a _ ↦ by
      have ⟨⟨l, (h : ↑l ∈ L)⟩, e⟩ := mk_out_eq_add N a
      simpa [P, hB.thetaShift_add_mem, *, hB.thetaShift_comm _ a, A.ne_zero, thetaShift_apply B a,
        mul_left_comm
        (conj _), mul_left_comm (exp (_ * _)) (exp _)] using Z congr($ht a) (_ - a)) y) i⟩
  have := @ofFinite (_ ⧸ N) ((finiteQuotient_iff _).2 (by
    simp [ZLattice.rank ℝ, (submoduleOfEquivOfLe hB.le_dualLattice).finrank_eq]))
  have x := of_riemannForm_eq hB (by simp [riemannForm, *]) (by simp) (h w)
  have := Finite.pi_iff.1 ((@up _ ![⟨_, x⟩] (by simp; tauto)).elim .of_injective) 0
  have li := ((iSupIndep.iInf _ fun y ↦ End.eigenspaces_iSupIndep
    (.mulLeftRight _ (hB.thetaShiftEnd (-y), thetaShiftEnd y))).comp (f := fun (q : _ ⧸ N) y ↦
    B.riemannPhase q.out y.1) fun _ _ h ↦ out_equiv_out.1 (leftRel_apply.2 (hp.isDualFamily.5 _
    (by simp_all [exp_add, exp_neg])))).linearIndependent _ (v := (thetaShiftEnd ·.out)) (by
    simp [DFunLike.ext_iff, Subtype.ext_iff, thetaShift, ← mul_assoc, add_assoc]
    grind [sub_eq_riemannForm]) fun q
    h ↦ by simpa [thetaShift, k] using congr(($h ⟨_, x⟩).1 (w - q.out))
  have e := li.fintype_card_le_finrank.antisymm (by
    simpa using finrank_le_iff_exists_linearMap.2 (up (finBasis ..).linearIndependent))
  ⟨eq_top_mono (by gcongr; simp) (li.span_eq_top_of_card_eq_finrank e),
    .trans (by simp) (e ▸ card_eq_nat_card), pos_of_ne_zero (by simp [·] at e)⟩

/-- Irreducibility: for Appell–Humbert data with positive Riemann form, a complex space of
functions that contains all twisted translates, by the dual lattice, of one non-zero theta
function contains every theta function.

Known result: Frobenius' dimension formula and irreducibility of the theta group. -/
lemma IsAppellHumbert.thetaSpace_le_of_thetaShift_mem (hf : f ∈ B.thetaSpace χ) (h : f ≠ 0) S (H :
  ∀ a ∈ B.dualLattice, B.thetaShift a f ∈ S) : B.thetaSpace χ ≤ S := (Projective.exists_dual_eq_one
  ℂ h).elim fun ℓ E g m ↦ by simpa [E] using! mem_span.1 (eq_top_iff'.1 finrank_sq_eq_relIndex.1
  ((ℓ.domRestrict _).smulRight ⟨g, m⟩)) ((S.submoduleOf _).comap (.applyₗ ⟨f, hf⟩)) (by aesop)

/-- Schur's lemma: for Appell–Humbert data with positive Riemann form, an endomorphism of the
space of theta functions that commutes with the twisted translations by the dual lattice is
a scalar. -/
lemma IsAppellHumbert.schur_lemma {Q : End ℂ (B.thetaSpace χ)} (h : ∀ a,
  Commute (thetaShiftEnd a) Q) : ∃ c : ℂ, Q = c • 1 := (Algebra.IsCentral.mem_center_iff ℂ).1
  (Subring.mem_center_iff.2 (Commute.span_left (by aesop) · (finrank_sq_eq_relIndex.1.ge ⟨⟩)))

lemma IsAppellHumbert.exists_theta_ne_zero : ∃ f ∈ B.thetaSpace χ, f ≠ 0 :=
  exists_mem_ne_zero_of_ne_bot (by grind [finrank_bot, → finrank_sq_eq_relIndex])

lemma IsAppellHumbert.exists_nsmul_mem_of_mem_dualLattice : ∃ N ≠ 0, ∀ a ∈ B.dualLattice, N • a ∈
  L := ⟨_, by nlinarith [hB.finrank_sq_eq_relIndex], fun _ ↦ (L.toAddSubgroup.nsmul_relIndex_mem ·)⟩
