/- GID: D5/S3/Zeros/GRH/Lib/Shimura/GoodReduction/ArcReduction
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Shimura/GoodReduction/ArcReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Shimura.GoodReduction.ArcReduction. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Shimura/GoodReduction/ArcReduction.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Shimura.GoodReduction.PeakContraction
import D5.S3.Zeros.GRH.Lib.Shimura.ThetaModuli.FamilyFromPoints
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Good reduction of unitary PEL abelian varieties, in analytic form (no toric
degeneration). Here a torus with polarisation prime to p is assumed to have arbitrarily expanding
non-unit multipliers dividing a power of p, prime to their conjugates, whose conjugates have unit
determinant on the Lie algebra. Then the sup of a valuation of theta values at torsion points is
multiplicative. Source: K.-W. Lan, Elevators for degenerations of PEL structures, Math. Res. Lett.
18 (2011); R. Kottwitz, Points on some Shimura varieties over finite fields, J. Amer. Math. Soc. 5
(1992), §5 (division algebra case); for the CM case B. Conrad, Semistable reduction for abelian
varieties (notes), Prop. 6.3, after Serre and Tate, Ann. of Math. 88 (1968).

This file: Theta tori over good places have multiplicative sup norm; degree and level are units. -/

open NumberField IsLocalRing Valuation LinearMap Ideal IsPrime valuationSubring PeriodMap

/-- Good reduction of a theta torus x: if Φ_{v₀} maps O_E into the valuation ring of v, over a
prime good for D, then the v-adic sup norm on torsion points is multiplicative
(`HasGoodReduction`), and r and |T| are v-units.

Known result: Good reduction of unitary PEL abelian varieties, in analytic form (no toric
degeneration). -/
lemma ThetaTorus.hasGoodReduction_and_val_card_eq_one {E} [Field E] [CMBase E] {V}
  [FinComplexSpace V] {D g ℓ} (x : ThetaTorus D g ℓ V)
  {v} {ρ : 𝓞 E →+* v.valuationSubring} (B : ∀ c, ρ c = Φ v₀ c.val) (hw : D.IsGoodAt
  (comap ρ (maximalIdeal _))) : HasGoodReduction x.B x.multiplier v D.r ∧ v (Nat.card D.T) = 1 := by
  have ⟨⟨hr, hT⟩, p, b, pp, pw, bw, cb, _, w, ww, pw', q⟩ := hw
  obtain ⟨⟨t, tw, tn⟩, n⟩ := Set.not_subset.1 (ww ∘ w.isMaximal.eq_of_le ne_top'),
    notMem_of_isCoprime_of_mem cb bw
  simp [(integers v).isUnit_iff_valuation_eq_one, B] at hr hT tn n
  let H := (2⁻¹ : ℂ) • (x.B + x.B.pullForm (Complex.I • 1))
  have : riemannForm H = x.B.riemannForm := by ext; simp [riemannForm, H, re_symm]; ring
  use ⟨x.hasGoodReduction_trivial.1, by grind [dualLattice_periodLattice,
    card_nsmul_mem_periodLattice], hr, x.hasGoodReduction_trivial.4,
    hasMultiplicativeNorm_of_expanding (B := H) ⟨x.intAction_mem_periodLattice, fun y z ↦ by
    simpa [H, Complex.ext_iff, re_symm, add_comm] using x.re_symm (Complex.I • y) (Complex.I • _),
    (by simpa [H, riemannForm, field] using x.isPosRiemann.1 · ·), by simp [H, ← adjoint],
    this ▸ x.isAppellHumbert_periodLattice.le_dualLattice, D.star_beta⟩
    (hw.1.2 <| mem_of_dvd _ ·.natCast pw) (by grind [dualLattice_periodLattice,
    card_nsmul_mem_periodLattice, RealComplexForm.dualLattice]) pp (by simp_all
    [v.mem_maximalIdeal_iff]) ((Continuous.tendsto' (by simp [continuous_clm_apply]; fun_prop) _ _
    x.isPeriodMap.complexMul.2).frequently (Metric.nhds_basis_ball.frequently_iff.2 fun r r0 ↦
    have ⟨a, ⟨k, ha⟩, nu, A⟩ := exists_pow_eq_span_inv_lt w.one_lt_q r0
    have K {y} h := mem_span_singleton.1 (ha.le (pow_mem_pow (x := y) h k))
    have h σ {y} h (e : v (σ y.val) = 1) := (@K y h).elim fun c k ↦
      have I c := (integers (v.comap σ)).mem_of_integral c.2.tower_top
      eq_one_of_one_le_mul_left (a := v (σ a)) (I a) (I c) (by simp [← map_mul, ← k, e])
    ⟨(Φ · (star a))⁻¹, by simp [pi_norm_lt_iff, *], star a,
      k, by simp [intAction, ← x.Q.eq_symm_apply,
      funext_iff, (by aesop : a ≠ 0)], by simpa, by grw [star_star, ← starRingAut_apply, K q]; simp
      [cb.symm.pow], by simpa using map_dvd starRingAut (K pw'), x.4.rec fun ε _ ↦ by
    simpa [← det_conj _ ε, det_prodMap, piMap, det_pi, h _ q, *, h _ tw, Subtype.forall'.1
      D.emb_beta_eq_of_ne] using .inl (h (star _) q (by simpa))⟩))⟩
