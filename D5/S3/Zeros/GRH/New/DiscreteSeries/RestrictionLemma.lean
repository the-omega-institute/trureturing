/- GID: D5/S3/Zeros/GRH/New/DiscreteSeries/RestrictionLemma
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/DiscreteSeries/RestrictionLemma
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.DiscreteSeries.RestrictionLemma. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/DiscreteSeries/RestrictionLemma.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.DiscreteSeries.TwoFactorSetup
import D5.S3.Zeros.GRH.Lib.Weil.DualPair.ModularDataDecay
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Discrete series coefficients near 1 and explicitly large Bessel functions. Near 1 a discrete
series coefficient of U(p,q) is an explicit phase times a real factor in [0,1], with uniform error,
and Laplace's method then gives Bessel functions and restriction periods that are explicitly large
at points of controlled size. The integral formula for coefficients, non-vanishing of periods and
fixed-rank asymptotics for coherent states are known. Related work: Nelson–Venkatesh, The orbit
method and analysis of automorphic forms, 2021; H. He, On the Gan–Gross–Prasad conjecture for
U(p,q), 2017; B. Sun, Matrix coefficients of cohomologically induced representations, 2007.

Part of: Every row pairs with a restriction of explicit level (see New.Exchange.RowsReached).

This file: Period of deep-level Poincaré series equals main term up to explicit error. Explicit
lower bound for oscillating integral of two coefficients over a subgroup. Cauchy matrix of
controlled size at which the phases of a restriction period cancel. -/

open MeasureTheory Matrix Space G EuclideanSpace Fintype Set Measure Subtype U Norms.L2Operator
  ComplexConjugate

/-- For F automorphic of level K(a), |F| ≤ S, |a| ≥ R at infinity, max(f, 10) ≤ d, d² ≤ Rλ(x),
gap bounds, φ = conj ψ_l(α⁻¹·ω): φ is integrable on U(V)_∞, and the period of F against ∑_γ
(φ ⊗ 1_{K(a)})(x⁻¹γh), γ rational on V ⊕ ⟨1⟩, is vR(φ)F(x) up to 10vLS/d, v = vol K(a);
λ(x) = `firstMinimum` of V moved by x, and L is the product named in the statement. -/
lemma norm_poincare_period_sub_le {E n s} [Field E] [CMType E] [Fintype n] {V : Space E n s}
  [StablyUnram E] {F S a R A d} (hF : V.IsAutomorphic F) (hS : ∀ g, ‖F g‖ ≤ S) (ha : a ≠ 0) {l : _ →
    @HCParam (n ⊕ Unit) (s ⊕ᵥ 1)} (hl : HasLevel F (principalLevel n a)) (hR : ∀ w,
  R ≤ ‖Φ w a.val‖) (hA : 2 * numInfPlaces E * (card n + 1) + 2 ≤
  A) (hB : 8 * (card n + 1) ^ 2 < A) (hg : ∀ w, (l w).HasLargeGap (2 * A)) (R0 : 0 ≤ R) x (hx :
  d ^ 2 ≤ R * (V.move x).firstMinimum) (hd : numInfPlaces E ≤ d) (hD : 10 ≤ d)
  (ω α : GInf ..) : let φ (g : GInf ..) := ∏ w, conj ((l w).dsCoeff ((α w)⁻¹ * g w * ω w :))
  let ψ g (r : GInf E s) := φ (g * inl s _ ∘ r)
  let L := ∏ w, (2 * (‖(α w).1.1‖ * ‖(ω w).1.1‖) ^ 2) ^ A *
    (16 ^ A * volume.real {r : USign s | ‖r.1.1 - 1‖ ≤ 1})
  let Z := V.sum (signedSpace (n := Unit) E 1); let i := sum.comp (.inl ..)
    let v :=
      volume.real (SetLike.coe (principalLevel n a)); let X (γ : Z.Γ) h := (i x)⁻¹ * γ.1 * i h
      let K γ h := φ (X γ h).1 * indicator (principalLevel (n ⊕ Unit) a) 1 (X γ h).2
      Integrable (ψ 1) ∧ ‖∫ h, ∑' γ, K γ h * F h ∂V.quotMeasure - v • realConv (ψ 1) F x‖ ≤
        v * L * S * (10 / d) := by
  intro φ ψ L Z j v X K
  have hL g t (h : 0 < t) (e : ∀ r : _ → _, t ≤ ∏ w, ‖(g w * inl s _ (r w)).1.1‖) :
    Integrable (ψ g) ∧ ∫ r, ‖ψ g r‖ ≤ L * t⁻¹ ^ A := open Finset in by
    have k w := integral_decay_le volume isProperMap_inl (by simpa) (g w)⁻¹
    refine have i := (Integrable.fintype_prod (k · |>.1.comp_inv.const_mul _)).mul_const _
      have N := ae_of_all _ fun r ↦ ?_; ⟨i.mono' (Continuous.aestronglyMeasurable (by fun_prop)) N,
      (integral_mono_of_nonneg (.of_forall (by simp)) i N).trans <| by
      simp_rw [integral_mul_const, L, prod_mul_distrib, integral_const_mul]; gcongr
      simpa [← fromBlocks_one', sub_eq_add_neg, fromBlocks_neg, fromBlocks_add, mul_pow] using
        (integral_fintype_prod_eq_prod _).trans_le (prod_le_prod₀ (by positivity [·, ·]) fun w _ ↦
        (integral_inv_eq_self ..).trans_le (k w).2)⟩
    grw [e r, ← prod_inv_distrib, ← Finset.prod_pow, ← prod_mul_distrib, norm_prod]; gcongr
    nth_grw 1 [Complex.norm_conj, norm_dsCoeff_le_pow (hg _) (by bound), pow_mul, ← mul_pow,
      ← mul_pow, map_inv, ← _root_.mul_inv_rev, U.norm_inv, ← U.norm_inv (ω _)]
    gcongr; have (x : type_of% (α ‹_›).1) := x.norm_pos; simp only [field, *]
    grw [← mul_pow, ← mul_pow, mul_comm ‖_‖, ← norm_mul₃_le]; simp [mul_assoc]
  have H g := (hL g 1 one_pos (by simp [↓le_prod_opNorm])).1; use H 1
  choose y hy using
    (fun ⟨_, g, rfl⟩ ↦ ⟨g.1.1 *ᵥ (0 ⊕ᵥ 1), by simp [↓move_vecAtPoint, ↓← ratEmbed_mulVec_vecAtPoint,
    funext_iff, Z, j, ↓sum_vecAtPoint, Space.vecAtPoint, signedSpace, entrywise]⟩ :
    ∀ γ : Z.Γ, ∃ y, ∀ k u, (Z.move u).vecAtPoint y = (u⁻¹ * γ * j k).mat *ᵥ Pi.single (.inr ()) 1)
  have ⟨C, hC, h1⟩ := (j.range.subgroupOf Z.Γ).exists_isComplement_left 1
  let W := {γ : C | ∃ k, (X γ k).2 ∈ principalLevel _ a}
  have key {u k} (hu : (X u k).2 ∈ principalLevel _ a) h :
      K u (k * h) = ψ (X u k).1 h.1 * indicator (principalLevel n a) 1 h.2 := by
    simp [K, X, ← mul_assoc, indicator]; congr!
    erw [mul_mem_cancel_left hu]; simp [principalLevel, mem_Kf, ← mat_snd, j,
      (show ∃ y ∈ Ô E, 0 = · * y by use 0; simp)]
  have M {W} [RCLike W] {f : _ → W} hf := ((measurePreserving_orbitMeasure.comp
    (measurePreserving_swap (ν := V.quotMeasure))).fubini (f := f) hf).elim fun i e ↦
    And.intro i.prod_right_ae (e ▸ hasSum_integral_measure i.integral_prod_left)
  let f (γ : W) := (Z.move (j x)).archCoords (y γ); let o : W := ⟨⟨_, h1⟩, x, by simp [X]⟩
  choose k h using @mem _ W
  have sep : Pairwise (d ^ 2 ≤ ‖f · - f ·‖) := fun γ γ' ne ↦ by
    obtain ⟨w, hw⟩ := MulAction.surjective₀ (a.ext.mt ha) (y γ - y γ')
    grw [← map_sub, ← hw, hx, ((le_inf le_rfl (by grw [← one_le_firstMinimum]; simp)).trans
      inf_le_firstMinimum_sum).trans ((Z.move (j x)).firstMinimum_le (fun i ↦ ?_) fun e ↦
      ne (val_injective (hC.leftQuotientEquiv.symm.injective (QuotientGroup.eq.2 ((((mem_range_sum
      stdForm_sum).1 (by simp)).2 ?_).imp' toUnitary.symm fun _ ↦ (toUnitary.injective <| .trans (by
      ext : 2; exact (mat_sum _).trans (by simp; rfl)) ·)))))), ← norm_smul_of_nonneg R0]
    simp [norm_eq, archCoords, -algebraMap_smul, mul_pow]; grw [← hR]
    choose t ht e using (h · |>.2 i (.inr ())); convert sub_mem (ht γ) (ht γ')
    use (isUnit_algebraMap_finAdele ha).mul_left_cancel (by
      simpa [mul_sub, ← e, fun γ ↦ hy γ.1 (k γ), X,
                        -mat_mul, ↓map_smulₛₗ] using! congr(((Z.move _).vecAtPoint $hw i).2))
    simpa [mat, ← ext_iff, hy _ 1, e, eq_sub_iff_add_eq, Unique.forall_iff] using
      (congr((Z.move γ).vecAtPoint $hw ·))
  obtain ⟨m, _, _, O : ‖f o‖ ≤ d⟩ := (isOpen_principalLevel (n := n) ha).measurableSet,
    C.to_countable.to_subtype, (norm_nonneg _).trans (hS x), by simp [hd.trans', hy _ x, o, f,
    archCoords, -mat_mul, sum_prod_type, norm_eq, NeZero.one_le]
  have N (γ : Elem {o}ᶜ) : d ^ 2 / 2 ≤ ‖f γ‖ := by nlinarith [(sep γ.2).trans (norm_sub_le ..)]
  have T := tsum_inv_pow_le_of_separated (by bound) (by nlinarith [@sep · · <| coe_ne_coe.2 ·]) N
    (by simpa [← mul_assoc])
  have J γ := ((integrable_congr (ae_of_all volume (key (h γ)))).2 ((H _).mul_prod (((
    integrableOn_const (by simp)).mono_set principalLevel_le_Kf).integrable_indicator
    m))).comp_mul_left (k γ)⁻¹
  simp [Subgroup.smul_def, -Subtype.forall] at M J
  have I γ := (J γ).mul_bdd hF.1.aestronglyMeasurable (.of_forall hS)
  have b (γ : Elem {o}ᶜ) : _ ≤ v * L * S * d ^ A * ‖f γ‖⁻¹ ^ A := (integral_mono (I γ).norm
    ((J γ).norm.mul_const S) (by grw [norm_mul, hS ·])).trans <| by
    rw [integral_mul_const, ← integral_mul_left_eq_self _ (k γ)]
    simp [key, h, volume_eq_prod, norm_indicator_eq_indicator_norm]
    grw [integral_prod_mul (‖ψ _ ·‖), (hL _ (‖f γ‖ / d) (by grw [← N]; bound) fun r ↦ by
      grw [(mem_and_norm_le_of_vecAtPoint _ _ _ (X γ (k γ * (r, 1))).mat 1
        (le_prod_opNorm (X γ _).1).2 _).2,
        O] <;> simp [hy 1 x, hy γ (k γ * (r, 1)), X, o, -mulVec_single, mul_assoc, field]
      rfl).2] <;> simp [m]; linear_combination
  convert! (((hasSum_singleton ..).hasSum_iff_compl.1 ((hasSum_integral_of_summable_integral_norm
    (fun p : _ × _ ↦ (M (I p.1)).1 p.2) ((summable_prod_of_nonneg (by positivity [·])).2 ⟨(I ·
    |>.norm |> M |>.2.summable), .compl_add (.of_nonneg_of_le (by simp; positivity [·])
    ((M (I _).norm).2.tsum_eq.trans_le <| b ·) (T.1.mul_left _)) .of_finite⟩)).prod_fiberwise
    (I · |> M |>.2))).norm_le_of_bounded (T.1.hasSum.mul_left _) (b · |>.trans'
    (norm_integral_le_integral_norm _))).trans _ with h
  rw [← (hC.1.comp (val_injective.prodMap (g := fun δ : V.Γ ↦
    ⟨⟨_, by simp [Z, sum_mem_Γ]⟩, δ, rfl⟩) _)).tsum_eq (hC.2.forall.2 _)]
  simp [hF.2, K, X, mul_assoc]; rfl
  simp_intro _ [isClosedEmbedding_sum.1.2.eq_iff]
  rintro ⟨σ, ⟨_, e⟩, δ, ⟨⟩⟩ m; exists ⟨⟨σ, δ * h, by
    simp [K, X, mul_assoc] at m ⊢; tauto⟩, δ, ((sum_mem_Γ ..).1 e).1⟩
  erw [← integral_mul_left_eq_self _ x, ← mul_smul_one, ← integral_indicator_const _ m,
    ← integral_prod_mul]
  simp [key, indicator, X, o]; congr! 3
  simp [← hl _ ‹_› (x * (_, 1)), mul_assoc]
  grw [mul_assoc, T.2, ← mul_pow, pow_le_of_le_one _ _ (by omega)] <;> field_simp <;> linarith

open Complex Real HCParam

/-- Laplace's method. Assume `IsTwoFactor`, large gaps h and the stated bounds on B, L, β, h; let
j = (j₁, j₂) have j₁ proper, j₂ continuous, ‖j₂(s)‖ ≤ β+1 if ‖j₁(s)−1‖ ≤ 1, and ν be right
invariant, finite on compacts. Then ν{‖j₁(s)−1‖ ≤ 1} ≤ β^{20(n+m)²}|∫ θ dν|,
θ = `HCParam.laplaceIntegrand`.

Discrete series coefficients near 1 and explicitly large Bessel functions. -/
lemma IsTwoFactor.laplace_method {n m X S} [Fintype n] [Fintype m] [Fintype X] [Group S]
  [TopologicalSpace S] [MeasurableSpace S] [MeasurableMul S] [BorelSpace S] (ν : Measure S)
  [ν.IsMulRightInvariant] [IsFiniteMeasureOnCompacts ν] {ε l η k τ} {B β : ℝ} {L M h : ℕ} [Nonempty
  n] [Nonempty m] {e : X ⊕ Fin M ≃ n} {j : S →* USign ε × _} {φ} (H : IsTwoFactor l k j τ B e φ)
  (hg : l.HasLargeGap h) (hg' : @HasLargeGap m _ η k h) (hB : 1 ≤ B) (hL : ∀ a, |l a| ≤ L) (hK :
  ∀ a, |k a| ≤ L) (hβ : 10 ^ 12 ≤ β) (hn : card n + card m + L ≤ β) (hh : 10 ^ 30 * ((card n + card
  m) ^ 2 * β.log) ^ 3 ≤ h) (hj : IsProperMap (j · |>.1)) (hj' : Continuous (j · |>.2)) (lip :
  ∀ s, ‖(subOnePair j s).1‖ ≤ 1 → ‖(j s).2.1.1‖ ≤ β + 1) : ν.real {s | ‖(subOnePair j s).1‖ ≤ 1} ≤
  β ^ (20 * (card n + card m) ^ 2) * ‖∫ s, l.laplaceIntegrand k j φ s ∂ν‖ := by
  obtain ⟨b : 16 ≤ β, a : 1 ≤ β.log⟩ := by bound,
    by grind [le_log_iff_exp_le, exp_one_lt_d9], hj.1, one_le_cast_card n, one_le_cast_card m
  have hb := measure_ball_le_covering ν ((U.sum (signMatrix_sum ..)).comp j) 1 (by bound :
    _ ≤ 200 * β ^ 5) (by bound : _ ≤ β + 1) (by field; nlinarith : _ ≤ β ^ 8)
  simp [U.sum, ← fromBlocks_one', sub_eq_add_neg, fromBlocks_neg, fromBlocks_add,
    -_root_.mul_inv_rev] at hb
  set N : ℕ := _ ^ 2; let g s := 2 / ‖(j s * 1).1.1.1‖
  have p c (_ : c ≤ 18 * N) s : ‖l.laplaceIntegrand k j φ s‖ ≤ g s ^ c := by
    simp [g, HCParam.laplaceIntegrand, H.re_phase]; grw [norm_dsCoeff_le_one hg', mul_one,
      norm_dsCoeff_le_pow hg]
    grw [gapThreshold, ← hh, ← a]; norm_cast; grind [Nat.le_self_pow]
  -- The cone: near `U(X)` both factors are Gaussians with one phase; far from it `laplaceIntegrand`
  -- is tiny.
  have A s : 4 * ‖l.laplaceIntegrand k j φ s‖ ≤ 8 *
    ((l.laplaceIntegrand k j φ s).re + 16 * β⁻¹ ^ (50 * N) * g s ^ (8 * N)) := by
    obtain e | e := le_total _ (β⁻¹ ^ _) <;> grw [mul_assoc, ← e, ← pow_add]
    grind [abs_re_le_norm]
    set T := _ * β.log with hT
    rw [← (_ ^ _ : ℝ).exp_log (by bound), (by simp [N]; ring : Real.log _ = -100 * T)]
    obtain ⟨t : 1 ≤ T, e, e1⟩ := by bound, mul_left_surjective₀ (by positivity : T ≠ 0) 1e-13
    have f : e ≤ 100⁻¹ := by nlinarith
    obtain ⟨r, z, w, v⟩ | o := (le_total ..).imp_left (H.exists_near_one e hB (by nlinarith) f s)
    · obtain ⟨⟨a, ⟨u, i⟩, b⟩, c, o, d⟩ := dsCoeff_gaussian_shape hg hL w t,
        dsCoeff_gaussian_shape hg'.neg (by simpa) v t
      set x : ℂ := _ - a; set y : ℂ := _ - c; set E := rexp _
      grw [z.trans (by simp [y, HCParam.laplaceIntegrand, ↓← H.phase_logOneAdd r (by bound)
        (by bound), phase, ← diagonal_neg,
        Complex.exp_sub, Complex.exp_neg]; field : _ = a * c - (-x * c + -x * y + -a * y)), sub_re,
        re_le_norm, norm_sub_le, norm_add₃_le]; clear * - u i o b d t; simp_all [abs_of_nonneg]
      grw [d]; nlinarith [(by bound : 0 < E), (by simp [E]; grind : E ≤ 1)]
    grw [← (?_ : ‖l.laplaceIntegrand k j φ s‖ ≤ rexp _)]; clear * -; grind [abs_re_le_norm]
    simp [HCParam.laplaceIntegrand, H.re_phase]
    grw [← pow_le_pow_iff_left₀, mul_pow, norm_dsCoeff_pow_four_le, norm_dsCoeff_pow_four_le,
      ← mul_pow, ← mul_inv, ← (?_ : 1 + e ^ 2 ≤ _ * _), ← log_le_log_iff] <;> try positivity
    simp; grw [← le_log_one_add_of_nonneg, ← hh]
    field; repeat nlinarith only [e1, f, t, o]
  have ⟨I, hw⟩ := integral_decay_le ν (j := .comp (.fst ..) j) hj (by rify [N]; bound : _ < 8 * N) 1
  have T := I.mono' (by cases funext H.phase_eq; fun_prop [HCParam.laplaceIntegrand, phase] :
    Continuous _).aestronglyMeasurable (.of_forall (p _ (by omega)))
  grw [((T.re.add (I.const_mul _)).const_mul 8).measure_le_integral (.of_forall (A · |>.trans' ?_))
    fun s o ↦ (A s).trans' (by simp [HCParam.laplaceIntegrand, H.re_phase]; grw
    [← half_le_norm_dsCoeff hL _ o.1, ← half_le_norm_dsCoeff hK _ o.2] <;> linarith),
    integral_const_mul, integral_add' T.re (by fun_prop),
    integral_const_mul, integral_re T, hw, ← ENNReal.ofReal_mul, RCLike.re_le_norm, (?_ : _ ^ _ ≤
    β ^ (20 * N) / 16), ← mul_assoc (16 * _), (?_ : _ * 16 ^ _ ≤ (β ^ (20 * N))⁻¹)] at hb
  have := ENNReal.toReal_le_of_le_ofReal (by bound)
    (hb.trans' (ν.mono (⟨by grw [norm_le_insert' _ 1]; simp; bound, lip · ·⟩)))
  field_simp at this; linarith!
  all_goals (repeat grw [b]); simp [field, ← pow_add, ← pow_mul, ← pow_succ, ← pow_succ']
    <;> bound [N.pos_of_neZero]

open Finset Lagrange

/-- Let l, l' satisfy `IsSteep` for X, B ≥ 1 and M, M+1, with M even and l' of some gap. Some
ω in U(diag(ε) ⊕ 1) has ‖ω‖ ≤ (n+1)²(6B)^{2M+1}, and j(r) = (r, ω⁻¹(r ⊕ 1)ω) satisfies
`IsTwoFactor` for l, −l', with phase `HCParam.phase` zero and second component of j(r) − 1 equal
to ω⁻¹((r−1) ⊕ 0)ω. -/
lemma IsSteep.exists_isTwoFactor_restriction {n X} [Fintype n] [Fintype X] {ε B h l l' M} {e :
  X ⊕ Fin M ≃ n} {e' : X ⊕ Fin (M + 1) ≃ n ⊕ Unit} (hM : Even M) (H : IsSteep l B e) (H' :
  IsSteep l' B e') (hg : l'.HasGap h) (hB : 1 ≤ B) : ∃ ω : USign (ε ⊕ᵥ 1),
  let j := (MonoidHom.id _).prod ((MulAut.conj ω).symm.toMonoidHom.comp (U.inl ..))
  ‖ω.1.1‖ ≤ card (n ⊕ Unit) ^ 2 * (6 * B) ^ (M + (M + 1)) ∧ IsTwoFactor l (-l') j (e' ∘ .inl) B
    e 0 ∧ ∀ s, (subOnePair j s).2 = ω⁻¹.1.1 * (subOnePair j s).1.fromBlocks 0 0 0 * ω.1.1 :=
  let x := Fin.append (-l'.lowestKType <| e' <| .inr ·.rev) (l.lowestKType ∘ e ∘ .inr)
  have o : ∀ i j, _ ∧ |(x i - x j : ℝ)| ≤ 6 * B := by simp [x, @Fin.forall_fin_add (_ + 1),
    H.weight_strictAnti.lt_iff_gt, H'.weight_strictAnti.lt_iff_gt]; rify; grind [IsSteep]
  have ⟨c, c1, hc⟩ := @exists_lagrange_weights _ x (o · · |>.1)
  let r {n} (g : Fin n → _) s y := (∏ j ∈ s, (x y - x (g j) : ℝ)) / c y
  let d a := r (.natAdd _) Finset.univ (.castAdd _ a) * (-1) ^ a.1
  let R y a := d a * r (.castAdd _) (Finset.univ.erase a) y
  have E a b : R (.castAdd _ b) a = ite (a = b) 1 0 := (c1 (a.castAdd _)).elim (by
    simp_rw [R, r, ← filter_ne', prod_filter]
    grind (splits := 20) [prod_eq_zero_iff, Fin.prod_univ_add])
  let f := e.sumCongr 1
  let ω := U.of IsHermInvolution.isUnit (Matrix.reindex f e' (fromRows (fromBlocks 1 0 0 (Matrix.of
    fun k a ↦ R (.natAdd _ k) a.rev)) (Matrix.of fun () ↦ 0 ⊕ᵥ (d ·.rev)))) (Matrix.ext (by
    have k a b := congr(ofReal $((Fin.sum_univ_add fun y ↦ R y a * (-1) ^ y.1 * R y b).symm.trans
      (.trans (by simp [mul_sum, eval_nodal]; grind) congr(d a * d b * $((hc (nodal (disjSum
      (Finset.univ.erase a) (Finset.univ.erase b)) (x <| .castAdd _ <| ·.elim id id))
      (by simp [-Nat.cast_add])).symm.trans (.trans (congrArg _ (by simp)) nodal_monic))))))
    simp [↓(reindex_equiv e').1, mul_apply, reindex_equiv e, signMatrix, H'.sign_inl, H'.sign_inr,
      Matrix.diagonal, f,
      H.sign_inl, H.sign_inr, pow_add, apply_ite, *] at k ⊢; grind [neg_one_pow_eq_ite]))
  ⟨ω, by
  refine ⟨sq (_ : ℝ) ▸ l2_opNorm_le_of_apply ((reindex_equiv f).1.2 ?_), have A s := ?_; ⟨⟨H,
      fun s ↦ ?_, by simp [trace_conj']; simp [trace], by simp, by simp, by simp [H'.sign_inl,
      H'.weight_eq_zero], by
              simp [↓reindex_equiv e', H'.weight_eq_zero]; rify; grind [IsSteep], fun u hu ↦
      (exists_unitary_sub_one_eq_inclMatrix e H.sign_inl hu.1).imp fun s hs ↦ Prod.ext hs ?_⟩, A⟩⟩
  · simp [↓reindex_equiv e', ω, R, d, apply_ite, pow_add]; split_ands <;>
      (repeat grw [fun n g s y ↦ (by grw [abs_div, div_le_self, abs_prod, (o ..).2,
      prod_const, card_finset_fin_le] <;> grind : |@r n g s y| ≤ _)]) <;> bound
  · erw [mul_assoc, Units.eq_inv_mul_iff_mul_eq]
    simp [mul_sub, ← sub_one_mul, mul_assoc, ← ext_iff]
  · rw [HCParam.phase, A, trace_mul_cycle', ← mul_assoc, ← fromRows_toRows (ω.1.1 * _),
      ((Matrix.reindex e e').symm.injective (Matrix.ext ?_) : toRows₁ _ = fromCols (intDiagonal
      l.lowestKType) (replicateCol Unit (ofReal ∘ (0 ⊕ᵥ -r (.castAdd _) Finset.univ ∘ .natAdd _) ∘
      e.symm)) * ω.1.1)] <;> simp [Matrix.mul_assoc, trace, mul_apply, Matrix.diagonal]
    simp +zetaDelta [H.weight_eq_zero, H'.weight_eq_zero]; grind [mul_prod_erase]
  erw [A, hs, mul_assoc, Units.inv_mul_eq_iff_eq_mul, ← (Matrix.reindex f e').symm.apply_eq_iff_eq]
  simp [← Matrix.mul_assoc, entrywise, ω, f, inclMatrix, reindex_equiv e]⟩
