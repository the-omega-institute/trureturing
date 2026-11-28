/- GID: D5/S3/Zeros/GRH/Lib/Shimura/Uniformisation/BallModel
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Shimura/Uniformisation/BallModel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Shimura.Uniformisation.BallModel. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Shimura/Uniformisation/BallModel.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Shimura.Transfer.MarkedPairs
import D5.S3.Zeros.GRH.Lib.Shimura.Uniformisation.ModelAlongArc
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Complex uniformisation of PEL abelian varieties; Appell–Humbert; finite class number
(known result; see Lib.Shimura.Uniformisation.AppellHumbert).

This file: Ball model for signature (1,n-1): periods, polarisation, linearised action at fixed
points. -/

noncomputable section

open Topology Matrix Polynomial ComplexOrder Complex LinearMap Real Fintype Finset


variable (E) {n} [Field E] [Ψ : CMBase E] [Fintype.{0} n] {D : PEL E} (e : (n → ℂ)
    ≃L[ℂ] ℂ × BallBase n) (H : Matrix n n ℂ)
attribute [local simp] map_smul' mulVec_sub ModuliPoint.act polarisationForm mul_sum
  vecMulVec_mulVec roots_eq_map_numberedRoots smul_smul
  PeriodMap.intAction PEL.xi_im_pos_and_re_eq_zero Prod.ext_iff toBilin'_apply' mulVec_transpose
attribute [local simp ←] Complex.coe_smul dotProduct_mulVec mulVec_mulVec
attribute [-simp] Prod.forall map_smul map_smul_of_tower map_sum Pi.star_apply Prod.smul_mk

/-- The map, ℂ-linear in q = (q₁,q') and ℝ-linear in w, with value ((e⁻¹q)ᵀHw₀, q₁y₂ − y₁q',
(q₁w_v)_{v≠v₀}), where w₀ = w_{v₀} and (y₁,y₂) = e(w̄₀). -/
@[simp] def ballPeriod : ℂ × BallBase n →ₗ[ℂ] RealVectors E n →ₗ[ℝ] BallFibre E
  n := by apply mk₂' ℂ ℝ fun q w ↦
  ((e.symm q ⬝ᵥ H *ᵥ (w · v₀)) • (1, 0) + q.1 • e (star (w · v₀)) - (e (star (w · v₀))).1 • q,
  fun v ↦ q.1 • (w · v)) <;> intros <;> ext <;>
  simp [-smul_eq_mul, ← Pi.add_def, ← Pi.smul_def] <;> ring

/-- The set of b in ℂ^(n−1) such that x = e⁻¹(1, b) in ℂⁿ is positive for H, that is, Re ∑ x_i
H_ij conj(x_j) > 0. -/
abbrev positiveBall := {b | 0 < (e.symm (1, b) ⬝ᵥ H *ᵥ star (e.symm (1, b))).re}

/-- The matrix of w ↦ 2(uᴴHw)/(uᴴHu)·u − w; if uᴴHu ≠ 0 it fixes u and is −1 on the w with uᴴHw
= 0. -/
abbrev formReflection u := vecMulVec u ((2 / star u ⬝ᵥ H *ᵥ u) • star u ᵥ* H) - 1

variable {E H}

lemma exists_eq_formReflection (hH : H.IsHermitian) {J} (p : (H * J).PosDef) : IsReflection J →
  ∃ u, 0 < star u ⬝ᵥ H *ᵥ u ∧ J = formReflection H u | ⟨u, _, _⟩ => ⟨u, by
              obtain _ := p.dotProduct_mulVec_pos (by aesop : u ≠ 0), star_form p.1
              simp_all [star_form hH, ext_iff_mulVec]
              grind⟩

/-- Assume `IsSignedFrameFor` g ℓ β, H = Φ_{v₀}(β) negative definite on {e(ȳ)₁ = 0}, and
`positiveBall` connected. Then an analytic family over this ball has frame g and, at b,
reflection in conj(e⁻¹(1,b)) and period map `ballPeriod` at (1,b). -/
lemma exists_analyticFamily_positiveBall e {H} (hS : IsConnected (positiveBall e H)) (hn : ∀ y ≠ 0,
  (e (star y)).1 = 0 → star y ⬝ᵥ H
  *ᵥ y < 0) {ℓ g β} (hβ : IsSignedFrameFor g ℓ β) (hH : β.map (Φ v₀) = H) : ∃ f : AnalyticFamily D,
  f.U.1 = positiveBall e H ∧ f.frame = g ∧ ∀ b ∈ f.U, f.reflection b =
  formReflection H (star (e.symm (1, b))) ∧ ⇑(f.torus b).Q = ⇑(ballPeriod E e H (1, b)) := by
  let f v := by apply mk₂' ℝ ℂ fun (w : RealVectors E D.Index) (p : BallFibre E D.Index) ↦ 2 * π *
    (Φ v D.ξ).im * if h : v = v₀ then (e (star (w · v))).1 * p.1.1 - e.symm (p.1 - p.1.1 •
    (1, 0)) ⬝ᵥ H *ᵥ (w · v) else star (w · v) ⬝ᵥ β.map (Φ v) *ᵥ p.2 ⟨v,
    h⟩ <;> as_aux_lemma => intros; split <;> simp [-smul_eq_mul, ← Pi.add_def,
      ← Pi.smul_def] <;> ring
  have U : IsOpen (positiveBall e H) := by apply isOpen_lt <;> fun_prop
  choose r hr _ using
    (hS.1.elim (by grind) : ∀ b, ∃ c ∈ positiveBall e H, b ∈ positiveBall e H → c = b)
  have z b := ne_zero_of_re_pos (hr b)
  let P b := ballPeriod E e H (1, r b)
  have l b w v (hv : (w · v) ≠ 0) : 0 < (f v w (P b w)).re := by
    by_cases v = v₀ <;> simp [*, f, P, pi_pos]
    set s := (e _).1
    linarith [by simpa [normSq, ← star_form (hH ▸ hβ.1.isHermitian_map) (star _)] using (by_cases
      (fun _ ↦ by simp_all) (hn ((w · v₀) - star (s • e.symm (1, r b))) · (by simp [s])
      |>.1.trans_le (mul_nonneg s.normSq_nonneg (hr b).le)))]
    simpa [*] using (hβ.2 v).re_dotProduct_pos hv
  have pos b w hw := sum_pos (Pi.lt_def.2 ⟨(by_cases (by simp [f, ·]) <|
    le_of_lt ∘ l b w ·), (Function.ne_iff.1 (mt transpose_eq_zero.1 hw)).imp (l b w)⟩)
  let Q b := ((P b).linearEquivOfInjective (.of_ker _ fun w ↦ (by simpa [·] using! pos b w))
    (by zify; simp [Fin.pos']; ring)).toContinuousLinearEquiv
  have hP b : IsPeriodMap (formReflection H (star (e.symm (1, r b)))) (Q b) := by
    simp_all [Q, P, IsPeriodMap, funext_iff, -smul_eq_mul, ← Pi.sub_def, ← Pi.smul_def]
    grind [smul_eq_mul]
  have d {w} b hb := (((ballPeriod E e H).flip w).toContinuousLinearMap.hasFDerivAt.comp _
    (hasFDerivAt_prodMk_right 1 b)).congr_of_eventuallyEq (f₁ := (Q · w))
    (.mono (U.mem_nhds hb) (by simp_all [P, Q]))
  refine suffices ∀ b, _ from ⟨⟨⟨_, U⟩, hS, g, _, fun b ↦ ⟨⟨β, _, (restrictScalars ℝ
    toContinuousLinearMap.1 ∘ₗ ∑ v, f v).toContinuousLinearMap ∘L (Q b).symm, hβ.1, hP _, ?_, ?_,
    isPosRiemann_of_re_pos (this b)⟩, ⟨_, _, by simp [z], rfl⟩, fun c ↦ ?_, .refl .., by
      simp [LinearMap.ext_iff, reindex_equiv (Q b)]; simp [Q, P, -smul_eq_mul, ← Pi.smul_def]
      simp [funext_iff, field]⟩, fun _ h _ ↦
      analyticAt_of_eventually_differentiable (.mono (U.mem_nhds h) (⟨_, d · ·⟩)), fun b hb v p ↦ by
    simpa [z, ← hP .., (d _ hb).fderiv, two_smul, self_eq_neg, -smul_eq_mul, ← Pi.smul_def] using
    congr($(p (Q b fun i _ ↦ star (e.symm (1, r b)) i)).1.2), by simp, this⟩, rfl, rfl, by
      simp +contextual [*, Q, P, funext_iff]⟩; (Q · |> reindex_equiv |>.1.2
      (by simpa using! pos _)) <;> simp [riemannForm_def, div_eq_iff, reindex_equiv (Q
    b)] <;> as_aux_lemma => intro y; simp [f, Q, P, ← hH, sum_mul, ← sum_sub_distrib, -smul_eq_mul,
    ← Pi.smul_def, ← star_form hβ.1.isHermitian_map (y · _)]; congr! 1; split <;> simp [*,
    mul_sub] <;> ring

/-- If H is hermitian and a = ūᵀHu > 0, there are linear coordinates e : ℂⁿ ≅ ℂ × ℂ^(n−1) with
a·e(y)₁ = yᵀHu and e(ū) = (1, 0), and the b for which x = e⁻¹(1, b) has Re xᵀHx̄ > 0 form a
set star-convex at 0. -/
lemma exists_ball_chart (hH : H.IsHermitian) {u a} (ha : star u ⬝ᵥ H *ᵥ u = a) (hu : 0 < a) : ∃ e,
  StarConvex ℝ 0 (positiveBall e H) ∧ (∀ y, a * (e y).1 = y ⬝ᵥ H *ᵥ u) ∧ e.symm (1, 0) =
  star u := by
  let j := ContinuousLinearEquiv.equivOfRightInverse (a⁻¹ • H.toBilin'.flip u
    ).toContinuousLinearMap (.toSpanSingleton ℂ (star u)) fun c ↦ by simp [*, hu.ne']
  refine .imp (fun e h ↦ ⟨fun b hb s t _ _ _ ↦ ?_, h⟩) ⟨j.trans (.prodCongr (.refl ..) (.ofFinrankEq
    (by simpa -dsimp using congr($j.finrank_eq.symm - 1)))), by simp -dsimp [j, hu.ne']⟩
  simpa [(e.injective (by simp [← h]) : e.symm (1, ofReal t • b) = star u + t • (e.symm (1, b) -
    star u)), ← h.1 (e.symm _), *, ← star_form hH (star _), field]
    using (convex_Ioi 0).add_smul_sub_mem hu.1 hb ⟨sq_nonneg t, by bound⟩

/-- An endomorphism Y of K × K^m that preserves both factors and acts by ν on the first is ν ⊕
N, and the characteristic roots of N are those of Y with one copy of ν removed. -/
lemma exists_roots_eq_erase {K} [Field K] ν (Y : Module.End K _) (h₀ : Y (1, 0) = (ν, 0)) (h : ∀ w,
    (Y (0, w)).1 = 0) : ∃ N : Matrix n n K, (∀ x, Y x = (ν * x.1, N *ᵥ x.2)) ∧ N.charpoly.roots =
    Y.charpoly.roots.erase ν := .imp (fun N (e : Y = .prodMap (0 - -ν • 1) N.toLin') ↦ e ▸ by
  simp [↓charpoly_prodMap, roots_mul, X_add_C_ne_zero, N.charpoly_monic.ne_zero, ↓charpoly_sub_smul,
    -map_neg]) ⟨(snd .. ∘ₗ Y ∘ₗ inr ..).toMatrix', by ext <;> simp [*, Prod.mk_zero_zero]⟩

/-- For an analytic family f and p = (b, z), the point with the frame of f, the reflection ℓ(b),
and vectors Q_b⁻¹(z_i) + P_i, Q_b the period map. -/
@[simp] def AnalyticFamily.ballPoint {ν} (f : AnalyticFamily D) (P : Fin ν → _) (p : _ × _) :=
  ModuliPoint.mk _ _ ((f.torus p.1).Q.symm ∘ p.2 + P) ⟨_,
  (f.torus p.1).isSignedFrameFor⟩ (f.torus _).reflection

/-- The Hecke translate of an analytic family by γ: frame gγ, same domain, complex structures
and period maps, forms B scaled by the c > 0 with c·γᴴγ in Ẑ^×. -/
def AnalyticFamily.heckeTranslate (f : AnalyticFamily D) (γ : GUPlus E D.Index) :
  AnalyticFamily D := by
  choose c h k using γ.2.1
  exact ⟨_, f.isConnected, f.frame * γ, _, fun b ↦ let x := f.torus b
    ⟨⟨_, _, c • x.B, x.isFrameFor.mul_iff.2 k,
      x.isPeriodMap, by simp [x.re_symm], by simp [map_rat_smul, x.riemannForm_eq, Rat.smul_def,
      mul_left_comm], isPosRiemann_of_re_pos (by simpa [h] using f.re_pos b)⟩,
      x.reflection, by simpa [h.ne'] using x.adjoint, x.exists_std_equiv⟩, f.analyticAt,
    f.eq_zero_of_linear, by simp [f.form_const 0], by simpa [h] using f.re_pos⟩

/-- Some analytic family, parametrising points A(q) with A(0) = o, meets every point with frame o.x.
If z : o·(g,α) ≅ o at level K(𝔑), z separable, o.reflection = `eigenReflection` True z μ, then z :
A(q)·(g,α) ≅ A(Kq) near 0, K linear, `localTerm`(t) = `localTerm`(0)·det(1 − tK). -/
lemma exists_ball_family {ν} (o : ModuliPoint E D.Index ν) : ∃ f : AnalyticFamily D, 0 ∈ f.U ∧
  f.ballPoint o.P 0 = o ∧ (∀ a : ModuliPoint E D.Index ν, a.x = o.x → ∃ p ∈ f.U.1 ×ˢ .univ,
  f.ballPoint 0 p = a) ∧ ∀ {g α z μ}, z.1.charpoly.Separable → o.reflection = eigenReflection True z
  μ → (o.act g α).IsLevelIso (levelGU D.Index D.𝔑) z o → ∃ K : Module.End ℂ _, (∀ᶠ q in 𝓝 0,
  ((f.ballPoint o.P q).act g α).IsLevelIso (levelGU D.Index D.𝔑) z (f.ballPoint o.P (K q))) ∧ ∀ t,
  (localTerm α z.1.charpoly μ).eval t = (localTerm α z.1.charpoly μ).eval 0 * (1 - t • K).det := by
  have ⟨_, _, _, ⟨β, S⟩, r₀⟩ := o
  obtain ⟨T, hH⟩ := ite_eq_left rfl ▸ S.2 _, S.1.isHermitian_map
  obtain ⟨u₀, hu₀, rfl⟩ := exists_eq_formReflection hH T r₀
  have ⟨e, hS, he, he₀⟩ := exists_ball_chart hH rfl hu₀
  have hn y hy (h : (e (star y)).1 = 0) := by
    simpa [← he (star y), h] using T.dotProduct_mulVec_pos (x := y) hy
  obtain ⟨f, hU, rfl, hf⟩ := exists_analyticFamily_positiveBall e (hS.isPathConnected
    (by simpa [*] using hu₀.1)).isConnected hn S rfl
  have h0 := (hU ▸ hS).mem f.isConnected.1
  refine ⟨f, h0, by simp [hf _ h0, *], ?_, fun {k α z j} hz hμ R ↦ ?_⟩
  rintro ⟨_, _, P, ⟨_, s⟩, h⟩ ⟨⟩
  cases by simpa using s.conj_eq_smul S (y := 1) ⟨one_pos, 1, by simp⟩
  obtain ⟨u, hu, rfl⟩ := exists_eq_formReflection hH (ite_eq_left rfl ▸ s.2 _ :) h
  have k := mt (hn u (by aesop)) hu.not_gt
  have ⟨b, hb⟩ : ∃ b, (1, b) = (e (star u)).1⁻¹ • e (star u) := by simp [k]
  have m : b ∈ f.U := hU.ge (by simpa [*, inv_mul_eq_div, div_div, mul_conj] using hu.1)
  exact ⟨(b, (f.torus b).Q ∘ P), by
    simp [(hf b m).1, m, hb, formReflection, ext_iff_mulVec, funext_iff]; simp [field, *]⟩
  obtain ⟨⟨c, h₀⟩, _, a, u⟩ := div_mem k.2.1 R.mem_level.1,
    (isReflection_eigenReflection hz).2 _ r₀ R.2
  obtain ⟨⟨⟩, hc, h₂⟩ := (u _).1 hμ,
    S.similitude_and_root_norm (by simpa [← mul_assoc] using h₀) R.reflection_eq
  set μ := numberedRoots (Ψ.Φ v₀) _ j
  have hr := h₂ v₀ μ (by aesop)
  obtain ⟨hμ, h₀⟩ := by simpa [hu₀.ne', smul_comm μ, -vecMulVec_smul] using congr($a *ᵥ u₀),
    mul_ne_zero_iff.1 (hr.trans_ne (by aesop))
  have hZ x w := by simpa [↓map_conjTranspose_mul_mul,
    dotProduct_mulVec _ _ᴴ, -dotProduct_mulVec] using congr(x ⬝ᵥ ($hc).map (Φ v₀) *ᵥ w)
  have ⟨N, hY, hN⟩ := exists_roots_eq_erase (star μ) (e.conj (z.1.map (Φ v₀))ᴴᵀ.toLin')
    (by simp [*, ← star_mulVec, ← e.symm_apply_eq.1 he₀]) fun w ↦ by
    simpa [hμ, ← he (_ ᵥ* _), ← he (e.symm _), hu₀.ne', h₀] using hZ (e.symm (0, w)) u₀
  erw [e.charpoly_conj, charpoly_toLin', z.1.charpoly_map (star _)] at hN
  let G a := ((mulLeft ℂ (Ψ.Φ v₀ a * μ)).prodMap (star (Φ v₀ a) • N).toLin').prodMap
    (piMap fun v : {a // a ≠ Ψ.v₀} ↦ (Φ v a • z.1.map (Φ v)).toLin')
  let K := (star μ⁻¹ • N).toLin'.prodMap (piMap (G <| α ·))
  refine ⟨K, .mono (((f.U.2.prod f.U.2).preimage (f := fun p ↦ ((K p).1, p.1))
    (by fun_prop)).mem_nhds (by simpa)) fun p ⟨h', h⟩ ↦
    have key a w : (f.torus (K p).1).Q (cmEmbedding a • z.1.map cmEmbedding *ᵥ w) =
      G a ((f.torus p.1).Q w) := by
      simp [hf _ h, hf _ h', -smul_eq_mul, ← Pi.smul_def]
      simpa [G, K, star_mulVec, by simpa [reindex_equiv e, ← e.eq_symm_apply] using hY, funext_iff,
        *, ← hr, field] using Or.inl (hZ (star μ⁻¹ • e.symm (1, p.1)) _)
    ⟨R.mem_level,
      (f.torus _).isPeriodMap.ratConj_eq (f.torus _).isPeriodMap (G 1) (by simp [← key]), by
      simpa [K, (f.torus _).Q.eq_symm_apply.2 (key ..)] using R.sub_mem_lattice⟩, fun t ↦ ?_⟩
  have hn r : _ → μ * t - r = -r * (1 - (star μ)⁻¹ * star r * t) := (by grind) ∘ h₂ v₀ r
  simp [lieRoots, (id rfl : 1 - t • K = .prodMap (1 - t • toLin' _) (piMap fun i ↦
    .prodMap (.prodMap (1 - t • mulLeft ..) (1 - t • toLin' _)) (piMap fun v ↦ 1 - t • toLin' _))),
    ← det_toMatrix', map_smul, prod_eq_mul_prod_subtype_ne _ v₀, IsLieRoot, sub_ite, μ,
    ← star_def, *, localTerm, ← map_val, ← map_erase, ← Multiset.map_erase _
    star_injective, ← erase_val, prod_ite, filter_eq', filter_ne', det_pi, piMap, @Subtype.prop _ (·
    ≠ _), -mul_eq_mul_left_iff, charpoly_map, det_prodMap, det_one_sub_smul_eq_prod_roots,
    ↓roots_map_conjugate, mul_comm t, eval_prod, ↓prod_embeddings_eq_prod_pairs,
    mul_assoc, -neg_mul, Lagrange.basis, Lagrange.basisDivisor]
  ring
