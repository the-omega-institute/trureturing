import GRH.Lib.General.Analysis.HolomorphicIntegral
import GRH.Lib.ClassField.Places.AdeleNorm
import GRH.Lib.ClassField.HeckeL.IdelicThetaSum
import GRH.Lib.Adelic.Adeles.MatrixApprox
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: Euler product, continuation to s = 1, non-vanishing and prime densities for Hecke
L-functions. Only real s is treated, and a non-trivial character of integral angular type is
continued to a neighbourhood of 1 from Tate's integral by a Riemann sum instead of Poisson
summation. Non-vanishing is proved only when its square is non-trivial, and densities are over
primes of degree one, with bounded error. Source: J. Tate, Fourier analysis in number fields and
Hecke's zeta-functions, 1950, in Cassels–Fröhlich ch. XV, §4.4–4.5; J. Milne, Class Field Theory, VI
4.8–4.9 (finite order); S. Lang, Algebraic Number Theory, Part Three (Analytic Theory)
(non-vanishing); the Riemann-sum continuation is Müntz's formula over ℚ, Titchmarsh, Theory of the
Riemann zeta-function, §2.11.

This file: Hecke's theorem: L-function of a nontrivial Hecke character is analytic at 1. -/

open NumberField Complex MeasureTheory Valued Function IsDedekindDomain


variable {K} [Field K] [NumberField K] {ψ : (𝔸f K)ˣ →* ℂˣ}

lemma CharUnramifiedAt.apply_locIdele_eq_zpow {w} (h : CharUnramifiedAt ψ w) x : ψ (locIdele w x) =
  ψ (locIdele w (uniformizer w)) ^ (-(v x.1).log)
  := by
  simpa [← div_eq_one] using h (x * _ ^ (v x.1).log) (by simp [-WithZero.inv_exp, WithZero.exp_neg])

namespace IsHeckeOfType

variable [PlaceEmbedding K] {n S} (h : IsHeckeOfType ψ n) (hS : Set.Finite S)
include h
attribute [-simp] Function.extend_apply' map_smul pow_eq_one_iff map_sub Prod.algebraMap_apply
attribute [local fun_prop] Continuous.rpow_const

/-- A Hecke character ψ of type n on the finite ideles of K is unitary: |ψ(x)| = 1 for every x. -/
lemma norm_eq_one x : ‖(ψ x).1‖ = 1 := by
  let U := (normHom.toMonoidHom.comp (Units.coeHom ℂ)).ker.comap ψ
  simpa [U, pow_eq_one_iff_of_nonneg, (finiteIndex_idele_subgroup_of_isOpen U (ψ.ker.isOpen_mono
    (by aesop_cat) h.1) fun x _ ↦ by simpa using congr(‖$(h.2 x)‖)).1] using U.pow_index_mem x

lemma norm_heckeCoeff_le v : ‖heckeCoeff ψ S v‖ ≤ 1 :=
  h.norm_eq_one _ ▸ norm_indicator_le_norm_self ..

lemma pow (d : ℕ) : IsHeckeOfType (ψ ^ d) (d • n) := h.imp (Subgroup.isOpen_mono
  (by aesop_cat)) (by simp_all [Finset.prod_pow, zpow_mul', ← mul_pow])

/-- Over a CM field K, if ψ is the finite part of a Hecke character of type n and n ≠ 0, then ψ
is not the trivial character. -/
lemma ne_one [IsCMField K] (hn : n ≠ 0) : ψ ≠ 1 := (ne_iff.1 hn).rec fun w _ e ↦ by
  have := (by fun_prop (disch := simp) : ContinuousAt (fun y ↦ ∏ u, (y u / ‖y u‖ : ℂ) ^ n u)
    (exp ∘ Pi.single w (log (-1) / n w))).continuousWithinAt.eq_const_of_mem_closure
    (denseRange_Φ.sdiff_singleton 0 _) (by simpa [e] using (h.2 <| .mk0 · ·))
  simp_all [neg_eq_self, log, apply_ite, ← exp_int_mul, mul_div]

open Real HeightOneSpectrum UniqueFactorizationMonoid FractionalIdeal Set in
/-- Tate's finite integral: let f vanish off ideles integral outside S and units at S, see only
S-components of integral ideles, with fψ = 1_V on Ô^×, V ∋ 1 open. Then κ = μ(Ô^× ∩ V) ≠ 0
and ∫ fψ|·|^s dμ converges to κ L^S(s, ψ) for real s > 1. -/
lemma tate_integral S (f : _ → ℂ) V μ [Measure.IsHaarMeasure μ] (hV : IsOpen V) (h₂ : 1 ∈ V)
  (h₀ : ∀ x, f x ≠ 0 → (∀ w ∉ S, v (x.1 w) ≤ 1) ∧ ∀ w ∈ S, v (x.1 w) = 1) (h₁ :
  ∀ u ∈ idelesUnitOff ∅, f u * ψ u = if u ∈ V then 1 else 0) (h₃ : ∀ x y, ↑x ∈ Ô K → ↑y ∈ Ô K →
  (∀ w ∈ S, y.1 w = x.1 w) → f y = f x) : μ.real (SetLike.coe (idelesUnitOff ∅) ∩ V) ≠ 0 ∧
  ∀ s > 1, let Z x := f x * ψ x * (finIdeleAbs x ^ s : ℝ)
  Integrable Z μ ∧ ∫ x, Z x ∂μ =
    eulerProd (heckeCoeff ψ S) s * μ.real (SetLike.coe (idelesUnitOff ∅) ∩ V) := by
  let χ : _ →* ℂ := ⟨⟨fun I ↦ ite (I = 0) 0 ((normalizedFactors I).map (asIdeal.extend (heckeCoeff ψ
    S) 0)).prod, by simp [↓normalizedFactors_one]⟩, by simp +contextual [ite_eq_iff', or_imp]⟩
  have e v : χ v.1 = heckeCoeff ψ S v := by
    simp [χ, v.3, asIdeal_injective, normalizedFactors_irreducible, irreducible]
  obtain ⟨U, _, _, _, d, _, _, hl, -⟩ := (isOpen_idelesUnitOff ∅).inter hV, h.norm_heckeCoeff_le
    (S := S), isCompact_idelesUnitOff_empty.measure_ne_top (μ := μ), Countable.of_preimage_singleton
    (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) · |>.countable), @exists_idele_divisor_hom ..
  refine (⟨·, ?_⟩) ((measureReal_ne_zero_iff).2 (U.measure_ne_zero μ ⟨1, by simpa⟩))
  intro s hs Z
  choose t hχ ht using (induction_on_prime · (by aesop) (fun _ ↦ (⟨1, ·.eq_one ▸ by
    simp +contextual [Z, ← d.mem_ker, indicator, ite_and, ↓map_one, finIdeleAbs,
      ideleAbs_eq_prod_of_v_eq_one, *]⟩)) fun I p _ hp ⟨t, b, ih⟩ ↦ by
    obtain ⟨v, rfl⟩ := exists_apply_eq_apply asIdeal (ofPrime hp)
    exact ⟨_, by simp [mul_le_one₀, *], (mul_left_surjective _).forall.2 fun x ↦ by
    rw [map_mul, hl v, ← mul_assoc, div_mul_cancel, map_mul, map_mul, Nat.cast_mul,
      natCast_mul_natCast_cpow, mul_mul_mul_comm, mul_assoc, ← ih]
    by_cases (d x).1 = I <;> by_cases hv : v ∈ S <;> simp [Z, v.3, heckeCoeff, *]
    · by_contra! n; simpa [↓← v_uniformizer_inv_mul_le_one_iff, count_coe_nonneg, *] using
        ((h₀ _ n.1).2 v hv).not_lt
    rw [h₃ x, mul_rpow] <;> simp +contextual [*, mul_mem, mem_Ô, count_coe_nonneg,
      norm_locField_eq_q_zpow, (ne_of_mem_of_not_mem · hv), finIdeleAbs, cpow_neg, inv_rpow, field,
      ofReal_cpow]⟩ : ∀ I, ∃ t, ‖χ I‖ ≤ 1 ∧ ∀ x, ite ((d x).1 = I) (Z x) 0 =
    χ I * I.absNorm ^ (-s : ℂ) * indicator (@idelesUnitOff K _ _ ∅ ∩ V) 1 (t * x))
  have E := funext e ▸ hasSum_eulerProd χ hχ hs
  refine (⟨.of_integral_ne_zero (by simp [eulerProd_eq_exp, *]), ·⟩)
    ((congrArg _ (funext fun x ↦ .trans (dite
    (f x = 0) (by aesop) fun h ↦ ((finprod_congr fun u ↦ congr(_ ^ $(Int.toNat_of_nonneg (by grind))
    )).trans (finprod_heightOneSpectrum_factorization' K (d x).ne_zero)) ▸ by simp [↓zpow_natCast,
    ← coeIdeal_pow, ← coeIdeal_finprod, coeIdeal_inj]) (tsum_congr (ht · x)))).trans
    ((hasSum_integral_of_summable_integral_norm (fun I ↦ .const_mul (.of_integral_ne_zero ?_) _) ?_
    ).unique ?_)) <;> simp [*, U.measurableSet, Pi.one_def, E.mul_right, integral_mul_left_eq_self,
    norm_indicator_eq_indicator_norm]; simpa using E.summable.norm.mul_right _

include hS

open InfinitePlace Valuation Units Real Module Pi DFunLike in
/-- Hecke's theorem at s = 1: for a Hecke character ψ ≠ 1 and a finite set S of primes, some
function of a real variable, analytic at 1, agrees with L^S(s, ψ) at all real s > 1 near 1.

Known result: Hecke L-functions: Euler product, continuation to s = 1, non-vanishing, prime
densities. -/
lemma exists_analyticAt_one_eulerProd (h0 : ψ ≠ 1) :
    ∃ F, AnalyticAt ℝ F 1 ∧ ∀ᶠ s in nhds 1, 1 < s → F s = eulerProd (heckeCoeff ψ S) s := by
  choose p hp using fun w ↦ show ∃ p : _ →A[ℝ] ℂ, ∀ x, p (mixedEmbedding K x) = Φ w x by
    let p : mixedEmbedding.mixedSpace K →ₐ[ℝ] ℂ :=
      AlgHom.comp (ite (w.embedding = Φ w) 1 conjAe) (dite _ (ofRealAm.comp
      <| evalAlgHom _ _ ⟨w, ·⟩ |>.comp (.fst ..)) fun _ ↦ (evalAlgHom _ _ ⟨w, by aesop⟩).comp
      (.snd ..))
    use ⟨p, p.toLinearMap.continuous_of_finiteDimensional⟩; cases mk_Φ w ▸ embedding_mk_eq _
      <;> aesop
  obtain ⟨⟨M, hM, H⟩, S, rfl⟩ := mem_nhds_zero_finAdele_iff.1
    ((isOpen_Ô.sdiff ((isCompact_idelesUnitOff_empty.diff h.1).image_auto
    val).isClosed).add_right (t := {-1}).mem_nhds (by simp)), hS.exists_finset_coe
  let X := (coeHom ℂ).comp (.coprod (∏ w, (.id _ / map (ofRealHom.1.comp normHom.toMonoidHom)).comp
    (map (p w).1.1.1) ^ n w) ψ); let d := (@isUnit_natCast_finAdele K _ _ _ hM).unit⁻¹
  choose T hT using @Set.Finite.exists_finset _ {w | ¬v (d.1 w) ≤ 1} d.1.2
  replace H y e := by simpa [d, ← mul_assoc, val_inj] using H (d * (val y - 1)) e
  choose hκ hI J using h.tate_integral T (adelicTent 1 d ⟨1, ·⟩) {y | d * (y.1 - 1) ∈ Ô K}
    .haar isOpen_Ô.preimage_of_continuous
    (by simp) (by simp_all [↓ite_eq_right_iff, le_antisymm_iff, mem_Ô]; grind
    [map_sub_eq_of_lt_right]) (by aesop) (by simp [mem_Ô]; grind [mul_le_one', map_sub_le])
  have ⟨c, c1, hc⟩ : ∃ c, ideleModule c = 1 ∧ X c ≠ 1 := (exists_ne h0).imp' (fun a ↦
    (map (algebraMap ..).1 (mk0 _ (rpow_pos_of_pos (ideleModule_pos (1, a⁻¹)) (finrank ℚ K)⁻¹).ne'),
    a)) (by simp [X, ideleModule, finIdeleAbs,
    ↓mixedEmbedding.finrank, rpow_inv_natCast_pow, finrank_pos.ne', rpow_nonneg, abs_of_nonneg])
  let A ρ (s : ℝ) a := X a * adelicTent ρ d (a.map val val) * ↑(ideleModule a ^ s)
  have Ac ρ s : Continuous (A ρ s ⟨·, 1⟩) := by
    simp [A, X]; fun_prop (disch := simp [IsUnit.ne_zero, ↓IsUnit.map, ne_of_gt])
  choose r hr Hr using (Metric.nhds_basis_closedBall.1 _).1 (isOpenMap_val.image_mem_nhds
    ((Ac 1 0).tendsto 1 ((isOpen_re_gt 0).mem_nhds (by simp [A, X]))))
  have hA {b s} := (Ac (r / 3 ^ b) s).integrable_of_hasCompactSupport (μ := .haar) (.intro
    (isOpenEmbedding_val.isCompact_preimage' (isCompact_closedBall ..) (Hr.trans (by simp)))
    (by simp [A]; grw [div_le_self] <;> bound))
  choose _ δ hδ C I hC using exists_abs_sub_thetaSum_le r d hr (by simpa using @Hr 0)
  have U b c s t := (fun e : _ = A _ s ↦ (integral_quotMeasure_tsum (principalIdeles K)
    ((((@hA b s).mul_prod (hI s t)).congr (.of_eq e)).comp_mul_left c)).imp_right (·.trans
    ((integral_mul_left_eq_self ..).trans (e ▸ J s t ▸ integral_prod_mul (A _ s ⟨·, 1⟩) _))))
    (by simp [A, X, ideleModule, mul_rpow, finIdeleAbs, apply_ite]; ac_rfl)
  have V b s hs := (fun v u ↦ (⟨v.sub' u, integral_sub v u, v.norm.add u.norm⟩ : _ ∧ _ ∧ _))
    ((U b 1 s hs).1.const_mul (X c)) (U b c s hs).1
  simp +contextual only [↓integral_const_mul, ↓U, c1, one_mul, ideleModule_principal_eq_one,
    ← mul_assoc (X c), ← sub_mul, ← mul_sub, map_mul, mul_left_comm c, tsum_mul_left,
    tsum_mul_right, ← ofReal_tsum, (by simpa [X, *, principalIdeles, mul_comm] using h.2 : ∀ γ :
    principalIdeles K, X γ = 1), A] at V
  choose P P0 e using eulerProd_erase (locIdele · (uniformizer _) |> h.norm_eq_one |>.le)
  obtain ⟨B, B0⟩ := (P T).fun_mul ((mellin_analytic_on_strip (by simp) (by fun_prop) (@hA _ 0).2
    (@hA _ 2)).2.2 1 (by simp)), mul_ne_zero (P0 T) (ne_zero_of_re_pos (integral_re (@hA 1 1) ▸
    integral_pos_of_integrable_nonneg_nonzero (x := 1) (continuous_re.comp (Ac ..)) hA.re ((by
    simp [A, val_inj, mul_pos_iff, mul_nonneg_iff]; grind : _ → _) <|
    @Hr ·) (by simpa [A, X, ideleModule])))
  refine ⟨_, ((((mellin_analytic_on_strip (s := 1 - δ / 2) ideleModule_pos (by fun_prop)
    (((V 0 (1 - δ / 2 + δ) (by bound)).2.2.const_mul C).2.mono' (.of_forall fun a ↦ ?_))
    (V _ 2 (by simp)).1).2.2 1 (by simpa)).fun_mul (P S)).fun_div B B0).div_const,
    (B.continuousAt.eventually_ne B0).mono fun x b s ↦ div_eq_of_eq_mul (mul_ne_zero (sub_ne_zero.2
    hc) (ofReal_ne_zero.2 hκ)) (by simp only [↓div_eq_iff b, *, heckeCoeff, comp]; ring)⟩
  simp [← ofReal_sub, abs_of_pos, rpow_pos_of_pos, rpow_add, -adelicTent]; grw [abs_sub_le,
    abs_sub_comm, hC, hC]; ring_nf; repeat simp [*, rpow_nonneg, le_of_lt]

/-- For a Hecke character ψ ≠ 1 and S finite, L^S(s, ψ) is continuous on real s ≥ 1, and the
ψ(ϖ_v), v ∉ S, have density −m on primes of degree one for some integer m ≥ 0, with L^S(1,
ψ) ≠ 0 if m = 0. -/
lemma exists_hasPrimeDensity (h0 : ψ ≠ 1) : ContinuousOn (eulerProd (heckeCoeff ψ S)) (.Ici 1) ∧
  ∃ m : ℕ, (m = 0 → ∀ s ≥ 1, eulerProd (heckeCoeff ψ S) s ≠ 0) ∧ HasPrimeDensity (heckeCoeff ψ S)
  (-m) := have ⟨F, hF, e⟩ := h.exists_analyticAt_one_eulerProd hS h0
  have A {s} := eulerProd_eq_exp (s := s) h.norm_heckeCoeff_le
  have T := hF.continuousAt.continuousWithinAt.congr' (eventually_nhdsWithin_iff.2 (by grind))
  ⟨continuousOn_extendFrom (by simp) fun _ ↦ (·.out.eq_or_lt.rec (· ▸ ⟨_, T⟩) (⟨_, A ·
  |>.2.2.cexp.continuousWithinAt⟩)), (hF.exists_eventuallyEq_pow_smul_nonzero_iff.2
  (frequently_gt_nhds 1 <| e.mp <| ·.mono (by aesop_cat))).imp fun m ⟨f, g, k, l⟩ ↦ ⟨by
  simp_all [le_iff_eq_or_lt, or_imp, eulerProd, extendFrom_eq _ T, l.self_of_nhds],
    hasPrimeDensity_of_tendsto h.norm_heckeCoeff_le k (g.continuousAt.continuousWithinAt.congr'
    (eventually_nhdsWithin_iff.2 ((e.and l).mono (by aesop (add simp [ne_of_gt, cpow_neg])))))⟩⟩

/-- For a Hecke character ψ of a number field with ψ² ≠ 1 and a finite set S of primes, the
partial L-function L^S(s, ψ) does not vanish at any real s ≥ 1.

Known result: Hecke L-functions: Euler product, continuation to s = 1, non-vanishing, prime
densities. -/
lemma eulerProd_ne_zero (h2 : ψ ^ 2 ≠ 1) {s} (hs : 1 ≤ s) : eulerProd (heckeCoeff ψ S) s ≠ 0 := by
  choose _ m k H using fun i ↦
    (h.pow (![1, 2] i)).exists_hasPrimeDensity hS (by fin_cases i <;> aesop)
  have := (hasPrimeDensity_const (-3)).re_le_re (.sum ![4, 1] H) (.mono hS.compl_mem_cofinite fun v
    _ _ ↦ by simp [sq,
    heckeCoeff, *]; nlinarith [h.norm_eq_one (locIdele v (uniformizer _)) ▸ sq_norm_sub_sq_re _])
  simp_all; norm_cast at *; grind
