/- GID: D5/S3/Zeros/GRH/Lib/GaloisRep/LocalGlobal/EigencharCompatibility
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/GaloisRep/LocalGlobal/EigencharCompatibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.GaloisRep.LocalGlobal.EigencharCompatibility. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/GaloisRep/LocalGlobal/EigencharCompatibility.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.GaloisRep.Main.SphericalAllRanks
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Local-global compatibility at tame level, away from and at l (known result; see
Lib.GaloisRep.LocalGlobal.LabelCompatibility).

This file: Local-global compatibility for sorted tame Iwahori eigencharacters at split places. -/

open Algebra QZChar ComplexOrder Fintype Ideal MonoidHom Polynomial QuotientGroup Set Subgroup
  Valued WithZero

attribute [local simp] Pi.mulSingle_apply Subring.mem_centralizer_iff Units.ext_iff funext_iff
  heckeGL norm_locField_eq_q_zpow coe_normAbsChar_locField

variable {ℓ} [ThePrime ℓ] [PadicIso ℓ] {E n} [Field E] [CMType E] {w} [Fintype n] {κ P ξ} {hw :
  _ ≠ w} {f : (stdSpace E n).forms κ} (H :
  IsIwahoriEigen (localFormRep (stdSpace E n) κ hw) (torusChar ξ) f)

include H

lemma IsIwahoriEigen.apply_eq_one_of_principal_unit {y} (h : v (y.1 - 1) < 1) :
  normAbsChar.prod (.pi ξ) y = 1 := by
  simpa [-Units.ext_iff, normAbsChar, dominantTorus, Monotone, apply_ite, H.2, (smul_left_injective
    ℂ H.1).eq_iff' (one_smul ..), by simpa using v.map_one_add_of_lt h] using fun i a ↦ (H.2.2
    (Pi.mulSingle i y) a).symm.trans (compactMean_apply (diagGL_mem_proIwahori.2 (by aesop)) _)

lemma IsIwahoriEigen.char_pow_q_sub_one_eq_one y (h : v y.1 = 1) : normAbsChar.prod (.pi ξ)
  (y ^ (w.q - 1)) = 1 := H.apply_eq_one_of_principal_unit (card_ResField w ▸
  residue_eq_iff_valuation_sub_lt_one.1 (algebraMap_pow_card_pred_eq_one (K := ResField w) (k :=
  ResField w) (.mk0 ⟦⟨_, h.le⟩⟧ (residue_eq_iff_valuation_sub_lt_one.1.mt (by simp [h])))))

/-- Let r be attached to an eigenform f (Weil data) with Iwahori eigencharacter ∏
ξ_i(t_i)|t_i|^{N−i} at split w, |ξ_1(ϖ)| ≥ … ≥ |ξ_N(ϖ)|. Above w, r has finite type and the
jumps of κ, and ∏(X − ιξ_i(x)) kills each s of degree k ≥ 0 with Artin preimage x of order
k.

Known result: Local-global compatibility at tame level, away from and at l. -/
lemma Attached.local_global_of_eigencharacter [Nonempty n] [WeilData E]
    [EmbeddedNumberField E] {r : GalRep ℓ E n} {A :
  ClosurePlace} (he : IsEigenform f.1 P) (hr : Attached P r) (hs : Antitone (‖ξ · (uniformizer
  w) |>.1‖)) (hA : IsPlaceOver A w) (s : decompGroup _ A) x (k : ℕ) (hQ : IsFrob A (w.q ^ k) s.1⁻¹)
  (hx : localArtin Gal(Ω/E) A w x = s) (hv : v x.1 = .exp (-k)) : IsFiniteTypeAt r A ∧
  HasJumpsAt r A (jumps κ (card n)) ∧ PolyKillsAt r A s.1 (∏ i, (X - C (ιℓ (ξ i x)))) := by
  wlog k₀ : 0 < k generalizing s x k
  · obtain ⟨⟨⟩, φ, hφ, e⟩ := not_lt.1 k₀,
      hA.exists_frob_inv_eq_localArtin (Γ := Gal(Ω/E)) (v_uniformizer w)
    have ⟨a, b, z⟩ := this _ _ 1 (by simpa) e (by simp) one_pos
    have G n h := (this (s * φ⁻¹ ^ n) (x * uniformizer w ^ n) n
      (by simpa using (hφ.pow n).mul_iff.2 hQ) (by simp_all) (by simp [*]) h).2.2
    use a, b, fun l ↦ eval₂_eq_zero_of_pos_pow ⟨_, by simp [commutes]⟩ ⟨_, by simp
                  [commutes]⟩ (z.1 l) (by simp) (by simpa using! G · · |>.1 l), @fun j d _ c ↦ ?_
    obtain ⟨⟨f, hf, -⟩, p⟩ := w.exists_q_eq_pow (hA.valuation_natCast_lt_one_iff.1
      (j.inducesPlace.1.1 ▸ valuation_comap_intQpBar_lt_one _)), a.2
    have W : IsWeilPair (j.toGp φ⁻¹) f := by simpa [IsWeilPair, j.isFrob_iff, ← hf]
    use p, eval₂_eq_zero_of_pos_pow ⟨_, forall_mem_range.2 (commute_coefEnd_linearFrob p c)⟩ ⟨_,
      forall_mem_range.2
      (commute_coefEnd_linearFrob p W)⟩ (z.2 W).2 (by simp) fun n h ↦ linearFrob_pow p W _ ▸
      linearFrob_mul p c (W.pow _) ▸ by simpa using! ((G n h).2 (c.mul (W.pow _))).2
  replace hs : Antitone (‖ξ · x |>.1‖) := fun i j c ↦ le_of_pow_le_pow_left₀ w.q_bounds.1.ne'
    (by simp) (by simpa [← norm_pow, by simpa [div_pow, div_eq_iff, ← pow_mul]
    using (H.char_pow_q_sub_one_eq_one (x / uniformizer w ^ k) (by simp [*]))] using
    pow_le_pow_left₀ (by simp) (hs c) _)
  let D := (zpowers (normAbsChar.prod (.pi ξ) x)).comap (normAbsChar.prod (.pi ξ))
  induction' m : D.index using Nat.strongRec with _ ih generalizing E k
  have := @finiteIndex_of_le _ _ _ D ⟨(@index_pow_local_le _ _ _ _ ⟨(mul_pos k₀
    w.q_bounds.1).ne'⟩ w).1⟩ fun _ ⟨y, t⟩ ↦ t ▸ ⟨-(v y.1).log * (w.q - 1), by simpa
    [mul_zpow, zpow_mul, ← zpow_natCast, inv_eq_iff_mul_eq_one] using (H.char_pow_q_sub_one_eq_one
        (x ^ (v y.1).log * y ^ k) (by rw [← exp_log (x := v _)] <;> simp [*, mul_comm]))⟩
  obtain G | ⟨p, hp, h⟩ := not_or_of_imp D.index.exists_prime_and_dvd
  · simp [D, hv, -zpow_neg, (zpow_right_strictMono₀ (by simp : (1 : ℂ) < w.q)).injective.eq_iff,
      eq_top_iff', mem_zpowers_iff, ← zpow_mul] at G
    cases Int.eq_one_of_dvd_one k.cast_nonneg ((G (uniformizer w)).imp (by simp +contextual))
    exact isUnitary_localFormRep |> fun b ↦ (H.exists_isExponent b self_mem_cyclicSpan).elim fun u
      ⟨h, o, l⟩ ↦ hasHeckePolyAt_iff_localFormRep.2 ⟨compactMean_mem_levelSpace u, fun
      j ↦ Multiset.esymm (List.ofFn (ξ · x |>.1)) j / w.q ^ j.choose 2,
      (Multiset.prod_X_sub_X_eq_sum_esymm (List.ofFn (ξ · x |>.1))).trans (by simp [heckePoly,
      mul_div_cancel₀, mul_assoc]), fun j ↦ sub_eq_zero.1 (Not.imp_symm (b.1 _) (by
      simp +contextual (maxDischargeDepth := 4) [-mem_levelSpace, (isBiInvariant_basicDoubleCoset
        j).heckeFun_adjoint _ _ b.2, IsBiInvariant, ↓(isBiInvariant_basicDoubleCoset
      j).heckeFun_adjoint _ (compactMean_mem_levelSpace u) b.2 (compactMean_mem_levelSpace u),
        IsBiInvariant.heckeFun_mem, compactMean_mem_levelSpace, b.compactMean_adjoint,
        ← (isBiInvariant_basicDoubleCoset j).heckeFun_comm, by
        simpa [partialHecke_zero_eq_heckeGL, -mem_levelSpace] using (l.apply_partialHecke (x := ·)
          hv · bot_le j)]))⟩ |> fun k ↦ ((sphericalCompat_std w (by simp) (he.of_mem_cyclicSpan (by
      simpa using compactMean_mem_cyclicSpan 1 h) fun c ↦ o (l.eq_zero_of_eq_zero_on_spherical hv
      (fun y ↦ (by simpa [·, eq_comm] using G y)) hs (by simp [c, ← compactMean_eq_self (H := Kw ..)
      · · ▸ b.compactMean_adjoint u _])))).2 hr k.1 A hA).imp (isGoodAt_iff.1 · |>.1) (.imp_right
      (by simpa [Polynomial.map_prod, Fin.prod_ofFn] using · _ _ k s (by simpa using hQ)))
  obtain ⟨χ, o, ⟨x₀⟩, h⟩ := by simpa [addOrderOf_eq_prime_iff (hp := ⟨hp⟩), DFunLike.ext_iff] using
    @exists_prime_addOrderOf_dvd_card' (Additive (_ ⧸ D) →+ QZ) _ _ p ⟨hp⟩ (by rwa [card_hom_QZ])
  choose μ u _ _ _ hu hb B hD hk using
    exists_step_of_local_char hw hA hp (χ.toMultiplicativeRight.comp (mk' D)) h (o ·) fun y a ↦
    χ.map_zero ▸ congrArg χ ((eq_one_iff _).2 ⟨0, (H.char_pow_q_sub_one_eq_one y a).symm⟩)
  cases (hb u).2 rfl
  obtain ⟨Y, X, f', _, he', hS, hξ'⟩ := hD x, (hk x).trans (χ.map_zero ▸ congrArg χ
    ((eq_one_iff x).2 (mem_zpowers _))), exists_baseChange_isIwahoriEigen hu hb (by simp [*]) H
  obtain ⟨⟨_, hr'⟩, n, rfl⟩ := (sphericalCompat_std u f'.2 he').1, Int.ofNat_dvd.1 (dvd_neg.1 ⟨_, by
    simpa [v_localNorm (absNorm_pow_inertiaDeg ..), *] using
      congr(log (v $((exists_localNorm_of_abelianLift_artinAt X).choose_spec).1)).symm⟩)
  rw [pow_mul, absNorm_pow_inertiaDeg, hA.artinAt_eq_of_localArtin_eq hx] at *
  obtain ⟨⟨y, o, d⟩, a, b, c⟩ := B.exists_localArtin_eq (g := (stepField μ).fixingSubgroupEquiv
    ⟨s, (·.2 ⟨s, X⟩)⟩) hQ n, (hS.exists_attached_descent hr' he' he).2.1 hr A
  have e := (div_mem_ker_iff _).1 (H.apply_eq_one_of_principal_unit (by simpa using
    (hA.localArtin_tame_symbol (x := 1) (hA.isUniformiser_iff.2 (hA.exists_uniformiser
    Gal(Ω/E)).choose_spec.1) (by simp [v_localNorm (absNorm_pow_inertiaDeg ..), *])
    ((div_mem_ker_iff _).2 (hx ▸ (B.localArtin_adeleNorm (AlgEquiv.restrictScalarsHom E)).1 d))
    congr($(((DiscreteUnits.ofBase Gal(Ω/E) Ω _).1.exists_nsmul
    (FinPlace.q_bounds _).1.ne').choose_spec).1))))
  simp_rw [← by simpa using congr($e.2)] at hs ⊢
  exact (ih _ (m ▸ Finite.card_subtype_lt fun ⟨y, e⟩ ↦ h (congr(χ $e) ▸ hk _ ▸
    abelianLift_artinAt_of_mem_closure (L := stepField μ))) hξ' he' hr' B _ _ _ ‹_› d o
    (by nlinarith) hs (.trans (by rcongr; simp; simp [D, ↓← e, mem_zpowers_iff, ↓norm_localNorm])
    (index_ker ((mk' D).comp (localNorm E u))))).imp a (.imp (b _) ((c ⟨s, X, Y⟩).2 _))
