/- GID: D5/S3/Zeros/GRH/New/Filling/GlobalSieve
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Filling/GlobalSieve
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Filling.GlobalSieve. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Filling/GlobalSieve.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Adelic.Adeles.FinitePlaceDensity
import D5.S3.Zeros.GRH.New.Filling.NearTerms
import D5.S3.Zeros.GRH.Lib.Adelic.CuspForms.RealConvolution
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Positive kernels and a sieve losing almost nothing. Systems of positive kernels, of one kind at
real and finite places and with each kernel the integral of the next over a common last entry,
multiply over places, and one-sided Poisson summation, entry by entry, bounds the sum over rational
points losing only a factor near 1, as the second moment's main term requires. Inductive Fourier
transforms of Kloosterman integrals and spectral large sieves losing a constant or X^ε are known.
Related work: Jacquet, Smooth transfer of Kloosterman integrals, 2003; Jacquet, Kloosterman
identities over a quadratic extension, 2004; Blomer–Buttcane, GL(3) Kloosterman sums and the
spectral large sieve, 2015; Deshouillers–Iwaniec, Kloosterman sums and Fourier coefficients of cusp
forms, 1982.

This file: Adelic sieve: one-sided Poisson summation per pivot, frequency sum bound, final sieve
inequality. -/

namespace Filling

open NumberField ENNReal Finset Fintype MeasureTheory Measure Real AddSubgroup Matrix ComplexOrder
  SemilocalField Complex
variable {E} [Field E] [CMType E] {𝔰} (S : Filling E 𝔰) (T : Finset (FinPlace E))

/-- The character x ↦ ψ_f(−x/ϖ) of the finite adeles, restricted to ∏_{w∈T} E_w by extending
elements by zero off T. -/
noncomputable def charOnPlaces : AddChar (LocProd T) ℂ :=
  S.selfDualChar.compAddMonoidHom (adeleOfLocal T)

lemma charOnPlaces_evalPlaces {x} (h : x ∈ integralOff T) : S.charOnPlaces T (evalPlaces T x) =
  S.selfDualChar x := .symm (eq_of_div_eq_one (S.selfDualChar.map_sub_eq_div .. ▸
  S.selfDualChar_eq_one_of_mem _ ((sub_adeleOfLocal_mem_iff T).2 h)))

/-- The bound [ξ]^((k − n⁷)/2) (den ξ)⁻⁶ b^(n⁹f) at a frequency ξ at the places of T, with n = ϱ
+ 1, [ξ] = [R : ξR] the generalised index. -/
noncomputable def frequencyGain (ξ : LocProd T) := √(genIndex ξ) ^ (𝔰.k - 𝔰.n ^ 7) / denomIndex O
  ξ ^ 6 * S.b ^ (𝔰.n ^ 9 * numInfPlaces E)

/-- The element t of E read as the point ((l_v v(t))_v, t) of ℂ^f × ∏_{w ∈ T} E_w, for scales
l_v at the infinite places. -/
noncomputable def ratPoint (l : _ → ℂ) t := (fun v ↦ l v * Φ v t, ratToPlaces T t)

attribute [local simp] frameScaleSq ratPoint unitOrOne intVectors funext_iff wave IsUnit.map
  prod_eq_zero_iff entrywise pi_pos Prod.isUnit_iff Pi.isUnit_iff toAdele Units.val_inj padTuple
  selfDualChar stdAddChar mul_mem mul_sum

/-- Assume B ≥ 1, |c_v|⁻¹ ≤ |x_v| ≤ B. Over any finite set of nonzero T-integers y, the sum of
[y]_T^(k/2) (den y)⁻⁶ ∏_v ℓ_k(1/|c_v y|_v), ℓ_k(r) = r^k min(1,r)⁶, is at most (b rd_E)^(3f) ∏_v
|x_v|^k (bB²)³. -/
lemma sum_frequencies_le [WeilData E] [T.StarStable]
    B k X (c : _ → ℂ) (x : _ → ℝ) (hB : 1 ≤ B) (hx : ∀ v, ‖c v‖⁻¹ ≤ |x v| ∧
  |x v| ≤ B) (h : ∀ y ∈ X, y ≠ 0 ∧ y ∈ ratIntegralOff T) : ∑ y ∈ X, (∏ v, dampedPower k ‖c v * Φ v
  y‖⁻¹) * (√(genIndex (ratToPlaces T y)) ^ k / denomIndex O (ratToPlaces T y) ^ 6) ≤
  (∏ v, |x v| ^ k * (S.b * B ^ 2) ^ 3) * (S.b * rootDiscr E) ^ (numInfPlaces E * 3) := by
  obtain ⟨Z, _, b⟩ := by simpa using tsum_sublatticeDisc_inv_le (1 : Gf E (Fin 2)) 1,
    rootDiscr_pos E, S.thousand_le_b
  simp_rw [dampedPower, norm_mul, mul_inv]; grw [← b, ← show 200 * (numInfPlaces E * 2) ≤ S.b by
    bound [S.f_le_b], ← ofReal_le_ofReal_iff, ENNReal.ofReal_mul, ← Z, ← ENNReal.sum_le_tsum
    (X.image (colSpan !![1; ·])), sum_image fun y _ u _ e ↦ (e.le ⟨1, rfl⟩).elim (by
    simp +contextual), mul_sum, ofReal_sum_of_nonneg, sum_le_sum fun y hy ↦ ?_]
  obtain ⟨⟨a, e, p, -⟩, u, w, f⟩ := exists_preimageLattice_eq_colLattice (m := finAdeleMat !![1; y])
    ⟨!![1, 0], by simp [vecMul]⟩, (denomIndex_ne_zero T _).pos, h y hy, show 1 = !![1; y].rank by
    simp [rank_eq_finrank_span_cols, finrank_span_eq_card]
  have : 0 < genIndex a.1.det := genIndex_pos a.det
  obtain ⟨D, _, -⟩ := sublatticeDisc_mul_index_sq_le (one_mul 1) _ !![,,] f le_rfl a (K := ⊤) (D :=
    ((∏ v, (1 + ‖Φ v y‖ ^ 2)) * genIndex a.1.det) ^ 2)
    (by erw [det_unique, genIndex_algebraMap]; simp [abs_norm_eq_prod_norm_sq,
    conj_mul', mul_pow, ← prod_pow]; norm_cast; simp) (by positivity) (.mul .one p) (by simp)
  simp [submoduleIndex, -det_unique] at D; grw [ite_eq_left (by tauto), le_of_sq_le_sq D,
    ← ENNReal.ofReal_mul, sqrt_genIndex_le_prod_norm T w,
    ← pow_le_pow_right₀ (mod_cast u) (by simp : 3 ≤ 6), ← (?_ : genIndex a.1.det ≤ denomIndex
    ..), fun v ↦ (?_ : min 1 (‖c v‖⁻¹ * _) ^ 6 ≤ (1000 * B ^ 2 / (1 + ‖Φ v y‖ ^ 2)) ^ 3), (hx _).1]
  any_goals intros; positivity
  · gcongr 1; simp [field, prod_pow, div_pow, mul_pow, *]
  · grw [pow_mul _ 2 3, (hx v).1, (hx v).2, min_def]; gcongr
    clear * - w hB; split <;> simp [*, field] at * <;> nlinarith [norm_nonneg (Φ v y)]
  grw [← submoduleIndex_colLattice_div, div_nat_le_self_of_nonnneg (by simp), ← e, Nat.cast_le]
  exact Nat.le_of_dvd u ((relIndex_dvd_of_le_left _ fun z ↦ by simp_all [preimageLattice, mem_Ô_iff
    T, -e]).trans (dvd_of_eq ((inf_relIndex_right ..).trans ((relIndex_comap _ (.mk' (evalPlaces
    T <| · 0) (by simp)) _).trans
    (congrArg _ (by ext; simp [locProd_O_eq_map_evalPlaces, Fin.exists_fin_succ_pi]))))))

variable [S.IsAdmissible] {A : Finset Eˣ} (hA : ∀ t ∈ A, ↑t ∈ ratIntegralOff T ∧
  ↑t⁻¹ ∈ ratIntegralOff T) (hg : (↑S.g)⁻¹ ∈ ratIntegralOff T)
include hA hg

/-- Iterated Poisson summation for a system on ℂ^f × ∏_T E_w, entries in finite sets V ⊂ A of
T-units, c_a = vol(Ô)∏_v l(v,a)⁻², l = `Filling.frameScaleSq`: if ε bounds sums of β over
nonzero T-integral frequencies and (∑_p Λ_i(p))² ≤ Γ∏_{a<i}c_a, then
Re ∑_{t∈V,p,q} J_{i+1} ≤ ∏_{a≤i}c_a·(En + (2i+1)Γε).

Positive kernels and a sieve losing almost nothing. -/
lemma one_sided_poisson {n J En Λ β} (K :
  SieveSystem (.map (unitOrOne ∘ ·) unitOrOne) (.map ((·⁻¹.1) ∘ ·) (ratToPlaces T
  S.g⁻¹ * ·⁻¹.1)) n J (fun x ↦ (∏ v, wave (x.1 v)) * S.charOnPlaces T x.2) En Λ β) {Γ ε} (hP : ∀ a
  (c : _ → ℂ), (∀ v, ‖c v‖⁻¹ ≤ |S.kappa v| / S.g) → ∀ X, (∀ y ∈ X, y ≠ 0 ∧ y ∈ ratIntegralOff T) →
  ∑ y ∈ X, β (ratPoint T (fun v ↦ c v / S.frameScaleSq v a) y) ≤ ε) (hε : 0 ≤ ε) (hΛ : ∀ i p, 0 ≤
  Λ i p) : let hd i (p : Fin i → A) t a := .map (unitOrOne ∘ ·) unitOrOne (ratPoint T
    (S.frameScaleSq · a) (padTuple (p · |>.1) t a).1)
  let c a := volÔ E / ∏ v, S.frameScaleSq v a ^ 2
  (∀ i ≤ n, (∑ p, Λ i (hd i p 1)) ^ 2 ≤ Γ * ∏ a ∈ range i, c a) → ∀ i ≤ n, ∀ V ⊆ A,
  (∑ t ∈ V, ∑ p, ∑ q, J (i + 1) (hd i p t) (hd i q t)).re ≤
    (∏ a ∈ range (i + 1), c a) * (En + (2 * i + 1) * Γ * ε) := by
  intro hd c hΓ
  refine Nat.strongRec fun i ih hi V hV ↦ ?_
  have := K.step_sum hi (hd i · 1)
  extract_lets F at *
  obtain ⟨⟨N, L⟩, o, ⟨hF, e, hM⟩, c0, d⟩ := show 0 ≤ F ∧ _ from K.nonneg_and_lowerSemicontinuous hi
    _ fun _ _ ↦ dite_eq_left rfl, (isOpen_univ.prod (isOpen_integralOff T) : @IsOpen (𝔸 E) _
        _), this,
    (by positivity : 0 ≤ c i), LinearMap.det_pi (S.frameScaleSq · i • (1 : ℂ →ₗ[ℝ] ℂ))
  set U := _ ×ˢ _; let m (z : 𝔸 E) := (fun v ↦ S.frameScaleSq v i * z.1 v, evalPlaces T z.2)
  have P : MeasurePreserving m (volume.restrict U) (ENNReal.ofReal (c i) •
    volume) := by simpa [d, U, volume_eq_prod, ← prod_restrict, prod_smul_left, prod_smul_right,
    abs_prod, div_eq_mul_inv, c, mul_smul, -frameScaleSq] using!
    MeasurePreserving.prod ⟨by fun_prop, map_linearMap_addHaar_eq_smul_addHaar _
    (d.trans_ne (by simp))⟩ ⟨by fun_prop, map_evalPlaces_restrict_volume T⟩
  have I := U.indicator_nonneg fun x _ ↦ (N (m x)).1
  refine (le_of_eq_of_le ?_ (IsDualFamily.sum_le_of_fourier ((integrable_indicator_iff
    o.measurableSet).2 (P.integrable_comp_of_integrable hF.re.smul_measure_nnreal)) I
    (V.map ⟨(⟨_, ·.1, rfl⟩), fun _ ↦ by simp⟩) (forall_mem_map.2 fun t h ↦ .of_frequently fun y k ↦
    (ite_eq_left ⟨trivial, (hA t (hV h)).1⟩).trans_le ((ofReal_le_ofReal_iff
    (k.exists.elim (I · |>.trans))).1 (((L _ fun _ ↦ continuousAt_const.update _
    (.prodMap (.piMap fun v ↦ continuousAt_unitOrOne (.mk0 _ (by simp [m])))
    (continuousAt_unitOrOne (t.map (ratToPlaces T).1)))).comp (g := m) (by fun_prop)).frequently _
    (k.mp (.mono (o.eventually_mem ⟨trivial, (hA t (hV h)).1⟩) (by simp +contextual [F,
    ofReal_le_ofReal])))))) ((reindex_equiv (Equiv.divRight₀ _ S.varpi_ne_zero).finsetCongr).1.2
    fun Y ↦ ?_))).trans (?_ : c i * (‖∫ x, F x‖ + ε * (∑ p, Λ i (hd i p 1)) ^ 2) ≤ _)
  simp +contextual [m, U, F, ← Subring.mem_comap, hA _ (hV _)]
  congr! <;> simp +contextual [hd, ↓Function.eq_update_iff]
  · erw [sum_map]
    grw [Y.insert_erase_subset 0, sum_insert (by simp),
      ← sum_filter_of_ne (p := (· ∈ ratIntegralOff T)), ← hP i (2 * π * .I / Φ · S.ϖ)
      (by simp [abs_kappa_eq, field, abs_of_pos]), mul_add, sum_mul, mul_sum]
    · gcongr with y h; any_goals simp at h; grw [← hM _ (by simp [h])]
      all_goals grw [← norm_smul_of_nonneg c0, ← toReal_ofReal c0, ← integral_smul_measure,
        ← P.hasLaw.integral_comp (by cases hF; simp [charOnPlaces, c]; fun_prop),
        ← integral_indicator o.measurableSet]; simp [m, U, ← eq_re_of_ofReal_le (N _),
        Set.indicator, apply_ite, ↓sub_conj, ← Complex.exp_sum, sum_mul, fourierChar_apply,
        div_eq_mul_inv, -neg_sub, -frameScaleSq]
      congr! 8; field; erw [S.charOnPlaces_evalPlaces T (mul_mem h.2 ‹_›)]; simp; ac_rfl
    simp +contextual
    refine fun y _ n ↦ (sub_adeleOfLocal_mem_iff T).1 ((S.forall_selfDualChar_mul_eq_one_iff _).1
      fun ⟨r, hr⟩ ↦ (mul_eq_right₀ (norm_ne_zero_iff.1 n)).1
      (.trans ?_ (integral_add_left_eq_self _ (0, r - adeleOfLocal T (evalPlaces T r)))))
    rw [← integral_const_mul]; congr with; simp [Set.indicator, U, m, add_mem_cancel_left, sub_mem,
      (mem_Ô_iff T).1 hr, mul_add, AddChar.map_add_eq_mul, div_eq_mul_inv, -frameScaleSq]
    simp_rw [adeleOfLocal_evalPlaces]; ring_nf!
  grw [← re_eq_norm.2 (integral_nonneg N), e, hΓ, prod_range_succ_comm, mul_assoc]
  gcongr; cases i <;> simp
  grw [re_le_norm, K.norm_bot_le, mul_comm]
  linear_combination (norm := ring_nf) ih _ .refl (by omega) A le_rfl + ε * hΓ _ hi
  simp [↓sum_mul, reindex_equiv (Fin.snocEquiv _), sum_prod_type, Fin.snocEquiv, sq, ←
    sum_add_distrib, ← A.sum_attach, show ∀ i p t, hd _ (Fin.snoc p t) 1 = hd i p t by
    grind [padTuple, Fin.snoc, Fin.castLT]]
  gcongr with t
  grw [sum_eq_add_sum_sdiff_singleton_of_mem ‹_›, ← A.attach.sdiff_subset]; gcongr with v
  let y := (S.g : E)⁻¹ * (t.1⁻¹ - v.1⁻¹)
  have : y ≠ 0 := by simp [y]; grind
  grw [re_le_norm, add_comm, K.off_diagonal, ← hP ‹_› S.g (by grw [← one_le_abs_kappa]; simp)
    {y} (by grind [mul_mem, sub_mem])]
  any_goals rw [show _ - _ = ratPoint T (S.g / S.frameScaleSq · ‹_›) y by
    simp [hd, y, field, ↓map_sub, ↓map_mul, ↓map_units_inv]]
  any_goals simp [*]
  all_goals grind [Finset.sum_nonneg, mul_nonneg]

/-- The sieve, under `Filling.IsAdmissible`: for the forms J_v of the Bessel systems, a system J' at
T (bounds e, `finHeadWeight`, `Filling.frequencyGain`), finite sets U ⊂ A of T-units, g⁻¹ a
T-integer: Re ∑_{t∈U, p,q∈A^ϱ} J'∏J_v ≤ vol(Ô)^(ϱ+1)∏l(v,i)⁻²·(e∏_v((1+b⁻¹⁰)/deg_v) +
b^(−6kf−10)/deg).

Positive kernels and a sieve losing almost nothing. -/
lemma sieve [WeilData E] [T.StarStable]
    {J' e U} (h' : SieveSystem unitOrOne (ratToPlaces T S.g⁻¹ * ·⁻¹.1) 𝔰.ϱ J'
  (S.charOnPlaces T) e (finHeadWeight (𝔰.n ^ 6)) (S.frequencyGain T)) (hU : U ⊆ A) :
  let x v (p : Fin 𝔰.ϱ → A) t i := unitOrOne (S.frameScaleSq v i * Φ v (padTuple (p · |>.1) t i).1)
  let y p t := Units.map (ratToPlaces T) ∘ padTuple (p · |>.1) t
  (∑ t ∈ U, ∑ p, ∑ q, (∏ v, (S.besselSys v).bandLimit 𝔰.n (x v p t) (x v q t)) * J' 𝔰.n (y p t) (y q
  t)).re ≤ (∏ i ∈ range 𝔰.n, volÔ E / ∏ v, S.frameScaleSq v i ^ 2) * ((∏ v, (1 + S.b⁻¹ ^ 10) /
    (S.besselSys v).deg) * e + S.besselDegree⁻¹ / S.b ^ (6 * 𝔰.k * numInfPlaces E + 10)) := by
  obtain ⟨b, r, _, N, K, Z, h, θ⟩ := S.one_le_b, rootDiscr_pos E, (by simp : S.g ≠ 0).pos,
    S.N_prime.pos, S.one_le_abs_kappa, S.sum_frequencies_le T, (S.besselSys · |>.band_limits.1),
    (by simp [Shape.bandConst] : 0 < 𝔰.bandConst)
  unfold headWeight finHeadWeight dampedPower at *
  refine ((S.one_sided_poisson T hA hg (h'.pi h) (fun a c hc X hy ↦ by
    simp_rw [frequencyGain, ratPoint, prod_mul_distrib, mul_assoc, ← mul_sum, ← mul_assoc,
      ← sum_mul] at *
    grw [Z _ _ _ _ (S.kappa · ^ (2 * 𝔰.ϱ + 1) / (S.g * S.N)) _ (fun v ↦ ⟨by
      simp [div_eq_mul_inv]; grw [hc, Nat.sub_le] <;> simp [pow_succ, field, K], by
      grw [abs_div, abs_pow, abs_kappa_le, div_le_self] <;> norm_cast <;> bound⟩) hy]; bound)
    (by positivity) (by intros; positivity) (Γ := S.b ^ _) (fun i hi ↦ by
    let m (p : Fin i → A) j := ∏ a ∈ range j, (padTuple (p · |>.1) 1 a).1
    have L v a := (by grw [frameScaleSq, ← pow_abs_two_mul, Nat.sub_le, abs_kappa_le,
      div_le_self] <;> bound : S.frameScaleSq v a ≤ _)
    beta_reduce
    grw [(.trans ?_ ((prod_univ_sum ..).ge.trans (prod_le_prod₀ (by intros; positivity) fun (j :
      Fin i) _ ↦ Z (S.N ^ i) (𝔰.n ^ 6) (image (m · j.succ) univ) (∏ a ∈ range j.succ, S.frameScaleSq
      · a) (fun _ ↦ S.N ^ i) (by bound) (by simp; grw [← K]; simp; bound) (by simp [m, hA,
      prod_mem, apply_dite, dite_eq_iff, -Subring.mem_comap]))) : ∑ p, _ ≤ _),
      volÔ_eq, abs_of_pos (by bound), N_le, N_le, L, half_le_self, S.rd_le_b]
    simp [field, ← pow_mul, ← pow_add, mul_pow]; grw [hi]
    iterate 3 simp [r, -frameScaleSq, le_of_lt, prod_pos]
    grw [← image_subset_iff.2 fun p h ↦ mem_piFinset.2 fun _ ↦
      mem_image_of_mem _ h, sum_image fun p _ q _ e ↦ funext fun j ↦ ?_]
    · simp_rw [@prod_range _ _ i, @prod_comm (Fin i), ← prod_mul_distrib]
      gcongr 3 <;> simp [m]
      split <;> simp +contextual [denomIndex, relIndex_eq_one.2, IsConcreteLE.le_iff, div_nonneg, *]
    simpa [m, prod_range_succ] using congr($e j / $(@Fin.cases i (fun k ↦ m p k = m q k) (by bound)
      (congrFun e) j.castSucc))) 𝔰.ϱ le_rfl U hU).trans_eq' (by congr! <;> ext <;> simp)).trans ?_
  gcongr
  grw [← IsAdmissible.prod_band_le_inv_deg, show _ + 1 ≤ S.b by grw [← k_le_b, ← S.ϱ_le_k]; grind,
    S.rd_le_b]
  simp [abs_div, field, mul_pow, ← pow_mul, ← pow_add, ← pow_succ', mul_comm _ (∏ _, _), mul_assoc]
  gcongr; grind [Fintype.card_pos, mul_le_mul_right S.pow_le_k (numInfPlaces E)]
