/- GID: D5/S3/Analytic/Zeta/NumberField/ZetaProduct
   generality: G
   mirror-B: D5/B/S3/Analytic/Zeta/NumberField/ZetaProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An analytic extension matching a nontrivial cyclotomic Artin series does not vanish at one. -/
module

public import D5.S3.Analytic.Zeta.NumberField.ZetaProductFactorization

public import D5.S3.Analytic.Zeta.NumberField.ZetaProductAnalytic

@[expose] public section

noncomputable section

open NumberField

open scoped nonZeroDivisors

namespace Chebotarev

attribute [local instance] Fintype.ofFinite

open Filter Topology Set in
/-- **Ingredient A, bounded real-log form.** Taking `log ‖·‖` of the corrected factorisation
`ζ_L(s) = (∏_χ L_χ(s)) · R(s)` and using that `ζ_L(s)` is a positive real gives
`log ζ_L(s) = Σ_χ log‖L_χ(s)‖ + log‖R(s)‖`. Since the ramified correction `‖R(s)‖` is bounded
away from `0` and `∞` near `s ↓ 1` (`log_norm_ramified_factor_bounded`), the gap between
`log ζ_L(s).re` and `Σ_χ log‖L_χ(s)‖` is `O(1)`. This `O(1)` slack is harmless for the pole-order
contradiction in `artinLSeries_one_ne_zero`. -/
private theorem log_dedekindZeta_re_sub_sum_log_norm_artinDirichlet_bounded
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      |Real.log (NumberField.dedekindZeta L (s : ℂ)).re -
        ∑ χ : galoisCharacter K L, Real.log ‖artinDirichletSeries K L χ (s : ℂ)‖| ≤ C := by
  obtain ⟨C, hC⟩ := log_norm_ramified_factor_bounded K L
  refine ⟨C, ?_⟩
  filter_upwards [hC, self_mem_nhdsWithin] with s hCs hs1
  simp only [mem_Ioi] at hs1
  have hs' : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs1
  have hpos : 0 < (NumberField.dedekindZeta L (s : ℂ)).re :=
    (show 0 < (NumberField.dedekindZeta L (s : ℂ)).re from by
      have hs1' : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs1
      set g : ℕ → ℝ := fun n ↦ (idealNormMultiplicity L n : ℝ) * (n : ℝ) ^ (-s) with hg
      have key : ∀ n : ℕ,
          (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) = ((g n : ℝ) : ℂ) := by
        intro n
        have hcast : ((n : ℝ) ^ (-s) : ℝ) = ((n : ℂ) ^ (-(s : ℂ))) := by
          rw [Complex.ofReal_cpow (Nat.cast_nonneg n) (-s)]
          norm_cast
        rw [hg]
        push_cast [hcast]
        ring
      have hsumC : Summable
          fun n : ℕ ↦ (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) :=
        ((show Summable fun n : ℕ ↦ ‖(idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-(s : ℂ))‖ from by
          have hcondition : 1 < ((s : ℂ)).re := hs1'
          classical
          have hbig : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (idealNormMultiplicity L k : ℝ))
              =O[Filter.atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ)) := by
            classical
            have h_finite : ∀ (b : ℕ), {I : NonzeroIdeal L | Ideal.absNorm I.1 = b}.Finite := fun b ↦
              Set.Finite.preimage (f := fun I : NonzeroIdeal L ↦ I.1) (fun _ _ _ _ ↦ Subtype.ext)
                (Ideal.finite_setOf_absNorm_eq (S := 𝓞 L) b)
            have h_sum_card : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, idealNormMultiplicity L k =
                Nat.card {I : NonzeroIdeal L // Ideal.absNorm I.1 ≤ n} := fun n ↦ by
              have key := Finset.card_preimage_eq_sum_card_image_eq (f := fun I : NonzeroIdeal L ↦
                Ideal.absNorm I.1) (s := Finset.Icc 1 n) (fun b _ ↦ h_finite b)
              rw [show ((fun I : NonzeroIdeal L ↦ Ideal.absNorm I.1) ⁻¹' ↑(Finset.Icc 1 n)) =
                  {I : NonzeroIdeal L | Ideal.absNorm I.1 ≤ n} by
                ext ⟨I, hI⟩
                simp only [Set.mem_preimage, Finset.coe_Icc, Set.mem_Icc, Set.mem_setOf_eq]
                exact ⟨fun h ↦ h.2, fun h ↦
                  ⟨Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp hI), h⟩⟩] at key
              exact key.symm
            have h_card_bridge : ∀ n : ℕ,
                Nat.card {I : NonzeroIdeal L // Ideal.absNorm I.1 ≤ n} =
                Nat.card {I : (Ideal (𝓞 L))⁰ // ((Ideal.absNorm I.1 : ℕ) : ℝ) ≤ (n : ℝ)} :=
              fun n ↦ Nat.card_congr
                { toFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
                    ⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩, by exact_mod_cast hn⟩
                  invFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
                    ⟨⟨I, mem_nonZeroDivisors_iff_ne_zero.mp hI⟩, by exact_mod_cast hn⟩
                  left_inv := fun _ ↦ rfl
                  right_inv := fun _ ↦ rfl }
            refine Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
              (((NumberField.Ideal.tendsto_norm_le_div_atTop₀ L).comp
                tendsto_natCast_atTop_atTop).congr' ?_)
            filter_upwards with n
            simp only [Function.comp_apply, Real.rpow_one]
            rw [← Nat.cast_sum, h_sum_card n, h_card_bridge n]
            push_cast
            rfl
          have h_lss : LSeriesSummable (fun n : ℕ ↦ ((idealNormMultiplicity L n : ℝ) : ℂ)) s :=
            LSeriesSummable_of_sum_norm_bigO_and_nonneg
              (f := fun n ↦ (idealNormMultiplicity L n : ℝ))
              hbig (fun _ ↦ Nat.cast_nonneg _) zero_le_one
              (by exact_mod_cast hcondition)
          have h_term_eq : LSeries.term (fun n : ℕ ↦ ((idealNormMultiplicity L n : ℝ) : ℂ)) (s : ℂ) =
              fun n ↦ (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) := by
            funext n
            simp only [LSeries.term]
            split_ifs with hn
            · subst hn
              have hzero : idealNormMultiplicity L 0 = 0 := by
                  unfold idealNormMultiplicity
                  rw [Nat.card_eq_zero]
                  exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩
              simp [hzero]
            · simp [Complex.cpow_neg, div_eq_mul_inv]
          exact (h_term_eq ▸ h_lss :
            Summable fun n ↦ (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-(s : ℂ))).norm)).of_norm
      have hsumR : Summable g := Complex.summable_ofReal.mp (by simpa only [key] using hsumC)
      have hre : (NumberField.dedekindZeta L (s : ℂ)).re = ∑' n : ℕ, g n := by
        rw [(show NumberField.dedekindZeta L (s : ℂ) = ∑' n : ℕ, (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) from by
          have hcondition : 1 < ((s : ℂ)).re := hs1'
          unfold NumberField.dedekindZeta LSeries
          refine tsum_congr fun n ↦ ?_
          unfold LSeries.term
          rcases Nat.eq_zero_or_pos n with rfl | hn
          · have hs0 : (s : ℂ) ≠ 0 := by
              intro hzero
              have hre := congrArg Complex.re hzero
              simp only [Complex.zero_re] at hre
              rw [hre] at hcondition
              norm_num at hcondition
            have hzero : idealNormMultiplicity L 0 = 0 := by
                unfold idealNormMultiplicity
                rw [Nat.card_eq_zero]
                exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩
            simp [hzero, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
          · simp only [hn.ne', ↓reduceIte]
            rw [Complex.cpow_neg, div_eq_mul_inv]
            congr 1
            unfold idealNormMultiplicity
            have hequiv : {I : Ideal (𝓞 L) // Ideal.absNorm I = n} ≃
                {I : NonzeroIdeal L // Ideal.absNorm I.1 = n} := by
              refine {
                toFun := fun ⟨I, hI⟩ ↦ ⟨⟨I, ?_⟩, hI⟩
                invFun := fun ⟨⟨I, _⟩, hI⟩ ↦ ⟨I, hI⟩
                left_inv := fun _ ↦ rfl
                right_inv := fun _ ↦ rfl }
              intro h
              rw [h, Ideal.absNorm_bot] at hI
              lia
            exact_mod_cast Nat.card_congr hequiv)]
        simp_rw [key]
        rw [Complex.re_tsum (by simpa only [key] using hsumC)]
        simp
      rw [hre]
      refine hsumR.tsum_pos (fun n ↦ ?_) 1 ?_
      · exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      · rw [hg]
        have hone : idealNormMultiplicity L 1 = 1 := by
          unfold idealNormMultiplicity
          have : Unique {I : NonzeroIdeal L // Ideal.absNorm I.1 = 1} :=
            { default := ⟨⟨⊤, by simp⟩, Ideal.absNorm_top⟩
              uniq := fun ⟨⟨I, hI⟩, hnorm⟩ ↦
                Subtype.ext (Subtype.ext (Ideal.absNorm_eq_one_iff.mp hnorm)) }
          exact Nat.card_unique
        simp [hone])
  have hfact : NumberField.dedekindZeta L (s : ℂ) =
      (∏ χ : galoisCharacter K L, artinDirichletSeries K L χ (s : ℂ)) *
        ∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
            ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-(s : ℂ)))⁻¹ := by
    rw [dedekindZeta_eq_prod_artinDirichletSeries K L hs', tprod_fintype]
  have hnorm : ‖NumberField.dedekindZeta L (s : ℂ)‖ = (NumberField.dedekindZeta L (s : ℂ)).re := by
    rw [(show ∀ {s : ℝ} (hs : 1 < s), (NumberField.dedekindZeta L (s : ℂ) = ((NumberField.dedekindZeta L (s : ℂ)).re : ℂ)) from by
      intro s hs
      classical
      have hs' : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs
      set g : ℕ → ℝ := fun n ↦ (idealNormMultiplicity L n : ℝ) * (n : ℝ) ^ (-s) with hg
      have key : ∀ n : ℕ,
          (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) = ((g n : ℝ) : ℂ) := by
        intro n
        have hcast : ((n : ℝ) ^ (-s) : ℝ) = ((n : ℂ) ^ (-(s : ℂ))) := by
          rw [Complex.ofReal_cpow (Nat.cast_nonneg n) (-s)]; norm_cast
        rw [hg]; push_cast [hcast]; ring
      have hval : NumberField.dedekindZeta L (s : ℂ) = ((∑' n, g n : ℝ) : ℂ) := by
        rw [(show NumberField.dedekindZeta L (s : ℂ) = ∑' n : ℕ, (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) from by
          have hcondition : 1 < ((s : ℂ)).re := hs'
          unfold NumberField.dedekindZeta LSeries
          refine tsum_congr fun n ↦ ?_
          unfold LSeries.term
          rcases Nat.eq_zero_or_pos n with rfl | hn
          · have hs0 : (s : ℂ) ≠ 0 := by
              intro hzero
              have hre := congrArg Complex.re hzero
              simp only [Complex.zero_re] at hre
              rw [hre] at hcondition
              norm_num at hcondition
            have hzero : idealNormMultiplicity L 0 = 0 := by
                unfold idealNormMultiplicity
                rw [Nat.card_eq_zero]
                exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩
            simp [hzero, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
          · simp only [hn.ne', ↓reduceIte]
            rw [Complex.cpow_neg, div_eq_mul_inv]
            congr 1
            unfold idealNormMultiplicity
            have hequiv : {I : Ideal (𝓞 L) // Ideal.absNorm I = n} ≃
                {I : NonzeroIdeal L // Ideal.absNorm I.1 = n} := by
              refine {
                toFun := fun ⟨I, hI⟩ ↦ ⟨⟨I, ?_⟩, hI⟩
                invFun := fun ⟨⟨I, _⟩, hI⟩ ↦ ⟨I, hI⟩
                left_inv := fun _ ↦ rfl
                right_inv := fun _ ↦ rfl }
              intro h
              rw [h, Ideal.absNorm_bot] at hI
              lia
            exact_mod_cast Nat.card_congr hequiv), Complex.ofReal_tsum]
        exact tsum_congr key
      rw [hval, Complex.ofReal_re]) hs1, Complex.norm_real, Real.norm_of_nonneg hpos.le,
      Complex.ofReal_re]
  have hprodχ_ne : (∏ χ : galoisCharacter K L, artinDirichletSeries K L χ (s : ℂ)) ≠ 0 := fun h0 ↦
    hpos.ne' (by rw [hfact, h0, zero_mul, Complex.zero_re])
  have hR_ne : (∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-(s : ℂ)))⁻¹) ≠ 0 :=
    fun h0 ↦ hpos.ne' (by rw [hfact, h0, mul_zero, Complex.zero_re])
  have hχ_ne : ∀ χ ∈ (Finset.univ : Finset (galoisCharacter K L)),
      ‖artinDirichletSeries K L χ (s : ℂ)‖ ≠ 0 := fun χ _ ↦
    norm_ne_zero_iff.mpr fun hχ0 ↦ hprodχ_ne (Finset.prod_eq_zero (Finset.mem_univ χ) hχ0)
  have hsplit : Real.log (NumberField.dedekindZeta L (s : ℂ)).re =
      (∑ χ : galoisCharacter K L, Real.log ‖artinDirichletSeries K L χ (s : ℂ)‖) +
        Real.log ‖∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
          ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-(s : ℂ)))⁻¹‖ := by
    rw [← hnorm, hfact, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr hprodχ_ne) (norm_ne_zero_iff.mpr hR_ne),
      norm_prod, Real.log_prod hχ_ne]
  rw [hsplit]
  simpa using hCs

open Filter Topology Set in
/-- **Assembly helper (ii).** For a nontrivial character `χ'`, the L-series `L_{χ'}` extends
analytically across `s = 1` (`artinLSeries_analytic_extension`, the LF4 leaf), hence `‖L_{χ'}(s)‖`
is bounded above on a right neighbourhood of `s = 1`. (Here `L_{χ'}(s) = artinDirichletSeries`,
which agrees with the analytic extension on `Re s > 1`.) -/
private theorem artinDirichletSeries_norm_le_of_ne_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2) (χ' : galoisCharacter K L) (hχ' : χ' ≠ 1) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), ‖artinDirichletSeries K L χ' (s : ℂ)‖ ≤ C := by
  obtain ⟨Lf', hLf'_an, hLf'_eq⟩ := artinLSeries_analytic_extension K L m hm χ' hχ'
  have hcont : ContinuousAt Lf' 1 :=
    ((show ∀ {Lf : ℂ → ℂ} (hLf : AnalyticOn ℂ Lf {s : ℂ | 1 - (Module.finrank ℚ K : ℝ)⁻¹ < s.re}), (AnalyticAt ℂ Lf 1) from by
      intro Lf hLf
      classical
      have hmem : (1 : ℂ) ∈ {s : ℂ | 1 - (Module.finrank ℚ K : ℝ)⁻¹ < s.re} := by
        have hdpos : (0 : ℝ) < (Module.finrank ℚ K : ℝ)⁻¹ := by
          have : 0 < Module.finrank ℚ K := Module.finrank_pos
          positivity
        simp only [Set.mem_setOf_eq, Complex.one_re]; linarith
      exact hLf.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hmem)) hLf'_an).continuousAt
  have hmap : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 1).comp nhdsWithin_le_nhds
  have hbdd : ∀ᶠ z in 𝓝 (1 : ℂ), ‖Lf' z‖ ≤ ‖Lf' 1‖ + 1 := by
    filter_upwards [hcont.norm.eventually (Metric.ball_mem_nhds ‖Lf' 1‖ one_pos)] with z hz
    rw [Real.dist_eq] at hz
    linarith [(abs_lt.mp hz).2]
  refine ⟨‖Lf' 1‖ + 1, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hmap.eventually hbdd] with s hs1 hbdd_s
  simp only [mem_Ioi] at hs1
  have heq : artinDirichletSeries K L χ' (s : ℂ) = Lf' (s : ℂ) := by
    rw [artinDirichletSeries, ← hLf'_eq (s : ℂ) (by simpa using hs1)]
  rwa [heq]

open Filter Topology Set in
/-- **Assembly helper (i).** The trivial-character L-series `L_1(s) = artinDirichletSeries K L 1 s`
is bounded above by the simple-pole asymptotic of `ζ_K`:
`log‖L_1(s)‖ ≤ log(1/(s-1)) + C` near `s ↓ 1`.

`L_1(s) = ∑'_{𝔞} χ̃_1(𝔞) N𝔞^{-s}` with `‖χ̃_1(𝔞)‖ ≤ 1` by the character-product norm bound, so
termwise `‖χ̃_1(𝔞) N𝔞^{-s}‖ ≤ N𝔞^{-s}` and hence `‖L_1(s)‖ ≤ ∑'_{𝔞} N𝔞^{-s} = ζ_K(s)`
(the ideal-norm sum reindexing for `K`). For real `s > 1`, `ζ_K(s) ≥ 1` (the unit-ideal term),
so `0 ≤ log ζ_K(s)` and `log ‖L_1(s)‖ ≤ log ζ_K(s) ≤ log(1/(s-1)) + C`
by the native simple-pole limit for `K`. -/
private theorem log_norm_artinDirichletSeries_one_le
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [_hAb : IsMulCommutative Gal(L/K)] :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      Real.log ‖artinDirichletSeries K L 1 (s : ℂ)‖ ≤ Real.log (1 / (s - 1)) + C := by
  obtain ⟨C, hC⟩ := (show ∃ C : ℝ, ∀ᶠ (s : ℝ) in 𝓝[>] (1 : ℝ),
      |Real.log (dedekindZeta K (s : ℂ)).re - Real.log (1 / (s - 1))| ≤ C from by
    set r := dedekindZeta_residue K
    have hrpos : 0 < r := dedekindZeta_residue_pos K
    have hF : Tendsto (fun s : ℝ ↦ (s - 1) * (dedekindZeta K (s : ℂ)).re)
        (𝓝[>] (1 : ℝ)) (𝓝 r) := by
      refine ((Complex.continuous_re.tendsto _).comp
        (tendsto_sub_one_mul_dedekindZeta_nhdsGT K)).congr fun s ↦ ?_
      rw [Function.comp_apply, show ((s : ℂ) - 1) = ((s - 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.re_ofReal_mul]
    refine ⟨max |Real.log (r / 2)| |Real.log (2 * r)|, ?_⟩
    have hev : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
        (s - 1) * (dedekindZeta K (s : ℂ)).re ∈ Ioo (r / 2) (2 * r) :=
      hF.eventually (Ioo_mem_nhds (by linarith) (by linarith))
    filter_upwards [hev, self_mem_nhdsWithin] with s hF_s hs1
    simp only [mem_Ioi] at hs1
    have hsm1 : (0 : ℝ) < s - 1 := by linarith
    obtain ⟨hlo, hhi⟩ := hF_s
    have hFpos : (0 : ℝ) < (s - 1) * (dedekindZeta K (s : ℂ)).re := by linarith
    have hζpos : (0 : ℝ) < (dedekindZeta K (s : ℂ)).re := (mul_pos_iff_of_pos_left hsm1).mp hFpos
    rw [one_div, Real.log_inv, sub_neg_eq_add,
      ← Real.log_mul hζpos.ne' hsm1.ne', mul_comm]
    exact abs_le_max_abs_abs (Real.log_lt_log (by linarith) hlo).le (Real.log_lt_log hFpos hhi).le)
  refine ⟨C, ?_⟩
  filter_upwards [hC, self_mem_nhdsWithin] with s hCs hs1
  simp only [mem_Ioi] at hs1
  have hs' : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs1
  have hζ := (show HasSum (fun I : NonzeroIdeal K ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))) (NumberField.dedekindZeta K (s : ℂ)) from by
    have hcondition : 1 < ((s : ℂ)).re := hs'
    classical
    haveI (n : ℕ) : Finite {I : NonzeroIdeal K // Ideal.absNorm I.1 = n} :=
      Set.Finite.to_subtype <| Set.Finite.of_finite_image (f := fun I : NonzeroIdeal K ↦ I.1)
        ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).subset (by rintro _ ⟨⟨I, _⟩, rfl, rfl⟩; rfl))
        (fun _ _ _ _ ↦ Subtype.ext)
    have hseries : Summable fun n : ℕ ↦ ‖(idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-(s : ℂ))‖ := by
      classical
      have hbig : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (idealNormMultiplicity K k : ℝ))
          =O[Filter.atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ)) := by
        classical
        have h_finite : ∀ (b : ℕ), {I : NonzeroIdeal K | Ideal.absNorm I.1 = b}.Finite := fun b ↦
          Set.Finite.preimage (f := fun I : NonzeroIdeal K ↦ I.1) (fun _ _ _ _ ↦ Subtype.ext)
            (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) b)
        have h_sum_card : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, idealNormMultiplicity K k =
            Nat.card {I : NonzeroIdeal K // Ideal.absNorm I.1 ≤ n} := fun n ↦ by
          have key := Finset.card_preimage_eq_sum_card_image_eq (f := fun I : NonzeroIdeal K ↦
            Ideal.absNorm I.1) (s := Finset.Icc 1 n) (fun b _ ↦ h_finite b)
          rw [show ((fun I : NonzeroIdeal K ↦ Ideal.absNorm I.1) ⁻¹' ↑(Finset.Icc 1 n)) =
              {I : NonzeroIdeal K | Ideal.absNorm I.1 ≤ n} by
            ext ⟨I, hI⟩
            simp only [Set.mem_preimage, Finset.coe_Icc, Set.mem_Icc, Set.mem_setOf_eq]
            exact ⟨fun h ↦ h.2, fun h ↦
              ⟨Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp hI), h⟩⟩] at key
          exact key.symm
        have h_card_bridge : ∀ n : ℕ,
            Nat.card {I : NonzeroIdeal K // Ideal.absNorm I.1 ≤ n} =
            Nat.card {I : (Ideal (𝓞 K))⁰ // ((Ideal.absNorm I.1 : ℕ) : ℝ) ≤ (n : ℝ)} :=
          fun n ↦ Nat.card_congr
            { toFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
                ⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩, by exact_mod_cast hn⟩
              invFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
                ⟨⟨I, mem_nonZeroDivisors_iff_ne_zero.mp hI⟩, by exact_mod_cast hn⟩
              left_inv := fun _ ↦ rfl
              right_inv := fun _ ↦ rfl }
        refine Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
          (((NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp
            tendsto_natCast_atTop_atTop).congr' ?_)
        filter_upwards with n
        simp only [Function.comp_apply, Real.rpow_one]
        rw [← Nat.cast_sum, h_sum_card n, h_card_bridge n]
        push_cast
        rfl
      have h_lss : LSeriesSummable (fun n : ℕ ↦ ((idealNormMultiplicity K n : ℝ) : ℂ)) s :=
        LSeriesSummable_of_sum_norm_bigO_and_nonneg
          (f := fun n ↦ (idealNormMultiplicity K n : ℝ))
          hbig (fun _ ↦ Nat.cast_nonneg _) zero_le_one
          (by exact_mod_cast hcondition)
      have h_term_eq : LSeries.term (fun n : ℕ ↦ ((idealNormMultiplicity K n : ℝ) : ℂ)) (s : ℂ) =
          fun n ↦ (idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) := by
        funext n
        simp only [LSeries.term]
        split_ifs with hn
        · subst hn
          have hzero : idealNormMultiplicity K 0 = 0 := by
              unfold idealNormMultiplicity
              rw [Nat.card_eq_zero]
              exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩
          simp [hzero]
        · simp [Complex.cpow_neg, div_eq_mul_inv]
      exact (h_term_eq ▸ h_lss :
        Summable fun n ↦ (idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-(s : ℂ))).norm
    have hzeta : NumberField.dedekindZeta K (s : ℂ) =
        ∑' n : ℕ, (idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) := by
      unfold NumberField.dedekindZeta LSeries
      refine tsum_congr fun n ↦ ?_
      unfold LSeries.term
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · have hs0 : (s : ℂ) ≠ 0 := by
          intro hzero
          have hre := congrArg Complex.re hzero
          simp only [Complex.zero_re] at hre
          rw [hre] at hcondition
          norm_num at hcondition
        have hzero : idealNormMultiplicity K 0 = 0 := by
            unfold idealNormMultiplicity
            rw [Nat.card_eq_zero]
            exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩
        simp [hzero, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
      · simp only [hn.ne', ↓reduceIte]
        rw [Complex.cpow_neg, div_eq_mul_inv]
        congr 1
        unfold idealNormMultiplicity
        have hequiv : {I : Ideal (𝓞 K) // Ideal.absNorm I = n} ≃
            {I : NonzeroIdeal K // Ideal.absNorm I.1 = n} := by
          refine {
            toFun := fun ⟨I, hI⟩ ↦ ⟨⟨I, ?_⟩, hI⟩
            invFun := fun ⟨⟨I, _⟩, hI⟩ ↦ ⟨I, hI⟩
            left_inv := fun _ ↦ rfl
            right_inv := fun _ ↦ rfl }
          intro h
          rw [h, Ideal.absNorm_bot] at hI
          lia
        exact_mod_cast Nat.card_congr hequiv
    set e := Equiv.sigmaFiberEquiv (fun I : NonzeroIdeal K ↦ Ideal.absNorm I.1)
    have hval : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n},
        (Ideal.absNorm (y.1).1 : ℂ) ^ (-(s : ℂ))) = (idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) :=
      fun n ↦ by
        rw [show (∑' y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n},
            (Ideal.absNorm y.1.1 : ℂ) ^ (-(s : ℂ))) = idealNormMultiplicity K n • (n : ℂ) ^ (-(s : ℂ)) from
          (tsum_congr fun y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n} ↦ by rw [y.2]).trans
            (tsum_const ((n : ℂ) ^ (-(s : ℂ)))), nsmul_eq_mul]
    have hnorm : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n},
        ‖(Ideal.absNorm (y.1).1 : ℂ) ^ (-(s : ℂ))‖) = ‖(idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-(s : ℂ))‖ :=
      fun n ↦ by
        rw [show (∑' y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n},
            ‖(Ideal.absNorm y.1.1 : ℂ) ^ (-(s : ℂ))‖) = idealNormMultiplicity K n • ‖(n : ℂ) ^ (-(s : ℂ))‖ from
          (tsum_congr fun y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n} ↦ by rw [y.2]).trans
            (tsum_const ‖(n : ℂ) ^ (-(s : ℂ))‖), nsmul_eq_mul, norm_mul,
          Complex.norm_natCast]
    have hsummable : Summable fun I : NonzeroIdeal K ↦ ‖(Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))‖ := by
      rw [← e.summable_iff]
      refine (summable_sigma_of_nonneg (fun _ ↦ norm_nonneg _)).mpr ⟨fun _ ↦ Summable.of_finite, ?_⟩
      exact hseries.congr fun n ↦ (hnorm n).symm
    have hsummable_sigma : Summable fun p : Σ n, {I : NonzeroIdeal K // Ideal.absNorm I.1 = n} ↦
        (Ideal.absNorm (e p).1 : ℂ) ^ (-(s : ℂ)) :=
      (e.summable_iff (f := fun I : NonzeroIdeal K ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ)))).mpr
        hsummable.of_norm
    have hval_sum : (∑' I : NonzeroIdeal K, (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ)))
        = NumberField.dedekindZeta K s := by
      rw [hzeta,
        ← e.tsum_eq (fun I ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))), hsummable_sigma.tsum_sigma]
      exact tsum_congr hval
    exact hval_sum ▸ hsummable.of_norm.hasSum)
  have hnorm_eq : ∀ 𝔞 : NonzeroIdeal K,
      ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖ = ((Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))).re := by
    intro 𝔞
    have hpos : 0 < Ideal.absNorm 𝔞.1 :=
      Nat.pos_of_ne_zero fun h ↦ 𝔞.2 (Ideal.absNorm_eq_zero_iff.mp h)
    have hcast : (Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ)) =
        (((Ideal.absNorm 𝔞.1 : ℝ) ^ (-s) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (by positivity), Complex.ofReal_natCast]; norm_cast
    rw [hcast, Complex.norm_real, Complex.ofReal_re, Real.norm_of_nonneg (by positivity)]
  have hsum_norm : Summable fun 𝔞 : NonzeroIdeal K ↦ ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖ :=
    hζ.summable.norm
  have hsum_norm_eq : (∑' 𝔞 : NonzeroIdeal K, ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖)
      = (NumberField.dedekindZeta K (s : ℂ)).re := by
    rw [tsum_congr hnorm_eq, ← Complex.re_tsum hζ.summable, hζ.tsum_eq]
  have hterm : ∀ 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥},
      ‖galoisCharacterOnIdeal K L 1 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖ ≤
        ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖ := by
    intro 𝔞
    rw [norm_mul]
    calc ‖galoisCharacterOnIdeal K L 1 𝔞.1‖ * ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖
        ≤ 1 * ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖ := by
          gcongr; exact (show ∀      
              (χ : galoisCharacter K L) (𝔞 : Ideal (𝓞 K)), (‖galoisCharacterOnIdeal K L χ 𝔞‖ ≤ 1) from by
            intro χ 𝔞
            classical
            rw [galoisCharacterOnIdeal, norm_prod]
            refine Finset.prod_le_one₀ (fun i _ ↦ norm_nonneg _) (fun 𝔭 _ ↦ ?_)
            rw [norm_pow]
            by_cases h : UnramifiedIn K L 𝔭
            · have hnorm : ‖(χ (frobeniusClass K L 𝔭).out : ℂ)‖ = 1 :=
                (((Units.coeHom ℂ).comp χ).isOfFinOrder
                  (isOfFinOrder_of_finite (frobeniusClass K L 𝔭).out)).norm_eq_one
              rw [if_pos h, hnorm, one_pow]
            · rw [if_neg h, norm_zero]
              exact zero_pow_le_one _) 1 𝔞.1
      _ = ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖ := one_mul _
  have hsum_term : Summable fun 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥} ↦
      ‖galoisCharacterOnIdeal K L 1 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖ :=
    hsum_norm.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm
  have hL1_le : ‖artinDirichletSeries K L 1 (s : ℂ)‖ ≤ (NumberField.dedekindZeta K (s : ℂ)).re := by
    rw [artinDirichletSeries]
    refine (norm_tsum_le_tsum_norm hsum_term).trans ?_
    rw [← hsum_norm_eq]
    exact Summable.tsum_le_tsum hterm hsum_term hsum_norm
  have hζ_ge1 : (1 : ℝ) ≤ (NumberField.dedekindZeta K (s : ℂ)).re := by
    rw [← hsum_norm_eq]
    refine le_trans ?_ (hsum_norm.le_tsum (⟨⊤, by simp⟩ : NonzeroIdeal K) fun 𝔞 _ ↦ norm_nonneg _)
    rw [Ideal.absNorm_top, Nat.cast_one, Complex.one_cpow, norm_one]
  have hlog_le : Real.log ‖artinDirichletSeries K L 1 (s : ℂ)‖ ≤
      Real.log (NumberField.dedekindZeta K (s : ℂ)).re := by
    rcases eq_or_lt_of_le (norm_nonneg (artinDirichletSeries K L 1 (s : ℂ))) with h0 | h0
    · rw [← h0, Real.log_zero]
      exact Real.log_nonneg hζ_ge1
    · exact Real.log_le_log h0 hL1_le
  exact hlog_le.trans (by linarith [abs_le.mp hCs])

open Classical in
open Classical Filter Topology Set in
/-- **Per-character log bound (Dirichlet's contradiction, assembled over all characters).** Given a
nontrivial `χ` whose χ-factor `L_χ` has an analytic-zero bound `log‖L_χ(s)‖ ≤ -log(1/(s-1)) + Cχ`
near `s ↓ 1`, every character factor `L_{χ'}` satisfies an eventual upper bound of the matching
shape `log‖L_{χ'}(s)‖ ≤ (pole at χ'=1) + (zero at χ'=χ) + C`: the trivial factor is the `ζ_K`-pole
(`log_norm_artinDirichletSeries_one_le`), the `χ`-factor is the supplied zero bound, and every other
factor is `O(1)` via its analytic extension (`artinDirichletSeries_norm_le_of_ne_one`). -/
private theorem log_norm_artinDirichletSeries_le_pole_zero_ite
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2) {χ : galoisCharacter K L} {Cχ : ℝ}
    (hCχ : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      Real.log ‖artinDirichletSeries K L χ (s : ℂ)‖ ≤ -Real.log (1 / (s - 1)) + Cχ)
    (χ' : galoisCharacter K L) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      Real.log ‖artinDirichletSeries K L χ' (s : ℂ)‖ ≤
        (if χ' = 1 then Real.log (1 / (s - 1)) else
          if χ' = χ then -Real.log (1 / (s - 1)) else 0) + C := by
  by_cases h1 : χ' = 1
  · subst h1
    obtain ⟨C1, hC1⟩ := log_norm_artinDirichletSeries_one_le K L
    exact ⟨C1, by filter_upwards [hC1] with s hs; rwa [if_pos rfl]⟩
  · by_cases hc : χ' = χ
    · subst hc
      exact ⟨Cχ, by filter_upwards [hCχ] with s hs; rwa [if_neg h1, if_pos rfl]⟩
    · obtain ⟨C, hC⟩ := artinDirichletSeries_norm_le_of_ne_one K L m hm χ' h1
      refine ⟨Real.log (max C 1), ?_⟩
      filter_upwards [hC] with s hs
      simp only [if_neg h1, if_neg hc, zero_add]
      have hmax1 : (1 : ℝ) ≤ max C 1 := le_max_right _ _
      rcases le_total ‖artinDirichletSeries K L χ' (s : ℂ)‖ 0 with h0 | h0
      · have hz : ‖artinDirichletSeries K L χ' (s : ℂ)‖ = 0 := le_antisymm h0 (norm_nonneg _)
        rw [hz, Real.log_zero]
        exact Real.log_nonneg hmax1
      · rcases eq_or_lt_of_le h0 with h0' | h0'
        · rw [← h0', Real.log_zero]; exact Real.log_nonneg hmax1
        · exact Real.log_le_log h0' (le_trans hs (le_max_left _ _))

/-- For real `s > 1` the χ-factor `L_χ(s) = artinDirichletSeries K L χ s` is nonzero: it is a
factor of the corrected factorisation `ζ_L(s) = (∏_{χ'} L_{χ'}(s)) · R(s)`, and `ζ_L(s)` is a
positive real by the norm-one term in its nonnegative ideal series, so no factor can vanish. -/
private theorem artinDirichletSeries_ne_zero_of_one_lt
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (χ : galoisCharacter K L) {s : ℝ}
    (hs : 1 < s) : artinDirichletSeries K L χ (s : ℂ) ≠ 0 := fun hzero ↦ by
  have hpos : 0 < (NumberField.dedekindZeta L (s : ℂ)).re := (show 0 < (NumberField.dedekindZeta L (s : ℂ)).re from by
    have hs' : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs
    set g : ℕ → ℝ := fun n ↦ (idealNormMultiplicity L n : ℝ) * (n : ℝ) ^ (-s) with hg
    have key : ∀ n : ℕ,
        (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) = ((g n : ℝ) : ℂ) := by
      intro n
      have hcast : ((n : ℝ) ^ (-s) : ℝ) = ((n : ℂ) ^ (-(s : ℂ))) := by
        rw [Complex.ofReal_cpow (Nat.cast_nonneg n) (-s)]
        norm_cast
      rw [hg]
      push_cast [hcast]
      ring
    have hsumC : Summable
        fun n : ℕ ↦ (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) :=
      ((show Summable fun n : ℕ ↦ ‖(idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-(s : ℂ))‖ from by
        have hcondition : 1 < ((s : ℂ)).re := hs'
        classical
        have hbig : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (idealNormMultiplicity L k : ℝ))
            =O[Filter.atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ)) := by
          classical
          have h_finite : ∀ (b : ℕ), {I : NonzeroIdeal L | Ideal.absNorm I.1 = b}.Finite := fun b ↦
            Set.Finite.preimage (f := fun I : NonzeroIdeal L ↦ I.1) (fun _ _ _ _ ↦ Subtype.ext)
              (Ideal.finite_setOf_absNorm_eq (S := 𝓞 L) b)
          have h_sum_card : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, idealNormMultiplicity L k =
              Nat.card {I : NonzeroIdeal L // Ideal.absNorm I.1 ≤ n} := fun n ↦ by
            have key := Finset.card_preimage_eq_sum_card_image_eq (f := fun I : NonzeroIdeal L ↦
              Ideal.absNorm I.1) (s := Finset.Icc 1 n) (fun b _ ↦ h_finite b)
            rw [show ((fun I : NonzeroIdeal L ↦ Ideal.absNorm I.1) ⁻¹' ↑(Finset.Icc 1 n)) =
                {I : NonzeroIdeal L | Ideal.absNorm I.1 ≤ n} by
              ext ⟨I, hI⟩
              simp only [Set.mem_preimage, Finset.coe_Icc, Set.mem_Icc, Set.mem_setOf_eq]
              exact ⟨fun h ↦ h.2, fun h ↦
                ⟨Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp hI), h⟩⟩] at key
            exact key.symm
          have h_card_bridge : ∀ n : ℕ,
              Nat.card {I : NonzeroIdeal L // Ideal.absNorm I.1 ≤ n} =
              Nat.card {I : (Ideal (𝓞 L))⁰ // ((Ideal.absNorm I.1 : ℕ) : ℝ) ≤ (n : ℝ)} :=
            fun n ↦ Nat.card_congr
              { toFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
                  ⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩, by exact_mod_cast hn⟩
                invFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
                  ⟨⟨I, mem_nonZeroDivisors_iff_ne_zero.mp hI⟩, by exact_mod_cast hn⟩
                left_inv := fun _ ↦ rfl
                right_inv := fun _ ↦ rfl }
          refine Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
            (((NumberField.Ideal.tendsto_norm_le_div_atTop₀ L).comp
              tendsto_natCast_atTop_atTop).congr' ?_)
          filter_upwards with n
          simp only [Function.comp_apply, Real.rpow_one]
          rw [← Nat.cast_sum, h_sum_card n, h_card_bridge n]
          push_cast
          rfl
        have h_lss : LSeriesSummable (fun n : ℕ ↦ ((idealNormMultiplicity L n : ℝ) : ℂ)) s :=
          LSeriesSummable_of_sum_norm_bigO_and_nonneg
            (f := fun n ↦ (idealNormMultiplicity L n : ℝ))
            hbig (fun _ ↦ Nat.cast_nonneg _) zero_le_one
            (by exact_mod_cast hcondition)
        have h_term_eq : LSeries.term (fun n : ℕ ↦ ((idealNormMultiplicity L n : ℝ) : ℂ)) (s : ℂ) =
            fun n ↦ (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) := by
          funext n
          simp only [LSeries.term]
          split_ifs with hn
          · subst hn
            have hzero : idealNormMultiplicity L 0 = 0 := by
                unfold idealNormMultiplicity
                rw [Nat.card_eq_zero]
                exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩
            simp [hzero]
          · simp [Complex.cpow_neg, div_eq_mul_inv]
        exact (h_term_eq ▸ h_lss :
          Summable fun n ↦ (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-(s : ℂ))).norm)).of_norm
    have hsumR : Summable g := Complex.summable_ofReal.mp (by simpa only [key] using hsumC)
    have hre : (NumberField.dedekindZeta L (s : ℂ)).re = ∑' n : ℕ, g n := by
      rw [(show NumberField.dedekindZeta L (s : ℂ) = ∑' n : ℕ, (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) from by
        have hcondition : 1 < ((s : ℂ)).re := hs'
        unfold NumberField.dedekindZeta LSeries
        refine tsum_congr fun n ↦ ?_
        unfold LSeries.term
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · have hs0 : (s : ℂ) ≠ 0 := by
            intro hzero
            have hre := congrArg Complex.re hzero
            simp only [Complex.zero_re] at hre
            rw [hre] at hcondition
            norm_num at hcondition
          have hzero : idealNormMultiplicity L 0 = 0 := by
              unfold idealNormMultiplicity
              rw [Nat.card_eq_zero]
              exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩
          simp [hzero, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
        · simp only [hn.ne', ↓reduceIte]
          rw [Complex.cpow_neg, div_eq_mul_inv]
          congr 1
          unfold idealNormMultiplicity
          have hequiv : {I : Ideal (𝓞 L) // Ideal.absNorm I = n} ≃
              {I : NonzeroIdeal L // Ideal.absNorm I.1 = n} := by
            refine {
              toFun := fun ⟨I, hI⟩ ↦ ⟨⟨I, ?_⟩, hI⟩
              invFun := fun ⟨⟨I, _⟩, hI⟩ ↦ ⟨I, hI⟩
              left_inv := fun _ ↦ rfl
              right_inv := fun _ ↦ rfl }
            intro h
            rw [h, Ideal.absNorm_bot] at hI
            lia
          exact_mod_cast Nat.card_congr hequiv)]
      simp_rw [key]
      rw [Complex.re_tsum (by simpa only [key] using hsumC)]
      simp
    rw [hre]
    refine hsumR.tsum_pos (fun n ↦ ?_) 1 ?_
    · exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · rw [hg]
      have hone : idealNormMultiplicity L 1 = 1 := by
        unfold idealNormMultiplicity
        have : Unique {I : NonzeroIdeal L // Ideal.absNorm I.1 = 1} :=
          { default := ⟨⟨⊤, by simp⟩, Ideal.absNorm_top⟩
            uniq := fun ⟨⟨I, hI⟩, hnorm⟩ ↦
              Subtype.ext (Subtype.ext (Ideal.absNorm_eq_one_iff.mp hnorm)) }
        exact Nat.card_unique
      simp [hone])
  have hs' : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs
  rw [show NumberField.dedekindZeta L (s : ℂ) = 0 by
    rw [dedekindZeta_eq_prod_artinDirichletSeries K L hs', tprod_fintype,
      Finset.prod_eq_zero (Finset.mem_univ χ) hzero, zero_mul], Complex.zero_re] at hpos
  exact lt_irrefl 0 hpos

open Classical Filter Topology Set in
/-- **Pole-cancellation contradiction.** If for a nontrivial `χ` every character factor obeys the
ite-bound `log‖L_{χ'}(s)‖ ≤ (pole at χ'=1) + (zero at χ'=χ) + C χ'` near `s ↓ 1`, then summing over
the finite character group cancels the `ζ_K`-pole (χ'=1) against the supposed zero (χ'=χ), leaving
`log ζ_L(s).re` bounded above — contradicting its divergence to `+∞`
by the native simple-pole limit, modulo the ramified `O(1)` slack
`log_dedekindZeta_re_sub_sum_log_norm_artinDirichlet_bounded`. -/
private theorem false_of_eventually_log_norm_le_pole_zero_ite
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] {χ : galoisCharacter K L} (hχ : χ ≠ 1)
    {C : galoisCharacter K L → ℝ} (hC : ∀ χ' : galoisCharacter K L, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      Real.log ‖artinDirichletSeries K L χ' (s : ℂ)‖ ≤
        (if χ' = 1 then Real.log (1 / (s - 1)) else
          if χ' = χ then -Real.log (1 / (s - 1)) else 0) + C χ') : False := by
  obtain ⟨CR, hCR⟩ := log_dedekindZeta_re_sub_sum_log_norm_artinDirichlet_bounded K L
  have hbound : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      Real.log (NumberField.dedekindZeta L (s : ℂ)).re ≤ (∑ χ', C χ') + CR := by
    filter_upwards [Filter.eventually_all.2 hC, hCR] with s hs_all hCRs
    have hsumle : ∑ χ' : galoisCharacter K L, Real.log ‖artinDirichletSeries K L χ' (s : ℂ)‖
        ≤ ∑ χ', C χ' := by
      calc ∑ χ' : galoisCharacter K L, Real.log ‖artinDirichletSeries K L χ' (s : ℂ)‖
          ≤ ∑ χ' : galoisCharacter K L,
              ((if χ' = 1 then Real.log (1 / (s - 1)) else
                if χ' = χ then -Real.log (1 / (s - 1)) else 0) + C χ') :=
            Finset.sum_le_sum fun χ' _ ↦ hs_all χ'
        _ = ∑ χ' : galoisCharacter K L, C χ' := by
            rw [Finset.sum_add_distrib, (show ∀ [FiniteDimensional K L] {χ : galoisCharacter K L} (hχ : χ ≠ 1) (a : ℝ), (∑ χ' : galoisCharacter K L, (if χ' = 1 then a else if χ' = χ then -a else 0) = 0) from by
              intro zetaInstance0 χ hχ a
              classical
              have hsplit : ∀ χ' : galoisCharacter K L,
                  (if χ' = 1 then a else if χ' = χ then -a else 0) =
                    (if χ' = 1 then a else 0) + (if χ' = χ then -a else 0) := fun χ' ↦ by
                by_cases h1 : χ' = 1
                · rw [if_pos h1, if_pos h1, if_neg (h1 ▸ Ne.symm hχ), add_zero]
                · rw [if_neg h1, if_neg h1]; by_cases hc : χ' = χ <;> simp [hc]
              rw [Finset.sum_congr rfl fun χ' _ ↦ hsplit χ', Finset.sum_add_distrib,
                Finset.sum_ite_eq' Finset.univ (1 : galoisCharacter K L), Finset.sum_ite_eq' Finset.univ χ]
              simp) hχ (Real.log (1 / (s - 1))),
              zero_add]
    have := abs_le.mp hCRs
    linarith [this.1, this.2]
  obtain ⟨s, hge, hle⟩ :=
    ((((show Tendsto (fun s : ℝ ↦ Real.log (NumberField.dedekindZeta L (s : ℂ)).re)
      (𝓝[>] (1 : ℝ)) atTop from by
      obtain ⟨C, hC⟩ := (show ∃ C : ℝ, ∀ᶠ (s : ℝ) in 𝓝[>] (1 : ℝ),
          |Real.log (dedekindZeta L (s : ℂ)).re - Real.log (1 / (s - 1))| ≤ C from by
        set r := dedekindZeta_residue L
        have hrpos : 0 < r := dedekindZeta_residue_pos L
        have hF : Tendsto (fun s : ℝ ↦ (s - 1) * (dedekindZeta L (s : ℂ)).re)
            (𝓝[>] (1 : ℝ)) (𝓝 r) := by
          refine ((Complex.continuous_re.tendsto _).comp
            (tendsto_sub_one_mul_dedekindZeta_nhdsGT L)).congr fun s ↦ ?_
          rw [Function.comp_apply, show ((s : ℂ) - 1) = ((s - 1 : ℝ) : ℂ) by push_cast; ring,
            Complex.re_ofReal_mul]
        refine ⟨max |Real.log (r / 2)| |Real.log (2 * r)|, ?_⟩
        have hev : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
            (s - 1) * (dedekindZeta L (s : ℂ)).re ∈ Ioo (r / 2) (2 * r) :=
          hF.eventually (Ioo_mem_nhds (by linarith) (by linarith))
        filter_upwards [hev, self_mem_nhdsWithin] with s hF_s hs1
        simp only [mem_Ioi] at hs1
        have hsm1 : (0 : ℝ) < s - 1 := by linarith
        obtain ⟨hlo, hhi⟩ := hF_s
        have hFpos : (0 : ℝ) < (s - 1) * (dedekindZeta L (s : ℂ)).re := by linarith
        have hζpos : (0 : ℝ) < (dedekindZeta L (s : ℂ)).re := (mul_pos_iff_of_pos_left hsm1).mp hFpos
        rw [one_div, Real.log_inv, sub_neg_eq_add,
          ← Real.log_mul hζpos.ne' hsm1.ne', mul_comm]
        exact abs_le_max_abs_abs (Real.log_lt_log (by linarith) hlo).le (Real.log_lt_log hFpos hhi).le)
      have hL : Tendsto (fun s : ℝ ↦ Real.log (1 / (s - 1))) (𝓝[>] (1 : ℝ)) atTop := by
        refine Real.tendsto_log_atTop.comp ?_
        have h1 : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) :=
          tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
            (((continuous_sub_right 1).tendsto' 1 0 (by ring)).mono_left nhdsWithin_le_nhds)
            (eventually_nhdsWithin_of_forall fun s hs ↦ by
              simp only [Set.mem_Ioi] at hs ⊢
              linarith)
        simpa only [one_div] using! h1.inv_tendsto_nhdsGT_zero
      have hlog : Tendsto (fun s : ℝ ↦ Real.log (1 / (s - 1)) + -C) (𝓝[>] (1 : ℝ)) atTop :=
        hL.atTop_add tendsto_const_nhds
      refine tendsto_atTop_mono' _ ?_ hlog
      filter_upwards [hC] with s hs
      linarith [(abs_le.mp hs).1])).eventually_ge_atTop ((∑ χ', C χ') + CR + 1)).and
      hbound).exists
  linarith

open Filter Topology Set in
/-- Sharifi 7.1.19 step 2 (p. 142): non-vanishing of `L(χ,1)` for
nontrivial `χ`. Source argument: if any `L(χ,1) = 0`, the
`log ζ_L = Σ_χ log L(χ,·)` decomposition leads to a sub-asymptotic
strictly weaker than the simple pole `log ζ_L ~ log(1/(s-1))`, a
contradiction. Uses `artinLSeries_analytic_extension` so that
"`L(χ, 1)` is defined" makes sense — the extension brings `s = 1` into
the analyticity domain.

**Stated at cyclotomic generality** (`L = K(μ_m)`): the proof bounds every other nontrivial
factor `L_{χ'}` near `s = 1` via its analytic extension
(`artinDirichletSeries_norm_le_of_ne_one` ⟸ `artinLSeries_analytic_extension`), which — like
the geometry-of-numbers leaf it rests on — is CFT-free only cyclotomically (see the restatement
note on `exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow`, expert review 2026-06-05). -/
theorem artinLSeries_one_ne_zero
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2) (χ : galoisCharacter K L) (_hχ : χ ≠ 1) :
    ∀ Lf : ℂ → ℂ,
      AnalyticOn ℂ Lf {s : ℂ | 1 - (Module.finrank ℚ K : ℝ)⁻¹ < s.re} →
      (∀ s : ℂ, 1 < s.re →
        Lf s = ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥},
          galoisCharacterOnIdeal K L χ 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s)) →
      Lf 1 ≠ 0 := by
  classical
  intro Lf hLf_an hLf_eq hLf0
  have hLf_eq' : ∀ s : ℂ, 1 < s.re → Lf s = artinDirichletSeries K L χ s :=
    fun s hs ↦ by rw [hLf_eq s hs, artinDirichletSeries]
  have hLf_at : AnalyticAt ℂ Lf 1 := (show ∀ {Lf : ℂ → ℂ} (hLf : AnalyticOn ℂ Lf {s : ℂ | 1 - (Module.finrank ℚ K : ℝ)⁻¹ < s.re}), (AnalyticAt ℂ Lf 1) from by
    intro Lf hLf
    classical
    have hmem : (1 : ℂ) ∈ {s : ℂ | 1 - (Module.finrank ℚ K : ℝ)⁻¹ < s.re} := by
      have hdpos : (0 : ℝ) < (Module.finrank ℚ K : ℝ)⁻¹ := by
        have : 0 < Module.finrank ℚ K := Module.finrank_pos
        positivity
      simp only [Set.mem_setOf_eq, Complex.one_re]; linarith
    exact hLf.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hmem)) hLf_an
  have hmap : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 1).comp nhdsWithin_le_nhds
  have hLf_ne : ¬ ∀ᶠ z in 𝓝 (1 : ℂ), Lf z = 0 := by
    intro hloc
    obtain ⟨s, hs0, hs1⟩ : ∃ s : ℝ, Lf (s : ℂ) = 0 ∧ 1 < s :=
      ((hmap.eventually hloc).and self_mem_nhdsWithin).exists
    exact artinDirichletSeries_ne_zero_of_one_lt K L χ hs1
      (by rw [← hLf_eq' _ (by simpa using hs1), hs0])
  obtain ⟨Cχ, hCχ⟩ := (show ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      Real.log ‖Lf (s : ℂ)‖ ≤ -Real.log (1 / (s - 1)) + C from by
    obtain ⟨n, g, hg_an, hg_ne, hg_eq⟩ :=
      (AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff hLf_at).mpr hLf_ne
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · refine absurd ?_ hg_ne
        have := hg_eq.self_of_nhds
        rw [pow_zero, one_smul] at this
        rw [← this, hLf0]
      · exact h
    have hg_cont : ContinuousAt g 1 := hg_an.continuousAt
    have hCg : ∀ᶠ z in 𝓝 (1 : ℂ), ‖g z‖ ≤ ‖g 1‖ + 1 := by
      filter_upwards [hg_cont.norm.eventually (Metric.ball_mem_nhds ‖g 1‖ one_pos)] with z hz
      rw [Real.dist_eq] at hz
      linarith [(abs_lt.mp hz).2]
    have hg0 : ∀ᶠ z in 𝓝 (1 : ℂ), g z ≠ 0 := hg_cont.eventually_ne hg_ne
    refine ⟨‖g 1‖ + 1, ?_⟩
    have hmap : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 1).comp nhdsWithin_le_nhds
    have hIoo : Set.Ioo (1 : ℝ) 2 ∈ 𝓝[>] (1 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [hmap.eventually hg_eq, hmap.eventually hCg, hmap.eventually hg0, hIoo]
      with s hfeq hgle hgne hsmem
    obtain ⟨hs1, hs2⟩ := hsmem
    have hpos : (0 : ℝ) < s - 1 := by linarith
    have hlt1 : s - 1 < 1 := by linarith
    have hgpos : (0 : ℝ) < ‖g (s : ℂ)‖ := norm_pos_iff.mpr hgne
    have hnorm : ‖Lf (s : ℂ)‖ = (s - 1) ^ n * ‖g (s : ℂ)‖ := by
      rw [hfeq, norm_smul, norm_pow]
      congr 2
      rw [show ((s : ℂ) - 1) = (((s - 1 : ℝ)) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg hpos.le]
    rw [hnorm, Real.log_mul (by positivity) hgpos.ne', Real.log_pow]
    have hlog_neg : Real.log (s - 1) < 0 := Real.log_neg hpos hlt1
    have hn_ge : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hn_step : (n : ℝ) * Real.log (s - 1) ≤ Real.log (s - 1) := by
      nlinarith [hn_ge, hlog_neg]
    have hloginv : -Real.log (1 / (s - 1)) = Real.log (s - 1) := by
      rw [one_div, Real.log_inv, neg_neg]
    rw [hloginv]
    have hgle' : Real.log ‖g (s : ℂ)‖ ≤ ‖g 1‖ + 1 := by
      calc Real.log ‖g (s : ℂ)‖ ≤ Real.log (‖g 1‖ + 1) :=
            Real.log_le_log hgpos hgle
        _ ≤ ‖g 1‖ + 1 := Real.log_le_self (by positivity)
    linarith)
  have hCχ' : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      Real.log ‖artinDirichletSeries K L χ (s : ℂ)‖ ≤ -Real.log (1 / (s - 1)) + Cχ := by
    filter_upwards [hCχ, self_mem_nhdsWithin] with s hs hs1
    simp only [mem_Ioi] at hs1
    rwa [← hLf_eq' (s : ℂ) (by simpa using hs1)]
  choose C hC using log_norm_artinDirichletSeries_le_pole_zero_ite K L m hm hCχ'
  exact false_of_eventually_log_norm_le_pole_zero_ite K L _hχ hC

end Chebotarev
