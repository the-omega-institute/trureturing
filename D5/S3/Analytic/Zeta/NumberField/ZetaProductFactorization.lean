/- GID: D5/S3/Analytic/Zeta/NumberField/ZetaProductFactorization
   generality: G
   mirror-B: D5/B/S3/Analytic/Zeta/NumberField/ZetaProductFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The log norm of the ramified Euler correction is bounded near one. -/
module

public import D5.S3.Analytic.Zeta.NumberField.ZetaProductAnalytic

@[expose] public section

noncomputable section

open NumberField

open scoped nonZeroDivisors

namespace Chebotarev

attribute [local instance] Fintype.ofFinite

/-- The Dirichlet series `L_χ(s) = ∑'_{𝔞 ≠ ⊥} χ(𝔞) N𝔞^{-s}` of a Galois character, as a function
of `s`. This is the analytic engine of Sharifi 7.1.16–7.1.19; for `1 < Re s` it equals the Euler
product over unramified primes (`exists_artinLSeries_eulerProduct_abelian`). -/
noncomputable def artinDirichletSeries
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) (s : ℂ) : ℂ :=
  ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥},
    galoisCharacterOnIdeal K L χ 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s)

/-- The Euler factor `(1 - N𝔓^{-s})^{-1}` of a nonzero prime `𝔓` of `𝓞 L`, written additively as
`1 + g 𝔓` with `g 𝔓 = (1 - N𝔓^{-s})^{-1} - 1`. Its norm is `≤ 2‖N𝔓^{-s}‖`
and `∑_𝔓 ‖N𝔓^{-s}‖` converges (a sub-sum of the absolutely
convergent `ζ_L`). -/
private theorem summable_norm_primeIdeal_factor_sub_one
    (L : Type*) [Field L] [NumberField L] {s : ℂ} (hs : 1 < s.re) :
    Summable fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} ↦
      ‖(1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹ - 1‖ := by
  have hsum : Summable fun 𝔞 : NonzeroIdeal L ↦ ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-s)‖ :=
    ((show HasSum (fun I : NonzeroIdeal L ↦ (Ideal.absNorm I.1 : ℂ) ^ (-s)) (NumberField.dedekindZeta L s) from by
      have hcondition : 1 < (s).re := hs
      classical
      haveI (n : ℕ) : Finite {I : NonzeroIdeal L // Ideal.absNorm I.1 = n} :=
        Set.Finite.to_subtype <| Set.Finite.of_finite_image (f := fun I : NonzeroIdeal L ↦ I.1)
          ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 L) n).subset (by rintro _ ⟨⟨I, _⟩, rfl, rfl⟩; rfl))
          (fun _ _ _ _ ↦ Subtype.ext)
      have hseries : Summable fun n : ℕ ↦ ‖(idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s)‖ := by
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
        have h_term_eq : LSeries.term (fun n : ℕ ↦ ((idealNormMultiplicity L n : ℝ) : ℂ)) s =
            fun n ↦ (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s) := by
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
          Summable fun n ↦ (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s)).norm
      have hzeta : NumberField.dedekindZeta L s =
          ∑' n : ℕ, (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s) := by
        unfold NumberField.dedekindZeta LSeries
        refine tsum_congr fun n ↦ ?_
        unfold LSeries.term
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · have hs0 : s ≠ 0 := by
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
          exact_mod_cast Nat.card_congr hequiv
      set e := Equiv.sigmaFiberEquiv (fun I : NonzeroIdeal L ↦ Ideal.absNorm I.1)
      have hval : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal L // Ideal.absNorm I.1 = n},
          (Ideal.absNorm (y.1).1 : ℂ) ^ (-s)) = (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s) :=
        fun n ↦ by
          rw [show (∑' y : {I : NonzeroIdeal L // Ideal.absNorm I.1 = n},
              (Ideal.absNorm y.1.1 : ℂ) ^ (-s)) = idealNormMultiplicity L n • (n : ℂ) ^ (-s) from
            (tsum_congr fun y : {I : NonzeroIdeal L // Ideal.absNorm I.1 = n} ↦ by rw [y.2]).trans
              (tsum_const ((n : ℂ) ^ (-s))), nsmul_eq_mul]
      have hnorm : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal L // Ideal.absNorm I.1 = n},
          ‖(Ideal.absNorm (y.1).1 : ℂ) ^ (-s)‖) = ‖(idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s)‖ :=
        fun n ↦ by
          rw [show (∑' y : {I : NonzeroIdeal L // Ideal.absNorm I.1 = n},
              ‖(Ideal.absNorm y.1.1 : ℂ) ^ (-s)‖) = idealNormMultiplicity L n • ‖(n : ℂ) ^ (-s)‖ from
            (tsum_congr fun y : {I : NonzeroIdeal L // Ideal.absNorm I.1 = n} ↦ by rw [y.2]).trans
              (tsum_const ‖(n : ℂ) ^ (-s)‖), nsmul_eq_mul, norm_mul,
            Complex.norm_natCast]
      have hsummable : Summable fun I : NonzeroIdeal L ↦ ‖(Ideal.absNorm I.1 : ℂ) ^ (-s)‖ := by
        rw [← e.summable_iff]
        refine (summable_sigma_of_nonneg (fun _ ↦ norm_nonneg _)).mpr ⟨fun _ ↦ Summable.of_finite, ?_⟩
        exact hseries.congr fun n ↦ (hnorm n).symm
      have hsummable_sigma : Summable fun p : Σ n, {I : NonzeroIdeal L // Ideal.absNorm I.1 = n} ↦
          (Ideal.absNorm (e p).1 : ℂ) ^ (-s) :=
        (e.summable_iff (f := fun I : NonzeroIdeal L ↦ (Ideal.absNorm I.1 : ℂ) ^ (-s))).mpr
          hsummable.of_norm
      have hval_sum : (∑' I : NonzeroIdeal L, (Ideal.absNorm I.1 : ℂ) ^ (-s))
          = NumberField.dedekindZeta L s := by
        rw [hzeta,
          ← e.tsum_eq (fun I ↦ (Ideal.absNorm I.1 : ℂ) ^ (-s)), hsummable_sigma.tsum_sigma]
        exact tsum_congr hval
      exact hval_sum ▸ hsummable.of_norm.hasSum)).summable.norm
  have hsumP : Summable fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} ↦
      ‖(Ideal.absNorm 𝔓.1 : ℂ) ^ (-s)‖ :=
    hsum.comp_injective (i := fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} ↦
      (⟨𝔓.1, 𝔓.2.2⟩ : NonzeroIdeal L))
      (fun a b h ↦ Subtype.ext (by simpa using h))
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun 𝔓 ↦ ?_) (hsumP.mul_left 2)
  exact (show ∀ {y : ℂ} (hy : ‖y‖ ≤ 1 / 2),
    ‖(1 - y)⁻¹ - 1‖ ≤ 2 * ‖y‖ from by
    intro y hy
    have hyne1 : (1 : ℂ) - y ≠ 0 := sub_ne_zero.mpr (by rintro rfl; norm_num at hy)
    have heq : (1 - y)⁻¹ - 1 = y * (1 - y)⁻¹ := by field_simp; ring
    rw [heq, norm_mul]
    have hnorm_lb : (2 : ℝ)⁻¹ ≤ ‖(1 : ℂ) - y‖ :=
      calc (2 : ℝ)⁻¹ = 1 - 1 / 2 := by norm_num
        _ ≤ 1 - ‖y‖ := by linarith
        _ ≤ ‖(1 : ℂ)‖ - ‖y‖ := by rw [norm_one]
        _ ≤ ‖(1 : ℂ) - y‖ := norm_sub_norm_le 1 y
    have hinv : ‖(1 - y)⁻¹‖ ≤ 2 := by
      rw [norm_inv, show (2 : ℝ) = (2⁻¹ : ℝ)⁻¹ by norm_num]
      exact inv_anti₀ (by norm_num) hnorm_lb
    rw [mul_comm 2 ‖y‖]
    gcongr) ((show ∀ {s : ℂ} (hs : 1 < s.re) (𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}), (‖(Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)‖ ≤ 1 / 2) from by
    intro s hs 𝔭
    classical
    have h2le : 2 ≤ Ideal.absNorm 𝔭.1 := (show ∀ {𝔭 : Ideal (𝓞 L)} (hp : 𝔭.IsPrime) (hb : 𝔭 ≠ ⊥), (2 ≤ Ideal.absNorm 𝔭) from by
      intro 𝔭 hp hb
      classical
      have hne0 : Ideal.absNorm 𝔭 ≠ 0 := fun h ↦ hb (Ideal.absNorm_eq_zero_iff.mp h)
      have hne1 : Ideal.absNorm 𝔭 ≠ 1 := fun h ↦ hp.ne_top (Ideal.absNorm_eq_one_iff.mp h)
      lia) 𝔭.2.1 𝔭.2.2
    have hpos : 0 < Ideal.absNorm 𝔭.1 := by lia
    rw [Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re]
    have hb2 : (2 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := by exact_mod_cast h2le
    have hb1 : (1 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := one_le_two.trans hb2
    calc (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s.re)
        ≤ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
      _ = ((Ideal.absNorm 𝔭.1 : ℝ))⁻¹ := Real.rpow_neg_one _
      _ ≤ (2 : ℝ)⁻¹ := by rw [inv_le_inv₀ (by linarith) (by norm_num)]; exact hb2
      _ = 1 / 2 := by norm_num) hs 𝔓)

/-- The prime-ideal Euler product of `ζ_L` is `Multipliable`, with `HasProd` value `ζ_L(s)`.
`Multipliable` (hence the partition / fiberwise-regrouping lemmas) follows from absolute
convergence (`summable_norm_primeIdeal_factor_sub_one`), and the value is pinned by the
prime-ideal Euler product `dedekindZeta_eq_tprod_primeIdeal`. -/
private theorem hasProd_primeIdeal_factor
    (L : Type*) [Field L] [NumberField L] {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} ↦
        (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹) (NumberField.dedekindZeta L s) := by
  have hmul : Multipliable fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} ↦
      (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹ := by
    simpa using multipliable_one_add_of_summable
      (f := fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} ↦
        (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹ - 1)
      (summable_norm_primeIdeal_factor_sub_one L hs)
  rw [dedekindZeta_eq_tprod_primeIdeal L hs]
  exact hmul.hasProd

/-- Prime-ideal Euler factors remain multipliable on every predicate-subtype of nonzero primes,
by restricting their summable factor difference. -/
private theorem multipliable_primeIdeal_factor_subtype
    (L : Type*) [Field L] [NumberField L] {s : ℂ} (hs : 1 < s.re)
    (p : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} → Prop) :
    Multipliable fun 𝔓 : {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} // p 𝔓} ↦
      (1 - (Ideal.absNorm 𝔓.1.1 : ℂ) ^ (-s))⁻¹ := by
  have hsum : Summable ((fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} ↦
      ‖(1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹ - 1‖) ∘ (↑) :
      {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} // p 𝔓} → ℝ) :=
    (summable_norm_primeIdeal_factor_sub_one L hs).subtype p
  simpa using multipliable_one_add_of_summable
    (f := fun 𝔓 : {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} // p 𝔓} ↦
      (1 - (Ideal.absNorm 𝔓.1.1 : ℂ) ^ (-s))⁻¹ - 1) hsum

/-- The χ-twisted local Euler product `∏'_{𝔭 unram} (1 - χ(σ_𝔭) N𝔭^{-s})^{-1} = L_χ` is
`Multipliable`. As for `ζ_L`, this is absolute convergence: `‖χ(σ_𝔭)‖ = 1`
by the finite order of Frobenius, so `‖χ(σ_𝔭) N𝔭^{-s}‖ = ‖N𝔭^{-s}‖ ≤ 1/2`, and `∑_{𝔭 unram} ‖N𝔭^{-s}‖`
is a sub-sum of the absolutely convergent `ζ_K`. -/
private theorem multipliable_artinLocalFactor
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) {s : ℂ} (hs : 1 < s.re) :
    Multipliable fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ↦
      (1 - (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹ := by
  have hsum : Summable fun 𝔞 : NonzeroIdeal K ↦ ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-s)‖ :=
    ((show HasSum (fun I : NonzeroIdeal K ↦ (Ideal.absNorm I.1 : ℂ) ^ (-s)) (NumberField.dedekindZeta K s) from by
      have hcondition : 1 < (s).re := hs
      classical
      haveI (n : ℕ) : Finite {I : NonzeroIdeal K // Ideal.absNorm I.1 = n} :=
        Set.Finite.to_subtype <| Set.Finite.of_finite_image (f := fun I : NonzeroIdeal K ↦ I.1)
          ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).subset (by rintro _ ⟨⟨I, _⟩, rfl, rfl⟩; rfl))
          (fun _ _ _ _ ↦ Subtype.ext)
      have hseries : Summable fun n : ℕ ↦ ‖(idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-s)‖ := by
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
        have h_term_eq : LSeries.term (fun n : ℕ ↦ ((idealNormMultiplicity K n : ℝ) : ℂ)) s =
            fun n ↦ (idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-s) := by
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
          Summable fun n ↦ (idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-s)).norm
      have hzeta : NumberField.dedekindZeta K s =
          ∑' n : ℕ, (idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-s) := by
        unfold NumberField.dedekindZeta LSeries
        refine tsum_congr fun n ↦ ?_
        unfold LSeries.term
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · have hs0 : s ≠ 0 := by
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
          (Ideal.absNorm (y.1).1 : ℂ) ^ (-s)) = (idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-s) :=
        fun n ↦ by
          rw [show (∑' y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n},
              (Ideal.absNorm y.1.1 : ℂ) ^ (-s)) = idealNormMultiplicity K n • (n : ℂ) ^ (-s) from
            (tsum_congr fun y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n} ↦ by rw [y.2]).trans
              (tsum_const ((n : ℂ) ^ (-s))), nsmul_eq_mul]
      have hnorm : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n},
          ‖(Ideal.absNorm (y.1).1 : ℂ) ^ (-s)‖) = ‖(idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-s)‖ :=
        fun n ↦ by
          rw [show (∑' y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n},
              ‖(Ideal.absNorm y.1.1 : ℂ) ^ (-s)‖) = idealNormMultiplicity K n • ‖(n : ℂ) ^ (-s)‖ from
            (tsum_congr fun y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n} ↦ by rw [y.2]).trans
              (tsum_const ‖(n : ℂ) ^ (-s)‖), nsmul_eq_mul, norm_mul,
            Complex.norm_natCast]
      have hsummable : Summable fun I : NonzeroIdeal K ↦ ‖(Ideal.absNorm I.1 : ℂ) ^ (-s)‖ := by
        rw [← e.summable_iff]
        refine (summable_sigma_of_nonneg (fun _ ↦ norm_nonneg _)).mpr ⟨fun _ ↦ Summable.of_finite, ?_⟩
        exact hseries.congr fun n ↦ (hnorm n).symm
      have hsummable_sigma : Summable fun p : Σ n, {I : NonzeroIdeal K // Ideal.absNorm I.1 = n} ↦
          (Ideal.absNorm (e p).1 : ℂ) ^ (-s) :=
        (e.summable_iff (f := fun I : NonzeroIdeal K ↦ (Ideal.absNorm I.1 : ℂ) ^ (-s))).mpr
          hsummable.of_norm
      have hval_sum : (∑' I : NonzeroIdeal K, (Ideal.absNorm I.1 : ℂ) ^ (-s))
          = NumberField.dedekindZeta K s := by
        rw [hzeta,
          ← e.tsum_eq (fun I ↦ (Ideal.absNorm I.1 : ℂ) ^ (-s)), hsummable_sigma.tsum_sigma]
        exact tsum_congr hval
      exact hval_sum ▸ hsummable.of_norm.hasSum)).summable.norm
  have hsumP : Summable fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ↦
      ‖(Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)‖ :=
    hsum.comp_injective (i := fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ↦
      (⟨𝔭.1, (𝔭.2.2).1⟩ : NonzeroIdeal K))
      (fun _ _ h ↦ Subtype.ext (by simpa using h))
  have hsummable : Summable fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ↦
      ‖(1 - (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹ - 1‖ := by
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun 𝔭 ↦ ?_) (hsumP.mul_left 2)
    set y : ℂ := (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s) with hy
    have hnorm : ‖(χ (frobeniusClass K L 𝔭.1).out : ℂ)‖ = 1 :=
      (((Units.coeHom ℂ).comp χ).isOfFinOrder
        (isOfFinOrder_of_finite (frobeniusClass K L 𝔭.1).out)).norm_eq_one
    have hynorm : ‖y‖ ≤ 1 / 2 := by
      rw [hy, norm_mul, hnorm, one_mul]
      exact (show ∀ {s : ℂ} (hs : 1 < s.re) (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}), (‖(Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)‖ ≤ 1 / 2) from by
        intro s hs 𝔭
        classical
        have h2le : 2 ≤ Ideal.absNorm 𝔭.1 := (show ∀ {𝔭 : Ideal (𝓞 K)} (hp : 𝔭.IsPrime) (hb : 𝔭 ≠ ⊥), (2 ≤ Ideal.absNorm 𝔭) from by
          intro 𝔭 hp hb
          classical
          have hne0 : Ideal.absNorm 𝔭 ≠ 0 := fun h ↦ hb (Ideal.absNorm_eq_zero_iff.mp h)
          have hne1 : Ideal.absNorm 𝔭 ≠ 1 := fun h ↦ hp.ne_top (Ideal.absNorm_eq_one_iff.mp h)
          lia) 𝔭.2.1 𝔭.2.2
        have hpos : 0 < Ideal.absNorm 𝔭.1 := by lia
        rw [Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re]
        have hb2 : (2 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := by exact_mod_cast h2le
        have hb1 : (1 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := one_le_two.trans hb2
        calc (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s.re)
            ≤ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
          _ = ((Ideal.absNorm 𝔭.1 : ℝ))⁻¹ := Real.rpow_neg_one _
          _ ≤ (2 : ℝ)⁻¹ := by rw [inv_le_inv₀ (by linarith) (by norm_num)]; exact hb2
          _ = 1 / 2 := by norm_num) hs
        ⟨𝔭.1, 𝔭.2.1, (𝔭.2.2).1⟩
    calc ‖(1 - y)⁻¹ - 1‖ ≤ 2 * ‖y‖ := (show ∀ {y : ℂ} (hy : ‖y‖ ≤ 1 / 2),
      ‖(1 - y)⁻¹ - 1‖ ≤ 2 * ‖y‖ from by
      intro y hy
      have hyne1 : (1 : ℂ) - y ≠ 0 := sub_ne_zero.mpr (by rintro rfl; norm_num at hy)
      have heq : (1 - y)⁻¹ - 1 = y * (1 - y)⁻¹ := by field_simp; ring
      rw [heq, norm_mul]
      have hnorm_lb : (2 : ℝ)⁻¹ ≤ ‖(1 : ℂ) - y‖ :=
        calc (2 : ℝ)⁻¹ = 1 - 1 / 2 := by norm_num
          _ ≤ 1 - ‖y‖ := by linarith
          _ ≤ ‖(1 : ℂ)‖ - ‖y‖ := by rw [norm_one]
          _ ≤ ‖(1 : ℂ) - y‖ := norm_sub_norm_le 1 y
      have hinv : ‖(1 - y)⁻¹‖ ≤ 2 := by
        rw [norm_inv, show (2 : ℝ) = (2⁻¹ : ℝ)⁻¹ by norm_num]
        exact inv_anti₀ (by norm_num) hnorm_lb
      rw [mul_comm 2 ‖y‖]
      gcongr) hynorm
      _ = 2 * ‖(Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)‖ := by
          rw [hy, norm_mul, hnorm, one_mul]
  simpa using multipliable_one_add_of_summable
    (f := fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ↦
      (1 - (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹ - 1) hsummable

open Finset in
set_option backward.isDefEq.respectTransparency false in
/-- The unramified part of the prime-ideal Euler product equals `∏_χ L_χ`. Regroup the unramified
`L`-primes fibrewise over the `K`-prime below them (`Equiv.sigmaFiberEquiv` +
`Multipliable.tprod_sigma`); each fibre product is `∏_χ (1 - χ(σ_𝔭) N𝔭^{-s})^{-1}`
(the local fibre calculation); swap the finite character
product out (`Multipliable.tprod_finsetProd`) and apply the abelian Euler product
(`exists_artinLSeries_eulerProduct_abelian`). -/
private theorem tprod_unramified_eq_prod_artinDirichletSeries
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] {s : ℂ} (hs : 1 < s.re) :
    (∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
          UnramifiedIn K L (𝔓.under (𝓞 K))},
        (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹)
      = ∏' χ : galoisCharacter K L, artinDirichletSeries K L χ s := by
  let underUP (𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧ UnramifiedIn K L (𝔓.under (𝓞 K))}) :
      {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} :=
    ⟨𝔓.1.under (𝓞 K), by haveI := 𝔓.2.1; exact inferInstance, 𝔓.2.2.2⟩
  let fiberUnderEquiv (c : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭}) :
      {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧ UnramifiedIn K L (𝔓.under (𝓞 K))} //
          underUP 𝔓 = c} ≃
        {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver c.1 ∧ 𝔓 ≠ ⊥} := {
    toFun := fun 𝔓 ↦ ⟨𝔓.1.1, 𝔓.1.2.1, ⟨by
      have h := congrArg Subtype.val 𝔓.2
      change 𝔓.1.1.under (𝓞 K) = c.1 at h
      rw [← h]⟩, 𝔓.1.2.2.1⟩
    invFun := fun 𝔔 ↦ ⟨⟨𝔔.1, 𝔔.2.1, 𝔔.2.2.2, by
        haveI := 𝔔.2.1; haveI := 𝔔.2.2.1; rw [← 𝔔.2.2.1.over]; exact c.2.2⟩, by
      haveI := 𝔔.2.1; haveI := 𝔔.2.2.1
      exact Subtype.ext (by change 𝔔.1.under (𝓞 K) = c.1; exact 𝔔.2.2.1.over.symm)⟩
    left_inv := fun 𝔓 ↦ by ext; rfl
    right_inv := fun 𝔔 ↦ by ext; rfl }
  let unramifiedFlattenEquiv :
      {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} // UnramifiedIn K L (𝔓.1.under (𝓞 K))} ≃
        {𝔔 : Ideal (𝓞 L) // 𝔔.IsPrime ∧ 𝔔 ≠ ⊥ ∧ UnramifiedIn K L (𝔔.under (𝓞 K))} := {
    toFun := fun 𝔓 ↦ ⟨𝔓.1.1, 𝔓.1.2.1, 𝔓.1.2.2, 𝔓.2⟩
    invFun := fun 𝔔 ↦ ⟨⟨𝔔.1, 𝔔.2.1, 𝔔.2.2.1⟩, 𝔔.2.2.2⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }
  classical
  set F : Ideal (𝓞 L) → ℂ := fun 𝔭 ↦ (1 - (Ideal.absNorm 𝔭 : ℂ) ^ (-s))⁻¹ with hF
  set G : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} → ℂ :=
    fun c ↦ ∏' χ : galoisCharacter K L,
      (1 - (χ (frobeniusClass K L c.1).out : ℂ) * (Ideal.absNorm c.1 : ℂ) ^ (-s))⁻¹ with hG
  -- `Multipliable.subtype` is avoided: it whnf-explodes on the `Ideal (𝓞 L)` prime subtype.
  -- Restrict the *summable* norm via `Summable.subtype`, then rebuild multipliability.
  have hmulU : Multipliable fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      UnramifiedIn K L (𝔓.under (𝓞 K))} ↦ F 𝔓.1 := by
    have hsumU : Summable ((fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} ↦
        ‖(1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹ - 1‖) ∘ (↑) :
        {x : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} //
          UnramifiedIn K L (x.1.under (𝓞 K))} → ℝ) :=
      (summable_norm_primeIdeal_factor_sub_one L hs).subtype
        (fun 𝔓 ↦ UnramifiedIn K L (𝔓.1.under (𝓞 K)))
    have hmul1 : Multipliable fun 𝔓 : {x : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} //
        UnramifiedIn K L (x.1.under (𝓞 K))} ↦ F 𝔓.1.1 := by
      simpa [hF] using multipliable_one_add_of_summable
        (f := fun 𝔓 : {x : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} //
            UnramifiedIn K L (x.1.under (𝓞 K))} ↦
          (1 - (Ideal.absNorm 𝔓.1.1 : ℂ) ^ (-s))⁻¹ - 1) hsumU
    exact (Equiv.multipliable_iff (unramifiedFlattenEquiv).symm).mpr hmul1
  have hfibHasProd : ∀ c : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
      HasProd (fun 𝔓 : {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
          UnramifiedIn K L (𝔓.under (𝓞 K))} // underUP 𝔓 = c} ↦ F 𝔓.1.1) (G c) := by
    intro c
    haveI : c.1.IsPrime := c.2.1
    haveI : c.1.IsMaximal := c.2.1.isMaximal ((c.2.2).1)
    haveI : Finite (c.1.primesOver (𝓞 L)) :=
      (IsDedekindDomain.primesOver_finite c.1 (𝓞 L)).to_subtype
    haveI : Finite {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver c.1 ∧ 𝔓 ≠ ⊥} :=
      Finite.of_injective
        (fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver c.1 ∧ 𝔓 ≠ ⊥} ↦
          (⟨𝔓.1, 𝔓.2.1, 𝔓.2.2.1⟩ : c.1.primesOver (𝓞 L)))
        (fun _ _ hab ↦ Subtype.ext (by simpa using hab))
    haveI : Finite {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
        UnramifiedIn K L (𝔓.under (𝓞 K))} // underUP 𝔓 = c} :=
      Finite.of_equiv _ (fiberUnderEquiv c).symm
    have hval : (∏' 𝔓 : {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
          UnramifiedIn K L (𝔓.under (𝓞 K))} // underUP 𝔓 = c}, F 𝔓.1.1) = G c := by
      simp only [hG]
      let 𝔭 : Ideal (𝓞 K) := c.1
      haveI : 𝔭.IsPrime := c.2.1
      have _hunr : UnramifiedIn K L 𝔭 := c.2.2
      have _hs : 1 < s.re := hs
      have hlocal :
          ∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥},
            (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹
            = ∏' χ : galoisCharacter K L,
              (1 - (χ (frobeniusClass K L 𝔭).out : ℂ) * (Ideal.absNorm 𝔭 : ℂ) ^ (-s))⁻¹ := by
        classical
        open scoped IsMulCommutative in
        letI : CommGroup Gal(L/K) := inferInstance
        letI : DistribMulAction Gal(L/K) (Ideal (𝓞 L)) := Ideal.pointwiseDistribMulAction
        letI : FaithfulSMul Gal(L/K) (𝓞 L) := IsGaloisGroup.faithful (𝓞 K)
        have hunr : UnramifiedIn K L 𝔭 := _hunr
        set σ : Gal(L/K) := (frobeniusClass K L 𝔭).out
        set Y : ℂ := (Ideal.absNorm 𝔭 : ℂ) ^ (-s) with hY
        set f : ℕ := orderOf σ with hf
        haveI : Fintype Gal(L/K) := Fintype.ofFinite _
        haveI : Fintype (Gal(L/K) →* ℂˣ) := Fintype.ofFinite _
        have hfpos : 0 < f := hf ▸ orderOf_pos_iff.mpr (isOfFinOrder_of_finite σ)
        have hresidue (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hlo : 𝔓.LiesOver 𝔭) :
            Module.finrank (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) = orderOf σ := by
          let C : ConjClasses Gal(L/K) := frobeniusClass K L 𝔭
          have hσ : ConjClasses.mk σ = C := Quotient.out_eq _
          have hCfrob : frobeniusClass K L 𝔭 = C := rfl
          have hunr : UnramifiedIn K L 𝔭 := _hunr
          have hra : Ideal.ramificationIdx' (𝔓.under (𝓞 K)) 𝔓 = 1 := by
            have hPbot := Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓
            have hpbot := Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPbot
            haveI : Algebra.IsUnramifiedAt (𝓞 K) 𝔓 :=
              hunr.2 𝔓 (‹𝔓.IsPrime›.isMaximal hPbot) hlo
            rw [Ideal.ramificationIdx'_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 hpbot]
            exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
          have : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓
            (Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓)
          have hclass : frobeniusClass K L 𝔭 =
              ConjClasses.mk (arithFrobAt (𝓞 K) Gal(L/K) 𝔓) := by
            let e : ∃ 𝔓₀ : Ideal (𝓞 L), 𝔓₀.IsPrime ∧ 𝔓₀.LiesOver 𝔭 := by
              obtain ⟨𝔓₀, hp₀, hcomap₀⟩ :=
                Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 L) 𝔭 (by
                  rw [(RingHom.injective_iff_ker_eq_bot _).mp
                    (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))]
                  exact bot_le)
              exact ⟨𝔓₀, hp₀, ⟨hcomap₀.symm⟩⟩
            let 𝔓₀ := Classical.choose e
            haveI : 𝔓₀.IsPrime := (Classical.choose_spec e).1
            have hlo₀ : 𝔓₀.LiesOver 𝔭 := (Classical.choose_spec e).2
            haveI : Finite (𝓞 L ⧸ 𝔓₀) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓₀
              (Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓₀)
            rw [frobeniusClass, dif_pos ⟨‹𝔭.IsPrime›, hunr⟩]
            change ConjClasses.mk (arithFrobAt (𝓞 K) Gal(L/K) 𝔓₀) =
              ConjClasses.mk (arithFrobAt (𝓞 K) Gal(L/K) 𝔓)
            exact ConjClasses.mk_eq_mk_iff_isConj.mpr <|
              isConj_arithFrobAt (𝓞 K) Gal(L/K) 𝔓₀ 𝔓 (hlo₀.over.symm.trans hlo.over)
          obtain ⟨c, hc⟩ : IsConj (arithFrobAt (𝓞 K) Gal(L/K) 𝔓) σ := by
            rw [← ConjClasses.mk_eq_mk_iff_isConj,
              ← hclass, hCfrob, hσ]
          have horder : orderOf (arithFrobAt (𝓞 K) Gal(L/K) 𝔓) =
              Module.finrank (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) := by
            have h : Ideal.ramificationIdx' (𝔓.under (𝓞 K)) 𝔓 = 1 := hra
            have hPbot : 𝔓 ≠ ⊥ := by
              intro hbot
              subst 𝔓
              simp only [Ideal.under_bot, Ideal.ramificationIdx'_bot, zero_ne_one] at h
            have hpbot : 𝔓.under (𝓞 K) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPbot
            have : 𝔓.IsMaximal := ‹𝔓.IsPrime›.isMaximal hPbot
            have : (𝔓.under (𝓞 K)).IsMaximal :=
              (inferInstance : (𝔓.under (𝓞 K)).IsPrime).isMaximal hpbot
            have : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 hPbot
            have : Algebra.IsUnramifiedAt (𝓞 K) 𝔓 :=
              Ideal.ramificationIdx_eq_one_iff.mp
                ((Ideal.ramificationIdx'_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 hpbot).symm.trans h)
            let : Field (𝓞 K ⧸ 𝔓.under (𝓞 K)) := Ideal.Quotient.field _
            let : Field (𝓞 L ⧸ 𝔓) := Ideal.Quotient.field _
            have : Finite (𝓞 K ⧸ 𝔓.under (𝓞 K)) :=
              Ideal.finiteQuotientOfFreeOfNeBot (𝔓.under (𝓞 K)) hpbot
            have : Algebra.IsSeparable (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) :=
              IsGalois.to_isSeparable
            have : Algebra.IsAlgebraic (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) :=
              Algebra.IsAlgebraic.of_finite _ _
            let : Fintype (𝓞 K ⧸ 𝔓.under (𝓞 K)) := Fintype.ofFinite _
            set g₀ : MulAction.stabilizer Gal(L/K) 𝔓 :=
              ⟨arithFrobAt (𝓞 K) Gal(L/K) 𝔓,
                IsArithFrobAt.arithFrobAt_mem_stabilizer (𝓞 K) Gal(L/K) 𝔓⟩ with hg₀
            have hres :
                Ideal.Quotient.stabilizerHom 𝔓 (𝔓.under (𝓞 K)) Gal(L/K) g₀ =
                  FiniteField.frobeniusAlgEquivOfAlgebraic
                    (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) := by
              ext x
              obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
              rw [hg₀, Ideal.Quotient.stabilizerHom_apply,
                FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ← Nat.card_eq_fintype_card]
              exact (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓).mk_apply b
            have hinj :
                Function.Injective (Ideal.Quotient.stabilizerHom 𝔓 (𝔓.under (𝓞 K)) Gal(L/K)) := by
              rw [← MonoidHom.ker_eq_bot_iff, Ideal.Quotient.ker_stabilizerHom]
              show (Ideal.inertia Gal(L/K) 𝔓).subgroupOf (MulAction.stabilizer Gal(L/K) 𝔓) = ⊥
              rw [show Ideal.inertia Gal(L/K) 𝔓 = ⊥ from by
                rw [Subgroup.eq_bot_iff_card,
                  Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/K)) (𝔓.under (𝓞 K)) 𝔓,
                  Ideal.ramificationIdxIn_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 Gal(L/K),
                  ← Ideal.ramificationIdx'_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 hpbot]
                exact h,
                Subgroup.bot_subgroupOf]
            calc
              orderOf (arithFrobAt (𝓞 K) Gal(L/K) 𝔓) = orderOf g₀ := by
                rw [hg₀, Subgroup.orderOf_mk]
              _ = orderOf (Ideal.Quotient.stabilizerHom 𝔓 (𝔓.under (𝓞 K)) Gal(L/K) g₀) :=
                  (orderOf_injective _ hinj g₀).symm
              _ = orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic
                    (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓)) := by rw [hres]
              _ = Module.finrank (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) :=
                  FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic _ _
          rw [← hc.orderOf_eq, horder]
        have hcount : Nat.card {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥}
            = Nat.card Gal(L/K) / f := by
          have hmul : Nat.card {𝔓 : Ideal (𝓞 L) //
              𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} * orderOf σ = Nat.card Gal(L/K) := by
            let C := frobeniusClass K L 𝔭
            have _hσ : ConjClasses.mk σ = C := Quotient.out_eq _
            have _hCfrob : frobeniusClass K L 𝔭 = C := rfl
            obtain ⟨𝔓₀, hp₀, hcomap₀⟩ :=
              Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 L) 𝔭 (by
                rw [(RingHom.injective_iff_ker_eq_bot _).mp
                  (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))]
                exact bot_le)
            have hlo₀ : 𝔓₀.LiesOver 𝔭 := ⟨hcomap₀.symm⟩
            haveI : 𝔓₀.IsPrime := hp₀
            rw [← hresidue 𝔓₀ hlo₀]
            have hcard : Nat.card {𝔓 : Ideal (𝓞 L) //
                  𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} *
                Module.finrank (𝓞 K ⧸ 𝔓₀.under (𝓞 K)) (𝓞 L ⧸ 𝔓₀) =
                  Nat.card Gal(L/K) := by
              have hlo : 𝔓₀.LiesOver 𝔭 := hlo₀
              have hpbot : 𝔭 ≠ ⊥ := (hunr).1
              have he : Ideal.ramificationIdx' (𝔓₀.under (𝓞 K)) 𝔓₀ = 1 := by
                have hPbot := Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓₀
                have hpbot := Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPbot
                haveI : Algebra.IsUnramifiedAt (𝓞 K) 𝔓₀ :=
                  hunr.2 𝔓₀ (‹𝔓₀.IsPrime›.isMaximal hPbot) hlo
                rw [Ideal.ramificationIdx'_eq_ramificationIdx (𝔓₀.under (𝓞 K)) 𝔓₀ hpbot]
                exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
              have hP0bot : 𝔓₀ ≠ ⊥ := by
                intro hbot
                subst 𝔓₀
                simp only [Ideal.under_bot, Ideal.ramificationIdx'_bot, zero_ne_one] at he
              have hunder : 𝔓₀.under (𝓞 K) = 𝔭 := hlo.over.symm
              have hp_under_bot : 𝔓₀.under (𝓞 K) ≠ ⊥ := hunder ▸ hpbot
              have : 𝔓₀.IsMaximal := ‹𝔓₀.IsPrime›.isMaximal hP0bot
              have : (𝔓₀.under (𝓞 K)).IsMaximal :=
                (inferInstance : (𝔓₀.under (𝓞 K)).IsPrime).isMaximal hp_under_bot
              have : Finite (𝓞 L ⧸ 𝔓₀) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓₀
                (Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓₀)
              have : Algebra.IsSeparable (𝓞 K ⧸ 𝔓₀.under (𝓞 K)) (𝓞 L ⧸ 𝔓₀) := by
                let : Field (𝓞 K ⧸ 𝔓₀.under (𝓞 K)) := Ideal.Quotient.field _
                let : Field (𝓞 L ⧸ 𝔓₀) := Ideal.Quotient.field _
                exact IsGalois.to_isSeparable
              haveI : Finite (𝓞 K ⧸ 𝔓₀.under (𝓞 K)) :=
                Ideal.finiteQuotientOfFreeOfNeBot _ hp_under_bot
              have H :=
                Ideal.ncard_primesOver_mul_card_inertia_mul_finrank
                  (G := Gal(L/K)) (𝔓₀.under (𝓞 K)) 𝔓₀
              rw [show Ideal.inertia Gal(L/K) 𝔓₀ = ⊥ from by
                    rw [Subgroup.eq_bot_iff_card,
                      Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/K)) (𝔓₀.under (𝓞 K)) 𝔓₀,
                      Ideal.ramificationIdxIn_eq_ramificationIdx (𝔓₀.under (𝓞 K)) 𝔓₀ Gal(L/K),
                      ← Ideal.ramificationIdx'_eq_ramificationIdx (𝔓₀.under (𝓞 K)) 𝔓₀ hp_under_bot]
                    exact he,
                  Subgroup.card_bot, mul_one,
                  ← Ideal.inertiaDeg'_eq_inertiaDeg (𝔓₀.under (𝓞 K)) 𝔓₀,
                  Ideal.inertiaDeg'_algebraMap (𝔓₀.under (𝓞 K)) 𝔓₀] at H
              have hset : (𝔓₀.under (𝓞 K)).primesOver (𝓞 L)
                  = {𝔓 : Ideal (𝓞 L) | 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} := by
                ext 𝔓
                refine ⟨fun ⟨hp, hlo'⟩ ↦ ?_, fun ⟨hp, hlo', _⟩ ↦ ?_⟩
                · have := hlo'
                  exact ⟨hp, hunder ▸ hlo', Ideal.ne_bot_of_liesOver_of_ne_bot hp_under_bot 𝔓⟩
                · exact ⟨hp, hunder ▸ hlo'⟩
              rwa [hset, ← Nat.card_coe_set_eq] at H
            exact hcard
          rw [← hf] at hmul
          exact (Nat.div_eq_of_eq_mul_left hfpos hmul.symm).symm
        have hRHS : (∏' χ : galoisCharacter K L,
              (1 - ((χ σ : ℂˣ) : ℂ) * Y)⁻¹)
            = ((1 - Y ^ f) ^ (Nat.card Gal(L/K) / f))⁻¹ := by
          let G := Gal(L/K)
          have hprod :
              ∏ χ : G →* ℂˣ, (1 - ((χ σ : ℂˣ) : ℂ) * Y)
                = (1 - Y ^ orderOf σ) ^ (Nat.card G / orderOf σ) := by
            classical
            let charEval (σ : G) : (G →* ℂˣ) →* ℂˣ :=
              (CommGroup.monoidHomMonoidHomEquiv G ℂ).symm σ
            have hker : Nat.card (charEval σ).ker = Nat.card G / orderOf σ := by
              have h1 : (charEval σ).ker = (MonoidHom.domRestrictHom (Subgroup.zpowers σ) ℂˣ).ker := by
                ext φ
                change (charEval σ) φ = 1 ↔ φ.domRestrict (Subgroup.zpowers σ) = 1
                rw [MonoidHom.domRestrict_eq_one_iff]
                refine ⟨fun hφ y hy ↦ ?_, fun hφ ↦ ?_⟩
                · dsimp only [charEval] at hφ
                  rw [CommGroup.monoidHomMonoidHomEquiv_symm_apply_apply] at hφ
                  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
                  rw [map_zpow, hφ, one_zpow]
                · dsimp only [charEval]
                  rw [CommGroup.monoidHomMonoidHomEquiv_symm_apply_apply]
                  exact hφ σ (Subgroup.mem_zpowers σ)
              rw [h1, CommGroup.card_domRestrictHom_ker]
              have hpos : 0 < orderOf σ := orderOf_pos_iff.mpr (isOfFinOrder_of_finite σ)
              have key : Nat.card G = Nat.card (G ⧸ Subgroup.zpowers σ) * orderOf σ := by
                rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers σ), Nat.card_zpowers]
              rw [key, Nat.mul_div_cancel _ hpos]
            set f := orderOf σ with hf
            have hfpos : 0 < f := orderOf_pos_iff.mpr (isOfFinOrder_of_finite σ)
            set evC : (G →* ℂˣ) →* ℂ := (Units.coeHom ℂ).comp (charEval σ) with hevC
            have hevC_apply : ∀ χ : G →* ℂˣ, evC χ = ((χ σ : ℂˣ) : ℂ) := fun χ ↦ by
              rw [hevC, MonoidHom.comp_apply, Units.coeHom_apply]
              dsimp only [charEval]
              rw [CommGroup.monoidHomMonoidHomEquiv_symm_apply_apply]
            have hfib1 : #{χ : G →* ℂˣ | evC χ = 1} = Nat.card (charEval σ).ker := by
              rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
              refine Fintype.card_congr (Equiv.subtypeEquivRight fun χ ↦ ?_)
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, MonoidHom.mem_ker, hevC_apply]
              rw [Units.val_eq_one]
              dsimp only [charEval]
              rw [CommGroup.monoidHomMonoidHomEquiv_symm_apply_apply]
            have huniform : ∀ c ∈ Set.range evC, #{χ : G →* ℂˣ | evC χ = c} = Nat.card (charEval σ).ker := by
              intro c hc
              rw [MonoidHom.card_fiber_eq_of_mem_range evC hc (⟨1, map_one _⟩ : (1 : ℂ) ∈ Set.range evC),
                hfib1]
            set t : Finset ℂ := Polynomial.nthRootsFinset f (1 : ℂ) with ht
            have hmaps : ∀ χ ∈ (Finset.univ : Finset (G →* ℂˣ)), evC χ ∈ t := by
              intro χ _
              rw [ht, Polynomial.mem_nthRootsFinset hfpos, hevC_apply,
                ← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]
            have hsub : Finset.univ.image evC ⊆ t := by
              intro c hc
              rw [Finset.mem_image] at hc
              obtain ⟨χ, _, rfl⟩ := hc
              exact hmaps χ (Finset.mem_univ χ)
            have hcardG : Nat.card G = (Finset.univ.image evC).card * Nat.card (charEval σ).ker := by
              have hsum := Finset.card_eq_sum_card_image evC (Finset.univ : Finset (G →* ℂˣ))
              rw [show (Finset.univ : Finset (G →* ℂˣ)).card = Nat.card (G →* ℂˣ) by
                rw [Nat.card_eq_fintype_card, Finset.card_univ],
                CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity] at hsum
              rw [hsum, Finset.sum_congr rfl (fun c hc ↦ huniform c ?_), Finset.sum_const, smul_eq_mul]
              rw [Finset.mem_image] at hc
              obtain ⟨χ, _, rfl⟩ := hc
              exact Set.mem_range_self χ
            have himgcard : (Finset.univ.image evC).card = f := by
              have hdvd : f ∣ Nat.card G := orderOf_dvd_natCard σ
              have hkereq : Nat.card (charEval σ).ker = Nat.card G / f := hker
              rw [hkereq] at hcardG
              exact Nat.eq_of_mul_eq_mul_right (hkereq ▸ Nat.card_pos)
                (by rw [← hcardG, Nat.mul_div_cancel' hdvd])
            have himg : Finset.univ.image evC = t :=
              Finset.eq_of_subset_of_card_le hsub
                (by rw [himgcard, ht, (Complex.isPrimitiveRoot_exp f hfpos.ne').card_nthRootsFinset])
            have hfiber := Finset.prod_fiberwise_of_maps_to' (s := (Finset.univ : Finset (G →* ℂˣ)))
              (t := t) (g := evC) (f := fun c : ℂ ↦ 1 - c * Y) hmaps
            have hLHS : ∏ χ : G →* ℂˣ, (1 - ((χ σ : ℂˣ) : ℂ) * Y)
                = ∏ χ : G →* ℂˣ, (1 - evC χ * Y) :=
              Finset.prod_congr rfl fun χ _ ↦ by rw [hevC_apply]
            rw [hLHS, ← hfiber]
            have hinner : ∀ c ∈ t, (∏ _χ ∈ {χ ∈ (Finset.univ : Finset (G →* ℂˣ)) | evC χ = c},
                (1 - c * Y)) = (1 - c * Y) ^ Nat.card (charEval σ).ker := by
              intro c hc
              have hrange : c ∈ Set.range evC := by
                rw [← himg, Finset.mem_image] at hc
                obtain ⟨χ, _, rfl⟩ := hc
                exact Set.mem_range_self χ
              rw [Finset.prod_const, huniform c hrange]
            rw [Finset.prod_congr rfl hinner, hker, Finset.prod_pow, ht,
              ← (Complex.isPrimitiveRoot_exp f hfpos.ne').pow_sub_pow_eq_prod_sub_mul 1 Y hfpos, one_pow]
          rw [tprod_fintype, Finset.prod_inv_distrib, hprod, hf]
        have hpbot : 𝔭 ≠ ⊥ := (_hunr).1
        haveI : 𝔭.IsMaximal := ‹𝔭.IsPrime›.isMaximal hpbot
        haveI : Finite (𝔭.primesOver (𝓞 L)) := (IsDedekindDomain.primesOver_finite 𝔭 (𝓞 L)).to_subtype
        haveI : Finite {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} :=
          Finite.of_injective
            (fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} ↦
              (⟨𝔓.1, 𝔓.2.1, 𝔓.2.2.1⟩ : 𝔭.primesOver (𝓞 L)))
            fun _ _ hab ↦ Subtype.ext (by simpa using hab)
        haveI : Fintype {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} := Fintype.ofFinite _
        have hterm : ∀ 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥},
            (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹ = (1 - Y ^ f)⁻¹ := by
          intro 𝔓
          haveI := 𝔓.2.1
          haveI hlo : 𝔓.1.LiesOver 𝔭 := 𝔓.2.2.1
          have hdeg : (𝔓.1.under (𝓞 K)).inertiaDeg' 𝔓.1 = f := by
            rw [Ideal.inertiaDeg'_algebraMap, hf]
            exact hresidue 𝔓.1 hlo
          haveI : 𝔓.1.LiesOver (𝔓.1.under (𝓞 K)) := Ideal.over_under (A := 𝓞 K) (P := 𝔓.1)
          have hpubot : 𝔓.1.under (𝓞 K) ≠ ⊥ := hlo.over ▸ hpbot
          haveI : (𝔓.1.under (𝓞 K)).IsPrime := hlo.over ▸ ‹𝔭.IsPrime›
          have hnorm : Ideal.absNorm 𝔓.1 = Ideal.absNorm 𝔭 ^ f := by
            rw [Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver 𝔓.1 (𝔓.1.under (𝓞 K)) inferInstance hpubot,
              hdeg, ← hlo.over]
          rw [hnorm, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul, hY]
        rw [tprod_congr hterm, tprod_fintype, Finset.prod_const, Finset.card_univ,
          ← Nat.card_eq_fintype_card, hcount, hRHS, Nat.card_eq_fintype_card, inv_pow]
      rw [← hlocal,
        ← (fiberUnderEquiv c).tprod_eq
          (fun 𝔔 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver c.1 ∧ 𝔓 ≠ ⊥} ↦ F 𝔔.1)]
      rfl
    rw [← hval]
    exact (Multipliable.of_finite).hasProd
  have hsig : HasProd G (∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      UnramifiedIn K L (𝔓.under (𝓞 K))}, F 𝔓.1) :=
    ((Equiv.sigmaFiberEquiv (underUP)).hasProd_iff.mpr hmulU.hasProd).sigma hfibHasProd
  rw [← hsig.tprod_eq]
  simp only [hG]
  simp_rw [tprod_fintype]
  rw [Multipliable.tprod_finsetProd (s := (Finset.univ : Finset (galoisCharacter K L)))
    (f := fun χ : galoisCharacter K L ↦
      fun c : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ↦
        (1 - (χ (frobeniusClass K L c.1).out : ℂ) * (Ideal.absNorm c.1 : ℂ) ^ (-s))⁻¹)
    (fun χ _ ↦ multipliable_artinLocalFactor K L χ hs)]
  refine Finset.prod_congr rfl fun χ _ ↦ ?_
  rw [artinDirichletSeries, ← exists_artinLSeries_eulerProduct_abelian K L χ s hs]

/-- Partition `ζ_L`'s prime-ideal Euler product into unramified-below and ramified-below factors
using `HasProd.mul_compl`. -/
private theorem dedekindZeta_eq_unramifiedNested_mul_ramifiedNested
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta L s =
      (∏' 𝔓 : {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} //
          UnramifiedIn K L (𝔓.1.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1.1 : ℂ) ^ (-s))⁻¹) *
        ∏' 𝔓 : {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} //
          ¬ UnramifiedIn K L (𝔓.1.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1.1 : ℂ) ^ (-s))⁻¹ := by
  -- `f`/`S` are pinned explicitly so `HasProd.mul_compl` does no higher-order unification
  -- (`?f ∘ Subtype.val`) on the nested `Ideal (𝓞 L)` prime subtype — that is the `whnf` bomb.
  let f : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} → ℂ :=
    fun 𝔓 ↦ (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹
  let S : Set {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} :=
    {𝔓 | UnramifiedIn K L (𝔓.1.under (𝓞 K))}
  have hSU := (multipliable_primeIdeal_factor_subtype L hs
    (fun 𝔓 ↦ UnramifiedIn K L (𝔓.1.under (𝓞 K)))).hasProd
  have hSUc := (multipliable_primeIdeal_factor_subtype L hs
    (fun 𝔓 ↦ ¬ UnramifiedIn K L (𝔓.1.under (𝓞 K)))).hasProd
  exact ((hSU.mul_compl (f := f) (s := S) hSUc).unique
    (hasProd_primeIdeal_factor L hs)).symm

/-- For `1 < Re s`, `ζ_L(s) = (∏_χ L_χ(s)) · R(s)` (Sharifi 7.1.16), where each `L_χ`
uses unramified primes and `R` corrects for the Euler factors above ramified primes.
The correction is finite and nonzero for real `s > 1`; omitting it gives a false identity. -/
theorem dedekindZeta_eq_prod_artinDirichletSeries
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta L s =
      (∏' χ : galoisCharacter K L, artinDirichletSeries K L χ s) *
        ∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
            ¬ UnramifiedIn K L (𝔓.under (𝓞 K))},
          (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹ := by
  let ramifiedFlattenEquiv :
      {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} // ¬ UnramifiedIn K L (𝔓.1.under (𝓞 K))} ≃
        {𝔔 : Ideal (𝓞 L) // 𝔔.IsPrime ∧ 𝔔 ≠ ⊥ ∧ ¬ UnramifiedIn K L (𝔔.under (𝓞 K))} := {
    toFun := fun 𝔓 ↦ ⟨𝔓.1.1, 𝔓.1.2.1, 𝔓.1.2.2, 𝔓.2⟩
    invFun := fun 𝔔 ↦ ⟨⟨𝔔.1, 𝔔.2.1, 𝔔.2.2.1⟩, 𝔔.2.2.2⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }
  let unramifiedFlattenEquiv :
      {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} // UnramifiedIn K L (𝔓.1.under (𝓞 K))} ≃
        {𝔔 : Ideal (𝓞 L) // 𝔔.IsPrime ∧ 𝔔 ≠ ⊥ ∧ UnramifiedIn K L (𝔔.under (𝓞 K))} := {
    toFun := fun 𝔓 ↦ ⟨𝔓.1.1, 𝔓.1.2.1, 𝔓.1.2.2, 𝔓.2⟩
    invFun := fun 𝔔 ↦ ⟨⟨𝔔.1, 𝔔.2.1, 𝔔.2.2.1⟩, 𝔔.2.2.2⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }
  have hUnramified :
      (∏' 𝔓 : {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} //
          UnramifiedIn K L (𝔓.1.under (𝓞 K))},
        (1 - (Ideal.absNorm 𝔓.1.1 : ℂ) ^ (-s))⁻¹)
        = ∏' χ : galoisCharacter K L, artinDirichletSeries K L χ s := by
    rw [← tprod_unramified_eq_prod_artinDirichletSeries K L hs]
    exact Equiv.tprod_eq unramifiedFlattenEquiv
      (fun 𝔔 ↦ (1 - (Ideal.absNorm 𝔔.1 : ℂ) ^ (-s))⁻¹)
  rw [dedekindZeta_eq_unramifiedNested_mul_ramifiedNested K L hs,
    hUnramified]
  congr 1
  exact Equiv.tprod_eq (ramifiedFlattenEquiv)
    (fun 𝔔 ↦ (1 - (Ideal.absNorm 𝔔.1 : ℂ) ^ (-s))⁻¹)

open Filter Topology Set in
/-- The ramified correction factor `R(s) = ∏'_{𝔓 ram-below} (1 - N𝔓^{-s})^{-1}` is a finite product
of factors each continuous at `s = 1` and tending to the finite nonzero limit `(1 - N𝔓^{-1})^{-1}`
(`N𝔓 ≥ 2`). Hence `‖R(s)‖` is bounded away from `0` and `∞` near `s ↓ 1`, so `|log ‖R(s)‖| ≤ C`.
This is the `O(1)` gap between `log ζ_L` and `Σ_χ log ‖L_χ‖` in the corrected factorisation. -/
theorem log_norm_ramified_factor_bounded
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [_hAb : IsMulCommutative Gal(L/K)] :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      |Real.log ‖∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
          ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-(s : ℂ)))⁻¹‖| ≤
        C := by
  letI : Finite {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      ¬ UnramifiedIn K L (𝔓.under (𝓞 K))} := by
    classical
    have hram : {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ UnramifiedIn K L 𝔭}.Finite := by
      let : Algebra (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) :=
        FractionRing.liftAlgebra (𝓞 K) (FractionRing (𝓞 L))
      have : IsScalarTower (𝓞 K) (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) :=
        FractionRing.isScalarTower_liftAlgebra (𝓞 K) (FractionRing (𝓞 L))
      have hbot : differentIdeal (𝓞 K) (𝓞 L) ≠ 0 := by
        rw [Ideal.zero_eq_bot]
        exact differentIdeal_ne_bot
      apply Set.Finite.subset
        ((Ideal.finite_factors hbot).image (fun v ↦ (v.asIdeal).under (𝓞 K)))
      rintro 𝔭 ⟨-, h𝔭bot, hnunr⟩
      simp only [UnramifiedIn, not_and, not_forall] at hnunr
      obtain ⟨𝔓, h𝔓max, h𝔓lo, h𝔓nu⟩ := hnunr h𝔭bot
      have := h𝔓max.isPrime
      have := h𝔓lo
      have h𝔓bot : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭bot 𝔓
      have hdvd : 𝔓 ∣ differentIdeal (𝓞 K) (𝓞 L) := by
        by_contra h
        exact h𝔓nu (not_dvd_differentIdeal_iff.mp h)
      exact ⟨⟨𝔓, h𝔓max.isPrime, h𝔓bot⟩, hdvd, h𝔓lo.over.symm⟩
    haveI : Finite {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ UnramifiedIn K L 𝔭} :=
      hram.to_subtype
    haveI : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ UnramifiedIn K L 𝔭},
        Finite (𝔭.1.primesOver (𝓞 L)) := fun 𝔭 ↦ by
      haveI : 𝔭.1.IsPrime := 𝔭.2.1
      haveI : 𝔭.1.IsMaximal := 𝔭.2.1.isMaximal 𝔭.2.2.1
      exact (IsDedekindDomain.primesOver_finite 𝔭.1 (𝓞 L)).to_subtype
    refine Finite.of_injective
      (fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧ ¬ UnramifiedIn K L (𝔓.under (𝓞 K))} ↦
        (show Σ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ UnramifiedIn K L 𝔭},
            𝔭.1.primesOver (𝓞 L) by
          haveI := 𝔓.2.1
          exact ⟨⟨𝔓.1.under (𝓞 K), inferInstance, Ideal.under_ne_bot (A := 𝓞 K) 𝔓.2.2.1, 𝔓.2.2.2⟩,
            ⟨𝔓.1, 𝔓.2.1, Ideal.over_under (A := 𝓞 K) (P := 𝔓.1)⟩⟩))
      (fun a b hab ↦ Subtype.ext (by simpa using congrArg (fun x ↦ (x.2 : Ideal (𝓞 L))) hab))
  classical
  haveI : Fintype {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      ¬ UnramifiedIn K L (𝔓.under (𝓞 K))} := Fintype.ofFinite _
  set R : ℝ → ℂ := fun s ↦ ∏ 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-(s : ℂ)))⁻¹ with hR
  have hbase : ∀ 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (Ideal.absNorm 𝔓.1 : ℂ) ≠ 0 := fun 𝔓 ↦ by
    have hne0 : Ideal.absNorm 𝔓.1 ≠ 0 := fun h ↦ 𝔓.2.2.1 (Ideal.absNorm_eq_zero_iff.mp h)
    exact_mod_cast hne0
  have hden1 : ∀ 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-(1 : ℂ))) ≠ 0 :=
    fun 𝔓 ↦ by
    have h2 : 2 ≤ Ideal.absNorm 𝔓.1 := (show ∀ {𝔭 : Ideal (𝓞 L)} (hp : 𝔭.IsPrime) (hb : 𝔭 ≠ ⊥), (2 ≤ Ideal.absNorm 𝔭) from by
      intro 𝔭 hp hb
      classical
      have hne0 : Ideal.absNorm 𝔭 ≠ 0 := fun h ↦ hb (Ideal.absNorm_eq_zero_iff.mp h)
      have hne1 : Ideal.absNorm 𝔭 ≠ 1 := fun h ↦ hp.ne_top (Ideal.absNorm_eq_one_iff.mp h)
      lia) 𝔓.2.1 𝔓.2.2.1
    have hlt : ‖(Ideal.absNorm 𝔓.1 : ℂ) ^ (-(1 : ℂ))‖ < 1 := by
      rw [Complex.cpow_neg_one, norm_inv, Complex.norm_natCast]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (by lia : 1 < Ideal.absNorm 𝔓.1))
    intro h
    rw [sub_eq_zero] at h
    rw [← h, norm_one] at hlt
    exact lt_irrefl _ hlt
  have hcont : ContinuousAt R 1 := by
    rw [ContinuousAt, hR]
    refine tendsto_finsetProd _ fun 𝔓 _ ↦ ?_
    have hcpow : ContinuousAt (fun s : ℝ ↦ (Ideal.absNorm 𝔓.1 : ℂ) ^ (-(s : ℂ))) 1 :=
      (continuousAt_const_cpow (hbase 𝔓)).comp Complex.continuous_ofReal.continuousAt.neg
    exact (continuousAt_const.sub hcpow).inv₀ (by simpa using hden1 𝔓)
  have hR1_ne : R 1 ≠ 0 :=
    hR ▸ Finset.prod_ne_zero_iff.mpr fun 𝔓 _ ↦ inv_ne_zero (by simpa using hden1 𝔓)
  have hlogcont : ContinuousAt (fun s : ℝ ↦ Real.log ‖R s‖) 1 :=
    hcont.norm.log (norm_ne_zero_iff.mpr hR1_ne)
  refine ⟨|Real.log ‖R 1‖| + 1, ?_⟩
  have hev : ∀ᶠ s : ℝ in 𝓝 (1 : ℝ),
      |Real.log ‖R s‖ - Real.log ‖R 1‖| ≤ 1 := by
    filter_upwards [hlogcont (Metric.closedBall_mem_nhds (Real.log ‖R 1‖) one_pos)] with s hs
    simpa only [Set.mem_preimage, Metric.mem_closedBall, Real.dist_eq] using hs
  filter_upwards [nhdsWithin_le_nhds hev] with s hs
  rw [show (∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-(s : ℂ)))⁻¹) = R s
    by rw [hR]; exact tprod_fintype _]
  have htri : |Real.log ‖R s‖| ≤ |Real.log ‖R s‖ - Real.log ‖R 1‖| + |Real.log ‖R 1‖| := by
    simpa using abs_add_le (Real.log ‖R s‖ - Real.log ‖R 1‖) (Real.log ‖R 1‖)
  linarith

end Chebotarev
