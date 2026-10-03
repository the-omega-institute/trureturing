/- GID: D5/S3/Factorization/Galois/Chebotarev/FixedFieldHigherDegreeTail
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/Chebotarev/FixedFieldHigherDegreeTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The non-degree-one fixed-field prime tail vanishes in the Dirichlet-density ratio. -/
module

public import D5.S3.Factorization.Galois.Chebotarev.FixedFieldMainTerm

/-!
# Density transfer through a fixed field

The error term from higher inertia degree and ramified primes vanishes in
the density ratio, completing the transfer from the cyclic fixed field.
-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

open Filter NumberField Topology Set

open scoped ENNReal

namespace Chebotarev

universe u v

variable {K : Type u} {L : Type v} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- **LEAF B: the degree-`≥ 2` part of `T` vanishes in the density ratio** (Sharifi 7.2.2
p. 143, "`Σ_𝔭 N𝔭⁻ˢ ~ Σ_P NP⁻ˢ`"). The complement `T₂ = T ∖ T₁` consists of primes `P` of `𝓞 E`
that are either of inertia degree `≥ 2` over `K` (so `N P = N(P ∩ 𝓞 K)^{≥2}`, contributing a
`Θ(Σ_𝔭 N𝔭⁻²ˢ)` tail that is bounded near `s = 1`) or lie over one of the finitely many primes
of `𝓞 K` ramified in `L` (a finite contribution).  Both are `o(Σ_univ^E)` since
`Σ_univ^E → ∞`, so `Σ_{T₂}/Σ_univ^E → 0`.

This is the asymptotic content that the (false) exact identity
`Σ_S = (f|C|/|G|)·Σ_T` elided: the relation `Σ_𝔭 N𝔭⁻ˢ ~ Σ_P NP⁻ˢ` holds only in the
`s → 1⁺` limit, with the higher-degree primes of `E` over `K` forming the discrepancy. -/
theorem primeIdealZetaSum_T2_div_univ_tendsto_zero
    (σ : Gal(L/K))
    (σE : Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (T₂set : Set (Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))))
    (hT₂ : T₂set = {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) |
        P.IsPrime ∧ UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P ∧
        frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P
          = ConjClasses.mk σE} \
      {P ∈ {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) |
          P.IsPrime ∧ UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P ∧
          frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P
            = ConjClasses.mk σE} |
        (P.under (𝓞 K)).inertiaDeg' P = 1 ∧ UnramifiedIn K L (P.under (𝓞 K))}) :
    Tendsto (fun s : ℝ ↦ primeIdealZetaSum T₂set s
      / primeIdealZetaSum (univ : Set (Ideal (𝓞 ↥(IntermediateField.fixedField
        (Subgroup.zpowers σ))))) s) (𝓝[>] 1) (𝓝 0) := by
  have tsum_comp_le_card_fibre_mul {β : Type v} {γ : Type u} (g : β → γ) (f : γ → ℝ≥0∞) (d : ℕ)
      (hfin : ∀ y, Finite (g ⁻¹' {y} : Set β)) (hfib : ∀ y, Nat.card (g ⁻¹' {y} : Set β) ≤ d) :
      ∑' b, f (g b) ≤ (d : ℝ≥0∞) * ∑' y, f y := by
    rw [← ENNReal.tsum_fiberwise (fun b ↦ f (g b)) g, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum (fun y ↦ ?_)
    rw [tsum_congr (fun b : (g ⁻¹' {y} : Set β) ↦ by rw [b.2])]
    haveI := hfin y
    letI := Fintype.ofFinite (g ⁻¹' {y} : Set β)
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul]
    gcongr
    exact_mod_cast hfib y

  have tsum_real_comp_le_card_fibre_mul {β : Type v} {γ : Type u} (g : β → γ) (FA : β → ℝ)
      (FK : γ → ℝ) (d : ℕ) (hsummA : Summable FA) (hsummK : Summable FK) (hnonnegA : ∀ b, 0 ≤ FA b)
      (hnonnegK : ∀ y, 0 ≤ FK y) (hterm : ∀ b, FA b ≤ FK (g b))
      (hfin : ∀ y, Finite (g ⁻¹' {y} : Set β)) (hfib : ∀ y, Nat.card (g ⁻¹' {y} : Set β) ≤ d) :
      ∑' b, FA b ≤ (d : ℝ) * ∑' y, FK y := by
    have hchain : ∑' b, ENNReal.ofReal (FA b)
        ≤ (d : ℝ≥0∞) * ∑' y, ENNReal.ofReal (FK y) :=
      calc ∑' b, ENNReal.ofReal (FA b) ≤ ∑' b, ENNReal.ofReal (FK (g b)) :=
            ENNReal.tsum_le_tsum fun b ↦ ENNReal.ofReal_le_ofReal (hterm b)
        _ ≤ (d : ℝ≥0∞) * ∑' y, ENNReal.ofReal (FK y) :=
            tsum_comp_le_card_fibre_mul g (fun y ↦ ENNReal.ofReal (FK y)) d hfin hfib
    rw [← ENNReal.ofReal_tsum_of_nonneg hnonnegA hsummA,
      ← ENNReal.ofReal_tsum_of_nonneg hnonnegK hsummK] at hchain
    rw [← ENNReal.toReal_ofReal (tsum_nonneg hnonnegA),
      ← ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg d) (tsum_nonneg hnonnegK)),
      ENNReal.ofReal_mul (Nat.cast_nonneg d), ENNReal.ofReal_natCast]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) hchain

  have absNorm_rpow_neg_le_under_sq (σ : Gal(L/K))
      (P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) [P.IsPrime]
      (hPb : P ≠ ⊥) {s : ℝ} (hs : 1 < s) (hdeg : 2 ≤ (P.under (𝓞 K)).inertiaDeg' P) :
      (Ideal.absNorm P : ℝ) ^ (-s) ≤ (Ideal.absNorm (P.under (𝓞 K)) : ℝ) ^ (-(2 : ℝ)) := by
    have hppr : (P.under (𝓞 K)).IsPrime := inferInstance
    have hpbot : P.under (𝓞 K) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPb
    haveI : P.LiesOver (P.under (𝓞 K)) := Ideal.over_under (A := 𝓞 K) (P := P)
    have hpow := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P (P.under (𝓞 K)) hppr hpbot
    have hn2 : 2 ≤ Ideal.absNorm (P.under (𝓞 K)) := by
      have h0 : Ideal.absNorm (P.under (𝓞 K)) ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hpbot
      have h1 : Ideal.absNorm (P.under (𝓞 K)) ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr hppr.ne_top
      omega
    rw [hpow, Nat.cast_pow,
      ← Real.rpow_natCast (Ideal.absNorm (P.under (𝓞 K)) : ℝ) ((P.under (𝓞 K)).inertiaDeg' P),
      ← Real.rpow_mul (by positivity)]
    refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.one_le_of_lt hn2) ?_
    nlinarith [mul_le_mul (show (2 : ℝ) ≤ ((P.under (𝓞 K)).inertiaDeg' P : ℝ) by exact_mod_cast hdeg)
      hs.le (by norm_num) (by positivity : (0 : ℝ) ≤ ((P.under (𝓞 K)).inertiaDeg' P : ℝ))]

  have card_primesOver_le_finrank (σ : Gal(L/K))
      [NoZeroSMulDivisors (𝓞 K) (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))]
      (𝔭 : Ideal (𝓞 K)) [𝔭.IsMaximal] (h𝔭 : 𝔭 ≠ ⊥) :
      Nat.card {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) //
          P.IsPrime ∧ P.LiesOver 𝔭}
        ≤ Module.finrank K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) := by
    letI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
      (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
    rw [show {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) //
          P.IsPrime ∧ P.LiesOver 𝔭}
        = ↥(𝔭.primesOver (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) from rfl,
      Nat.card_coe_set_eq, ← IsDedekindDomain.coe_primesOverFinset h𝔭, Set.ncard_coe_finset]
    exact Ideal.card_primesOverFinset_le_finrank (R := 𝓞 K)
      (S := 𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))
      (K := K) (L := ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) h𝔭

  have primeIdealZetaSum_degTwo_le (σ : Gal(L/K)) {s : ℝ}
      (hs : 1 < s) (Aset : Set (Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))))
      (hA : Aset = {P | P.IsPrime ∧ P ≠ ⊥ ∧
        UnramifiedIn K L (P.under (𝓞 K)) ∧ 2 ≤ (P.under (𝓞 K)).inertiaDeg' P}) :
      primeIdealZetaSum Aset s
        ≤ (Module.finrank K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) : ℝ)
          * primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) 2 := by
    letI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
      (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
    haveI : NoZeroSMulDivisors (𝓞 K)
        (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) :=
      ⟨fun {c x} h ↦ by
        rw [Algebra.smul_def, mul_eq_zero] at h
        exact h.imp (fun h ↦ RingOfIntegers.algebraMap.injective K _ (by rwa [map_zero])) id⟩
    set AP := {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) //
      P ∈ Aset ∧ P.IsPrime ∧ P ≠ ⊥} with hAP
    set KP := {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ (univ : Set (Ideal (𝓞 K))) ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} with hKP
    have hunder : ∀ P : AP, (P.1.under (𝓞 K)).IsPrime ∧ P.1.under (𝓞 K) ≠ ⊥ := by
      rintro ⟨P, hPA, hPp, hPb⟩
      haveI := hPp
      exact ⟨inferInstance, Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPb⟩
    set g : AP → KP := fun P ↦ ⟨P.1.under (𝓞 K), mem_univ _, (hunder P).1, (hunder P).2⟩ with hg
    have hterm : ∀ P : AP, (Ideal.absNorm P.1 : ℝ) ^ (-s)
        ≤ (Ideal.absNorm (g P).1 : ℝ) ^ (-(2 : ℝ)) := by
      rintro ⟨P, hPA, hPp, hPb⟩
      haveI := hPp
      rw [hA] at hPA
      exact absNorm_rpow_neg_le_under_sq σ P hPb hs hPA.2.2.2
    have hinj : ∀ 𝔭 : KP, Finite (g ⁻¹' {𝔭} : Set AP) ∧
        Nat.card (g ⁻¹' {𝔭} : Set AP)
          ≤ Module.finrank K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) := by
      intro 𝔭
      haveI := 𝔭.2.2.1
      haveI : 𝔭.1.IsMaximal := 𝔭.2.2.1.isMaximal 𝔭.2.2.2
      have hmem : ∀ P : (g ⁻¹' {𝔭} : Set AP), P.1.1.IsPrime ∧ P.1.1.LiesOver 𝔭.1 := by
        rintro ⟨⟨P, hPA, hPp, hPb⟩, hgP⟩
        haveI := hPp
        exact ⟨hPp, ⟨(congrArg Subtype.val hgP : P.under (𝓞 K) = 𝔭.1) ▸
          (Ideal.over_under (A := 𝓞 K) (P := P)).over⟩⟩
      set hmap : (g ⁻¹' {𝔭} : Set AP) → {P : Ideal (𝓞 ↥(IntermediateField.fixedField
          (Subgroup.zpowers σ))) // P.IsPrime ∧ P.LiesOver 𝔭.1} := fun P ↦ ⟨P.1.1, hmem P⟩ with hhmap
      have hmapinj : Function.Injective hmap := by
        rintro ⟨⟨P, hP⟩, hgP⟩ ⟨⟨Q, hQ⟩, hgQ⟩ hPQ
        exact Subtype.ext (Subtype.ext (by simpa only [hhmap, Subtype.mk.injEq] using hPQ))
      haveI : Finite {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) //
          P.IsPrime ∧ P.LiesOver 𝔭.1} :=
        (IsDedekindDomain.primesOver_finite 𝔭.1 _).to_subtype
      exact ⟨Finite.of_injective hmap hmapinj, (Nat.card_le_card_of_injective hmap hmapinj).trans
        (card_primesOver_le_finrank σ 𝔭.1 𝔭.2.2.2)⟩
    rw [primeIdealZetaSum, primeIdealZetaSum]
    exact tsum_real_comp_le_card_fibre_mul g _ _ _ ((show ∀ (S : Set (Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))) {s : ℝ}, 1 < s → Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) from by
      intro S s hs
      exact (((show Summable (fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ (Ideal.absNorm I.1 : ℝ) ^ (-s)) from
        (((show HasSum (fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))) (NumberField.dedekindZeta ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) (s : ℂ)) from by
          have hcondition : 1 < ((s : ℂ)).re := (by simpa using hs)
          classical
          haveI (n : ℕ) : Finite {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n} :=
            Set.Finite.to_subtype <| Set.Finite.of_finite_image (f := fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ I.1)
              ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) n).subset (by rintro _ ⟨⟨I, _⟩, rfl, rfl⟩; rfl))
              (fun _ _ _ _ ↦ Subtype.ext)
          have hseries : Summable fun n : ℕ ↦ ‖(idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℂ) * (n : ℂ) ^ (-(s : ℂ))‖ := by
            classical
            have hbig : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) k : ℝ))
                =O[Filter.atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ)) := by
              classical
              have h_finite : ∀ (b : ℕ), {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) | Ideal.absNorm I.1 = b}.Finite := fun b ↦
                Set.Finite.preimage (f := fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ I.1) (fun _ _ _ _ ↦ Subtype.ext)
                  (Ideal.finite_setOf_absNorm_eq (S := 𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) b)
              have h_sum_card : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) k =
                  Nat.card {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 ≤ n} := fun n ↦ by
                have key := Finset.card_preimage_eq_sum_card_image_eq (f := fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦
                  Ideal.absNorm I.1) (s := Finset.Icc 1 n) (fun b _ ↦ h_finite b)
                rw [show ((fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ Ideal.absNorm I.1) ⁻¹' ↑(Finset.Icc 1 n)) =
                    {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) | Ideal.absNorm I.1 ≤ n} by
                  ext ⟨I, hI⟩
                  simp only [Set.mem_preimage, Finset.coe_Icc, Set.mem_Icc, Set.mem_setOf_eq]
                  exact ⟨fun h ↦ h.2, fun h ↦
                    ⟨Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp hI), h⟩⟩] at key
                exact key.symm
              have h_card_bridge : ∀ n : ℕ,
                  Nat.card {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 ≤ n} =
                  Nat.card {I : (Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))⁰ // ((Ideal.absNorm I.1 : ℕ) : ℝ) ≤ (n : ℝ)} :=
                fun n ↦ Nat.card_congr
                  { toFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
                      ⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩, by exact_mod_cast hn⟩
                    invFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
                      ⟨⟨I, mem_nonZeroDivisors_iff_ne_zero.mp hI⟩, by exact_mod_cast hn⟩
                    left_inv := fun _ ↦ rfl
                    right_inv := fun _ ↦ rfl }
              refine Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
                (((NumberField.Ideal.tendsto_norm_le_div_atTop₀ ↥(IntermediateField.fixedField (Subgroup.zpowers σ))).comp
                  tendsto_natCast_atTop_atTop).congr' ?_)
              filter_upwards with n
              simp only [Function.comp_apply, Real.rpow_one]
              rw [← Nat.cast_sum, h_sum_card n, h_card_bridge n]
              push_cast
              rfl
            have h_lss : LSeriesSummable (fun n : ℕ ↦ ((idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℝ) : ℂ)) s :=
              LSeriesSummable_of_sum_norm_bigO_and_nonneg
                (f := fun n ↦ (idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℝ))
                hbig (fun _ ↦ Nat.cast_nonneg _) zero_le_one
                (by exact_mod_cast hcondition)
            have h_term_eq : LSeries.term (fun n : ℕ ↦ ((idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℝ) : ℂ)) (s : ℂ) =
                fun n ↦ (idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) := by
              funext n
              simp only [LSeries.term]
              split_ifs with hn
              · subst hn
                have hzero : idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) 0 = 0 := by
                    unfold idealNormMultiplicity
                    rw [Nat.card_eq_zero]
                    exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩
                simp [hzero]
              · simp [Complex.cpow_neg, div_eq_mul_inv]
            exact (h_term_eq ▸ h_lss :
              Summable fun n ↦ (idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℂ) * (n : ℂ) ^ (-(s : ℂ))).norm
          have hzeta : NumberField.dedekindZeta ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) (s : ℂ) =
              ∑' n : ℕ, (idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) := by
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
              have hzero : idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) 0 = 0 := by
                  unfold idealNormMultiplicity
                  rw [Nat.card_eq_zero]
                  exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩
              simp [hzero, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
            · simp only [hn.ne', ↓reduceIte]
              rw [Complex.cpow_neg, div_eq_mul_inv]
              congr 1
              unfold idealNormMultiplicity
              have hequiv : {I : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) // Ideal.absNorm I = n} ≃
                  {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n} := by
                refine {
                  toFun := fun ⟨I, hI⟩ ↦ ⟨⟨I, ?_⟩, hI⟩
                  invFun := fun ⟨⟨I, _⟩, hI⟩ ↦ ⟨I, hI⟩
                  left_inv := fun _ ↦ rfl
                  right_inv := fun _ ↦ rfl }
                intro h
                rw [h, Ideal.absNorm_bot] at hI
                lia
              exact_mod_cast Nat.card_congr hequiv
          set e := Equiv.sigmaFiberEquiv (fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ Ideal.absNorm I.1)
          have hval : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n},
              (Ideal.absNorm (y.1).1 : ℂ) ^ (-(s : ℂ))) = (idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) :=
            fun n ↦ by
              rw [show (∑' y : {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n},
                  (Ideal.absNorm y.1.1 : ℂ) ^ (-(s : ℂ))) = idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n • (n : ℂ) ^ (-(s : ℂ)) from
                (tsum_congr fun y : {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n} ↦ by rw [y.2]).trans
                  (tsum_const ((n : ℂ) ^ (-(s : ℂ)))), nsmul_eq_mul]
          have hnorm : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n},
              ‖(Ideal.absNorm (y.1).1 : ℂ) ^ (-(s : ℂ))‖) = ‖(idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℂ) * (n : ℂ) ^ (-(s : ℂ))‖ :=
            fun n ↦ by
              rw [show (∑' y : {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n},
                  ‖(Ideal.absNorm y.1.1 : ℂ) ^ (-(s : ℂ))‖) = idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n • ‖(n : ℂ) ^ (-(s : ℂ))‖ from
                (tsum_congr fun y : {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n} ↦ by rw [y.2]).trans
                  (tsum_const ‖(n : ℂ) ^ (-(s : ℂ))‖), nsmul_eq_mul, norm_mul,
                Complex.norm_natCast]
          have hsummable : Summable fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ ‖(Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))‖ := by
            rw [← e.summable_iff]
            refine (summable_sigma_of_nonneg (fun _ ↦ norm_nonneg _)).mpr ⟨fun _ ↦ Summable.of_finite, ?_⟩
            exact hseries.congr fun n ↦ (hnorm n).symm
          have hsummable_sigma : Summable fun p : Σ n, {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n} ↦
              (Ideal.absNorm (e p).1 : ℂ) ^ (-(s : ℂ)) :=
            (e.summable_iff (f := fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ)))).mpr
              hsummable.of_norm
          have hval_sum : (∑' I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)), (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ)))
              = NumberField.dedekindZeta ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) s := by
            rw [hzeta,
              ← e.tsum_eq (fun I ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))), hsummable_sigma.tsum_sigma]
            exact tsum_congr hval
          exact hval_sum ▸ hsummable.of_norm.hasSum)).summable.norm).congr
          fun I ↦ (Complex.norm_natCast_cpow_of_pos
            (Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp I.2)) _).trans <| by simp)).comp_injective
        (i := fun 𝔭 : {𝔭 : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
          (⟨𝔭.1, 𝔭.2.2.2⟩ : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))
        fun _ _ hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab)).congr fun _ ↦ rfl) Aset (by linarith))
      ((show ∀ (S : Set (Ideal (𝓞 K))) {s : ℝ}, 1 < s → Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) from by
        intro S s hs
        exact (((show Summable (fun I : NonzeroIdeal K ↦ (Ideal.absNorm I.1 : ℝ) ^ (-s)) from
          (((show HasSum (fun I : NonzeroIdeal K ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))) (NumberField.dedekindZeta K (s : ℂ)) from by
            have hcondition : 1 < ((s : ℂ)).re := (by simpa using hs)
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
            exact hval_sum ▸ hsummable.of_norm.hasSum)).summable.norm).congr
            fun I ↦ (Complex.norm_natCast_cpow_of_pos
              (Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp I.2)) _).trans <| by simp)).comp_injective
          (i := fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
            (⟨𝔭.1, 𝔭.2.2.2⟩ : NonzeroIdeal K))
          fun _ _ hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab)).congr fun _ ↦ rfl) (univ : Set (Ideal (𝓞 K))) (by norm_num)) (fun _ ↦ by positivity)
      (fun _ ↦ by positivity) hterm (fun 𝔭 ↦ (hinj 𝔭).1) (fun 𝔭 ↦ (hinj 𝔭).2)

  have ramifiedBelow_finite (σ : Gal(L/K))
      (Bset : Set (Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))))
      (hB : Bset = {P | P.IsPrime ∧ P ≠ ⊥ ∧ ¬ UnramifiedIn K L (P.under (𝓞 K))}) :
      Bset.Finite := by
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
    apply Set.Finite.subset (hram.biUnion (t := fun 𝔭 ↦
      (𝔭.primesOver (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))) ?_)
    · rw [hB]
      rintro P ⟨hPp, hPb, hPnu⟩
      haveI := hPp
      exact Set.mem_biUnion ⟨inferInstance, Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPb, hPnu⟩
        ⟨hPp, Ideal.over_under (A := 𝓞 K) (P := P)⟩
    · rintro 𝔭 ⟨hp, hb, -⟩
      haveI := hp
      haveI : 𝔭.IsMaximal := hp.isMaximal hb
      exact IsDedekindDomain.primesOver_finite 𝔭 _
  haveI : IsGalois ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
    IsGalois.tower_top_intermediateField _
  set Aset := {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) |
    P.IsPrime ∧ P ≠ ⊥ ∧ UnramifiedIn K L (P.under (𝓞 K)) ∧
    2 ≤ (P.under (𝓞 K)).inertiaDeg' P} with hAdef
  set Bset := {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) |
    P.IsPrime ∧ P ≠ ⊥ ∧ ¬ UnramifiedIn K L (P.under (𝓞 K))} with hBdef
  have hsub : T₂set ⊆ Aset ∪ Bset := by
    rw [hT₂]
    rintro P ⟨⟨hPp, hPunr, hPfr⟩, hPnotT1⟩
    haveI := hPp
    simp only [Set.mem_setOf_eq, not_and] at hPnotT1
    have hPb : P ≠ ⊥ := (hPunr).1
    by_cases hunrK : UnramifiedIn K L (P.under (𝓞 K))
    · refine Or.inl ⟨hPp, hPb, hunrK, ?_⟩
      have hdegne : (P.under (𝓞 K)).inertiaDeg' P ≠ 1 := fun hdeg1 ↦
        hPnotT1 ⟨hPp, hPunr, hPfr⟩ hdeg1 hunrK
      have hppr : (P.under (𝓞 K)).IsPrime := inferInstance
      haveI : (P.under (𝓞 K)).IsMaximal :=
        hppr.isMaximal (Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPb)
      haveI : P.LiesOver (P.under (𝓞 K)) := Ideal.over_under (A := 𝓞 K) (P := P)
      have hpos : 0 < (P.under (𝓞 K)).inertiaDeg' P := Ideal.inertiaDeg_pos' _ _
      omega
    · exact Or.inr ⟨hPp, hPb, hunrK⟩
  have hdisj : Disjoint Aset Bset := by
    rw [Set.disjoint_left]
    rintro P ⟨-, -, hunrK, -⟩ ⟨-, -, hnunrK⟩
    exact hnunrK hunrK
  have hBfin : Bset.Finite := ramifiedBelow_finite σ Bset hBdef
  refine tendsto_primeIdealZetaSum_div_univ_zero_of_le_const
    (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) T₂set
    ((Module.finrank K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) : ℝ)
        * primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) 2
      + (Nat.card {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) //
          P ∈ Bset ∧ P.IsPrime ∧ P ≠ ⊥} : ℝ)) ?_
  let T : Set (IsDedekindDomain.HeightOneSpectrum
      (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) :=
    {P | P.asIdeal ∈ Bset}
  let e : {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) //
      P ∈ Bset ∧ P.IsPrime ∧ P ≠ ⊥} ≃ T :=
    { toFun := fun P ↦ ⟨⟨P.1, P.2.2.1, P.2.2.2⟩, P.2.1⟩
      invFun := fun P ↦ ⟨P.1.asIdeal, P.2, P.1.isPrime, P.1.ne_bot⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hTfin : T.Finite :=
    hBfin.preimage IsDedekindDomain.HeightOneSpectrum.asIdeal_injective.injOn
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Set.mem_Ioi] at hs
  have hBbound : primeIdealZetaSum Bset s ≤
      (Nat.card {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) //
        P ∈ Bset ∧ P.IsPrime ∧ P ≠ ⊥} : ℝ) := by
    calc
      primeIdealZetaSum Bset s = NumberField.Set.primeIdealZetaSum T s := by
        rw [NumberField.Set.primeIdealZetaSum_def, Chebotarev.primeIdealZetaSum]
        exact e.tsum_eq (fun P : T ↦ (Ideal.absNorm P.1.asIdeal : ℝ) ^ (-s))
      _ ≤ (T.ncard : ℝ) :=
        NumberField.Set.primeIdealZetaSum_le_card_of_finite hTfin (by linarith)
      _ = (Nat.card {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) //
          P ∈ Bset ∧ P.IsPrime ∧ P ≠ ⊥} : ℝ) := by
        exact_mod_cast (Nat.card_congr e).symm
  calc primeIdealZetaSum T₂set s ≤ primeIdealZetaSum (Aset ∪ Bset) s :=
        (show ∀ {S T : Set (Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))}, S ⊆ T → ∀ {s : ℝ}, 1 < s → primeIdealZetaSum S s ≤ primeIdealZetaSum T s from by
          intro S T hST s hs
          rw [primeIdealZetaSum, primeIdealZetaSum]
          refine ((show ∀ (S : Set (Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))) {s : ℝ}, 1 < s → Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) from by
            intro S s hs
            exact (((show Summable (fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ (Ideal.absNorm I.1 : ℝ) ^ (-s)) from
              (((show HasSum (fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))) (NumberField.dedekindZeta ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) (s : ℂ)) from by
                have hcondition : 1 < ((s : ℂ)).re := (by simpa using hs)
                classical
                haveI (n : ℕ) : Finite {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n} :=
                  Set.Finite.to_subtype <| Set.Finite.of_finite_image (f := fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ I.1)
                    ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) n).subset (by rintro _ ⟨⟨I, _⟩, rfl, rfl⟩; rfl))
                    (fun _ _ _ _ ↦ Subtype.ext)
                have hseries : Summable fun n : ℕ ↦ ‖(idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℂ) * (n : ℂ) ^ (-(s : ℂ))‖ := by
                  classical
                  have hbig : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) k : ℝ))
                      =O[Filter.atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ)) := by
                    classical
                    have h_finite : ∀ (b : ℕ), {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) | Ideal.absNorm I.1 = b}.Finite := fun b ↦
                      Set.Finite.preimage (f := fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ I.1) (fun _ _ _ _ ↦ Subtype.ext)
                        (Ideal.finite_setOf_absNorm_eq (S := 𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) b)
                    have h_sum_card : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) k =
                        Nat.card {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 ≤ n} := fun n ↦ by
                      have key := Finset.card_preimage_eq_sum_card_image_eq (f := fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦
                        Ideal.absNorm I.1) (s := Finset.Icc 1 n) (fun b _ ↦ h_finite b)
                      rw [show ((fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ Ideal.absNorm I.1) ⁻¹' ↑(Finset.Icc 1 n)) =
                          {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) | Ideal.absNorm I.1 ≤ n} by
                        ext ⟨I, hI⟩
                        simp only [Set.mem_preimage, Finset.coe_Icc, Set.mem_Icc, Set.mem_setOf_eq]
                        exact ⟨fun h ↦ h.2, fun h ↦
                          ⟨Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp hI), h⟩⟩] at key
                      exact key.symm
                    have h_card_bridge : ∀ n : ℕ,
                        Nat.card {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 ≤ n} =
                        Nat.card {I : (Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))⁰ // ((Ideal.absNorm I.1 : ℕ) : ℝ) ≤ (n : ℝ)} :=
                      fun n ↦ Nat.card_congr
                        { toFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
                            ⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩, by exact_mod_cast hn⟩
                          invFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
                            ⟨⟨I, mem_nonZeroDivisors_iff_ne_zero.mp hI⟩, by exact_mod_cast hn⟩
                          left_inv := fun _ ↦ rfl
                          right_inv := fun _ ↦ rfl }
                    refine Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
                      (((NumberField.Ideal.tendsto_norm_le_div_atTop₀ ↥(IntermediateField.fixedField (Subgroup.zpowers σ))).comp
                        tendsto_natCast_atTop_atTop).congr' ?_)
                    filter_upwards with n
                    simp only [Function.comp_apply, Real.rpow_one]
                    rw [← Nat.cast_sum, h_sum_card n, h_card_bridge n]
                    push_cast
                    rfl
                  have h_lss : LSeriesSummable (fun n : ℕ ↦ ((idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℝ) : ℂ)) s :=
                    LSeriesSummable_of_sum_norm_bigO_and_nonneg
                      (f := fun n ↦ (idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℝ))
                      hbig (fun _ ↦ Nat.cast_nonneg _) zero_le_one
                      (by exact_mod_cast hcondition)
                  have h_term_eq : LSeries.term (fun n : ℕ ↦ ((idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℝ) : ℂ)) (s : ℂ) =
                      fun n ↦ (idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) := by
                    funext n
                    simp only [LSeries.term]
                    split_ifs with hn
                    · subst hn
                      have hzero : idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) 0 = 0 := by
                          unfold idealNormMultiplicity
                          rw [Nat.card_eq_zero]
                          exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩
                      simp [hzero]
                    · simp [Complex.cpow_neg, div_eq_mul_inv]
                  exact (h_term_eq ▸ h_lss :
                    Summable fun n ↦ (idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℂ) * (n : ℂ) ^ (-(s : ℂ))).norm
                have hzeta : NumberField.dedekindZeta ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) (s : ℂ) =
                    ∑' n : ℕ, (idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) := by
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
                    have hzero : idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) 0 = 0 := by
                        unfold idealNormMultiplicity
                        rw [Nat.card_eq_zero]
                        exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩
                    simp [hzero, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
                  · simp only [hn.ne', ↓reduceIte]
                    rw [Complex.cpow_neg, div_eq_mul_inv]
                    congr 1
                    unfold idealNormMultiplicity
                    have hequiv : {I : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) // Ideal.absNorm I = n} ≃
                        {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n} := by
                      refine {
                        toFun := fun ⟨I, hI⟩ ↦ ⟨⟨I, ?_⟩, hI⟩
                        invFun := fun ⟨⟨I, _⟩, hI⟩ ↦ ⟨I, hI⟩
                        left_inv := fun _ ↦ rfl
                        right_inv := fun _ ↦ rfl }
                      intro h
                      rw [h, Ideal.absNorm_bot] at hI
                      lia
                    exact_mod_cast Nat.card_congr hequiv
                set e := Equiv.sigmaFiberEquiv (fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ Ideal.absNorm I.1)
                have hval : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n},
                    (Ideal.absNorm (y.1).1 : ℂ) ^ (-(s : ℂ))) = (idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) :=
                  fun n ↦ by
                    rw [show (∑' y : {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n},
                        (Ideal.absNorm y.1.1 : ℂ) ^ (-(s : ℂ))) = idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n • (n : ℂ) ^ (-(s : ℂ)) from
                      (tsum_congr fun y : {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n} ↦ by rw [y.2]).trans
                        (tsum_const ((n : ℂ) ^ (-(s : ℂ)))), nsmul_eq_mul]
                have hnorm : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n},
                    ‖(Ideal.absNorm (y.1).1 : ℂ) ^ (-(s : ℂ))‖) = ‖(idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℂ) * (n : ℂ) ^ (-(s : ℂ))‖ :=
                  fun n ↦ by
                    rw [show (∑' y : {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n},
                        ‖(Ideal.absNorm y.1.1 : ℂ) ^ (-(s : ℂ))‖) = idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n • ‖(n : ℂ) ^ (-(s : ℂ))‖ from
                      (tsum_congr fun y : {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n} ↦ by rw [y.2]).trans
                        (tsum_const ‖(n : ℂ) ^ (-(s : ℂ))‖), nsmul_eq_mul, norm_mul,
                      Complex.norm_natCast]
                have hsummable : Summable fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ ‖(Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))‖ := by
                  rw [← e.summable_iff]
                  refine (summable_sigma_of_nonneg (fun _ ↦ norm_nonneg _)).mpr ⟨fun _ ↦ Summable.of_finite, ?_⟩
                  exact hseries.congr fun n ↦ (hnorm n).symm
                have hsummable_sigma : Summable fun p : Σ n, {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n} ↦
                    (Ideal.absNorm (e p).1 : ℂ) ^ (-(s : ℂ)) :=
                  (e.summable_iff (f := fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ)))).mpr
                    hsummable.of_norm
                have hval_sum : (∑' I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)), (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ)))
                    = NumberField.dedekindZeta ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) s := by
                  rw [hzeta,
                    ← e.tsum_eq (fun I ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))), hsummable_sigma.tsum_sigma]
                  exact tsum_congr hval
                exact hval_sum ▸ hsummable.of_norm.hasSum)).summable.norm).congr
                fun I ↦ (Complex.norm_natCast_cpow_of_pos
                  (Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp I.2)) _).trans <| by simp)).comp_injective
              (i := fun 𝔭 : {𝔭 : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
                (⟨𝔭.1, 𝔭.2.2.2⟩ : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))
              fun _ _ hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab)).congr fun _ ↦ rfl) S hs).tsum_le_tsum_of_inj
            (fun 𝔭 ↦ ⟨𝔭.1, hST 𝔭.2.1, 𝔭.2.2.1, 𝔭.2.2.2⟩)
            (fun a b hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab))
            (fun c _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
            (fun _ ↦ le_rfl) ((show ∀ (S : Set (Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))) {s : ℝ}, 1 < s → Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) from by
              intro S s hs
              exact (((show Summable (fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ (Ideal.absNorm I.1 : ℝ) ^ (-s)) from
                (((show HasSum (fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))) (NumberField.dedekindZeta ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) (s : ℂ)) from by
                  have hcondition : 1 < ((s : ℂ)).re := (by simpa using hs)
                  classical
                  haveI (n : ℕ) : Finite {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n} :=
                    Set.Finite.to_subtype <| Set.Finite.of_finite_image (f := fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ I.1)
                      ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) n).subset (by rintro _ ⟨⟨I, _⟩, rfl, rfl⟩; rfl))
                      (fun _ _ _ _ ↦ Subtype.ext)
                  have hseries : Summable fun n : ℕ ↦ ‖(idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℂ) * (n : ℂ) ^ (-(s : ℂ))‖ := by
                    classical
                    have hbig : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) k : ℝ))
                        =O[Filter.atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ)) := by
                      classical
                      have h_finite : ∀ (b : ℕ), {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) | Ideal.absNorm I.1 = b}.Finite := fun b ↦
                        Set.Finite.preimage (f := fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ I.1) (fun _ _ _ _ ↦ Subtype.ext)
                          (Ideal.finite_setOf_absNorm_eq (S := 𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) b)
                      have h_sum_card : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) k =
                          Nat.card {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 ≤ n} := fun n ↦ by
                        have key := Finset.card_preimage_eq_sum_card_image_eq (f := fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦
                          Ideal.absNorm I.1) (s := Finset.Icc 1 n) (fun b _ ↦ h_finite b)
                        rw [show ((fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ Ideal.absNorm I.1) ⁻¹' ↑(Finset.Icc 1 n)) =
                            {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) | Ideal.absNorm I.1 ≤ n} by
                          ext ⟨I, hI⟩
                          simp only [Set.mem_preimage, Finset.coe_Icc, Set.mem_Icc, Set.mem_setOf_eq]
                          exact ⟨fun h ↦ h.2, fun h ↦
                            ⟨Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp hI), h⟩⟩] at key
                        exact key.symm
                      have h_card_bridge : ∀ n : ℕ,
                          Nat.card {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 ≤ n} =
                          Nat.card {I : (Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))⁰ // ((Ideal.absNorm I.1 : ℕ) : ℝ) ≤ (n : ℝ)} :=
                        fun n ↦ Nat.card_congr
                          { toFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
                              ⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩, by exact_mod_cast hn⟩
                            invFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
                              ⟨⟨I, mem_nonZeroDivisors_iff_ne_zero.mp hI⟩, by exact_mod_cast hn⟩
                            left_inv := fun _ ↦ rfl
                            right_inv := fun _ ↦ rfl }
                      refine Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
                        (((NumberField.Ideal.tendsto_norm_le_div_atTop₀ ↥(IntermediateField.fixedField (Subgroup.zpowers σ))).comp
                          tendsto_natCast_atTop_atTop).congr' ?_)
                      filter_upwards with n
                      simp only [Function.comp_apply, Real.rpow_one]
                      rw [← Nat.cast_sum, h_sum_card n, h_card_bridge n]
                      push_cast
                      rfl
                    have h_lss : LSeriesSummable (fun n : ℕ ↦ ((idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℝ) : ℂ)) s :=
                      LSeriesSummable_of_sum_norm_bigO_and_nonneg
                        (f := fun n ↦ (idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℝ))
                        hbig (fun _ ↦ Nat.cast_nonneg _) zero_le_one
                        (by exact_mod_cast hcondition)
                    have h_term_eq : LSeries.term (fun n : ℕ ↦ ((idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℝ) : ℂ)) (s : ℂ) =
                        fun n ↦ (idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) := by
                      funext n
                      simp only [LSeries.term]
                      split_ifs with hn
                      · subst hn
                        have hzero : idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) 0 = 0 := by
                            unfold idealNormMultiplicity
                            rw [Nat.card_eq_zero]
                            exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩
                        simp [hzero]
                      · simp [Complex.cpow_neg, div_eq_mul_inv]
                    exact (h_term_eq ▸ h_lss :
                      Summable fun n ↦ (idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℂ) * (n : ℂ) ^ (-(s : ℂ))).norm
                  have hzeta : NumberField.dedekindZeta ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) (s : ℂ) =
                      ∑' n : ℕ, (idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) := by
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
                      have hzero : idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) 0 = 0 := by
                          unfold idealNormMultiplicity
                          rw [Nat.card_eq_zero]
                          exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩
                      simp [hzero, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
                    · simp only [hn.ne', ↓reduceIte]
                      rw [Complex.cpow_neg, div_eq_mul_inv]
                      congr 1
                      unfold idealNormMultiplicity
                      have hequiv : {I : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) // Ideal.absNorm I = n} ≃
                          {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n} := by
                        refine {
                          toFun := fun ⟨I, hI⟩ ↦ ⟨⟨I, ?_⟩, hI⟩
                          invFun := fun ⟨⟨I, _⟩, hI⟩ ↦ ⟨I, hI⟩
                          left_inv := fun _ ↦ rfl
                          right_inv := fun _ ↦ rfl }
                        intro h
                        rw [h, Ideal.absNorm_bot] at hI
                        lia
                      exact_mod_cast Nat.card_congr hequiv
                  set e := Equiv.sigmaFiberEquiv (fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ Ideal.absNorm I.1)
                  have hval : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n},
                      (Ideal.absNorm (y.1).1 : ℂ) ^ (-(s : ℂ))) = (idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) :=
                    fun n ↦ by
                      rw [show (∑' y : {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n},
                          (Ideal.absNorm y.1.1 : ℂ) ^ (-(s : ℂ))) = idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n • (n : ℂ) ^ (-(s : ℂ)) from
                        (tsum_congr fun y : {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n} ↦ by rw [y.2]).trans
                          (tsum_const ((n : ℂ) ^ (-(s : ℂ)))), nsmul_eq_mul]
                  have hnorm : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n},
                      ‖(Ideal.absNorm (y.1).1 : ℂ) ^ (-(s : ℂ))‖) = ‖(idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℂ) * (n : ℂ) ^ (-(s : ℂ))‖ :=
                    fun n ↦ by
                      rw [show (∑' y : {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n},
                          ‖(Ideal.absNorm y.1.1 : ℂ) ^ (-(s : ℂ))‖) = idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n • ‖(n : ℂ) ^ (-(s : ℂ))‖ from
                        (tsum_congr fun y : {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n} ↦ by rw [y.2]).trans
                          (tsum_const ‖(n : ℂ) ^ (-(s : ℂ))‖), nsmul_eq_mul, norm_mul,
                        Complex.norm_natCast]
                  have hsummable : Summable fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ ‖(Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))‖ := by
                    rw [← e.summable_iff]
                    refine (summable_sigma_of_nonneg (fun _ ↦ norm_nonneg _)).mpr ⟨fun _ ↦ Summable.of_finite, ?_⟩
                    exact hseries.congr fun n ↦ (hnorm n).symm
                  have hsummable_sigma : Summable fun p : Σ n, {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n} ↦
                      (Ideal.absNorm (e p).1 : ℂ) ^ (-(s : ℂ)) :=
                    (e.summable_iff (f := fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ)))).mpr
                      hsummable.of_norm
                  have hval_sum : (∑' I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)), (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ)))
                      = NumberField.dedekindZeta ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) s := by
                    rw [hzeta,
                      ← e.tsum_eq (fun I ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))), hsummable_sigma.tsum_sigma]
                    exact tsum_congr hval
                  exact hval_sum ▸ hsummable.of_norm.hasSum)).summable.norm).congr
                  fun I ↦ (Complex.norm_natCast_cpow_of_pos
                    (Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp I.2)) _).trans <| by simp)).comp_injective
                (i := fun 𝔭 : {𝔭 : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
                  (⟨𝔭.1, 𝔭.2.2.2⟩ : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))
                fun _ _ hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab)).congr fun _ ↦ rfl) T hs)) hsub hs
    _ = primeIdealZetaSum Aset s + primeIdealZetaSum Bset s :=
        (show ∀ {S T : Set (Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))}, Disjoint S T → ∀ {s : ℝ}, 1 < s → primeIdealZetaSum (S ∪ T) s = primeIdealZetaSum S s + primeIdealZetaSum T s from by
          intro S T hDisj s hs
          let eS : {𝔭 : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ≃
              ↑{x : {𝔭 : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) // 𝔭 ∈ S ∪ T ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} | (x.1 : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) ∈ S} :=
            { toFun := fun 𝔭 ↦ ⟨⟨𝔭.1, Or.inl 𝔭.2.1, 𝔭.2.2.1, 𝔭.2.2.2⟩, 𝔭.2.1⟩
              invFun := fun x ↦ ⟨x.1.1, x.2, x.1.2.2.1, x.1.2.2.2⟩
              left_inv := fun _ ↦ rfl
              right_inv := fun _ ↦ rfl }
          let eT : {𝔭 : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) // 𝔭 ∈ T ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ≃
              ↑{x : {𝔭 : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) // 𝔭 ∈ S ∪ T ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} | (x.1 : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) ∈ S}ᶜ :=
            { toFun := fun 𝔭 ↦ ⟨⟨𝔭.1, Or.inr 𝔭.2.1, 𝔭.2.2.1, 𝔭.2.2.2⟩,
                fun h ↦ hDisj.le_bot ⟨h, 𝔭.2.1⟩⟩
              invFun := fun x ↦ ⟨x.1.1, x.1.2.1.resolve_left x.2, x.1.2.2.1, x.1.2.2.2⟩
              left_inv := fun _ ↦ rfl
              right_inv := fun _ ↦ rfl }
          rw [primeIdealZetaSum, primeIdealZetaSum, primeIdealZetaSum,
            ← ((show ∀ (S : Set (Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))) {s : ℝ}, 1 < s → Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) from by
              intro S s hs
              exact (((show Summable (fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ (Ideal.absNorm I.1 : ℝ) ^ (-s)) from
                (((show HasSum (fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))) (NumberField.dedekindZeta ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) (s : ℂ)) from by
                  have hcondition : 1 < ((s : ℂ)).re := (by simpa using hs)
                  classical
                  haveI (n : ℕ) : Finite {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n} :=
                    Set.Finite.to_subtype <| Set.Finite.of_finite_image (f := fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ I.1)
                      ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) n).subset (by rintro _ ⟨⟨I, _⟩, rfl, rfl⟩; rfl))
                      (fun _ _ _ _ ↦ Subtype.ext)
                  have hseries : Summable fun n : ℕ ↦ ‖(idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℂ) * (n : ℂ) ^ (-(s : ℂ))‖ := by
                    classical
                    have hbig : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) k : ℝ))
                        =O[Filter.atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ)) := by
                      classical
                      have h_finite : ∀ (b : ℕ), {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) | Ideal.absNorm I.1 = b}.Finite := fun b ↦
                        Set.Finite.preimage (f := fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ I.1) (fun _ _ _ _ ↦ Subtype.ext)
                          (Ideal.finite_setOf_absNorm_eq (S := 𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) b)
                      have h_sum_card : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) k =
                          Nat.card {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 ≤ n} := fun n ↦ by
                        have key := Finset.card_preimage_eq_sum_card_image_eq (f := fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦
                          Ideal.absNorm I.1) (s := Finset.Icc 1 n) (fun b _ ↦ h_finite b)
                        rw [show ((fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ Ideal.absNorm I.1) ⁻¹' ↑(Finset.Icc 1 n)) =
                            {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) | Ideal.absNorm I.1 ≤ n} by
                          ext ⟨I, hI⟩
                          simp only [Set.mem_preimage, Finset.coe_Icc, Set.mem_Icc, Set.mem_setOf_eq]
                          exact ⟨fun h ↦ h.2, fun h ↦
                            ⟨Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp hI), h⟩⟩] at key
                        exact key.symm
                      have h_card_bridge : ∀ n : ℕ,
                          Nat.card {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 ≤ n} =
                          Nat.card {I : (Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))⁰ // ((Ideal.absNorm I.1 : ℕ) : ℝ) ≤ (n : ℝ)} :=
                        fun n ↦ Nat.card_congr
                          { toFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
                              ⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩, by exact_mod_cast hn⟩
                            invFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
                              ⟨⟨I, mem_nonZeroDivisors_iff_ne_zero.mp hI⟩, by exact_mod_cast hn⟩
                            left_inv := fun _ ↦ rfl
                            right_inv := fun _ ↦ rfl }
                      refine Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
                        (((NumberField.Ideal.tendsto_norm_le_div_atTop₀ ↥(IntermediateField.fixedField (Subgroup.zpowers σ))).comp
                          tendsto_natCast_atTop_atTop).congr' ?_)
                      filter_upwards with n
                      simp only [Function.comp_apply, Real.rpow_one]
                      rw [← Nat.cast_sum, h_sum_card n, h_card_bridge n]
                      push_cast
                      rfl
                    have h_lss : LSeriesSummable (fun n : ℕ ↦ ((idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℝ) : ℂ)) s :=
                      LSeriesSummable_of_sum_norm_bigO_and_nonneg
                        (f := fun n ↦ (idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℝ))
                        hbig (fun _ ↦ Nat.cast_nonneg _) zero_le_one
                        (by exact_mod_cast hcondition)
                    have h_term_eq : LSeries.term (fun n : ℕ ↦ ((idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℝ) : ℂ)) (s : ℂ) =
                        fun n ↦ (idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) := by
                      funext n
                      simp only [LSeries.term]
                      split_ifs with hn
                      · subst hn
                        have hzero : idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) 0 = 0 := by
                            unfold idealNormMultiplicity
                            rw [Nat.card_eq_zero]
                            exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩
                        simp [hzero]
                      · simp [Complex.cpow_neg, div_eq_mul_inv]
                    exact (h_term_eq ▸ h_lss :
                      Summable fun n ↦ (idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℂ) * (n : ℂ) ^ (-(s : ℂ))).norm
                  have hzeta : NumberField.dedekindZeta ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) (s : ℂ) =
                      ∑' n : ℕ, (idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) := by
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
                      have hzero : idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) 0 = 0 := by
                          unfold idealNormMultiplicity
                          rw [Nat.card_eq_zero]
                          exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩
                      simp [hzero, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
                    · simp only [hn.ne', ↓reduceIte]
                      rw [Complex.cpow_neg, div_eq_mul_inv]
                      congr 1
                      unfold idealNormMultiplicity
                      have hequiv : {I : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) // Ideal.absNorm I = n} ≃
                          {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n} := by
                        refine {
                          toFun := fun ⟨I, hI⟩ ↦ ⟨⟨I, ?_⟩, hI⟩
                          invFun := fun ⟨⟨I, _⟩, hI⟩ ↦ ⟨I, hI⟩
                          left_inv := fun _ ↦ rfl
                          right_inv := fun _ ↦ rfl }
                        intro h
                        rw [h, Ideal.absNorm_bot] at hI
                        lia
                      exact_mod_cast Nat.card_congr hequiv
                  set e := Equiv.sigmaFiberEquiv (fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ Ideal.absNorm I.1)
                  have hval : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n},
                      (Ideal.absNorm (y.1).1 : ℂ) ^ (-(s : ℂ))) = (idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) :=
                    fun n ↦ by
                      rw [show (∑' y : {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n},
                          (Ideal.absNorm y.1.1 : ℂ) ^ (-(s : ℂ))) = idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n • (n : ℂ) ^ (-(s : ℂ)) from
                        (tsum_congr fun y : {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n} ↦ by rw [y.2]).trans
                          (tsum_const ((n : ℂ) ^ (-(s : ℂ)))), nsmul_eq_mul]
                  have hnorm : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n},
                      ‖(Ideal.absNorm (y.1).1 : ℂ) ^ (-(s : ℂ))‖) = ‖(idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℂ) * (n : ℂ) ^ (-(s : ℂ))‖ :=
                    fun n ↦ by
                      rw [show (∑' y : {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n},
                          ‖(Ideal.absNorm y.1.1 : ℂ) ^ (-(s : ℂ))‖) = idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n • ‖(n : ℂ) ^ (-(s : ℂ))‖ from
                        (tsum_congr fun y : {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n} ↦ by rw [y.2]).trans
                          (tsum_const ‖(n : ℂ) ^ (-(s : ℂ))‖), nsmul_eq_mul, norm_mul,
                        Complex.norm_natCast]
                  have hsummable : Summable fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ ‖(Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))‖ := by
                    rw [← e.summable_iff]
                    refine (summable_sigma_of_nonneg (fun _ ↦ norm_nonneg _)).mpr ⟨fun _ ↦ Summable.of_finite, ?_⟩
                    exact hseries.congr fun n ↦ (hnorm n).symm
                  have hsummable_sigma : Summable fun p : Σ n, {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n} ↦
                      (Ideal.absNorm (e p).1 : ℂ) ^ (-(s : ℂ)) :=
                    (e.summable_iff (f := fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ)))).mpr
                      hsummable.of_norm
                  have hval_sum : (∑' I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)), (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ)))
                      = NumberField.dedekindZeta ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) s := by
                    rw [hzeta,
                      ← e.tsum_eq (fun I ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))), hsummable_sigma.tsum_sigma]
                    exact tsum_congr hval
                  exact hval_sum ▸ hsummable.of_norm.hasSum)).summable.norm).congr
                  fun I ↦ (Complex.norm_natCast_cpow_of_pos
                    (Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp I.2)) _).trans <| by simp)).comp_injective
                (i := fun 𝔭 : {𝔭 : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
                  (⟨𝔭.1, 𝔭.2.2.2⟩ : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))
                fun _ _ hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab)).congr fun _ ↦ rfl) (S ∪ T) hs).tsum_subtype_add_tsum_subtype_compl
              {x | (x.1 : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) ∈ S},
            ← eS.tsum_eq (fun x ↦ (Ideal.absNorm (x.1 : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) : ℝ) ^ (-s)),
            ← eT.tsum_eq (fun x ↦ (Ideal.absNorm (x.1 : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) : ℝ) ^ (-s))]
          rfl) hdisj hs
    _ ≤ _ := add_le_add (primeIdealZetaSum_degTwo_le σ hs Aset hAdef)
        hBbound

end Chebotarev
