/- GID: D5/S3/Factorization/Galois/Chebotarev/FixedFieldDensity
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/Chebotarev/FixedFieldDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Abelian density over a cyclic fixed field lifts to the base conjugacy-class density. -/
module

public import D5.S3.Factorization.Galois.Chebotarev.FixedFieldHigherDegreeTail

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

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]


/-- **Density-lift through the fixed-field subextension** (Sharifi 7.2.2
Step 1, p. 143). Let `σ ∈ Gal(L/K)`, `E = L^⟨σ⟩` the fixed field of the
cyclic subgroup `⟨σ⟩`, and `σ_E ∈ Gal(L/E)` the corresponding element.
Given the abelian-case density over `E` for the Frobenius-fibre of `σ_E`
(value `1/|Gal(L/E)|`), the density over `K` of the Frobenius **class** of
`σ` is `|C|/|G|`.

Source quote (verbatim, p. 143): "δ(S) = … = (f|C|/|G|) δ(T_σ),
recalling once again that `Σ_𝔭 N𝔭^{-s} ~ Σ_P NP^{-s}`. Supposing the
theorem for K/E, we have δ(T_σ) = 1/f, and we therefore obtain δ(S) =
|C|/|G|." Here `f = ord σ = |Gal(L/E)|`, and the counting factor is
`count_primes_above_with_frobenius_eq_sigma`.

The hypothesis `hEfix` records that `E` is the fixed field of `⟨σ⟩`; the
hypothesis `hσE` records that `σ_E` restricts to `σ` over `K` (so `σ_E`
generates `Gal(L/E)` and a prime with `Frob^E_𝔓 = σ_E` has `Frob^K_𝔓 = σ`);
the hypothesis `hab` is the abelian-case output for `L/E` from
`chebotarev_abelian`. -/
theorem density_lift_through_fixedField
    (σ : Gal(L/K)) (E : IntermediateField K L) (σE : Gal(L/E))
    (hσE : letI : IsScalarTower K ↥E L := E.isScalarTower_mid'; σE.restrictScalars K = σ)
    (_hEfix : E = IntermediateField.fixedField (Subgroup.zpowers σ))
    (_hab : HasDirichletDensity
        {P : Ideal (𝓞 ↥E) | P.IsPrime ∧ UnramifiedIn ↥E L P ∧
          frobeniusClass ↥E L P = ConjClasses.mk σE}
        ((Nat.card Gal(L/E) : ℝ)⁻¹)) :
    HasDirichletDensity
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = ConjClasses.mk σ}
      ((Nat.card (ConjClasses.mk σ).carrier : ℝ) / Nat.card Gal(L/K)) := by
  subst _hEfix
  haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
    (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
  haveI : IsMulCommutative Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) :=
    .of_comm fun a b ↦ by
      obtain ⟨x, rfl⟩ := (IntermediateField.subgroupEquivAlgEquiv (Subgroup.zpowers σ)).surjective a
      obtain ⟨y, rfl⟩ := (IntermediateField.subgroupEquivAlgEquiv (Subgroup.zpowers σ)).surjective b
      rw [← map_mul _ x y, ← map_mul _ y x, mul_comm' x y]
  have horderE' :
      orderOf σ = Nat.card Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) :=
    (by rw [← Nat.card_congr
        (IntermediateField.subgroupEquivAlgEquiv (Subgroup.zpowers σ)).toEquiv,
        Nat.card_zpowers] :
      Nat.card Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) = orderOf σ).symm
  set Tset := {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) |
    P.IsPrime ∧ UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P ∧
    frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P
      = ConjClasses.mk σE} with hTset
  set T₁set := {P ∈ Tset | (P.under (𝓞 K)).inertiaDeg' P = 1 ∧ UnramifiedIn K L (P.under (𝓞 K))}
    with hT₁set
  set T₂set := Tset \ T₁set with hT₂set
  have hT₁sub : T₁set ⊆ Tset := fun x hx ↦ hx.1
  have hsplit : ∀ {s : ℝ}, 1 < s → primeIdealZetaSum Tset s
      = primeIdealZetaSum T₁set s + primeIdealZetaSum T₂set s := by
    intro s hs
    rw [(Set.union_sdiff_cancel hT₁sub).symm,
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
        rfl) (Set.disjoint_sdiff_right) hs]
  have hleafB : Tendsto (fun s : ℝ ↦ primeIdealZetaSum T₂set s
      / primeIdealZetaSum (univ : Set (Ideal (𝓞 ↥(IntermediateField.fixedField
        (Subgroup.zpowers σ))))) s) (𝓝[>] 1) (𝓝 0) :=
    primeIdealZetaSum_T2_div_univ_tendsto_zero σ σE T₂set hT₂set
  have htendT₁ : Tendsto (fun s : ℝ ↦ primeIdealZetaSum T₁set s
      / primeIdealZetaSum (univ : Set (Ideal (𝓞 ↥(IntermediateField.fixedField
        (Subgroup.zpowers σ))))) s) (𝓝[>] 1)
      (𝓝 ((Nat.card Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) : ℝ)⁻¹)) := by
    have := _hab.sub hleafB
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [mem_Ioi] at hs
    rw [hsplit hs]
    ring
  rw [HasDirichletDensity]
  have hratio : Tendsto
      (fun s : ℝ ↦ primeIdealZetaSum (univ : Set (Ideal (𝓞 ↥(IntermediateField.fixedField
        (Subgroup.zpowers σ))))) s
          / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s)
      (𝓝[>] 1) (𝓝 1) := by
    have hcancel := (primeIdealZetaSum_univ_tendsto_log
      (↥(IntermediateField.fixedField (Subgroup.zpowers σ)))).div
      (primeIdealZetaSum_univ_tendsto_log K) one_ne_zero
    rw [one_div_one] at hcancel
    refine hcancel.congr' ?_
    have hL : Tendsto (fun s : ℝ ↦ Real.log (1 / (s - 1))) (𝓝[>] (1 : ℝ)) atTop := by
      refine Real.tendsto_log_atTop.comp ?_
      have h1 : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          (((continuous_sub_right 1).tendsto' 1 0 (by ring)).mono_left nhdsWithin_le_nhds)
          (eventually_nhdsWithin_of_forall fun s hs ↦ by
            simp only [Set.mem_Ioi] at hs ⊢
            linarith)
      simpa only [one_div] using! h1.inv_tendsto_nhdsGT_zero
    filter_upwards [hL.eventually_gt_atTop 0] with s hs
    simp only [Pi.div_apply]
    rw [div_div_div_cancel_right₀ hs.ne']
  have hmain : Tendsto
      (fun s : ℝ ↦ ((orderOf σ : ℝ) * Nat.card (ConjClasses.mk σ).carrier / Nat.card Gal(L/K))
        * (primeIdealZetaSum T₁set s
              / primeIdealZetaSum (univ : Set (Ideal (𝓞 ↥(IntermediateField.fixedField
                (Subgroup.zpowers σ))))) s)
          * (primeIdealZetaSum (univ : Set (Ideal (𝓞 ↥(IntermediateField.fixedField
              (Subgroup.zpowers σ))))) s
              / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s))
      (𝓝[>] 1)
      (𝓝 (((orderOf σ : ℝ) * Nat.card (ConjClasses.mk σ).carrier / Nat.card Gal(L/K))
        * (Nat.card Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) : ℝ)⁻¹ * 1)) :=
    ((htendT₁.const_mul _).mul hratio)
  have hval : ((orderOf σ : ℝ) * Nat.card (ConjClasses.mk σ).carrier / Nat.card Gal(L/K))
        * (Nat.card Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) : ℝ)⁻¹ * 1
      = (Nat.card (ConjClasses.mk σ).carrier : ℝ) / Nat.card Gal(L/K) := by
    have hordpos : 0 < orderOf σ := orderOf_pos_iff.mpr (isOfFinOrder_of_finite σ)
    rw [← horderE', mul_one]
    field_simp
  rw [hval] at hmain
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    (primeIdealZetaSum_univ_tendsto_atTop (↥(IntermediateField.fixedField
      (Subgroup.zpowers σ)))).eventually_gt_atTop 0] with s hs hEpos
  simp only [mem_Ioi] at hs
  have hT₁flat : T₁set = {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) |
      P.IsPrime ∧ UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P ∧
      frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P = ConjClasses.mk σE ∧
      (P.under (𝓞 K)).inertiaDeg' P = 1 ∧ UnramifiedIn K L (P.under (𝓞 K))} := by
    rw [hT₁set, hTset]
    ext P
    simp only [Set.mem_setOf_eq]
    tauto
  have hleafA := primeIdealZetaSum_fibre_eq_smul σ σE hσE horderE' hs
  rw [← hT₁flat] at hleafA
  have hc_pos : (0 : ℝ) < orderOf σ * Nat.card (ConjClasses.mk σ).carrier := by
    have h₁ : 0 < orderOf σ := orderOf_pos_iff.mpr (isOfFinOrder_of_finite σ)
    have : Nonempty (ConjClasses.mk σ).carrier := ⟨⟨σ, ConjClasses.mem_carrier_mk⟩⟩
    have h₂ : 0 < Nat.card (ConjClasses.mk σ).carrier := Nat.card_pos
    positivity
  have hG_pos : (0 : ℝ) < Nat.card Gal(L/K) := by exact_mod_cast Nat.card_pos
  have hAB : ((orderOf σ : ℝ) * Nat.card (ConjClasses.mk σ).carrier / Nat.card Gal(L/K))
      * ((Nat.card Gal(L/K) : ℝ) / (orderOf σ * Nat.card (ConjClasses.mk σ).carrier)) = 1 := by
    rw [div_mul_div_comm, mul_comm ((orderOf σ : ℝ) * _), div_self (by positivity)]
  have hSeq : primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
      = ((orderOf σ : ℝ) * Nat.card (ConjClasses.mk σ).carrier / Nat.card Gal(L/K))
        * primeIdealZetaSum T₁set s := by
    rw [hleafA, ← mul_assoc, hAB, one_mul]
  rw [hSeq, mul_assoc ((orderOf σ : ℝ) * Nat.card (ConjClasses.mk σ).carrier / Nat.card Gal(L/K)),
    div_mul_div_cancel₀ hEpos.ne']
  ring

end Chebotarev
