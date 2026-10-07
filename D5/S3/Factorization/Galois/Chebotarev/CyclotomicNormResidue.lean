/- GID: D5/S3/Factorization/Galois/Chebotarev/CyclotomicNormResidue
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/Chebotarev/CyclotomicNormResidue
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coprime-norm Frobenius elements generate the abelian Galois group. -/
module
public import D5.S3.Analytic.Zeta.NumberField.CoprimePrimeSum
public import D5.S3.Factorization.Galois.Chebotarev.Frobenius
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
/-!
# Coprime-norm Frobenius generation
Coprime-norm unramified prime sums have the universal logarithmic asymptotic.
Native splitting counts and norm identities in the fixed field yield a field-degree
comparison. Passing to the logarithmic limit forces the fixed field to have degree one,
so a subgroup containing all qualifying Frobenius representatives is the whole Galois group.
-/
@[expose] public section

noncomputable section

namespace Chebotarev

open NumberField
open scoped Pointwise nonZeroDivisors

/-! ### Coprime-restricted Frobenii generation

The κ-uniformity transfer in `ZetaProduct.lean` realizes only the residues that are *coprime-norm
ideal Frobenius* values, so it needs Frobenius generation with the Frobenius
hypothesis restricted to primes of **coprime norm** (`(N𝔭).Coprime m`). The proof is the same
fixed-field zeta comparison, but the `K`-side prime sum runs only over coprime-norm unramified
primes; the excluded primes (unramified but with `¬(N𝔭).Coprime m`) form a **finite** set (they
all divide the fixed ideal `(m)`), so the comparison ratio still tends to `1`. The finiteness
argument and the restricted log-asymptotic
feed the field-degree comparison. -/

section CoprimeRestrictedComparison

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (m : ℕ) [NeZero m]


set_option maxHeartbeats 800000 in
/-- **Coprime-restricted bound on the fixed-field degree.** The coprime-norm analog of
`finrank_fixedField_le_one_of_forall_frobenius_mem`: with the Frobenius hypothesis required only
on coprime-norm unramified primes, `[F:K] ≤ 1`. Same proof, dividing the coprime-restricted
comparison by `log(1/(s-1))` and passing to the limit; the coprime-restricted `K`-side ratio
tends to `1` by `primeIdealZetaSum_unramified_coprime_div_log_tendsto_one`. -/
private theorem finrank_fixedField_le_one_of_forall_frobenius_mem_of_coprime
    [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K))
    (hH : ∀ 𝔭 : Ideal (𝓞 K), ∀ _ : 𝔭.IsPrime, 𝔭 ≠ ⊥ → UnramifiedIn K L 𝔭 →
      (Ideal.absNorm 𝔭).Coprime m → ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H) :
    Module.finrank K (IntermediateField.fixedField H) ≤ 1 := by
  set F := IntermediateField.fixedField H
  haveI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup H
  haveI : NumberField F := NumberField.of_intermediateField F
  set d : ℕ := Module.finrank K ↥F
  rw [← Nat.cast_le (α := ℝ), Nat.cast_one]
  set A : ℝ → ℝ := fun s ↦ primeIdealZetaSum
    {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ (Ideal.absNorm 𝔭).Coprime m} s
  set B : ℝ → ℝ := fun s ↦
    primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 ↥F))) s
  have hAtend : Filter.Tendsto (fun s ↦ A s / Real.log (1 / (s - 1)))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) :=
    primeIdealZetaSum_unramified_coprime_div_log_tendsto_one K L m
  have hBtend : Filter.Tendsto (fun s ↦ B s / Real.log (1 / (s - 1)))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) :=
    primeIdealZetaSum_univ_tendsto_log (↥F)
  have hLpos : ∀ᶠ s in nhdsWithin 1 (Set.Ioi 1), 0 < Real.log (1 / (s - 1)) :=
    (show Filter.Tendsto (fun s : ℝ ↦ Real.log (1 / (s - 1)))
        (nhdsWithin 1 (Set.Ioi 1)) Filter.atTop from by
      refine Real.tendsto_log_atTop.comp ?_
      have h1 : Filter.Tendsto (fun s : ℝ ↦ s - 1)
          (nhdsWithin 1 (Set.Ioi 1)) (nhdsWithin 0 (Set.Ioi 0)) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          (((continuous_sub_right 1).tendsto' 1 0 (by ring)).mono_left nhdsWithin_le_nhds)
          (eventually_nhdsWithin_of_forall fun s hs ↦ by
            simp only [Set.mem_Ioi] at hs ⊢
            linarith)
      simpa only [one_div] using! h1.inv_tendsto_nhdsGT_zero).eventually_gt_atTop 0
  have hNonzeroIdealNormSummable :
      (∀ {s : ℝ}, 1 < s →
        Summable (fun I : NonzeroIdeal K ↦ (Ideal.absNorm I.1 : ℝ) ^ (-s))) ∧
      (∀ (M : IntermediateField K L) {s : ℝ}, 1 < s →
        Summable (fun I : NonzeroIdeal (↥M) ↦ (Ideal.absNorm I.1 : ℝ) ^ (-s))) := by
    constructor
    all_goals
      first
      | intro s hs
        let N := K
        change Summable (fun I : NonzeroIdeal N ↦ (Ideal.absNorm I.1 : ℝ) ^ (-s))
      | intro M s hs
        let N := (↥M)
        letI : NumberField N := NumberField.of_intermediateField M
        change Summable (fun I : NonzeroIdeal N ↦ (Ideal.absNorm I.1 : ℝ) ^ (-s))
      exact (show Summable (fun I : NonzeroIdeal N ↦ (Ideal.absNorm I.1 : ℝ) ^ (-s)) from
    (((show HasSum (fun I : NonzeroIdeal N ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))) (NumberField.dedekindZeta N (s : ℂ)) from by
      have hcondition : 1 < ((s : ℂ)).re := (by simpa using hs)
      classical
      haveI (n : ℕ) : Finite {I : NonzeroIdeal N // Ideal.absNorm I.1 = n} :=
        Set.Finite.to_subtype <| Set.Finite.of_finite_image (f := fun I : NonzeroIdeal N ↦ I.1)
          ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 N) n).subset (by rintro _ ⟨⟨I, _⟩, rfl, rfl⟩; rfl))
          (fun _ _ _ _ ↦ Subtype.ext)
      have hseries : Summable fun n : ℕ ↦ ‖(idealNormMultiplicity N n : ℂ) * (n : ℂ) ^ (-(s : ℂ))‖ := by
        classical
        have hbig : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (idealNormMultiplicity N k : ℝ))
            =O[Filter.atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ)) := by
          classical
          have h_finite : ∀ (b : ℕ), {I : NonzeroIdeal N | Ideal.absNorm I.1 = b}.Finite := fun b ↦
            Set.Finite.preimage (f := fun I : NonzeroIdeal N ↦ I.1) (fun _ _ _ _ ↦ Subtype.ext)
              (Ideal.finite_setOf_absNorm_eq (S := 𝓞 N) b)
          have h_sum_card : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, idealNormMultiplicity N k =
              Nat.card {I : NonzeroIdeal N // Ideal.absNorm I.1 ≤ n} := fun n ↦ by
            have key := Finset.card_preimage_eq_sum_card_image_eq (f := fun I : NonzeroIdeal N ↦
              Ideal.absNorm I.1) (s := Finset.Icc 1 n) (fun b _ ↦ h_finite b)
            rw [show ((fun I : NonzeroIdeal N ↦ Ideal.absNorm I.1) ⁻¹' ↑(Finset.Icc 1 n)) =
                {I : NonzeroIdeal N | Ideal.absNorm I.1 ≤ n} by
              ext ⟨I, hI⟩
              simp only [Set.mem_preimage, Finset.coe_Icc, Set.mem_Icc, Set.mem_setOf_eq]
              exact ⟨fun h ↦ h.2, fun h ↦
                ⟨Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp hI), h⟩⟩] at key
            exact key.symm
          have h_card_bridge : ∀ n : ℕ,
              Nat.card {I : NonzeroIdeal N // Ideal.absNorm I.1 ≤ n} =
              Nat.card {I : (Ideal (𝓞 N))⁰ // ((Ideal.absNorm I.1 : ℕ) : ℝ) ≤ (n : ℝ)} :=
            fun n ↦ Nat.card_congr
              { toFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
                  ⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩, by exact_mod_cast hn⟩
                invFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
                  ⟨⟨I, mem_nonZeroDivisors_iff_ne_zero.mp hI⟩, by exact_mod_cast hn⟩
                left_inv := fun _ ↦ rfl
                right_inv := fun _ ↦ rfl }
          refine Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
            (((NumberField.Ideal.tendsto_norm_le_div_atTop₀ N).comp
              tendsto_natCast_atTop_atTop).congr' ?_)
          filter_upwards with n
          simp only [Function.comp_apply, Real.rpow_one]
          rw [← Nat.cast_sum, h_sum_card n, h_card_bridge n]
          push_cast
          rfl
        have h_lss : LSeriesSummable (fun n : ℕ ↦ ((idealNormMultiplicity N n : ℝ) : ℂ)) s :=
          LSeriesSummable_of_sum_norm_bigO_and_nonneg
            (f := fun n ↦ (idealNormMultiplicity N n : ℝ))
            hbig (fun _ ↦ Nat.cast_nonneg _) zero_le_one
            (by exact_mod_cast hcondition)
        have h_term_eq : LSeries.term (fun n : ℕ ↦ ((idealNormMultiplicity N n : ℝ) : ℂ)) (s : ℂ) =
            fun n ↦ (idealNormMultiplicity N n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) := by
          funext n
          simp only [LSeries.term]
          split_ifs with hn
          · subst hn
            have hzero : idealNormMultiplicity N 0 = 0 := by
                unfold idealNormMultiplicity
                rw [Nat.card_eq_zero]
                exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩
            simp [hzero]
          · simp [Complex.cpow_neg, div_eq_mul_inv]
        exact (h_term_eq ▸ h_lss :
          Summable fun n ↦ (idealNormMultiplicity N n : ℂ) * (n : ℂ) ^ (-(s : ℂ))).norm
      have hzeta : NumberField.dedekindZeta N (s : ℂ) =
          ∑' n : ℕ, (idealNormMultiplicity N n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) := by
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
          have hzero : idealNormMultiplicity N 0 = 0 := by
              unfold idealNormMultiplicity
              rw [Nat.card_eq_zero]
              exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩
          simp [hzero, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
        · simp only [hn.ne', ↓reduceIte]
          rw [Complex.cpow_neg, div_eq_mul_inv]
          congr 1
          unfold idealNormMultiplicity
          have hequiv : {I : Ideal (𝓞 N) // Ideal.absNorm I = n} ≃
              {I : NonzeroIdeal N // Ideal.absNorm I.1 = n} := by
            refine {
              toFun := fun ⟨I, hI⟩ ↦ ⟨⟨I, ?_⟩, hI⟩
              invFun := fun ⟨⟨I, _⟩, hI⟩ ↦ ⟨I, hI⟩
              left_inv := fun _ ↦ rfl
              right_inv := fun _ ↦ rfl }
            intro h
            rw [h, Ideal.absNorm_bot] at hI
            lia
          exact_mod_cast Nat.card_congr hequiv
      set e := Equiv.sigmaFiberEquiv (fun I : NonzeroIdeal N ↦ Ideal.absNorm I.1)
      have hval : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal N // Ideal.absNorm I.1 = n},
          (Ideal.absNorm (y.1).1 : ℂ) ^ (-(s : ℂ))) = (idealNormMultiplicity N n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) :=
        fun n ↦ by
          rw [show (∑' y : {I : NonzeroIdeal N // Ideal.absNorm I.1 = n},
              (Ideal.absNorm y.1.1 : ℂ) ^ (-(s : ℂ))) = idealNormMultiplicity N n • (n : ℂ) ^ (-(s : ℂ)) from
            (tsum_congr fun y : {I : NonzeroIdeal N // Ideal.absNorm I.1 = n} ↦ by rw [y.2]).trans
              (tsum_const ((n : ℂ) ^ (-(s : ℂ)))), nsmul_eq_mul]
      have hnorm : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal N // Ideal.absNorm I.1 = n},
          ‖(Ideal.absNorm (y.1).1 : ℂ) ^ (-(s : ℂ))‖) = ‖(idealNormMultiplicity N n : ℂ) * (n : ℂ) ^ (-(s : ℂ))‖ :=
        fun n ↦ by
          rw [show (∑' y : {I : NonzeroIdeal N // Ideal.absNorm I.1 = n},
              ‖(Ideal.absNorm y.1.1 : ℂ) ^ (-(s : ℂ))‖) = idealNormMultiplicity N n • ‖(n : ℂ) ^ (-(s : ℂ))‖ from
            (tsum_congr fun y : {I : NonzeroIdeal N // Ideal.absNorm I.1 = n} ↦ by rw [y.2]).trans
              (tsum_const ‖(n : ℂ) ^ (-(s : ℂ))‖), nsmul_eq_mul, norm_mul,
            Complex.norm_natCast]
      have hsummable : Summable fun I : NonzeroIdeal N ↦ ‖(Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))‖ := by
        rw [← e.summable_iff]
        refine (summable_sigma_of_nonneg (fun _ ↦ norm_nonneg _)).mpr ⟨fun _ ↦ Summable.of_finite, ?_⟩
        exact hseries.congr fun n ↦ (hnorm n).symm
      have hsummable_sigma : Summable fun p : Σ n, {I : NonzeroIdeal N // Ideal.absNorm I.1 = n} ↦
          (Ideal.absNorm (e p).1 : ℂ) ^ (-(s : ℂ)) :=
        (e.summable_iff (f := fun I : NonzeroIdeal N ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ)))).mpr
          hsummable.of_norm
      have hval_sum : (∑' I : NonzeroIdeal N, (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ)))
          = NumberField.dedekindZeta N s := by
        rw [hzeta,
          ← e.tsum_eq (fun I ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))), hsummable_sigma.tsum_sigma]
        exact tsum_congr hval
      exact hval_sum ▸ hsummable.of_norm.hasSum)).summable.norm).congr
      fun I ↦ (Complex.norm_natCast_cpow_of_pos
        (Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp I.2)) _).trans <| by simp)
  have hev : ∀ᶠ s in nhdsWithin 1 (Set.Ioi 1),
      (d : ℝ) * (A s / Real.log (1 / (s - 1))) ≤ B s / Real.log (1 / (s - 1)) := by
    filter_upwards [hLpos, self_mem_nhdsWithin] with s hLs hs1
    simp only [Set.mem_Ioi] at hs1
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right ((show ∀ [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K))
        (hH : ∀ 𝔭 : Ideal (𝓞 K), ∀ _ : 𝔭.IsPrime, 𝔭 ≠ ⊥ → UnramifiedIn K L 𝔭 →
          (Ideal.absNorm 𝔭).Coprime m → ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H)
        {s : ℝ} (hs : 1 < s), ((Module.finrank K ↥(IntermediateField.fixedField H) : ℝ) * primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ (Ideal.absNorm 𝔭).Coprime m} s ≤ primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 ↥(IntermediateField.fixedField H)))) s) from by
      intro cnrInstance0 H hH s hs
      set F := IntermediateField.fixedField H
      haveI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup H
      haveI : NumberField F := NumberField.of_intermediateField F
      have hsplit : ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → UnramifiedIn K L 𝔭 → (Ideal.absNorm 𝔭).Coprime m →
          Nat.card {𝔮 : Ideal (𝓞 F) // 𝔮.IsPrime ∧ 𝔮.LiesOver 𝔭 ∧ 𝔮 ≠ ⊥} = Module.finrank K ↥F
            ∧ ∀ 𝔮 : Ideal (𝓞 F), 𝔮.IsPrime → 𝔮.LiesOver 𝔭 → Ideal.absNorm 𝔮 = Ideal.absNorm 𝔭 :=
        fun 𝔭 h𝔭p h𝔭unr h𝔭cop ↦
          ⟨(show ∀      
              [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K))
              (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
              (hmem : ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H), (Nat.card {𝔮 : Ideal (𝓞 ↥(IntermediateField.fixedField H)) // 𝔮.IsPrime ∧ 𝔮.LiesOver 𝔭 ∧ 𝔮 ≠ ⊥} = Module.finrank K ↥(IntermediateField.fixedField H)) from by
            intro cnrInstance0 H 𝔭 cnrInstance1 hunr hmem
            set F := IntermediateField.fixedField H
            haveI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup H
            haveI : NumberField F := NumberField.of_intermediateField F
            have hunrF : UnramifiedIn K (↥F) 𝔭 := (show ∀      
                (F : IntermediateField K L) [IsGalois K F]
                (𝔭 : Ideal (𝓞 K)) (hunr : UnramifiedIn K L 𝔭), (UnramifiedIn K (↥F) 𝔭) from by
              intro F cnrInstance0 𝔭 hunr
              haveI : IsScalarTower K F L := F.isScalarTower_mid'
              haveI : IsScalarTower (𝓞 K) (𝓞 F) (𝓞 L) := inferInstance
              refine ⟨hunr.1, fun 𝔮 h𝔮max h𝔮lo ↦ ?_⟩
              haveI := h𝔮lo
              haveI := h𝔮max.isPrime
              obtain ⟨𝔓, h𝔓prime, hcomap⟩ :=
                Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 L) 𝔮 (by
                  rw [(RingHom.injective_iff_ker_eq_bot _).mp
                    (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 L))]
                  exact bot_le)
              have h𝔓lo : 𝔓.LiesOver 𝔮 := ⟨hcomap.symm⟩
              haveI := h𝔓prime
              haveI := h𝔓lo
              haveI : 𝔓.LiesOver 𝔭 := ⟨by rw [← Ideal.under_under (B := 𝓞 F) 𝔓, h𝔓lo.over.symm, h𝔮lo.over.symm]⟩
              haveI : Algebra.IsUnramifiedAt (𝓞 K) 𝔓 :=
                hunr.2 𝔓 (h𝔓prime.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓)) inferInstance
              exact Algebra.IsUnramifiedAt.of_liesOver (𝓞 K) 𝔮 𝔓) F 𝔭 hunr
            have hresdeg := (show ∀      
                [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K))
                (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
                (hmem : ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H), (haveI : IsGalois K (IntermediateField.fixedField H) := IsGalois.of_fixedField_normal_subgroup H; haveI : NumberField (IntermediateField.fixedField H) := NumberField.of_intermediateField _; ∀ 𝔮 : Ideal (𝓞 ↥(IntermediateField.fixedField H)), 𝔮.IsPrime → 𝔮.LiesOver 𝔭 → Module.finrank (𝓞 K ⧸ 𝔮.under (𝓞 K)) (𝓞 ↥(IntermediateField.fixedField H) ⧸ 𝔮) = 1) from by
              intro cnrInstance0 H 𝔭 cnrInstance1 hunr hmem
              set F := IntermediateField.fixedField H
              haveI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup H
              haveI : NumberField F := NumberField.of_intermediateField F
              have hunrF : UnramifiedIn K (↥F) 𝔭 := (show ∀      
                  (F : IntermediateField K L) [IsGalois K F]
                  (𝔭 : Ideal (𝓞 K)) (hunr : UnramifiedIn K L 𝔭), (UnramifiedIn K (↥F) 𝔭) from by
                intro F cnrInstance0 𝔭 hunr
                haveI : IsScalarTower K F L := F.isScalarTower_mid'
                haveI : IsScalarTower (𝓞 K) (𝓞 F) (𝓞 L) := inferInstance
                refine ⟨hunr.1, fun 𝔮 h𝔮max h𝔮lo ↦ ?_⟩
                haveI := h𝔮lo
                haveI := h𝔮max.isPrime
                obtain ⟨𝔓, h𝔓prime, hcomap⟩ :=
                  Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 L) 𝔮 (by
                    rw [(RingHom.injective_iff_ker_eq_bot _).mp
                      (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 L))]
                    exact bot_le)
                have h𝔓lo : 𝔓.LiesOver 𝔮 := ⟨hcomap.symm⟩
                haveI := h𝔓prime
                haveI := h𝔓lo
                haveI : 𝔓.LiesOver 𝔭 := ⟨by rw [← Ideal.under_under (B := 𝓞 F) 𝔓, h𝔓lo.over.symm, h𝔮lo.over.symm]⟩
                haveI : Algebra.IsUnramifiedAt (𝓞 K) 𝔓 :=
                  hunr.2 𝔓 (h𝔓prime.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓)) inferInstance
                exact Algebra.IsUnramifiedAt.of_liesOver (𝓞 K) 𝔮 𝔓) F 𝔭 hunr
              have hfc : frobeniusClass K (↥F) 𝔭 = ConjClasses.mk (1 : Gal(↥F/K)) :=
                (show ∀      
                    [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K))
                    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
                    (hmem : ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H), (haveI : IsGalois K (IntermediateField.fixedField H) := IsGalois.of_fixedField_normal_subgroup H; frobeniusClass K (↥(IntermediateField.fixedField H)) 𝔭 = ConjClasses.mk 1) from by
                  intro cnrInstance0 H 𝔭 cnrInstance1 hunr hmem
                  set F := IntermediateField.fixedField H with hF
                  haveI : IsScalarTower K F L := F.isScalarTower_mid'
                  haveI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup H
                  haveI : NumberField F := NumberField.of_intermediateField F
                  letI : FaithfulSMul Gal(↥F/K) (𝓞 F) := IsGaloisGroup.faithful (𝓞 K)
                  obtain ⟨𝔓, h𝔓p, hcomap⟩ :=
                    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 L) 𝔭 (by
                      rw [(RingHom.injective_iff_ker_eq_bot _).mp
                        (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))]
                      exact bot_le)
                  have h𝔓lo : 𝔓.LiesOver 𝔭 := ⟨hcomap.symm⟩
                  haveI := h𝔓p
                  haveI := h𝔓lo
                  haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓
                    (Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓)
                  set σ : L ≃ₐ[K] L := arithFrobAt (𝓞 K) Gal(L/K) 𝔓
                  have hclass : frobeniusClass K L 𝔭 = ConjClasses.mk σ := by
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
                    change ConjClasses.mk (arithFrobAt (𝓞 K) Gal(L/K) 𝔓₀) = ConjClasses.mk σ
                    exact ConjClasses.mk_eq_mk_iff_isConj.mpr <|
                      isConj_arithFrobAt (𝓞 K) Gal(L/K) 𝔓₀ 𝔓 (hlo₀.over.symm.trans h𝔓lo.over)
                  have hconj : IsConj σ ((frobeniusClass K L 𝔭).out) := by
                    have hout : ConjClasses.mk ((frobeniusClass K L 𝔭).out) =
                        frobeniusClass K L 𝔭 := Quotient.out_eq _
                    exact ConjClasses.mk_eq_mk_iff_isConj.mp (hclass.symm.trans hout.symm)
                  have hσeq : σ = (frobeniusClass K L 𝔭).out := by
                    obtain ⟨c, hc⟩ := hconj
                    rw [SemiconjBy, mul_comm' (c : Gal(L/K)) σ] at hc
                    exact mul_right_cancel hc
                  have hσfix : σ ∈ F.fixingSubgroup := by
                    rw [hF, IntermediateField.fixingSubgroup_fixedField]
                    exact hσeq ▸ hmem
                  have hrestr : σ.restrictNormal F = 1 :=
                    MonoidHom.mem_ker.mp <| (IntermediateField.restrictNormalHom_ker F).ge hσfix
                  have h𝔮lo : (𝔓.under (𝓞 F)).LiesOver 𝔭 :=
                    ⟨by rw [← Ideal.under_under (B := 𝓞 F) 𝔓]; exact h𝔓lo.over⟩
                  haveI := h𝔮lo
                  have hfrobF : IsArithFrobAt (𝓞 K) (σ.restrictNormal F) (𝔓.under (𝓞 F)) :=
                    (show ∀      
                        (F : IntermediateField K L) [IsGalois K F] (σ : L ≃ₐ[K] L)
                        (𝔓 : Ideal (𝓞 L)) (hσ : IsArithFrobAt (𝓞 K) σ 𝔓), (haveI : IsScalarTower K F L := F.isScalarTower_mid'; IsArithFrobAt (𝓞 K) (σ.restrictNormal F) (𝔓.under (𝓞 F))) from by
                      intro F cnrInstance0 σ 𝔓 hσ
                      haveI : IsScalarTower K F L := F.isScalarTower_mid'
                      intro y
                      have hsmul : σ • (algebraMap (𝓞 F) (𝓞 L) y) =
                          algebraMap (𝓞 F) (𝓞 L) ((σ.restrictNormal F) • y) := by
                        have hbridgeL : ∀ (g : L ≃ₐ[K] L) (x : 𝓞 L), ((g • x : 𝓞 L) : L) = g • (x : L) :=
                          fun g x ↦ by simpa [Algebra.smul_def] using
                            (smul_distrib_smul (G := L ≃ₐ[K] L) (R := 𝓞 L) (S := L) g x 1).symm
                        have hbridgeF : ∀ (g : F ≃ₐ[K] F) (z : 𝓞 F), ((g • z : 𝓞 F) : F) = g • (z : F) :=
                          fun g z ↦ by simpa [Algebra.smul_def] using
                            (smul_distrib_smul (G := F ≃ₐ[K] F) (R := 𝓞 F) (S := F) g z 1).symm
                        have hcoe : ∀ z : 𝓞 F,
                            ((algebraMap (𝓞 F) (𝓞 L) z : 𝓞 L) : L) = algebraMap F L (z : F) :=
                          fun z ↦ by
                            rw [RingOfIntegers.coe_eq_algebraMap,
                              ← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 L) L,
                              RingOfIntegers.coe_eq_algebraMap, ← IsScalarTower.algebraMap_apply (𝓞 F) F L]
                        rw [RingOfIntegers.ext_iff]
                        change ((σ • algebraMap (𝓞 F) (𝓞 L) y : 𝓞 L) : L) =
                            ((algebraMap (𝓞 F) (𝓞 L) ((σ.restrictNormal F) • y) : 𝓞 L) : L)
                        rw [hbridgeL, hcoe y, hcoe ((σ.restrictNormal F) • y), hbridgeF,
                          AlgEquiv.smul_def, AlgEquiv.smul_def, AlgEquiv.restrictNormal_commutes]
                      rw [Ideal.under_under 𝔓, Ideal.under, Ideal.mem_comap, map_sub, map_pow,
                        show (MulSemiringAction.toAlgHom (𝓞 K) (𝓞 F) (σ.restrictNormal F)) y
                            = (σ.restrictNormal F) • y from rfl, ← hsmul]
                      exact hσ (algebraMap (𝓞 F) (𝓞 L) y)) F σ 𝔓 (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓)
                  have hunrF := (show ∀      
                      (F : IntermediateField K L) [IsGalois K F]
                      (𝔭 : Ideal (𝓞 K)) (hunr : UnramifiedIn K L 𝔭), (UnramifiedIn K (↥F) 𝔭) from by
                    intro F cnrInstance0 𝔭 hunr
                    haveI : IsScalarTower K F L := F.isScalarTower_mid'
                    haveI : IsScalarTower (𝓞 K) (𝓞 F) (𝓞 L) := inferInstance
                    refine ⟨hunr.1, fun 𝔮 h𝔮max h𝔮lo ↦ ?_⟩
                    haveI := h𝔮lo
                    haveI := h𝔮max.isPrime
                    obtain ⟨𝔓, h𝔓prime, hcomap⟩ :=
                      Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 L) 𝔮 (by
                        rw [(RingHom.injective_iff_ker_eq_bot _).mp
                          (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 L))]
                        exact bot_le)
                    have h𝔓lo : 𝔓.LiesOver 𝔮 := ⟨hcomap.symm⟩
                    haveI := h𝔓prime
                    haveI := h𝔓lo
                    haveI : 𝔓.LiesOver 𝔭 := ⟨by rw [← Ideal.under_under (B := 𝓞 F) 𝔓, h𝔓lo.over.symm, h𝔮lo.over.symm]⟩
                    haveI : Algebra.IsUnramifiedAt (𝓞 K) 𝔓 :=
                      hunr.2 𝔓 (h𝔓prime.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓)) inferInstance
                    exact Algebra.IsUnramifiedAt.of_liesOver (𝓞 K) 𝔮 𝔓) F 𝔭 hunr
                  have hclassF : frobeniusClass K (↥F) 𝔭 =
                      ConjClasses.mk (σ.restrictNormal F) := by
                    let e : ∃ 𝔮₀ : Ideal (𝓞 F), 𝔮₀.IsPrime ∧ 𝔮₀.LiesOver 𝔭 := by
                      obtain ⟨𝔮₀, hq₀, hcomap₀⟩ :=
                        Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 F) 𝔭 (by
                          rw [(RingHom.injective_iff_ker_eq_bot _).mp
                            (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 F))]
                          exact bot_le)
                      exact ⟨𝔮₀, hq₀, ⟨hcomap₀.symm⟩⟩
                    let 𝔮₀ := Classical.choose e
                    haveI : 𝔮₀.IsPrime := (Classical.choose_spec e).1
                    have hq₀lo : 𝔮₀.LiesOver 𝔭 := (Classical.choose_spec e).2
                    haveI : Finite (𝓞 F ⧸ 𝔮₀) := Ideal.finiteQuotientOfFreeOfNeBot 𝔮₀
                      (Ideal.ne_bot_of_liesOver_of_ne_bot hunrF.1 𝔮₀)
                    haveI : (𝔓.under (𝓞 F)).IsPrime := inferInstance
                    have hqbot := Ideal.ne_bot_of_liesOver_of_ne_bot hunrF.1 (𝔓.under (𝓞 F))
                    haveI : Finite (𝓞 F ⧸ 𝔓.under (𝓞 F)) :=
                      Ideal.finiteQuotientOfFreeOfNeBot _ hqbot
                    haveI : Algebra.IsUnramifiedAt (𝓞 K) (𝔓.under (𝓞 F)) :=
                      hunrF.2 _ (‹(𝔓.under (𝓞 F)).IsPrime›.isMaximal hqbot) h𝔮lo
                    have heq : σ.restrictNormal F =
                        arithFrobAt (𝓞 K) Gal(↥F/K) (𝔓.under (𝓞 F)) :=
                      MulSemiringAction.toAlgHom_injective (𝓞 K) (𝓞 F) <|
                        AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt hfrobF
                          (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(↥F/K) (𝔓.under (𝓞 F)))
                          (𝔓.under (𝓞 F)).primeCompl_le_nonZeroDivisors
                    rw [frobeniusClass, dif_pos ⟨‹𝔭.IsPrime›, hunrF⟩]
                    change ConjClasses.mk (arithFrobAt (𝓞 K) Gal(↥F/K) 𝔮₀) =
                      ConjClasses.mk (σ.restrictNormal F)
                    rw [heq]
                    exact ConjClasses.mk_eq_mk_iff_isConj.mpr <|
                      isConj_arithFrobAt (𝓞 K) Gal(↥F/K) 𝔮₀ (𝔓.under (𝓞 F))
                        (hq₀lo.over.symm.trans h𝔮lo.over)
                  rw [hclassF, hrestr]) H 𝔭 hunr hmem
              intro 𝔮 h𝔮p h𝔮lo
              haveI := h𝔮p
              haveI := h𝔮lo
              have hresidue :
                  Module.finrank (𝓞 K ⧸ 𝔮.under (𝓞 K)) (𝓞 ↥F ⧸ 𝔮) =
                    orderOf (1 : Gal(↥F/K)) := by
                let L := ↥F
                let σ : Gal(L/K) := 1
                let C : ConjClasses Gal(L/K) := ConjClasses.mk σ
                have hσ : ConjClasses.mk σ = C := rfl
                have hCfrob : frobeniusClass K L 𝔭 = C := by simpa [L, σ, C] using hfc
                let 𝔓 : Ideal (𝓞 L) := 𝔮
                have hlo : 𝔓.LiesOver 𝔭 := h𝔮lo
                have hunr : UnramifiedIn K L 𝔭 := hunrF
                change Module.finrank (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) = orderOf σ
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
                  letI : DistribMulAction Gal(L/K) (Ideal (𝓞 L)) := Ideal.pointwiseDistribMulAction
                  letI : FaithfulSMul Gal(L/K) (𝓞 L) := IsGaloisGroup.faithful (𝓞 K)
                  have h : Ideal.ramificationIdx' (𝔓.under (𝓞 K)) 𝔓 = 1 := hra
                  have hPbot : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓
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
              rw [hresidue, orderOf_one]) H 𝔭 hunr hmem
            obtain ⟨𝔮₀, h𝔮₀p, hcomap₀⟩ :=
              Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 F) 𝔭 (by
                rw [(RingHom.injective_iff_ker_eq_bot _).mp
                  (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 F))]
                exact bot_le)
            have h𝔮₀lo : 𝔮₀.LiesOver 𝔭 := ⟨hcomap₀.symm⟩
            haveI := h𝔮₀p
            haveI := h𝔮₀lo
            have hcard : Nat.card {𝔮 : Ideal (𝓞 ↥F) //
                  𝔮.IsPrime ∧ 𝔮.LiesOver 𝔭 ∧ 𝔮 ≠ ⊥} *
                Module.finrank (𝓞 K ⧸ 𝔮₀.under (𝓞 K)) (𝓞 ↥F ⧸ 𝔮₀) =
                  Nat.card Gal(↥F/K) := by
              have hlo : 𝔮₀.LiesOver 𝔭 := h𝔮₀lo
              have hpbot : 𝔭 ≠ ⊥ := (hunrF).1
              have he : Ideal.ramificationIdx' (𝔮₀.under (𝓞 K)) 𝔮₀ = 1 := by
                have hqbot := Ideal.ne_bot_of_liesOver_of_ne_bot hunrF.1 𝔮₀
                have hpbot := Ideal.IsIntegral.comap_ne_bot (𝓞 K) hqbot
                haveI : Algebra.IsUnramifiedAt (𝓞 K) 𝔮₀ :=
                  hunrF.2 𝔮₀ (‹𝔮₀.IsPrime›.isMaximal hqbot) hlo
                rw [Ideal.ramificationIdx'_eq_ramificationIdx (𝔮₀.under (𝓞 K)) 𝔮₀ hpbot]
                exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
              have hP0bot : 𝔮₀ ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hunrF.1 𝔮₀
              have hunder : 𝔮₀.under (𝓞 K) = 𝔭 := hlo.over.symm
              have hp_under_bot : 𝔮₀.under (𝓞 K) ≠ ⊥ := hunder ▸ hpbot
              have : 𝔮₀.IsMaximal := ‹𝔮₀.IsPrime›.isMaximal hP0bot
              have : (𝔮₀.under (𝓞 K)).IsMaximal :=
                (inferInstance : (𝔮₀.under (𝓞 K)).IsPrime).isMaximal hp_under_bot
              have : Finite (𝓞 (↥F) ⧸ 𝔮₀) := Ideal.finiteQuotientOfFreeOfNeBot 𝔮₀
                (Ideal.ne_bot_of_liesOver_of_ne_bot hunrF.1 𝔮₀)
              have : Algebra.IsSeparable (𝓞 K ⧸ 𝔮₀.under (𝓞 K)) (𝓞 (↥F) ⧸ 𝔮₀) := by
                let : Field (𝓞 K ⧸ 𝔮₀.under (𝓞 K)) := Ideal.Quotient.field _
                let : Field (𝓞 (↥F) ⧸ 𝔮₀) := Ideal.Quotient.field _
                exact IsGalois.to_isSeparable
              haveI : Finite (𝓞 K ⧸ 𝔮₀.under (𝓞 K)) :=
                Ideal.finiteQuotientOfFreeOfNeBot _ hp_under_bot
              have H :=
                Ideal.ncard_primesOver_mul_card_inertia_mul_finrank
                  (G := Gal(↥F/K)) (𝔮₀.under (𝓞 K)) 𝔮₀
              rw [show Ideal.inertia Gal(↥F/K) 𝔮₀ = ⊥ from by
                    rw [Subgroup.eq_bot_iff_card,
                      Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(↥F/K)) (𝔮₀.under (𝓞 K)) 𝔮₀,
                      Ideal.ramificationIdxIn_eq_ramificationIdx (𝔮₀.under (𝓞 K)) 𝔮₀ Gal(↥F/K),
                      ← Ideal.ramificationIdx'_eq_ramificationIdx (𝔮₀.under (𝓞 K)) 𝔮₀ hp_under_bot]
                    exact he,
                  Subgroup.card_bot, mul_one,
                  ← Ideal.inertiaDeg'_eq_inertiaDeg (𝔮₀.under (𝓞 K)) 𝔮₀,
                  Ideal.inertiaDeg'_algebraMap (𝔮₀.under (𝓞 K)) 𝔮₀] at H
              have hset : (𝔮₀.under (𝓞 K)).primesOver (𝓞 (↥F))
                  = {𝔓 : Ideal (𝓞 (↥F)) | 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} := by
                ext 𝔓
                refine ⟨fun ⟨hp, hlo'⟩ ↦ ?_, fun ⟨hp, hlo', _⟩ ↦ ?_⟩
                · have := hlo'
                  exact ⟨hp, hunder ▸ hlo', Ideal.ne_bot_of_liesOver_of_ne_bot hp_under_bot 𝔓⟩
                · exact ⟨hp, hunder ▸ hlo'⟩
              rwa [hset, ← Nat.card_coe_set_eq] at H
            rw [hresdeg 𝔮₀ h𝔮₀p h𝔮₀lo, mul_one] at hcard
            rw [hcard, IsGalois.card_aut_eq_finrank K (↥F)]) H 𝔭 h𝔭unr
              (hH 𝔭 h𝔭p ((h𝔭unr).1) h𝔭unr h𝔭cop),
            (show ∀      
                [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K))
                (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
                (hmem : ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H), (haveI : IsGalois K (IntermediateField.fixedField H) := IsGalois.of_fixedField_normal_subgroup H; haveI : NumberField (IntermediateField.fixedField H) := NumberField.of_intermediateField _; ∀ 𝔮 : Ideal (𝓞 ↥(IntermediateField.fixedField H)), 𝔮.IsPrime → 𝔮.LiesOver 𝔭 → Ideal.absNorm 𝔮 = Ideal.absNorm 𝔭) from by
              intro cnrInstance0 H 𝔭 cnrInstance1 hunr hmem
              set F := IntermediateField.fixedField H
              haveI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup H
              haveI : NumberField F := NumberField.of_intermediateField F
              have hresdeg := (show ∀      
                  [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K))
                  (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
                  (hmem : ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H), (haveI : IsGalois K (IntermediateField.fixedField H) := IsGalois.of_fixedField_normal_subgroup H; haveI : NumberField (IntermediateField.fixedField H) := NumberField.of_intermediateField _; ∀ 𝔮 : Ideal (𝓞 ↥(IntermediateField.fixedField H)), 𝔮.IsPrime → 𝔮.LiesOver 𝔭 → Module.finrank (𝓞 K ⧸ 𝔮.under (𝓞 K)) (𝓞 ↥(IntermediateField.fixedField H) ⧸ 𝔮) = 1) from by
                intro cnrInstance0 H 𝔭 cnrInstance1 hunr hmem
                set F := IntermediateField.fixedField H
                haveI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup H
                haveI : NumberField F := NumberField.of_intermediateField F
                have hunrF : UnramifiedIn K (↥F) 𝔭 := (show ∀      
                    (F : IntermediateField K L) [IsGalois K F]
                    (𝔭 : Ideal (𝓞 K)) (hunr : UnramifiedIn K L 𝔭), (UnramifiedIn K (↥F) 𝔭) from by
                  intro F cnrInstance0 𝔭 hunr
                  haveI : IsScalarTower K F L := F.isScalarTower_mid'
                  haveI : IsScalarTower (𝓞 K) (𝓞 F) (𝓞 L) := inferInstance
                  refine ⟨hunr.1, fun 𝔮 h𝔮max h𝔮lo ↦ ?_⟩
                  haveI := h𝔮lo
                  haveI := h𝔮max.isPrime
                  obtain ⟨𝔓, h𝔓prime, hcomap⟩ :=
                    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 L) 𝔮 (by
                      rw [(RingHom.injective_iff_ker_eq_bot _).mp
                        (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 L))]
                      exact bot_le)
                  have h𝔓lo : 𝔓.LiesOver 𝔮 := ⟨hcomap.symm⟩
                  haveI := h𝔓prime
                  haveI := h𝔓lo
                  haveI : 𝔓.LiesOver 𝔭 := ⟨by rw [← Ideal.under_under (B := 𝓞 F) 𝔓, h𝔓lo.over.symm, h𝔮lo.over.symm]⟩
                  haveI : Algebra.IsUnramifiedAt (𝓞 K) 𝔓 :=
                    hunr.2 𝔓 (h𝔓prime.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓)) inferInstance
                  exact Algebra.IsUnramifiedAt.of_liesOver (𝓞 K) 𝔮 𝔓) F 𝔭 hunr
                have hfc : frobeniusClass K (↥F) 𝔭 = ConjClasses.mk (1 : Gal(↥F/K)) :=
                  (show ∀      
                      [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K))
                      (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
                      (hmem : ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H), (haveI : IsGalois K (IntermediateField.fixedField H) := IsGalois.of_fixedField_normal_subgroup H; frobeniusClass K (↥(IntermediateField.fixedField H)) 𝔭 = ConjClasses.mk 1) from by
                    intro cnrInstance0 H 𝔭 cnrInstance1 hunr hmem
                    set F := IntermediateField.fixedField H with hF
                    haveI : IsScalarTower K F L := F.isScalarTower_mid'
                    haveI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup H
                    haveI : NumberField F := NumberField.of_intermediateField F
                    letI : FaithfulSMul Gal(↥F/K) (𝓞 F) := IsGaloisGroup.faithful (𝓞 K)
                    obtain ⟨𝔓, h𝔓p, hcomap⟩ :=
                      Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 L) 𝔭 (by
                        rw [(RingHom.injective_iff_ker_eq_bot _).mp
                          (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))]
                        exact bot_le)
                    have h𝔓lo : 𝔓.LiesOver 𝔭 := ⟨hcomap.symm⟩
                    haveI := h𝔓p
                    haveI := h𝔓lo
                    haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓
                      (Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓)
                    set σ : L ≃ₐ[K] L := arithFrobAt (𝓞 K) Gal(L/K) 𝔓
                    have hclass : frobeniusClass K L 𝔭 = ConjClasses.mk σ := by
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
                      change ConjClasses.mk (arithFrobAt (𝓞 K) Gal(L/K) 𝔓₀) = ConjClasses.mk σ
                      exact ConjClasses.mk_eq_mk_iff_isConj.mpr <|
                        isConj_arithFrobAt (𝓞 K) Gal(L/K) 𝔓₀ 𝔓 (hlo₀.over.symm.trans h𝔓lo.over)
                    have hconj : IsConj σ ((frobeniusClass K L 𝔭).out) := by
                      have hout : ConjClasses.mk ((frobeniusClass K L 𝔭).out) =
                          frobeniusClass K L 𝔭 := Quotient.out_eq _
                      exact ConjClasses.mk_eq_mk_iff_isConj.mp (hclass.symm.trans hout.symm)
                    have hσeq : σ = (frobeniusClass K L 𝔭).out := by
                      obtain ⟨c, hc⟩ := hconj
                      rw [SemiconjBy, mul_comm' (c : Gal(L/K)) σ] at hc
                      exact mul_right_cancel hc
                    have hσfix : σ ∈ F.fixingSubgroup := by
                      rw [hF, IntermediateField.fixingSubgroup_fixedField]
                      exact hσeq ▸ hmem
                    have hrestr : σ.restrictNormal F = 1 :=
                      MonoidHom.mem_ker.mp <| (IntermediateField.restrictNormalHom_ker F).ge hσfix
                    have h𝔮lo : (𝔓.under (𝓞 F)).LiesOver 𝔭 :=
                      ⟨by rw [← Ideal.under_under (B := 𝓞 F) 𝔓]; exact h𝔓lo.over⟩
                    haveI := h𝔮lo
                    have hfrobF : IsArithFrobAt (𝓞 K) (σ.restrictNormal F) (𝔓.under (𝓞 F)) :=
                      (show ∀      
                          (F : IntermediateField K L) [IsGalois K F] (σ : L ≃ₐ[K] L)
                          (𝔓 : Ideal (𝓞 L)) (hσ : IsArithFrobAt (𝓞 K) σ 𝔓), (haveI : IsScalarTower K F L := F.isScalarTower_mid'; IsArithFrobAt (𝓞 K) (σ.restrictNormal F) (𝔓.under (𝓞 F))) from by
                        intro F cnrInstance0 σ 𝔓 hσ
                        haveI : IsScalarTower K F L := F.isScalarTower_mid'
                        intro y
                        have hsmul : σ • (algebraMap (𝓞 F) (𝓞 L) y) =
                            algebraMap (𝓞 F) (𝓞 L) ((σ.restrictNormal F) • y) := by
                          have hbridgeL : ∀ (g : L ≃ₐ[K] L) (x : 𝓞 L), ((g • x : 𝓞 L) : L) = g • (x : L) :=
                            fun g x ↦ by simpa [Algebra.smul_def] using
                              (smul_distrib_smul (G := L ≃ₐ[K] L) (R := 𝓞 L) (S := L) g x 1).symm
                          have hbridgeF : ∀ (g : F ≃ₐ[K] F) (z : 𝓞 F), ((g • z : 𝓞 F) : F) = g • (z : F) :=
                            fun g z ↦ by simpa [Algebra.smul_def] using
                              (smul_distrib_smul (G := F ≃ₐ[K] F) (R := 𝓞 F) (S := F) g z 1).symm
                          have hcoe : ∀ z : 𝓞 F,
                              ((algebraMap (𝓞 F) (𝓞 L) z : 𝓞 L) : L) = algebraMap F L (z : F) :=
                            fun z ↦ by
                              rw [RingOfIntegers.coe_eq_algebraMap,
                                ← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 L) L,
                                RingOfIntegers.coe_eq_algebraMap, ← IsScalarTower.algebraMap_apply (𝓞 F) F L]
                          rw [RingOfIntegers.ext_iff]
                          change ((σ • algebraMap (𝓞 F) (𝓞 L) y : 𝓞 L) : L) =
                              ((algebraMap (𝓞 F) (𝓞 L) ((σ.restrictNormal F) • y) : 𝓞 L) : L)
                          rw [hbridgeL, hcoe y, hcoe ((σ.restrictNormal F) • y), hbridgeF,
                            AlgEquiv.smul_def, AlgEquiv.smul_def, AlgEquiv.restrictNormal_commutes]
                        rw [Ideal.under_under 𝔓, Ideal.under, Ideal.mem_comap, map_sub, map_pow,
                          show (MulSemiringAction.toAlgHom (𝓞 K) (𝓞 F) (σ.restrictNormal F)) y
                              = (σ.restrictNormal F) • y from rfl, ← hsmul]
                        exact hσ (algebraMap (𝓞 F) (𝓞 L) y)) F σ 𝔓 (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓)
                    have hunrF := (show ∀      
                        (F : IntermediateField K L) [IsGalois K F]
                        (𝔭 : Ideal (𝓞 K)) (hunr : UnramifiedIn K L 𝔭), (UnramifiedIn K (↥F) 𝔭) from by
                      intro F cnrInstance0 𝔭 hunr
                      haveI : IsScalarTower K F L := F.isScalarTower_mid'
                      haveI : IsScalarTower (𝓞 K) (𝓞 F) (𝓞 L) := inferInstance
                      refine ⟨hunr.1, fun 𝔮 h𝔮max h𝔮lo ↦ ?_⟩
                      haveI := h𝔮lo
                      haveI := h𝔮max.isPrime
                      obtain ⟨𝔓, h𝔓prime, hcomap⟩ :=
                        Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 L) 𝔮 (by
                          rw [(RingHom.injective_iff_ker_eq_bot _).mp
                            (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 L))]
                          exact bot_le)
                      have h𝔓lo : 𝔓.LiesOver 𝔮 := ⟨hcomap.symm⟩
                      haveI := h𝔓prime
                      haveI := h𝔓lo
                      haveI : 𝔓.LiesOver 𝔭 := ⟨by rw [← Ideal.under_under (B := 𝓞 F) 𝔓, h𝔓lo.over.symm, h𝔮lo.over.symm]⟩
                      haveI : Algebra.IsUnramifiedAt (𝓞 K) 𝔓 :=
                        hunr.2 𝔓 (h𝔓prime.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓)) inferInstance
                      exact Algebra.IsUnramifiedAt.of_liesOver (𝓞 K) 𝔮 𝔓) F 𝔭 hunr
                    have hclassF : frobeniusClass K (↥F) 𝔭 =
                        ConjClasses.mk (σ.restrictNormal F) := by
                      let e : ∃ 𝔮₀ : Ideal (𝓞 F), 𝔮₀.IsPrime ∧ 𝔮₀.LiesOver 𝔭 := by
                        obtain ⟨𝔮₀, hq₀, hcomap₀⟩ :=
                          Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 F) 𝔭 (by
                            rw [(RingHom.injective_iff_ker_eq_bot _).mp
                              (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 F))]
                            exact bot_le)
                        exact ⟨𝔮₀, hq₀, ⟨hcomap₀.symm⟩⟩
                      let 𝔮₀ := Classical.choose e
                      haveI : 𝔮₀.IsPrime := (Classical.choose_spec e).1
                      have hq₀lo : 𝔮₀.LiesOver 𝔭 := (Classical.choose_spec e).2
                      haveI : Finite (𝓞 F ⧸ 𝔮₀) := Ideal.finiteQuotientOfFreeOfNeBot 𝔮₀
                        (Ideal.ne_bot_of_liesOver_of_ne_bot hunrF.1 𝔮₀)
                      haveI : (𝔓.under (𝓞 F)).IsPrime := inferInstance
                      have hqbot := Ideal.ne_bot_of_liesOver_of_ne_bot hunrF.1 (𝔓.under (𝓞 F))
                      haveI : Finite (𝓞 F ⧸ 𝔓.under (𝓞 F)) :=
                        Ideal.finiteQuotientOfFreeOfNeBot _ hqbot
                      haveI : Algebra.IsUnramifiedAt (𝓞 K) (𝔓.under (𝓞 F)) :=
                        hunrF.2 _ (‹(𝔓.under (𝓞 F)).IsPrime›.isMaximal hqbot) h𝔮lo
                      have heq : σ.restrictNormal F =
                          arithFrobAt (𝓞 K) Gal(↥F/K) (𝔓.under (𝓞 F)) :=
                        MulSemiringAction.toAlgHom_injective (𝓞 K) (𝓞 F) <|
                          AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt hfrobF
                            (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(↥F/K) (𝔓.under (𝓞 F)))
                            (𝔓.under (𝓞 F)).primeCompl_le_nonZeroDivisors
                      rw [frobeniusClass, dif_pos ⟨‹𝔭.IsPrime›, hunrF⟩]
                      change ConjClasses.mk (arithFrobAt (𝓞 K) Gal(↥F/K) 𝔮₀) =
                        ConjClasses.mk (σ.restrictNormal F)
                      rw [heq]
                      exact ConjClasses.mk_eq_mk_iff_isConj.mpr <|
                        isConj_arithFrobAt (𝓞 K) Gal(↥F/K) 𝔮₀ (𝔓.under (𝓞 F))
                          (hq₀lo.over.symm.trans h𝔮lo.over)
                    rw [hclassF, hrestr]) H 𝔭 hunr hmem
                intro 𝔮 h𝔮p h𝔮lo
                haveI := h𝔮p
                haveI := h𝔮lo
                have hresidue :
                    Module.finrank (𝓞 K ⧸ 𝔮.under (𝓞 K)) (𝓞 ↥F ⧸ 𝔮) =
                      orderOf (1 : Gal(↥F/K)) := by
                  let L := ↥F
                  let σ : Gal(L/K) := 1
                  let C : ConjClasses Gal(L/K) := ConjClasses.mk σ
                  have hσ : ConjClasses.mk σ = C := rfl
                  have hCfrob : frobeniusClass K L 𝔭 = C := by simpa [L, σ, C] using hfc
                  let 𝔓 : Ideal (𝓞 L) := 𝔮
                  have hlo : 𝔓.LiesOver 𝔭 := h𝔮lo
                  have hunr : UnramifiedIn K L 𝔭 := hunrF
                  change Module.finrank (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) = orderOf σ
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
                    letI : DistribMulAction Gal(L/K) (Ideal (𝓞 L)) := Ideal.pointwiseDistribMulAction
                    letI : FaithfulSMul Gal(L/K) (𝓞 L) := IsGaloisGroup.faithful (𝓞 K)
                    have h : Ideal.ramificationIdx' (𝔓.under (𝓞 K)) 𝔓 = 1 := hra
                    have hPbot : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓
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
                rw [hresidue, orderOf_one]) H 𝔭 hunr hmem
              intro 𝔮 h𝔮p h𝔮lo
              haveI := h𝔮p
              haveI := h𝔮lo
              have hinert : (𝔮.under (𝓞 K)).inertiaDeg' 𝔮 = 1 := by
                rw [Ideal.inertiaDeg'_algebraMap]
                exact hresdeg 𝔮 h𝔮p h𝔮lo
              have hunder : 𝔮.under (𝓞 K) = 𝔭 := h𝔮lo.over.symm
              rw [Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver 𝔮 (𝔮.under (𝓞 K)) inferInstance
                (hunder ▸ (hunr).1), hinert, pow_one, hunder]) H 𝔭 h𝔭unr
              (hH 𝔭 h𝔭p ((h𝔭unr).1) h𝔭unr h𝔭cop)⟩
      have hregroup :
        primeIdealZetaSum {𝔮 : Ideal (𝓞 ↥(IntermediateField.fixedField H)) | 𝔮.IsPrime ∧
            UnramifiedIn K L (𝔮.under (𝓞 K)) ∧ (Ideal.absNorm (𝔮.under (𝓞 K))).Coprime m} s
          = (Module.finrank K ↥(IntermediateField.fixedField H) : ℝ) * primeIdealZetaSum
              {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ (Ideal.absNorm 𝔭).Coprime m} s := by
        set F := IntermediateField.fixedField H
        haveI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup H
        haveI : NumberField F := NumberField.of_intermediateField F
        set U : Set (Ideal (𝓞 K)) :=
          {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ (Ideal.absNorm 𝔭).Coprime m}
        set V : Set (Ideal (𝓞 F)) :=
          {𝔮 | 𝔮.IsPrime ∧ UnramifiedIn K L (𝔮.under (𝓞 K)) ∧ (Ideal.absNorm (𝔮.under (𝓞 K))).Coprime m}
        set IU := {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ U ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}
        set IV := {𝔮 : Ideal (𝓞 F) // 𝔮 ∈ V ∧ 𝔮.IsPrime ∧ 𝔮 ≠ ⊥}
        have hφ_mem : ∀ 𝔮 : IV, (𝔮.1.under (𝓞 K)) ∈ U ∧ (𝔮.1.under (𝓞 K)).IsPrime
            ∧ (𝔮.1.under (𝓞 K)) ≠ ⊥ := fun 𝔮 ↦ by
          haveI := 𝔮.2.2.1
          exact ⟨⟨inferInstance, 𝔮.2.1.2.1, 𝔮.2.1.2.2⟩, inferInstance,
            Ideal.IsIntegral.comap_ne_bot (𝓞 K) 𝔮.2.2.2⟩
        set φ : IV → IU := fun 𝔮 ↦ ⟨𝔮.1.under (𝓞 K), hφ_mem 𝔮⟩
        set e := Equiv.sigmaFiberEquiv φ
        have hsummSig : Summable (fun p : Σ 𝔭 : IU, {𝔮 : IV // φ 𝔮 = 𝔭} ↦
            (Ideal.absNorm (e p).1 : ℝ) ^ (-s)) :=
          (e.summable_iff (f := fun 𝔮 : IV ↦ (Ideal.absNorm 𝔮.1 : ℝ) ^ (-s))).mpr
            ((show ∀ (S : Set (Ideal (𝓞 (↥F)))) {s : ℝ}, 1 < s → Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 (↥F)) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) from by
              intro S s hs
              exact (((hNonzeroIdealNormSummable.2 F hs)).comp_injective
                (i := fun 𝔭 : {𝔭 : Ideal (𝓞 (↥F)) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
                  (⟨𝔭.1, 𝔭.2.2.2⟩ : NonzeroIdeal (↥F)))
                fun _ _ hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab)).congr fun _ ↦ rfl) V hs)
        rw [primeIdealZetaSum, ← e.tsum_eq (fun 𝔮 : IV ↦ (Ideal.absNorm (𝔮.1) : ℝ) ^ (-s)),
          hsummSig.tsum_sigma, primeIdealZetaSum, ← tsum_mul_left]
        refine tsum_congr (fun 𝔭 ↦ ?_)
        haveI := 𝔭.2.2.1
        have hfibeq : {𝔮 : IV // φ 𝔮 = 𝔭} ≃
            {𝔮 : Ideal (𝓞 F) // 𝔮.IsPrime ∧ 𝔮.LiesOver 𝔭.1 ∧ 𝔮 ≠ ⊥} :=
          { toFun := fun x ↦ ⟨x.1.1, x.1.2.2.1, ⟨(Subtype.ext_iff.mp x.2).symm⟩, x.1.2.2.2⟩
            invFun := fun y ↦ ⟨⟨y.1, ⟨y.2.1, by
                haveI := y.2.1
                haveI := y.2.2.1
                exact (y.2.2.1.over ▸ 𝔭.2.1.2 : UnramifiedIn K L (y.1.under (𝓞 K)) ∧
                  (Ideal.absNorm (y.1.under (𝓞 K))).Coprime m)⟩, y.2.1, y.2.2.2⟩,
              Subtype.ext (haveI := y.2.2.1; y.2.2.1.over.symm)⟩
            left_inv := fun _ ↦ rfl
            right_inv := fun _ ↦ rfl }
        have hconst : ∀ x : {𝔮 : IV // φ 𝔮 = 𝔭}, (Ideal.absNorm (e ⟨𝔭, x⟩).1 : ℝ) ^ (-s)
            = (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) := fun x ↦ by
          change (Ideal.absNorm x.1.1 : ℝ) ^ (-s) = (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)
          rw [(hsplit 𝔭.1 𝔭.2.2.1 𝔭.2.1.2.1 𝔭.2.1.2.2).2 x.1.1 x.1.2.2.1 ⟨(Subtype.ext_iff.mp x.2).symm⟩]
        haveI : 𝔭.1.IsMaximal := 𝔭.2.2.1.isMaximal 𝔭.2.2.2
        haveI : Finite {𝔮 : Ideal (𝓞 F) // 𝔮.IsPrime ∧ 𝔮.LiesOver 𝔭.1 ∧ 𝔮 ≠ ⊥} := by
          letI : Finite (𝔭.1.primesOver (𝓞 F)) :=
            (IsDedekindDomain.primesOver_finite 𝔭.1 (𝓞 F)).to_subtype
          refine Finite.of_injective (β := 𝔭.1.primesOver (𝓞 F))
            (fun y ↦ ⟨y.1, y.2.1, y.2.2.1⟩) fun a b hab ↦ Subtype.ext ?_
          exact congrArg (Subtype.val : 𝔭.1.primesOver (𝓞 F) → _) hab
        haveI : Finite {𝔮 : IV // φ 𝔮 = 𝔭} := Finite.of_equiv _ hfibeq.symm
        rw [tsum_congr hconst, tsum_const, Nat.card_congr hfibeq,
          (hsplit 𝔭.1 𝔭.2.2.1 𝔭.2.1.2.1 𝔭.2.1.2.2).1, nsmul_eq_mul, mul_comm]
      rw [← hregroup]
      exact (show ∀ {S T : Set (Ideal (𝓞 (↥F)))}, S ⊆ T → ∀ {s : ℝ}, 1 < s → primeIdealZetaSum S s ≤ primeIdealZetaSum T s from by
        intro S T hST s hs
        rw [primeIdealZetaSum, primeIdealZetaSum]
        refine ((show ∀ (S : Set (Ideal (𝓞 (↥F)))) {s : ℝ}, 1 < s → Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 (↥F)) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) from by
          intro S s hs
          exact (((hNonzeroIdealNormSummable.2 F hs)).comp_injective
            (i := fun 𝔭 : {𝔭 : Ideal (𝓞 (↥F)) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
              (⟨𝔭.1, 𝔭.2.2.2⟩ : NonzeroIdeal (↥F)))
            fun _ _ hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab)).congr fun _ ↦ rfl) S hs).tsum_le_tsum_of_inj
          (fun 𝔭 ↦ ⟨𝔭.1, hST 𝔭.2.1, 𝔭.2.2.1, 𝔭.2.2.2⟩)
          (fun a b hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab))
          (fun c _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
          (fun _ ↦ le_rfl) ((show ∀ (S : Set (Ideal (𝓞 (↥F)))) {s : ℝ}, 1 < s → Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 (↥F)) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) from by
            intro S s hs
            exact (((hNonzeroIdealNormSummable.2 F hs)).comp_injective
              (i := fun 𝔭 : {𝔭 : Ideal (𝓞 (↥F)) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
                (⟨𝔭.1, 𝔭.2.2.2⟩ : NonzeroIdeal (↥F)))
              fun _ _ hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab)).congr fun _ ↦ rfl) T hs)) (Set.subset_univ _) hs) H hH hs1) hLs.le
  have hlim := le_of_tendsto_of_tendsto (hAtend.const_mul (d : ℝ)) hBtend hev
  simpa using hlim

/-- **Frobenii of coprime-norm primes generate the Galois group** (abelian case). A subgroup of
`Gal(L/K)` containing the Frobenius representative of every nonzero prime of `K` that is
unramified in `L` **and has norm coprime to `m`** is all of `Gal(L/K)`.

The κ-uniformity realization in `ZetaProduct.lean` uses this theorem for residues arising from
coprime-norm ideal Frobenius values. The fixed-field zeta comparison uses coprime-norm primes (the
excluded unramified primes with non-coprime norm form a finite set, leaving the comparison ratio
unchanged): reduce `H = ⊤` to `[F:K] ≤ 1` and apply
`finrank_fixedField_le_one_of_forall_frobenius_mem_of_coprime`. -/
theorem subgroup_eq_top_of_forall_frobenius_mem_of_coprime
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m] (H : Subgroup Gal(L/K))
    (hH : ∀ 𝔭 : Ideal (𝓞 K), ∀ _ : 𝔭.IsPrime, 𝔭 ≠ ⊥ → UnramifiedIn K L 𝔭 →
      (Ideal.absNorm 𝔭).Coprime m → ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H) :
    H = ⊤ := by
  rw [← Subgroup.card_eq_iff_eq_top]
  have hfk : Module.finrank K (IntermediateField.fixedField H) = 1 :=
    le_antisymm (finrank_fixedField_le_one_of_forall_frobenius_mem_of_coprime K L m H hH)
      Module.finrank_pos
  have htower := Module.finrank_mul_finrank K (IntermediateField.fixedField H) L
  rw [hfk, one_mul] at htower
  rw [IsGalois.card_aut_eq_finrank K L, ← htower, IntermediateField.finrank_fixedField_eq_card H]

end CoprimeRestrictedComparison

end Chebotarev
