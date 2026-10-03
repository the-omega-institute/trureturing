/- GID: D5/S3/Analytic/Zeta/NumberField/CoprimePrimeSum
   generality: G
   mirror-B: D5/B/S3/Analytic/Zeta/NumberField/CoprimePrimeSum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The coprime-norm unramified prime-ideal zeta sum has a logarithmic leading term. -/
module

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

/-- The coprime-norm-unramified prime sum is asymptotic to `log(1/(s-1))`: it differs from the
universal prime sum (`primeIdealZetaSum_univ_tendsto_log`) by the finitely many excluded
primes — ramified or with norm not coprime to `m` —
whose bounded contribution is negligible against `log → ∞`. -/
theorem primeIdealZetaSum_unramified_coprime_div_log_tendsto_one :
    Filter.Tendsto
      (fun s : ℝ ↦
        primeIdealZetaSum
            {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ (Ideal.absNorm 𝔭).Coprime m} s
          / Real.log (1 / (s - 1)))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
  set Uc : Set (Ideal (𝓞 K)) :=
    {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ (Ideal.absNorm 𝔭).Coprime m}
  set D : Set (Ideal (𝓞 K)) :=
    {𝔭 | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ (UnramifiedIn K L 𝔭 ∧ (Ideal.absNorm 𝔭).Coprime m)}
  have hdisj : Disjoint Uc D :=
    Set.disjoint_left.mpr fun 𝔭 hc hd ↦ hd.2.2 ⟨hc.2.1, hc.2.2⟩
  have hcover : ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔭 ∈ Uc ∪ D := fun 𝔭 hp hne ↦ by
    by_cases h : UnramifiedIn K L 𝔭 ∧ (Ideal.absNorm 𝔭).Coprime m
    · exact Or.inl ⟨hp, h.1, h.2⟩
    · exact Or.inr ⟨hp, hne, h⟩
  have hDfin : D.Finite := by
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
    have hbad : {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ (Ideal.absNorm 𝔭).Coprime m}.Finite := by
      classical
      refine Set.Finite.subset
        (Set.Finite.biUnion (s := (↑m.primeFactors : Set ℕ))
          (t := fun p : ℕ =>
            {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ (p : 𝓞 K) ∈ 𝔭})
          (Set.toFinite _) fun p hp ↦ ?_)
        ?_
      · have hp0 : p ≠ 0 := (Nat.pos_of_mem_primeFactors hp).ne'
        have hspan : (Ideal.span {(p : 𝓞 K)}) ≠ 0 := by
          simp only [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
          exact_mod_cast hp0
        refine ((Ideal.finite_factors (R := 𝓞 K) hspan).image (·.asIdeal)).subset ?_
        rintro 𝔭 ⟨hprime, hne, hmem⟩
        exact ⟨⟨𝔭, hprime, hne⟩,
          Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hmem), rfl⟩
      · rintro 𝔭 ⟨hprime, hne, hncop⟩
        have := hprime
        have hfactor : ∃ p ∈ m.primeFactors, (p : 𝓞 K) ∈ 𝔭 := by
          have h𝔭 : 𝔭 ≠ ⊥ := hne
          have hN0 : Ideal.absNorm 𝔭 ≠ 0 :=
            fun h ↦ h𝔭 (Ideal.absNorm_eq_zero_iff.mp h)
          have hN1' : Ideal.absNorm 𝔭 ≠ 1 :=
            fun h ↦ ‹𝔭.IsPrime›.ne_top (Ideal.absNorm_eq_one_iff.mp h)
          obtain ⟨r, hr, hrdvd, hrm⟩ :=
            exists_prime_dvd_natCast_mem K 𝔭 _ (by lia) (Ideal.absNorm_mem 𝔭)
          have hNdvd : Ideal.absNorm 𝔭 ∣ r ^ Module.finrank ℤ (𝓞 K) := by
            have hd := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hrm)
            rw [Ideal.absNorm_span_singleton,
              show ((r : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) (r : ℤ) by
                push_cast
                rfl,
              Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast] at hd
            exact hd
          obtain ⟨p, hp, hpdvd⟩ :=
            Nat.exists_prime_and_dvd (hncop : Nat.gcd (Ideal.absNorm 𝔭) m ≠ 1)
          have hpr : p ∣ r ^ Module.finrank ℤ (𝓞 K) :=
            (hpdvd.trans (Nat.gcd_dvd_left _ _)).trans hNdvd
          have hpeqr : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow hpr)
          exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpdvd.trans (Nat.gcd_dvd_right _ _), NeZero.ne m⟩,
            hpeqr ▸ hrm⟩
        obtain ⟨p, hp, hpmem⟩ := hfactor
        exact Set.mem_biUnion hp ⟨hprime, hne, hpmem⟩
    refine (hram.union hbad).subset ?_
    rintro 𝔭 ⟨hp, hne, hnot⟩
    by_cases hunr : UnramifiedIn K L 𝔭
    · exact Or.inr ⟨hp, hne, fun hcop ↦ hnot ⟨hunr, hcop⟩⟩
    · exact Or.inl ⟨hp, hne, hunr⟩
  obtain ⟨CD, hCD⟩ : ∃ CD : ℝ, ∀ᶠ s in nhdsWithin 1 (Set.Ioi 1), primeIdealZetaSum D s ≤ CD := by
    refine ⟨Nat.card {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ D ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, ?_⟩
    let T : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
      {𝔭 | 𝔭.asIdeal ∈ D}
    let e : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ D ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ≃ T :=
      { toFun := fun 𝔭 ↦ ⟨⟨𝔭.1, 𝔭.2.2.1, 𝔭.2.2.2⟩, 𝔭.2.1⟩
        invFun := fun 𝔭 ↦ ⟨𝔭.1.asIdeal, 𝔭.2, 𝔭.1.isPrime, 𝔭.1.ne_bot⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    have hTfin : T.Finite :=
      hDfin.preimage IsDedekindDomain.HeightOneSpectrum.asIdeal_injective.injOn
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Set.mem_Ioi] at hs
    calc
      primeIdealZetaSum D s = NumberField.Set.primeIdealZetaSum T s := by
        rw [NumberField.Set.primeIdealZetaSum_def, Chebotarev.primeIdealZetaSum]
        exact e.tsum_eq (fun 𝔭 : T ↦ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s))
      _ ≤ (T.ncard : ℝ) :=
        NumberField.Set.primeIdealZetaSum_le_card_of_finite hTfin (by linarith)
      _ = (Nat.card {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ D ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} : ℝ) := by
        exact_mod_cast (Nat.card_congr e).symm
  have hDzero : Filter.Tendsto (fun s : ℝ ↦ primeIdealZetaSum D s / Real.log (1 / (s - 1)))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
    have hL : Filter.Tendsto (fun s : ℝ ↦ Real.log (1 / (s - 1)))
        (nhdsWithin 1 (Set.Ioi 1)) Filter.atTop := by
      refine Real.tendsto_log_atTop.comp ?_
      have h1 : Filter.Tendsto (fun s : ℝ ↦ s - 1)
          (nhdsWithin 1 (Set.Ioi 1)) (nhdsWithin 0 (Set.Ioi 0)) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          (((continuous_sub_right 1).tendsto' 1 0 (by ring)).mono_left nhdsWithin_le_nhds)
          (eventually_nhdsWithin_of_forall fun s hs ↦ by
            simp only [Set.mem_Ioi] at hs ⊢
            linarith)
      simpa only [one_div] using! h1.inv_tendsto_nhdsGT_zero
    refine squeeze_zero_norm' ?_ (Filter.Tendsto.div_atTop tendsto_const_nhds hL (a := CD))
    filter_upwards [hCD, hL.eventually_gt_atTop 0] with s hub hLpos
    have hDnn : 0 ≤ primeIdealZetaSum D s := by
      rw [primeIdealZetaSum]
      exact tsum_nonneg fun _ ↦ Real.rpow_nonneg (by positivity) _
    rw [Real.norm_of_nonneg (div_nonneg hDnn hLpos.le)]
    gcongr
  have hcomb : Filter.Tendsto (fun s : ℝ ↦
      primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s / Real.log (1 / (s - 1))
        - primeIdealZetaSum D s / Real.log (1 / (s - 1))) (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
    simpa using (primeIdealZetaSum_univ_tendsto_log K).sub hDzero
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Set.mem_Ioi] at hs
  have hadd : primeIdealZetaSum Uc s + primeIdealZetaSum D s =
      primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s := by
    rw [← (show ∀ {S T : Set (Ideal (𝓞 K))}, Disjoint S T → ∀ {s : ℝ}, 1 < s → primeIdealZetaSum (S ∪ T) s = primeIdealZetaSum S s + primeIdealZetaSum T s from by
      intro S T hDisj s hs
      let eS : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ≃
          ↑{x : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∪ T ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} | (x.1 : Ideal (𝓞 K)) ∈ S} :=
        { toFun := fun 𝔭 ↦ ⟨⟨𝔭.1, Or.inl 𝔭.2.1, 𝔭.2.2.1, 𝔭.2.2.2⟩, 𝔭.2.1⟩
          invFun := fun x ↦ ⟨x.1.1, x.2, x.1.2.2.1, x.1.2.2.2⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
      let eT : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ T ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ≃
          ↑{x : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∪ T ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} | (x.1 : Ideal (𝓞 K)) ∈ S}ᶜ :=
        { toFun := fun 𝔭 ↦ ⟨⟨𝔭.1, Or.inr 𝔭.2.1, 𝔭.2.2.1, 𝔭.2.2.2⟩,
            fun h ↦ hDisj.le_bot ⟨h, 𝔭.2.1⟩⟩
          invFun := fun x ↦ ⟨x.1.1, x.1.2.1.resolve_left x.2, x.1.2.2.1, x.1.2.2.2⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
      have hsum : Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∪ T ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
          (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) :=
        (show ∀ (S : Set (Ideal (𝓞 K))) {s : ℝ}, 1 < s → Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) from by
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
            fun _ _ hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab)).congr fun _ ↦ rfl) (S ∪ T) hs
      rw [primeIdealZetaSum, primeIdealZetaSum, primeIdealZetaSum,
        ← hsum.tsum_subtype_add_tsum_subtype_compl
          {x | (x.1 : Ideal (𝓞 K)) ∈ S},
        ← eS.tsum_eq (fun x ↦ (Ideal.absNorm (x.1 : Ideal (𝓞 K)) : ℝ) ^ (-s)),
        ← eT.tsum_eq (fun x ↦ (Ideal.absNorm (x.1 : Ideal (𝓞 K)) : ℝ) ^ (-s))]
      rfl) hdisj hs,
      (show ∀ {S : Set (Ideal (𝓞 K))}, (∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔭 ∈ S) → ∀ s : ℝ, primeIdealZetaSum S s = primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s from by
        intro S hS s
        let e : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ≃
            {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ (Set.univ : Set (Ideal (𝓞 K))) ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} :=
          Equiv.subtypeEquivRight fun 𝔭 ↦
            ⟨fun h ↦ ⟨Set.mem_univ _, h.2⟩, fun h ↦ ⟨hS 𝔭 h.2.1 h.2.2, h.2⟩⟩
        rw [primeIdealZetaSum, primeIdealZetaSum,
          ← e.tsum_eq (fun 𝔭 ↦ (Ideal.absNorm (𝔭.1 : Ideal (𝓞 K)) : ℝ) ^ (-s))]
        rfl) hcover s]
  rw [← sub_div, ← hadd, add_sub_cancel_right]

end CoprimeRestrictedComparison

end Chebotarev
