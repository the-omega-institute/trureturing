/- GID: D5/S3/Factorization/Galois/Chebotarev/Cyclotomic
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/Chebotarev/Cyclotomic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cyclotomic Frobenius fibres have inverse Galois-group Dirichlet density. -/
module

public import D5.S3.Factorization.Galois.Chebotarev.CyclotomicCharacterBounds

public import D5.S3.Analytic.Zeta.NumberField.ZetaProduct
public import D5.S3.Factorization.Galois.Chebotarev.CyclotomicNormResidue
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Chebotarev's theorem: cyclotomic case

For a number field `K`, an integer `m ≥ 1`, and the cyclotomic extension
`L = K(μ_m)`, the Dirichlet density of primes `𝔭` of `𝓞 K` (unramified in `L`)
whose Frobenius equals a given `σ ∈ Gal(L/K)` is `1 / |Gal(L/K)|`.

The proof is the direct generalisation of Dirichlet's theorem (Sharifi
§7.2.1; Stevenhagen–Lenstra Appendix paragraph 3). The argument:

1. By Frobenius reciprocity for cyclotomic extensions, `χ(σ_𝔭)` depends only
   on `N𝔭 mod m` for every character `χ` of `Gal(L/K)`.
2. The orthogonality relation `Σ_χ χ(σ)^{-1} χ(σ_𝔭) = |G|` if `σ_𝔭 = σ` (and
   `0` otherwise) holds character-by-character.
3. Combining the two and using `log ζ_K(s) ~ Σ_𝔭 N𝔭^{-s}`,
   `log L(χ, s)` bounded for `χ ≠ 1`, and `L(χ, 1) ≠ 0` from
   `ZetaProduct.artinLSeries_one_ne_zero`, the Dirichlet density of
   `{𝔭 : σ_𝔭 = σ}` equals `1 / |G|`.

## Main results

* `Chebotarev.cyclotomic_density_from_two_sided_asymp` — the density of
  primes of `K` unramified in `K(μ_m)` with Frobenius equal to `σ` is
  `1 / |Gal(K(μ_m)/K)|`.

## References

* Sharifi, *Algebraic Number Theory*, §7.2.1 (`docs/algnum.pdf`, p. 142).
* Stevenhagen–Lenstra, *Chebotarëv and his density theorem*, Appendix
  paragraph 3 (`docs/cheb.pdf`, p. 18).
-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

open NumberField Filter Topology

namespace Chebotarev

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]


/-! ### Assembly helpers for `primeIdealZetaSum_frobeniusFibre_asymp`

The orthogonality collapse runs the character sum `∑_χ (χ σ)⁻¹ · (∑'_𝔭 χ(Frob 𝔭) N𝔭⁻ˢ)` two ways:

* interchanging the finite `∑_χ` with the prime `∑'_𝔭` and collapsing the inner character sum by
  orthogonality gives `|G| · P_σ(s)` (the fibre prime sum, real and nonnegative);
* splitting `∑_χ` into the trivial character `χ = 1` (contributing `∑'_𝔭 N𝔭⁻ˢ` over unramified
  primes, asymptotic to `log(1/(s-1))`) and the nontrivial characters (each bounded by
  `artinLSeries_prime_sum_bounded_of_ne_one`).

Comparing the two yields `|G| · P_σ(s) = log(1/(s-1)) + O(1)`, hence `P_σ(s)/log → 1/|G|`. -/

/-- The bare prime sum over the unramified primes is asymptotic to `log(1/(s-1))`: it differs from
the universal prime sum by only finitely many ramified primes, whose bounded contribution is
negligible against `log → ∞`. -/
private theorem primeIdealZetaSum_unramified_div_log_tendsto_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] :
    Tendsto
      (fun s : ℝ ↦
        primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} s
          / Real.log (1 / (s - 1)))
      (𝓝[>] 1) (𝓝 1) := by
  set U : Set (Ideal (𝓞 K)) := {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭}
  set R : Set (Ideal (𝓞 K)) := {𝔭 | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ UnramifiedIn K L 𝔭}
  have hdisj : Disjoint U R :=
    Set.disjoint_left.mpr fun 𝔭 hu hr ↦ hr.2.2 hu.2
  have hcover : ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔭 ∈ U ∪ R := fun 𝔭 hp hne ↦ by
    by_cases hunr : UnramifiedIn K L 𝔭
    · exact Or.inl ⟨hp, hunr⟩
    · exact Or.inr ⟨hp, hne, hunr⟩
  have hRfin : R.Finite := by
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
  obtain ⟨CR, hCR⟩ : ∃ CR : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), primeIdealZetaSum R s ≤ CR := by
    refine ⟨Nat.card {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ R ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, ?_⟩
    let T : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
      {𝔭 | 𝔭.asIdeal ∈ R}
    let e : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ R ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ≃ T :=
      { toFun := fun 𝔭 ↦ ⟨⟨𝔭.1, 𝔭.2.2.1, 𝔭.2.2.2⟩, 𝔭.2.1⟩
        invFun := fun 𝔭 ↦ ⟨𝔭.1.asIdeal, 𝔭.2, 𝔭.1.isPrime, 𝔭.1.ne_bot⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    have hTfin : T.Finite :=
      hRfin.preimage IsDedekindDomain.HeightOneSpectrum.asIdeal_injective.injOn
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Set.mem_Ioi] at hs
    calc
      primeIdealZetaSum R s = NumberField.Set.primeIdealZetaSum T s := by
        rw [NumberField.Set.primeIdealZetaSum_def, Chebotarev.primeIdealZetaSum]
        exact e.tsum_eq (fun 𝔭 : T ↦ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s))
      _ ≤ (T.ncard : ℝ) :=
        NumberField.Set.primeIdealZetaSum_le_card_of_finite hTfin (by linarith)
      _ = (Nat.card {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ R ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} : ℝ) := by
        exact_mod_cast (Nat.card_congr e).symm
  have hRzero : Tendsto (fun s : ℝ ↦ primeIdealZetaSum R s / Real.log (1 / (s - 1)))
      (𝓝[>] 1) (𝓝 0) := by
    have hL : Tendsto (fun s : ℝ ↦ Real.log (1 / (s - 1))) (𝓝[>] (1 : ℝ)) atTop := by
      refine Real.tendsto_log_atTop.comp ?_
      have h1 : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          (((continuous_sub_right 1).tendsto' 1 0 (by ring)).mono_left nhdsWithin_le_nhds)
          (eventually_nhdsWithin_of_forall fun s hs ↦ by
            simp only [Set.mem_Ioi] at hs ⊢
            linarith)
      simpa only [one_div] using! h1.inv_tendsto_nhdsGT_zero
    refine squeeze_zero_norm' ?_ (Filter.Tendsto.div_atTop tendsto_const_nhds hL (a := CR))
    filter_upwards [hCR, hL.eventually_gt_atTop 0] with s hub hLpos
    have hRnn : 0 ≤ primeIdealZetaSum R s := by
      rw [primeIdealZetaSum]
      exact tsum_nonneg fun _ ↦ Real.rpow_nonneg (by positivity) _
    rw [Real.norm_of_nonneg (div_nonneg hRnn hLpos.le)]
    gcongr
  have hcomb : Tendsto (fun s : ℝ ↦
      primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s / Real.log (1 / (s - 1))
        - primeIdealZetaSum R s / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 1) := by
    simpa using (primeIdealZetaSum_univ_tendsto_log K).sub hRzero
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Set.mem_Ioi] at hs
  have hadd : primeIdealZetaSum U s + primeIdealZetaSum R s =
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
      rw [primeIdealZetaSum, primeIdealZetaSum, primeIdealZetaSum,
        ← ((show ∀ (S : Set (Ideal (𝓞 K))) {s : ℝ}, 1 < s → Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) from by
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
            fun _ _ hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab)).congr fun _ ↦ rfl) (S ∪ T) hs).tsum_subtype_add_tsum_subtype_compl
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
        unfold primeIdealZetaSum
        exact e.tsum_eq (fun 𝔭 ↦ (Ideal.absNorm (𝔭.1 : Ideal (𝓞 K)) : ℝ) ^ (-s))) hcover s]
  rw [← sub_div, ← hadd, add_sub_cancel_right]

/-- The nontrivial-character remainder `∑_{χ≠1} (χ σ)⁻¹ · twistedPrimeSum χ s` stays bounded as
`s ↓ 1`: each `χ ≠ 1` term is bounded by `artinLSeries_prime_sum_bounded_of_ne_one` (the `‖(χ σ)⁻¹‖
= 1` weight being harmless), and the finite sum of bounds is a bound for the sum. -/
private theorem exists_sum_charTwist_erase_norm_bounded
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2)
    [Fintype (galoisCharacter K L)] [DecidableEq (galoisCharacter K L)] (σ : Gal(L/K)) :
    ∃ CB : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      ‖∑ χ ∈ Finset.univ.erase (1 : galoisCharacter K L),
          ((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s‖ ≤ CB := by
  have : IsMulCommutative Gal(L/K) := IsCyclotomicExtension.isMulCommutative (S := {m}) K L
  have hterm : ∀ χ : galoisCharacter K L, χ ≠ 1 → ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      ‖((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s‖ ≤ C := fun χ hχ ↦ by
    obtain ⟨C, hC⟩ := artinLSeries_prime_sum_bounded_of_ne_one K L m hm χ hχ
    refine ⟨C, ?_⟩
    filter_upwards [hC] with s hs
    have hnorm1 : ‖((χ σ : ℂ))⁻¹‖ = 1 := by
      rw [norm_inv, inv_eq_one]
      exact (((Units.coeHom ℂ).comp χ).isOfFinOrder (isOfFinOrder_of_finite σ)).norm_eq_one
    rw [norm_mul, hnorm1, one_mul]
    exact hs
  have hCfun : ∀ χ : galoisCharacter K L, ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      χ ∈ Finset.univ.erase (1 : galoisCharacter K L) →
        ‖((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s‖ ≤ C := fun χ ↦ by
    by_cases hχ : χ = 1
    · refine ⟨0, ?_⟩
      filter_upwards with s hmem
      exact absurd (Finset.mem_erase.mp hmem).1 (not_not.mpr hχ)
    · obtain ⟨C, hC⟩ := hterm χ hχ
      refine ⟨C, ?_⟩
      filter_upwards [hC] with s hs _
      exact hs
  choose C hC using hCfun
  refine ⟨∑ χ ∈ Finset.univ.erase (1 : galoisCharacter K L), C χ, ?_⟩
  have hall : ∀ᶠ s in 𝓝[>] (1 : ℝ), ∀ χ ∈ Finset.univ.erase (1 : galoisCharacter K L),
      ‖((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s‖ ≤ C χ :=
    (eventually_all_finset _).mpr fun χ hmem ↦ (hC χ).mono fun s hs ↦ hs hmem
  filter_upwards [hall] with s hs
  calc ‖∑ χ ∈ Finset.univ.erase (1 : galoisCharacter K L), ((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s‖
      ≤ ∑ χ ∈ Finset.univ.erase (1 : galoisCharacter K L),
          ‖((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s‖ := norm_sum_le _ _
    _ ≤ ∑ χ ∈ Finset.univ.erase (1 : galoisCharacter K L), C χ :=
      Finset.sum_le_sum fun χ hχ ↦ hs χ hχ

/-- Sharifi 7.2.1 step (iv-a) — the numerator asymptotic. The prime-sum over the Frobenius fibre
`{σ_𝔭 = σ}` is asymptotic to `(1/|G|) log(1/(s-1))` as `s ↓ 1`. -/
theorem primeIdealZetaSum_frobeniusFibre_asymp
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2)
    (σ : Gal(L/K)) :
    Tendsto
      (fun s : ℝ ↦
        primeIdealZetaSum
            {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
              frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
          / Real.log (1 / (s - 1)))
      (𝓝[>] 1) (𝓝 ((Nat.card Gal(L/K) : ℝ)⁻¹)) := by
  classical
  have : Fintype (galoisCharacter K L) := Fintype.ofFinite _
  set N : ℕ := Nat.card Gal(L/K) with hN
  have hNpos : 0 < N := Nat.card_pos
  set B : ℝ → ℂ := fun s ↦ ∑ χ ∈ Finset.univ.erase (1 : galoisCharacter K L),
    ((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s
  obtain ⟨CB, hCB⟩ : ∃ CB : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), ‖B s‖ ≤ CB :=
    exists_sum_charTwist_erase_norm_bounded K L m hm σ
  have hBlog : Tendsto (fun s : ℝ ↦ (B s).re / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 0) := by
    have hL : Tendsto (fun s : ℝ ↦ Real.log (1 / (s - 1))) (𝓝[>] (1 : ℝ)) atTop := by
      refine Real.tendsto_log_atTop.comp ?_
      have h1 : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          (((continuous_sub_right 1).tendsto' 1 0 (by ring)).mono_left nhdsWithin_le_nhds)
          (eventually_nhdsWithin_of_forall fun s hs ↦ by
            simp only [Set.mem_Ioi] at hs ⊢
            linarith)
      simpa only [one_div] using! h1.inv_tendsto_nhdsGT_zero
    refine squeeze_zero_norm' ?_ (Filter.Tendsto.div_atTop tendsto_const_nhds hL (a := CB))
    filter_upwards [hCB, hL.eventually_gt_atTop 0] with s hub hLpos
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hLpos]
    gcongr
    exact (RCLike.abs_re_le_norm (B s)).trans hub
  have hlim : Tendsto (fun s : ℝ ↦ (N : ℝ)⁻¹ *
      (primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} s
          / Real.log (1 / (s - 1))
        + (B s).re / Real.log (1 / (s - 1)))) (𝓝[>] 1) (𝓝 ((N : ℝ)⁻¹)) := by
    have := ((primeIdealZetaSum_unramified_div_log_tendsto_one K L).add hBlog).const_mul (N : ℝ)⁻¹
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Set.mem_Ioi] at hs
  have hmaster : (N : ℝ) *
      primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
      = primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} s + (B s).re := by
    rw [hN]
    exact (show ∀ (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] [Fintype (galoisCharacter K L)] [DecidableEq (galoisCharacter K L)] (σ : Gal(L/K)) {s : ℝ} (hs : 1 < s), ((Nat.card Gal(L/K) : ℝ) * primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ frobeniusClass K L 𝔭 = ConjClasses.mk σ} s = primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} s + (∑ χ ∈ Finset.univ.erase (1 : galoisCharacter K L), ((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s).re) from by
      intro m root119Instance0 root119Instance1 root119Instance2 root119Instance3 σ s hs
      classical
      classical
      set U : Set (Ideal (𝓞 K)) := {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭}
      have hMb : (∑ χ : galoisCharacter K L, ((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s)
          = (primeIdealZetaSum U s : ℂ)
            + ∑ χ ∈ Finset.univ.erase (1 : galoisCharacter K L),
                ((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : galoisCharacter K L)),
          show ((1 : galoisCharacter K L) σ : ℂ) = 1 by simp, inv_one, one_mul, (show ∀ s : ℝ, twistedPrimeSum K L 1 s =
            (primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} s : ℂ) from by
            intro s
            have hinj : Function.Injective
                (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ∧
                    𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
                  (⟨𝔭.1, 𝔭.2.1.1, 𝔭.2.1.2⟩ : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭})) :=
              fun a b hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab)
            have hsurj : Function.Surjective
                (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ∧
                    𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
                  (⟨𝔭.1, 𝔭.2.1.1, 𝔭.2.1.2⟩ : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭})) :=
              fun 𝔭 ↦ ⟨⟨𝔭.1, ⟨𝔭.2.1, 𝔭.2.2⟩, 𝔭.2.1, (𝔭.2.2).1⟩, rfl⟩
            rw [twistedPrimeSum, primeIdealZetaSum, Complex.ofReal_tsum,
              ← hinj.tsum_eq (f := fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ↦
                ((1 : galoisCharacter K L) (frobeniusClass K L 𝔭.1).out : ℂ)
                  * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ)))
                (by rw [hsurj.range_eq]; exact Set.subset_univ _)]
            refine tsum_congr fun 𝔭 ↦ ?_
            rw [show ((1 : galoisCharacter K L) (frobeniusClass K L 𝔭.1).out : ℂ) = 1 by simp, one_mul,
              show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by push_cast; ring,
              Complex.ofReal_cpow (by positivity), Complex.ofReal_natCast])]
      have heq := ((show ∀ (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] [Fintype (galoisCharacter K L)] (σ : Gal(L/K)) {s : ℝ} (hs : 1 < s), ((∑ χ : galoisCharacter K L, ((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s) = (Nat.card Gal(L/K) : ℂ) * (primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ frobeniusClass K L 𝔭 = ConjClasses.mk σ} s : ℂ)) from by
        intro m root119Instance0 root119Instance1 root119Instance2 σ s hs
        classical
        classical
        have hfreal : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
            (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ)) = ((Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) : ℝ) := fun 𝔭 ↦ by
          rw [show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by push_cast; ring,
            Complex.ofReal_cpow (by positivity), Complex.ofReal_natCast]
        have hinterchange : (∑ χ : galoisCharacter K L, ((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s)
            = ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
                (∑ χ : galoisCharacter K L, ((χ σ : ℂ))⁻¹ * (χ (frobeniusClass K L 𝔭.1).out : ℂ))
                  * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ)) := by
          have hstep : ∀ χ : galoisCharacter K L, ((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s
              = ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
                  ((χ σ : ℂ))⁻¹ * (χ (frobeniusClass K L 𝔭.1).out : ℂ)
                    * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ)) := fun χ ↦ by
            rw [twistedPrimeSum, ← tsum_mul_left]
            exact tsum_congr fun 𝔭 ↦ by ring
          rw [Finset.sum_congr rfl fun χ _ ↦ hstep χ,
            ← Summable.tsum_finsetSum (fun χ _ ↦
              (((show ∀ (χ : galoisCharacter K L) {s : ℝ} (hs : 1 < s), (Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ↦ (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ)))) from by
                intro χ s hs
                classical
                have hs0 : Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ↦
                    (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) :=
                  (((show ∀ (S : Set (Ideal (𝓞 K))) {s : ℝ}, 1 < s → Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) from by
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
                      fun _ _ hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab)).congr fun _ ↦ rfl) _ hs).comp_injective
                    (i := fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ↦
                      (⟨𝔭.1, ⟨𝔭.2.1, 𝔭.2.2⟩, 𝔭.2.1, (𝔭.2.2).1⟩ :
                        {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}))
                    (fun _ _ hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab))).congr fun 𝔭 ↦ rfl
                have hnorm1 : ∀ c : ConjClasses Gal(L/K), ‖(χ c.out : ℂ)‖ = 1 := fun c ↦
                  (((Units.coeHom ℂ).comp χ).isOfFinOrder (isOfFinOrder_of_finite c.out)).norm_eq_one
                have hnormterm : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
                    ‖(χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ))‖ =
                      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) := fun 𝔭 ↦ by
                  have hpos : 0 < Ideal.absNorm 𝔭.1 := by
                    have hne : Ideal.absNorm 𝔭.1 ≠ 0 := fun h ↦
                      (𝔭.2.2).1 (Ideal.absNorm_eq_zero_iff.mp h)
                    lia
                  rw [norm_mul, hnorm1, one_mul, Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re,
                    Complex.ofReal_re]
                exact Summable.of_norm (hs0.congr fun 𝔭 ↦ (hnormterm 𝔭).symm)) χ hs).mul_left ((χ σ : ℂ))⁻¹).congr fun 𝔭 ↦ by ring)]
          exact tsum_congr fun 𝔭 ↦ (Finset.sum_mul _ _ _).symm
        have horth (g : Gal(L/K)) :
            (∑ χ : galoisCharacter K L, (χ g : ℂ)) =
              if g = 1 then (Nat.card Gal(L/K) : ℂ) else 0 := by
          haveI : IsMulCommutative Gal(L/K) :=
            IsCyclotomicExtension.isMulCommutative (S := {m}) K L
          letI : CommGroup Gal(L/K) := { mul_comm := mul_comm' }
          haveI : NeZero (Monoid.exponent Gal(L/K)) :=
            ⟨Monoid.exponent_ne_zero_of_finite⟩
          haveI : HasEnoughRootsOfUnity ℂ (Monoid.exponent Gal(L/K)) := inferInstance
          split_ifs with hg
          · subst hg
            simpa only [map_one, Units.val_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
              mul_one, ← Nat.card_eq_fintype_card]
              using congrArg Nat.cast
                (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity Gal(L/K) ℂ)
          · letI : AddGroup (Additive (galoisCharacter K L)) := inferInstance
            letI : CommSemiring ℂ := inferInstance
            let ψ : AddChar (Additive (galoisCharacter K L)) ℂ := {
              toFun := fun χ => ((Additive.toMul χ g : ℂˣ) : ℂ)
              map_zero_eq_one' := by simp
              map_add_eq_mul' := by
                intro χ τ
                change (((Additive.toMul χ * Additive.toMul τ) g : ℂˣ) : ℂ) =
                  ((Additive.toMul χ g : ℂˣ) : ℂ) * ((Additive.toMul τ g : ℂˣ) : ℂ)
                rw [MonoidHom.mul_apply, Units.val_mul] }
            have hψ : ψ ≠ 0 := by
              intro hzero
              obtain ⟨χ, hχ⟩ :=
                CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Gal(L/K) ℂ hg
              have hval := congrArg
                (fun φ : AddChar (Additive (galoisCharacter K L)) ℂ =>
                  φ (Additive.ofMul χ)) hzero
              exact hχ (Units.ext (by simpa [ψ] using hval))
            have hsum : (∑ χ : Additive (galoisCharacter K L), ψ χ) = 0 := by
              rw [AddChar.sum_eq_ite ψ, if_neg hψ]
            have htransport :
                (∑ χ : galoisCharacter K L, (χ g : ℂ)) =
                  ∑ χ : Additive (galoisCharacter K L), ψ χ :=
              Fintype.sum_equiv Additive.ofMul _ _ (fun χ => rfl)
            exact htransport.trans hsum
        have hcollapse : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
            (∑ χ : galoisCharacter K L, ((χ σ : ℂ))⁻¹ * (χ (frobeniusClass K L 𝔭.1).out : ℂ))
                * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ))
              = if frobeniusClass K L 𝔭.1 = ConjClasses.mk σ then
                  (Nat.card Gal(L/K) : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ)) else 0 := fun 𝔭 ↦ by
          haveI : IsMulCommutative Gal(L/K) :=
            IsCyclotomicExtension.isMulCommutative (S := {m}) K L
          let τ := (frobeniusClass K L 𝔭.1).out
          have hmk : ConjClasses.mk τ = frobeniusClass K L 𝔭.1 := Quotient.out_eq _
          have hchar :
              (∑ χ : galoisCharacter K L, ((χ σ : ℂ))⁻¹ * (χ τ : ℂ)) =
                ∑ χ : galoisCharacter K L, (χ (σ⁻¹ * τ) : ℂ) := by
            refine Finset.sum_congr rfl fun χ _ ↦ ?_
            rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
          rw [hchar, horth (σ⁻¹ * τ)]
          by_cases h : frobeniusClass K L 𝔭.1 = ConjClasses.mk σ
          · have hστ : σ = τ := by
              obtain ⟨c, hc⟩ : IsConj τ σ :=
                ConjClasses.mk_eq_mk_iff_isConj.mp (hmk.trans h)
              rw [SemiconjBy, mul_comm' (c : Gal(L/K))] at hc
              exact (mul_right_cancel hc).symm
            rw [if_pos (by simp [hστ]), if_pos h]
          · have hne : σ⁻¹ * τ ≠ 1 := by
              intro heq
              have hστ : σ = τ := inv_mul_eq_one.mp heq
              apply h
              rw [← hmk, hστ]
            rw [if_neg hne, if_neg h, zero_mul]
        have hfinj : Function.Injective
            (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
                frobeniusClass K L 𝔭 = ConjClasses.mk σ} ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
              (⟨𝔭.1, 𝔭.2.1.1, 𝔭.2.1.2.1⟩ : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭})) :=
          fun a b hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab)
        have hfibre : primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
              frobeniusClass K L 𝔭 = ConjClasses.mk σ} s =
            ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
              (if frobeniusClass K L 𝔭.1 = ConjClasses.mk σ then (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) else 0) :=
          by
          rw [primeIdealZetaSum, ← hfinj.tsum_eq
            (f := fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ↦
              if frobeniusClass K L 𝔭.1 = ConjClasses.mk σ then (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) else 0)
            ?_]
          · exact tsum_congr fun 𝔭 ↦ (if_pos 𝔭.2.1.2.2).symm
          · rintro 𝔭 h𝔭
            have h : frobeniusClass K L 𝔭.1 = ConjClasses.mk σ := by
              by_contra hne
              exact h𝔭 (if_neg hne)
            exact ⟨⟨𝔭.1, ⟨𝔭.2.1, 𝔭.2.2, h⟩, 𝔭.2.1, (𝔭.2.2).1⟩, rfl⟩
        rw [hinterchange, tsum_congr hcollapse, hfibre, Complex.ofReal_tsum, ← tsum_mul_left]
        refine tsum_congr fun 𝔭 ↦ ?_
        rw [apply_ite (Complex.ofReal), mul_ite, Complex.ofReal_zero, mul_zero, hfreal 𝔭]) m σ hs).symm.trans hMb
      have := congrArg Complex.re heq
      simpa [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.natCast_re,
        Complex.natCast_im] using this) m σ hs
  rw [← add_div, ← hmaster, mul_div_assoc, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast hNpos.ne'), one_mul]

/-- Sharifi 7.2.1 step (iv) — two-sided log-asymptotic comparison (p. 142).
Source: "on the one hand we have Σ_χ χ(σ)^{-1} log L(χ,s) ~ |G|
Σ_{φ_𝔭=σ} N𝔭^{-s}, whereas on the other we have Σ_χ χ(σ)^{-1} log L(χ,s)
~ log ζ_K(s) ~ log(s-1)^{-1}". Comparing yields density `1/|G|`. -/
theorem cyclotomic_density_from_two_sided_asymp
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2)
    (σ : Gal(L/K)) :
    Tendsto
      (fun s : ℝ ↦
        primeIdealZetaSum
            {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
              frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
          / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
      (𝓝[>] 1) (𝓝 ((Nat.card Gal(L/K) : ℝ)⁻¹)) :=
by
  have hnum := primeIdealZetaSum_frobeniusFibre_asymp K L m hm σ
  have hden := primeIdealZetaSum_univ_tendsto_log K
  have hlog : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), Real.log (1 / (s - 1)) ≠ 0 := by
    have h2 : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), s < 2 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
    filter_upwards [self_mem_nhdsWithin, h2] with s hs1 hs2
    have hpos : (0 : ℝ) < s - 1 := sub_pos.mpr hs1
    exact (Real.log_pos ((one_lt_div₀ hpos).2 (by linarith))).ne'
  exact (div_one ((Nat.card Gal(L/K) : ℝ)⁻¹) ▸ hnum.div hden one_ne_zero).congr'
    (hlog.mono fun s hs ↦ div_div_div_cancel_right₀ hs _ _)


end Chebotarev
