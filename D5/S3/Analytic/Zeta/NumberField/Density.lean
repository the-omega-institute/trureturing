/- GID: D5/S3/Analytic/Zeta/NumberField/Density
   generality: G
   mirror-B: D5/B/S3/Analytic/Zeta/NumberField/Density
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite prime-ideal sets have zero Dirichlet density. -/
module

public import D5.S3.Analytic.Zeta.NumberField.PrimeIdealLogTail

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Algebra.Order.Field
public import D5.S3.Analytic.Zeta.NumberField.NumberFieldEulerProduct
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.NumberTheory.NumberField.DirichletDensity
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# Dirichlet density of a set of prime ideals

For a number field `K`, the Dirichlet density of a set `S` of prime ideals of `𝓞 K` is, when it
exists,

  δ(S) = lim_{s → 1⁺} ( Σ_{𝔭 ∈ S} N𝔭^{-s} ) / ( Σ_𝔭 N𝔭^{-s} ),

with both sums running over nonzero prime ideals. The denominator is asymptotic to
`log (s - 1)^{-1}` as `s ↓ 1` (Sharifi, *Algebraic Number Theory*, §7.1.12; `docs/algnum.pdf`).

## Main definitions

* `Chebotarev.primeIdealZetaSum` — the partial Dirichlet series `Σ_{𝔭 ∈ S} N𝔭^{-s}`.
* `Chebotarev.HasDirichletDensity` — `S` has Dirichlet density `δ`.
* `Chebotarev.HasLowerDirichletDensity` — the `liminf` variant used in the
  Chebotarev argument (Sharifi 7.2.2 Step 2).

## References

* Sharifi, *Algebraic Number Theory*, §7.1.13 (`docs/algnum.pdf`).
* Stevenhagen–Lenstra, *Chebotarëv and his density theorem* (`docs/cheb.pdf`).
-/

@[expose] public section

noncomputable section

open Filter NumberField Topology Set

open scoped nonZeroDivisors

namespace Chebotarev

variable {K : Type*} [Field K] [NumberField K] {S : Set (Ideal (𝓞 K))} {δ : ℝ}


variable (K)

/-- Euler-product-log identity: `log ζ_K(s) = Σ_𝔭 N𝔭^{-s} + O(1)` as `s ↓ 1`
(Sharifi 7.1.12, p. 140). -/
theorem logDedekindZeta_sub_primeIdealZetaSum_bounded :
    ∃ C : ℝ, ∀ᶠ (s : ℝ) in 𝓝[>] (1 : ℝ), |Real.log (dedekindZeta K (s : ℂ)).re
      - primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s| ≤ C := by
  obtain ⟨C, hC⟩ := abs_tsum_neg_log_one_sub_sub_rpow_le K
  refine ⟨C, ?_⟩
  filter_upwards [hC, self_mem_nhdsWithin] with s hs_bound hs1
  simp only [mem_Ioi] at hs1
  have hreindex : primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s =
      ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) := by
    rw [primeIdealZetaSum, ← (Equiv.subtypeEquivRight fun 𝔭 ↦
      ⟨fun h ↦ ⟨mem_univ _, h⟩, And.right⟩).tsum_eq _]
    rfl
  rwa [log_dedekindZeta_re_eq_tsum_neg_log_one_sub K hs1,
    hreindex,
    ← ((show ∀ {s : ℝ}, 1 < s → Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ - Real.log (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s))) from by
      intro s hs
      exact ((Real.summable_log_one_add_of_summable
        ((show ∀ {s : ℝ}, 1 < s → Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) from by
          intro s hs
          exact (((show ∀ (S : Set (Ideal (𝓞 K))) {s : ℝ}, 1 < s → Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) from by
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
              fun _ _ hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab)).congr fun _ ↦ rfl) (univ : Set (Ideal (𝓞 K))) hs).comp_injective
            (Equiv.subtypeEquivRight fun _ ↦ ⟨(⟨mem_univ _, ·⟩), And.right⟩).injective).congr fun _ ↦ rfl) hs).neg).neg).congr fun _ ↦ rfl) hs1).tsum_sub
      ((show ∀ {s : ℝ}, 1 < s → Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) from by
        intro s hs
        exact (((show ∀ (S : Set (Ideal (𝓞 K))) {s : ℝ}, 1 < s → Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) from by
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
            fun _ _ hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab)).congr fun _ ↦ rfl) (univ : Set (Ideal (𝓞 K))) hs).comp_injective
          (Equiv.subtypeEquivRight fun _ ↦ ⟨(⟨mem_univ _, ·⟩), And.right⟩).injective).congr fun _ ↦ rfl) hs1)]

/-- Sharifi 7.1.12 proof (p. 140), lower bound: `log(1/(s-1)) - C ≤ Σ_𝔭 N𝔭^{-s}`. -/
theorem log_minus_bounded_le_primeIdealZetaSum :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      Real.log (1 / (s - 1)) - C
        ≤ primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s := by
  obtain ⟨C₁, h₁⟩ := logDedekindZeta_sub_primeIdealZetaSum_bounded K
  obtain ⟨C₂, h₂⟩ := (show ∃ C : ℝ, ∀ᶠ (s : ℝ) in 𝓝[>] (1 : ℝ),
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
  refine ⟨C₁ + C₂, ?_⟩
  filter_upwards [h₁, h₂] with s hs₁ hs₂
  linarith [abs_le.mp hs₁, abs_le.mp hs₂]

/-- Sharifi 7.1.12 proof (p. 140), upper bound: `Σ_𝔭 N𝔭^{-s} ≤ log(1/(s-1)) + C'`. -/
theorem primeIdealZetaSum_le_log_plus_bounded :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s
        ≤ Real.log (1 / (s - 1)) + C := by
  obtain ⟨C₁, h₁⟩ := logDedekindZeta_sub_primeIdealZetaSum_bounded K
  obtain ⟨C₂, h₂⟩ := (show ∃ C : ℝ, ∀ᶠ (s : ℝ) in 𝓝[>] (1 : ℝ),
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
  refine ⟨C₁ + C₂, ?_⟩
  filter_upwards [h₁, h₂] with s hs₁ hs₂
  linarith [abs_le.mp hs₁, abs_le.mp hs₂]

/-- **Sharifi 7.1.12**, *Algebraic Number Theory*, p. 140.

The denominator `Σ_𝔭 N𝔭^{-s}` is asymptotic to `log(1/(s-1))` as `s ↓ 1`. This is the analytic
ingredient that makes the Dirichlet-density definition robust under the L-function comparisons in
the Chebotarev proof. -/
theorem primeIdealZetaSum_univ_tendsto_log :
    Tendsto
      (fun s : ℝ ↦ primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s
        / Real.log (1 / (s - 1)))
      (𝓝[>] 1) (𝓝 1) := by
  obtain ⟨C₁, hle⟩ := primeIdealZetaSum_le_log_plus_bounded K
  obtain ⟨C₂, hlower⟩ := log_minus_bounded_le_primeIdealZetaSum K
  have hL : Tendsto (fun s : ℝ ↦ Real.log (1 / (s - 1))) (𝓝[>] (1 : ℝ)) atTop := by
    refine Real.tendsto_log_atTop.comp ?_
    have h1 : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (((continuous_sub_right 1).tendsto' 1 0 (by ring)).mono_left nhdsWithin_le_nhds)
        (eventually_nhdsWithin_of_forall fun s hs ↦ by
          simp only [Set.mem_Ioi] at hs ⊢
          linarith)
    simpa only [one_div] using! h1.inv_tendsto_nhdsGT_zero
  have h0 : Tendsto (fun s : ℝ ↦
      (primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s - Real.log (1 / (s - 1))) /
        Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 0) :=
    tendsto_bdd_div_atTop_nhds_zero (b := -C₂) (B := C₁)
      (hlower.mono fun s h ↦ by linarith) (hle.mono fun s h ↦ by linarith) hL
  refine (add_zero (1 : ℝ) ▸ h0.const_add 1).congr' ?_
  filter_upwards [hL.eventually_gt_atTop 0] with s h
  rw [add_div_eq_mul_add_div _ _ h.ne', one_mul, add_sub_cancel]

/-- The full prime-ideal zeta sum diverges to `+∞` as `s ↓ 1` (it is asymptotic to
`log(1/(s-1)) → ∞`). -/
theorem primeIdealZetaSum_univ_tendsto_atTop :
    Tendsto (primeIdealZetaSum (univ : Set (Ideal (𝓞 K)))) (𝓝[>] 1) atTop := by
  have hL : Tendsto (fun s : ℝ ↦ Real.log (1 / (s - 1))) (𝓝[>] (1 : ℝ)) atTop := by
    refine Real.tendsto_log_atTop.comp ?_
    have h1 : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (((continuous_sub_right 1).tendsto' 1 0 (by ring)).mono_left nhdsWithin_le_nhds)
        (eventually_nhdsWithin_of_forall fun s hs ↦ by
          simp only [Set.mem_Ioi] at hs ⊢
          linarith)
    simpa only [one_div] using! h1.inv_tendsto_nhdsGT_zero
  have hhalf : Tendsto (fun s : ℝ ↦ (1 / 2 : ℝ) * Real.log (1 / (s - 1))) (𝓝[>] 1) atTop :=
    hL.const_mul_atTop (by norm_num)
  refine tendsto_atTop_mono' _ ?_ hhalf
  filter_upwards [(primeIdealZetaSum_univ_tendsto_log K).eventually
      (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)), hL.eventually_gt_atTop 0] with s hs hpos
  exact ((lt_div_iff₀ hpos).mp hs).le

/-- **Squeeze to zero density from a constant numerator bound.** If the partial sum `Σ_{𝔭 ∈ U} N𝔭⁻ˢ`
is bounded above by a fixed constant `C` for all `s` near `1` (from the right), then the density
ratio `Σ_U / Σ_univ → 0`, since the denominator `→ ∞`. This is the common engine behind
`hasDirichletDensity_of_finite` (where `C = |U|`) and the degree-`≥ 2` / ramified tail bound in the
Chebotarev fixed-field reduction. -/
theorem tendsto_primeIdealZetaSum_div_univ_zero_of_le_const (U : Set (Ideal (𝓞 K))) (C : ℝ)
    (hbd : ∀ᶠ s in 𝓝[>] (1 : ℝ), primeIdealZetaSum U s ≤ C) :
    Tendsto (fun s : ℝ ↦ primeIdealZetaSum U s
      / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s) (𝓝[>] 1) (𝓝 0) := by
  have hUniv := primeIdealZetaSum_univ_tendsto_atTop K
  have hUnivPos : ∀ᶠ s in 𝓝[>] (1 : ℝ), 0 < primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s :=
    hUniv.eventually_gt_atTop 0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ ↦ 0)
    (h := fun s ↦ C / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s)
    tendsto_const_nhds (tendsto_const_nhds.div_atTop hUniv) ?_ ?_
  · filter_upwards [hUnivPos] with s hpos
    exact div_nonneg ((by unfold primeIdealZetaSum; exact tsum_nonneg fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)) hpos.le
  · filter_upwards [hUnivPos, hbd] with s hpos hle
    exact div_le_div_of_nonneg_right hle hpos.le

/-- **Density of a finite set of primes is `0`** (Sharifi 7.1.13). The numerator `Σ_{𝔭 ∈ S} N𝔭^{-s}`
is bounded (finitely many terms, each `≤ 1`) while the denominator `Σ_𝔭 N𝔭^{-s} → ∞`, so the ratio
`→ 0`. -/
theorem hasDirichletDensity_of_finite (hS : S.Finite) :
    HasDirichletDensity S 0 := by
  let T : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
    {𝔭 | 𝔭.asIdeal ∈ S}
  let e : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ≃ T :=
    { toFun := fun 𝔭 ↦ ⟨⟨𝔭.1, 𝔭.2.2.1, 𝔭.2.2.2⟩, 𝔭.2.1⟩
      invFun := fun 𝔭 ↦ ⟨𝔭.1.asIdeal, 𝔭.2, 𝔭.1.isPrime, 𝔭.1.ne_bot⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hTfin : T.Finite :=
    hS.preimage IsDedekindDomain.HeightOneSpectrum.asIdeal_injective.injOn
  refine tendsto_primeIdealZetaSum_div_univ_zero_of_le_const K S (T.ncard : ℝ) ?_
  refine eventually_nhdsWithin_of_forall fun s hs ↦ ?_
  calc
    primeIdealZetaSum S s = NumberField.Set.primeIdealZetaSum T s := by
      rw [NumberField.Set.primeIdealZetaSum_def, Chebotarev.primeIdealZetaSum]
      exact e.tsum_eq (fun 𝔭 : T ↦ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s))
    _ ≤ (T.ncard : ℝ) :=
      NumberField.Set.primeIdealZetaSum_le_card_of_finite hTfin
        (le_of_lt (zero_lt_one.trans hs))

end Chebotarev
