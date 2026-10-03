/- GID: D5/S3/Factorization/Galois/Chebotarev/AbelianCrossing
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/Chebotarev/AbelianCrossing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An admissible cyclotomic crossing bounds the Frobenius-fibre density liminf below. -/
module

public import D5.S3.Factorization.Galois.Chebotarev.CyclotomicCrossingFibres

public import D5.S3.Factorization.Galois.Chebotarev.Cyclotomic
public import D5.S3.Factorization.Galois.Chebotarev.FixedFieldDensity
public import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Chebotarev's theorem: abelian case

For an abelian Galois extension `L/K` of number fields and any
`σ ∈ Gal(L/K)`, the Dirichlet density of primes `𝔭` of `𝓞 K` (unramified in
`L`) whose Frobenius equals `σ` is `1 / |Gal(L/K)|`.

The proof reduces to the cyclotomic case by *crossing with cyclotomic
extensions* (Chebotarev's original technique). For `m` coprime to the
discriminant of `L`, the field `L(μ_m)` is Galois over `K` with
`Gal(L(μ_m)/K) ≅ G × H` where `H = Gal(K(μ_m)/K) ⊆ (ℤ/mℤ)^×`. For `τ ∈ H`
with `|G| | ord(τ)`, the subgroup `⟨(σ, τ)⟩` has trivial intersection with
`G × {1}`, so its fixed field `F` satisfies `F(μ_m) = L(μ_m)` — making
`L(μ_m)/F` cyclotomic. The cyclotomic case applied to `L(μ_m)/F` and
`(σ, τ)` gives
`δ_F(primes P with σ_P = (σ, τ)) = 1/(|G| · |H|)`, and the (cyclic)
reduction lifts this through `F/K` to a lower-density bound on the primes
of `K` with Frobenius `σ`. Summing over `τ ∈ H_n = {τ : n | ord(τ)}`,

  δ_inf,K({𝔭 : σ_𝔭 = σ}) ≥ |H_n| / (|G| · |H|).

As `m` varies (chosen via Dirichlet's theorem to satisfy `m ≡ 1 mod n^k` for
large `k`), `|H_n|/|H| → 1`, so `δ_inf ≥ 1/|G|`. Summing over `σ ∈ G` then
forces equality.

## Main results

* `Chebotarev.chebotarev_abelian` — the density of primes
  of `K` unramified in an abelian extension `L/K` with Frobenius equal to
  `σ` is `1/|Gal(L/K)|`.

## References

* Sharifi, *Algebraic Number Theory*, §7.2.2 Step 2 (`docs/algnum.pdf`,
  pp. 143–144).
* Stevenhagen–Lenstra, *Chebotarëv and his density theorem*, Appendix
  paragraph 4 (`docs/cheb.pdf`, p. 18).
-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

open NumberField Filter Topology Set

namespace Chebotarev

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]


/-- Sharifi 7.2.2 Step 2 — partial **lower bound** on `δ_inf(S_σ)` coming from one
cyclotomic crossing modulus `m`: `|H_n(m)|/(|G|·|H(m)|)` bounds the `liminf` of the
density ratio for `S_σ` in `K`. Source quote (p. 144): "δ_inf(S_σ) ≥ |H_n|/(|G|·|H|)".

The crossing is only valid at *admissible* `m`, so this per-`m` bound carries the same
two hypotheses as `exists_cyclotomicCrossing_fibres`: `hm4 : m % 4 ≠ 2` (feeding the
cyclotomic case) and `hcop : ((NumberField.discr L).natAbs).Coprime m` (the
linear-disjointness via the everywhere-unramified intersection / `discr_dvd_discr`). The
consumer `liminf_ratio_ge_inv_card_G` drives `m` along admissible primes. -/
theorem liminf_density_S_sigma_ge_card_H_n_div_GH
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [hAb : IsMulCommutative Gal(L/K)] (σ : Gal(L/K)) (m : ℕ) (_hm : 1 ≤ m)
    (hm4 : m % 4 ≠ 2) (hcop : ((NumberField.discr L).natAbs).Coprime m) :
    (Nat.card {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ} : ℝ)
        / (Nat.card Gal(L/K) * Nat.card ((ZMod m)ˣ))
      ≤ Filter.liminf
          (fun s : ℝ ↦
            primeIdealZetaSum
                {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
                  frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
              / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
          (𝓝[>] 1) := by
  classical
  set Sσ : Set (Ideal (𝓞 K)) :=
    {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ frobeniusClass K L 𝔭 = ConjClasses.mk σ}
    with hSσ
  set c : ℝ := (Nat.card Gal(L/K) * Nat.card ((ZMod m)ˣ) : ℝ)⁻¹ with hc
  obtain ⟨S, hpd, hsub, hd⟩ := exists_cyclotomicCrossing_fibres K L σ m _hm hm4 hcop
  have : Fintype {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ} := Fintype.ofFinite _
  set t : Finset {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ} := Finset.univ with ht
  have hpd' : (t : Set {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ}).PairwiseDisjoint S := by
    rw [ht, Finset.coe_univ]; exact hpd
  have hsummablePrime : ∀ (S : Set (Ideal (𝓞 K))) {s : ℝ}, 1 < s →
      Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
        (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) := by
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
      fun _ _ hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab)).congr fun _ ↦ rfl
  have hUdens : HasDirichletDensity (⋃ i ∈ t, S i) ((t.card : ℝ) • c) :=
    (show ∀ (t : Finset {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ}) (S : {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ} → Set (Ideal (𝓞 K))) (c : ℝ) (hdisj : (t : Set {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ}).PairwiseDisjoint S) (hdens : ∀ i ∈ t, HasDirichletDensity (S i) c), (HasDirichletDensity (⋃ i ∈ t, S i) ((t.card : ℝ) • c)) from by
      intro t S c hdisj hdens
      classical
      classical
      induction t using Finset.induction with
      | empty =>
          have : IsEmpty {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ (∅ : Set (Ideal (𝓞 K))) ∧
              𝔭.IsPrime ∧ 𝔭 ≠ ⊥} := ⟨(·.2.1)⟩
          have hempty : HasDirichletDensity (∅ : Set (Ideal (𝓞 K))) 0 := by
            simpa only [HasDirichletDensity, primeIdealZetaSum, tsum_empty, zero_div]
              using tendsto_const_nhds
          simpa using hempty
      | insert a t ha ih =>
          have hdisj' : (t : Set {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ}).PairwiseDisjoint S :=
            hdisj.subset (Finset.coe_subset.mpr (Finset.subset_insert a t))
          have hdisjUnion : Disjoint (S a) (⋃ i ∈ t, S i) :=
            Set.disjoint_iUnion₂_right.2 fun i hi ↦
              hdisj (Finset.mem_insert_self a t) (Finset.mem_insert_of_mem hi) fun h ↦ ha (h ▸ hi)
          have hbase := hdens a (Finset.mem_insert_self a t)
          have hrec := ih hdisj' fun i hi ↦ hdens i (Finset.mem_insert_of_mem hi)
          have hcard : ((insert a t).card : ℝ) • c = c + (t.card : ℝ) • c := by
            rw [Finset.card_insert_of_notMem ha]; push_cast; ring
          rw [Finset.set_biUnion_insert, hcard]
          have hsumEq : ∀ {s : ℝ}, 1 < s →
              primeIdealZetaSum (S a ∪ ⋃ i ∈ t, S i) s =
                primeIdealZetaSum (S a) s + primeIdealZetaSum (⋃ i ∈ t, S i) s := by
            intro s hs
            let A : Set (Ideal (𝓞 K)) :=
              {𝔭 | 𝔭 ∈ S a ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}
            let B : Set (Ideal (𝓞 K)) :=
              {𝔭 | 𝔭 ∈ (⋃ i ∈ t, S i) ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}
            have hAB : Disjoint A B :=
              hdisjUnion.mono (fun 𝔭 h𝔭 ↦ h𝔭.1) (fun 𝔭 h𝔭 ↦ h𝔭.1)
            have hABunion : A ∪ B =
                {𝔭 : Ideal (𝓞 K) | 𝔭 ∈ (S a ∪ ⋃ i ∈ t, S i) ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} := by
              ext 𝔭
              simp only [A, B, Set.mem_union, Set.mem_setOf_eq]
              tauto
            let f : Ideal (𝓞 K) → ℝ := fun 𝔭 ↦ (Ideal.absNorm 𝔭 : ℝ) ^ (-s)
            have hA : Summable (fun 𝔭 : A ↦ f 𝔭.1) := hsummablePrime (S a) hs
            have hB : Summable (fun 𝔭 : B ↦ f 𝔭.1) := hsummablePrime (⋃ i ∈ t, S i) hs
            have hUnion : (∑' 𝔭 : ↑(A ∪ B), f 𝔭.1) =
                (∑' 𝔭 : A, f 𝔭.1) + ∑' 𝔭 : B, f 𝔭.1 :=
              Summable.tsum_union_disjoint (f := f) (s := A) (t := B) hAB hA hB
            have hReplace : (∑' 𝔭 : ↑(A ∪ B), f 𝔭.1) =
                ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) | 𝔭 ∈ (S a ∪ ⋃ i ∈ t, S i) ∧
                  𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, f 𝔭.1 :=
              congrArg (fun C : Set (Ideal (𝓞 K)) ↦ ∑' 𝔭 : C, f 𝔭.1) hABunion
            exact hReplace.symm.trans hUnion
          change Tendsto
            (fun s : ℝ ↦ primeIdealZetaSum (S a ∪ ⋃ i ∈ t, S i) s /
              primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
            (𝓝[>] 1) (𝓝 (c + (t.card : ℝ) • c))
          change Tendsto
            (fun s : ℝ ↦ primeIdealZetaSum (S a) s /
              primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
            (𝓝[>] 1) (𝓝 c) at hbase
          change Tendsto
            (fun s : ℝ ↦ primeIdealZetaSum (⋃ i ∈ t, S i) s /
              primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
            (𝓝[>] 1) (𝓝 ((t.card : ℝ) • c)) at hrec
          have hsumTend := hbase.add hrec
          apply hsumTend.congr'
          filter_upwards [self_mem_nhdsWithin] with s hs
          simp only [Set.mem_Ioi] at hs
          rw [hsumEq hs, add_div]) t S c hpd' fun i _ ↦ hd i
  have hUsub : (⋃ i ∈ t, S i) ⊆ Sσ := Set.iUnion₂_subset fun i _ ↦ hsub i
  have hUlow : HasLowerDirichletDensity (⋃ i ∈ t, S i) ((t.card : ℝ) • c) := hUdens.liminf_eq
  have hSσlow : HasLowerDirichletDensity Sσ
      (Filter.liminf
        (fun s : ℝ ↦ primeIdealZetaSum Sσ s / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
        (𝓝[>] 1)) := rfl
  have hmono := (show ∀ {S T : Set (Ideal (𝓞 K))}, S ⊆ T → ∀ {δ ε : ℝ}, HasLowerDirichletDensity S δ → HasLowerDirichletDensity T ε → δ ≤ ε from by
    intro S T hST δ ε hS hT
    rw [HasLowerDirichletDensity] at hS hT
    rw [← hS, ← hT]
    refine liminf_le_liminf ?_ ((show ∀ (S : Set (Ideal (𝓞 K))), IsBoundedUnder (· ≥ ·) (𝓝[>] (1 : ℝ)) (fun s ↦ primeIdealZetaSum S s / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s) from by
      intro S
      exact isBoundedUnder_of ⟨0, fun s ↦ div_nonneg ((by unfold primeIdealZetaSum; exact tsum_nonneg fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _))
        ((by unfold primeIdealZetaSum; exact tsum_nonneg fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _))⟩) S)
      (isCoboundedUnder_ge_of_eventually_le (x := 1) _
        ((show ∀ (S : Set (Ideal (𝓞 K))), ∀ᶠ s in 𝓝[>] (1 : ℝ), primeIdealZetaSum S s / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s ≤ 1 from by
          intro S
          filter_upwards [self_mem_nhdsWithin] with s hs using
            div_le_one_of_le₀ ((show ∀ {S : Set (Ideal (𝓞 K))} {s : ℝ}, 1 < s → primeIdealZetaSum S s ≤ primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s from by
              intro S s hs
              rw [primeIdealZetaSum, primeIdealZetaSum]
              refine ((show ∀ (S : Set (Ideal (𝓞 K))) {s : ℝ}, 1 < s → Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) from by
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
                  fun _ _ hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab)).congr fun _ ↦ rfl) S hs).tsum_le_tsum_of_inj
                (fun 𝔭 ↦ ⟨𝔭.1, mem_univ _, 𝔭.2.2.1, 𝔭.2.2.2⟩)
                (fun a b hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab))
                (fun c _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
                (fun _ ↦ le_rfl) ((show ∀ (S : Set (Ideal (𝓞 K))) {s : ℝ}, 1 < s → Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) from by
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
                    fun _ _ hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab)).congr fun _ ↦ rfl) (univ : Set (Ideal (𝓞 K))) hs)) hs) ((by unfold primeIdealZetaSum; exact tsum_nonneg fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _))) T))
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact div_le_div_of_nonneg_right ((show ∀ {S T : Set (Ideal (𝓞 K))}, S ⊆ T → ∀ {s : ℝ}, 1 < s → primeIdealZetaSum S s ≤ primeIdealZetaSum T s from by
      intro S T hST s hs
      rw [primeIdealZetaSum, primeIdealZetaSum]
      refine ((show ∀ (S : Set (Ideal (𝓞 K))) {s : ℝ}, 1 < s → Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) from by
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
          fun _ _ hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab)).congr fun _ ↦ rfl) S hs).tsum_le_tsum_of_inj
        (fun 𝔭 ↦ ⟨𝔭.1, hST 𝔭.2.1, 𝔭.2.2.1, 𝔭.2.2.2⟩)
        (fun a b hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab))
        (fun c _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (fun _ ↦ le_rfl) ((show ∀ (S : Set (Ideal (𝓞 K))) {s : ℝ}, 1 < s → Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) from by
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
            fun _ _ hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab)).congr fun _ ↦ rfl) T hs)) hST hs)
      ((by unfold primeIdealZetaSum; exact tsum_nonneg fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _))) hUsub hUlow hSσlow
  have htcard : (t.card : ℝ) • c
      = (Nat.card {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ} : ℝ)
          / (Nat.card Gal(L/K) * Nat.card ((ZMod m)ˣ)) := by
    rw [ht, Finset.card_univ, hc, smul_eq_mul, ← Nat.card_eq_fintype_card, div_eq_mul_inv]
  rw [htcard] at hmono
  exact hmono

end Chebotarev
