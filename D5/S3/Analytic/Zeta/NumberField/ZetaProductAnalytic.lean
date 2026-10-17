/- GID: D5/S3/Analytic/Zeta/NumberField/ZetaProductAnalytic
   generality: G
   mirror-B: D5/B/S3/Analytic/Zeta/NumberField/ZetaProductAnalytic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A nontrivial cyclotomic Artin series has an analytic extension to the stated half-plane. -/
module

public import D5.S3.Analytic.Zeta.NumberField.ZetaProductL2

@[expose] public section

noncomputable section

open NumberField MeasureTheory Set

open scoped nonZeroDivisors

namespace Chebotarev

/-- **Geometry of numbers (Sharifi 7.1.19, p. 142).** For a nontrivial
character `χ` of order `n = orderOf χ`, the number of nonzero ideals `𝔞 ⊆ 𝓞 K` with `N𝔞 ≤ N`
and `χ(𝔞) = ζ` is `C·N + O(N^{1-1/d})` (`d = [K:ℚ]`), with the **leading constant `C` independent
of `ζ`**. Verbatim (p. 142):
> "The geometry of numbers can be used to show that the number of ideals `𝔞` of `𝒪_K` with
> `N𝔞 ≤ N` for `N ≥ 1` and `χ(𝔞) = ζ` is `CN + O(N^{1−d⁻¹})`, where `C` is a constant
> independent of `ζ`."

**Cyclotomic generality**: the general-abelian value-fibre
count needs class field theory, but for `L = K(μ_m)` it is CFT-free. The reduction is now an
**exact set equality** (not a thin-error bridge): for `ζ ≠ 0` the value-fibre `{χ(𝔞) = ζ}` equals
the **unramified-supported** Frobenius-value-fibre `{U 𝔞 ∧ χ(Frob_𝔞) = ζ}`, where
`U 𝔞 := ∀ 𝔭 ∈ normalizedFactors 𝔞, UnramifiedIn K L 𝔭`. Here `U` is the exact
support condition `χ(𝔞) ≠ 0`, since `χ(𝔞) = 0` whenever a factor is ramified while the junk-class
`Frob_𝔞` ignores ramified factors. Partitioning that fibre over `S_ζ = {g : χ g = ζ}`
(`|S_ζ| = |ker χ|`) and applying the **unramified-supported**
Frobenius-fibre equidistribution (`exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le`, L2) per `g`,
with leading density `κ` independent of `g`, gives `C = |ker χ|·κ` and `C' = |ker χ|·C₂`, both
independent of `ζ`. The
class-independent leading term is mathlib's `tendsto_norm_le_and_mk_eq_div_atTop`; the new content —
the project's deepest analytic input — is the effective `O(N^{1-1/d})` boundary rate, supplied
by `Chebotarev.exists_card_inter_smul_lattice_sub_volume_mul_pow_le` (the effective
Lipschitz-boundary lattice-point count in `ForMathlib/LatticePointCount.lean`, a standalone
mathlib-PR) fed by the Lipschitz-frontier input `normLeOne_frontier_lipschitz_cover`. -/
theorem exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2) (χ : galoisCharacter K L) (_hχ : χ ≠ 1) :
    ∃ C C' : ℝ, ∀ ζ : ℂ, ζ ^ orderOf χ = 1 → ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {𝔞 : Ideal (𝓞 K) //
            𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ galoisCharacterOnIdeal K L χ 𝔞 = ζ} : ℝ)
          - C * (N : ℝ)|
        ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  obtain ⟨κ, C₂, hL2⟩ := exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le K L m hm
  set κ₀ : ℕ := Nat.card (MonoidHom.ker χ) with hκ₀
  refine ⟨(κ₀ : ℝ) * κ, (κ₀ : ℝ) * C₂, fun ζ hζ N hN ↦ ?_⟩
  set P : ℝ := (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) with hP
  have hord : 0 < orderOf χ := orderOf_pos_iff.mpr (isOfFinOrder_of_finite χ)
  have hζ0 : ζ ≠ 0 := by
    intro h; subst h
    rw [zero_pow hord.ne'] at hζ
    exact zero_ne_one hζ
  set ζu : ℂˣ := Units.mk0 ζ hζ0
  have hζuval : (ζu : ℂ) = ζ := rfl
  have hζun : ζu ^ orderOf χ = 1 := by
    apply Units.ext; push_cast; rw [hζuval]; exact hζ
  set B : ℝ := (Nat.card {𝔞 : Ideal (𝓞 K) //
      𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
        (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
          (χ (frobeniusIdeal K L 𝔞) : ℂ) = ζ} : ℝ) with hB
  have hAB : (Nat.card {𝔞 : Ideal (𝓞 K) //
      𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ galoisCharacterOnIdeal K L χ 𝔞 = ζ} : ℝ) = B := by
    rw [hB]
    exact congrArg _
      ((show ∀      
          [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
          [IsCyclotomicExtension {m} K L] (χ : galoisCharacter K L) (ζ : ℂ) (hζ : ζ ≠ 0) (N : ℕ), (Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ galoisCharacterOnIdeal K L χ 𝔞 = ζ} = Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧ (χ (frobeniusIdeal K L 𝔞) : ℂ) = ζ}) from by
        intro cnrInstance0 cnrInstance1 m cnrInstance2 cnrInstance3 χ ζ hζ N
        classical
        refine Nat.card_congr (Equiv.subtypeEquivRight fun 𝔞 ↦ and_congr_right fun h𝔞 ↦
          and_congr_right fun _hN ↦ ?_)
        constructor
        · intro hval
          have hU : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭 :=
            fun 𝔭 ↦ (show ∀      
                (χ : galoisCharacter K L) {𝔞 𝔭 : Ideal (𝓞 K)} (h : galoisCharacterOnIdeal K L χ 𝔞 ≠ 0)
                (h𝔭 : 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞), (UnramifiedIn K L 𝔭) from by
              intro χ 𝔞 𝔭 h h𝔭
              classical
              by_contra hnr
              refine h ?_
              rw [galoisCharacterOnIdeal, ← Finset.prod_multiset_map_count]
              exact Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨𝔭, h𝔭, if_neg hnr⟩)) χ
              (hval ▸ hζ)
          exact ⟨hU, by rwa [← (show ∀      
              [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
              [IsCyclotomicExtension {m} K L] (χ : galoisCharacter K L) {𝔞 : Ideal (𝓞 K)}
              (hU : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭), (galoisCharacterOnIdeal K L χ 𝔞 = (χ (frobeniusIdeal K L 𝔞) : ℂ)) from by
            intro cnrInstance0 cnrInstance1 m cnrInstance2 cnrInstance3 χ 𝔞 hU
            classical
            letI : CommGroup Gal(L/K) := { mul_comm := mul_comm' }
            have hfrob : (χ (frobeniusIdeal K L 𝔞) : ℂ) =
                ((UniqueFactorizationMonoid.normalizedFactors 𝔞).map
                  (fun 𝔭 ↦ (χ (frobeniusClass K L 𝔭).out : ℂ))).prod := by
              rw [frobeniusIdeal, map_multiset_prod, ← Units.coeHom_apply, map_multiset_prod,
                Multiset.map_map, Multiset.map_map]
              rfl
            rw [galoisCharacterOnIdeal, ← Finset.prod_multiset_map_count, hfrob]
            refine congrArg Multiset.prod (Multiset.map_congr rfl fun 𝔭 h𝔭 ↦ ?_)
            rw [if_pos (hU 𝔭 h𝔭)]) m χ hU]⟩
        · rintro ⟨hU, hfrob⟩
          rw [(show ∀      
              [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
              [IsCyclotomicExtension {m} K L] (χ : galoisCharacter K L) {𝔞 : Ideal (𝓞 K)}
              (hU : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭), (galoisCharacterOnIdeal K L χ 𝔞 = (χ (frobeniusIdeal K L 𝔞) : ℂ)) from by
            intro cnrInstance0 cnrInstance1 m cnrInstance2 cnrInstance3 χ 𝔞 hU
            classical
            letI : CommGroup Gal(L/K) := { mul_comm := mul_comm' }
            have hfrob : (χ (frobeniusIdeal K L 𝔞) : ℂ) =
                ((UniqueFactorizationMonoid.normalizedFactors 𝔞).map
                  (fun 𝔭 ↦ (χ (frobeniusClass K L 𝔭).out : ℂ))).prod := by
              rw [frobeniusIdeal, map_multiset_prod, ← Units.coeHom_apply, map_multiset_prod,
                Multiset.map_map, Multiset.map_map]
              rfl
            rw [galoisCharacterOnIdeal, ← Finset.prod_multiset_map_count, hfrob]
            refine congrArg Multiset.prod (Multiset.map_congr rfl fun 𝔭 h𝔭 ↦ ?_)
            rw [if_pos (hU 𝔭 h𝔭)]) m χ hU]
          exact hfrob) m χ ζ hζ0 N)
  rw [hAB]
  have hpart : B = ∑ g : {g : Gal(L/K) // (χ g : ℂ) = ζ},
      (Nat.card {𝔞 : Ideal (𝓞 K) //
        𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
          (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
            frobeniusIdeal K L 𝔞 = g.1} : ℝ) := by
    rw [hB, (show ∀ [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] (χ : galoisCharacter K L) (ζ : ℂ) (N : ℕ), (Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧ (χ (frobeniusIdeal K L 𝔞) : ℂ) = ζ} = ∑ g : {g : Gal(L/K) // (χ g : ℂ) = ζ}, Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧ frobeniusIdeal K L 𝔞 = g.1}) from by
      intro analyticInstance0 analyticInstance1 m analyticInstance2 analyticInstance3 χ ζ N
      classical
      classical
      haveI hfinN : Finite {𝔞 : Ideal (𝓞 K) // Ideal.absNorm 𝔞 ≤ N} :=
        (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) N).to_subtype
      haveI hfin : ∀ g : {g : Gal(L/K) // (χ g : ℂ) = ζ},
          Finite {𝔞 : Ideal (𝓞 K) //
            𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
              (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
                frobeniusIdeal K L 𝔞 = g.1} := fun g ↦
        Finite.of_injective
          (fun a ↦ (⟨a.1, a.2.2.1⟩ : {𝔞 : Ideal (𝓞 K) // Ideal.absNorm 𝔞 ≤ N}))
          (fun _ _ hab ↦ by ext1; simpa using hab)
      rw [← Nat.card_sigma]
      refine (Nat.card_congr (Equiv.ofBijective
        (fun a ↦ (⟨a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2.1, by rw [a.2.2.2.2.2]; exact a.1.2⟩ :
          {𝔞 : Ideal (𝓞 K) //
            𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
              (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
                (χ (frobeniusIdeal K L 𝔞) : ℂ) = ζ})) ⟨?_, ?_⟩)).symm
      · rintro ⟨⟨g₁, hg₁⟩, ⟨𝔞, ha1, ha2, haU, ha3⟩⟩ ⟨⟨g₂, hg₂⟩, ⟨𝔟, hb1, hb2, hbU, hb3⟩⟩ hab
        have h𝔞𝔟 : 𝔞 = 𝔟 := congrArg Subtype.val hab
        subst h𝔞𝔟
        have hg : g₁ = g₂ := ha3.symm.trans hb3
        subst hg
        rfl
      · rintro ⟨𝔞, h1, h2, hU, h3⟩
        exact ⟨⟨⟨frobeniusIdeal K L 𝔞, h3⟩, ⟨𝔞, h1, h2, hU, rfl⟩⟩, rfl⟩) m χ ζ N, Nat.cast_sum]
  have hSκ₀ : Nat.card {g : Gal(L/K) // (χ g : ℂ) = ζ} = κ₀ := by
    rw [hκ₀]
    have heq : {g : Gal(L/K) // (χ g : ℂ) = ζ} = {g : Gal(L/K) // χ g = ζu} := by
      congr 1; ext g
      rw [← hζuval]
      exact ⟨fun h ↦ Units.ext h, fun h ↦ congrArg Units.val h⟩
    rw [heq]
    letI : CommGroup Gal(L/K) := { mul_comm := mul_comm' }
    haveI : NeZero (orderOf χ) := ⟨hord.ne'⟩
    haveI : Finite (MonoidHom.range χ) :=
      Finite.of_surjective χ.rangeRestrict χ.rangeRestrict_surjective
    have hpow : ∀ g : Gal(L/K), (χ g) ^ orderOf χ = 1 := fun g ↦ by
      rw [← MonoidHom.pow_apply, pow_orderOf_eq_one, MonoidHom.one_apply]
    have hsub : MonoidHom.range χ ≤ rootsOfUnity (orderOf χ) ℂ := by
      rintro x ⟨g, rfl⟩
      exact (mem_rootsOfUnity (orderOf χ) (χ g)).mpr (hpow g)
    have hpowexp : ∀ g : Gal(L/K),
        (χ g) ^ Monoid.exponent (MonoidHom.range χ) = 1 := fun g ↦ by
      have hmem : χ g ∈ MonoidHom.range χ := ⟨g, rfl⟩
      simpa using congrArg Subtype.val
        (Monoid.pow_exponent_eq_one (⟨χ g, hmem⟩ : MonoidHom.range χ))
    have hoe : orderOf χ = Monoid.exponent (MonoidHom.range χ) := by
      apply Nat.dvd_antisymm
      · rw [orderOf_dvd_iff_pow_eq_one]
        exact MonoidHom.ext fun g ↦ by simpa [MonoidHom.pow_apply] using hpowexp g
      · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
        rintro ⟨x, g, rfl⟩
        exact Subtype.ext (by simpa [Subgroup.coe_pow] using hpow g)
    have himage : MonoidHom.range χ = rootsOfUnity (orderOf χ) ℂ :=
      Subgroup.eq_of_le_of_card_ge hsub (by
        rw [Complex.card_rootsOfUnity, hoe,
          IsCyclic.exponent_eq_card (α := MonoidHom.range χ)])
    obtain ⟨g₀, hg₀⟩ : ∃ g : Gal(L/K), χ g = ζu :=
      χ.mem_range.mp (himage ▸ (mem_rootsOfUnity (orderOf χ) ζu).mpr hζun)
    refine Nat.card_congr ((Equiv.subtypeEquivProp ?_).trans (χ.fiberEquivKer g₀))
    ext g
    simp [Set.mem_preimage, hg₀]
  have hcardℝ : (Fintype.card {g : Gal(L/K) // (χ g : ℂ) = ζ} : ℝ) = (κ₀ : ℝ) := by
    rw [← Nat.card_eq_fintype_card, hSκ₀]
  rw [hpart]
  calc
    |∑ g : {g : Gal(L/K) // (χ g : ℂ) = ζ},
          (Nat.card {𝔞 : Ideal (𝓞 K) //
            𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
              (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
                frobeniusIdeal K L 𝔞 = g.1} : ℝ)
          - (κ₀ : ℝ) * κ * N|
        = |∑ g : {g : Gal(L/K) // (χ g : ℂ) = ζ},
            ((Nat.card {𝔞 : Ideal (𝓞 K) //
              𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
                (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
                  frobeniusIdeal K L 𝔞 = g.1} : ℝ) - κ * N)| := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardℝ]
          ring_nf
    _ ≤ ∑ g : {g : Gal(L/K) // (χ g : ℂ) = ζ},
          |(Nat.card {𝔞 : Ideal (𝓞 K) //
            𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
              (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
                frobeniusIdeal K L 𝔞 = g.1} : ℝ) - κ * N| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _g : {g : Gal(L/K) // (χ g : ℂ) = ζ}, C₂ * P :=
          Finset.sum_le_sum fun g _ ↦ hL2 g.1 N hN
    _ = (κ₀ : ℝ) * C₂ * P := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardℝ]; ring


/-- Sharifi 7.1.19 step 1 (p. 142): geometry-of-numbers bound. The
partial-sum character sum `Σ_{N𝔞≤N} χ(𝔞)` (with `χ(𝔞) = galoisCharacterOnIdeal K L χ 𝔞` the
completely-multiplicative ideal character) is `O(N^{1-1/[K:ℚ]})` for a
nontrivial character `χ`. This is the convergence input that extends
`L(χ,·)` to `Z(1 - [K:ℚ]^{-1})`. -/
theorem character_sum_geometry_of_numbers_bound
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2) (χ : galoisCharacter K L) (_hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ N : ℕ,
      ‖∑' 𝔞 : {𝔞 : Ideal (𝓞 K) //
                𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N},
        galoisCharacterOnIdeal K L χ 𝔞.1‖
        ≤ C * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  obtain ⟨C₀, C', hcount⟩ := exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow K L m hm χ _hχ
  refine ⟨(orderOf χ : ℝ) * C', fun N ↦ ?_⟩
  have hC' : 0 ≤ C' := (abs_nonneg _).trans (by simpa using hcount 1 (one_pow _) 1 le_rfl)
  rcases Nat.eq_zero_or_pos N with rfl | hN1
  · haveI : IsEmpty {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ 0} :=
      ⟨fun 𝔞 ↦ 𝔞.2.1 (Ideal.absNorm_eq_zero_iff.mp (Nat.le_zero.mp 𝔞.2.2))⟩
    rw [tsum_empty, norm_zero]
    positivity
  have hord0 : orderOf χ ≠ 0 := (orderOf_pos_iff.mpr (isOfFinOrder_of_finite χ)).ne'
  have hord2 : 1 < orderOf χ :=
    lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr hord0) fun h ↦ _hχ (orderOf_eq_one_iff.mp h.symm)
  obtain ⟨ζ₀, hζ₀⟩ : ∃ z : ℂ, IsPrimitiveRoot z (orderOf χ) :=
    ⟨_, Complex.isPrimitiveRoot_exp _ hord0⟩
  set R : Finset ℂ := Polynomial.nthRootsFinset (orderOf χ) (1 : ℂ) with hR
  have hmemR : ∀ {z : ℂ}, z ∈ R ↔ z ^ orderOf χ = 1 := fun {z} ↦
    Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hord0) 1
  haveI := (show ∀ (N : ℕ), (Finite {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N}) from by
    intro N
    classical
    exact
      haveI : Finite {𝔞 : Ideal (𝓞 K) // Ideal.absNorm 𝔞 ≤ N} :=
        (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) N).to_subtype
      Finite.of_injective (fun a ↦ (⟨a.1, a.2.2⟩ : {𝔞 : Ideal (𝓞 K) // Ideal.absNorm 𝔞 ≤ N}))
        fun _ _ hab ↦ Subtype.ext (by simpa using hab)) N
  haveI := Fintype.ofFinite {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N}
  have hsum :
    ∑ 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N},
        galoisCharacterOnIdeal K L χ 𝔞.1
      = ∑ v ∈ Polynomial.nthRootsFinset (orderOf χ) 1,
          (((Nat.card {𝔞 : Ideal (𝓞 K) //
            𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ galoisCharacterOnIdeal K L χ 𝔞 = v} : ℝ)
              - C₀ * N : ℝ) : ℂ) * v := by
    classical
    obtain ⟨ζ₀, hζ₀⟩ : ∃ z : ℂ, IsPrimitiveRoot z (orderOf χ) :=
      ⟨_, Complex.isPrimitiveRoot_exp _ (by lia)⟩
    have h0R : (0 : ℂ) ∉ Polynomial.nthRootsFinset (orderOf χ) 1 := fun h ↦ by
      rw [Polynomial.mem_nthRootsFinset (by lia) 1, zero_pow (by lia)] at h
      exact zero_ne_one h
    calc ∑ 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N},
          galoisCharacterOnIdeal K L χ 𝔞.1
        = ∑ v ∈ insert (0 : ℂ) (Polynomial.nthRootsFinset (orderOf χ) 1),
            ∑ 𝔞 ∈ (Finset.univ : Finset {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N})
              with galoisCharacterOnIdeal K L χ 𝔞.1 = v, v :=
          (Finset.sum_fiberwise_of_maps_to'
            (fun 𝔞 _ ↦ (show ∀ [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] (χ : galoisCharacter K L) (𝔞 : Ideal (𝓞 K)), (galoisCharacterOnIdeal K L χ 𝔞 ∈ insert (0 : ℂ) (Polynomial.nthRootsFinset (orderOf χ) 1)) from by
              intro analyticInstance0 analyticInstance1 m analyticInstance2 analyticInstance3 χ 𝔞
              classical
              classical
              by_cases hU : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭
              · refine Finset.mem_insert_of_mem
                  (Polynomial.mem_nthRootsFinset (orderOf_pos_iff.mpr (isOfFinOrder_of_finite χ)) 1 |>.mpr ?_)
                rw [(show ∀      
                    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
                    [IsCyclotomicExtension {m} K L] (χ : galoisCharacter K L) {𝔞 : Ideal (𝓞 K)}
                    (hU : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭), (galoisCharacterOnIdeal K L χ 𝔞 = (χ (frobeniusIdeal K L 𝔞) : ℂ)) from by
                  intro cnrInstance0 cnrInstance1 m cnrInstance2 cnrInstance3 χ 𝔞 hU
                  classical
                  letI : CommGroup Gal(L/K) := { mul_comm := mul_comm' }
                  have hfrob : (χ (frobeniusIdeal K L 𝔞) : ℂ) =
                      ((UniqueFactorizationMonoid.normalizedFactors 𝔞).map
                        (fun 𝔭 ↦ (χ (frobeniusClass K L 𝔭).out : ℂ))).prod := by
                    rw [frobeniusIdeal, map_multiset_prod, ← Units.coeHom_apply, map_multiset_prod,
                      Multiset.map_map, Multiset.map_map]
                    rfl
                  rw [galoisCharacterOnIdeal, ← Finset.prod_multiset_map_count, hfrob]
                  refine congrArg Multiset.prod (Multiset.map_congr rfl fun 𝔭 h𝔭 ↦ ?_)
                  rw [if_pos (hU 𝔭 h𝔭)]) m χ hU,
                  ← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, pow_orderOf_eq_one,
                  MonoidHom.one_apply, Units.val_one]
              · push Not at hU
                obtain ⟨𝔭, h𝔭, hram⟩ := hU
                rw [galoisCharacterOnIdeal, ← Finset.prod_multiset_map_count,
                  Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨𝔭, h𝔭, if_neg hram⟩)]
                exact Finset.mem_insert_self _ _) m χ 𝔞.1)
            fun z : ℂ ↦ z).symm
      _ = ∑ v ∈ insert (0 : ℂ) (Polynomial.nthRootsFinset (orderOf χ) 1),
            (Nat.card {𝔞 : Ideal (𝓞 K) //
              𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ galoisCharacterOnIdeal K L χ 𝔞 = v} : ℂ) * v := by
          refine Finset.sum_congr rfl fun v _ ↦ ?_
          rw [Finset.sum_const, nsmul_eq_mul]
          refine congrArg (· * v) (congrArg (Nat.cast : ℕ → ℂ) ?_)
          rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
          exact Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter
            (fun 𝔞 : Ideal (𝓞 K) ↦ 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N)
            (fun 𝔞 ↦ galoisCharacterOnIdeal K L χ 𝔞 = v)).trans
            (Equiv.subtypeEquivRight fun 𝔞 ↦ and_assoc))
      _ = ∑ v ∈ Polynomial.nthRootsFinset (orderOf χ) 1, (Nat.card {𝔞 : Ideal (𝓞 K) //
            𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ galoisCharacterOnIdeal K L χ 𝔞 = v} : ℂ) * v := by
          rw [Finset.sum_insert h0R, mul_zero, zero_add]
      _ = ∑ v ∈ Polynomial.nthRootsFinset (orderOf χ) 1, ((((Nat.card {𝔞 : Ideal (𝓞 K) //
            𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ galoisCharacterOnIdeal K L χ 𝔞 = v} : ℝ)
              - C₀ * N : ℝ) : ℂ) * v + ((C₀ * N : ℝ) : ℂ) * v) := by
          refine Finset.sum_congr rfl fun v _ ↦ ?_
          push_cast
          ring
      _ = ∑ v ∈ Polynomial.nthRootsFinset (orderOf χ) 1, (((Nat.card {𝔞 : Ideal (𝓞 K) //
            𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ galoisCharacterOnIdeal K L χ 𝔞 = v} : ℝ)
              - C₀ * N : ℝ) : ℂ) * v := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum,
            (show ∑ v ∈ Polynomial.nthRootsFinset (orderOf χ) (1 : ℂ), v = 0 from by
              rw [Polynomial.nthRootsFinset,
                hζ₀.nthRoots_eq (show (1 : ℂ) ^ orderOf χ = 1 by simp),
                Multiset.toFinset_map, Multiset.toFinset_range]
              simp only [mul_one]
              rw [Finset.sum_image (fun i hi j hj hij ↦ hζ₀.injOn_pow hi hj hij)]
              exact hζ₀.geom_sum_eq_zero hord2), mul_zero, add_zero]
  rw [tsum_fintype, hsum]
  calc ‖∑ v ∈ R, (((Nat.card {𝔞 : Ideal (𝓞 K) //
        𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ galoisCharacterOnIdeal K L χ 𝔞 = v} : ℝ)
          - C₀ * N : ℝ) : ℂ) * v‖
      ≤ ∑ v ∈ R, ‖(((Nat.card {𝔞 : Ideal (𝓞 K) //
          𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ galoisCharacterOnIdeal K L χ 𝔞 = v} : ℝ)
            - C₀ * N : ℝ) : ℂ) * v‖ := norm_sum_le _ _
    _ ≤ ∑ _v ∈ R, C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
        refine Finset.sum_le_sum fun v hv ↦ ?_
        rw [norm_mul, Complex.norm_eq_one_of_pow_eq_one (hmemR.mp hv) hord0, mul_one,
          Complex.norm_real, Real.norm_eq_abs]
        exact hcount v (hmemR.mp hv) N hN1
    _ = (orderOf χ : ℝ) * C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
        rw [Finset.sum_const, hR, hζ₀.card_nthRootsFinset, nsmul_eq_mul]
        ring

/-- The `n`-th Dirichlet coefficient of the Artin L-series `L(χ,·)`, i.e. the sum of the ideal
character `χ̃(𝔞)` over the (finitely many) nonzero ideals `𝔞` of `𝓞 K` with `N𝔞 = n`. This is the
arithmetic function whose L-series is `∑_𝔞 χ̃(𝔞) N𝔞^{-s}`. -/
private noncomputable def galoisCharacterCoeff
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) (n : ℕ) : ℂ :=
  ∑' 𝔞 : {𝔞 : NonzeroIdeal K // Ideal.absNorm 𝔞.1 = n}, galoisCharacterOnIdeal K L χ 𝔞.1.1

/-- **Step 1 (the LF3 input).** The partial sums of the L-series coefficients grow like
`O(n^{1-1/d})`, `d = [K:ℚ]`. This is the geometry-of-numbers character-sum bound
`character_sum_geometry_of_numbers_bound` rewritten through the partial-sum bridge. -/
private theorem sum_galoisCharacterCoeff_isBigO
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2) (χ : galoisCharacter K L) (_hχ : χ ≠ 1) :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, galoisCharacterCoeff K L χ k)
      =O[Filter.atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹)) := by
  obtain ⟨C, hC⟩ := character_sum_geometry_of_numbers_bound K L m hm χ _hχ
  refine Asymptotics.isBigO_iff.mpr ⟨C, Filter.Eventually.of_forall fun n ↦ ?_⟩
  rw [(show ∀ (χ : galoisCharacter K L) (n : ℕ), (∑ k ∈ Finset.Icc 1 n, galoisCharacterCoeff K L χ k = ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ n}, galoisCharacterOnIdeal K L χ 𝔞.1) from by
    intro χ n
    classical
    classical
    haveI := (show ∀ (N : ℕ), (Finite {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N}) from by
      intro N
      classical
      exact
        haveI : Finite {𝔞 : Ideal (𝓞 K) // Ideal.absNorm 𝔞 ≤ N} :=
          (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) N).to_subtype
        Finite.of_injective (fun a ↦ (⟨a.1, a.2.2⟩ : {𝔞 : Ideal (𝓞 K) // Ideal.absNorm 𝔞 ≤ N}))
          fun _ _ hab ↦ Subtype.ext (by simpa using hab)) n
    haveI := Fintype.ofFinite {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ n}
    rw [tsum_fintype, ← Finset.sum_fiberwise_of_maps_to (t := Finset.Icc 1 n)
        (g := fun 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ n} ↦ Ideal.absNorm 𝔞.1)
        (fun 𝔞 _ ↦ Finset.mem_Icc.mpr
          ⟨Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp 𝔞.2.1), 𝔞.2.2⟩)
        (fun 𝔞 ↦ galoisCharacterOnIdeal K L χ 𝔞.1)]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [galoisCharacterCoeff, ← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
    haveI := (show ∀ (n : ℕ), (Finite {𝔞 : NonzeroIdeal K // Ideal.absNorm 𝔞.1 = n}) from by
      intro n
      classical
      exact
        Set.Finite.to_subtype <| Set.Finite.of_finite_image (f := fun I : NonzeroIdeal K ↦ I.1)
          ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).subset (by rintro _ ⟨⟨I, _⟩, rfl, rfl⟩; rfl))
          (fun _ _ _ _ ↦ Subtype.ext)) k
    haveI := Fintype.ofFinite {𝔞 : NonzeroIdeal K // Ideal.absNorm 𝔞.1 = k}
    rw [tsum_fintype]
    exact Fintype.sum_equiv
      { toFun := fun ⟨⟨𝔞, h𝔞ne⟩, hnorm⟩ ↦
          (⟨⟨𝔞, h𝔞ne, hnorm.le.trans (Finset.mem_Icc.mp hk).2⟩, hnorm⟩ :
            {x : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ n} // Ideal.absNorm x.1 = k})
        invFun := fun ⟨⟨𝔞, h𝔞⟩, hnorm⟩ ↦ ⟨⟨𝔞, h𝔞.1⟩, hnorm⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl } _ _ fun _ ↦ rfl) χ n,
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  exact hC n

open Filter Topology Set MeasureTheory Asymptotics in
/-- Sharifi 7.1.19 step 1b (p. 142) — analytic extension of `L(χ,·)`.
Combining the geometry-of-numbers bound
`character_sum_geometry_of_numbers_bound`
with Sharifi Lemma 7.1.5 (p. 138, a generic Dirichlet-series
convergence criterion given a polynomial bound on partial sums), the
Dirichlet series `L(χ,s) = Σ_𝔞 χ(𝔞) N𝔞^{-s}` converges absolutely and
uniformly on every compact subset of `Z(1 - 1/[K:ℚ])`, defining an
analytic extension of `L(χ,·)` from `Re s > 1` to that half-plane.

Source quote (verbatim, p. 142):
> "By Lemma 7.1.5, we therefore have that `Σ_𝔞⊂𝓞_K χ(𝔞) N𝔞^{-s}`
> converges absolutely and uniformly on every compact subset of
> `Z(1 - d^{-1})`."

Mathlib analogue of Sharifi Lemma 7.1.5:
`LSeries.summable_of_partial_sums_le_const_mul_rpow` (or the
`LSeries.tendsto_neg_logDerivLSeries_eq_*` machinery in
`Mathlib.NumberTheory.LSeries.*`).

**Stated at cyclotomic generality** (`L = K(μ_m)`), like the geometry-of-numbers input it rests
on (`character_sum_geometry_of_numbers_bound`, leaf G — see the restatement note there, expert
review 2026-06-05): the general-abelian partial-sum bound needs class field theory, while for
`L = K(μ_m)` it is CFT-free. Every consumer (the non-vanishing chain, the cyclotomic Chebotarev
case) instantiates at a cyclotomic extension. -/
theorem artinLSeries_analytic_extension
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2) (χ : galoisCharacter K L) (_hχ : χ ≠ 1) :
    ∃ Lf : ℂ → ℂ,
      AnalyticOn ℂ Lf {s : ℂ | 1 - (Module.finrank ℚ K : ℝ)⁻¹ < s.re} ∧
      (∀ s : ℂ, 1 < s.re →
        Lf s =
          ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥},
            galoisCharacterOnIdeal K L χ 𝔞.1 *
              (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s)) := by
  classical
  set r : ℝ := 1 - (Module.finrank ℚ K : ℝ)⁻¹ with hr_def
  have hrinv : (0 : ℝ) < (Module.finrank ℚ K : ℝ)⁻¹ := by
    rw [inv_pos]; exact_mod_cast Module.finrank_pos
  have hr0 : 0 ≤ r := by
    rw [hr_def, sub_nonneg, inv_le_one_iff₀]; right; exact_mod_cast Module.finrank_pos
  have hr1 : r < 1 := by rw [hr_def]; linarith
  set S : ℝ → ℂ := fun t ↦ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, galoisCharacterCoeff K L χ k with hS_def
  have hS_zero : ∀ t : ℝ, t < 1 → S t = 0 := fun t ht ↦ by
    change ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, galoisCharacterCoeff K L χ k = 0
    rw [Nat.floor_eq_zero.mpr ht, Finset.Icc_eq_empty (by norm_num), Finset.sum_empty]
  have hS_bigO : S =O[Filter.atTop] (fun t : ℝ ↦ t ^ r) :=
    ((sum_galoisCharacterCoeff_isBigO K L m hm χ _hχ).comp_tendsto
      tendsto_nat_floor_atTop).trans <|
      isEquivalent_nat_floor.isBigO.rpow hr0 (Filter.eventually_ge_atTop 0)
  refine ⟨fun s ↦ s * mellin S (-s), ?_, fun s hs ↦ ?_⟩
  · refine DifferentiableOn.analyticOn (fun s₀ hs₀ ↦ ?_)
      (isOpen_lt continuous_const Complex.continuous_re)
    have hs₀' : r < s₀.re := hs₀
    have hfc : LocallyIntegrableOn S (Ioi (0 : ℝ)) := by
      simpa only [one_mul] using (locallyIntegrableOn_mul_sum_Icc (a := 0) (m := 1)
        (galoisCharacterCoeff K L χ) le_rfl (locallyIntegrableOn_const 1)).mono_set
          Set.Ioi_subset_Ici_self
    have hf_top : S =O[Filter.atTop] (fun t : ℝ ↦ t ^ (-(-r))) := by rw [neg_neg]; exact hS_bigO
    have hf_bot : S =O[𝓝[>] (0 : ℝ)] (fun t : ℝ ↦ t ^ (-(-s₀.re - 1))) :=
      Filter.EventuallyEq.trans_isBigO
        (by filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht using
          hS_zero t (Set.mem_Ioo.mp ht).2) (Asymptotics.isBigO_zero _ _)
    have hmellin : DifferentiableAt ℂ (mellin S) (-s₀) :=
      mellin_differentiableAt_of_isBigO_rpow hfc hf_top (by rw [Complex.neg_re]; linarith)
        hf_bot (by rw [Complex.neg_re]; linarith)
    exact (differentiableAt_id.mul (hmellin.comp s₀ differentiableAt_id.neg)).differentiableWithinAt
  · have hssum : LSeriesSummable (galoisCharacterCoeff K L χ) s :=
      LSeriesSummable_of_sum_norm_bigO ((show ∀ (χ : galoisCharacter K L), ((fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, ‖galoisCharacterCoeff K L χ k‖) =O[Filter.atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ))) from by
        intro χ
        classical
        refine (Asymptotics.isBigO_of_le Filter.atTop fun n ↦ ?_).trans
          ((show (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (idealNormMultiplicity K k : ℝ)) =O[Filter.atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ)) from by
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
            rfl))
        rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _),
          Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)]
        exact Finset.sum_le_sum fun k _ ↦ (show ∀ (χ : galoisCharacter K L) (n : ℕ), (‖galoisCharacterCoeff K L χ n‖ ≤ (idealNormMultiplicity K n : ℝ)) from by
          intro χ n
          classical
          haveI := (show ∀ (n : ℕ), (Finite {𝔞 : NonzeroIdeal K // Ideal.absNorm 𝔞.1 = n}) from by
            intro n
            classical
            exact
              Set.Finite.to_subtype <| Set.Finite.of_finite_image (f := fun I : NonzeroIdeal K ↦ I.1)
                ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).subset (by rintro _ ⟨⟨I, _⟩, rfl, rfl⟩; rfl))
                (fun _ _ _ _ ↦ Subtype.ext)) n
          haveI := Fintype.ofFinite {𝔞 : NonzeroIdeal K // Ideal.absNorm 𝔞.1 = n}
          calc ‖galoisCharacterCoeff K L χ n‖
              ≤ ∑' 𝔞 : {𝔞 : NonzeroIdeal K // Ideal.absNorm 𝔞.1 = n},
                  ‖galoisCharacterOnIdeal K L χ 𝔞.1.1‖ :=
                norm_tsum_le_tsum_norm Summable.of_finite
            _ = ∑ 𝔞 : {𝔞 : NonzeroIdeal K // Ideal.absNorm 𝔞.1 = n},
                  ‖galoisCharacterOnIdeal K L χ 𝔞.1.1‖ := tsum_fintype _
            _ ≤ ∑ _𝔞 : {𝔞 : NonzeroIdeal K // Ideal.absNorm 𝔞.1 = n}, (1 : ℝ) :=
                Finset.sum_le_sum fun 𝔞 _ ↦ (show ∀      
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
                    exact zero_pow_le_one _) χ 𝔞.1.1
            _ = (idealNormMultiplicity K n : ℝ) := by
                rw [Finset.sum_const, nsmul_eq_mul, mul_one, idealNormMultiplicity,
                  Nat.card_eq_fintype_card]
                simp [Finset.card_univ]) χ k) χ) zero_le_one
        (by exact_mod_cast hs)
    rw [← (show ∀ (χ : galoisCharacter K L) (s : ℂ) (hs : 1 < s.re), (LSeries (galoisCharacterCoeff K L χ) s = ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥}, galoisCharacterOnIdeal K L χ 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s)) from by
      intro χ s hs
      classical
      classical
      set e := Equiv.sigmaFiberEquiv (fun I : NonzeroIdeal K ↦ Ideal.absNorm I.1) with he
      have hsummable : Summable fun I : NonzeroIdeal K ↦
          ‖galoisCharacterOnIdeal K L χ I.1 * (Ideal.absNorm I.1 : ℂ) ^ (-s)‖ := by
        refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun I ↦ ?_)
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
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) ((show ∀      
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
            exact zero_pow_le_one _) χ I.1)
      have hsummable_sigma : Summable fun p : Σ n, {I : NonzeroIdeal K // Ideal.absNorm I.1 = n} ↦
          galoisCharacterOnIdeal K L χ (e p).1 * (Ideal.absNorm (e p).1 : ℂ) ^ (-s) :=
        (e.summable_iff (f := fun I : NonzeroIdeal K ↦
          galoisCharacterOnIdeal K L χ I.1 * (Ideal.absNorm I.1 : ℂ) ^ (-s))).mpr hsummable.of_norm
      have hfiber_val : ∀ n : ℕ,
          (∑' y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n},
            galoisCharacterOnIdeal K L χ (y.1).1 * (Ideal.absNorm (y.1).1 : ℂ) ^ (-s))
            = galoisCharacterCoeff K L χ n * (n : ℂ) ^ (-s) := fun n ↦ by
        have hconst : ∀ y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n},
            galoisCharacterOnIdeal K L χ (y.1).1 * (Ideal.absNorm (y.1).1 : ℂ) ^ (-s) =
              galoisCharacterOnIdeal K L χ (y.1).1 * (n : ℂ) ^ (-s) := fun y ↦ by rw [y.2]
        rw [tsum_congr hconst, tsum_mul_right, galoisCharacterCoeff]
      rw [show LSeries (galoisCharacterCoeff K L χ) s =
          ∑' n, galoisCharacterCoeff K L χ n * (n : ℂ) ^ (-s) from
        tsum_congr fun n ↦ LSeries.term_def₀ ((show ∀      
            (χ : galoisCharacter K L), galoisCharacterCoeff K L χ 0 = 0 from by
          intro χ
          have : IsEmpty {𝔞 : NonzeroIdeal K // Ideal.absNorm 𝔞.1 = 0} :=
            ⟨fun 𝔞 ↦ 𝔞.1.2 (Ideal.absNorm_eq_zero_iff.mp 𝔞.2)⟩
          rw [galoisCharacterCoeff, tsum_empty]) χ) s n,
        ← e.tsum_eq (fun I : NonzeroIdeal K ↦
          galoisCharacterOnIdeal K L χ I.1 * (Ideal.absNorm I.1 : ℂ) ^ (-s)),
        hsummable_sigma.tsum_sigma]
      exact (tsum_congr hfiber_val).symm) χ s hs,
      LSeries_eq_mul_integral (galoisCharacterCoeff K L χ) hr0
        (lt_of_lt_of_le hr1 (by exact_mod_cast hs.le)) hssum
        (sum_galoisCharacterCoeff_isBigO K L m hm χ _hχ),
      (show ∀ (S : ℝ → ℂ) (hS : ∀ t < 1, S t = 0) (s : ℂ), (∫ t in Ioi (1 : ℝ), S t * (t : ℂ) ^ (-(s + 1)) = mellin S (-s)) from by
        intro S hS s
        classical
        rw [mellin, show (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (-s - 1) • S t) =
            ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (-s - 1) • S t from ?_]
        · refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
          rw [smul_eq_mul]
          ring_nf
        · have hinter : Ioi (0 : ℝ) ∩ Ioi (1 : ℝ) = Ioi (1 : ℝ) :=
            inter_eq_right.mpr (Ioi_subset_Ioi (by norm_num))
          rw [← hinter, ← setIntegral_indicator measurableSet_Ioi]
          refine setIntegral_congr_ae measurableSet_Ioi ?_
          filter_upwards [show ∀ᵐ t : ℝ ∂volume, t ≠ 1 from
            ae_iff.mpr (by simp : volume {x : ℝ | ¬x ≠ 1} = 0)] with t ht _
          rw [indicator_apply]
          by_cases h1 : t ∈ Ioi (1 : ℝ)
          · rw [if_pos h1]
          · rw [if_neg h1, hS t (lt_of_le_of_ne (not_lt.mp (by simpa using h1)) ht), smul_zero]) S hS_zero s]

end Chebotarev
