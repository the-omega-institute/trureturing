/- GID: D5/S3/Factorization/Galois/GoldenCubicBlockKummerTower
   generality: I
   mirror-B: D5/B/S3/Factorization/Galois/GoldenCubicBlockKummerTower
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Actual Lucas cubic blocks give degree three per Kummer layer. -/

import D5.S3.Factorization.GoldenCubicBlockNoncube
import D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower

open D5.S1.Scale
open D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods

abbrev Base := CyclotomicField 3 ℚ
abbrev Ambient := AlgebraicClosure Base

def block (j : ℕ) : ℕ := (goldenLucas (3 ^ j) ^ 2 + 3).natAbs

noncomputable def tower (roots : ℕ → Ambient) : ℕ → IntermediateField Base Ambient
  | 0 => ⊥
  | m + 1 => tower roots m ⊔ IntermediateField.adjoin Base {roots (m + 1)}

private theorem base_not_cube (a : ℕ) (ha : ¬ ∃ z : ℤ, z ^ 3 = (a : ℤ)) :
    ¬ ∃ x : Base, x ^ 3 = (a : Base) := by
  have hq : ∀ y : ℚ, y ^ 3 ≠ (a : ℚ) := by
    intro y hy
    obtain ⟨z, hz⟩ :=
      IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := ℤ) (K := ℚ)
        (show 0 < 3 by decide) (by rw [hy]; exact isIntegral_intCast (a : ℤ))
    apply ha
    refine ⟨z, ?_⟩
    have hzpow : (z : ℚ) ^ 3 = (a : ℚ) := by
      calc
        (z : ℚ) ^ 3 = y ^ 3 := by simpa using congrArg (fun t : ℚ => t ^ (3 : ℕ)) hz
        _ = (a : ℚ) := hy
    exact_mod_cast hzpow
  have hirr : Irreducible (Polynomial.X ^ 3 - Polynomial.C (a : ℚ)) :=
    (X_pow_sub_C_irreducible_iff_of_prime (by decide : Nat.Prime 3)).2 hq
  rintro ⟨x, hx⟩
  have haeval : Polynomial.aeval x (Polynomial.X ^ 3 - Polynomial.C (a : ℚ)) = 0 := by
    simp [hx]
  have hmin : Polynomial.X ^ 3 - Polynomial.C (a : ℚ) = minpoly ℚ x := by
    exact minpoly.eq_of_irreducible_of_monic hirr haeval
      (Polynomial.monic_X_pow_sub_C (a : ℚ) (by decide : 3 ≠ 0))
  have hdeg : (minpoly ℚ x).natDegree = 3 := by
    rw [← hmin, Polynomial.natDegree_X_pow_sub_C]
  have hbound : (minpoly ℚ x).natDegree ≤ Module.finrank ℚ Base :=
    minpoly.natDegree_le x
  have hbase : Module.finrank ℚ Base = 2 := by
    letI : NeZero (3 : ℚ) := ⟨by norm_num⟩
    letI : IsCyclotomicExtension {3} ℚ Base :=
      CyclotomicField.isCyclotomicExtension 3 ℚ
    rw [IsCyclotomicExtension.finrank (n := 3) Base
      (Polynomial.cyclotomic.irreducible_rat (by decide : 0 < 3))]
    decide
  omega

private theorem cubic_descent {K L : Type*} [Field K] [Field L] [Algebra K L]
    {ζ a b : K} (hζ : IsPrimitiveRoot ζ 3) (ha : a ≠ 0) (hb : b ≠ 0)
    (σ : L ≃ₐ[K] L) (β z : L)
    (hβ : β ^ 3 = algebraMap K L b)
    (hσβ : σ β = algebraMap K L ζ * β)
    (hz : z ^ 3 = algebraMap K L a)
    (hfix : ∀ y : L, σ y = y → ∃ c : K, algebraMap K L c = y) :
    ∃ e : ℕ, e ≤ 3 ∧ ∃ c : K, a * b ^ e = c ^ 3 := by
  have haL : algebraMap K L a ≠ 0 := by
    simpa using (algebraMap K L).injective.ne ha
  have hbL : algebraMap K L b ≠ 0 := by
    simpa using (algebraMap K L).injective.ne hb
  have hz0 : z ≠ 0 := by
    intro h
    exact haL (hz.symm.trans (by simp [h]))
  have hβ0 : β ≠ 0 := by
    intro h
    exact hbL (hβ.symm.trans (by simp [h]))
  have hratio : (σ z / z) ^ 3 = 1 := by
    calc
      (σ z / z) ^ 3 = σ (z ^ 3) / z ^ 3 := by rw [div_pow, map_pow]
      _ = algebraMap K L a / algebraMap K L a := by rw [hz, σ.commutes]
      _ = 1 := div_self haL
  have hζL : IsPrimitiveRoot (algebraMap K L ζ) 3 :=
    hζ.map_of_injective (algebraMap K L).injective
  obtain ⟨k, hk, hpow⟩ := hζL.eq_pow_of_pow_eq_one hratio
  have hσz : σ z = (algebraMap K L ζ) ^ k * z := by
    calc
      σ z = (σ z / z) * z := (div_mul_cancel₀ _ hz0).symm
      _ = (algebraMap K L ζ) ^ k * z := by rw [← hpow]
  have hσq : σ (z / β ^ k) = z / β ^ k := by
    rw [map_div₀, map_pow, hσz, hσβ, mul_pow]
    field_simp [hβ0, hζL.ne_zero]
  obtain ⟨c, hc⟩ := hfix _ hσq
  have hzrep : z = algebraMap K L c * β ^ k := by
    calc
      z = (z / β ^ k) * β ^ k := (div_mul_cancel₀ _ (pow_ne_zero _ hβ0)).symm
      _ = algebraMap K L c * β ^ k := by rw [← hc]
  have hclass : a = c ^ 3 * b ^ k := (algebraMap K L).injective (by
    calc
      algebraMap K L a = z ^ 3 := hz.symm
      _ = (algebraMap K L c * β ^ k) ^ 3 := by rw [hzrep]
      _ = algebraMap K L (c ^ 3 * b ^ k) := by
        rw [mul_pow, ← pow_mul, mul_comm k 3, pow_mul, hβ, map_mul, map_pow, map_pow])
  refine ⟨3 - k, Nat.sub_le _ _, c * b, ?_⟩
  rw [hclass, mul_assoc, ← pow_add, Nat.add_sub_of_le hk.le, mul_pow]

private theorem fixed_of_degree_three {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = 3) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (y : L) (hy : σ y = y) :
    ∃ c : K, algebraMap K L c = y := by
  have hcard : Nat.card (L ≃ₐ[K] L) = 3 := by
    rw [IsGalois.card_aut_eq_finrank, hdeg]
  let Hfix : Subgroup (L ≃ₐ[K] L) := {
    carrier := {τ | τ y = y}
    one_mem' := by simp
    mul_mem' := by
      intro τ υ hτ hυ
      change (τ * υ) y = y
      rw [AlgEquiv.mul_apply, hυ, hτ]
    inv_mem' := by
      intro τ hτ
      change τ.symm y = y
      apply τ.injective
      simpa using hτ.symm
  }
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hzp : Subgroup.zpowers σ = ⊤ :=
    zpowers_eq_top_of_prime_card hcard hσ
  have htop : Hfix = ⊤ := by
    apply top_unique
    rw [← hzp]
    exact Subgroup.zpowers_le.mpr hy
  apply (IsGalois.mem_range_algebraMap_iff_fixed y).2
  intro τ
  have hτ : τ ∈ Hfix := by rw [htop]; exact Subgroup.mem_top τ
  exact hτ

private theorem cubic_stage_descent {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {ζ a b : K}
    (hζ : IsPrimitiveRoot ζ 3) (ha : a ≠ 0) (hb : b ≠ 0)
    (hdeg : Module.finrank K L = 3) (β z : L)
    (hβ : β ^ 3 = algebraMap K L b)
    (hgen : IntermediateField.adjoin K {β} = ⊤)
    (hz : z ^ 3 = algebraMap K L a) :
    ∃ e : ℕ, e ≤ 3 ∧ ∃ c : K, a * b ^ e = c ^ 3 := by
  have hζdim : (primitiveRoots (Module.finrank K L) K).Nonempty := by
    rw [hdeg]
    exact ⟨ζ, (mem_primitiveRoots (by decide : 0 < 3)).mpr hζ⟩
  have hβdim : β ^ (Module.finrank K L) = algebraMap K L b := by
    simpa only [hdeg] using hβ
  have hsplit : Polynomial.IsSplittingField K L
      (Polynomial.X ^ 3 - Polynomial.C b) := by
    simpa only [hdeg] using
      (isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top hζdim hβdim hgen)
  letI : Polynomial.IsSplittingField K L
      (Polynomial.X ^ 3 - Polynomial.C b) := hsplit
  have hirr : Irreducible (Polynomial.X ^ 3 - Polynomial.C b) := by
    simpa only [hdeg] using
      (irreducible_X_pow_sub_C_of_root_adjoin_eq_top hβdim hgen)
  letI : NeZero (3 : ℕ) := ⟨by decide⟩
  letI : IsGalois K L :=
    isGalois_of_isSplittingField_X_pow_sub_C
      ⟨ζ, (mem_primitiveRoots (by decide : 0 < 3)).mpr hζ⟩ hirr L
  let σ : L ≃ₐ[K] L :=
    (autEquivZmod hirr L hζ).symm (Multiplicative.ofAdd ((1 : ℕ) : ZMod 3))
  have hσβ : σ β = algebraMap K L ζ * β := by
    simpa only [σ, pow_one, Algebra.smul_def] using
      (autEquivZmod_symm_apply_natCast hirr L hβ hζ 1)
  have hβ0 : β ≠ 0 := by
    intro h
    apply (algebraMap K L).injective.ne hb
    simpa [h] using hβ.symm
  have hσ : σ ≠ 1 := by
    intro h
    have heq : (algebraMap K L ζ) * β = 1 * β := by
      simpa [h] using hσβ.symm
    exact hζ.ne_one (by decide : 1 < 3)
      ((algebraMap K L).injective (by simpa using mul_right_cancel₀ hβ0 heq))
  exact cubic_descent hζ ha hb σ β z hβ hσβ hz
    (fun y hy => fixed_of_degree_three hdeg σ hσ y hy)

private theorem tower_noncube (roots : ℕ → Ambient)
    (hroots : ∀ j, 1 ≤ j → roots j ^ 3 = algebraMap Base Ambient (block j))
    (hblock : ∀ j, 1 ≤ j → ¬ ∃ t : ℕ, t ^ 3 = block j)
    (hcoprime : ∀ i j, 1 ≤ i → 1 ≤ j → i ≠ j → (block i).Coprime (block j))
    (stage_step : ∀ n,
      (∀ t : tower roots n, t ^ 3 ≠ (block (n + 1) : tower roots n)) →
      IntermediateField.relfinrank (tower roots n) (tower roots (n + 1)) = 3)
    (m : ℕ) :
    ∀ a : ℕ, (¬ ∃ t : ℕ, t ^ 3 = a) →
      (∀ i : ℕ, 1 ≤ i → i ≤ m → a.Coprime (block i)) →
      ∀ x : tower roots m, x ^ 3 ≠ (a : tower roots m) := by
  have nat_cube_of_int_cube (a : ℕ)
      (h : ∃ z : ℤ, z ^ 3 = (a : ℤ)) : ∃ t : ℕ, t ^ 3 = a := by
    obtain ⟨z, hz⟩ := h
    have hznonneg : 0 ≤ z :=
      (by decide : Odd 3).pow_nonneg_iff.mp (hz ▸ Int.natCast_nonneg a)
    refine ⟨z.toNat, ?_⟩
    have hcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hznonneg
    have hpow : ((z.toNat ^ 3 : ℕ) : ℤ) = (a : ℤ) := by
      simpa only [Nat.cast_pow, hcast] using hz
    exact_mod_cast hpow
  have noncube_mul_coprime_power (a b : ℕ)
      (ha : ¬ ∃ t : ℕ, t ^ 3 = a) (hab : a.Coprime b) (e : ℕ) :
      ¬ ∃ t : ℕ, t ^ 3 = a * b ^ e := by
    rintro ⟨t, ht⟩
    have hcp : IsCoprime (a : ℤ) ((b : ℤ) ^ e) :=
      (Nat.Coprime.isCoprime hab).pow_right
    have hpow : (a : ℤ) * (b : ℤ) ^ e = (t : ℤ) ^ 3 := by
      exact_mod_cast ht.symm
    obtain ⟨d, hd⟩ := Int.eq_pow_of_mul_eq_pow_odd_left hcp (by decide : Odd 3) hpow
    exact ha (nat_cube_of_int_cube a ⟨d, hd.symm⟩)
  induction m with
  | zero =>
      intro a ha _ x hx
      have haInt : ¬ ∃ z : ℤ, z ^ 3 = (a : ℤ) := by
        intro h
        exact ha (nat_cube_of_int_cube a h)
      apply base_not_cube a haInt
      have hxbot : (x : Ambient) ∈ (⊥ : IntermediateField Base Ambient) := by
        simpa only [tower] using x.property
      obtain ⟨y, hy⟩ := IntermediateField.mem_bot.mp hxbot
      refine ⟨y, (algebraMap Base Ambient).injective ?_⟩
      rw [map_pow, hy]
      exact congrArg Subtype.val hx
  | succ m ih =>
      intro a ha hcop x hx
      have hblock : ¬ ∃ t : ℕ, t ^ 3 = block (m + 1) :=
        hblock (m + 1) (by omega)
      have hnotcube : ∀ t : tower roots m,
          t ^ 3 ≠ (block (m + 1) : tower roots m) :=
        ih (block (m + 1)) hblock (by
          intro i hi him
          exact hcoprime (m + 1) i (by omega) hi (by omega))
      have hle : tower roots m ≤ tower roots (m + 1) := by
        dsimp [tower]
        exact le_sup_left
      letI : Algebra (tower roots m) (tower roots (m + 1)) :=
        (IntermediateField.inclusion hle).toAlgebra
      have hdeg : Module.finrank (tower roots m) (tower roots (m + 1)) = 3 := by
        have h := stage_step m hnotcube
        rw [IntermediateField.relfinrank_eq_finrank_of_le hle] at h
        change Module.finrank (tower roots m) (tower roots (m + 1)) = 3 at h
        exact h
      letI : FiniteDimensional (tower roots m) (tower roots (m + 1)) :=
        Module.finite_of_finrank_pos (by rw [hdeg]; decide)
      have hβmem : roots (m + 1) ∈ tower roots (m + 1) := by
        change roots (m + 1) ∈
          tower roots m ⊔ IntermediateField.adjoin Base {roots (m + 1)}
        exact (le_sup_right : IntermediateField.adjoin Base {roots (m + 1)} ≤
          tower roots m ⊔ IntermediateField.adjoin Base {roots (m + 1)})
          (IntermediateField.mem_adjoin_simple_self Base (roots (m + 1)))
      let β : tower roots (m + 1) := ⟨roots (m + 1), hβmem⟩
      have hβ : β ^ 3 =
          algebraMap (tower roots m) (tower roots (m + 1))
            (block (m + 1) : tower roots m) := by
        apply Subtype.ext
        simpa [β] using hroots (m + 1) (by omega)
      have hgen : IntermediateField.adjoin (tower roots m) {β} =
          (⊤ : IntermediateField (tower roots m) (tower roots (m + 1))) := by
        have hirr : Irreducible
            (Polynomial.X ^ 3 - Polynomial.C (block (m + 1) : tower roots m)) :=
          (X_pow_sub_C_irreducible_iff_of_prime (by decide : Nat.Prime 3)).2 hnotcube
        have hpoly : Polynomial.aeval β
            (Polynomial.X ^ 3 - Polynomial.C (block (m + 1) : tower roots m)) = 0 := by
          simp [hβ]
        have hint : IsIntegral (tower roots m) β :=
          ⟨Polynomial.X ^ 3 - Polynomial.C (block (m + 1) : tower roots m),
            Polynomial.monic_X_pow_sub_C _ (by decide : 3 ≠ 0), hpoly⟩
        have hmin : Polynomial.X ^ 3 - Polynomial.C (block (m + 1) : tower roots m) =
            minpoly (tower roots m) β :=
          minpoly.eq_of_irreducible_of_monic hirr hpoly
            (Polynomial.monic_X_pow_sub_C _ (by decide : 3 ≠ 0))
        apply IntermediateField.eq_of_le_of_finrank_eq le_top
        rw [IntermediateField.finrank_top', IntermediateField.adjoin.finrank hint,
          ← hmin, Polynomial.natDegree_X_pow_sub_C]
        exact hdeg.symm
      letI : NeZero (3 : ℚ) := ⟨by norm_num⟩
      letI : IsCyclotomicExtension {3} ℚ Base :=
        CyclotomicField.isCyclotomicExtension 3 ℚ
      let ζ : tower roots m :=
        algebraMap Base (tower roots m) (IsCyclotomicExtension.zeta 3 ℚ Base)
      have hζ : IsPrimitiveRoot ζ 3 :=
        (IsCyclotomicExtension.zeta_spec 3 ℚ Base).map_of_injective
          (algebraMap Base (tower roots m)).injective
      have ha0 : a ≠ 0 := by
        intro h
        apply ha
        exact ⟨0, by simp [h]⟩
      have hb0 : block (m + 1) ≠ 0 := by
        intro h
        apply hblock
        exact ⟨0, by simp [h]⟩
      have hx' : x ^ 3 =
          algebraMap (tower roots m) (tower roots (m + 1)) (a : tower roots m) := by
        simpa using hx
      obtain ⟨e, _, c, hc⟩ :=
        cubic_stage_descent hζ (Nat.cast_ne_zero.mpr ha0)
          (Nat.cast_ne_zero.mpr hb0) hdeg β x hβ hgen hx'
      have ha' : ¬ ∃ t : ℕ, t ^ 3 = a * block (m + 1) ^ e :=
        noncube_mul_coprime_power a (block (m + 1)) ha
          (hcop (m + 1) (by omega) (by omega)) e
      have hcop' : ∀ i : ℕ, 1 ≤ i → i ≤ m →
          (a * block (m + 1) ^ e).Coprime (block i) := by
        intro i hi him
        rw [Nat.coprime_mul_iff_left]
        exact ⟨hcop i hi (by omega),
          (hcoprime (m + 1) i (by omega) hi (by omega)).pow_left e⟩
      apply ih (a * block (m + 1) ^ e) ha' hcop' c
      simpa only [Nat.cast_mul, Nat.cast_pow] using hc.symm

/-- Every choice of cubic roots of the actual Lucas blocks produces a tower
with one cubic degree increase per block. -/
theorem golden_cubic_block_kummer_tower_degree (roots : ℕ → Ambient)
    (hroots : ∀ j, 1 ≤ j → roots j ^ 3 = algebraMap Base Ambient (block j)) (J : ℕ) :
    Module.finrank Base (tower roots J) = 3 ^ J := by
  have hblock (j : ℕ) (hj : 1 ≤ j) : ¬ ∃ t : ℕ, t ^ 3 = block j := by
    rintro ⟨t, ht⟩
    apply D5.S3.Factorization.GoldenCubicBlockNoncube.golden_cubic_block_not_cube j hj
    refine ⟨(t : ℤ), ?_⟩
    have hb : (block j : ℤ) = goldenLucas (3 ^ j) ^ 2 + 3 := by
      have hnonneg : 0 ≤ goldenLucas (3 ^ j) ^ 2 + 3 := by positivity
      simp [block, abs_of_nonneg hnonneg]
    have htInt : (t : ℤ) ^ 3 = (block j : ℤ) := by exact_mod_cast ht
    exact htInt.trans hb
  have hcoprime (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hij : i ≠ j) :
      (block i).Coprime (block j) :=
    cubic_block_native_power_periods.2.1 i j hi hj hij
  have stage_step (n : ℕ)
      (hnotcube : ∀ t : tower roots n, t ^ 3 ≠ (block (n + 1) : tower roots n)) :
      IntermediateField.relfinrank (tower roots n) (tower roots (n + 1)) = 3 := by
    let K := tower roots n
    let j := n + 1
    have hirr : Irreducible (Polynomial.X ^ 3 - Polynomial.C (block j : K)) :=
      (X_pow_sub_C_irreducible_iff_of_prime (by decide : Nat.Prime 3)).2 hnotcube
    have hrad : (roots j) ^ 3 = algebraMap K Ambient (block j : K) := by
      simpa [K, j] using hroots j (by omega)
    have hpoly : Polynomial.aeval (roots j)
        (Polynomial.X ^ 3 - Polynomial.C (block j : K)) = 0 := by
      simp [hrad]
    have hint : IsIntegral K (roots j) :=
      ⟨Polynomial.X ^ 3 - Polynomial.C (block j : K),
        Polynomial.monic_X_pow_sub_C _ (by decide : 3 ≠ 0), hpoly⟩
    have hmin : Polynomial.X ^ 3 - Polynomial.C (block j : K) =
        minpoly K (roots j) := by
      exact minpoly.eq_of_irreducible_of_monic hirr hpoly
        (Polynomial.monic_X_pow_sub_C _ (by decide : 3 ≠ 0))
    have hstage : (IntermediateField.adjoin K {roots j}).restrictScalars Base =
        tower roots (n + 1) := by
      simpa [K, j, tower] using
        (IntermediateField.restrictScalars_adjoin_eq_sup Base (tower roots n) {roots (n + 1)})
    have hle : K ≤ tower roots (n + 1) := by
      dsimp [K, tower]
      exact le_sup_left
    have hext : IntermediateField.extendScalars hle =
        IntermediateField.adjoin K {roots j} := by
      apply IntermediateField.restrictScalars_injective Base
      rw [IntermediateField.extendScalars_restrictScalars]
      exact hstage.symm
    rw [IntermediateField.relfinrank_eq_finrank_of_le hle, hext,
      IntermediateField.adjoin.finrank hint, ← hmin, Polynomial.natDegree_X_pow_sub_C]
  induction J with
  | zero =>
      change Module.finrank Base (⊥ : IntermediateField Base Ambient) = 1
      exact (IntermediateField.finrank_bot :
        Module.finrank Base (⊥ : IntermediateField Base Ambient) = 1)
  | succ m ih =>
      have hnotcube : ∀ t : tower roots m,
          t ^ 3 ≠ (block (m + 1) : tower roots m) :=
        tower_noncube roots hroots hblock hcoprime stage_step m (block (m + 1))
          (hblock (m + 1) (by omega)) (by
            intro i hi him
            exact hcoprime (m + 1) i (by omega) hi (by omega))
      have hle : tower roots m ≤ tower roots (m + 1) := by
        dsimp [tower]
        exact le_sup_left
      calc
        Module.finrank Base (tower roots (m + 1)) =
            Module.finrank Base (tower roots m) *
              IntermediateField.relfinrank (tower roots m) (tower roots (m + 1)) :=
          (IntermediateField.finrank_bot_mul_relfinrank hle).symm
        _ = 3 ^ (m + 1) := by rw [ih, stage_step m hnotcube, pow_succ]

end D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower
