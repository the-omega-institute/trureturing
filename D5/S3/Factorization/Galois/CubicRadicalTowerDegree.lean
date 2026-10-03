/- GID: D5/S3/Factorization/Galois/CubicRadicalTowerDegree
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/CubicRadicalTowerDegree
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Saturated base-field noncube tests force every cubic radical stage to have degree three. -/

import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.Tactic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped WithZero

universe u v

namespace D5.S3.Factorization.Galois.CubicRadicalTowerDegree

noncomputable def radicalTower {K L : Type*} [Field K] [Field L] [Algebra K L]
    (roots : ℕ → L) : ℕ → IntermediateField K L
  := Nat.rec (⊥ : IntermediateField K L)
    (fun m F => F ⊔ IntermediateField.adjoin K {roots (m + 1)})

/-- Base-field tests that detect noncubes and are unchanged by earlier radical powers
certify every degree increase and preserve terminal noncube tests in the radical tower. -/
theorem cubic_radical_tower_degree_of_saturated_noncube_tests
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (ζ : K) (hζ : IsPrimitiveRoot ζ 3)
    (rad : ℕ → K) (roots : ℕ → L) (J : ℕ)
    (hroots : ∀ j, 1 ≤ j → j ≤ J → roots j ^ 3 = algebraMap K L (rad j))
    (P : ℕ → K → Prop)
    (hPcube : ∀ n, n ≤ J → ∀ a, P n a → ¬ ∃ c : K, c ^ 3 = a)
    (hPmul : ∀ n, n ≤ J → ∀ i, 1 ≤ i → i ≤ n → ∀ a e,
      P n a → P n (a * rad i ^ e))
    (hPfresh : ∀ n, n < J → P n (rad (n + 1))) :
    Module.finrank K (radicalTower (K := K) roots J) = 3 ^ J ∧
      ∀ a, P J a → ∀ x : radicalTower (K := K) roots J,
        x ^ 3 ≠ algebraMap K (radicalTower (K := K) roots J) a := by
  have cubic_stage_descent {K L : Type v} [Field K] [Field L] [Algebra K L]
      [FiniteDimensional K L] {ζ a b : K}
      (hζ : IsPrimitiveRoot ζ 3) (ha : a ≠ 0) (hb : b ≠ 0)
      (hdeg : Module.finrank K L = 3) (β z : L)
      (hβ : β ^ 3 = algebraMap K L b)
      (hgen : IntermediateField.adjoin K {β} = ⊤)
      (hz : z ^ 3 = algebraMap K L a) :
      ∃ e : ℕ, e ≤ 3 ∧ ∃ c : K, a * b ^ e = c ^ 3 := by
    have cubic_descent {K L : Type v} [Field K] [Field L] [Algebra K L]
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
      (fun y hy => by
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
        exact hτ)
  have hrad : ∀ j, 1 ≤ j → j ≤ J → rad j ≠ 0 := by
    intro j hj hjJ hzero
    have htest := hPfresh (j - 1) (by omega)
    have hindex : j - 1 + 1 = j := by omega
    rw [hindex] at htest
    exact hPcube (j - 1) (by omega) (rad j) htest ⟨0, by simp [hzero]⟩
  have stage_step (n : ℕ) (hn : n < J)
      (hnotcube : ∀ t : radicalTower (K := K) roots n,
        t ^ 3 ≠ algebraMap K (radicalTower (K := K) roots n) (rad (n + 1))) :
      IntermediateField.relfinrank (radicalTower (K := K) roots n)
        (radicalTower (K := K) roots (n + 1)) = 3 := by
    let F := radicalTower (K := K) roots n
    let j := n + 1
    have hirr : Irreducible (Polynomial.X ^ 3 -
        Polynomial.C (algebraMap K F (rad j))) :=
      (X_pow_sub_C_irreducible_iff_of_prime (by decide : Nat.Prime 3)).2 hnotcube
    have hradroot : roots j ^ 3 =
        algebraMap F L (algebraMap K F (rad j)) := by
      rw [← IsScalarTower.algebraMap_apply K F L]
      exact hroots j (by dsimp [j]; omega) (by dsimp [j]; omega)
    have hpoly : Polynomial.aeval (roots j)
        (Polynomial.X ^ 3 - Polynomial.C (algebraMap K F (rad j))) = 0 := by
      simp [hradroot]
    have hint : IsIntegral F (roots j) :=
      ⟨Polynomial.X ^ 3 - Polynomial.C (algebraMap K F (rad j)),
        Polynomial.monic_X_pow_sub_C _ (by decide : 3 ≠ 0), hpoly⟩
    have hmin : Polynomial.X ^ 3 - Polynomial.C (algebraMap K F (rad j)) =
        minpoly F (roots j) :=
      minpoly.eq_of_irreducible_of_monic hirr hpoly
        (Polynomial.monic_X_pow_sub_C _ (by decide : 3 ≠ 0))
    have hstage : (IntermediateField.adjoin F {roots j}).restrictScalars K =
        radicalTower (K := K) roots (n + 1) := by
      change (IntermediateField.adjoin (radicalTower (K := K) roots n)
        {roots (n + 1)}).restrictScalars K =
          radicalTower (K := K) roots n ⊔ IntermediateField.adjoin K {roots (n + 1)}
      exact IntermediateField.restrictScalars_adjoin_eq_sup K
        (radicalTower (K := K) roots n) {roots (n + 1)}
    have hle : F ≤ radicalTower (K := K) roots (n + 1) := by
      change radicalTower (K := K) roots n ≤ radicalTower (K := K) roots n ⊔
        IntermediateField.adjoin K {roots (n + 1)}
      exact le_sup_left
    have hext : IntermediateField.extendScalars hle =
        IntermediateField.adjoin F {roots j} := by
      apply IntermediateField.restrictScalars_injective K
      rw [IntermediateField.extendScalars_restrictScalars]
      exact hstage.symm
    rw [IntermediateField.relfinrank_eq_finrank_of_le hle, hext,
      IntermediateField.adjoin.finrank hint, ← hmin, Polynomial.natDegree_X_pow_sub_C]
  have noncube_in_tower (m : ℕ) : m ≤ J → ∀ n, m ≤ n → n ≤ J → ∀ a,
      P n a → ∀ x : radicalTower (K := K) roots m,
        x ^ 3 ≠ algebraMap K (radicalTower (K := K) roots m) a := by
    induction m with
    | zero =>
      intro _ n _ hn a ha x hx
      have hxbot : (x : L) ∈ (⊥ : IntermediateField K L) := x.property
      obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hxbot
      apply hPcube n hn a ha
      refine ⟨c, (algebraMap K L).injective ?_⟩
      rw [map_pow, hc]
      exact congrArg Subtype.val hx
    | succ m ih =>
      intro hmJ n hmn hnJ a ha x hx
      have hnotcube : ∀ t : radicalTower (K := K) roots m,
          t ^ 3 ≠ algebraMap K (radicalTower (K := K) roots m) (rad (m + 1)) :=
        ih (by omega) m le_rfl (by omega) (rad (m + 1)) (hPfresh m (by omega))
      have hle : radicalTower (K := K) roots m ≤ radicalTower (K := K) roots (m + 1) := by
        change radicalTower (K := K) roots m ≤ radicalTower (K := K) roots m ⊔
          IntermediateField.adjoin K {roots (m + 1)}
        exact le_sup_left
      letI : Algebra (radicalTower (K := K) roots m) (radicalTower (K := K) roots (m + 1)) :=
        (IntermediateField.inclusion hle).toAlgebra
      have hdeg : Module.finrank (radicalTower (K := K) roots m)
          (radicalTower (K := K) roots (m + 1)) = 3 := by
        have h := stage_step m (by omega) hnotcube
        rw [IntermediateField.relfinrank_eq_finrank_of_le hle] at h
        change Module.finrank (radicalTower (K := K) roots m)
          (radicalTower (K := K) roots (m + 1)) = 3 at h
        exact h
      letI : FiniteDimensional (radicalTower (K := K) roots m)
          (radicalTower (K := K) roots (m + 1)) :=
        Module.finite_of_finrank_pos (by rw [hdeg]; decide)
      have hβmem : roots (m + 1) ∈ radicalTower (K := K) roots (m + 1) := by
        change roots (m + 1) ∈ radicalTower (K := K) roots m ⊔
          IntermediateField.adjoin K {roots (m + 1)}
        exact (le_sup_right : IntermediateField.adjoin K {roots (m + 1)} ≤
          radicalTower (K := K) roots m ⊔ IntermediateField.adjoin K {roots (m + 1)})
          (IntermediateField.mem_adjoin_simple_self K (roots (m + 1)))
      let β : radicalTower (K := K) roots (m + 1) := ⟨roots (m + 1), hβmem⟩
      let b : radicalTower (K := K) roots m := algebraMap K (radicalTower (K := K) roots m) (rad (m + 1))
      have hβ : β ^ 3 =
          algebraMap (radicalTower (K := K) roots m) (radicalTower (K := K) roots (m + 1)) b := by
        apply Subtype.ext
        change roots (m + 1) ^ 3 =
          ((IntermediateField.inclusion hle)
            (algebraMap K (radicalTower (K := K) roots m) (rad (m + 1))) : L)
        rw [(IntermediateField.inclusion hle).commutes]
        exact hroots (m + 1) (by omega) (by omega)
      have hgen : IntermediateField.adjoin (radicalTower (K := K) roots m) {β} =
          (⊤ : IntermediateField (radicalTower (K := K) roots m) (radicalTower (K := K) roots (m + 1))) := by
        have hirr : Irreducible (Polynomial.X ^ 3 - Polynomial.C b) :=
          (X_pow_sub_C_irreducible_iff_of_prime (by decide : Nat.Prime 3)).2 hnotcube
        have hpoly : Polynomial.aeval β (Polynomial.X ^ 3 - Polynomial.C b) = 0 := by
          simp [hβ]
        have hint : IsIntegral (radicalTower (K := K) roots m) β :=
          ⟨Polynomial.X ^ 3 - Polynomial.C b,
            Polynomial.monic_X_pow_sub_C _ (by decide : 3 ≠ 0), hpoly⟩
        have hmin : Polynomial.X ^ 3 - Polynomial.C b =
            minpoly (radicalTower (K := K) roots m) β :=
          minpoly.eq_of_irreducible_of_monic hirr hpoly
            (Polynomial.monic_X_pow_sub_C _ (by decide : 3 ≠ 0))
        apply IntermediateField.eq_of_le_of_finrank_eq le_top
        rw [IntermediateField.finrank_top', IntermediateField.adjoin.finrank hint,
          ← hmin, Polynomial.natDegree_X_pow_sub_C]
        exact hdeg.symm
      let ζm : radicalTower (K := K) roots m := algebraMap K (radicalTower (K := K) roots m) ζ
      have hζm : IsPrimitiveRoot ζm 3 :=
        hζ.map_of_injective (algebraMap K (radicalTower (K := K) roots m)).injective
      have ha0 : a ≠ 0 := by
        intro ha0
        exact hPcube n hnJ a ha ⟨0, by simp [ha0]⟩
      have haF : algebraMap K (radicalTower (K := K) roots m) a ≠ 0 := by
        simpa only [map_zero] using
          (algebraMap K (radicalTower (K := K) roots m)).injective.ne ha0
      have hbF : b ≠ 0 := by
        simpa only [b, map_zero] using
          (algebraMap K (radicalTower (K := K) roots m)).injective.ne
            (hrad (m + 1) (by omega) (by omega))
      have hx' : x ^ 3 =
          algebraMap (radicalTower (K := K) roots m) (radicalTower (K := K) roots (m + 1))
            (algebraMap K (radicalTower (K := K) roots m) a) := by
        change x ^ 3 = (IntermediateField.inclusion hle)
          (algebraMap K (radicalTower (K := K) roots m) a)
        rw [(IntermediateField.inclusion hle).commutes]
        exact hx
      obtain ⟨e, _, c, hc⟩ :=
        cubic_stage_descent
          hζm haF hbF hdeg β x hβ hgen hx'
      apply ih (by omega) n (by omega) hnJ (a * rad (m + 1) ^ e)
        (hPmul n hnJ (m + 1) (by omega) (by omega) a e ha) c
      simpa only [b, map_mul, map_pow] using hc.symm
  have degree_all (m : ℕ) : m ≤ J → Module.finrank K (radicalTower (K := K) roots m) = 3 ^ m := by
    induction m with
    | zero =>
        intro _
        change Module.finrank K (⊥ : IntermediateField K L) = 1
        exact IntermediateField.finrank_bot
    | succ m ih =>
        intro hmJ
        have hnotcube : ∀ t : radicalTower (K := K) roots m,
            t ^ 3 ≠ algebraMap K (radicalTower (K := K) roots m) (rad (m + 1)) :=
          noncube_in_tower m (by omega) m le_rfl (by omega)
            (rad (m + 1)) (hPfresh m (by omega))
        have hle : radicalTower (K := K) roots m ≤ radicalTower (K := K) roots (m + 1) := by
          change radicalTower (K := K) roots m ≤ radicalTower (K := K) roots m ⊔
            IntermediateField.adjoin K {roots (m + 1)}
          exact le_sup_left
        calc
          Module.finrank K (radicalTower (K := K) roots (m + 1)) =
              Module.finrank K (radicalTower (K := K) roots m) *
                IntermediateField.relfinrank (radicalTower (K := K) roots m)
                  (radicalTower (K := K) roots (m + 1)) :=
            (IntermediateField.finrank_bot_mul_relfinrank hle).symm
          _ = 3 ^ (m + 1) := by
            rw [ih (by omega), stage_step m (by omega) hnotcube, pow_succ]
  refine ⟨degree_all J le_rfl, ?_⟩
  intro a ha x
  exact noncube_in_tower J le_rfl J le_rfl le_rfl a ha x

set_option maxHeartbeats 800000 in
/-- Diagonal valuations certify a full independent cubic radical degree and keep
a valuation-neutral noncube unit outside the radical span. -/
theorem finite_valuation_degree_and_unit_noncube
    {K L : Type} [Field K] [Field L] [Algebra K L]
    {ι : Type} [Fintype ι]
    (ζ : K) (hζ : IsPrimitiveRoot ζ 3)
    (rad : ι → K) (root : ι → L)
    (hroot : ∀ i, root i ^ 3 = algebraMap K L (rad i))
    (hrad : ∀ i, rad i ≠ 0)
    (ν : ι → Valuation K (WithZero (Multiplicative ℤ)))
    (hdiag : ∀ i, ¬ (3 : ℤ) ∣ WithZero.log (ν i (rad i)))
    (hoff : ∀ i j, i ≠ j → ν i (rad j) = 1)
    (u : K) (hu0 : u ≠ 0) (hunoncube : ¬ ∃ c : K, c ^ 3 = u)
    (huval : ∀ i, WithZero.log (ν i u) = 0) :
    Module.finrank K (IntermediateField.adjoin K (Set.range root)) =
        3 ^ Fintype.card ι ∧
      ∀ x : IntermediateField.adjoin K (Set.range root),
        x ^ 3 ≠ algebraMap K (IntermediateField.adjoin K (Set.range root)) u := by
  have tower_eq_common_adjoin {K L : Type} [Field K] [Field L] [Algebra K L]
      (roots : ℕ → L) (J : ℕ) :
      D5.S3.Factorization.Galois.CubicRadicalTowerDegree.radicalTower (K := K) roots J =
        IntermediateField.adjoin K (roots '' Set.Icc 1 J) := by
    induction J with
    | zero =>
      have hs : Set.Icc (1 : ℕ) 0 = ∅ := by
        ext i
        simp only [Set.mem_Icc, Set.mem_empty_iff_false, iff_false]
        omega
      rw [hs, Set.image_empty, IntermediateField.adjoin_empty]
      rfl
    | succ m ih =>
      have hs : Set.Icc (1 : ℕ) (m + 1) = Set.Icc 1 m ∪ {m + 1} := by
        ext i
        simp only [Set.mem_Icc, Set.mem_union, Set.mem_singleton_iff]
        omega
      rw [hs, Set.image_union, Set.image_singleton, IntermediateField.adjoin_union]
      change D5.S3.Factorization.Galois.CubicRadicalTowerDegree.radicalTower (K := K) roots m ⊔
        IntermediateField.adjoin K {roots (m + 1)} =
          IntermediateField.adjoin K (roots '' Set.Icc 1 m) ⊔
            IntermediateField.adjoin K {roots (m + 1)}
      rw [ih]

  have finite_support_representation {K L : Type} [Field K] [Field L] [Algebra K L]
      {ι : Type} [Fintype ι] (root : ι → L) :
      let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
      let roots : ℕ → L := fun n =>
        if hn : 1 ≤ n ∧ n ≤ Fintype.card ι
        then root (e ⟨n - 1, by omega⟩) else 0
      D5.S3.Factorization.Galois.CubicRadicalTowerDegree.radicalTower (K := K) roots (Fintype.card ι) =
        IntermediateField.adjoin K (Set.range root) := by
    classical
    let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
    let roots : ℕ → L := fun n =>
      if hn : 1 ≤ n ∧ n ≤ Fintype.card ι
      then root (e ⟨n - 1, by omega⟩) else 0
    change D5.S3.Factorization.Galois.CubicRadicalTowerDegree.radicalTower (K := K) roots (Fintype.card ι) =
      IntermediateField.adjoin K (Set.range root)
    rw [tower_eq_common_adjoin]
    congr 1
    ext y
    constructor
    · rintro ⟨n, hn, hy⟩
      have hn' : 1 ≤ n ∧ n ≤ Fintype.card ι := hn
      refine ⟨e ⟨n - 1, by omega⟩, ?_⟩
      change roots n = y at hy
      dsimp only [roots] at hy
      rw [dif_pos hn'] at hy
      exact hy
    · rintro ⟨i, rfl⟩
      let n := (e.symm i).val + 1
      have hn : 1 ≤ n ∧ n ≤ Fintype.card ι := by
        dsimp [n]
        have hi := (e.symm i).isLt
        constructor <;> omega
      refine ⟨n, hn, ?_⟩
      simp only [roots, dif_pos hn]
      have hindex : (⟨n - 1, by omega⟩ : Fin (Fintype.card ι)) = e.symm i := by
        apply Fin.ext
        simp only [n, Nat.add_sub_cancel]
      rw [hindex, e.apply_symm_apply]

  have valuation_unit_span_noncube
      {K : Type} [Field K] {ι : Type} [Fintype ι]
      (rad : ι → K) (ν : ι → Valuation K (WithZero (Multiplicative ℤ)))
      (u : K) (hu0 : u ≠ 0) (hunoncube : ¬ ∃ c : K, c ^ 3 = u)
      (hdiag : ∀ i, ¬ (3 : ℤ) ∣ WithZero.log (ν i (rad i)))
      (hoff : ∀ i j, i ≠ j → ν i (rad j) = 1)
      (huval : ∀ i, WithZero.log (ν i u) = 0)
      (e : ι → ℕ) : ¬ ∃ c : K, c ^ 3 = u * ∏ i, rad i ^ e i := by
    classical
    have hrad (i : ι) : rad i ≠ 0 := by
      intro hz
      exact hdiag i (by simp [hz])
    rintro ⟨c, hc⟩
    have hdiv (i : ι) : 3 ∣ e i := by
      have hvalprod : ν i (∏ k, rad k ^ e k) = (ν i (rad i)) ^ e i := by
        calc
          ν i (∏ k, rad k ^ e k) = ∏ k, ν i (rad k ^ e k) := by rw [map_prod]
          _ = ν i (rad i ^ e i) :=
            Finset.prod_eq_single_of_mem i (Finset.mem_univ i)
              (by
                intro k _ hki
                rw [map_pow, hoff i k hki.symm, one_pow])
          _ = (ν i (rad i)) ^ e i := by rw [map_pow]
      have hlog := congrArg WithZero.log (congrArg (ν i) hc)
      simp only [map_pow, map_mul, hvalprod] at hlog
      rw [WithZero.log_pow,
        WithZero.log_mul ((ν i).ne_zero_iff.mpr hu0)
          (pow_ne_zero _ ((ν i).ne_zero_iff.mpr (hrad i))),
        WithZero.log_pow, huval i] at hlog
      simp only [nsmul_eq_mul, zero_add] at hlog
      have hthree : (3 : ℤ) ∣ (e i : ℤ) * WithZero.log (ν i (rad i)) :=
        ⟨WithZero.log (ν i c), hlog.symm⟩
      have hdvd := Int.Prime.dvd_mul' Nat.prime_three hthree
      have hcast : (3 : ℤ) ∣ (e i : ℤ) := hdvd.resolve_right (hdiag i)
      exact_mod_cast hcast
    let b : K := ∏ i, rad i ^ (e i / 3)
    have hb : b ≠ 0 := by
      dsimp [b]
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      exact pow_ne_zero _ (hrad i)
    have hprod : (∏ i, rad i ^ e i) = b ^ 3 := by
      dsimp [b]
      calc
        (∏ i, rad i ^ e i) = ∏ i, (rad i ^ (e i / 3)) ^ 3 := by
          apply Finset.prod_congr rfl
          intro i _
          have he : e i = 3 * (e i / 3) := (Nat.mul_div_cancel' (hdiv i)).symm
          calc
            rad i ^ e i = rad i ^ ((e i / 3) * 3) :=
              congrArg (fun n : ℕ => rad i ^ n) (he.trans (mul_comm _ _))
            _ = (rad i ^ (e i / 3)) ^ 3 := by rw [pow_mul]
        _ = (∏ i, rad i ^ (e i / 3)) ^ 3 := by rw [Finset.prod_pow]
    have hc' : c ^ 3 = u * b ^ 3 := by simpa only [hprod] using hc
    apply hunoncube
    refine ⟨c / b, ?_⟩
    apply (mul_right_cancel₀ (pow_ne_zero _ hb))
    calc
      (c / b) ^ 3 * b ^ 3 = c ^ 3 := by field_simp [hb]
      _ = u * b ^ 3 := hc'

  classical
  let N := Fintype.card ι
  let equiv : Fin N ≃ ι := (Fintype.equivFin ι).symm
  let radseq : ℕ → K := fun n =>
    if hn : 1 ≤ n ∧ n ≤ N then rad (equiv ⟨n - 1, by omega⟩) else 1
  let roots : ℕ → L := fun n =>
    if hn : 1 ≤ n ∧ n ≤ N then root (equiv ⟨n - 1, by omega⟩) else 0
  let νseq : ℕ → Valuation K (WithZero (Multiplicative ℤ)) := fun n =>
    if hn : 1 ≤ n ∧ n ≤ N then ν (equiv ⟨n - 1, by omega⟩) else 1
  have hrootseq (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) :
      roots n ^ 3 = algebraMap K L (radseq n) := by
    dsimp only [roots, radseq]
    simp only [dif_pos (show 1 ≤ n ∧ n ≤ N from ⟨hn, hnN⟩)]
    exact hroot _
  have hradseq (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) : radseq n ≠ 0 := by
    dsimp only [radseq]
    simp only [dif_pos (show 1 ≤ n ∧ n ≤ N from ⟨hn, hnN⟩)]
    exact hrad _
  have hdiagseq (n : ℕ) (hn : n < N) :
      ¬ (3 : ℤ) ∣ WithZero.log (νseq (n + 1) (radseq (n + 1))) := by
    have hn' : 1 ≤ n + 1 ∧ n + 1 ≤ N := ⟨by omega, by omega⟩
    dsimp only [νseq, radseq]
    simp only [dif_pos hn']
    exact hdiag _
  have hoffseq (n : ℕ) (hn : n < N) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      νseq (n + 1) (radseq i) = 1 := by
    have hni : 1 ≤ i ∧ i ≤ N := ⟨hi, by omega⟩
    have hnn : 1 ≤ n + 1 ∧ n + 1 ≤ N := ⟨by omega, by omega⟩
    dsimp only [νseq, radseq]
    simp only [dif_pos hni, dif_pos hnn]
    apply hoff
    intro heq
    have hf := congrArg Fin.val (equiv.injective heq)
    change n + 1 - 1 = i - 1 at hf
    omega
  have hdiagFin (k : Fin N) :
      ¬ (3 : ℤ) ∣ WithZero.log (νseq (k.val + 1) (radseq (k.val + 1))) :=
    hdiagseq k.val k.isLt
  have hoffFin (k l : Fin N) (hkl : k ≠ l) :
      νseq (k.val + 1) (radseq (l.val + 1)) = 1 := by
    have hk : 1 ≤ k.val + 1 ∧ k.val + 1 ≤ N := ⟨by omega, by omega⟩
    have hl : 1 ≤ l.val + 1 ∧ l.val + 1 ≤ N := ⟨by omega, by omega⟩
    dsimp only [νseq, radseq]
    simp only [dif_pos hk, dif_pos hl]
    apply hoff
    intro heq
    exact hkl (equiv.injective heq)
  have huvalFin (k : Fin N) : WithZero.log (νseq (k.val + 1) u) = 0 := by
    have hk : 1 ≤ k.val + 1 ∧ k.val + 1 ≤ N := ⟨by omega, by omega⟩
    dsimp only [νseq]
    simp only [dif_pos hk]
    exact huval _
  let P : ℕ → K → Prop := fun n a =>
    (n < N ∧ a ≠ 0 ∧ ¬ (3 : ℤ) ∣ WithZero.log (νseq (n + 1) a)) ∨
      (n = N ∧ ∃ e : Fin N → ℕ,
        a = u * ∏ k : Fin N, radseq (k.val + 1) ^ e k)
  have hPcube : ∀ n, n ≤ N → ∀ a, P n a → ¬ ∃ c : K, c ^ 3 = a := by
    intro n hn a ha
    rcases ha with ⟨hlt, _, hval⟩ | ⟨heq, e, he⟩
    · rintro ⟨c, hc⟩
      apply hval
      rw [← hc, map_pow, WithZero.log_pow, nsmul_eq_mul]
      exact ⟨WithZero.log (νseq (n + 1) c), by ring⟩
    · subst n
      rw [he]
      exact valuation_unit_span_noncube
        (fun k : Fin N => radseq (k.val + 1))
        (fun k : Fin N => νseq (k.val + 1))
        u hu0 hunoncube hdiagFin hoffFin huvalFin e
  have hPmul : ∀ n, n ≤ N → ∀ i, 1 ≤ i → i ≤ n → ∀ a q,
      P n a → P n (a * radseq i ^ q) := by
    intro n hn i hi hin a q ha
    rcases ha with ⟨hlt, ha0, hval⟩ | ⟨heq, f, hf⟩
    · left
      refine ⟨hlt, mul_ne_zero ha0 (pow_ne_zero _ (hradseq i hi (by omega))), ?_⟩
      change ¬ (3 : ℤ) ∣ WithZero.log (νseq (n + 1) (a * radseq i ^ q))
      rw [map_mul,
        WithZero.log_mul ((νseq (n + 1)).ne_zero_iff.mpr ha0)
          ((νseq (n + 1)).ne_zero_iff.mpr
            (pow_ne_zero _ (hradseq i hi (by omega)))),
        map_pow, hoffseq n hlt i hi hin, one_pow]
      simpa using hval
    · subst n
      right
      let k : Fin N := ⟨i - 1, by omega⟩
      have hk : k.val + 1 = i := by dsimp [k]; omega
      let f' : Fin N → ℕ := Function.update f k (f k + q)
      refine ⟨rfl, f', ?_⟩
      have hnew :
          (∏ l : Fin N, radseq (l.val + 1) ^ f' l) =
            (∏ l : Fin N, radseq (l.val + 1) ^ f l) *
              radseq (k.val + 1) ^ q := by
        have hupdate :
            (∏ l : Fin N, radseq (l.val + 1) ^ f' l) =
              radseq (k.val + 1) ^ (f k + q) *
                ∏ l ∈ (Finset.univ : Finset (Fin N)).erase k,
                  radseq (l.val + 1) ^ f l := by
          calc
            _ = ∏ l : Fin N,
                Function.update (fun t : Fin N => radseq (t.val + 1) ^ f t) k
                  (radseq (k.val + 1) ^ (f k + q)) l := by
              apply Finset.prod_congr rfl
              intro l _
              by_cases h : l = k
              · subst l; simp [f', Function.update]
              · simp [f', Function.update, h]
            _ = _ := by
              simpa only [Finset.sdiff_singleton_eq_erase] using
                (Finset.prod_update_of_mem (Finset.mem_univ k) _ _)
        rw [hupdate, pow_add]
        calc
          (radseq (k.val + 1) ^ f k * radseq (k.val + 1) ^ q) *
              ∏ l ∈ (Finset.univ : Finset (Fin N)).erase k,
                radseq (l.val + 1) ^ f l =
            (radseq (k.val + 1) ^ f k *
              ∏ l ∈ (Finset.univ : Finset (Fin N)).erase k,
                radseq (l.val + 1) ^ f l) * radseq (k.val + 1) ^ q := by ac_rfl
          _ = _ :=
            congrArg (fun z : K => z * radseq (k.val + 1) ^ q)
              (Finset.mul_prod_erase (Finset.univ : Finset (Fin N))
                (fun l : Fin N => radseq (l.val + 1) ^ f l) (Finset.mem_univ k))
      calc
        a * radseq i ^ q =
            (u * ∏ l : Fin N, radseq (l.val + 1) ^ f l) *
              radseq (k.val + 1) ^ q := by rw [hf, hk]
        _ = u * ∏ l : Fin N, radseq (l.val + 1) ^ f' l := by
          rw [hnew]
          ring
  have hPfresh : ∀ n, n < N → P n (radseq (n + 1)) := by
    intro n hn
    exact Or.inl ⟨hn, hradseq (n + 1) (by omega) (by omega), hdiagseq n hn⟩
  have hmain := D5.S3.Factorization.Galois.CubicRadicalTowerDegree.cubic_radical_tower_degree_of_saturated_noncube_tests
    ζ hζ radseq roots N hrootseq P hPcube hPmul hPfresh
  have hrepr := finite_support_representation (K := K) (L := L) root
  change D5.S3.Factorization.Galois.CubicRadicalTowerDegree.radicalTower (K := K) roots N =
    IntermediateField.adjoin K (Set.range root) at hrepr
  rw [← hrepr]
  refine ⟨hmain.1, ?_⟩
  intro x
  exact hmain.2 u (Or.inr ⟨rfl, (fun _ => 0), by simp⟩) x


end D5.S3.Factorization.Galois.CubicRadicalTowerDegree
