/- GID: D5/S3/Factorization/Galois/GoldenCubicCompleteCyclotomicDisjointness
   generality: I
   mirror-B: D5/B/S3/Factorization/Galois/GoldenCubicCompleteCyclotomicDisjointness
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The actual complete golden cubic radical field meets the corresponding cyclotomic field only in the cubic cyclotomic base. -/

import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic
import D5.S3.Factorization.Galois.GoldenCubicCompleteUnitObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness

abbrev E := CyclotomicField 3 ℚ
abbrev L := AlgebraicClosure E

def modulus (j : ℕ) : ℕ := 80 * 3 ^ (j + 2)

def actualCyclotomic (ζ : L) : IntermediateField E L :=
  IntermediateField.adjoin E {ζ}

def ninthField (j : ℕ) (ζ : L) : IntermediateField E L :=
  IntermediateField.adjoin E {ζ ^ (modulus j / 9)}

open D5.S1.Scale
open D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct
open D5.S3.Factorization.QuadraticIdeals.EisensteinCyclotomicBridge
open D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods
open NumberField IsDedekindDomain
open scoped WithZero

def blockValue (i : ℕ) : ℕ := blockNorm ((goldenLucas (3 ^ i) - 1).toNat)
def support (j : ℕ) : Finset ℕ :=
  (Finset.Ico 1 j).biUnion (fun i => (blockValue i).primeFactors)
abbrev radicalIndex (j : ℕ) := ({p : ℕ // p ∈ support j} × Bool) ⊕ Fin 2

set_option maxHeartbeats 800000 in
theorem actual_complete_cubic_cyclotomic_disjointness (j : ℕ) :
    letI : IsCyclotomicExtension {3} ℚ E := CyclotomicField.isCyclotomicExtension 3 ℚ
    let φ : EisensteinOrder ≃ₐ[ℤ] 𝓞 E := Classical.choice eisenstein_cyclotomic_equiv_exists
    let B : ℕ → ℕ := blockValue
    let S : Finset ℕ := support j
    let I := radicalIndex j
    ∃ ζ : L, IsPrimitiveRoot ζ (modulus j) ∧
      ∃ π : ℕ → EisensteinOrder, ∃ root : I → L,
        ((∀ p ∈ S,
          (Ideal.span {π p}).IsPrime ∧ QuadraticAlgebra.norm (π p) = (p : ℤ) ∧
          (3 : EisensteinOrder) ∣ π p - 1 ∧ p % 3 = 1 ∧
          IsCoprime (π p) (star (π p))) ∧
        (∀ p ∈ S, ∀ q ∈ S, p ≠ q →
          IsCoprime (π p) (π q) ∧ IsCoprime (π p) (star (π q)) ∧
          IsCoprime (star (π p)) (π q) ∧ IsCoprime (star (π p)) (star (π q))) ∧
        (∀ i, 1 ≤ i → i < j →
          orientedFactor ((goldenLucas (3 ^ i) - 1).toNat) =
            ∏ p ∈ (B i).primeFactors,
              π p ^ padicValNat p (Nat.fib (fibonacciRank p))) ∧
        (∀ v : I, root v ^ 3 = algebraMap E L
          ((Sum.elim (fun w => φ (if w.2 then star (π w.1.val) else π w.1.val))
            (fun k => if k.val = 0 then (2 : 𝓞 E) else 3) v) : E)) ∧
        Module.finrank E (IntermediateField.adjoin E (Set.range root)) =
          3 ^ (2 * S.card + 2) ∧
        (∀ x : IntermediateField.adjoin E (Set.range root),
          x ^ 3 ≠ algebraMap E (IntermediateField.adjoin E (Set.range root))
            (IsCyclotomicExtension.zeta 3 ℚ E)) ∧
        IsGalois E (IntermediateField.adjoin E (Set.range root)) ∧
        (∃ e : ((IntermediateField.adjoin E (Set.range root)) ≃ₐ[E]
            (IntermediateField.adjoin E (Set.range root))) ≃*
            (I → Multiplicative (ZMod 3)),
          ∀ σ : (IntermediateField.adjoin E (Set.range root)) ≃ₐ[E]
              (IntermediateField.adjoin E (Set.range root)), ∀ i : I,
            σ (⟨root i, IntermediateField.subset_adjoin E (Set.range root) ⟨i, rfl⟩⟩ :
                IntermediateField.adjoin E (Set.range root)) =
              algebraMap E (IntermediateField.adjoin E (Set.range root))
                (IsCyclotomicExtension.zeta 3 ℚ E) ^
                (Multiplicative.toAdd (e σ i)).val *
                  (⟨root i, IntermediateField.subset_adjoin E (Set.range root) ⟨i, rfl⟩⟩ :
                    IntermediateField.adjoin E (Set.range root)))) ∧
        IntermediateField.adjoin E (Set.range root) ⊓ actualCyclotomic ζ = ⊥ := by
  classical
  letI : IsCyclotomicExtension {3} ℚ E := CyclotomicField.isCyclotomicExtension 3 ℚ
  have modulus_ne_zero (j : ℕ) : modulus j ≠ 0 := by
    unfold modulus
    positivity

  have three_dvd_modulus (j : ℕ) : 3 ∣ modulus j := by
    refine ⟨80 * 3 ^ (j + 1), ?_⟩
    simp [modulus, pow_succ, mul_assoc, mul_comm]

  have nine_dvd_modulus (j : ℕ) : 9 ∣ modulus j := by
    refine ⟨80 * 3 ^ j, ?_⟩
    simp [modulus, pow_add, pow_two, mul_assoc, mul_comm, mul_left_comm]

  have ninthField_le_actualCyclotomic (j : ℕ) (ζ : L) :
      ninthField j ζ ≤ actualCyclotomic ζ := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    have hx' : x = ζ ^ (modulus j / 9) := Set.mem_singleton_iff.mp hx
    rw [hx']
    change ζ ^ (modulus j / 9) ∈ IntermediateField.adjoin E {ζ}
    simpa only [zpow_natCast] using
      (IntermediateField.adjoin E {ζ}).pow_mem
        (IntermediateField.mem_adjoin_simple_self E ζ) ((modulus j / 9 : ℕ) : ℤ)

  -- Both primitive cubic roots are powers of the cube of this ninth root.
  have base_zeta_is_cube_in_ninth_field (j : ℕ) (ζ : L)
      (hζ : IsPrimitiveRoot ζ (modulus j)) :
      ∃ t : ninthField j ζ,
        t ^ 3 = algebraMap E (ninthField j ζ)
          (IsCyclotomicExtension.zeta 3 ℚ E) := by
    let ζ9 : L := ζ ^ (modulus j / 9)
    have hζ9 : IsPrimitiveRoot ζ9 9 := by
      have hprod : modulus j = (modulus j / 9) * 9 :=
        (Nat.div_mul_cancel (nine_dvd_modulus j)).symm
      exact hζ.pow (Nat.pos_of_ne_zero (modulus_ne_zero j)) hprod
    have hζ9cubed : IsPrimitiveRoot (ζ9 ^ 3) 3 := by
      exact hζ9.pow (by decide : 0 < 9) (by decide : 9 = 3 * 3)
    let ζ3 : E := IsCyclotomicExtension.zeta 3 ℚ E
    have hζ3 : IsPrimitiveRoot ζ3 3 := IsCyclotomicExtension.zeta_spec 3 ℚ E
    have hζ3L : IsPrimitiveRoot (algebraMap E L ζ3) 3 :=
      hζ3.map_of_injective (algebraMap E L).injective
    obtain ⟨i, hi, heq⟩ := hζ9cubed.eq_pow_of_pow_eq_one hζ3L.pow_eq_one
    have hmem : ζ9 ^ i ∈ ninthField j ζ := by
      change ζ9 ^ i ∈ IntermediateField.adjoin E {ζ9}
      simpa only [zpow_natCast] using
        (IntermediateField.adjoin E {ζ9}).pow_mem
          (IntermediateField.mem_adjoin_simple_self E ζ9) (i : ℤ)
    refine ⟨⟨ζ9 ^ i, hmem⟩, ?_⟩
    apply Subtype.ext
    change (ζ9 ^ i) ^ 3 = algebraMap E L ζ3
    calc
      (ζ9 ^ i) ^ 3 = (ζ9 ^ 3) ^ i := pow_right_comm ζ9 i 3
      _ = algebraMap E L ζ3 := heq

  -- The embedded copy of E lies in the rational m-th cyclotomic field.
  have actual_cyclotomic_over_rat (j : ℕ) (ζ : L)
      (hζ : IsPrimitiveRoot ζ (modulus j)) :
      IsCyclotomicExtension {modulus j} ℚ
        ((actualCyclotomic ζ).restrictScalars ℚ) := by
    let m := modulus j
    letI : NeZero m := ⟨modulus_ne_zero j⟩
    letI : IsCyclotomicExtension {3} ℚ E :=
      CyclotomicField.isCyclotomicExtension 3 ℚ
    let f : E →ₐ[ℚ] L := IsScalarTower.toAlgHom ℚ E L
    let KQ : IntermediateField ℚ L := f.fieldRange
    let CQ : IntermediateField ℚ L := IntermediateField.adjoin ℚ {ζ}
    have hKQ : IsCyclotomicExtension {3} ℚ KQ :=
      IsCyclotomicExtension.equiv {3} ℚ E f.equivFieldRange
    have hCQ : IsCyclotomicExtension {m} ℚ CQ :=
      (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin
        m ℚ L CQ hζ).2 rfl
    have hle : KQ ≤ CQ :=
      IntermediateField.isCyclotomicExtension_le_of_dvd
        (n₁ := 3) (n₂ := m) (h₁ := hKQ) (h₂ := hCQ)
        ℚ L KQ CQ (three_dvd_modulus j)
    have hcompat : algebraMap E L = (algebraMap KQ L) ∘ f.equivFieldRange := by
      funext x
      rfl
    have heq : (actualCyclotomic ζ).restrictScalars ℚ = CQ := by
      calc
        (actualCyclotomic ζ).restrictScalars ℚ =
            (IntermediateField.adjoin KQ {ζ}).restrictScalars ℚ := by
              exact IntermediateField.restrictScalars_adjoin_of_algEquiv
                f.equivFieldRange hcompat {ζ}
        _ = KQ ⊔ CQ := by
          exact IntermediateField.restrictScalars_adjoin_eq_sup ℚ KQ {ζ}
        _ = CQ := sup_eq_right.mpr hle
    exact heq.symm ▸ inferInstance

  -- The automorphisms over E form the mod-three restriction kernel.
  have actual_galois_equiv_restriction_kernel (j : ℕ) (ζ : L)
      (hζ : IsPrimitiveRoot ζ (modulus j)) :
      Nonempty ((actualCyclotomic ζ ≃ₐ[E] actualCyclotomic ζ) ≃*
        (ZMod.unitsMap (three_dvd_modulus j)).ker) := by
    let m := modulus j
    let C := actualCyclotomic ζ
    letI : NeZero m := ⟨modulus_ne_zero j⟩
    letI : IsCyclotomicExtension {3} ℚ E :=
      CyclotomicField.isCyclotomicExtension 3 ℚ
    letI : IsCyclotomicExtension {m} ℚ C := by
      change IsCyclotomicExtension {m} ℚ (C.restrictScalars ℚ)
      exact actual_cyclotomic_over_rat j ζ hζ
    letI : NumberField C := IsCyclotomicExtension.numberField {m} ℚ C
    letI : IsGalois ℚ E := IsCyclotomicExtension.isGalois {3} ℚ E
    let eQ := IsCyclotomicExtension.Rat.galEquivZMod m C
    let e3 := IsCyclotomicExtension.Rat.galEquivZMod 3 E
    let r := ZMod.unitsMap (three_dvd_modulus j)
    have hcomm (τ : C ≃ₐ[ℚ] C) : e3 (τ.restrictNormal E) = r (eQ τ) :=
      IsCyclotomicExtension.Rat.galEquivZMod_restrictNormal_apply
        m C E (three_dvd_modulus j) τ
    have hfix (σ : C ≃ₐ[E] C) :
        (σ.restrictScalars ℚ).restrictNormal E = 1 := by
      apply AlgEquiv.ext
      intro x
      apply (algebraMap E C).injective
      exact (AlgEquiv.restrictNormal_commutes (σ.restrictScalars ℚ) E x).trans
        (σ.commutes x)
    let e : (C ≃ₐ[E] C) →* r.ker := {
      toFun := fun σ => ⟨eQ (σ.restrictScalars ℚ), by
        change r (eQ (σ.restrictScalars ℚ)) = 1
        rw [← hcomm, hfix]
        exact map_one e3⟩
      map_one' := by
        apply Subtype.ext
        change eQ (AlgEquiv.restrictScalars ℚ (1 : C ≃ₐ[E] C)) = 1
        have hrest : AlgEquiv.restrictScalars ℚ (1 : C ≃ₐ[E] C) = 1 :=
          AlgEquiv.ext (fun _ => rfl)
        rw [hrest, map_one]
      map_mul' := by
        intro σ τ
        apply Subtype.ext
        change eQ (AlgEquiv.restrictScalars ℚ (σ * τ)) =
          eQ (AlgEquiv.restrictScalars ℚ σ) * eQ (AlgEquiv.restrictScalars ℚ τ)
        have hrest : AlgEquiv.restrictScalars ℚ (σ * τ) =
            AlgEquiv.restrictScalars ℚ σ * AlgEquiv.restrictScalars ℚ τ :=
          AlgEquiv.ext (fun _ => rfl)
        rw [hrest, map_mul]
    }
    have hinj : Function.Injective e := by
      intro σ τ h
      apply AlgEquiv.restrictScalars_injective ℚ
      apply eQ.injective
      exact congrArg Subtype.val h
    have hsurj : Function.Surjective e := by
      intro u
      let τ : C ≃ₐ[ℚ] C := eQ.symm u.1
      have hτ : τ.restrictNormal E = 1 := by
        apply e3.injective
        have h := hcomm τ
        change e3 (τ.restrictNormal E) = r (eQ τ) at h
        rw [eQ.apply_symm_apply, u.property] at h
        simpa only [map_one] using h
      have hτfix (x : E) : τ (algebraMap E C x) = algebraMap E C x := by
        have h := AlgEquiv.restrictNormal_commutes τ E x
        rw [hτ] at h
        simpa only [AlgEquiv.one_apply] using h.symm
      let σ : C ≃ₐ[E] C := { τ.toRingEquiv with commutes' := hτfix }
      refine ⟨σ, ?_⟩
      apply Subtype.ext
      change eQ τ = u.1
      exact eQ.apply_symm_apply u.1
    exact ⟨MulEquiv.ofBijective e ⟨hinj, hsurj⟩⟩

  letI : NeZero (modulus j : E) := ⟨by exact_mod_cast modulus_ne_zero j⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L (modulus j)
  have hcomplete := D5.S3.Factorization.Galois.GoldenCubicCompleteUnitObstruction.golden_cubic_complete_degree_and_unit_obstruction j
  dsimp only at hcomplete
  let π := Classical.choose hcomplete
  have hπdata := Classical.choose_spec hcomplete
  let root := Classical.choose hπdata
  have hdata := Classical.choose_spec hπdata
  let M : IntermediateField E L := IntermediateField.adjoin E (Set.range root)
  let C : IntermediateField E L := actualCyclotomic ζ
  let Q : IntermediateField E L := ninthField j ζ
  have hdegree : Module.finrank E M = 3 ^ (2 * (support j).card + 2) :=
    hdata.2.2.2.2.1
  letI : FiniteDimensional E M :=
    FiniteDimensional.of_finrank_pos (by rw [hdegree]; positivity)
  have hMnoncube : ∀ x : M, x ^ 3 ≠
      algebraMap E M (IsCyclotomicExtension.zeta 3 ℚ E) := hdata.2.2.2.2.2.1
  letI : IsGalois E M := hdata.2.2.2.2.2.2.1
  let eM := Classical.choose hdata.2.2.2.2.2.2.2
  have hMexp (σ : M ≃ₐ[E] M) : σ ^ 3 = 1 := by
    apply eM.injective
    have hthree (x : Multiplicative (ZMod 3)) : x ^ 3 = 1 := by
      have h := pow_card_eq_one (x := x)
      simpa only [show Fintype.card (Multiplicative (ZMod 3)) = 3 by decide] using h
    calc
      eM (σ ^ 3) = (eM σ) ^ 3 := map_pow eM σ 3
      _ = 1 := by
        ext i
        exact hthree (eM σ i)
      _ = eM 1 := (map_one eM).symm
  letI : NeZero (modulus j) := ⟨modulus_ne_zero j⟩
  letI : IsCyclotomicExtension {modulus j} E C :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin
      (modulus j) E L C hζ).2 rfl
  letI : FiniteDimensional E C :=
    IsCyclotomicExtension.finiteDimensional {modulus j} E C
  letI : IsGalois E C := IsCyclotomicExtension.isGalois {modulus j} E C
  have hQC : Q ≤ C := ninthField_le_actualCyclotomic j ζ
  have hQcube : ∃ q : Q,
      q ^ 3 = algebraMap E Q (IsCyclotomicExtension.zeta 3 ℚ E) :=
    base_zeta_is_cube_in_ninth_field j ζ hζ
  have hQgalDegree : IsGalois E Q ∧ Module.finrank E Q = 3 := by
    let ζ9 : L := ζ ^ (modulus j / 9)
    have hζ9 : IsPrimitiveRoot ζ9 9 := by
      have hprod : modulus j = (modulus j / 9) * 9 :=
        (Nat.div_mul_cancel (nine_dvd_modulus j)).symm
      exact hζ.pow (Nat.pos_of_ne_zero (modulus_ne_zero j)) hprod
    have hQcycloE : IsCyclotomicExtension {9} E Q :=
      (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin
        9 E L Q hζ9).2 rfl
    letI : IsCyclotomicExtension {9} E Q := hQcycloE
    have hQgal : IsGalois E Q := IsCyclotomicExtension.isGalois {9} E Q
    let f : E →ₐ[ℚ] L := IsScalarTower.toAlgHom ℚ E L
    let KQ : IntermediateField ℚ L := f.fieldRange
    let CQ : IntermediateField ℚ L := IntermediateField.adjoin ℚ {ζ9}
    have hKQ : IsCyclotomicExtension {3} ℚ KQ :=
      IsCyclotomicExtension.equiv {3} ℚ E f.equivFieldRange
    have hCQ : IsCyclotomicExtension {9} ℚ CQ :=
      (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin
        9 ℚ L CQ hζ9).2 rfl
    have hle : KQ ≤ CQ :=
      IntermediateField.isCyclotomicExtension_le_of_dvd
        (n₁ := 3) (n₂ := 9) (h₁ := hKQ) (h₂ := hCQ)
        ℚ L KQ CQ (by decide : 3 ∣ 9)
    have hcompat : algebraMap E L = (algebraMap KQ L) ∘ f.equivFieldRange := by
      funext x
      rfl
    have heq : Q.restrictScalars ℚ = CQ := by
      calc
        Q.restrictScalars ℚ =
            (IntermediateField.adjoin KQ {ζ9}).restrictScalars ℚ := by
              exact IntermediateField.restrictScalars_adjoin_of_algEquiv
                f.equivFieldRange hcompat {ζ9}
        _ = KQ ⊔ CQ := by
          exact IntermediateField.restrictScalars_adjoin_eq_sup ℚ KQ {ζ9}
        _ = CQ := sup_eq_right.mpr hle
    have hQcycloQ : IsCyclotomicExtension {9} ℚ Q := by
      change IsCyclotomicExtension {9} ℚ (Q.restrictScalars ℚ)
      exact heq.symm ▸ hCQ
    letI : IsCyclotomicExtension {9} ℚ Q := hQcycloQ
    have hEdeg : Module.finrank ℚ E = 2 := by
      rw [IsCyclotomicExtension.Rat.finrank 3 E]
      decide
    have hQdeg : Module.finrank ℚ Q = 6 := by
      rw [IsCyclotomicExtension.Rat.finrank 9 Q]
      decide
    have hrel : Module.finrank E Q = 3 := by
      have h := Module.finrank_mul_finrank ℚ E Q
      rw [hEdeg, hQdeg] at h
      omega
    exact ⟨hQgal, hrel⟩
  letI : IsGalois E Q := hQgalDegree.1
  let U := (ZMod (modulus j))ˣ
  have hUindex : (powMonoidHom 3 : U →* U).range.index = 3 := by
    let A := (ZMod 80)ˣ
    let B := (ZMod (3 ^ (j + 2)))ˣ
    have hc : Nat.Coprime 80 (3 ^ (j + 2)) := by
      exact (show Nat.Coprime 80 3 by decide).pow_right _
    let e : U ≃* A × B :=
      (Units.mapEquiv (ZMod.chineseRemainder hc).toMulEquiv).trans .prodUnits
    have hAcard : Fintype.card A = 32 := by
      change Fintype.card (ZMod 80)ˣ = 32
      rw [ZMod.card_units_eq_totient]
      decide
    have hAroot (a : A) (ha : a ^ 3 = 1) : a = 1 := by
      have ha32 : a ^ 32 = 1 := by
        simpa only [hAcard] using (pow_card_eq_one (x := a))
      calc
        a = a ^ (32 + 1) := by rw [pow_succ, ha32, one_mul]
        _ = a ^ (3 * 11) := by norm_num
        _ = (a ^ 3) ^ 11 := by rw [pow_mul]
        _ = 1 := by rw [ha, one_pow]
    have hAsub : Nat.card {a : A // a ^ 3 = 1} = 1 := by
      letI : Subsingleton {a : A // a ^ 3 = 1} :=
        ⟨by intro a b; apply Subtype.ext; rw [hAroot a.1 a.2, hAroot b.1 b.2]⟩
      haveI : Nonempty {a : A // a ^ 3 = 1} := ⟨⟨1, by simp⟩⟩
      exact Nat.card_unique
    have hBcard : Nat.card B = 3 ^ (j + 1) * 2 := by
      change Nat.card (ZMod (3 ^ (j + 2)))ˣ = _
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        show j + 2 = (j + 1) + 1 by omega,
        Nat.totient_prime_pow_succ Nat.prime_three]
    have hBsub : Nat.card {b : B // b ^ 3 = 1} = 3 := by
      letI : IsCyclic B :=
        ZMod.isCyclic_units_of_prime_pow 3 Nat.prime_three (by decide) (j + 2)
      change Nat.card (powMonoidHom 3 : B →* B).ker = 3
      rw [IsCyclic.card_powMonoidHom_ker, hBcard]
      apply Nat.gcd_eq_right
      refine ⟨3 ^ j * 2, ?_⟩
      simp [pow_succ, mul_assoc, mul_comm, mul_left_comm]
    have hpair (v : A × B) : v ^ 3 = 1 ↔ v.1 ^ 3 = 1 ∧ v.2 ^ 3 = 1 := by
      constructor
      · intro hv
        exact ⟨congrArg Prod.fst hv, congrArg Prod.snd hv⟩
      · rintro ⟨ha, hb⟩
        exact Prod.ext ha hb
    let eCubes : {u : U // u ^ 3 = 1} ≃ {v : A × B // v ^ 3 = 1} :=
      e.toEquiv.subtypeEquiv (by
        intro u
        constructor
        · intro hu
          change (e u) ^ 3 = 1
          simpa only [map_pow, map_one] using congrArg e hu
        · intro hu
          apply e.injective
          change (e u) ^ 3 = 1 at hu
          simpa only [map_pow, map_one] using hu)
    let pairCubes : {v : A × B // v ^ 3 = 1} ≃
        {a : A // a ^ 3 = 1} × {b : B // b ^ 3 = 1} :=
      ((Equiv.refl (A × B)).subtypeEquiv hpair).trans Equiv.subtypeProdEquivProd
    have hker : Nat.card (powMonoidHom 3 : U →* U).ker = 3 := by
      change Nat.card {u : U // u ^ 3 = 1} = 3
      calc
        _ = Nat.card {v : A × B // v ^ 3 = 1} := Nat.card_congr eCubes
        _ = Nat.card ({a : A // a ^ 3 = 1} × {b : B // b ^ 3 = 1}) :=
          Nat.card_congr pairCubes
        _ = Nat.card {a : A // a ^ 3 = 1} * Nat.card {b : B // b ^ 3 = 1} :=
          Nat.card_prod _ _
        _ = 3 := by rw [hAsub, hBsub]
    rw [Subgroup.index_range]
    exact hker
  let r : U →* (ZMod 3)ˣ := ZMod.unitsMap (three_dvd_modulus j)
  let H : Subgroup U := r.ker
  have hHindex : (powMonoidHom 3 : H →* H).range.index = 3 := by
    have h3card : Fintype.card (ZMod 3)ˣ = 2 := by
      rw [ZMod.card_units_eq_totient]
      decide
    have hrootInH (u : U) (hu : u ^ 3 = 1) : u ∈ H := by
      change r u = 1
      have h2 : (r u) ^ 2 = 1 := by
        simpa only [h3card] using (pow_card_eq_one (x := r u))
      calc
        r u = (r u) ^ (2 + 1) := by rw [pow_succ, h2, one_mul]
        _ = r (u ^ 3) := by rw [show 2 + 1 = 3 by decide, map_pow]
        _ = 1 := by rw [hu, map_one]
    let rootsEquiv : {x : H // x ^ 3 = 1} ≃ {u : U // u ^ 3 = 1} := {
      toFun := fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩
      invFun := fun u => ⟨⟨u.1, hrootInH u.1 u.2⟩, by
        apply Subtype.ext
        exact u.2⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := by
        intro u
        apply Subtype.ext
        rfl
    }
    have hker : Nat.card (powMonoidHom 3 : H →* H).ker = 3 := by
      change Nat.card {x : H // x ^ 3 = 1} = 3
      calc
        _ = Nat.card {u : U // u ^ 3 = 1} := Nat.card_congr rootsEquiv
        _ = Nat.card (powMonoidHom 3 : U →* U).ker := rfl
        _ = 3 := by
          have h := hUindex
          rwa [Subgroup.index_range] at h
    rw [Subgroup.index_range]
    exact hker
  let eC : (C ≃ₐ[E] C) ≃* H :=
    Classical.choice (actual_galois_equiv_restriction_kernel j ζ hζ)
  have hCcomm (σ τ : C ≃ₐ[E] C) : σ * τ = τ * σ := by
    apply eC.injective
    calc
      eC (σ * τ) = eC σ * eC τ := map_mul eC σ τ
      _ = eC τ * eC σ := mul_comm _ _
      _ = eC (τ * σ) := (map_mul eC τ σ).symm
  letI : CommGroup (C ≃ₐ[E] C) := ⟨hCcomm⟩
  have hCindex :
      (powMonoidHom 3 : (C ≃ₐ[E] C) →* (C ≃ₐ[E] C)).range.index = 3 := by
    have hcomap : (powMonoidHom 3 : (C ≃ₐ[E] C) →* (C ≃ₐ[E] C)).range =
        ((powMonoidHom 3 : H →* H).range).comap eC.toMonoidHom := by
      ext g
      constructor
      · rintro ⟨u, hu⟩
        change u ^ 3 = g at hu
        change ∃ v : H, v ^ 3 = eC g
        refine ⟨eC u, ?_⟩
        rw [← map_pow, hu]
      · intro hg
        change ∃ u : (C ≃ₐ[E] C), u ^ 3 = g
        change ∃ v : H, v ^ 3 = eC g at hg
        obtain ⟨v, hv⟩ := hg
        refine ⟨eC.symm v, ?_⟩
        apply eC.injective
        rw [map_pow, eC.apply_symm_apply]
        exact hv
    calc
      (powMonoidHom 3 : (C ≃ₐ[E] C) →* (C ≃ₐ[E] C)).range.index =
          (((powMonoidHom 3 : H →* H).range).comap eC.toMonoidHom).index :=
        congrArg Subgroup.index hcomap
      _ = ((powMonoidHom 3 : H →* H).range).index :=
        Subgroup.index_comap_of_surjective (H := (powMonoidHom 3 : H →* H).range)
          eC.surjective
      _ = 3 := hHindex
  have cubic_kernel_rigidity :
      ∀ {G T₀ : Type} [CommGroup G] [Finite G] [Group T₀] [Finite T₀],
        (powMonoidHom 3 : G →* G).range.index = 3 →
        (f : G →* T₀) → Function.Surjective f →
        (∀ t : T₀, t ^ 3 = 1) → Nat.card T₀ ≠ 1 →
        (powMonoidHom 3 : G →* G).range = f.ker := by
    intro G T₀ _ _ _ _ hindex f hf hexp hnontrivial
    have hle : (powMonoidHom 3 : G →* G).range ≤ f.ker := by
      rintro x ⟨g, rfl⟩
      change f (g ^ 3) = 1
      rw [map_pow, hexp]
    have hdiv : f.ker.index ∣ 3 := by
      simpa only [hindex] using Subgroup.index_dvd_of_le hle
    have hkerIndex : f.ker.index = Nat.card T₀ := by
      rw [Subgroup.index_ker, f.range_eq_top_of_surjective hf, Subgroup.card_top]
    have hcardT : Nat.card T₀ = 3 := by
      rcases Nat.prime_three.eq_one_or_self_of_dvd _ (hkerIndex ▸ hdiv) with h | h
      · exact False.elim (hnontrivial h)
      · exact h
    have hcard : Nat.card f.ker ≤ Nat.card (powMonoidHom 3 : G →* G).range := by
      have h₁ := Subgroup.card_mul_index (powMonoidHom 3 : G →* G).range
      have h₂ := Subgroup.card_mul_index f.ker
      rw [hindex] at h₁
      rw [hkerIndex, hcardT] at h₂
      omega
    exact Subgroup.eq_of_le_of_card_ge hle hcard
  refine ⟨ζ, hζ, π, root, hdata, ?_⟩
  let T : IntermediateField E L := M ⊓ C
  have hTM : T ≤ M := inf_le_left
  have hTC : T ≤ C := inf_le_right
  letI : IsScalarTower E T M := .of_algebraMap_eq' rfl
  letI : IsScalarTower E T C := .of_algebraMap_eq' rfl
  letI : FiniteDimensional E T := FiniteDimensional.left E T M
  letI : Normal E T := by
    change Normal E ↥(M ⊓ C : IntermediateField E L)
    infer_instance
  letI : IsGalois E T := {
    to_isSeparable := Algebra.isSeparable_tower_bot_of_isSeparable E T M
    to_normal := inferInstance
  }
  change T = ⊥
  by_contra hT
  let T' : IntermediateField E C := IntermediateField.restrict hTC
  let Q' : IntermediateField E C := IntermediateField.restrict hQC
  let eT : T ≃ₐ[E] T' := IntermediateField.restrictAlgEquiv hTC
  let eQ : Q ≃ₐ[E] Q' := IntermediateField.restrictAlgEquiv hQC
  letI : IsGalois E T' := IsGalois.of_algEquiv eT
  letI : IsGalois E Q' := IsGalois.of_algEquiv eQ
  letI : Normal E T' := inferInstance
  letI : Normal E Q' := inferInstance
  have hT'nonbot : T' ≠ ⊥ := by
    intro h
    apply hT
    calc
      T = IntermediateField.lift T' := (IntermediateField.lift_restrict hTC).symm
      _ = ⊥ := by rw [h, IntermediateField.lift_bot]
  have hTexp (τ : T ≃ₐ[E] T) : τ ^ 3 = 1 := by
    let fM : (M ≃ₐ[E] M) →* (T ≃ₐ[E] T) := AlgEquiv.restrictNormalHom T
    obtain ⟨σ, hσ⟩ := (AlgEquiv.restrictNormalHom_surjective M) τ
    rw [← hσ, ← map_pow, hMexp σ, map_one]
  have hT'exp (τ : T' ≃ₐ[E] T') : τ ^ 3 = 1 := by
    let a : (T' ≃ₐ[E] T') ≃* (T ≃ₐ[E] T) := eT.autCongr.symm
    apply a.injective
    rw [map_pow, hTexp (a τ), map_one]
  have hT'cardne : Nat.card (T' ≃ₐ[E] T') ≠ 1 := by
    intro h
    have hdegreeT : Module.finrank E T' = 1 := by
      rw [← IsGalois.card_aut_eq_finrank E T']
      exact h
    exact hT'nonbot (IntermediateField.finrank_eq_one_iff.mp hdegreeT)
  have hQ'card : Nat.card (Q' ≃ₐ[E] Q') = 3 := by
    rw [IsGalois.card_aut_eq_finrank E Q']
    rw [← eQ.toLinearEquiv.finrank_eq]
    exact hQgalDegree.2
  have hQ'exp (τ : Q' ≃ₐ[E] Q') : τ ^ 3 = 1 := by
    have h := pow_card_eq_one' (x := τ)
    simpa only [hQ'card] using h
  let fT : (C ≃ₐ[E] C) →* (T' ≃ₐ[E] T') := AlgEquiv.restrictNormalHom T'
  let fQ : (C ≃ₐ[E] C) →* (Q' ≃ₐ[E] Q') := AlgEquiv.restrictNormalHom Q'
  have hTsurj : Function.Surjective fT := AlgEquiv.restrictNormalHom_surjective C
  have hQsurj : Function.Surjective fQ := AlgEquiv.restrictNormalHom_surjective C
  have hTker : (powMonoidHom 3 : (C ≃ₐ[E] C) →* (C ≃ₐ[E] C)).range = fT.ker :=
    cubic_kernel_rigidity hCindex fT hTsurj hT'exp hT'cardne
  have hQker : (powMonoidHom 3 : (C ≃ₐ[E] C) →* (C ≃ₐ[E] C)).range = fQ.ker :=
    cubic_kernel_rigidity hCindex fQ hQsurj hQ'exp (by omega)
  have hfix : T'.fixingSubgroup = Q'.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker T',
      ← IntermediateField.restrictNormalHom_ker Q']
    exact hTker.symm.trans hQker
  have hT'Q' : T' = Q' := by
    calc
      T' = IntermediateField.fixedField T'.fixingSubgroup :=
        (IsGalois.fixedField_fixingSubgroup T').symm
      _ = IntermediateField.fixedField Q'.fixingSubgroup := by rw [hfix]
      _ = Q' := IsGalois.fixedField_fixingSubgroup Q'
  have hTQ : T = Q := by
    calc
      T = IntermediateField.lift T' := (IntermediateField.lift_restrict hTC).symm
      _ = IntermediateField.lift Q' := by rw [hT'Q']
      _ = Q := IntermediateField.lift_restrict hQC
  have hQM : Q ≤ M := by
    rw [← hTQ]
    exact hTM
  obtain ⟨q, hq⟩ := hQcube
  have hqM : (IntermediateField.inclusion hQM q) ^ 3 =
      algebraMap E M (IsCyclotomicExtension.zeta 3 ℚ E) := by
    calc
      (IntermediateField.inclusion hQM q) ^ 3 =
          IntermediateField.inclusion hQM (q ^ 3) := (map_pow _ q 3).symm
      _ = algebraMap E M (IsCyclotomicExtension.zeta 3 ℚ E) := by
        rw [hq]
        exact (IntermediateField.inclusion hQM).commutes _
  exact hMnoncube _ hqM

end D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness
