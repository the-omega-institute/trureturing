/- GID: D5/S3/Factorization/Galois/GoldenCubicCompatibilityCompositum
   generality: I
   mirror-B: D5/B/S3/Factorization/Galois/GoldenCubicCompatibilityCompositum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual radical and cyclotomic fields carry the character-defined compatibility automorphism and its residue action. -/
import D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness
import D5.S3.Factorization.QuadraticIdeals.CubicIdealCharacter
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.FieldTheory.SplittingField.IsSplittingField
import Mathlib.GroupTheory.IndexNormal
import Mathlib.Algebra.Group.Conj
import Mathlib.Data.Set.Card
import Mathlib.Tactic
import Mathlib.RingTheory.Frobenius
import Mathlib.Algebra.Algebra.Equiv
import D5.S3.Factorization.Galois.Chebotarev.Main
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.RingTheory.Unramified.Locus

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Polynomial NumberField
open Filter Set Topology Chebotarev
open scoped Pointwise nonZeroDivisors

open D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness
open D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open D5.S3.Factorization.QuadraticIdeals.EisensteinCyclotomicBridge
open D5.S3.Factorization.QuadraticIdeals.CubicIdealCharacter
open scoped NumberField

def ActualCompositumData (j : ℕ) (a : (ZMod (modulus j))ˣ) : Prop :=
    letI : IsCyclotomicExtension {3} ℚ E := CyclotomicField.isCyclotomicExtension 3 ℚ
    ∃ ζ : L, IsPrimitiveRoot ζ (modulus j) ∧
      ∃ π : ℕ → EisensteinOrder, ∃ root : radicalIndex j → L,
        let φ : EisensteinOrder ≃ₐ[ℤ] 𝓞 E :=
          Classical.choice eisenstein_cyclotomic_equiv_exists
        let B : ℕ → ℕ := blockValue
        let S : Finset ℕ := support j
        let I := radicalIndex j
        let f : EisensteinOrder →+* E :=
          (algebraMap (𝓞 E) E).comp φ.toRingHom
        let ξ : E := f QuadraticAlgebra.omega
        let lam : EisensteinOrder := 1 + 2 * QuadraticAlgebra.omega
        let κ : {p : ℕ // p ∈ S} → E := fun p =>
          f (localCubicSymbol (Ideal.span {π p.1}) lam)
        let target : I → E := Sum.elim
          (fun w => if w.2 then (κ w.1)⁻¹ ^ 2 else (κ w.1) ^ 2)
          (fun _ => ξ ^ 2)
        ((∀ p ∈ S,
          (Ideal.span {π p}).IsPrime ∧ QuadraticAlgebra.norm (π p) = (p : ℤ) ∧
          (3 : EisensteinOrder) ∣ π p - 1 ∧ p % 3 = 1 ∧
          IsCoprime (π p) (star (π p))) ∧
        (∀ p ∈ S, ∀ q ∈ S, p ≠ q →
          IsCoprime (π p) (π q) ∧ IsCoprime (π p) (star (π q)) ∧
          IsCoprime (star (π p)) (π q) ∧
          IsCoprime (star (π p)) (star (π q))) ∧
        (∀ i, 1 ≤ i → i < j →
          orientedFactor ((D5.S1.Scale.goldenLucas (3 ^ i) - 1).toNat) =
            ∏ p ∈ (B i).primeFactors,
              π p ^ padicValNat p
                (Nat.fib (D5.S3.Arith.Primes.FiniteFibonacciRankClosure.fibonacciRank p))) ∧
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
            σ (⟨root i, IntermediateField.subset_adjoin E (Set.range root)
                ⟨i, rfl⟩⟩ : IntermediateField.adjoin E (Set.range root)) =
              algebraMap E (IntermediateField.adjoin E (Set.range root))
                (IsCyclotomicExtension.zeta 3 ℚ E) ^
                (Multiplicative.toAdd (e σ i)).val *
                  (⟨root i, IntermediateField.subset_adjoin E (Set.range root)
                    ⟨i, rfl⟩⟩ : IntermediateField.adjoin E (Set.range root)))) ∧
        (∀ p : {p : ℕ // p ∈ S},
          let P : Ideal EisensteinOrder := Ideal.span {π p.1}
          let q := Ideal.Quotient.mk P
          lam ∉ P ∧ (3 : EisensteinOrder) ∉ P ∧
            q (localCubicSymbol P lam) = q lam ^ ((p.1 - 1) / 3)) ∧
        let M : IntermediateField E L := IntermediateField.adjoin E (Set.range root)
        let C : IntermediateField E L := actualCyclotomic ζ
        let F : IntermediateField E L := M ⊔ C
        M ⊓ C = ⊥ ∧
        let M' : IntermediateField E F :=
          IntermediateField.restrict (show M ≤ F from le_sup_left)
        let C' : IntermediateField E F :=
          IntermediateField.restrict (show C ≤ F from le_sup_right)
        let aM : M ≃ₐ[E] M' :=
          IntermediateField.restrictAlgEquiv (show M ≤ F from le_sup_left)
        let aC : C ≃ₐ[E] C' :=
          IntermediateField.restrictAlgEquiv (show C ≤ F from le_sup_right)
        let β : radicalIndex j → M := fun v =>
          ⟨root v, IntermediateField.subset_adjoin E (Set.range root) ⟨v, rfl⟩⟩
        let ζC : C := ⟨ζ, IntermediateField.mem_adjoin_simple_self E ζ⟩
        let β₂ : F :=
          ⟨root (Sum.inr (0 : Fin 2)),
            (show M ≤ F from le_sup_left)
              (IntermediateField.subset_adjoin E (Set.range root)
                ⟨Sum.inr (0 : Fin 2), rfl⟩)⟩
        let ζ₃ : E := IsCyclotomicExtension.zeta 3 ℚ E
        let z : F := algebraMap E F ξ
        Normal ℚ F ∧
        ∃ gcoord : I → Multiplicative (ZMod 3),
          (∀ v, ζ₃ ^ (Multiplicative.toAdd (gcoord v)).val = target v) ∧
        ∃ e : (F ≃ₐ[E] F) ≃* ((M ≃ₐ[E] M) × (C ≃ₐ[E] C)),
          ∃ gM : M ≃ₐ[E] M, ∃ σa : C ≃ₐ[E] C, ∃ gF : F ≃ₐ[E] F,
            e gF = (gM, σa) ∧
            (∀ v, gM (β v) = algebraMap E M (target v) * β v) ∧
            σa ζC = ζC ^ a.val.val ∧
            (∀ x : M', gF (x : F) = ((aM.autCongr gM x : M') : F)) ∧
            (∀ x : C', gF (x : F) = ((aC.autCongr σa x : C') : F)) ∧
            Module.finrank E F =
              3 ^ (2 * (D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.support j).card + 2) * Module.finrank E C ∧
            ∃ hNF : NumberField F, ∃ hGal : IsGalois ℚ F,
              letI : NumberField F := hNF
              letI : IsGalois ℚ F := hGal
              gF β₂ = z ^ 2 * β₂ ∧
              IsCyclotomicExtension {modulus j} ℚ C ∧
              (∀ (𝔭 : Ideal (𝓞 ℚ)) (_ : 𝔭.IsPrime)
                  (_ : Chebotarev.UnramifiedIn ℚ F 𝔭)
                  (hcop : (Ideal.absNorm 𝔭).Coprime (modulus j)),
                  Chebotarev.frobeniusClass ℚ F 𝔭 =
                    ConjClasses.mk (gF.restrictScalars ℚ) →
                  ZMod.unitOfCoprime (Ideal.absNorm 𝔭) hcop = a)

theorem actual_compositum_data (j : ℕ) (a : (ZMod (modulus j))ˣ)
    (ha : ZMod.unitsMap (show 3 ∣ modulus j by
      refine ⟨80 * 3 ^ (j + 1), ?_⟩
      simp [modulus, pow_succ, mul_assoc, mul_comm]) a = 1) :
    ActualCompositumData j a := by
  classical
  letI : IsCyclotomicExtension {3} ℚ E :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  letI : IsGalois ℚ E := IsCyclotomicExtension.isGalois {3} ℚ E
  have hdiv : 3 ∣ modulus j := by
    refine ⟨80 * 3 ^ (j + 1), ?_⟩
    simp [modulus, pow_succ, mul_assoc, mul_comm]
  have ha' : ZMod.unitsMap hdiv a = 1 := ha
  have hcomplete := actual_complete_cubic_cyclotomic_disjointness j
  dsimp only at hcomplete
  obtain ⟨ζ, hζ, π, root, hdata, hdisj⟩ := hcomplete
  let φ : EisensteinOrder ≃ₐ[ℤ] 𝓞 E :=
    Classical.choice eisenstein_cyclotomic_equiv_exists
  let f : EisensteinOrder →+* E :=
    (algebraMap (𝓞 E) E).comp φ.toRingHom
  let ξ : E := f QuadraticAlgebra.omega
  let lam : EisensteinOrder := 1 + 2 * QuadraticAlgebra.omega
  let κ : {p : ℕ // p ∈ D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.support j} → E := fun p =>
    f (localCubicSymbol (Ideal.span {π p.1}) lam)
  let target : radicalIndex j → E := Sum.elim
    (fun w => if w.2 then (κ w.1)⁻¹ ^ 2 else (κ w.1) ^ 2)
    (fun _ => ξ ^ 2)
  have hLamNorm : Algebra.norm ℤ lam = 3 := by
    rw [Algebra.norm_apply]
    change (DistribSMul.toLinearMap ℤ EisensteinOrder lam).det = 3
    rw [QuadraticAlgebra.det_toLinearMap_eq_norm]
    norm_num [lam, QuadraticAlgebra.norm_def, QuadraticAlgebra.re_mul,
      QuadraticAlgebra.im_mul, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  have hLamSq : lam ^ 2 = -(3 : EisensteinOrder) := by
    apply QuadraticAlgebra.ext
    · norm_num [lam, pow_two, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.im_mul, QuadraticAlgebra.re_ofNat,
        QuadraticAlgebra.im_ofNat, QuadraticAlgebra.re_one,
        QuadraticAlgebra.im_one]
    · norm_num [lam, pow_two, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.im_mul, QuadraticAlgebra.re_ofNat,
        QuadraticAlgebra.im_ofNat, QuadraticAlgebra.re_one,
        QuadraticAlgebra.im_one]
  have hEuler (p : {p : ℕ // p ∈ D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.support j}) :
      let P : Ideal EisensteinOrder := Ideal.span {π p.1}
      let q := Ideal.Quotient.mk P
      lam ∉ P ∧ (3 : EisensteinOrder) ∉ P ∧
        q (localCubicSymbol P lam) = q lam ^ ((p.1 - 1) / 3) := by
    let P : Ideal EisensteinOrder := Ideal.span {π p.1}
    let q := Ideal.Quotient.mk P
    have hπ := hdata.1 p.1 p.2
    have hp : p.1.Prime := by
      obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp p.2
      exact Nat.prime_of_mem_primeFactors hpi
    letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    letI : NeZero (3 : ℚ) := ⟨by norm_num⟩
    letI : IsPrincipalIdealRing (𝓞 E) :=
      IsCyclotomicExtension.Rat.three_pid E
    letI : IsDomain EisensteinOrder :=
      φ.toRingEquiv.isDomain_iff.mpr inferInstance
    letI : IsPrincipalIdealRing EisensteinOrder :=
      IsPrincipalIdealRing.of_surjective φ.symm.toRingHom φ.symm.surjective
    have hAlgNorm : Algebra.norm ℤ (π p.1) = QuadraticAlgebra.norm (π p.1) := by
      rw [Algebra.norm_apply]
      exact QuadraticAlgebra.det_toLinearMap_eq_norm _
    have hPnorm : Ideal.absNorm P = p.1 := by
      change Ideal.absNorm (Ideal.span {π p.1}) = p.1
      rw [Ideal.absNorm_span_singleton, hAlgNorm, hπ.2.1]
      simp
    have hPne : P ≠ ⊥ := by
      intro h
      rw [h, Ideal.absNorm_bot] at hPnorm
      exact hp.ne_zero hPnorm.symm
    have hPmax : P.IsMaximal := hπ.1.isMaximal hPne
    have hPfinite : Finite (EisensteinOrder ⧸ P) :=
      (Ideal.absNorm_ne_zero_iff P).mp (by rw [hPnorm]; exact hp.ne_zero)
    have hPcard : Nat.card (EisensteinOrder ⧸ P) = p.1 := by
      simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply] using hPnorm
    have hLamNot : lam ∉ P := by
      intro hmem
      have hdvd : p.1 ∣ 3 := by
        have h := Ideal.absNorm_dvd_absNorm_of_le
          ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
        have h' : p.1 ∣ Int.natAbs (3 : ℤ) := by
          simpa only [hPnorm, Ideal.absNorm_span_singleton, hLamNorm] using h
        norm_num at h'
        exact h'
      have hp3 : p.1 = 3 :=
        (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdvd
      omega
    have hThreeNot : (3 : EisensteinOrder) ∉ P := by
      intro hmem
      have hsq : lam ^ 2 ∈ P := by
        rw [hLamSq]
        exact P.neg_mem hmem
      exact hLamNot (hπ.1.mem_of_pow_mem 2 hsq)
    have hcardmod : Nat.card (EisensteinOrder ⧸ P) % 3 = 1 := by
      rw [hPcard]
      exact hπ.2.2.2.1
    have hchar :=
      (cubic_ideal_character_and_factored_multiplicativity
        ({()} : Finset Unit) (fun _ => P)
        (by intro i hi; exact hPmax)
        (by intro i hi; exact hPfinite)
        (by intro i hi; exact hcardmod)
        (by intro i hi; exact hThreeNot)).1 () (by simp) lam hLamNot
    change lam ∉ P ∧ (3 : EisensteinOrder) ∉ P ∧
      q (localCubicSymbol P lam) = q lam ^ ((p.1 - 1) / 3)
    refine ⟨hLamNot, hThreeNot, ?_⟩
    simpa only [q, hPcard] using hchar.2.1
  have hωpoly : (QuadraticAlgebra.omega : EisensteinOrder) ^ 2 +
      QuadraticAlgebra.omega + 1 = 0 := by
    rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_add]
    simp
  have hξpoly : ξ ^ 2 + ξ + 1 = 0 := by
    have h := congrArg f hωpoly
    simpa only [map_add, map_pow, map_one, map_zero, ξ] using h
  have hξ3 : ξ ^ 3 = 1 := by
    linear_combination (ξ - 1) * hξpoly
  have hξne : ξ ≠ 1 := by
    intro heq
    rw [heq] at hξpoly
    norm_num at hξpoly
  have hξ2ne : ξ ^ 2 ≠ 1 := by
    intro h2
    apply hξne
    calc
      ξ = ξ ^ 2 * ξ := by rw [h2]; ring
      _ = ξ ^ 3 := by ring
      _ = 1 := hξ3
  have hξprimitive : IsPrimitiveRoot ξ 3 := by
    refine (IsPrimitiveRoot.iff (by decide : 0 < 3)).2 ⟨hξ3, ?_⟩
    intro n hn hlt
    have hn' : n = 1 ∨ n = 2 := by omega
    rcases hn' with rfl | rfl
    · simpa only [pow_one] using hξne
    · exact hξ2ne
  have hκ3 (p : {p : ℕ // p ∈
      D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.support j}) :
      (κ p) ^ 3 = 1 := by
    have hcases : localCubicSymbol (Ideal.span {π p.1}) lam = 1 ∨
        localCubicSymbol (Ideal.span {π p.1}) lam = QuadraticAlgebra.omega ∨
        localCubicSymbol (Ideal.span {π p.1}) lam = QuadraticAlgebra.omega ^ 2 := by
      dsimp [localCubicSymbol]
      split_ifs <;> simp
    rcases hcases with h | h | h
    · simp only [κ, h, map_one, one_pow]
    · simpa only [κ, h, ξ] using hξ3
    · calc
        (κ p) ^ 3 = (ξ ^ 2) ^ 3 := by simp only [κ, h, map_pow, ξ]
        _ = (ξ ^ 3) ^ 2 := by rw [← pow_mul, ← pow_mul]
        _ = 1 := by rw [hξ3]; simp
  let ζ₃ : E := IsCyclotomicExtension.zeta 3 ℚ E
  have hζ₃ : IsPrimitiveRoot ζ₃ 3 :=
    IsCyclotomicExtension.zeta_spec 3 ℚ E
  have htarget3 (v : radicalIndex j) : (target v) ^ 3 = 1 := by
    rcases v with w | i
    · by_cases hb : w.2
      · change (if w.2 then (κ w.1)⁻¹ ^ 2 else (κ w.1) ^ 2) ^ 3 = 1
        rw [if_pos hb]
        calc
          ((κ w.1)⁻¹ ^ 2) ^ 3 = ((κ w.1) ^ 3)⁻¹ ^ 2 := by
            rw [pow_right_comm, inv_pow]
          _ = 1 := by rw [hκ3]; simp
      · change (if w.2 then (κ w.1)⁻¹ ^ 2 else (κ w.1) ^ 2) ^ 3 = 1
        rw [if_neg hb]
        rw [pow_right_comm, hκ3] <;> simp
    · change (ξ ^ 2) ^ 3 = 1
      rw [pow_right_comm, hξ3] <;> simp
  have hcoordExist (v : radicalIndex j) :
      ∃ n : ℕ, n < 3 ∧ target v = ζ₃ ^ n := by
    obtain ⟨n, hn, hpow⟩ := hζ₃.eq_pow_of_pow_eq_one (htarget3 v)
    exact ⟨n, hn, hpow.symm⟩
  choose coordNat hcoordBound hcoordPow using hcoordExist
  have hQnormal : Normal ℚ (((IntermediateField.adjoin E (Set.range root)) ⊔
      actualCyclotomic ζ).restrictScalars ℚ) := by
    let S : Finset ℕ :=
      D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.support j
    have hπ := hdata.1
    have hroot := hdata.2.2.2.1
    have hdegree := hdata.2.2.2.2.1
    let φ : EisensteinOrder ≃ₐ[ℤ] 𝓞 E :=
      Classical.choice eisenstein_cyclotomic_equiv_exists
    let f : EisensteinOrder →+* E :=
      (algebraMap (𝓞 E) E).comp φ.toRingHom
    let M : IntermediateField E L := IntermediateField.adjoin E (Set.range root)
    let Cyc : IntermediateField E L := actualCyclotomic ζ
    let rad : radicalIndex j → E :=
      Sum.elim
        (fun w => f (if w.2 then star (π w.1.val) else π w.1.val))
        (fun k => if k.val = 0 then (2 : E) else 3)
    let β : radicalIndex j → M := fun v =>
      ⟨root v, IntermediateField.subset_adjoin E (Set.range root) ⟨v, rfl⟩⟩
    have hβ (v : radicalIndex j) :
        β v ^ 3 = algebraMap E M (rad v) := by
      cases v with
      | inl w =>
          apply Subtype.ext
          simpa [β, rad, f, φ, NumberField.RingOfIntegers.coe_eq_algebraMap]
            using hroot (Sum.inl w)
      | inr k =>
          fin_cases k
          · apply Subtype.ext
            change root (Sum.inr (0 : Fin 2)) ^ 3 = algebraMap E L (2 : E)
            rw [map_ofNat]
            simpa [NumberField.RingOfIntegers.coe_eq_algebraMap, map_ofNat]
              using hroot (Sum.inr (0 : Fin 2))
          · apply Subtype.ext
            change root (Sum.inr (1 : Fin 2)) ^ 3 = algebraMap E L (3 : E)
            rw [map_ofNat]
            simpa [NumberField.RingOfIntegers.coe_eq_algebraMap, map_ofNat]
              using hroot (Sum.inr (1 : Fin 2))
    let z : M := algebraMap E M (IsCyclotomicExtension.zeta 3 ℚ E)
    have hz : IsPrimitiveRoot z 3 :=
      (IsCyclotomicExtension.zeta_spec 3 ℚ E).map_of_injective
        (algebraMap E M).injective
    let q : ℕ → ℚ[X] := fun p =>
      X ^ 6 - C ((QuadraticAlgebra.trace (π p) : ℤ) : ℚ) * X ^ 3 + C (p : ℚ)
    let P : ℚ[X] := cyclotomic 3 ℚ * (X ^ 3 - C (2 : ℚ)) *
      (X ^ 3 - C (3 : ℚ)) * ∏ p ∈ S, q p
    have hfInt (n : ℤ) : f (algebraMap ℤ EisensteinOrder n) = (n : E) := by
      change f (n : EisensteinOrder) = (n : E)
      exact map_intCast f n
    have hsum (p : ℕ) :
        f (π p) + f (star (π p)) =
          ((QuadraticAlgebra.trace (π p) : ℤ) : E) := by
      have h := congrArg f (QuadraticAlgebra.algebraMap_trace_eq_add_star (π p))
      simpa only [map_add, hfInt] using h.symm
    have hnorm (p : ℕ) (hp : p ∈ S) :
        f (π p) * f (star (π p)) = (p : E) := by
      have h := congrArg f (QuadraticAlgebra.algebraMap_norm_eq_mul_star (π p))
      rw [(hπ p hp).2.1] at h
      simpa only [map_mul, hfInt, Int.cast_natCast] using h.symm
    have hpolyFactor (p : ℕ) (hp : p ∈ S) :
        (q p).map (algebraMap ℚ E) =
          (X ^ 3 - C (f (π p))) * (X ^ 3 - C (f (star (π p)))) := by
      simp only [q, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
        Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
        Polynomial.map_intCast, Polynomial.map_natCast]
      change X ^ 6 - C (((QuadraticAlgebra.trace (π p) : ℤ) : E)) * X ^ 3 +
        C (p : E) =
        (X ^ 3 - C (f (π p))) * (X ^ 3 - C (f (star (π p))))
      rw [← hsum p, ← hnorm p hp]
      simp only [map_add, map_mul]
      ring
    have hqmap (p : ℕ) (hp : p ∈ S) :
        (q p).map (algebraMap ℚ M) =
          ((X ^ 3 - C (f (π p)) : E[X]).map (algebraMap E M)) *
          ((X ^ 3 - C (f (star (π p))) : E[X]).map (algebraMap E M)) := by
      have h := congrArg (Polynomial.map (algebraMap E M)) (hpolyFactor p hp)
      simpa only [Polynomial.map_map, ← IsScalarTower.algebraMap_eq,
        Polynomial.map_mul] using h
    have hcubic (v : radicalIndex j) :
        ((X ^ 3 - C (rad v) : E[X]).map (algebraMap E M)).Splits := by
      simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.map_C] using X_pow_sub_C_splits_of_isPrimitiveRoot hz (hβ v)
    have hqsplit (p : ℕ) (hp : p ∈ S) :
        ((q p).map (algebraMap ℚ M)).Splits := by
      rw [hqmap p hp]
      have hfirst :
          ((X ^ 3 - C (f (π p)) : E[X]).map (algebraMap E M)).Splits := by
        simpa [rad] using hcubic (Sum.inl (⟨p, hp⟩, false))
      have hsecond :
          ((X ^ 3 - C (f (star (π p))) : E[X]).map (algebraMap E M)).Splits := by
        simpa [rad] using hcubic (Sum.inl (⟨p, hp⟩, true))
      exact hfirst.mul hsecond
    have hcyclo : ((cyclotomic 3 ℚ).map (algebraMap ℚ M)).Splits := by
      have hE := IsCyclotomicExtension.splits_cyclotomic ℚ E
        (show 3 ∈ ({3} : Set ℕ) by simp)
      have hM := hE.map (algebraMap E M)
      simpa only [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] using hM
    have htwo : (((X ^ 3 - C (2 : ℚ)) : ℚ[X]).map (algebraMap ℚ M)).Splits := by
      simpa [rad, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.map_C, map_ofNat] using hcubic (Sum.inr (0 : Fin 2))
    have hthree : (((X ^ 3 - C (3 : ℚ)) : ℚ[X]).map (algebraMap ℚ M)).Splits := by
      simpa [rad, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.map_C, map_ofNat] using hcubic (Sum.inr (1 : Fin 2))
    have hPsplit : (P.map (algebraMap ℚ M)).Splits := by
      simp only [P, Polynomial.map_mul, Polynomial.map_prod]
      exact ((hcyclo.mul htwo).mul hthree).mul
        (Polynomial.Splits.prod (fun p hp => hqsplit p hp))
    have hqne (p : ℕ) (hp : p ∈ S) : q p ≠ 0 := by
      intro hzero
      have h := hpolyFactor p hp
      rw [hzero, Polynomial.map_zero] at h
      have hleft : (X ^ 3 - C (f (π p)) : E[X]) ≠ 0 :=
        X_pow_sub_C_ne_zero (by decide) _
      have hright : (X ^ 3 - C (f (star (π p))) : E[X]) ≠ 0 :=
        X_pow_sub_C_ne_zero (by decide) _
      exact (mul_ne_zero hleft hright) h.symm
    have hPne : P ≠ 0 := by
      dsimp only [P]
      apply mul_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero
          · exact cyclotomic_ne_zero 3 ℚ
          · exact X_pow_sub_C_ne_zero (by decide) _
        · exact X_pow_sub_C_ne_zero (by decide) _
      · exact Finset.prod_ne_zero_iff.mpr (fun p hp => hqne p hp)
    have hqeval (p : ℕ) (hp : p ∈ S) (b : Bool) :
        aeval (β (Sum.inl (⟨p, hp⟩, b))) (q p) = 0 := by
      rw [← eval_map_algebraMap, hqmap p hp, eval_mul, mul_eq_zero]
      cases b with
      | false =>
          left
          simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
            Polynomial.map_C, eval_sub, eval_pow, eval_X, eval_C]
          simpa [rad] using sub_eq_zero.mpr (hβ (Sum.inl (⟨p, hp⟩, false)))
      | true =>
          right
          simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
            Polynomial.map_C, eval_sub, eval_pow, eval_X, eval_C]
          simpa [rad] using sub_eq_zero.mpr (hβ (Sum.inl (⟨p, hp⟩, true)))
    letI : Module.IsTorsionFree ℚ M := DivisionSemiring.to_moduleIsTorsionFree
    have hrootP (v : radicalIndex j) : β v ∈ P.rootSet M := by
      rw [mem_rootSet_of_ne hPne]
      cases v with
      | inl w =>
          obtain ⟨p, b⟩ := w
          have hprod : aeval (β (Sum.inl (p, b)))
              (∏ u ∈ S, q u) = 0 := by
            rw [map_prod]
            exact Finset.prod_eq_zero p.property (hqeval p.val p.property b)
          simp [P, hprod]
      | inr k =>
          fin_cases k
          · have ht : aeval (β (Sum.inr (0 : Fin 2)))
                (X ^ 3 - C (2 : ℚ)) = 0 := by
              simpa [rad, map_ofNat] using sub_eq_zero.mpr (hβ (Sum.inr (0 : Fin 2)))
            simp [P, ht]
          · have ht : aeval (β (Sum.inr (1 : Fin 2)))
                (X ^ 3 - C (3 : ℚ)) = 0 := by
              simpa [rad, map_ofNat] using sub_eq_zero.mpr (hβ (Sum.inr (1 : Fin 2)))
            simp [P, ht]
    have hzP : z ∈ P.rootSet M := by
      rw [mem_rootSet_of_ne hPne]
      have hc : aeval z (cyclotomic 3 ℚ) = 0 := by
        rw [← eval_map_algebraMap, map_cyclotomic]
        exact hz.isRoot_cyclotomic (by decide)
      simp only [P, map_mul, hc, zero_mul]
    let incl : M →ₐ[ℚ] L := M.val.toRingHom.toRatAlgHom
    have hInclRange : incl.fieldRange = M.restrictScalars ℚ := by
      ext x
      constructor
      · rintro ⟨t, rfl⟩
        exact t.property
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    let fE : E →ₐ[ℚ] L := IsScalarTower.toAlgHom ℚ E L
    let KQ : IntermediateField ℚ L := fE.fieldRange
    have hKQ : IsCyclotomicExtension {3} ℚ KQ :=
      IsCyclotomicExtension.equiv {3} ℚ E fE.equivFieldRange
    let ζ3 : E := IsCyclotomicExtension.zeta 3 ℚ E
    have hζ3L : IsPrimitiveRoot (algebraMap E L ζ3) 3 :=
      (IsCyclotomicExtension.zeta_spec 3 ℚ E).map_of_injective
        (algebraMap E L).injective
    have hKQeq : KQ = IntermediateField.adjoin ℚ {algebraMap E L ζ3} :=
      (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin
        3 ℚ L KQ hζ3L).mp hKQ
    have hcompat : algebraMap E L = (algebraMap KQ L) ∘ fE.equivFieldRange := by
      funext x
      rfl
    have hMrat : M.restrictScalars ℚ =
        KQ ⊔ IntermediateField.adjoin ℚ (Set.range root) := by
      calc
        M.restrictScalars ℚ =
            (IntermediateField.adjoin KQ (Set.range root)).restrictScalars ℚ := by
              exact IntermediateField.restrictScalars_adjoin_of_algEquiv
                fE.equivFieldRange hcompat (Set.range root)
        _ = KQ ⊔ IntermediateField.adjoin ℚ (Set.range root) :=
          IntermediateField.restrictScalars_adjoin_eq_sup ℚ KQ (Set.range root)
    have hgen : IntermediateField.adjoin ℚ (P.rootSet M) = ⊤ := by
      apply IntermediateField.map_injective incl
      rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map, hInclRange]
      change IntermediateField.adjoin ℚ (Subtype.val '' P.rootSet M) =
        M.restrictScalars ℚ
      apply le_antisymm
      · apply IntermediateField.adjoin_le_iff.mpr
        rintro x ⟨t, ht, rfl⟩
        exact t.property
      · rw [hMrat, hKQeq]
        apply sup_le
        · apply IntermediateField.adjoin_le_iff.mpr
          intro x hx
          rcases Set.mem_singleton_iff.mp hx with rfl
          exact IntermediateField.subset_adjoin ℚ _ ⟨z, hzP, rfl⟩
        · apply IntermediateField.adjoin_le_iff.mpr
          rintro x ⟨v, rfl⟩
          exact IntermediateField.subset_adjoin ℚ _ ⟨β v, hrootP v, rfl⟩
    letI : IsSplittingField ℚ M P :=
      isSplittingField_iff_intermediateField.mpr ⟨hPsplit, hgen⟩
    have hMnormal : Normal ℚ M := Normal.of_isSplittingField P
    have hmzero : modulus j ≠ 0 := by
      unfold modulus
      positivity
    letI : NeZero (modulus j) := ⟨hmzero⟩
    have hthreeDiv : 3 ∣ modulus j := by
      refine ⟨80 * 3 ^ (j + 1), ?_⟩
      simp [modulus, pow_succ, mul_assoc, mul_comm]
    let CQ : IntermediateField ℚ L := IntermediateField.adjoin ℚ {ζ}
    have hCQ : IsCyclotomicExtension {modulus j} ℚ CQ :=
      (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin
        (modulus j) ℚ L CQ hζ).2 rfl
    have hle : KQ ≤ CQ :=
      IntermediateField.isCyclotomicExtension_le_of_dvd
        (n₁ := 3) (n₂ := modulus j) (h₁ := hKQ) (h₂ := hCQ)
        ℚ L KQ CQ hthreeDiv
    have hCeq : Cyc.restrictScalars ℚ = CQ := by
      calc
        Cyc.restrictScalars ℚ =
            (IntermediateField.adjoin KQ {ζ}).restrictScalars ℚ := by
              exact IntermediateField.restrictScalars_adjoin_of_algEquiv
                fE.equivFieldRange hcompat {ζ}
        _ = KQ ⊔ CQ := IntermediateField.restrictScalars_adjoin_eq_sup ℚ KQ {ζ}
        _ = CQ := sup_eq_right.mpr hle
    have hCnormal : Normal ℚ (Cyc.restrictScalars ℚ) := by
      letI : IsCyclotomicExtension {modulus j} ℚ CQ := hCQ
      letI : IsGalois ℚ CQ := IsCyclotomicExtension.isGalois {modulus j} ℚ CQ
      exact hCeq.symm ▸ inferInstance
    have hMQnormal : Normal ℚ (M.restrictScalars ℚ) :=
      IntermediateField.restrictScalars_normal.mpr hMnormal
    letI : Normal ℚ (M.restrictScalars ℚ) := hMQnormal
    letI : Normal ℚ (Cyc.restrictScalars ℚ) := hCnormal
    have hnormal : Normal ℚ ((M ⊔ Cyc).restrictScalars ℚ) := by
      rw [← IntermediateField.restrictScalars_sup]
      exact @IntermediateField.normal_sup ℚ L _ _ _
        (M.restrictScalars ℚ) (Cyc.restrictScalars ℚ) hMQnormal hCnormal
    exact hnormal
  let M : IntermediateField E L := IntermediateField.adjoin E (Set.range root)
  let C : IntermediateField E L := actualCyclotomic ζ
  let F : IntermediateField E L := M ⊔ C
  have hactualDisj : M ⊓ C = ⊥ := hdisj
  have hFnormal : Normal ℚ F :=
    IntermediateField.restrictScalars_normal.mp hQnormal
  let β : radicalIndex j → M := fun v =>
    ⟨root v, IntermediateField.subset_adjoin E (Set.range root) ⟨v, rfl⟩⟩
  let ζC : C := ⟨ζ, IntermediateField.mem_adjoin_simple_self E ζ⟩
  let gcoord : radicalIndex j → Multiplicative (ZMod 3) :=
    fun v => Multiplicative.ofAdd ((coordNat v : ℕ) : ZMod 3)
  have hcoord (v : radicalIndex j) :
      ζ₃ ^ (Multiplicative.toAdd (gcoord v)).val = target v := by
    change ζ₃ ^ (((coordNat v : ℕ) : ZMod 3).val) = target v
    simpa only [ZMod.val_natCast_of_lt (hcoordBound v)] using
      (hcoordPow v).symm
  let β₂ : F :=
    ⟨root (Sum.inr (0 : Fin 2)),
      (show M ≤ F from le_sup_left)
        (IntermediateField.subset_adjoin E (Set.range root)
          ⟨Sum.inr (0 : Fin 2), rfl⟩)⟩
  let z : F := algebraMap E F ξ
  have hdegree : Module.finrank E M = 3 ^ (2 * (D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.support j).card + 2) :=
    hdata.2.2.2.2.1
  letI : IsGalois E M := hdata.2.2.2.2.2.2.1
  letI : FiniteDimensional E M :=
    FiniteDimensional.of_finrank_pos (by rw [hdegree]; positivity)
  letI : NumberField M := NumberField.of_module_finite E M
  letI : NeZero (modulus j) := ⟨by simp [modulus]⟩
  letI : IsCyclotomicExtension {modulus j} E C :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin
      (modulus j) E L C hζ).2 rfl
  letI : FiniteDimensional E C :=
    IsCyclotomicExtension.finiteDimensional {modulus j} E C
  letI : IsGalois E C := IsCyclotomicExtension.isGalois {modulus j} E C
  letI : FiniteDimensional E F := IntermediateField.finiteDimensional_sup M C
  letI : IsGalois E F := ⟨⟩
  have hLD : M.LinearDisjoint C :=
    IntermediateField.LinearDisjoint.of_inf_eq_bot hdisj
  have hdegF : Module.finrank E F =
      3 ^ (2 * (D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.support j).card + 2) * Module.finrank E C := by
    simpa only [F, hdegree] using hLD.finrank_sup
  have hMF : M ≤ F := le_sup_left
  have hCF : C ≤ F := le_sup_right
  let M' : IntermediateField E F := IntermediateField.restrict hMF
  let C' : IntermediateField E F := IntermediateField.restrict hCF
  let aM : M ≃ₐ[E] M' := IntermediateField.restrictAlgEquiv hMF
  let aC : C ≃ₐ[E] C' := IntermediateField.restrictAlgEquiv hCF
  letI : IsGalois E M' := IsGalois.of_algEquiv aM
  letI : IsGalois E C' := IsGalois.of_algEquiv aC
  have htop : M' ⊔ C' = ⊤ := by
    apply IntermediateField.lift_injective F
    rw [IntermediateField.lift_sup, IntermediateField.lift_restrict,
      IntermediateField.lift_restrict, IntermediateField.lift_top]
  let rM : (F ≃ₐ[E] F) →* (M' ≃ₐ[E] M') := AlgEquiv.restrictNormalHom M'
  let rC : (F ≃ₐ[E] F) →* (C' ≃ₐ[E] C') := AlgEquiv.restrictNormalHom C'
  let r : (F ≃ₐ[E] F) →* ((M' ≃ₐ[E] M') × (C' ≃ₐ[E] C')) := rM.prod rC
  have hrinj : Function.Injective r := by
    apply (injective_iff_map_eq_one r).2
    intro σ hσ
    have hm : σ ∈ rM.ker := by
      change rM σ = 1
      exact congrArg Prod.fst hσ
    have hc : σ ∈ rC.ker := by
      change rC σ = 1
      exact congrArg Prod.snd hσ
    have hm' : σ ∈ M'.fixingSubgroup := by
      rwa [← IntermediateField.restrictNormalHom_ker M']
    have hc' : σ ∈ C'.fixingSubgroup := by
      rwa [← IntermediateField.restrictNormalHom_ker C']
    have htopfix : σ ∈ (⊤ : IntermediateField E F).fixingSubgroup := by
      rw [← htop, IntermediateField.fixingSubgroup_sup]
      exact ⟨hm', hc'⟩
    simpa only [IntermediateField.fixingSubgroup_top, Subgroup.mem_bot] using htopfix
  have hcard : Nat.card (F ≃ₐ[E] F) =
      Nat.card ((M' ≃ₐ[E] M') × (C' ≃ₐ[E] C')) := by
    calc
      Nat.card (F ≃ₐ[E] F) = Module.finrank E F :=
        IsGalois.card_aut_eq_finrank E F
      _ = Module.finrank E M * Module.finrank E C := hLD.finrank_sup
      _ = Module.finrank E M' * Module.finrank E C' := by
        rw [aM.toLinearEquiv.finrank_eq, aC.toLinearEquiv.finrank_eq]
      _ = Nat.card ((M' ≃ₐ[E] M') × (C' ≃ₐ[E] C')) := by
        rw [Nat.card_prod, IsGalois.card_aut_eq_finrank E M',
          IsGalois.card_aut_eq_finrank E C']
  have hrbij : Function.Bijective r :=
    hrinj.bijective_of_nat_card_le hcard.symm.le
  let eF : (F ≃ₐ[E] F) ≃* ((M' ≃ₐ[E] M') × (C' ≃ₐ[E] C')) :=
    MulEquiv.ofBijective r hrbij
  let e : (F ≃ₐ[E] F) ≃* ((M ≃ₐ[E] M) × (C ≃ₐ[E] C)) :=
    eF.trans (aM.autCongr.symm.prodCongr aC.autCongr.symm)
  obtain ⟨eM, heM⟩ := hdata.2.2.2.2.2.2.2
  let gM : M ≃ₐ[E] M := eM.symm gcoord
  have hgM (v : radicalIndex j) :
      gM (β v) = algebraMap E M (target v) * β v := by
    calc
      gM (β v) =
          algebraMap E M ζ₃ ^ (Multiplicative.toAdd (gcoord v)).val * β v := by
            simpa only [gM, eM.apply_symm_apply, ζ₃] using heM gM v
      _ = algebraMap E M (target v) * β v := by
        rw [← map_pow, hcoord]
  let f : E →ₐ[ℚ] L := IsScalarTower.toAlgHom ℚ E L
  let KQ : IntermediateField ℚ L := f.fieldRange
  let CQ : IntermediateField ℚ L := IntermediateField.adjoin ℚ {ζ}
  have hKQ : IsCyclotomicExtension {3} ℚ KQ :=
    IsCyclotomicExtension.equiv {3} ℚ E f.equivFieldRange
  have hCQ : IsCyclotomicExtension {modulus j} ℚ CQ :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin
      (modulus j) ℚ L CQ hζ).2 rfl
  have hle : KQ ≤ CQ :=
    IntermediateField.isCyclotomicExtension_le_of_dvd
      (n₁ := 3) (n₂ := modulus j) (h₁ := hKQ) (h₂ := hCQ)
      ℚ L KQ CQ hdiv
  have hcompat : algebraMap E L = (algebraMap KQ L) ∘ f.equivFieldRange := by
    funext x
    rfl
  have heq : C.restrictScalars ℚ = CQ := by
    calc
      C.restrictScalars ℚ =
          (IntermediateField.adjoin KQ {ζ}).restrictScalars ℚ := by
            exact IntermediateField.restrictScalars_adjoin_of_algEquiv
              f.equivFieldRange hcompat {ζ}
      _ = KQ ⊔ CQ := by
        exact IntermediateField.restrictScalars_adjoin_eq_sup ℚ KQ {ζ}
      _ = CQ := sup_eq_right.mpr hle
  letI : IsCyclotomicExtension {modulus j} ℚ C := by
    change IsCyclotomicExtension {modulus j} ℚ (C.restrictScalars ℚ)
    exact heq.symm ▸ hCQ
  letI : NumberField C := IsCyclotomicExtension.numberField {modulus j} ℚ C
  let eQ := IsCyclotomicExtension.Rat.galEquivZMod (modulus j) C
  let e3 := IsCyclotomicExtension.Rat.galEquivZMod 3 E
  let τ : C ≃ₐ[ℚ] C := eQ.symm a
  have hcomm : e3 (τ.restrictNormal E) = ZMod.unitsMap hdiv (eQ τ) :=
    IsCyclotomicExtension.Rat.galEquivZMod_restrictNormal_apply
      (modulus j) C E hdiv τ
  have hτ : τ.restrictNormal E = 1 := by
    apply e3.injective
    rw [hcomm, eQ.apply_symm_apply, ha']
    exact (map_one e3).symm
  have hτfix (x : E) : τ (algebraMap E C x) = algebraMap E C x := by
    have h := AlgEquiv.restrictNormal_commutes τ E x
    rw [hτ] at h
    simpa only [AlgEquiv.one_apply] using h.symm
  let σa : C ≃ₐ[E] C := { τ.toRingEquiv with commutes' := hτfix }
  have hζpow : ζC ^ (modulus j) = 1 := by
    apply Subtype.ext
    exact hζ.pow_eq_one
  have hσa : σa ζC = ζC ^ a.val.val := by
    change τ ζC = ζC ^ a.val.val
    have h := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
      (modulus j) C τ hζpow
    change τ ζC = ζC ^ (eQ τ).val.val at h
    simpa only [τ, eQ.apply_symm_apply] using h
  let gF : F ≃ₐ[E] F := e.symm (gM, σa)
  have heG : e gF = (gM, σa) := e.apply_symm_apply _
  have hrM : rM gF = aM.autCongr gM := by
    have h := congrArg Prod.fst heG
    change aM.autCongr.symm (rM gF) = gM at h
    exact (aM.autCongr.symm).injective (by simpa only [MulEquiv.symm_apply_apply] using h)
  have hrC : rC gF = aC.autCongr σa := by
    have h := congrArg Prod.snd heG
    change aC.autCongr.symm (rC gF) = σa at h
    exact (aC.autCongr.symm).injective (by simpa only [MulEquiv.symm_apply_apply] using h)
  have hpointM (x : M') :
      gF (x : F) = ((aM.autCongr gM x : M') : F) := by
    have h := AlgEquiv.restrictNormal_commutes gF M' x
    change ((rM gF) x : F) = gF (x : F) at h
    rw [hrM] at h
    exact h.symm
  have hpointC (x : C') :
      gF (x : F) = ((aC.autCongr σa x : C') : F) := by
    have h := AlgEquiv.restrictNormal_commutes gF C' x
    change ((rC gF) x : F) = gF (x : F) at h
    rw [hrC] at h
    exact h.symm
  have hgm2 : gM (β (Sum.inr (0 : Fin 2))) =
      (algebraMap E M ξ) ^ 2 * β (Sum.inr (0 : Fin 2)) := by
    have h := hgM (Sum.inr (0 : Fin 2))
    change gM (β (Sum.inr (0 : Fin 2))) =
      algebraMap E M (ξ ^ 2) * β (Sum.inr (0 : Fin 2)) at h
    simpa only [map_pow] using h
  have hgfβ : gF β₂ = z ^ 2 * β₂ := by
    calc
      gF β₂ = gF ((aM (β (Sum.inr (0 : Fin 2))) : M') : F) := rfl
      _ = ((aM.autCongr gM (aM (β (Sum.inr (0 : Fin 2)))) : M') : F) :=
        hpointM _
      _ = ((aM (gM (β (Sum.inr (0 : Fin 2)))) : M') : F) := by
        congr 1
        simp only [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
          aM.symm_apply_apply]
      _ = z ^ 2 * β₂ := by
        rw [hgm2, map_mul, map_pow]
        change ((aM (algebraMap E M ξ) : M') : F) ^ 2 * β₂ = z ^ 2 * β₂
        have hzmap : ((aM (algebraMap E M ξ) : M') : F) = z :=
          congrArg (fun x : M' => (x : F)) (aM.commutes ξ)
        rw [hzmap]
  letI : NumberField F := NumberField.of_module_finite E F
  letI : IsGalois ℚ F := ⟨⟩
  let gQ : F ≃ₐ[ℚ] F := gF.restrictScalars ℚ
  let ζF : F := ((aC ζC : C') : F)
  have hζCL : IsPrimitiveRoot (algebraMap C L ζC) (modulus j) := by
    simpa [ζC] using hζ
  have hζC : IsPrimitiveRoot ζC (modulus j) :=
    hζCL.of_map_of_injective (algebraMap C L).injective
  have hζC' : IsPrimitiveRoot (aC ζC) (modulus j) :=
    hζC.map_of_injective aC.injective
  have hζF : IsPrimitiveRoot ζF (modulus j) :=
    hζC'.map_of_injective (algebraMap C' F).injective
  have hact : gQ ζF = ζF ^ a.val.val := by
    have h := hpointC (aC ζC)
    simpa only [gQ, ζF, AlgEquiv.restrictScalars_apply, AlgEquiv.autCongr_apply,
      AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, hσa, map_pow,
      IntermediateField.coe_pow] using h
  have hres : ∀ (𝔭 : Ideal (𝓞 ℚ)) (_ : 𝔭.IsPrime)
      (_ : Chebotarev.UnramifiedIn ℚ F 𝔭)
      (hcop : (Ideal.absNorm 𝔭).Coprime (modulus j)),
      Chebotarev.frobeniusClass ℚ F 𝔭 = ConjClasses.mk gQ →
      ZMod.unitOfCoprime (Ideal.absNorm 𝔭) hcop = a := by
    intro 𝔭 hp hunr hcop hclass
    letI : 𝔭.IsPrime := hp
    classical
    obtain ⟨𝔓₀, h𝔓₀, hcomap₀⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 F) 𝔭 (by
        rw [(RingHom.injective_iff_ker_eq_bot _).mp
          (FaithfulSMul.algebraMap_injective (𝓞 ℚ) (𝓞 F))]
        exact bot_le)
    have hlo₀ : 𝔓₀.LiesOver 𝔭 := ⟨hcomap₀.symm⟩
    letI : 𝔓₀.IsPrime := h𝔓₀
    letI : Finite (𝓞 F ⧸ 𝔓₀) :=
      Ideal.finiteQuotientOfFreeOfNeBot 𝔓₀
        (Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓₀)
    let σ : F ≃ₐ[ℚ] F := arithFrobAt (𝓞 ℚ) Gal(F/ℚ) 𝔓₀
    have hσ : IsArithFrobAt (𝓞 ℚ) σ 𝔓₀ :=
      IsArithFrobAt.arithFrobAt (𝓞 ℚ) Gal(F/ℚ) 𝔓₀
    have hclassσ : Chebotarev.frobeniusClass ℚ F 𝔭 = ConjClasses.mk σ := by
      let e : ∃ 𝔓 : Ideal (𝓞 F), 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 := by
        obtain ⟨𝔓, hp, hcomap⟩ :=
          Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 F) 𝔭 (by
            rw [(RingHom.injective_iff_ker_eq_bot _).mp
              (FaithfulSMul.algebraMap_injective (𝓞 ℚ) (𝓞 F))]
            exact bot_le)
        exact ⟨𝔓, hp, ⟨hcomap.symm⟩⟩
      let 𝔓 := Classical.choose e
      letI : 𝔓.IsPrime := (Classical.choose_spec e).1
      have hlo : 𝔓.LiesOver 𝔭 := (Classical.choose_spec e).2
      letI : Finite (𝓞 F ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓
        (Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓)
      rw [Chebotarev.frobeniusClass, dif_pos ⟨‹𝔭.IsPrime›, hunr⟩]
      change ConjClasses.mk (arithFrobAt (𝓞 ℚ) Gal(F/ℚ) 𝔓) = ConjClasses.mk σ
      exact ConjClasses.mk_eq_mk_iff_isConj.mpr <|
        isConj_arithFrobAt (𝓞 ℚ) Gal(F/ℚ) 𝔓 𝔓₀ (hlo.over.symm.trans hlo₀.over)
    have hconj : IsConj σ gQ :=
      ConjClasses.mk_eq_mk_iff_isConj.mp (hclassσ.symm.trans hclass)
    obtain ⟨t, ht⟩ := isConj_iff.mp hconj
    let 𝔓 : Ideal (𝓞 F) := t • 𝔓₀
    letI : 𝔓.IsPrime := inferInstance
    have hlo : 𝔓.LiesOver 𝔭 := inferInstance
    have hg : IsArithFrobAt (𝓞 ℚ) gQ 𝔓 := by
      rw [← ht]
      exact hσ.conj t
    let z : 𝓞 F := hζF.toInteger
    have hzint : IsPrimitiveRoot z (modulus j) := hζF.toInteger_isPrimitiveRoot
    have hPne : Ideal.absNorm 𝔓 ≠ 1 :=
      fun h => (inferInstance : 𝔓.IsPrime).ne_top (Ideal.absNorm_eq_one_iff.mp h)
    have hPcop : (Ideal.absNorm 𝔓).Coprime (modulus j) := by
      rw [Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver 𝔓 𝔭
        (inferInstance : 𝔭.IsPrime) hunr.1]
      exact Nat.Coprime.pow_left _ hcop
    have hmnotmem : ((modulus j) : 𝓞 F) ∉ 𝔓 := by
      intro hmem
      have hd := Ideal.absNorm_dvd_absNorm_of_le
        ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
      rw [Ideal.absNorm_span_singleton,
        show (((modulus j) : ℕ) : 𝓞 F) = algebraMap ℤ (𝓞 F) ((modulus j) : ℤ) by push_cast; rfl,
        Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast] at hd
      exact hPne ((hPcop.pow_right _).eq_one_of_dvd hd)
    have hqcard : Ideal.absNorm 𝔭 =
        Nat.card (𝓞 ℚ ⧸ 𝔓.under (𝓞 ℚ)) := by
      rw [show 𝔭 = 𝔓.under (𝓞 ℚ) from hlo.over,
        Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have hkey := hg.apply_of_pow_eq_one hzint.pow_eq_one hmnotmem
    rw [← hqcard] at hkey
    have hmap := congrArg (algebraMap (𝓞 F) F) hkey
    have hnormaction : gQ ζF = ζF ^ Ideal.absNorm 𝔭 := by
      rwa [map_pow,
        show (algebraMap (𝓞 F) F)
            ((MulSemiringAction.toAlgHom (𝓞 ℚ) (𝓞 F) gQ) z) = gQ ζF from rfl,
        show (algebraMap (𝓞 F) F) z = ζF from rfl] at hmap
    have hpow : ζF ^ Ideal.absNorm 𝔭 = ζF ^ a.val.val :=
      hnormaction.symm.trans hact
    have hmodord : Ideal.absNorm 𝔭 ≡ a.val.val [MOD orderOf ζF] :=
      (hζF.isOfFinOrder (NeZero.ne (modulus j))).pow_eq_pow_iff_modEq.mp hpow
    have hmod : Ideal.absNorm 𝔭 ≡ a.val.val [MOD (modulus j)] := by
      simpa only [hζF.eq_orderOf] using hmodord
    apply Units.ext
    rw [ZMod.coe_unitOfCoprime, ← ZMod.natCast_zmod_val a.val]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  exact ⟨ζ, hζ, π, root, hdata, hEuler, hactualDisj, hFnormal,
    gcoord, hcoord, e, gM, σa, gF, heG, hgM, hσa,
    hpointM, hpointC, hdegF, inferInstance, inferInstance,
    hgfβ, inferInstance, hres⟩
