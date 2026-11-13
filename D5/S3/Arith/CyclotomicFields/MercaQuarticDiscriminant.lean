/- GID: D5/S3/Arith/CyclotomicFields/MercaQuarticDiscriminant
   generality: G
   mirror-B: D5/B/S3/Arith/CyclotomicFields/MercaQuarticDiscriminant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual ramification and discriminant of the Merca cyclic quartic field. -/

import D5.S3.Arith.CyclotomicFields.MercaQuadraticSubfield
import D5.S3.Factorization.Dedekind.TameDifferent
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-!
The actual quartic fixed field has one prime above r, of inertia degree one
and ramification index four. Its tame different and discriminant are computed
from the existing cyclotomic and Dedekind suppliers.
-/

set_option autoImplicit false
noncomputable section
open scoped NumberField

namespace D5.S3.Arith.CyclotomicFields.MercaQuarticDiscriminant

open NumberField NumberField.InfinitePlace Ideal UniqueFactorizationMonoid IsCyclotomicExtension

attribute [local instance] Ideal.Quotient.field
open MercaQuarticField

variable (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5)

attribute [local instance] Int.ideal_span_isMaximal_of_prime

private lemma unique_prime (P Q : Ideal (𝓞 (MercaQuarticField.Field r hr)))
    [P.IsPrime] [P.LiesOver (Ideal.span {(r : ℤ)})]
    [Q.IsPrime] [Q.LiesOver (Ideal.span {(r : ℤ)})] : P = Q := by
  let P' : Ideal.primesOver P (𝓞 (Ambient r)) := Classical.choice inferInstance
  let Q' : Ideal.primesOver Q (𝓞 (Ambient r)) := Classical.choice inferInstance
  letI : P'.val.IsPrime := P'.property.1
  letI : Q'.val.IsPrime := Q'.property.1
  letI : P'.val.LiesOver P := P'.property.2
  letI : Q'.val.LiesOver Q := Q'.property.2
  letI : P'.val.LiesOver (Ideal.span {(r : ℤ)}) :=
    Ideal.LiesOver.trans P'.val P (Ideal.span {(r : ℤ)})
  letI : Q'.val.LiesOver (Ideal.span {(r : ℤ)}) :=
    Ideal.LiesOver.trans Q'.val Q (Ideal.span {(r : ℤ)})
  have he : P'.val = Q'.val := by
    rw [Rat.eq_span_zeta_sub_one_of_liesOver' r (Ambient r)
      (IsCyclotomicExtension.zeta_spec r ℚ (Ambient r)) P'.val,
      Rat.eq_span_zeta_sub_one_of_liesOver' r (Ambient r)
      (IsCyclotomicExtension.zeta_spec r ℚ (Ambient r)) Q'.val]
  exact ((Ideal.over_def P'.val P).trans
    (congrArg (fun I : Ideal (𝓞 (Ambient r)) => I.under (𝓞 (MercaQuarticField.Field r hr)))
      he)).trans (Ideal.over_def Q'.val Q).symm

/-- The actual quartic maximal order has one prime above r, with e=4 and f=1. -/
theorem prime_structure (P : Ideal (𝓞 (MercaQuarticField.Field r hr)))
    [P.IsPrime] [P.LiesOver (Ideal.span {(r : ℤ)})] :
    (Ideal.primesOver (Ideal.span {(r : ℤ)}) (𝓞 (MercaQuarticField.Field r hr))).ncard = 1 ∧
    P.ramificationIdx ℤ = 4 ∧ P.inertiaDeg ℤ = 1 := by
  have hsingle : Ideal.primesOver (Ideal.span {(r : ℤ)})
      (𝓞 (MercaQuarticField.Field r hr)) = {P} := by
    ext Q
    constructor
    · intro hQ
      letI : Q.IsPrime := hQ.1
      letI : Q.LiesOver (Ideal.span {(r : ℤ)}) := hQ.2
      exact Set.mem_singleton_iff.mpr (unique_prime r hr Q P)
    · intro hQ
      have he : Q = P := Set.mem_singleton_iff.mp hQ
      subst Q
      exact ⟨inferInstance, inferInstance⟩
  have hcard : (Ideal.primesOver (Ideal.span {(r : ℤ)} )
      (𝓞 (MercaQuarticField.Field r hr))).ncard = 1 := by
    rw [hsingle, Set.ncard_singleton]
  let P' : Ideal.primesOver P (𝓞 (Ambient r)) := Classical.choice inferInstance
  letI : P'.val.IsPrime := P'.property.1
  letI : P'.val.LiesOver P := P'.property.2
  letI : P'.val.LiesOver (Ideal.span {(r : ℤ)}) :=
    Ideal.LiesOver.trans P'.val P (Ideal.span {(r : ℤ)})
  have hfA := Rat.inertiaDeg_eq_of_prime r (Ambient r) P'.val
  have ht := Ideal.inertiaDeg_tower (R := ℤ) P P'.val
  have hf : P.inertiaDeg ℤ = 1 := by
    rw [hfA] at ht
    exact Nat.eq_one_of_dvd_one ⟨_, ht⟩
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (Ideal.span {(r : ℤ)}) (𝓞 (MercaQuarticField.Field r hr))
    Gal(MercaQuarticField.Field r hr/ℚ)
  rw [hcard, one_mul,
    Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(r : ℤ)}) P
      Gal(MercaQuarticField.Field r hr/ℚ),
    Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(r : ℤ)}) P
      Gal(MercaQuarticField.Field r hr/ℚ),
    hf, mul_one, IsGalois.card_aut_eq_finrank, (field_structure r hr).1] at hfund
  exact ⟨hcard, hfund, hf⟩

private lemma different_exponent (P : Ideal (𝓞 (MercaQuarticField.Field r hr)))
    [P.IsPrime] [P.LiesOver (Ideal.span {(r : ℤ)})] :
    multiplicity P (differentIdeal ℤ (𝓞 (MercaQuarticField.Field r hr))) = 3 := by
  classical
  have hpbot : Ideal.span {(r : ℤ)} ≠ ⊥ := by
    simpa using (Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero : (r : ℤ) ≠ 0)
  have hPbot : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hpbot P
  letI : P.IsMaximal := (inferInstance : P.IsPrime).isMaximal hPbot
  have he := (prime_structure r hr P).2.1
  have hmap : Ideal.map (algebraMap ℤ (𝓞 (MercaQuarticField.Field r hr)))
      (Ideal.span {(r : ℤ)}) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective
      (FaithfulSMul.algebraMap_injective ℤ _)).not.mpr hpbot
  obtain ⟨Q, hsup, hfactor⟩ := Ideal.eq_prime_pow_mul_coprime hmap P
  rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
    (Ideal.span {(r : ℤ)}) P hmap, he] at hfactor
  have hfour : (4 : ℤ ⧸ Ideal.span {(r : ℤ)}) ≠ 0 := by
    intro h
    have hm : (4 : ℤ) ∈ Ideal.span {(r : ℤ)} :=
      Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using h)
    have hd : r ∣ 4 := by exact_mod_cast Ideal.mem_span_singleton.mp hm
    have := Nat.le_of_dvd (by decide : 0 < 4) hd
    omega
  have hsep : Algebra.IsSeparable (ℤ ⧸ Ideal.span {(r : ℤ)})
      ((𝓞 (MercaQuarticField.Field r hr)) ⧸ P) := inferInstance
  have hnot : ¬ P ^ 4 ∣ differentIdeal ℤ (𝓞 (MercaQuarticField.Field r hr)) := by
    rw [D5.S3.Factorization.Dedekind.TameDifferent.prime_power_divides_different_iff
      ℤ hpbot P Q ((Ideal.isCoprime_iff_sup_eq.mpr hsup).pow_left) hfactor.symm]
    exact not_or.mpr ⟨not_not.mpr hsep, hfour⟩
  have hlower : P ^ 3 ∣ differentIdeal ℤ (𝓞 (MercaQuarticField.Field r hr)) := by
    simpa only [Nat.reduceSub] using
      (pow_sub_one_dvd_differentIdeal ℤ P 4 hpbot ⟨Q, hfactor⟩)
  exact multiplicity_eq_of_emultiplicity_eq_some
    (emultiplicity_eq_coe.mpr ⟨hlower, hnot⟩)

/-- The actual absolute different is the cube of the unique prime above r. -/
theorem different_eq (P : Ideal (𝓞 (MercaQuarticField.Field r hr)))
    [P.IsPrime] [P.LiesOver (Ideal.span {(r : ℤ)})] :
    differentIdeal ℤ (𝓞 (MercaQuarticField.Field r hr)) = P ^ 3 := by
  classical
  let D := differentIdeal ℤ (𝓞 (MercaQuarticField.Field r hr))
  have hDne : D ≠ ⊥ := differentIdeal_ne_bot
  have hfactorOnly : ∀ Q ∈ normalizedFactors D, Q = P := by
    intro Q hQ
    have hprime := prime_of_normalized_factor Q hQ
    letI : Q.IsPrime := Ideal.isPrime_of_prime hprime
    letI : Q.IsMaximal := (inferInstance : Q.IsPrime).isMaximal hprime.ne_zero
    obtain ⟨p, n, hn, hpmem, hp, hnormQ⟩ := Ideal.exists_prime_and_absNorm_eq_pow Q
    letI : Fact p.Prime := ⟨hp⟩
    letI : Q.LiesOver (Ideal.span {(p : ℤ)}) :=
      (Ideal.liesOver_span_iff (inferInstance : Q.IsPrime).ne_top
        (Nat.prime_iff_prime_int.mp hp)).mpr (by simpa only [map_natCast] using hpmem)
    have hnormdiv : Q.absNorm ∣ (NumberField.discr (MercaQuarticField.Field r hr)).natAbs := by
      rw [← NumberField.absNorm_differentIdeal (MercaQuarticField.Field r hr)
        (𝓞 (MercaQuarticField.Field r hr))]
      exact Ideal.absNorm_dvd_absNorm_of_le
        (Ideal.dvd_iff_le.mp (dvd_of_mem_normalizedFactors hQ))
    have hpdiv : p ∣ (NumberField.discr (MercaQuarticField.Field r hr)).natAbs := by
      rw [hnormQ] at hnormdiv
      exact (dvd_pow_self p hn.ne').trans hnormdiv
    have hdivA := Int.natAbs_dvd_natAbs.mpr
      (NumberField.discr_dvd_discr (MercaQuarticField.Field r hr) (Ambient r))
    have hA : (NumberField.discr (Ambient r)).natAbs = r ^ (r - 2) := by
      rw [Rat.discr_prime r (Ambient r)]
      simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one,
        Int.natAbs_natCast, one_pow, one_mul]
    have hpr : p = r := by
      have hd := hpdiv.trans hdivA
      rw [hA] at hd
      exact (Nat.prime_dvd_prime_iff_eq hp (Fact.out : r.Prime)).mp
        (hp.dvd_of_dvd_pow hd)
    subst p
    exact unique_prime r hr Q P
  have hrep : normalizedFactors D = Multiset.replicate (normalizedFactors D).card P :=
    Multiset.eq_replicate_of_mem hfactorOnly
  have hpbot : Ideal.span {(r : ℤ)} ≠ ⊥ := by
    simpa using (Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero : (r : ℤ) ≠ 0)
  have hPbot : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hpbot P
  have hirr : Irreducible P := (Ideal.prime_of_isPrime hPbot inferInstance).irreducible
  have hcount : (normalizedFactors D).count P = 3 := by
    have h := multiplicity_eq_count_normalizedFactors hirr hDne
    simpa only [normalize_eq] using h.symm.trans (different_exponent r hr P)
  have hcard : (normalizedFactors D).card = 3 := by
    rw [hrep, Multiset.count_replicate_self] at hcount
    exact hcount
  change D = P ^ 3
  rw [← Ideal.prod_normalizedFactors_eq_self hDne, hrep, hcard, Multiset.prod_replicate]

/-- The cyclic quartic CM field has genuine number-field discriminant r cubed. -/
theorem discriminant : NumberField.discr (MercaQuarticField.Field r hr) = (r : ℤ) ^ 3 := by
  let P : Ideal.primesOver (Ideal.span {(r : ℤ)})
      (𝓞 (MercaQuarticField.Field r hr)) := Classical.choice inferInstance
  letI : P.val.IsPrime := P.property.1
  letI : P.val.LiesOver (Ideal.span {(r : ℤ)}) := P.property.2
  have hnorm := Ideal.pow_inertiaDeg r P.val
  rw [(prime_structure r hr P.val).2.2, pow_one] at hnorm
  have habs : (NumberField.discr (MercaQuarticField.Field r hr)).natAbs = r ^ 3 := by
    rw [← NumberField.absNorm_differentIdeal (MercaQuarticField.Field r hr)
        (𝓞 (MercaQuarticField.Field r hr)),
      different_eq r hr P.val, map_pow, ← hnorm]
  have hcomplex : nrComplexPlaces (MercaQuarticField.Field r hr) = 2 := by
    have h := NumberField.IsTotallyComplex.finrank (MercaQuarticField.Field r hr)
    rw [(field_structure r hr).1] at h
    omega
  have hsign := NumberField.sign_discr (MercaQuarticField.Field r hr)
  rw [hcomplex] at hsign
  have hpos : 0 < NumberField.discr (MercaQuarticField.Field r hr) :=
    Int.sign_eq_one_iff_pos.mp (by simpa using hsign)
  calc
    _ = |NumberField.discr (MercaQuarticField.Field r hr)| := (abs_of_pos hpos).symm
    _ = ((NumberField.discr (MercaQuarticField.Field r hr)).natAbs : ℤ) :=
      (Int.natCast_natAbs _).symm
    _ = (r : ℤ) ^ 3 := by exact_mod_cast habs

end D5.S3.Arith.CyclotomicFields.MercaQuarticDiscriminant
