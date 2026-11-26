/- GID: D5/S3/Arith/FactorialRatio/Weighted/IdealTail
   generality: G
   mirror-B: D5/B/S3/Arith/FactorialRatio/Weighted/IdealTail
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.RingTheory.Ideal.Norm.AbsNorm, mathlib/module/Mathlib.RingTheory.DedekindDomain.Factorization]
   utility: none
   digest: Bounded-norm ideal intersections and their exact weighted tail norms. -/

module

public import D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Ideal.Int
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
The intersection is taken over actual nonzero integral ideals, including the
unit ideal when the norm bound is positive. At bound zero the family is empty
and its intersection is the unit ideal. The exponent at a nonzero prime ideal
P is log_(NP)(t). Taking the norm only after multiplying these intersections
gives the weighted tail with residue-degree weights.

No assertion here interchanges an ideal norm and an ideal gcd. The comparison
with a factorial defined independently by p-orderings is a separate statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FactorialRatio.Weighted.IdealTail

open Finset UniqueFactorizationMonoid IsDedekindDomain
open CompositionGcd CompositionGcd.NumberFieldNorm
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]

local instance ringOfIntegersInfinite : Infinite (𝓞 K) :=
  Module.Free.infinite ℤ (𝓞 K)

/-- Intersection of all nonzero integral ideals of absolute norm at most t. -/
@[expose] public noncomputable def idealIntersection (t : ℕ) : Ideal (𝓞 K) :=
  ⨅ (I : Ideal (𝓞 K)) (_ : I ≠ ⊥ ∧ I.absNorm ≤ t), I

/-- The ideal product over the strict tail M<k<=H. -/
@[expose] public noncomputable def idealTail (H M : ℕ) : Ideal (𝓞 K) :=
  ∏ k ∈ Ioc M H, idealIntersection K (H / k)

private noncomputable def primeIndices (H : ℕ) : Finset (Σ _ : ℕ, Ideal (𝓞 K)) :=
  (Nat.primesLE H).sigma (primesAbove K)

private noncomputable def normEuler (H t : ℕ) : Ideal (𝓞 K) :=
  ∏ a ∈ primeIndices K H, a.2 ^ Nat.log a.2.absNorm t

private theorem above_properties {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)}
    (hP : P ∈ primesAbove K p) :
    P.IsPrime ∧ P ≠ ⊥ ∧ P.under ℤ = rationalPrimeIdeal p ∧
      P.absNorm = p ^ P.inertiaDeg ℤ := by
  letI : (rationalPrimeIdeal p).IsPrime := rationalPrimeIdeal_isPrime hp
  letI : (rationalPrimeIdeal p).IsMaximal :=
    Ideal.isMaximal_of_isPrime_of_ne_bot _ (rationalPrimeIdeal_ne_bot hp)
  obtain ⟨hprime, hover⟩ :=
    (IsDedekindDomain.mem_primesOverFinset_iff
      (rationalPrimeIdeal_ne_bot hp) (𝓞 K)).mp hP
  letI : P.IsPrime := hprime
  letI : P.LiesOver (rationalPrimeIdeal p) := hover
  letI : P.LiesOver (Ideal.span {(p : ℤ)}) := by
    simpa only [rationalPrimeIdeal] using hover
  exact ⟨hprime, Ideal.ne_bot_of_liesOver_of_ne_bot (rationalPrimeIdeal_ne_bot hp) P,
    (Ideal.over_def P (rationalPrimeIdeal p)).symm, (Ideal.pow_inertiaDeg p P).symm⟩

private theorem prime_norm_gt_one (P : HeightOneSpectrum (𝓞 K)) :
    1 < P.asIdeal.absNorm := by
  have h0 : P.asIdeal.absNorm ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot
  have h1 : P.asIdeal.absNorm ≠ 1 :=
    Ideal.absNorm_eq_one_iff.not.mpr P.isPrime.ne_top
  omega

private theorem above_base (P : HeightOneSpectrum (𝓞 K)) :
    let p := (P.asIdeal.under ℤ).absNorm
    p.Prime ∧ P.asIdeal ∈ primesAbove K p ∧ p ≤ P.asIdeal.absNorm := by
  letI : NeZero P.asIdeal := ⟨P.ne_bot⟩
  let p := (P.asIdeal.under ℤ).absNorm
  have hp : p.Prime := Nat.absNorm_under_prime P.asIdeal
  letI : (rationalPrimeIdeal p).IsPrime := rationalPrimeIdeal_isPrime hp
  letI : (rationalPrimeIdeal p).IsMaximal :=
    Ideal.isMaximal_of_isPrime_of_ne_bot _ (rationalPrimeIdeal_ne_bot hp)
  have hmem : P.asIdeal ∈ primesAbove K p := by
    apply (IsDedekindDomain.mem_primesOverFinset_iff
      (rationalPrimeIdeal_ne_bot hp) (𝓞 K)).mpr
    exact ⟨P.isPrime, Int.liesOver_span_absNorm P.asIdeal⟩
  refine ⟨hp, hmem, ?_⟩
  letI : P.asIdeal.LiesOver (rationalPrimeIdeal p) := Int.liesOver_span_absNorm P.asIdeal
  letI : P.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
    simpa only [rationalPrimeIdeal] using Int.liesOver_span_absNorm P.asIdeal
  rw [← Ideal.pow_inertiaDeg p P.asIdeal]
  have hf := P.asIdeal.inertiaDeg_pos ℤ
  calc
    p = p ^ 1 := (pow_one _).symm
    _ ≤ p ^ P.asIdeal.inertiaDeg ℤ := Nat.pow_le_pow_right hp.pos hf

private theorem primeIndices_injective {H : ℕ} :
    Set.InjOn (fun a : Σ _ : ℕ, Ideal (𝓞 K) => a.2) (primeIndices K H) := by
  intro a ha b hb hab
  obtain ⟨ha0, ha1⟩ := Finset.mem_sigma.mp ha
  obtain ⟨hb0, hb1⟩ := Finset.mem_sigma.mp hb
  have hpa := above_properties K (Nat.mem_primesLE.mp ha0).2 ha1
  have hpb := above_properties K (Nat.mem_primesLE.mp hb0).2 hb1
  have hi : rationalPrimeIdeal a.1 = rationalPrimeIdeal b.1 := by
    rw [← hpa.2.2.1, ← hpb.2.2.1]
    exact congrArg (Ideal.under ℤ) hab
  have hpq := congrArg Ideal.absNorm hi
  have hab0 : a.1 = b.1 := by
    simpa [rationalPrimeIdeal, Ideal.absNorm_span_natCast] using hpq
  exact Sigma.ext hab0 (by simpa using hab)

private theorem normEuler_ne_bot (H t : ℕ) : normEuler K H t ≠ ⊥ := by
  apply Finset.prod_ne_zero_iff.mpr
  intro a ha
  obtain ⟨hp, hP⟩ := Finset.mem_sigma.mp ha
  exact pow_ne_zero _ (above_properties K (Nat.mem_primesLE.mp hp).2 hP).2.1

private theorem normEuler_eq_inf (H t : ℕ) :
    normEuler K H t =
      (primeIndices K H).inf (fun a => a.2 ^ Nat.log a.2.absNorm t) := by
  symm
  apply IsDedekindDomain.inf_pow_eq_prod_of_prime
  · intro a ha
    obtain ⟨hp, hP⟩ := Finset.mem_sigma.mp ha
    have h := above_properties K (Nat.mem_primesLE.mp hp).2 hP
    exact Ideal.prime_of_isPrime h.2.1 h.1
  · intro a ha b hb hab
    exact fun heq => hab (primeIndices_injective K ha hb heq)

private theorem intersection_le_prime_power (t : ℕ) (P : HeightOneSpectrum (𝓞 K)) :
    idealIntersection K t ≤ P.asIdeal ^ Nat.log P.asIdeal.absNorm t := by
  by_cases ht : t = 0
  · simp [ht]
  · apply iInf_le_of_le (P.asIdeal ^ Nat.log P.asIdeal.absNorm t)
    apply iInf_le_of_le
      (show P.asIdeal ^ Nat.log P.asIdeal.absNorm t ≠ ⊥ ∧
        (P.asIdeal ^ Nat.log P.asIdeal.absNorm t).absNorm ≤ t from
        ⟨pow_ne_zero _ P.ne_bot, by
          simpa only [map_pow] using Nat.pow_log_le_self P.asIdeal.absNorm ht⟩)
    exact le_rfl

private theorem normEuler_le_ideal {H t : ℕ} (htH : t ≤ H) (I : Ideal (𝓞 K))
    (hI : I ≠ ⊥) (hIt : I.absNorm ≤ t) : normEuler K H t ≤ I := by
  rw [← Ideal.iInf_maxPowDividing_eq hI]
  apply le_iInf
  intro P
  rw [HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count P hI]
  let v := (normalizedFactors I).count P.asIdeal
  have hIP : I ≤ P.asIdeal ^ v := by
    change I ≤ P.asIdeal ^ (normalizedFactors I).count P.asIdeal
    rw [← HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count P hI]
    exact (Ideal.iInf_maxPowDividing_eq hI).symm.le.trans
      (iInf_le (fun Q : HeightOneSpectrum (𝓞 K) => Q.maxPowDividing I) P)
  have hNorm : P.asIdeal.absNorm ^ v ≤ t := by
    have hd := Ideal.absNorm_dvd_absNorm_of_le hIP
    rw [map_pow] at hd
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr hI)) hd).trans hIt
  have hv : v ≤ Nat.log P.asIdeal.absNorm t :=
    Nat.le_log_of_pow_le (prime_norm_gt_one K P) hNorm
  change normEuler K H t ≤ P.asIdeal ^ v
  by_cases hv0 : v = 0
  · simp only [hv0, pow_zero, Ideal.one_eq_top, le_top]
  · have hNP : P.asIdeal.absNorm ≤ t := by
      calc
        P.asIdeal.absNorm = P.asIdeal.absNorm ^ 1 := (pow_one _).symm
        _ ≤ P.asIdeal.absNorm ^ v := Nat.pow_le_pow_right
          (by have := prime_norm_gt_one K P; omega) (Nat.one_le_iff_ne_zero.mpr hv0)
        _ ≤ t := hNorm
    obtain ⟨hp, hP, hpNorm⟩ := above_base K P
    have hidx : (⟨(P.asIdeal.under ℤ).absNorm, P.asIdeal⟩ : Σ _ : ℕ, Ideal (𝓞 K)) ∈
        primeIndices K H :=
      Finset.mem_sigma.mpr ⟨Nat.mem_primesLE.mpr ⟨hpNorm.trans (hNP.trans htH), hp⟩, hP⟩
    exact (Ideal.dvd_iff_le.mp (Finset.dvd_prod_of_mem _ hidx)).trans
      (Ideal.pow_le_pow_right hv)

private theorem intersection_eq_normEuler {H t : ℕ} (htH : t ≤ H) :
    idealIntersection K t = normEuler K H t := by
  apply le_antisymm
  · rw [normEuler_eq_inf]
    apply Finset.le_inf
    intro a ha
    obtain ⟨hp, hP⟩ := Finset.mem_sigma.mp ha
    have h := above_properties K (Nat.mem_primesLE.mp hp).2 hP
    exact intersection_le_prime_power K t ⟨a.2, h.1, h.2.1⟩
  · apply le_iInf
    intro I
    apply le_iInf
    intro hI
    exact normEuler_le_ideal K htH I hI.1 hI.2

private theorem count_prod {α : Type*} (s : Finset α) (f : α → Ideal (𝓞 K))
    (hf : ∀ a ∈ s, f a ≠ ⊥) (P : Ideal (𝓞 K)) :
    (normalizedFactors (∏ a ∈ s, f a)).count P =
      ∑ a ∈ s, (normalizedFactors (f a)).count P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [← Ideal.one_eq_top]
  | @insert a s ha ih =>
    have hs : ∀ b ∈ s, f b ≠ ⊥ := fun b hb => hf b (Finset.mem_insert_of_mem hb)
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      normalizedFactors_mul (hf a (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr hs), Multiset.count_add, ih hs]

private theorem normEuler_count {H t : ℕ} (htH : t ≤ H)
    (P : HeightOneSpectrum (𝓞 K)) :
    (normalizedFactors (normEuler K H t)).count P.asIdeal = Nat.log P.asIdeal.absNorm t := by
  classical
  unfold normEuler
  rw [count_prod K _ _ (fun a ha => by
    obtain ⟨hp, hP⟩ := Finset.mem_sigma.mp ha
    exact pow_ne_zero _ (above_properties K (Nat.mem_primesLE.mp hp).2 hP).2.1)]
  have hterm (a : Σ _ : ℕ, Ideal (𝓞 K)) (ha : a ∈ primeIndices K H) :
      (normalizedFactors (a.2 ^ Nat.log a.2.absNorm t)).count P.asIdeal =
        if a.2 = P.asIdeal then Nat.log P.asIdeal.absNorm t else 0 := by
    obtain ⟨hp, hP⟩ := Finset.mem_sigma.mp ha
    have h := above_properties K (Nat.mem_primesLE.mp hp).2 hP
    rw [normalizedFactors_of_irreducible_pow (Ideal.prime_of_isPrime h.2.1 h.1).irreducible,
      normalize_eq]
    by_cases heq : a.2 = P.asIdeal
    · simp [heq]
    · rw [if_neg heq, Multiset.count_replicate]
      simp [heq, Ne.symm heq]
  rw [Finset.sum_congr rfl hterm]
  let a : Σ _ : ℕ, Ideal (𝓞 K) := ⟨(P.asIdeal.under ℤ).absNorm, P.asIdeal⟩
  obtain ⟨hp, hP, hpNorm⟩ := above_base K P
  by_cases ha : a ∈ primeIndices K H
  · rw [Finset.sum_eq_single a]
    · simp [a]
    · intro b hb hba
      have hbP : b.2 ≠ P.asIdeal := by
        intro heq
        exact hba (primeIndices_injective K hb ha heq)
      simp [hbP]
    · exact fun hn => (hn ha).elim
  · have hHp : H < (P.asIdeal.under ℤ).absNorm := by
      by_contra hn
      apply ha
      dsimp [a]
      exact Finset.mem_sigma.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.le_of_not_gt hn, hp⟩, hP⟩
    have hz : Nat.log P.asIdeal.absNorm t = 0 :=
      Nat.log_of_lt ((htH.trans_lt hHp).trans_le hpNorm)
    simp [hz]

private theorem log_floor_sum {q H M : ℕ} (hq : 1 < q) :
    (∑ k ∈ Ioc M H, Nat.log q (H / k)) =
      ∑ j ∈ range (H + 1), floorMinimum H M (q ^ (j + 1)) := by
  classical
  have hpowers {k j : ℕ} (hk : 0 < k) :
      q ^ (j + 1) ≤ H / k ↔ k ≤ H / q ^ (j + 1) := by
    rw [Nat.le_div_iff_mul_le hk,
      Nat.le_div_iff_mul_le (pow_pos (by omega : 0 < q) _), mul_comm]
  have hlog (k : ℕ) (hk : k ∈ Ioc M H) :
      Nat.log q (H / k) = ∑ j ∈ range (H + 1),
        if k ≤ H / q ^ (j + 1) then 1 else 0 := by
    obtain ⟨hkM, hkH⟩ := Finset.mem_Ioc.mp hk
    have hkpos : 0 < k := by omega
    have hn : H / k ≠ 0 := (Nat.div_pos hkH hkpos).ne'
    have hfilt : (range (H + 1)).filter (fun j => k ≤ H / q ^ (j + 1)) =
        range (Nat.log q (H / k)) := by
      ext j
      rw [Finset.mem_filter, Finset.mem_range, Finset.mem_range, ← hpowers hkpos,
        ← Nat.le_log_iff_pow_le hq hn]
      have hbound := (Nat.log_le_self q (H / k)).trans (Nat.div_le_self H k)
      omega
    rw [← Finset.sum_filter, hfilt]
    simp
  calc
    _ = ∑ k ∈ Ioc M H, ∑ j ∈ range (H + 1),
        if k ≤ H / q ^ (j + 1) then 1 else 0 := Finset.sum_congr rfl hlog
    _ = ∑ j ∈ range (H + 1), ∑ k ∈ Ioc M H,
        if k ≤ H / q ^ (j + 1) then 1 else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      have hfilt : (Ioc M H).filter (fun k => k ≤ H / q ^ (j + 1)) =
          Ioc M (H / q ^ (j + 1)) := by
        ext k
        rw [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ioc]
        have := Nat.div_le_self H (q ^ (j + 1))
        omega
      rw [← Finset.sum_filter, hfilt]
      simp [floorMinimum]

private theorem residue_tail_reindex {p f H M : ℕ} (hp : p.Prime) (hf : 0 < f) :
    (∑ j ∈ range (H + 1), floorMinimum H M ((p ^ f) ^ (j + 1))) =
      ∑ j ∈ range (H + 1),
        if f ∣ j + 1 then floorMinimum H M (p ^ (j + 1)) else 0 := by
  classical
  apply Finset.sum_bij_ne_zero (fun j _ _ => f * (j + 1) - 1)
  · intro j hj hnonzero
    have hpos : 0 < f * (j + 1) := Nat.mul_pos hf (by omega)
    have hdenom : p ^ (f * (j + 1)) ≤ H := by
      by_contra hn
      apply hnonzero
      rw [← pow_mul]
      simp [floorMinimum, Nat.div_eq_of_lt (lt_of_not_ge hn)]
    have hpower : f * (j + 1) < p ^ (f * (j + 1)) := Nat.lt_pow_self hp.one_lt
    apply Finset.mem_range.mpr
    omega
  · intro j hj hjnz k hk hknz heq
    have hjpos : 0 < f * (j + 1) := Nat.mul_pos hf (by omega)
    have hkpos : 0 < f * (k + 1) := Nat.mul_pos hf (by omega)
    have hm : f * (j + 1) = f * (k + 1) := by omega
    have hh := Nat.mul_left_cancel hf hm
    omega
  · intro k hk hnonzero
    have hdiv : f ∣ k + 1 := by
      by_contra hn
      simp [hn] at hnonzero
    have hmul : f * ((k + 1) / f) = k + 1 := Nat.mul_div_cancel' hdiv
    have hqpos : 0 < (k + 1) / f := by nlinarith
    let j := (k + 1) / f - 1
    have hj : j ∈ range (H + 1) := by
      have hkbound := Finset.mem_range.mp hk
      have hqle := Nat.div_le_self (k + 1) f
      apply Finset.mem_range.mpr
      dsimp [j]
      omega
    have he : f * (j + 1) = k + 1 := by
      dsimp [j]
      rw [Nat.sub_add_cancel hqpos]
      exact hmul
    refine ⟨j, hj, ?_, ?_⟩
    · rw [← pow_mul, he]
      simpa only [if_pos hdiv] using hnonzero
    · omega
  · intro j hj hnonzero
    have hpos : 0 < f * (j + 1) := Nat.mul_pos hf (by omega)
    rw [Nat.sub_add_cancel hpos, if_pos (dvd_mul_right f (j + 1)), ← pow_mul]

private theorem tail_norm (H M : ℕ) :
    (idealTail K H M).absNorm = weightedTail H M (normWeight K) := by
  classical
  have htail : idealTail K H M = ∏ a ∈ primeIndices K H,
      a.2 ^ (∑ k ∈ Ioc M H, Nat.log a.2.absNorm (H / k)) := by
    unfold idealTail
    simp_rw [intersection_eq_normEuler K (Nat.div_le_self H _), normEuler]
    rw [Finset.prod_comm]
    exact Finset.prod_congr rfl fun a _ => (Finset.prod_pow_eq_pow_sum _ _ _)
  rw [htail]
  unfold primeIndices
  rw [Finset.prod_sigma, map_prod]
  unfold weightedTail normWeight
  apply Finset.prod_congr rfl
  intro p hp
  have hpprime := (Nat.mem_primesLE.mp hp).2
  rw [map_prod]
  calc
    _ = ∏ P ∈ primesAbove K p,
        p ^ (P.inertiaDeg ℤ * (∑ j ∈ range (H + 1),
          if P.inertiaDeg ℤ ∣ j + 1 then floorMinimum H M (p ^ (j + 1)) else 0)) := by
      apply Finset.prod_congr rfl
      intro P hP
      have h := above_properties K hpprime hP
      letI : P.IsPrime := h.1
      letI : P.LiesOver (rationalPrimeIdeal p) := ⟨h.2.2.1.symm⟩
      letI : P.LiesOver (Ideal.span {(p : ℤ)}) := by
        simpa only [rationalPrimeIdeal] using
          (show P.LiesOver (rationalPrimeIdeal p) from inferInstance)
      have hNP : 1 < P.absNorm := prime_norm_gt_one K ⟨P, h.1, h.2.1⟩
      rw [map_pow, log_floor_sum hNP, h.2.2.2, pow_mul,
        residue_tail_reindex hpprime (P.inertiaDeg_pos ℤ)]
    _ = p ^ (∑ P ∈ primesAbove K p, P.inertiaDeg ℤ *
        (∑ j ∈ range (H + 1),
          if P.inertiaDeg ℤ ∣ j + 1 then floorMinimum H M (p ^ (j + 1)) else 0)) :=
      Finset.prod_pow_eq_pow_sum _ _ _
    _ = _ := by
      congr 1
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro P _
      split_ifs <;> simp

/-- Actual bounded-norm ideal intersections have logarithmic prime-ideal
exponents, and their tail product has exactly the residue-weighted norm. -/
public theorem ideal_intersection_tail (H M : ℕ) :
    (∀ t : ℕ,
      {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ I.absNorm ≤ t}.Finite ∧
      idealIntersection K t ≠ ⊥ ∧
      (∀ P : HeightOneSpectrum (𝓞 K),
        (normalizedFactors (idealIntersection K t)).count P.asIdeal =
          Nat.log P.asIdeal.absNorm t)) ∧
    idealIntersection K 0 = ⊤ ∧
    (idealTail K H M).absNorm = weightedTail H M (normWeight K) := by
  classical
  refine ⟨?_, ?_, tail_norm K H M⟩
  · intro t
    refine ⟨(Ideal.finite_setOfPred_absNorm_le t).subset (fun I hI => hI.2), ?_, ?_⟩
    · rw [intersection_eq_normEuler K (Nat.le_refl t)]
      exact normEuler_ne_bot K t t
    · intro P
      rw [intersection_eq_normEuler K (Nat.le_refl t)]
      exact normEuler_count K (Nat.le_refl t) P
  · apply le_antisymm le_top
    apply le_iInf
    intro I
    apply le_iInf
    intro hI
    have hz : I.absNorm = 0 := Nat.eq_zero_of_le_zero hI.2
    exact (hI.1 (Ideal.absNorm_eq_zero_iff.mp hz)).elim

end D5.S3.Arith.FactorialRatio.Weighted.IdealTail
