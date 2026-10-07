/- GID: D5/S3/Arith/Covering/PrimeCutOwnerCapacity
   generality: G
   mirror-B: D5/B/S3/Arith/Covering/PrimeCutOwnerCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fresh ternary prime fans bound selected owners in globally minimal odd covers. -/

import D5.S3.Arith.Congruence.ConditionalComparison.ArithmeticCoordinates
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Sum
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos7.OddDistinctCoveringSystem

open scoped BigOperators

variable {L : ℕ}

/-- One pure next-level class and one tagged class for every prime on each side. -/
def ternaryPrimeFanModulus (h : ℕ) (S T : Finset ℕ) : Unit ⊕ S ⊕ T → ℕ :=
  Sum.elim (fun _ => 3 ^ (h + 1))
    (Sum.elim (fun p => 3 ^ (h + 1) * p.val) (fun p => 3 ^ (h + 1) * p.val))

/-- A single fan simultaneously encloses every pair of matching tag roots. -/
theorem ternary_prime_fan_covers
    (h u : ℕ) (S T : Finset ℕ) (phase : ℕ → ℕ)
    (hS : ∀ p : S, Nat.Coprime (3 ^ (h + 1)) p.val)
    (hT : ∀ p : T, Nat.Coprime (3 ^ (h + 1)) p.val) :
    ∃ a : Unit ⊕ S ⊕ T → ℕ, ∀ (x : ℕ) (p : S) (t : T),
      x ≡ u [MOD 3 ^ h] → x ≡ phase p.val [MOD p.val] →
      x ≡ phase t.val [MOD t.val] →
      ∃ j, x ≡ a j [MOD ternaryPrimeFanModulus h S T j] := by
  let D := 3 ^ h
  let N := 3 ^ (h + 1)
  let a : Unit ⊕ S ⊕ T → ℕ := Sum.elim (fun _ => u % D)
    (Sum.elim
      (fun p => (Nat.chineseRemainder (hS p) (u % D + D) (phase p.val)).val)
      (fun p => (Nat.chineseRemainder (hT p) (u % D + D * 2) (phase p.val)).val))
  refine ⟨a, ?_⟩
  intro x p t hxD hxL hxR
  let digit : Fin 3 := ⟨x / D % 3, Nat.mod_lt _ (by decide)⟩
  have heq : x % N = u % D + D * digit.val := by
    dsimp only [N, digit]
    rw [Nat.mod_pow_succ]
    change x % D + D * (x / D % 3) = u % D + D * (x / D % 3)
    rw [show x % D = u % D from hxD]
  have hbranch : x ≡ u % D + D * digit.val [MOD N] := by
    change x % N = (u % D + D * digit.val) % N
    rw [← heq, Nat.mod_mod]
  have hdigit : digit.val = 0 ∨ digit.val = 1 ∨ digit.val = 2 := by
    have := digit.isLt
    omega
  rcases hdigit with hdigit | hdigit | hdigit
  · exact ⟨Sum.inl (), by simpa [ternaryPrimeFanModulus, a, hdigit] using hbranch⟩
  · refine ⟨Sum.inr (Sum.inl p), ?_⟩
    have hb : x ≡ u % D + D [MOD N] := by simpa [hdigit] using hbranch
    exact Nat.chineseRemainder_modEq_unique (hS p) hb hxL
  · refine ⟨Sum.inr (Sum.inr t), ?_⟩
    have hb : x ≡ u % D + D * 2 [MOD N] := by simpa [hdigit] using hbranch
    exact Nat.chineseRemainder_modEq_unique (hT t) hb hxR

/-- A fresh replacement of no larger cardinality and smaller cost contradicts
global cardinality-then-modulus-sum minimality. -/
theorem fresh_finite_replacement_descent
    (F : OddDistinctCoveringSystem L)
    (hcountMin : ∀ {n : ℕ}, OddDistinctCoveringSystem n → L ≤ n)
    (hsumMin : ∀ H : OddDistinctCoveringSystem L,
      (∑ i, F.modulus i) ≤ ∑ i, H.modulus i)
    {I J : Type*} [Fintype I] [Fintype J]
    (slot : I ↪ Fin L) (m a : J → ℕ)
    (hm : ∀ j, 1 < m j) (ho : ∀ j, Odd (m j))
    (hinj : Function.Injective m)
    (hfresh : ∀ j i, m j ≠ F.modulus i)
    (hcover : ∀ x i, x ≡ F.residue (slot i) [MOD F.modulus (slot i)] →
      ∃ j, x ≡ a j [MOD m j])
    (hsize : Fintype.card J ≤ Fintype.card I)
    (hcost : (∑ j, m j) < ∑ i, F.modulus (slot i)) : False := by
  classical
  let Rem := {i : Fin L // i ∉ Set.range (slot : I → Fin L)}
  let eOld : I ⊕ Rem ≃ Fin L :=
    (Equiv.sumCongr (Equiv.ofInjective slot slot.injective) (Equiv.refl Rem)).trans
      (Equiv.sumCompl (fun i => i ∈ Set.range (slot : I → Fin L)))
  let newMod : J ⊕ Rem → ℕ := Sum.elim m (fun i => F.modulus i.val)
  let newRes : J ⊕ Rem → ℕ := Sum.elim a (fun i => F.residue i.val)
  have hnewInj : Function.Injective newMod := by
    rintro (j | i) (k | l) heq
    · exact congrArg Sum.inl (hinj heq)
    · exact False.elim (hfresh j l.val heq)
    · exact False.elim (hfresh k i.val heq.symm)
    · exact congrArg Sum.inr (Subtype.ext (F.modulus_injective heq))
  let makeCover (n : ℕ) (e : J ⊕ Rem ≃ Fin n) : OddDistinctCoveringSystem n :=
    { modulus := fun i => newMod (e.symm i)
      residue := fun i => newRes (e.symm i)
      covers := by
        intro x
        obtain ⟨i, hxi⟩ := F.covers x
        by_cases hi : i ∈ Set.range (slot : I → Fin L)
        · obtain ⟨j, rfl⟩ := hi
          obtain ⟨k, hk⟩ := hcover x j hxi
          exact ⟨e (Sum.inl k), by simpa [newMod, newRes] using hk⟩
        · exact ⟨e (Sum.inr ⟨i, hi⟩), by simpa [newMod, newRes] using hxi⟩
      modulus_one_lt := by
        intro i
        cases e.symm i with
        | inl j => exact hm j
        | inr j => exact F.modulus_one_lt j.val
      modulus_odd := by
        intro i
        cases e.symm i with
        | inl j => exact ho j
        | inr j => exact F.modulus_odd j.val
      modulus_injective := hnewInj.comp e.symm.injective }
  have holdCard : Fintype.card I + Fintype.card Rem = L := by
    simpa using Fintype.card_congr eOld
  have hnewCard : Fintype.card (J ⊕ Rem) = L := by
    have hmin := hcountMin (makeCover _ (Fintype.equivFin _))
    simp only [Fintype.card_sum] at hmin ⊢
    omega
  let e : J ⊕ Rem ≃ Fin L :=
    (Fintype.equivFin _).trans (finCongr hnewCard)
  let H := makeCover L e
  have htotal : (∑ j, newMod j) < ∑ i, F.modulus i := by
    rw [← eOld.sum_comp F.modulus, Fintype.sum_sum_type, Fintype.sum_sum_type]
    exact Nat.add_lt_add_right hcost (∑ i : Rem, F.modulus i.val)
  have hsum : (∑ i, H.modulus i) = ∑ j, newMod j := e.symm.sum_comp newMod
  have hmin := hsumMin H
  rw [hsum] at hmin
  exact (Nat.not_lt_of_ge hmin) htotal

/-- Matching distinct prime tags on disjoint sides cost at least one used tag
per selected original in a globally minimal cover. -/
theorem selected_prime_cut_card_le
    (F : OddDistinctCoveringSystem L)
    (hcountMin : ∀ {n : ℕ}, OddDistinctCoveringSystem n → L ≤ n)
    (hsumMin : ∀ H : OddDistinctCoveringSystem L,
      (∑ i, F.modulus i) ≤ ∑ i, H.modulus i)
    (h q u : ℕ) (hq : 7 ≤ q)
    (hnoNext : ∀ i, ¬ 3 ^ (h + 1) ∣ F.modulus i)
    {I : Type*} [Fintype I] (slot : I ↪ Fin L)
    (cofactor left right : I → ℕ) (phase : ℕ → ℕ)
    (hlabel : ∀ i, F.modulus (slot i) = 3 ^ h * q * cofactor i)
    (hword : ∀ i, F.residue (slot i) ≡ u [MOD 3 ^ h])
    (hleftPrime : ∀ i, Nat.Prime (left i))
    (hrightPrime : ∀ i, Nat.Prime (right i))
    (hleftDiv : ∀ i, left i ∣ cofactor i)
    (hrightDiv : ∀ i, right i ∣ cofactor i)
    (hleftPhase : ∀ i, F.residue (slot i) ≡ phase (left i) [MOD left i])
    (hrightPhase : ∀ i, F.residue (slot i) ≡ phase (right i) [MOD right i])
    (hdisjoint : Disjoint (Finset.univ.image left) (Finset.univ.image right)) :
    Fintype.card I ≤ (Finset.univ.image left).card + (Finset.univ.image right).card := by
  classical
  by_contra hcard
  let S := Finset.univ.image left
  let T := Finset.univ.image right
  let D := 3 ^ h
  let N := 3 ^ (h + 1)
  have hDpos : 0 < D := pow_pos (by decide) h
  have hNpos : 0 < N := pow_pos (by decide) (h + 1)
  have hN : N = 3 * D := by simp [N, D, pow_succ, Nat.mul_comm]
  have hNodd : Odd N := (by decide : Odd 3).pow
  have hcofpos (i : I) : 0 < cofactor i := by
    have hm := F.modulus_one_lt (slot i)
    rw [hlabel i] at hm
    by_contra hc
    have : cofactor i = 0 := by omega
    simp [this] at hm
  have hcofdvd (i : I) : cofactor i ∣ F.modulus (slot i) := by
    rw [hlabel i]
    exact dvd_mul_left _ _
  have hcofThree (i : I) : ¬ 3 ∣ cofactor i := by
    rintro ⟨k, hk⟩
    apply hnoNext (slot i)
    rw [hlabel i, hk, pow_succ]
    exact ⟨q * k, by ring⟩
  have hleftOdd (i : I) : Odd (left i) :=
    (F.modulus_odd (slot i)).of_dvd_nat ((hleftDiv i).trans (hcofdvd i))
  have hrightOdd (i : I) : Odd (right i) :=
    (F.modulus_odd (slot i)).of_dvd_nat ((hrightDiv i).trans (hcofdvd i))
  have hS (p : S) : 1 < p.val ∧ Odd p.val ∧ Nat.Coprime N p.val := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp p.property
    rw [← hi]
    refine ⟨(hleftPrime i).one_lt, hleftOdd i, ?_⟩
    have hc : Nat.Coprime 3 (left i) := by
      apply Nat.Coprime.symm
      apply (hleftPrime i).coprime_iff_not_dvd.mpr
      intro hd
      rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with he | he
      · exact (hleftPrime i).ne_one he
      · exact hcofThree i (he ▸ hleftDiv i)
    exact hc.pow_left (h + 1)
  have hT (p : T) : 1 < p.val ∧ Odd p.val ∧ Nat.Coprime N p.val := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp p.property
    rw [← hi]
    refine ⟨(hrightPrime i).one_lt, hrightOdd i, ?_⟩
    have hc : Nat.Coprime 3 (right i) := by
      apply Nat.Coprime.symm
      apply (hrightPrime i).coprime_iff_not_dvd.mpr
      intro hd
      rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with he | he
      · exact (hrightPrime i).ne_one he
      · exact hcofThree i (he ▸ hrightDiv i)
    exact hc.pow_left (h + 1)
  let K := Unit ⊕ S ⊕ T
  let m : K → ℕ := ternaryPrimeFanModulus h S T
  obtain ⟨a, ha⟩ := ternary_prime_fan_covers h u S T phase
    (fun p => (hS p).2.2) (fun p => (hT p).2.2)
  have hm : ∀ j, 1 < m j := by
    rintro (j | (p | p))
    · change 1 < N
      omega
    · change 1 < N * p.val
      have := (hS p).1
      nlinarith
    · change 1 < N * p.val
      have := (hT p).1
      nlinarith
  have ho : ∀ j, Odd (m j) := by
    rintro (j | (p | p))
    · exact hNodd
    · exact hNodd.mul (hS p).2.1
    · exact hNodd.mul (hT p).2.1
  have hsep (p : S) (t : T) : p.val ≠ t.val := by
    intro heq
    exact Finset.disjoint_left.mp hdisjoint p.property (heq ▸ t.property)
  have hinj : Function.Injective m := by
    rintro (j | (p | p)) (k | (t | t)) heq
    · exact congrArg Sum.inl (Subsingleton.elim j k)
    · change N = N * t.val at heq
      have := (hS t).1
      exfalso
      nlinarith
    · change N = N * t.val at heq
      have := (hT t).1
      exfalso
      nlinarith
    · change N * p.val = N at heq
      have := (hS p).1
      exfalso
      nlinarith
    · change N * p.val = N * t.val at heq
      exact congrArg (Sum.inr ∘ Sum.inl) (Subtype.ext (by nlinarith : p.val = t.val))
    · change N * p.val = N * t.val at heq
      exact False.elim (hsep p t (by nlinarith))
    · change N * p.val = N at heq
      have := (hT p).1
      exfalso
      nlinarith
    · change N * p.val = N * t.val at heq
      exact False.elim (hsep t p (by nlinarith))
    · change N * p.val = N * t.val at heq
      exact congrArg (Sum.inr ∘ Sum.inr) (Subtype.ext (by nlinarith : p.val = t.val))
  have hfresh : ∀ j i, m j ≠ F.modulus i := by
    intro j i heq
    apply hnoNext i
    rw [← heq]
    change N ∣ m j
    rcases j with j | (p | p)
    · exact dvd_refl N
    · exact dvd_mul_right N p.val
    · exact dvd_mul_right N p.val
  have hcover : ∀ x i, x ≡ F.residue (slot i) [MOD F.modulus (slot i)] →
      ∃ j, x ≡ a j [MOD m j] := by
    intro x i hx
    have hDdvd : D ∣ F.modulus (slot i) := by
      refine ⟨q * cofactor i, ?_⟩
      rw [hlabel i]
      simp [D, Nat.mul_assoc]
    have hxD : x ≡ u [MOD D] := (hx.of_dvd hDdvd).trans (hword i)
    have hxL : x ≡ phase (left i) [MOD left i] :=
      (hx.of_dvd ((hleftDiv i).trans (hcofdvd i))).trans (hleftPhase i)
    have hxR : x ≡ phase (right i) [MOD right i] :=
      (hx.of_dvd ((hrightDiv i).trans (hcofdvd i))).trans (hrightPhase i)
    exact ha x ⟨left i, Finset.mem_image_of_mem left (Finset.mem_univ i)⟩
      ⟨right i, Finset.mem_image_of_mem right (Finset.mem_univ i)⟩ hxD hxL hxR
  have hsize : Fintype.card K ≤ Fintype.card I := by
    simp only [K, Fintype.card_sum, Fintype.card_unit, Fintype.card_coe]
    dsimp only [S, T]
    omega
  have hpair (i : I) : left i + right i ≤ cofactor i := by
    have hne : left i ≠ right i := by
      intro heq
      exact Finset.disjoint_left.mp hdisjoint
        (Finset.mem_image_of_mem left (Finset.mem_univ i))
        (heq ▸ Finset.mem_image_of_mem right (Finset.mem_univ i))
    have hc : Nat.Coprime (left i) (right i) := by
      apply (hleftPrime i).coprime_iff_not_dvd.mpr
      intro hd
      rcases (Nat.dvd_prime (hrightPrime i)).mp hd with he | he
      · exact (hleftPrime i).ne_one he
      · exact hne he
    have hmul : left i * right i ≤ cofactor i :=
      Nat.le_of_dvd (hcofpos i) (hc.mul_dvd_of_dvd_of_dvd (hleftDiv i) (hrightDiv i))
    have hl := (hleftPrime i).two_le
    have hr := (hrightPrime i).two_le
    nlinarith [Nat.zero_le ((left i - 2) * (right i - 2))]
  have hleftSum : (∑ p ∈ S, p) ≤ ∑ i, left i := by
    exact Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)
  have hrightSum : (∑ p ∈ T, p) ≤ ∑ i, right i := by
    exact Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)
  have htagSum : (∑ p ∈ S, p) + (∑ p ∈ T, p) ≤ ∑ i, cofactor i := by
    calc
      _ ≤ (∑ i, left i) + ∑ i, right i := Nat.add_le_add hleftSum hrightSum
      _ = ∑ i, (left i + right i) := (Finset.sum_add_distrib).symm
      _ ≤ ∑ i, cofactor i := Finset.sum_le_sum fun i _ => hpair i
  have hIpos : 0 < Fintype.card I := by omega
  have : Nonempty I := Fintype.card_pos_iff.mp hIpos
  have hMpos : 0 < ∑ i, cofactor i := by
    exact Finset.sum_pos (fun i _ => hcofpos i) Finset.univ_nonempty
  have hsumNew : (∑ j, m j) = N * (1 + (∑ p ∈ S, p) + ∑ p ∈ T, p) := by
    simp only [K, m, ternaryPrimeFanModulus, Fintype.sum_sum_type, Fintype.sum_unique,
      Sum.elim_inl, Sum.elim_inr, Finset.sum_coe_sort]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    ring
  have hsumOld : (∑ i, F.modulus (slot i)) = D * q * ∑ i, cofactor i := by
    simp_rw [hlabel]
    rw [Finset.mul_sum]
  have hcost : (∑ j, m j) < ∑ i, F.modulus (slot i) := by
    rw [hsumNew, hsumOld, hN]
    have hb : 3 * (1 + (∑ p ∈ S, p) + ∑ p ∈ T, p) < q * ∑ i, cofactor i := by
      nlinarith
    have := Nat.mul_lt_mul_of_pos_left hb hDpos
    nlinarith
  exact fresh_finite_replacement_descent F hcountMin hsumMin slot m a
    hm ho hinj hfresh hcover hsize hcost

end Erdos7.OddDistinctCoveringSystem
