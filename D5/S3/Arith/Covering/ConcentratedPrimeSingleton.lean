/- GID: D5/S3/Arith/Covering/ConcentratedPrimeSingleton
   generality: G
   mirror-B: D5/B/S3/Arith/Covering/ConcentratedPrimeSingleton
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Private-prime concentration forces a singleton in a count-and-sum minimal odd cover. -/

import D5.S3.Arith.Congruence.ConditionalComparison.ArithmeticCoordinates
import D5.S3.Arith.Congruence.ConditionalComparison.PrefixLiability
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos7.OddDistinctCoveringSystem

open scoped BigOperators

variable {L : ℕ}

private theorem deleting_owner_contradicts_count_minimality
    (F : OddDistinctCoveringSystem L)
    (hcountMin : ∀ {N : ℕ}, OddDistinctCoveringSystem N → L ≤ N)
    (r : Fin L)
    (hcover : ∀ x : ℕ, ∃ i : Fin L,
      i ≠ r ∧ x ≡ F.residue i [MOD F.modulus i]) : False := by
  classical
  let I := {i : Fin L // i ≠ r}
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let F' : OddDistinctCoveringSystem (Fintype.card I) :=
    { residue := fun j => F.residue (e.symm j).val
      modulus := fun j => F.modulus (e.symm j).val
      covers := by
        intro x
        obtain ⟨i, hi, hxi⟩ := hcover x
        refine ⟨e ⟨i, hi⟩, ?_⟩
        simpa only [Equiv.symm_apply_apply] using hxi
      modulus_one_lt := fun j => F.modulus_one_lt (e.symm j).val
      modulus_odd := fun j => F.modulus_odd (e.symm j).val
      modulus_injective := by
        intro i j hij
        apply e.symm.injective
        apply Subtype.ext
        exact F.modulus_injective hij }
  have hbound : L ≤ Fintype.card I := hcountMin F'
  have hstrict : Fintype.card I < L := by
    simpa only [I, Fintype.card_fin] using
      (Fintype.card_subtype_lt (p := fun i : Fin L => i ≠ r) (x := r)
        (by simp))
  exact (Nat.not_lt_of_ge hbound) hstrict

private theorem owner_has_private_point
    (F : OddDistinctCoveringSystem L)
    (hcountMin : ∀ {N : ℕ}, OddDistinctCoveringSystem N → L ≤ N)
    (r : Fin L) :
    ∃ x : ℕ, x ≡ F.residue r [MOD F.modulus r] ∧
      ∀ i : Fin L, i ≠ r → ¬x ≡ F.residue i [MOD F.modulus i] := by
  classical
  by_contra hprivate
  apply deleting_owner_contradicts_count_minimality F hcountMin r
  intro x
  by_cases hxr : x ≡ F.residue r [MOD F.modulus r]
  · by_contra hother
    apply hprivate
    exact ⟨x, hxr, fun i hi hxi => hother ⟨i, hi, hxi⟩⟩
  · obtain ⟨i, hxi⟩ := F.covers x
    refine ⟨i, ?_, hxi⟩
    intro hi
    subst i
    exact hxr hxi

/-- A point of one congruence class that belongs to no other original class. -/
def Private (F : OddDistinctCoveringSystem L) (i : Fin L) (x : ℕ) : Prop :=
  x ≡ F.residue i [MOD F.modulus i] ∧
    ∀ j, j ≠ i → ¬x ≡ F.residue j [MOD F.modulus j]

/-- In a cover minimizing first cardinality and then modulus sum, concentration
of a pure prime class's private points modulo three forces an actual modulus-3p
class whose residue modulo p occurs in no other p-bearing original class. -/
theorem concentrated_pure_prime_supplies_three_prime_singleton
    (F : OddDistinctCoveringSystem L)
    (hcountMin : ∀ {N : ℕ}, OddDistinctCoveringSystem N → L ≤ N)
    (hsumMin : ∀ H : OddDistinctCoveringSystem L,
      (∑ i, F.modulus i) ≤ ∑ i, H.modulus i)
    (p : ℕ) (hp : Nat.Prime p) (hp3 : 3 < p)
    (g : Fin L) (hg : F.modulus g = p)
    (a : ℕ) (hconc : ∀ x, Private F g x → x ≡ a [MOD 3]) :
    ∃ j : Fin L, F.modulus j = 3 * p ∧ F.residue j ≡ a [MOD 3] ∧
      ∀ k : Fin L, p ∣ F.modulus k →
        F.residue k ≡ F.residue j [MOD p] → k = j := by
  classical
  have hpThree : p.Coprime 3 := hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt (by decide : 0 < (3 : ℕ)) hp3)
  let Q := 3 * F.commonModulus
  have hQzero : Q ≠ 0 := mul_ne_zero (by decide) F.commonModulus_ne_zero
  obtain ⟨G, R, hpRnot, hQ⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hQzero p hp.ne_one
  have hpR : p.Coprime R := hp.coprime_iff_not_dvd.mpr hpRnot
  have hperiod : ∀ i, F.modulus i ∣ p ^ G * R := by
    intro i
    rw [← hQ]
    exact (F.modulus_dvd_commonModulus i).trans (dvd_mul_left _ 3)
  have hThreeR : 3 ∣ R := by
    apply (hpThree.symm.pow_right G).dvd_of_dvd_mul_left
    rw [← hQ]
    exact dvd_mul_right _ _
  have hfreeR (i : Fin L) (hi : ¬p ∣ F.modulus i) : F.modulus i ∣ R :=
    ((hp.coprime_iff_not_dvd.mpr hi).symm.pow_right G).dvd_of_dvd_mul_left
      (hperiod i)
  have hnoContain : ∀ i,
      (p ^ (0 + 1) ∣ F.modulus i ∧ F.residue i ≡ F.residue g [MOD p ^ 0]) →
      i ≠ g → ∃ z : ℕ, z ≡ F.residue i [MOD F.modulus i] ∧
        ¬z ≡ F.residue g [MOD F.modulus g] := by
    intro i _ hig
    obtain ⟨z, hzi, hzPrivate⟩ := owner_has_private_point F hcountMin i
    exact ⟨z, hzi, hzPrivate g hig.symm⟩
  have hprefix := Erdos7.prefix_liability F.modulus F.residue hp hpR hperiod F.covers
    g (by simpa only [zero_add, pow_one] using hg) hnoContain
  have hholeThree (x : ℕ)
      (hx : ∀ i, ¬p ∣ F.modulus i → ¬x ≡ F.residue i [MOD F.modulus i]) :
      x ≡ a [MOD 3] := by
    have hhole : ∀ i, ¬(p ^ (0 + 1) ∣ F.modulus i ∧
        F.residue i ≡ F.residue g [MOD p ^ 0]) →
        ¬x ≡ F.residue i [MOD F.modulus i] := by
      intro i hi
      apply hx i
      intro hpi
      apply hi
      simpa only [zero_add, pow_one, pow_zero, Nat.modEq_one, and_true] using hpi
    obtain ⟨_, y, hyg, hyPrivate, hyx⟩ := (hprefix x).mp hhole
    exact (hyx.of_dvd hThreeR).symm.trans (hconc y ⟨hyg, hyPrivate⟩)
  have hprivateThree (i : Fin L) (hpi : p ∣ F.modulus i)
      (x : ℕ) (hx : Private F i x) : x ≡ a [MOD 3] := by
    apply hholeThree x
    intro k hpk
    apply hx.2 k
    intro hki
    subst k
    exact hpk hpi
  have hactual : ∃ j : Fin L, F.modulus j = 3 * p := by
    by_contra hmissing
    have hmissingAt (i : Fin L) : F.modulus i ≠ 3 * p :=
      fun hi => hmissing ⟨i, hi⟩
    obtain ⟨y, hyg, hyPrivate⟩ := owner_has_private_point F hcountMin g
    let c := if F.residue g % p = 0 then 1 else 0
    have hc : ¬c ≡ F.residue g [MOD p] := by
      change c % p ≠ F.residue g % p
      dsimp only [c]
      split_ifs with hz
      · rw [Nat.mod_eq_of_lt hp.one_lt, hz]
        decide
      · simpa only [Nat.zero_mod] using Ne.symm hz
    obtain ⟨x, hxc, hxy⟩ := Nat.chineseRemainder hpR c y
    obtain ⟨r, hxr⟩ := F.covers x
    have hrg : r ≠ g := by
      intro he
      subst r
      exact hc (hxc.symm.trans (by simpa only [hg] using hxr))
    have hpr : p ∣ F.modulus r := by
      by_contra hn
      exact hyPrivate r hrg ((hxy.of_dvd (hfreeR r hn)).symm.trans hxr)
    obtain ⟨m, hm⟩ := hpr
    have hmOdd : Odd m := (F.modulus_odd r).of_dvd_nat
      (by rw [hm]; exact dvd_mul_left m p)
    have hmOne : m ≠ 1 := by
      intro he
      exact hrg (F.modulus_injective (by simpa only [hm, he, mul_one] using hg.symm))
    obtain ⟨v, hv⟩ := hmOdd
    have hmThree : 3 ≤ m := by omega
    have hprice : 3 * p < F.modulus r := by
      have hle : 3 * p ≤ F.modulus r := by
        rw [hm, mul_comm p m]
        exact Nat.mul_le_mul_right p hmThree
      exact lt_of_le_of_ne hle (Ne.symm (hmissingAt r))
    obtain ⟨w, hwp, hwThree⟩ := Nat.chineseRemainder hpThree (F.residue r) a
    have hreplace (z : ℕ) (hz : Private F r z) : z ≡ w [MOD 3 * p] := by
      apply (Nat.modEq_and_modEq_iff_modEq_mul hpThree.symm).mp
      exact ⟨(hprivateThree r (by rw [hm]; exact dvd_mul_right p m) z hz).trans
        hwThree.symm, (hz.1.of_dvd (by rw [hm]; exact dvd_mul_right p m)).trans hwp.symm⟩
    let newMod : Fin L → ℕ := fun i => if i = r then 3 * p else F.modulus i
    let newRes : Fin L → ℕ := fun i => if i = r then w else F.residue i
    have hnewCover : ∀ z : ℕ, ∃ i : Fin L, z ≡ newRes i [MOD newMod i] := by
      intro z
      by_cases hpriv : Private F r z
      · exact ⟨r, by simpa only [newMod, newRes, if_pos rfl] using hreplace z hpriv⟩
      · have hother : ∃ i : Fin L, i ≠ r ∧ z ≡ F.residue i [MOD F.modulus i] := by
          by_contra hnone
          obtain ⟨i, hzi⟩ := F.covers z
          have hir : i = r := by
            by_contra hir
            exact hnone ⟨i, hir, hzi⟩
          apply hpriv
          refine ⟨by simpa only [hir] using hzi, ?_⟩
          intro k hkr hzk
          exact hnone ⟨k, hkr, hzk⟩
        obtain ⟨i, hir, hzi⟩ := hother
        exact ⟨i, by simpa only [newMod, newRes, if_neg hir] using hzi⟩
    have hnewInjective : Function.Injective newMod := by
      intro i j hij
      by_cases hi : i = r
      · subst i
        by_cases hj : j = r
        · exact hj.symm
        · exact False.elim (hmissingAt j
            (by simpa only [newMod, if_pos rfl, if_neg hj] using hij.symm))
      · by_cases hj : j = r
        · subst j
          exact False.elim (hmissingAt i
            (by simpa only [newMod, if_pos rfl, if_neg hi] using hij))
        · apply F.modulus_injective
          simpa only [newMod, if_neg hi, if_neg hj] using hij
    have hpOdd : Odd p := by simpa only [hg] using F.modulus_odd g
    let H : OddDistinctCoveringSystem L :=
      { residue := newRes
        modulus := newMod
        covers := hnewCover
        modulus_one_lt := by
          intro i
          by_cases hi : i = r
          · simp only [newMod, if_pos hi]
            omega
          · simpa only [newMod, if_neg hi] using F.modulus_one_lt i
        modulus_odd := by
          intro i
          by_cases hi : i = r
          · simpa only [newMod, if_pos hi] using (show Odd (3 : ℕ) by decide).mul hpOdd
          · simpa only [newMod, if_neg hi] using F.modulus_odd i
        modulus_injective := hnewInjective }
    have hcost : (∑ i, newMod i) < ∑ i, F.modulus i := by
      apply Finset.sum_lt_sum
      · intro i _
        by_cases hi : i = r
        · subst i
          simpa only [newMod, if_pos rfl] using hprice.le
        · simp only [newMod, if_neg hi, le_refl]
      · exact ⟨r, Finset.mem_univ r, by simpa only [newMod, if_pos rfl] using hprice⟩
    exact (Nat.not_lt_of_ge (hsumMin H)) hcost
  obtain ⟨j, hj⟩ := hactual
  have hpj : p ∣ F.modulus j := by rw [hj]; exact dvd_mul_left p 3
  have hjThree : F.residue j ≡ a [MOD 3] := by
    obtain ⟨z, hz, hzPrivate⟩ := owner_has_private_point F hcountMin j
    have hzThree : z ≡ F.residue j [MOD 3] :=
      hz.of_dvd (by rw [hj]; exact dvd_mul_right 3 p)
    exact hzThree.symm.trans (hprivateThree j hpj z ⟨hz, hzPrivate⟩)
  refine ⟨j, hj, hjThree, ?_⟩
  intro k hpk hkroot
  by_contra hkj
  obtain ⟨z, hz, hzPrivate⟩ := owner_has_private_point F hcountMin k
  apply hzPrivate j (Ne.symm hkj)
  rw [hj]
  apply (Nat.modEq_and_modEq_iff_modEq_mul hpThree.symm).mp
  exact ⟨(hprivateThree k hpk z ⟨hz, hzPrivate⟩).trans hjThree.symm,
    (hz.of_dvd hpk).trans hkroot⟩

end Erdos7.OddDistinctCoveringSystem
