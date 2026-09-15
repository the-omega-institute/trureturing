/- GID: D5/S3/Factorization/Combinatorics/StrictDivisorChainMobius
   generality: G
   mirror-B: D5/B/S3/Factorization/Combinatorics/StrictDivisorChainMobius
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The alternating number of strict divisor chains from one to a positive integer equals its Möbius value. -/

import D5.S3.Factorization.Combinatorics.StrictDivisorChainCount
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

set_option autoImplicit false

open scoped BigOperators
open D5.S3.Factorization.Combinatorics.StrictDivisorChainCount

namespace D5.S3.Factorization.Combinatorics.StrictDivisorChainMobius

/-- The alternating count of strict divisor chains, through the prime-factor rank of the endpoint. -/
noncomputable def chainSum (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (ArithmeticFunction.cardFactors n + 1),
    (-1 : ℤ) ^ k * (Nat.card (Chain n k) : ℤ)

set_option maxHeartbeats 800000 in
/-- The alternating count of strict divisor chains to a positive integer is its Möbius value. -/
theorem chain_alternating_sum_eq_moebius (n : ℕ) (hn : 1 ≤ n) :
    chainSum n = ArithmeticFunction.moebius n := by
  classical
  have rank_lt : ∀ a b : ℕ, 0 < a → a ∣ b → a < b →
      ArithmeticFunction.cardFactors a < ArithmeticFunction.cardFactors b := by
    intro a b ha hab hlt
    obtain ⟨c, rfl⟩ := hab
    have hc : 1 < c := by
      by_contra! hc
      have hle := Nat.mul_le_mul_left a hc
      simp only [mul_one] at hle
      omega
    rw [ArithmeticFunction.cardFactors_mul ha.ne' (by omega)]
    have := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hc
    omega
  have rank_support : ∀ n k : ℕ, ArithmeticFunction.cardFactors n < k →
      Nat.card (Chain n k) = 0 := by
    intro m k hk
    have : IsEmpty (Chain m k) := ⟨by
      intro c
      have hmono : Monotone c.val :=
        (Fin.strictMono_iff_lt_succ.mpr fun i => (c.prop.2.2 i).2).monotone
      have hpos : ∀ i, 0 < (c.val i).val := by
        intro i
        have h := hmono (Fin.zero_le i)
        have hz := c.prop.1
        change (c.val 0).val ≤ (c.val i).val at h
        omega
      have hbound : ∀ i : Fin (k + 1), i.val ≤
          ArithmeticFunction.cardFactors (c.val i).val := by
        intro i
        induction i using Fin.induction with
        | zero => exact Nat.zero_le _
        | succ i ih =>
          have h := rank_lt _ _ (hpos i.castSucc) (c.prop.2.2 i).1 (c.prop.2.2 i).2
          change i.val + 1 ≤ _
          exact Nat.succ_le_of_lt (lt_of_le_of_lt ih h)
      have h := hbound (Fin.last k)
      rw [c.prop.2.1] at h
      exact (Nat.not_le_of_lt hk) h⟩
    exact Nat.card_of_isEmpty
  have zero_count : ∀ n : ℕ, Nat.card (Chain n 0) = if n = 1 then 1 else 0 := by
    intro m
    by_cases hm : m = 1
    · subst m
      rw [if_pos rfl, Nat.card_eq_one_iff_unique]
      constructor
      · refine ⟨fun c d => ?_⟩
        apply Subtype.ext
        funext i
        have hi : i = 0 := Fin.ext (by omega)
        subst i
        exact Fin.ext (c.prop.1.trans d.prop.1.symm)
      · exact ⟨⟨fun _ => ⟨1, by omega⟩, rfl, rfl, fun i => Fin.elim0 i⟩⟩
    · rw [if_neg hm]
      have : IsEmpty (Chain m 0) := ⟨by
        intro c
        have hfirst := c.prop.1
        have hlast := c.prop.2.1
        have h : m = 1 := hlast.symm.trans hfirst
        exact hm h⟩
      exact Nat.card_of_isEmpty
  have last_step : ∀ m k : ℕ, 1 < m →
      Nat.card (Chain m (k + 1)) = ∑ d ∈ m.properDivisors, Nat.card (Chain d k) := by
    intro m k hm
    let S := Σ d : {d : ℕ // d ∈ m.properDivisors}, Chain d.val k
    let extend : S → Fin (k + 2) → Fin (m + 1) := fun s =>
      Fin.lastCases ⟨m, by omega⟩ (fun i => ⟨(s.2.val i).val, by
        have hi := (s.2.val i).is_lt
        have hd := (Nat.mem_properDivisors.mp s.1.prop).2
        omega⟩)
    have extend_first : ∀ s, (extend s 0).val = 1 := by
      intro s
      change (extend s (Fin.castSucc (0 : Fin (k + 1)))).val = 1
      simpa only [extend, Fin.lastCases_castSucc] using s.2.prop.1
    have extend_last : ∀ s, (extend s (Fin.last (k + 1))).val = m := by
      intro s
      simp only [extend, Fin.lastCases_last]
    have extend_step : ∀ s (i : Fin (k + 1)),
        (extend s i.castSucc).val ∣ (extend s i.succ).val ∧
          extend s i.castSucc < extend s i.succ := by
      intro s i
      induction i using Fin.lastCases with
      | last =>
        simpa only [extend, Fin.lastCases_castSucc, Fin.succ_last, Fin.lastCases_last,
          s.2.prop.2.1, Fin.lt_def] using Nat.mem_properDivisors.mp s.1.prop
      | cast i =>
        simpa only [extend, Fin.succ_castSucc, Fin.lastCases_castSucc, Fin.lt_def]
          using s.2.prop.2.2 i
    let append : S → Chain m (k + 1) := fun s =>
      ⟨extend s, extend_first s, extend_last s, extend_step s⟩
    have hinj : Function.Injective append := by
      rintro ⟨⟨d, hd⟩, c⟩ ⟨⟨e, he⟩, b⟩ h
      have hval := congrArg (fun x : Chain m (k + 1) =>
        (x.val (Fin.castSucc (Fin.last k))).val) h
      have hde : d = e := by
        simpa only [append, extend, Fin.lastCases_castSucc, c.prop.2.1, b.prop.2.1] using hval
      subst e
      have hcb : c = b := by
        apply Subtype.ext
        funext i
        apply Fin.ext
        have hi := congrArg (fun x : Chain m (k + 1) => (x.val i.castSucc).val) h
        simpa only [append, extend, Fin.lastCases_castSucc] using hi
      subst b
      rfl
    have hsurj : Function.Surjective append := by
      intro c
      let d := (c.val (Fin.castSucc (Fin.last k))).val
      have hd : d ∈ m.properDivisors := by
        apply Nat.mem_properDivisors.mpr
        have h := c.prop.2.2 (Fin.last k)
        simpa only [Fin.lt_def, Fin.succ_last, c.prop.2.1] using h
      have hmono : Monotone c.val :=
        (Fin.strictMono_iff_lt_succ.mpr fun i => (c.prop.2.2 i).2).monotone
      let trimmed : Fin (k + 1) → Fin (d + 1) := fun i =>
        ⟨(c.val i.castSucc).val, by
          have h := hmono (show i.castSucc ≤ (Fin.last k).castSucc from Fin.le_last i)
          change (c.val i.castSucc).val ≤ d at h
          omega⟩
      let b : Chain d k := ⟨trimmed, c.prop.1, rfl, by
        intro i
        exact c.prop.2.2 i.castSucc⟩
      refine ⟨⟨⟨d, hd⟩, b⟩, ?_⟩
      apply Subtype.ext
      funext i
      apply Fin.ext
      induction i using Fin.lastCases with
      | last => exact (extend_last _).trans c.prop.2.1.symm
      | cast i => simp only [append, extend, Fin.lastCases_castSucc, b, trimmed]
    let e : S ≃ Chain m (k + 1) := Equiv.ofBijective append ⟨hinj, hsurj⟩
    rw [← Nat.card_congr e, Nat.card_sigma]
    exact Finset.sum_coe_sort m.properDivisors (fun d => Nat.card (Chain d k))
  sorry

end D5.S3.Factorization.Combinatorics.StrictDivisorChainMobius
