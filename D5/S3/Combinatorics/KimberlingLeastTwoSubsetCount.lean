/- GID: D5/S3/Combinatorics/KimberlingLeastTwoSubsetCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/KimberlingLeastTwoSubsetCount
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Order.Interval.Finset.Nat, mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: Every subset whose least two elements sum to its maximum is counted by OEIS A077866 after shifting the index by three. -/

import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount

open Finset

/-!
Clark Kimberling's 2022 comment on OEIS A077866 conjectures that the number
of subsets of `{1, ..., N}` whose two least elements sum to their maximum is
`A077866(N - 3)`. The independent sequence below has the entry's four initial
values and four-term recurrence. Issue #11414 preregisters the full statement.

The counted subset has a unique decomposition `{a, b, a + b} ∪ T`, where
`0 < a < b` and `T` lies strictly between `b` and `a + b`. The source's
weighted-triangle and parity formulas are already public; the new content is
the source-faithful decomposition and its cardinality proof.
-/

private def subsetFrom (a b : ℕ) (T : Finset ℕ) : Finset ℕ :=
  insert a (insert b (insert (a + b) T))

private def validWitness (n a b : ℕ) (T : Finset ℕ) : Prop :=
  0 < a ∧ a < b ∧ a + b ≤ n ∧ T ⊆ Ioo b (a + b)

private theorem member_eq_or_between {n a b : ℕ} {T : Finset ℕ}
    (h : validWitness n a b T) {x : ℕ} (hx : x ∈ subsetFrom a b T) :
    x = a ∨ x = b ∨ x = a + b ∨ b < x ∧ x < a + b := by
  simp only [subsetFrom, mem_insert] at hx
  rcases hx with rfl | rfl | rfl | hx
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr ((mem_Ioo.mp (h.2.2.2 hx)))))

private theorem first_le_member {n a b : ℕ} {T : Finset ℕ}
    (h : validWitness n a b T) {x : ℕ} (hx : x ∈ subsetFrom a b T) : a ≤ x := by
  have hab := h.2.1
  rcases member_eq_or_between h hx with rfl | rfl | rfl | ⟨hbx, _⟩ <;> omega

private theorem second_le_member_of_ne_first {n a b : ℕ} {T : Finset ℕ}
    (h : validWitness n a b T) {x : ℕ} (hx : x ∈ subsetFrom a b T)
    (hxa : x ≠ a) : b ≤ x := by
  have ha := h.1
  rcases member_eq_or_between h hx with hax | rfl | rfl | ⟨hbx, _⟩ <;> omega

private theorem first_eq_of_subset_eq {n a b c d : ℕ} {T U : Finset ℕ}
    (hab : validWitness n a b T) (hcd : validWitness n c d U)
    (heq : subsetFrom a b T = subsetFrom c d U) : a = c := by
  have ha : a ∈ subsetFrom a b T := by simp [subsetFrom]
  have hc : c ∈ subsetFrom c d U := by simp [subsetFrom]
  have hac := first_le_member hab (heq.symm ▸ hc)
  have hca := first_le_member hcd (heq ▸ ha)
  omega

private theorem second_eq_of_subset_eq {n a b c d : ℕ} {T U : Finset ℕ}
    (hab : validWitness n a b T) (hcd : validWitness n c d U)
    (heq : subsetFrom a b T = subsetFrom c d U) : b = d := by
  have hac := first_eq_of_subset_eq hab hcd heq
  subst c
  have hb : b ∈ subsetFrom a b T := by simp [subsetFrom]
  have hd : d ∈ subsetFrom a d U := by simp [subsetFrom]
  have hab_lt := hab.2.1
  have had_lt := hcd.2.1
  have hbd := second_le_member_of_ne_first hab (heq.symm ▸ hd) (by omega)
  have hdb := second_le_member_of_ne_first hcd (heq ▸ hb) (by omega)
  omega

private theorem witness_injective {n a b c d : ℕ} {T U : Finset ℕ}
    (hab : validWitness n a b T) (hcd : validWitness n c d U)
    (heq : subsetFrom a b T = subsetFrom c d U) : a = c ∧ b = d ∧ T = U := by
  have hac := first_eq_of_subset_eq hab hcd heq
  have hbd := second_eq_of_subset_eq hab hcd heq
  subst c
  subst d
  refine ⟨rfl, rfl, ?_⟩
  ext x
  constructor <;> intro hx
  · have hxS : x ∈ subsetFrom a b U := heq ▸ (by simp [subsetFrom, hx])
    have hbounds := mem_Ioo.mp (hab.2.2.2 hx)
    have ha_pos := hab.1
    have hab_lt := hab.2.1
    simp only [subsetFrom, mem_insert] at hxS
    rcases hxS with hxa | hxb | hxab | hxU
    · omega
    · omega
    · omega
    · exact hxU
  · have hxS : x ∈ subsetFrom a b T := heq.symm ▸ (by simp [subsetFrom, hx])
    have hbounds := mem_Ioo.mp (hcd.2.2.2 hx)
    have ha_pos := hcd.1
    have hab_lt := hcd.2.1
    simp only [subsetFrom, mem_insert] at hxS
    rcases hxS with hxa | hxb | hxab | hxT
    · omega
    · omega
    · omega
    · exact hxT

private def witnesses (n : ℕ) : Finset (ℕ × ℕ × Finset ℕ) :=
  (Icc 1 n).biUnion fun a =>
    (Icc (a + 1) (n - a)).biUnion fun b =>
      ((Ioo b (a + b)).powerset).image fun T => (a, b, T)

private theorem mem_witnesses_iff {n a b : ℕ} {T : Finset ℕ} :
    (a, b, T) ∈ witnesses n ↔ validWitness n a b T := by
  classical
  simp only [witnesses, mem_biUnion, mem_image, mem_Icc, mem_powerset]
  constructor
  · rintro ⟨a', ⟨ha', han⟩, b', ⟨hb', hbn⟩, T', hT', heq⟩
    cases heq
    exact ⟨by omega, by omega, by omega, hT'⟩
  · rintro ⟨ha, hab, habn, hT⟩
    refine ⟨a, ⟨by omega, by omega⟩, b, ⟨by omega, by omega⟩, T, hT, rfl⟩

private def countedSubsets (n : ℕ) : Finset (Finset ℕ) :=
  (witnesses n).image fun w => subsetFrom w.1 w.2.1 w.2.2

private theorem card_countedSubsets_eq_card_witnesses (n : ℕ) :
    (countedSubsets n).card = (witnesses n).card := by
  classical
  rw [countedSubsets, card_image_iff]
  intro w hw v hv heq
  rcases w with ⟨a, b, T⟩
  rcases v with ⟨c, d, U⟩
  have hab := mem_witnesses_iff.mp hw
  have hcd := mem_witnesses_iff.mp hv
  obtain ⟨rfl, rfl, rfl⟩ := witness_injective hab hcd heq
  rfl

private theorem card_witnesses (n : ℕ) :
    (witnesses n).card =
      ∑ a ∈ Icc 1 n, ∑ _b ∈ Icc (a + 1) (n - a), 2 ^ (a - 1) := by
  classical
  unfold witnesses
  rw [card_biUnion]
  · apply sum_congr rfl
    intro a ha
    rw [card_biUnion]
    · apply sum_congr rfl
      intro b hb
      rw [card_image_of_injective]
      · rw [card_powerset, Nat.card_Ioo]
        have hab : a + 1 ≤ b := (mem_Icc.mp hb).1
        have hexp : a + b - b - 1 = a - 1 := by omega
        rw [hexp]
      · intro T U h
        exact congrArg (fun w : ℕ × ℕ × Finset ℕ => w.2.2) h
    · intro b hb d hd hbd
      apply disjoint_left.mpr
      intro w hw hw'
      obtain ⟨T, hT, hTw⟩ := mem_image.mp hw
      obtain ⟨U, hU, hUw⟩ := mem_image.mp hw'
      have h : b = d := by
        have h1 := congrArg (fun z : ℕ × ℕ × Finset ℕ => z.2.1) hTw
        have h2 := congrArg (fun z : ℕ × ℕ × Finset ℕ => z.2.1) hUw
        simpa using h1.trans h2.symm
      exact hbd h
  · intro a ha c hc hac
    apply disjoint_left.mpr
    intro w hw hw'
    obtain ⟨b, hb, hwb⟩ := mem_biUnion.mp hw
    obtain ⟨d, hd, hwd⟩ := mem_biUnion.mp hw'
    obtain ⟨T, hT, hTw⟩ := mem_image.mp hwb
    obtain ⟨U, hU, hUw⟩ := mem_image.mp hwd
    have h : a = c := by
      have h1 := congrArg (fun z : ℕ × ℕ × Finset ℕ => z.1) hTw
      have h2 := congrArg (fun z : ℕ × ℕ × Finset ℕ => z.1) hUw
      simpa using h1.trans h2.symm
    exact hac h

private theorem card_countedSubsets_formula (n : ℕ) :
    (countedSubsets n).card =
      ∑ a ∈ Icc 1 n, (n - 2 * a) * 2 ^ (a - 1) := by
  rw [card_countedSubsets_eq_card_witnesses, card_witnesses]
  apply sum_congr rfl
  intro a ha
  have han : a ≤ n := (mem_Icc.mp ha).2
  simp only [sum_const, nsmul_eq_mul, Nat.card_Icc]
  congr 1
  have h1 (x y : ℕ) : x + 1 - (y + 1) = x - y := by omega
  rw [h1, Nat.sub_sub]
  simp [two_mul]

/-- A subset of `{1, ..., n}` with two least elements `a < b` and maximum `a + b`. -/
def literalGood (n : ℕ) (S : Finset ℕ) : Prop :=
  S ⊆ Icc 1 n ∧
    ∃ a b : ℕ, a ∈ S ∧ b ∈ S ∧ a < b ∧
      (∀ x ∈ S, a ≤ x) ∧
      (∀ x ∈ S, x ≠ a → b ≤ x) ∧
      a + b ∈ S ∧ (∀ x ∈ S, x ≤ a + b)

private theorem mem_countedSubsets_iff (n : ℕ) (S : Finset ℕ) :
    S ∈ countedSubsets n ↔ literalGood n S := by
  classical
  constructor
  · intro hS
    obtain ⟨⟨a, b, T⟩, hw, rfl⟩ := mem_image.mp hS
    have h := mem_witnesses_iff.mp hw
    have ha_pos := h.1
    have hsum_le := h.2.2.1
    refine ⟨?_, a, b, by simp [subsetFrom], by simp [subsetFrom], h.2.1,
      ?_, ?_, by simp [subsetFrom], ?_⟩
    · intro x hx
      have hax := first_le_member h hx
      have hxn : x ≤ a + b := by
        rcases member_eq_or_between h hx with hxa | hxb | hxab | hmid <;> omega
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    · intro x hx
      exact first_le_member h hx
    · intro x hx hxa
      exact second_le_member_of_ne_first h hx hxa
    · intro x hx
      rcases member_eq_or_between h hx with hxa | hxb | hxab | hmid <;> omega
  · rintro ⟨hsub, a, b, ha, hb, hab, hmin, hsecond, hsum, hmax⟩
    let T := S \ {a, b, a + b}
    have ha_pos : 0 < a := by
      have := mem_Icc.mp (hsub ha)
      omega
    have hsum_le : a + b ≤ n := (mem_Icc.mp (hsub hsum)).2
    have hT : T ⊆ Ioo b (a + b) := by
      intro x hx
      have hxS := (mem_sdiff.mp hx).1
      have hxnot := (mem_sdiff.mp hx).2
      have hxa : x ≠ a := by
        intro heq
        exact hxnot (by simp [heq])
      have hxb : x ≠ b := by
        intro heq
        exact hxnot (by simp [heq])
      have hxsum : x ≠ a + b := by
        intro heq
        exact hxnot (by simp [heq])
      have hbx := hsecond x hxS hxa
      have hxs := hmax x hxS
      exact mem_Ioo.mpr ⟨by omega, by omega⟩
    have hrepr : S = subsetFrom a b T := by
      ext x
      constructor
      · intro hx
        by_cases hxa : x = a
        · simp [subsetFrom, hxa]
        by_cases hxb : x = b
        · simp [subsetFrom, hxb]
        by_cases hxsum : x = a + b
        · simp [subsetFrom, hxsum]
        have hxT : x ∈ T := mem_sdiff.mpr ⟨hx, by simp [hxa, hxb, hxsum]⟩
        simp [subsetFrom, hxT]
      · intro hx
        simp only [subsetFrom, mem_insert] at hx
        rcases hx with rfl | rfl | rfl | hxT
        · exact ha
        · exact hb
        · exact hsum
        · exact (mem_sdiff.mp hxT).1
    apply mem_image.mpr
    refine ⟨(a, b, T), mem_witnesses_iff.mpr ⟨ha_pos, hab, hsum_le, hT⟩, ?_⟩
    exact hrepr.symm

/-- Number of subsets in Kimberling's conjecture, counted from the literal set family. -/
noncomputable def subsetCount (n : ℕ) : ℕ := by
  classical
  exact ((Icc 1 n).powerset.filter (literalGood n)).card

private theorem subsetCount_formula (n : ℕ) :
    subsetCount n = ∑ a ∈ Icc 1 n, (n - 2 * a) * 2 ^ (a - 1) := by
  classical
  have hsets : (Icc 1 n).powerset.filter (literalGood n) = countedSubsets n := by
    ext S
    constructor
    · intro h
      exact (mem_countedSubsets_iff n S).mpr (mem_filter.mp h).2
    · intro h
      have hgood := (mem_countedSubsets_iff n S).mp h
      exact mem_filter.mpr ⟨mem_powerset.mpr hgood.1, hgood⟩
  rw [subsetCount, hsets, card_countedSubsets_formula]

private def geom (m : ℕ) : ℕ := ∑ a ∈ Icc 1 (m + 1), 2 ^ (a - 1)

private theorem geom_add_one (m : ℕ) : geom m + 1 = 2 ^ (m + 1) := by
  induction m with
  | zero => norm_num [geom]
  | succ m ih =>
    unfold geom at ih ⊢
    rw [show m + 1 + 1 = (m + 1) + 1 by omega,
      sum_Icc_succ_top (by omega : 1 ≤ (m + 1) + 1)]
    have hexp : (m + 1 + 1) - 1 = m + 1 := by omega
    rw [hexp]
    rw [pow_succ]
    omega

private def weighted (m : ℕ) : ℕ :=
  ∑ a ∈ Icc 1 (m + 1), (2 * m + 3 - 2 * a) * 2 ^ (a - 1)

private theorem weighted_closed (m : ℕ) :
    weighted m + (2 * m + 5) = 3 * 2 ^ (m + 1) := by
  induction m with
  | zero => norm_num [weighted]
  | succ m ih =>
    have hstep : weighted (m + 1) = weighted m + 2 * geom m + 2 ^ (m + 1) := by
      unfold weighted geom
      rw [show (m + 1) + 1 = (m + 1) + 1 by rfl,
        sum_Icc_succ_top (by omega : 1 ≤ (m + 1) + 1)]
      have hnew : (2 * (m + 1) + 3 - 2 * (m + 1 + 1)) = 1 := by omega
      have hexp : (m + 1 + 1) - 1 = m + 1 := by omega
      rw [hnew, hexp, one_mul]
      have hpoint (a : ℕ) (ha : a ∈ Icc 1 (m + 1)) :
          (2 * (m + 1) + 3 - 2 * a) * 2 ^ (a - 1) =
            (2 * m + 3 - 2 * a) * 2 ^ (a - 1) + 2 * 2 ^ (a - 1) := by
        have ha_le := (mem_Icc.mp ha).2
        have hcoeff : 2 * (m + 1) + 3 - 2 * a =
            (2 * m + 3 - 2 * a) + 2 := by omega
        rw [hcoeff]
        ring
      rw [sum_congr rfl hpoint, sum_add_distrib]
      simp only [← mul_sum]
    have hgeom := geom_add_one m
    rw [hstep, pow_succ]
    omega

private theorem subsetCount_odd (m : ℕ) :
    subsetCount (2 * m + 3) + (2 * m + 5) = 3 * 2 ^ (m + 1) := by
  rw [subsetCount_formula]
  have hsub : Icc 1 (m + 1) ⊆ Icc 1 (2 * m + 3) := by
    intro a ha
    simp only [mem_Icc] at ha ⊢
    omega
  have hsum :
      (∑ a ∈ Icc 1 (2 * m + 3), (2 * m + 3 - 2 * a) * 2 ^ (a - 1)) =
        weighted m := by
    unfold weighted
    apply (sum_subset hsub ?_).symm
    intro a ha hanot
    have ha_big : m + 1 < a := by
      have ha_low := (mem_Icc.mp ha).1
      have : a ∉ Icc 1 (m + 1) := hanot
      simp only [mem_Icc, not_and] at this
      exact lt_of_not_ge (this ha_low)
    have hzero : 2 * m + 3 - 2 * a = 0 := by omega
    simp [hzero]
  rw [hsum]
  exact weighted_closed m

private theorem subsetCount_even (m : ℕ) :
    subsetCount (2 * m + 4) + (2 * m + 6) = 2 ^ (m + 3) := by
  rw [subsetCount_formula]
  have hsub : Icc 1 (m + 1) ⊆ Icc 1 (2 * m + 4) := by
    intro a ha
    simp only [mem_Icc] at ha ⊢
    omega
  have hsum :
      (∑ a ∈ Icc 1 (2 * m + 4), (2 * m + 4 - 2 * a) * 2 ^ (a - 1)) =
        weighted m + geom m := by
    have htrim := (sum_subset hsub (f := fun a =>
      (2 * m + 4 - 2 * a) * 2 ^ (a - 1)) ?_).symm
    · rw [htrim]
      unfold weighted geom
      calc
        (∑ a ∈ Icc 1 (m + 1), (2 * m + 4 - 2 * a) * 2 ^ (a - 1)) =
            ∑ a ∈ Icc 1 (m + 1),
              ((2 * m + 3 - 2 * a) * 2 ^ (a - 1) + 2 ^ (a - 1)) := by
                apply sum_congr rfl
                intro a ha
                have ha_le := (mem_Icc.mp ha).2
                have hcoeff : 2 * m + 4 - 2 * a =
                    (2 * m + 3 - 2 * a) + 1 := by omega
                rw [hcoeff]
                ring
        _ = _ := by rw [sum_add_distrib]
    · intro a ha hanot
      have ha_big : m + 1 < a := by
        have ha_low := (mem_Icc.mp ha).1
        simp only [mem_Icc, not_and] at hanot
        exact lt_of_not_ge (hanot ha_low)
      have hzero : 2 * m + 4 - 2 * a = 0 := by omega
      simp [hzero]
  rw [hsum]
  have hw := weighted_closed m
  have hg := geom_add_one m
  have hp : 2 ^ (m + 3) = 4 * 2 ^ (m + 1) := by
    rw [show m + 3 = (m + 1) + 2 by omega, pow_add]
    norm_num
    ring
  omega

private def a077866 (n : ℕ) : ℕ :=
  if n % 2 = 0 then 3 * 2 ^ (n / 2 + 1) - (n + 5)
  else 2 ^ (n / 2 + 3) - (n + 5)

private theorem a077866_even (m : ℕ) :
    a077866 (2 * m) = 3 * 2 ^ (m + 1) - (2 * m + 5) := by
  simp [a077866]

private theorem a077866_odd (m : ℕ) :
    a077866 (2 * m + 1) = 2 ^ (m + 3) - (2 * m + 6) := by
  have hdiv : (2 * m + 1) / 2 = m := by omega
  simp [a077866, hdiv]

private theorem result_closed (n : ℕ) : subsetCount (n + 3) = a077866 n := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [show m + m = 2 * m by omega, a077866_even]
    have h := subsetCount_odd m
    omega
  · rw [show 2 * m + 1 + 3 = 2 * m + 4 by omega, a077866_odd]
    have h := subsetCount_even m
    omega

private theorem a077866_even_add (m : ℕ) :
    a077866 (2 * m) + (2 * m + 5) = 3 * 2 ^ (m + 1) := by
  rw [a077866_even]
  have h := weighted_closed m
  omega

private theorem a077866_odd_add (m : ℕ) :
    a077866 (2 * m + 1) + (2 * m + 6) = 2 ^ (m + 3) := by
  rw [a077866_odd]
  have h := subsetCount_even m
  omega

private theorem a077866_initial :
    a077866 0 = 1 ∧ a077866 1 = 2 ∧
      a077866 2 = 5 ∧ a077866 3 = 8 := by
  norm_num [a077866]

private theorem a077866_recurrence (n : ℕ) :
    a077866 (n + 4) + 4 * a077866 (n + 1) =
      2 * a077866 (n + 3) + a077866 (n + 2) + 2 * a077866 n := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [show m + m = 2 * m by omega]
    have h0 := a077866_even_add m
    have h1 := a077866_odd_add m
    have h2 := a077866_even_add (m + 1)
    have h3 := a077866_odd_add (m + 1)
    have h4 := a077866_even_add (m + 2)
    have e2 : a077866 (2 * m + 2) + (2 * m + 7) = 3 * 2 ^ (m + 2) := by
      simpa only [show 2 * (m + 1) + 5 = 2 * m + 7 by omega,
        show 2 * (m + 1) = 2 * m + 2 by omega,
        show (m + 1) + 1 = m + 2 by omega] using h2
    have e3 : a077866 (2 * m + 3) + (2 * m + 8) = 2 ^ (m + 4) := by
      simpa only [show 2 * (m + 1) + 1 + (2 * (m + 1) + 6) =
          (2 * m + 3) + (2 * m + 8) by omega,
        show 2 * (m + 1) + 1 = 2 * m + 3 by omega,
        show 2 * (m + 1) + 6 = 2 * m + 8 by omega,
        show (m + 1) + 3 = m + 4 by omega] using h3
    have e4 : a077866 (2 * m + 4) + (2 * m + 9) = 3 * 2 ^ (m + 3) := by
      simpa only [show 2 * (m + 2) + 5 = 2 * m + 9 by omega,
        show 2 * (m + 2) = 2 * m + 4 by omega,
        show (m + 2) + 1 = m + 3 by omega] using h4
    have hp1 : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by
      rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
      ring
    have hp2 : 2 ^ (m + 3) = 4 * 2 ^ (m + 1) := by
      rw [show m + 3 = (m + 1) + 2 by omega, pow_add]
      norm_num
      ring
    have hp3 : 2 ^ (m + 4) = 8 * 2 ^ (m + 1) := by
      rw [show m + 4 = (m + 1) + 3 by omega, pow_add]
      norm_num
      ring
    omega
  · rw [show 2 * m + 1 + 4 = 2 * m + 5 by omega,
      show 2 * m + 1 + 1 = 2 * m + 2 by omega,
      show 2 * m + 1 + 3 = 2 * m + 4 by omega,
      show 2 * m + 1 + 2 = 2 * m + 3 by omega]
    have h0 := a077866_odd_add m
    have h1 := a077866_even_add (m + 1)
    have h2 := a077866_odd_add (m + 1)
    have h3 := a077866_even_add (m + 2)
    have h4 := a077866_odd_add (m + 2)
    have e1 : a077866 (2 * m + 2) + (2 * m + 7) = 3 * 2 ^ (m + 2) := by
      simpa only [show 2 * (m + 1) + 5 = 2 * m + 7 by omega,
        show 2 * (m + 1) = 2 * m + 2 by omega,
        show (m + 1) + 1 = m + 2 by omega] using h1
    have e2 : a077866 (2 * m + 3) + (2 * m + 8) = 2 ^ (m + 4) := by
      simpa only [show 2 * (m + 1) + 6 = 2 * m + 8 by omega,
        show 2 * (m + 1) + 1 = 2 * m + 3 by omega,
        show (m + 1) + 3 = m + 4 by omega] using h2
    have e3 : a077866 (2 * m + 4) + (2 * m + 9) = 3 * 2 ^ (m + 3) := by
      simpa only [show 2 * (m + 2) + 5 = 2 * m + 9 by omega,
        show 2 * (m + 2) = 2 * m + 4 by omega,
        show (m + 2) + 1 = m + 3 by omega] using h3
    have e4 : a077866 (2 * m + 5) + (2 * m + 10) = 2 ^ (m + 5) := by
      simpa only [show 2 * (m + 2) + 6 = 2 * m + 10 by omega,
        show 2 * (m + 2) + 1 = 2 * m + 5 by omega,
        show (m + 2) + 3 = m + 5 by omega] using h4
    have hp1 : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by
      rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
      ring
    have hp2 : 2 ^ (m + 3) = 4 * 2 ^ (m + 1) := by
      rw [show m + 3 = (m + 1) + 2 by omega, pow_add]
      norm_num
      ring
    have hp3 : 2 ^ (m + 4) = 8 * 2 ^ (m + 1) := by
      rw [show m + 4 = (m + 1) + 3 by omega, pow_add]
      norm_num
      ring
    have hp4 : 2 ^ (m + 5) = 16 * 2 ^ (m + 1) := by
      rw [show m + 5 = (m + 1) + 4 by omega, pow_add]
      norm_num
      ring
    omega

/-- A077866 from the four initial terms and recurrence printed in the OEIS entry. -/
def oeisSequence : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 5
  | 3 => 8
  | n + 4 =>
      2 * oeisSequence (n + 3) + oeisSequence (n + 2) +
        2 * oeisSequence n - 4 * oeisSequence (n + 1)

private theorem oeisSequence_eq_closed (n : ℕ) : oeisSequence n = a077866 n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h0 : n = 0
    · subst n; norm_num [oeisSequence, a077866]
    by_cases h1 : n = 1
    · subst n; norm_num [oeisSequence, a077866]
    by_cases h2 : n = 2
    · subst n; norm_num [oeisSequence, a077866]
    by_cases h3 : n = 3
    · subst n; norm_num [oeisSequence, a077866]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    change 2 * oeisSequence (k + 3) + oeisSequence (k + 2) +
        2 * oeisSequence k - 4 * oeisSequence (k + 1) = a077866 (k + 4)
    rw [ih (k + 3) (by omega), ih (k + 2) (by omega),
      ih k (by omega), ih (k + 1) (by omega)]
    have hrec := a077866_recurrence k
    omega

/-- Kimberling's 2022 OEIS A077866 subset-count conjecture, including its base cases. -/
def claim : Prop :=
  subsetCount 0 = 0 ∧ subsetCount 1 = 0 ∧ subsetCount 2 = 0 ∧
    ∀ n : ℕ, subsetCount (n + 3) = oeisSequence n

/-- The subset count agrees with A077866 at every index, after the shift by three. -/
theorem result : claim := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [subsetCount_formula]
  · norm_num [subsetCount_formula]
  · rw [subsetCount_formula]
    apply Finset.sum_eq_zero
    intro a ha
    have ha' : 1 ≤ a ∧ a ≤ 2 := mem_Icc.mp ha
    have hzero : 2 - 2 * a = 0 := by omega
    simp [hzero]
  · intro n
    rw [oeisSequence_eq_closed]
    exact result_closed n

#print axioms literalGood
#print axioms subsetCount
#print axioms oeisSequence
#print axioms claim
#print axioms result

end D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount
