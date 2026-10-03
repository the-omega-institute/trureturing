/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingRoyalLow
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingRoyalLow
   mirror-E: none(waiver:royal-low-counting)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DyckWord, mathlib/module/Mathlib.Algebra.BigOperators.Group.Finset.Basic, mathlib/module/Mathlib.RingTheory.PowerSeries.Basic, mathlib/module/Mathlib.RingTheory.PowerSeries.Inverse, mathlib/module/Mathlib.Data.Set.Card]
   utility: none
   digest: Proves the low Royal nonnesting generating-function identity. -/
import D5.S3.Combinatorics.Nonnesting.NonnestingRoyalLowFiber
import Mathlib.Combinatorics.Enumerative.DyckWord
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalDownRuns
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalGround
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalGroundSeries
import D5.S3.Combinatorics.Nonnesting.NonnestingDefs
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.Set.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.Combinatorics.Nonnesting.NonnestingRoyalLow

open NonnestingBasicRoyalDownCount

open DyckStep NonnestingBasicRoyalDownRuns Classical

open DyckStep NonnestingRoyalLowFiber

open DyckStep NonnestingBasicRoyalGround
open Classical in

open NonnestingBasicRoyalIncBlocks

open DyckStep

open scoped symmDiff

open DyckStep NonnestingBasicRoyalEncoding NonnestingBasicRoyalShape NonnestingBasicRoyalIncBlocks
  NonnestingRoyalLowFiber PowerSeries NonnestingBasicOrders  NonnestingDefs
  NonnestingBasicRoyalBijection NonnestingBasicRoyalIncConverse NonnestingRoyalLowGap
  NonnestingRoyalLowConverse NonnestingBasicRoyalGround NonnestingBasicRoyalGroundCount
  NonnestingBasicRoyalGroundSeries NonnestingBasicRoyalDownRuns NonnestingBasicRoyalDownSeries
local notation "toggle" =>
  (fun (active : Finset ℕ) (letter : ℕ) => active ∆ Singleton.singleton letter)
set_option maxHeartbeats 2000000 in
theorem result : NonnestingDefs.claim1132 := by
  classical
  let groundSeries : PowerSeries ℤ :=
    PowerSeries.mk fun n => (groundWeight n : ℤ)
  let downSeries : PowerSeries ℤ :=
    PowerSeries.mk fun n => (downWeight n : ℤ)
  have downPairs_eq_flat_sum (s : List DyckStep) :
      downPairs s = ∑ k ∈ Finset.range (s.count D - 1),
        if ∃ u z : List DyckStep, s = u ++ [D, D] ++ z ∧ u.count D = k then 1 else 0 := by
    let flatAt (s : List DyckStep) (k : ℕ) : Prop :=
      ∃ u z : List DyckStep, s = u ++ [D, D] ++ z ∧ u.count D = k
    change downPairs s = ∑ k ∈ Finset.range (s.count D - 1),
      if flatAt s k then 1 else 0
    have hU (t : List DyckStep) (k : ℕ) :
        flatAt (U :: t) k ↔ flatAt t k := by
      constructor
      · rintro ⟨u, z, hu, hk⟩
        cases u with
        | nil => simp at hu
        | cons a u =>
          have ha : a = U := by
            have h := congrArg List.head? hu
            simpa using h.symm
          subst a
          refine ⟨u, z, ?_, ?_⟩
          · simpa using hu
          · simpa using hk
      · rintro ⟨u, z, hu, hk⟩
        exact ⟨U :: u, z, by simp [hu], by simpa using hk⟩
    have hD (t : List DyckStep) (k : ℕ) :
        flatAt (D :: t) (k + 1) ↔ flatAt t k := by
      constructor
      · rintro ⟨u, z, hu, hk⟩
        cases u with
        | nil => simp at hk
        | cons a u =>
          have ha : a = D := by
            have h := congrArg List.head? hu
            simpa using h.symm
          subst a
          refine ⟨u, z, ?_, ?_⟩
          · simpa using hu
          · simpa using hk
      · rintro ⟨u, z, hu, hk⟩
        exact ⟨D :: u, z, by simp [hu], by simp [hk]⟩
    have hD0 (t : List DyckStep) :
        flatAt (D :: t) 0 ↔ t.head? = some D := by
      constructor
      · rintro ⟨u, z, hu, hk⟩
        cases u with
        | nil =>
          have ht : t = D :: z := by simpa using congrArg List.tail hu
          simp [ht]
        | cons a u =>
          have ha : a = D := by
            have h := congrArg List.head? hu
            simpa using h.symm
          subst a; simp at hk
      · intro h
        cases t with
        | nil => simp at h
        | cons a t =>
          have ha : a = D := by simpa using h
          subst a; exact ⟨[], t, rfl, rfl⟩
    induction s with
    | nil => simp [downPairs]
    | cons a s ih =>
      cases a with
      | U =>
        have hw : downPairs (U :: s) = downPairs s := by
          cases s with
          | nil => rfl
          | cons a s => cases a <;> simp [downPairs]
        have hc : (U :: s).count D = s.count D := by simp
        rw [hw]; rw [hc]
        simpa only [hU] using ih
      | D =>
        have hw : downPairs (D :: s) = downPairs s +
            if s.head? = some D then 1 else 0 := by
          cases s with
          | nil => simp [downPairs]
          | cons a s => cases a <;> simp [downPairs] <;> omega
        by_cases hs : s.count D = 0
        · have hhead : s.head? ≠ some D := by
            cases s with
            | nil => simp
            | cons a s => cases a <;> (simp at hs ⊢)
          have hzero : downPairs s = 0 := by simpa [hs] using ih
          simp [hw, hs, hhead, hzero]
        · have hpos : 0 < s.count D := Nat.pos_of_ne_zero hs
          have hsize : (D :: s).count D - 1 = s.count D := by simp
          rw [hw, hsize]; have hsum :
              (∑ k ∈ Finset.range (s.count D),
                if flatAt (D :: s) k then 1 else 0) =
              (if flatAt (D :: s) 0 then 1 else 0) +
                ∑ k ∈ Finset.range (s.count D - 1),
                  if flatAt (D :: s) (k + 1) then 1 else 0 := by
            conv_lhs => rw [show s.count D = (s.count D - 1) + 1 by omega,
              Finset.sum_range_succ']
            ac_rfl
          have htail :
              (∑ k ∈ Finset.range (s.count D - 1),
                if flatAt (D :: s) (k + 1) then 1 else 0) = downPairs s := by
            simpa only [hD] using ih.symm
          have hfirst : (if flatAt (D :: s) 0 then 1 else 0) =
              (if s.head? = some D then 1 else 0) := by simp [hD0]
          rw [hsum, hfirst, htail]; omega
  have groundSingletons_eq_ground_sum (d : DyckWord) :
      groundSingletons d = ∑ k ∈ Finset.range (d.toList.count D - 1),
        if ∃ u z : List DyckStep,
          d.toList = u ++ [D, U, D] ++ z ∧ u.count D = k ∧
            u.count U = u.count D + 1 then 1 else 0 := by
    let groundAt (s : List DyckStep) (k : ℕ) (height : ℤ) : Prop :=
      ∃ u z : List DyckStep, s = u ++ [D, U, D] ++ z ∧ u.count D = k ∧
        height + (u.count U : ℤ) = (u.count D : ℤ) + 1
    let groundScan (height : ℤ) (steps : List DyckStep) : ℕ :=
      (List.rec (motive := fun _ => ℤ → ℕ) (fun _ => 0)
        (fun step tail previous level =>
          match step with
          | U => previous (level + 1)
          | D => previous (level - 1) +
              if level = 1 ∧ tail.take 2 = [U, D] then 1 else 0) steps) height
    have groundScan_nil (height : ℤ) : groundScan height [] = 0 := by rfl
    have groundScan_U (height : ℤ) (tail : List DyckStep) :
        groundScan height (U :: tail) = groundScan (height + 1) tail := by rfl
    have groundScan_D (height : ℤ) (tail : List DyckStep) :
        groundScan height (D :: tail) = groundScan (height - 1) tail +
          if height = 1 ∧ tail.take 2 = [U, D] then 1 else 0 := by rfl
    have hsum : ∀ (s : List DyckStep) (height : ℤ),
        groundScan height s = ∑ k ∈ Finset.range (s.count D),
          if groundAt s k height then 1 else 0 := by
      intro s
      induction s with
      | nil => intro height; simp [groundScan_nil, groundScan_U, groundScan_D]
      | cons step s ih =>
        intro height
        cases step with
        | U =>
          have hshift (k : ℕ) : groundAt (U :: s) k height ↔
              groundAt s k (height + 1) := by
            constructor
            · rintro ⟨u, z, hu, hk, hh⟩
              cases u with
              | nil => simp at hu
              | cons a u =>
                have ha : a = U := by
                  have he := congrArg List.head? hu
                  simpa using he.symm
                subst a
                refine ⟨u, z, by simpa using hu, by simpa using hk, ?_⟩
                simp at hh; omega
            · rintro ⟨u, z, hu, hk, hh⟩
              refine ⟨U :: u, z, by simp [hu], by simpa using hk, ?_⟩
              simp; omega
          simpa [groundScan_nil, groundScan_U, groundScan_D, hshift] using ih (height + 1)
        | D =>
          have hshift (k : ℕ) : groundAt (D :: s) (k + 1) height ↔
              groundAt s k (height - 1) := by
            constructor
            · rintro ⟨u, z, hu, hk, hh⟩
              cases u with
              | nil => simp at hk
              | cons a u =>
                have ha : a = D := by
                  have he := congrArg List.head? hu
                  simpa using he.symm
                subst a
                refine ⟨u, z, by simpa using hu, ?_, ?_⟩
                · simpa using hk
                · simp at hh
                  omega
            · rintro ⟨u, z, hu, hk, hh⟩
              refine ⟨D :: u, z, by simp [hu], by simp [hk], ?_⟩
              simp; omega
          have hfirst : groundAt (D :: s) 0 height ↔
              height = 1 ∧ s.take 2 = [U, D] := by
            constructor
            · rintro ⟨u, z, hu, hk, hh⟩
              cases u with
              | nil =>
                have ht : s = U :: D :: z := by
                  simpa using congrArg List.tail hu
                simpa [ht] using hh
              | cons a u =>
                have ha : a = D := by
                  have he := congrArg List.head? hu
                  simpa using he.symm
                subst a; simp at hk
            · rintro ⟨hh, ht⟩
              refine ⟨[], s.drop 2, ?_, by simp, by simpa using hh⟩
              have he := s.take_append_drop 2; rw [ht] at he
              simpa using congrArg (D :: ·) he.symm
          simp only [groundScan_nil, groundScan_U, groundScan_D,
            List.count_cons, beq_self_eq_true, ↓reduceIte]
          rw [Finset.sum_range_succ']; simp only [hshift, hfirst]; rw [← ih]
    have habove : ∀ (s : List DyckStep) (height : ℤ) (tail : List DyckStep),
        (∀ i, 1 ≤ height + ((s.take i).count U : ℤ) - (s.take i).count D) →
        groundScan height (s ++ tail) =
          groundScan (height + (s.count U : ℤ) - s.count D) tail := by
      intro s
      induction s with
      | nil => intro height tail _; simp
      | cons step s ih =>
        intro height tail h
        cases step with
        | U =>
          have hs : ∀ i, 1 ≤ height + 1 + ((s.take i).count U : ℤ) -
              (s.take i).count D := by
            intro i; have hi := h (i + 1); simp at hi; omega
          simp only [List.cons_append, groundScan_nil, groundScan_U, groundScan_D]
          rw [ih (height + 1) tail hs]; congr 1; simp; omega
        | D =>
          have hheight : height ≠ 1 := by
            have hi := h 1; simp at hi; omega
          have hs : ∀ i, 1 ≤ height - 1 + ((s.take i).count U : ℤ) -
              (s.take i).count D := by
            intro i; have hi := h (i + 1); simp at hi; omega
          simp only [List.cons_append, groundScan_nil, groundScan_U, groundScan_D,
            hheight, false_and, ↓reduceIte,
            Nat.add_zero]
          rw [ih (height - 1) tail hs]; congr 1; simp; omega
    have hscan : ∀ n (d : DyckWord), d.semilength = n →
        groundScan 0 d.toList = groundSingletons d := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro d hn
        by_cases hd : d = 0
        · subst d
          change groundScan 0 [] = groundSingletons 0; simp [groundScan_nil, groundSingletons]
        let p := d.insidePart; let q := d.outsidePart
        have hword : d.toList = U :: (p.toList ++ D :: q.toList) := by
          have he := congrArg DyckWord.toList (d.nest_insidePart_add_outsidePart hd)
          change U :: (p.toList ++ [D]) ++ q.toList = d.toList at he
          simpa only [List.cons_append, List.append_assoc, List.singleton_append,
            List.nil_append] using he.symm
        have hp : ∀ i, 1 ≤ (1 : ℤ) + ((p.toList.take i).count U : ℤ) -
            (p.toList.take i).count D := by
          intro i; have hi := p.count_D_le_count_U i; omega
        have hq : groundScan 0 q.toList = groundSingletons q := by
          apply ih q.semilength
          · simpa [q, hn] using d.semilength_outsidePart_lt hd
          · rfl
        have hsingle : q.toList.take 2 = [U, D] ↔ q ≠ 0 ∧ q.insidePart = 0 := by
          constructor
          · intro ht
            have hne : q ≠ 0 := by
              intro hz; rw [hz] at ht; change ([] : List DyckStep) = [U, D] at ht; cases ht
            have hlist : q.toList = U :: D :: q.toList.drop 2 := by
              simpa [ht] using (q.toList.take_append_drop 2).symm
            have hhead : q.toList.take 1 = [U] := by rw [hlist]; rfl
            have hlen : 1 < q.toList.length := by
              have hl := congrArg List.length hlist; simp only [List.length_cons] at hl; omega
            have hf : q.firstReturn = 1 := by
              rw [DyckWord.firstReturn, List.findIdx_eq, List.getElem_range]
              · simp [ht, hhead]
              · simpa using hlen
            refine ⟨hne, ?_⟩
            apply DyckWord.ext; change q.insidePart.toList = []
            simp [DyckWord.insidePart, hne, hf, DyckWord.denest, DyckWord.take, ht]
          · rintro ⟨hne, hi⟩
            have he := congrArg DyckWord.toList (q.nest_insidePart_add_outsidePart hne)
            rw [hi] at he; change U :: D :: q.outsidePart.toList = q.toList at he; simp [← he]
        rw [hword, groundScan_U, show (0 : ℤ) + 1 = 1 by omega,
          habove p.toList 1 (D :: q.toList) hp]
        rw [p.count_U_eq_count_D]
        simp only [add_sub_cancel_right, groundScan_nil, groundScan_U, groundScan_D,
          sub_self, hq, hsingle]
        conv_rhs => rw [groundSingletons, dif_neg hd]
        simp only [true_and]; rfl
    rw [← hscan d.semilength d rfl, hsum]
    have hlast : ¬ groundAt d.toList (d.toList.count D - 1) 0 := by
      rintro ⟨u, z, hu, hk, _⟩
      have hc := congrArg (List.count D) hu; simp at hc; omega
    have heq : ∀ k, groundAt d.toList k 0 ↔
        ∃ u z : List DyckStep, d.toList = u ++ [D, U, D] ++ z ∧
          u.count D = k ∧ u.count U = u.count D + 1 := by
      intro k; simp only [groundAt, zero_add]
      constructor <;> rintro ⟨u, z, hu, hk, hh⟩ <;>
        exact ⟨u, z, hu, hk, by omega⟩
    by_cases hc : d.toList.count D = 0
    · simp [hc]
    · conv_lhs => rw [show d.toList.count D = (d.toList.count D - 1) + 1 by omega,
        Finset.sum_range_succ]
      simp only [hlast, ↓reduceIte, Nat.add_zero, heq]
  have incBlocks_ascent_iff_no_cut (n : ℕ) (ks : List ℕ)
      (hpos : ∀ k ∈ ks, 0 < k) (hsum : ks.sum = n)
      (t : ℕ) (ht : t + 1 < n) :
      (incBlocks n ks)[t]'(by
        have length_eq (size : ℕ) (blocks : List ℕ) :
            (incBlocks size blocks).length = blocks.sum := by
          induction blocks generalizing size <;> simp [incBlocks, *]
        have hl := length_eq n ks; rw [hsum] at hl
        omega) <
      (incBlocks n ks)[t + 1]'(by
        have length_eq (size : ℕ) (blocks : List ℕ) :
            (incBlocks size blocks).length = blocks.sum := by
          induction blocks generalizing size <;> simp [incBlocks, *]
        have hl := length_eq n ks; rw [hsum] at hl
        omega) ↔
        ∀ r : ℕ, 0 < r → r < ks.length → (ks.take r).sum ≠ t + 1 := by
    have incBlocks_perm (n : ℕ) (ks : List ℕ)
        (hpos : ∀ k ∈ ks, 0 < k) (hsum : ks.sum = n) :
        (incBlocks n ks).Perm (List.range' 1 n) := by
      induction ks generalizing n with
      | nil =>
        have hn : n = 0 := by simpa using hsum.symm
        simp [incBlocks, hn]
      | cons k ks ih =>
        have hk : 0 < k := hpos k (by simp)
        have hpos' : ∀ x ∈ ks, 0 < x := by
          intro x hx; exact hpos x (by simp [hx])
        have hsum' : ks.sum = n - k := by
          simp only [List.sum_cons] at hsum; omega
        have hkn : k ≤ n := by
          simp only [List.sum_cons] at hsum; omega
        have htail := ih (n - k) hpos' hsum'; have hrange : List.range' 1 n =
            List.range' 1 (n - k) ++ List.range' (n - k + 1) k := by
          have hn : n - k + k = n := by omega
          simpa [hn, Nat.add_comm] using
            (List.range'_append (s := 1) (m := n - k) (n := k) (step := 1)).symm
        change (List.range' (n - k + 1) k ++ incBlocks (n - k) ks).Perm
          (List.range' 1 n)
        refine (htail.append_left _).trans ?_
        rw [hrange]; exact List.perm_append_comm
    induction ks generalizing n t with
    | nil =>
      simp at hsum; omega
    | cons k ks ih =>
      have hk : 0 < k := hpos k (by simp)
      have hpos' : ∀ x ∈ ks, 0 < x := by
        intro x hx; exact hpos x (by simp [hx])
      have hsum' : ks.sum = n - k := by
        simp only [List.sum_cons] at hsum; omega
      have hkn : k ≤ n := by
        simp only [List.sum_cons] at hsum; omega
      let q := incBlocks (n - k) ks; have hqperm : q.Perm (List.range' 1 (n - k)) :=
        incBlocks_perm (n - k) ks hpos' hsum'
      have hqlen : q.length = n - k := by simpa [q] using hqperm.length_eq
      have hlen : (incBlocks n (k :: ks)).length = n := by
        simp [incBlocks, q, hqlen]; omega
      by_cases hlt : t + 1 < k
      · have ht0 : t < k := by omega
        have hval0 : (incBlocks n (k :: ks))[t] = n - k + 1 + t := by
          simp [incBlocks, ht0]
        have hval1 : (incBlocks n (k :: ks))[t + 1] = n - k + 1 + (t + 1) := by
          simp [incBlocks, hlt]
        constructor
        · intro _ r hr hrlen heq
          obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
          simp only [List.take_succ_cons, List.sum_cons] at heq; omega
        · intro _
          rw [hval0, hval1]; omega
      · by_cases heq : t + 1 = k
        · have ht0 : t < k := by omega
          have hqpos : 0 < q.length := by rw [hqlen]; omega
          have hval0 : (incBlocks n (k :: ks))[t] = n := by
            simp [incBlocks, ht0]; omega
          have hval1 : (incBlocks n (k :: ks))[t + 1] = q[0] := by
            simp [incBlocks, heq, q]
          have hqval : q[0] ≤ n - k := by
            have hm := hqperm.subset (List.getElem_mem hqpos); have hr := List.mem_range'_1.mp hm
            omega
          constructor
          · intro hasc
            rw [hval0, hval1] at hasc; omega
          · intro hall
            have hcut : ((k :: ks).take 1).sum = t + 1 := by simp [heq]
            have hrest : 1 < (k :: ks).length := by
              cases ks with
              | nil => simp [q, incBlocks] at hqpos
              | cons a as => simp
            exact False.elim ((hall 1 (by omega) hrest) hcut)
        · have hkt : k < t + 1 := by omega
          have htk : k ≤ t := by omega
          have htq : t - k + 1 < n - k := by omega
          have hval0 : (incBlocks n (k :: ks))[t] = q[t - k] := by
            simp [incBlocks, List.getElem_append, show ¬ t < k by omega, q]
          have hval1 : (incBlocks n (k :: ks))[t + 1] = q[t - k + 1] := by
            have heq' : t + 1 - k = t - k + 1 := by omega
            simp [incBlocks, List.getElem_append,
              show ¬ t + 1 < k by omega, q, heq']
          have hcuts :
              (∀ r : ℕ, 0 < r → r < (k :: ks).length →
                ((k :: ks).take r).sum ≠ t + 1) ↔
              (∀ r : ℕ, 0 < r → r < ks.length →
                (ks.take r).sum ≠ (t - k) + 1) := by
            constructor
            · intro hall r hr hrlen hbad
              have hfull := hall (r + 1) (by omega) (by simpa using hrlen)
              simp only [List.take_succ_cons, List.sum_cons] at hfull; apply hfull; omega
            · intro hall r hr hrlen hbad
              obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
              simp only [List.take_succ_cons, List.sum_cons] at hbad
              by_cases hs : s = 0
              · subst s
                simp at hbad; omega
              · have hspos : 0 < s := by omega
                have hslen : s < ks.length := by simpa using hrlen
                exact (hall s hspos hslen) (by omega)
          rw [hval0, hval1, hcuts]; exact ih (n - k) hpos' hsum' (t - k) htq
  have indexed_downstep_gap (s : List DyckStep) (k : ℕ)
      (hk : k + 1 < s.count D) :
      ∃ u v z : List DyckStep,
        s = u ++ [D] ++ v ++ [D] ++ z ∧
        v.count D = 0 ∧ u.count D = k := by
    have firstD : ∀ (t : List DyckStep), 0 < t.count D →
        ∃ v z : List DyckStep, t = v ++ D :: z ∧ v.count D = 0 := by
      intro t
      induction t with
      | nil => simp
      | cons a t ih =>
        cases a with
        | D =>
          intro _; exact ⟨[], t, rfl, rfl⟩
        | U =>
          intro h
          have ht : 0 < t.count D := by simpa using h
          obtain ⟨v, z, hv, hzero⟩ := ih ht
          exact ⟨U :: v, z, by simp [hv], by simpa using hzero⟩
    induction s generalizing k with
    | nil => simp at hk
    | cons a s ih =>
      cases a with
      | U =>
        have hs : k + 1 < s.count D := by simpa using hk
        obtain ⟨u, v, z, hsplit, hzero, hcount⟩ := ih k hs
        exact ⟨U :: u, v, z, by simp [hsplit], hzero, by simpa using hcount⟩
      | D =>
        cases k with
        | zero =>
          have hs : 0 < s.count D := by simpa using hk
          obtain ⟨v, z, hsplit, hzero⟩ := firstD s hs
          exact ⟨[], v, z, by simp [hsplit], hzero, rfl⟩
        | succ k =>
          have hs : k + 1 < s.count D := by simpa using hk
          obtain ⟨u, v, z, hsplit, hzero, hcount⟩ := ih k hs
          exact ⟨D :: u, v, z, by simp [hsplit], hzero, by simpa using hcount⟩
  have incBlocks_perm (n : ℕ) (ks : List ℕ)
      (hpos : ∀ k ∈ ks, 0 < k) (hsum : ks.sum = n) :
      (incBlocks n ks).Perm (List.range' 1 n) := by
    induction ks generalizing n with
    | nil =>
      have hn : n = 0 := by simpa using hsum.symm
      simp [incBlocks, hn]
    | cons k ks ih =>
      have hk : 0 < k := hpos k (by simp)
      have hpos' : ∀ x ∈ ks, 0 < x := by
        intro x hx; exact hpos x (by simp [hx])
      have hsum' : ks.sum = n - k := by
        simp only [List.sum_cons] at hsum; omega
      have hkn : k ≤ n := by
        simp only [List.sum_cons] at hsum; omega
      have htail := ih (n - k) hpos' hsum'; have hrange : List.range' 1 n =
          List.range' 1 (n - k) ++ List.range' (n - k + 1) k := by
        have hn : n - k + k = n := by omega
        simpa [hn, Nat.add_comm] using
          (List.range'_append (s := 1) (m := n - k) (n := k) (step := 1)).symm
      change (List.range' (n - k + 1) k ++ incBlocks (n - k) ks).Perm
        (List.range' 1 n)
      refine (htail.append_left _).trans ?_
      rw [hrange]; exact List.perm_append_comm
  let lowPatterns : List (List ℕ) := [[1, 1, 3, 2], [2, 2, 1, 3]]
  let baseSet (n : ℕ) : Set (List ℕ) := {w | w ∈ avoiders n []}
  let lowSet (n : ℕ) : Set (List ℕ) := {w | w ∈ avoiders n lowPatterns}
  let lowWords (n : ℕ) : Type :=
    {x : {w : List ℕ // w ∈ baseSet n} // x.1 ∈ lowSet n}
  let shapeOf (n : ℕ) (x : lowWords n) : DyckWord :=
    ((royalEncoding n).symm ⟨x.1.1, x.1.2⟩).1.2
  have goodPositions_iff_factors (n : ℕ) (d : DyckWord)
      (hd : d.semilength = n) (i : Fin (n - 1)) :
      i ∈ goodPositions n d ↔
        (∃ u z : List DyckStep,
          d.toList = u ++ [D, D] ++ z ∧ u.count D = i.val) ∨
        (∃ u z : List DyckStep,
          d.toList = u ++ [D, U, D] ++ z ∧
            u.count D = i.val ∧ u.count U = u.count D + 1) := by
    have goodPositions_gap_iff (n : ℕ) (d : DyckWord) (i : Fin (n - 1))
        (u v z : List DyckStep)
        (hsplit : d.toList = u ++ [D] ++ v ++ [D] ++ z)
        (hnoD : v.count D = 0) (hindex : u.count D = i.val) :
        i ∈ goodPositions n d ↔
          v = [] ∨ (v = [U] ∧ u.count U = u.count D + 1) := by
      have unique : ∀ (a b a' b' : List DyckStep),
          a ++ D :: b = a' ++ D :: b' →
          a.count D = a'.count D → a = a' ∧ b = b' := by
        intro a
        induction a with
        | nil =>
          intro b a' b' he hc
          cases a' with
          | nil =>
            simp only [List.nil_append, List.cons.injEq] at he; exact ⟨rfl, he.2⟩
          | cons x xs =>
            have hx : x = D := by
              have h := congrArg List.head? he
              simpa using h.symm
            subst x; simp at hc
        | cons x xs ih =>
          intro b a' b' he hc
          cases a' with
          | nil =>
            have hx : x = D := by
              have h := congrArg List.head? he
              simpa using h
            subst x; simp at hc
          | cons y ys =>
            have hxy : x = y := by
              have h := congrArg List.head? he
              simpa using h
            subst y
            have htail : xs ++ D :: b = ys ++ D :: b' := by
              simpa using he
            have hcounts : xs.count D = ys.count D := by
              simp only [List.count_cons] at hc; omega
            obtain ⟨hpre, hsuf⟩ := ih b ys b' htail hcounts
            exact ⟨by rw [hpre], hsuf⟩
      constructor
      · intro hi
        exact (Finset.mem_filter.mp hi).2 u v z hsplit hnoD hindex
      · intro hgood
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        intro u' v' z' hsplit' hnoD' hindex'
        have he : u ++ D :: (v ++ D :: z) = u' ++ D :: (v' ++ D :: z') := by
          simpa [List.append_assoc] using hsplit.symm.trans hsplit'
        obtain ⟨hu, htail⟩ := unique u (v ++ D :: z) u' (v' ++ D :: z') he
          (hindex.trans hindex'.symm)
        have hv : v = v' :=
          (unique v z v' z' htail (hnoD.trans hnoD'.symm)).1
        subst u'; subst v'; exact hgood
    have hk : i.val + 1 < d.toList.count D := by
      rw [← d.semilength_eq_count_D, hd]; have hi := i.isLt; omega
    obtain ⟨u, v, z, hsplit, hnoD, hindex⟩ := indexed_downstep_gap d.toList i.val hk
    rw [goodPositions_gap_iff n d i u v z hsplit hnoD hindex]
    constructor
    · intro h
      rcases h with hnil | ⟨hsingle, hground⟩
      · left
        exact ⟨u, z, by simpa [hnil] using hsplit, hindex⟩
      · right
        exact ⟨u, z, by simpa [hsingle] using hsplit, hindex, hground⟩
    · intro h
      rcases h with ⟨u', z', hsplit', hindex'⟩ |
        ⟨u', z', hsplit', hindex', hground'⟩
      · have h := (goodPositions_gap_iff n d i u' [] z'
          (by simpa using hsplit') (by simp) hindex').mpr (Or.inl rfl)
        exact (goodPositions_gap_iff n d i u v z hsplit hnoD hindex).mp h
      · have h := (goodPositions_gap_iff n d i u' [U] z'
          (by simpa using hsplit') (by simp) hindex').mpr
            (Or.inr ⟨rfl, hground'⟩)
        exact (goodPositions_gap_iff n d i u v z hsplit hnoD hindex).mp h
  have royal_root_of_down_bridge (A R : PowerSeries ℤ)
      (hA : 1 - (1 + X) * A + 2 * X * A ^ 2 = 0)
      (hbridge : (1 - 2 * X * A) * R = 1 - X) :
      X * R ^ 2 - (1 - X) ^ 2 * R + (1 - X) ^ 2 = 0 := by
    let B : PowerSeries ℤ := 1 - 2 * X * A; let C : PowerSeries ℤ := 1 - X
    let E : PowerSeries ℤ := X * R ^ 2 - C ^ 2 * R + C ^ 2
    have hBR : B * R = C := by simpa [B, C] using hbridge
    have hpoly : X - B * C + B ^ 2 =
        2 * X * (1 - (1 + X) * A + 2 * X * A ^ 2) := by
      dsimp [B, C]; ring
    have hzero : X - B * C + B ^ 2 = 0 := by rw [hpoly, hA]; ring
    have hmul : B ^ 2 * E = 0 := by
      change B ^ 2 * (X * R ^ 2 - C ^ 2 * R + C ^ 2) = 0
      calc
        B ^ 2 * (X * R ^ 2 - C ^ 2 * R + C ^ 2) =
            B ^ 2 * (X * R ^ 2) - B ^ 2 * (C ^ 2 * R) + B ^ 2 * C ^ 2 := by ring
        _ =
            C ^ 2 * (X - B * C + B ^ 2) := by
              rw [← hBR]; ring
        _ = 0 := by rw [hzero]; ring
    have hBunit : IsUnit B := by
      rw [PowerSeries.isUnit_iff_constantCoeff]; simp [B]
    have hE : E = 0 := (hBunit.pow 2).mul_left_cancel (by simpa using hmul)
    simpa [E, C] using hE
  have low_fiber_card (n : ℕ) (d : DyckWord) (hd : d.semilength = n) :
      Nat.card {x : {w : List ℕ // w ∈ avoiders n []} //
        ((royalEncoding n).symm x).1.2 = d ∧
        x.1 ∈ avoiders n [[1, 1, 3, 2], [2, 2, 1, 3]]} =
        2 ^ (goodPositions n d).card := by
    let good := goodPositions n d
    let C := {c : Composition n //
      ∀ t (ht : t + 1 < n),
        (incBlocks n c.blocks)[t]'(by
          have hl := (incBlocks_perm n c.blocks (fun _ h => c.blocks_pos h)
            c.blocks_sum).length_eq
          simp only [List.length_range'] at hl
          omega) <
        (incBlocks n c.blocks)[t + 1]'(by
          have hl := (incBlocks_perm n c.blocks (fun _ h => c.blocks_pos h)
            c.blocks_sum).length_eq
          simp only [List.length_range'] at hl
          omega) → (⟨t, by omega⟩ : Fin (n - 1)) ∈ good}
    let W := {pd : royalPairs n // pd.1.2 = d ∧
      (royalEncoding n pd).1 ∈ avoiders n [[1, 1, 3, 2], [2, 2, 1, 3]]}
    let Y := {x : {w : List ℕ // w ∈ avoiders n []} //
      ((royalEncoding n).symm x).1.2 = d ∧
      x.1 ∈ avoiders n [[1, 1, 3, 2], [2, 2, 1, 3]]}
    have hforced :
        Fintype.card {c : Composition n //
          ∀ i : Fin (n - 1), i ∉ good →
            i ∈ compositionAsSetEquiv n ((compositionEquiv n) c)} =
          2 ^ good.card := by
      let e : Composition n ≃ Finset (Fin (n - 1)) :=
        (compositionEquiv n).trans (compositionAsSetEquiv n)
      let bad : Finset (Fin (n - 1)) := Finset.univ \ good
      have he : {c : Composition n // ∀ i : Fin (n - 1), i ∉ good → i ∈ e c} ≃
          {s : Finset (Fin (n - 1)) // s ∈ Finset.Icc bad Finset.univ} :=
        { toFun := fun c => ⟨e c.1, by
            simp only [Finset.mem_Icc, Finset.subset_univ, and_true]; intro i hi
            exact c.2 i ((Finset.mem_sdiff.mp hi).2)⟩
          invFun := fun s => ⟨e.symm s.1, by
            intro i hi; have hs : bad ⊆ s.1 := (Finset.mem_Icc.mp s.2).1
            have hbad : i ∈ bad := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩
            simpa using hs hbad⟩
          left_inv := by intro c; apply Subtype.ext; simp
          right_inv := by intro s; apply Subtype.ext; simp }
      have hcard : Fintype.card {c : Composition n //
          ∀ i : Fin (n - 1), i ∉ good → i ∈ e c} =
          (Finset.Icc bad Finset.univ).card := by
        exact (Fintype.card_congr he).trans (Fintype.card_coe _)
      have hbad : (Finset.univ : Finset (Fin (n - 1))).card - bad.card = good.card := by
        rw [show bad.card = (Finset.univ : Finset (Fin (n - 1))).card - good.card from
          Finset.card_sdiff_of_subset (Finset.subset_univ good)]
        have hle := Finset.card_le_card (Finset.subset_univ good); omega
      change Fintype.card {c : Composition n //
        ∀ i : Fin (n - 1), i ∉ good → i ∈ e c} = 2 ^ good.card
      exact hcard.trans
        ((Finset.card_Icc_finset (Finset.subset_univ bad)).trans (congrArg (2 ^ ·) hbad))
    have hcountAllowed :
        Fintype.card {c : Composition n //
          ∀ t (ht : t + 1 < n),
            (incBlocks n c.blocks)[t]'(by
              have hl := (incBlocks_perm n c.blocks (fun _ h => c.blocks_pos h)
                c.blocks_sum).length_eq
              simp only [List.length_range'] at hl
              omega) <
            (incBlocks n c.blocks)[t + 1]'(by
              have hl := (incBlocks_perm n c.blocks (fun _ h => c.blocks_pos h)
                c.blocks_sum).length_eq
              simp only [List.length_range'] at hl
              omega) →
            (⟨t, by omega⟩ : Fin (n - 1)) ∈ good} = 2 ^ good.card := by
      let e : Composition n ≃ Finset (Fin (n - 1)) :=
        (compositionEquiv n).trans (compositionAsSetEquiv n)
      have hcut (c : Composition n) (t : ℕ) (ht : t + 1 < n) :
          (⟨t, by omega⟩ : Fin (n - 1)) ∈ e c ↔
            ∃ r : ℕ, 0 < r ∧ r < c.blocks.length ∧ (c.blocks.take r).sum = t + 1 := by
        change (⟨t, by omega⟩ : Fin (n - 1)) ∈
          compositionAsSetEquiv n c.toCompositionAsSet ↔ _
        simp only [compositionAsSetEquiv, Equiv.coe_fn_mk, Set.toFinset_ofPred,
          Finset.mem_filter, Finset.mem_univ, true_and]
        rw [c.toCompositionAsSet.mem_boundaries_iff_exists_blocks_sum_take_eq]
        rw [c.toCompositionAsSet_blocks, c.toCompositionAsSet_boundaries,
          c.card_boundaries_eq_succ_length]
        constructor
        · rintro ⟨r, hr, heq⟩
          change r < c.blocks.length + 1 at hr
          have hr0 : 0 < r := by
            by_contra h
            have : r = 0 := by omega
            subst r; simp at heq; omega
          have hrl : r < c.blocks.length := by
            by_contra h
            have : r = c.blocks.length := by omega
            subst r; simp [c.blocks_sum] at heq; omega
          exact ⟨r, hr0, hrl, by simpa [Nat.add_comm] using heq⟩
        · rintro ⟨r, hr0, hrl, heq⟩
          exact ⟨r, by change r < c.blocks.length + 1; omega,
            by simpa [Nat.add_comm] using heq⟩
      have hpred (c : Composition n) :
          (∀ t (ht : t + 1 < n),
            (incBlocks n c.blocks)[t]'(by
              have hl := (incBlocks_perm n c.blocks (fun _ h => c.blocks_pos h)
                c.blocks_sum).length_eq
              simp only [List.length_range'] at hl
              omega) <
            (incBlocks n c.blocks)[t + 1]'(by
              have hl := (incBlocks_perm n c.blocks (fun _ h => c.blocks_pos h)
                c.blocks_sum).length_eq
              simp only [List.length_range'] at hl
              omega) → (⟨t, by omega⟩ : Fin (n - 1)) ∈ good) ↔
          (∀ i : Fin (n - 1), i ∉ good → i ∈ e c) := by
        constructor
        · intro h i hi
          by_contra hnot
          have hasc := (incBlocks_ascent_iff_no_cut n c.blocks
            (fun _ h => c.blocks_pos h) c.blocks_sum i.val (by omega)).2
          have : ∀ r : ℕ, 0 < r → r < c.blocks.length →
              (c.blocks.take r).sum ≠ i.val + 1 := by
            intro r hr0 hrl heq; apply hnot; exact (hcut c i.val (by omega)).2 ⟨r, hr0, hrl, heq⟩
          exact hi (h i.val (by omega) (hasc this))
        · intro h t ht hasc
          by_contra hnot
          have hmem := h (⟨t, by omega⟩ : Fin (n - 1)) hnot
          obtain ⟨r, hr0, hrl, heq⟩ := (hcut c t ht).1 hmem
          have hnocut := (incBlocks_ascent_iff_no_cut n c.blocks
            (fun _ h => c.blocks_pos h) c.blocks_sum t ht).1 hasc
          exact hnocut r hr0 hrl heq
      have hcard := hforced
      change Fintype.card {c : Composition n //
        ∀ i : Fin (n - 1), i ∉ good → i ∈ e c} = 2 ^ good.card at hcard
      let f : {c : Composition n //
          ∀ t (ht : t + 1 < n),
            (incBlocks n c.blocks)[t]'(by
              have hl := (incBlocks_perm n c.blocks (fun _ h => c.blocks_pos h)
                c.blocks_sum).length_eq
              simp only [List.length_range'] at hl
              omega) <
            (incBlocks n c.blocks)[t + 1]'(by
              have hl := (incBlocks_perm n c.blocks (fun _ h => c.blocks_pos h)
                c.blocks_sum).length_eq
              simp only [List.length_range'] at hl
              omega) → (⟨t, by omega⟩ : Fin (n - 1)) ∈ good} ≃
          {c : Composition n // ∀ i : Fin (n - 1), i ∉ good → i ∈ e c} :=
        Equiv.subtypeEquiv (Equiv.refl _) (by intro c; exact hpred c)
      exact (Fintype.card_congr f).trans hcard
    have equivalence := lowFiberEncoding n d hd; change C ≃ Y at equivalence
    calc
      Nat.card Y = Nat.card C := (Nat.card_congr equivalence).symm
      _ = Fintype.card C := Nat.card_eq_fintype_card
      _ = 2 ^ good.card := by
        change Fintype.card C = 2 ^ good.card at hcountAllowed; exact hcountAllowed
  have low_total_card (n : ℕ) :
      (avoiders n [[1, 1, 3, 2], [2, 2, 1, 3]]).ncard =
        ∑ d : {d : DyckWord // d.semilength = n},
          2 ^ (goodPositions n d.1).card := by
    have hbaseFinite (m : ℕ) : (baseSet m).Finite := by
      let base : List ℕ := (List.range' 1 m).flatMap (fun i => [i, i])
      have hfin : {w : List ℕ | w ∈ base.permutations}.Finite := by
        simpa using (Set.finite_mem_finset base.permutations.toFinset)
      apply hfin.subset; intro w hw; change w ∈ avoiders m [] at hw
      simpa [base, List.mem_permutations] using hw.1
    have hlowFinite (m : ℕ) : (lowSet m).Finite := by
      apply (hbaseFinite m).subset; intro w hw; change w ∈ avoiders m lowPatterns at hw
      change w ∈ avoiders m []; exact ⟨hw.1, hw.2.1, hw.2.2.1, by simp⟩
    letI : Fintype {w : List ℕ // w ∈ baseSet n} := (hbaseFinite n).fintype
    letI : Fintype (lowWords n) := by
      change Fintype {x : {w : List ℕ // w ∈ baseSet n} // x.1 ∈ lowSet n}
      infer_instance
    letI : Fintype (lowSet n) := (hlowFinite n).fintype
    letI : Fintype {d : DyckWord // d.semilength = n} := inferInstance
    let shapeKey : lowWords n → {d : DyckWord // d.semilength = n} := fun x =>
      ⟨shapeOf n x, by
        change ((royalEncoding n).symm ⟨x.1.1, x.1.2⟩).1.2.semilength = n
        have hp := ((royalEncoding n).symm ⟨x.1.1, x.1.2⟩).2.1
        have hpl : ((royalEncoding n).symm ⟨x.1.1, x.1.2⟩).1.1.length = n := by
          simpa using hp.length_eq
        calc
          ((royalEncoding n).symm ⟨x.1.1, x.1.2⟩).1.2.semilength =
              ((royalEncoding n).symm ⟨x.1.1, x.1.2⟩).1.1.length :=
            ((royalEncoding n).symm ⟨x.1.1, x.1.2⟩).2.2.symm
          _ = n := hpl⟩
    let fiber : {d : DyckWord // d.semilength = n} → Type := fun d =>
      {x : lowWords n // shapeKey x = d}
    letI : (d : {d : DyckWord // d.semilength = n}) → Fintype (fiber d) := fun d => by
      exact Fintype.ofFinite (fiber d)
    let sigma : Type := Σ d : {d : DyckWord // d.semilength = n}, fiber d
    let e : sigma ≃ lowWords n := Equiv.sigmaFiberEquiv shapeKey
    have hcard : Nat.card (lowWords n) =
        ∑ d : {d : DyckWord // d.semilength = n}, Nat.card (fiber d) := by
      rw [← Nat.card_congr e, Nat.card_sigma]
    have hfiber (d : {d : DyckWord // d.semilength = n}) :
        Nat.card (fiber d) = 2 ^ (goodPositions n d.1).card := by
      let old : Type := {x : {w : List ℕ // w ∈ avoiders n []} //
        ((royalEncoding n).symm x).1.2 = d.1 ∧
        x.1 ∈ avoiders n lowPatterns}
      let new : Type := fiber d; let q : old ≃ new :=
        { toFun := fun x =>
            ⟨⟨x.1, x.2.2⟩, by
              apply Subtype.ext; exact x.2.1⟩
          invFun := fun x =>
            ⟨x.1.1, ⟨congrArg Subtype.val x.2, x.1.2⟩⟩
          left_inv := by
            intro x; apply Subtype.ext; apply Subtype.ext; rfl
          right_inv := by
            intro x; apply Subtype.ext
            rfl }
      rw [← Nat.card_congr q]; exact low_fiber_card n d.1 d.2
    let eLow : lowWords n ≃ lowSet n :=
      { toFun := fun x => ⟨x.1.1, x.2⟩
        invFun := fun w =>
          ⟨⟨w.1, by
            change w.1 ∈ avoiders n []; exact ⟨w.2.1, w.2.2.1, w.2.2.2.1, by simp⟩⟩, w.2⟩
        left_inv := by intro x; rfl
        right_inv := by intro w; rfl }
    have hlowCard : (lowSet n).ncard = Nat.card (lowWords n) := by
      calc
        (lowSet n).ncard = Fintype.card (lowSet n) :=
          (Set.fintypeCard_eq_ncard (s := lowSet n)).symm
        _ = Nat.card (lowSet n) := by rw [Nat.card_eq_fintype_card]
        _ = Nat.card (lowWords n) := (Nat.card_congr eLow).symm
    have hfinal : (lowSet n).ncard =
        ∑ d : {d : DyckWord // d.semilength = n},
          2 ^ (goodPositions n d.1).card := by
      rw [hlowCard, hcard]; apply Finset.sum_congr rfl; intro d hd; exact hfiber d
    simpa [lowSet, lowPatterns] using hfinal
  have hweight (n : ℕ) (d : DyckWord) (hd : d.semilength = n) :
      (goodPositions n d).card = downPairs d.toList + groundSingletons d := by
    let flat (k : ℕ) : Prop := ∃ u z : List DyckStep,
      d.toList = u ++ [D, D] ++ z ∧ u.count D = k
    let ground (k : ℕ) : Prop := ∃ u z : List DyckStep,
      d.toList = u ++ [D, U, D] ++ z ∧ u.count D = k ∧
        u.count U = u.count D + 1
    have hdisjoint (k : ℕ) : flat k → ¬ ground k := by
      rintro ⟨u, z, hu, hk⟩ ⟨v, t, hv, hvk, _⟩
      have he : u ++ D :: D :: z = v ++ D :: U :: D :: t := by
        simpa using hu.symm.trans hv
      rcases List.append_eq_append_iff.mp he with ⟨r, hr, he⟩ | ⟨r, hr, he⟩
      · have hc : r.count D = 0 := by
          have hc := congrArg (List.count D) hr; simp only [List.count_append] at hc; omega
        cases r with
        | nil => simp at he
        | cons a r =>
          have ha : a = D := by
            have hh := congrArg List.head? he
            simpa using hh.symm
          subst a; simp at hc
      · have hc : r.count D = 0 := by
          have hc := congrArg (List.count D) hr; simp only [List.count_append] at hc; omega
        cases r with
        | nil => simp at he
        | cons a r =>
          have ha : a = D := by
            have hh := congrArg List.head? he
            simpa using hh.symm
          subst a; simp at hc
    have hcard : (goodPositions n d).card =
        ∑ i : Fin (n - 1), if i ∈ goodPositions n d then 1 else 0 := by
      symm; simp
    have hsplit (i : Fin (n - 1)) :
        (if i ∈ goodPositions n d then 1 else 0) =
          (if flat i.val then 1 else 0) + (if ground i.val then 1 else 0) := by
      simp only [goodPositions_iff_factors n d hd i]
      change (if flat i.val ∨ ground i.val then 1 else 0) = _
      by_cases hf : flat i.val
      · have hg : ¬ ground i.val := hdisjoint i.val hf
        simp [hf, hg]
      · by_cases hg : ground i.val <;> simp [hf, hg]
    rw [hcard]
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib,
      Fin.sum_univ_eq_sum_range (fun k => if flat k then 1 else 0),
      Fin.sum_univ_eq_sum_range (fun k => if ground k then 1 else 0),
      downPairs_eq_flat_sum, groundSingletons_eq_ground_sum]
    have hcount : d.toList.count D = n := d.semilength_eq_count_D.symm.trans hd; rw [hcount]
  have hseries : NonnestingDefs.gf [[1, 1, 3, 2], [2, 2, 1, 3]] = groundSeries := by
    apply PowerSeries.ext; intro n
    simp only [NonnestingDefs.gf, groundSeries, PowerSeries.coeff_mk]; rw [low_total_card]; congr 1
    unfold groundWeight; apply Fintype.sum_congr; intro d; rw [hweight n d.1 d.2]
  change NonnestingDefs.IsRoyalRoot _; rw [hseries]
  exact royal_root_of_down_bridge downSeries groundSeries
    downSeries_quadratic groundSeries_bridge
#print axioms result

end D5.S3.Combinatorics.Nonnesting.NonnestingRoyalLow
