/- GID: D5/S3/Arith/FibonacciAtomic/TreePeakHeightFrontier
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/TreePeakHeightFrontier
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Nat.Log]
   utility: none
   digest: Ordered binary interval trees control complete-message peaks and dependency heights. -/

import D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity
import D5.S3.Arith.FibonacciAtomic.TreeMessageRealization
import D5.S3.Arith.FibonacciAtomic.BalancedIntervalTree
import D5.S3.Arith.FibonacciAtomic.FourMessageTreeRigidity
import Mathlib.Data.Nat.Log

set_option autoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.Arith.FibonacciAtomic.TreePeakHeightFrontier

open FirstRejectionCutCapacity (task interval Cross Internal crossings internals d c delta)
open TreeMessageRealization (Tree leaf fork leaves Full subtrees height optimum)
open D5.S3.Observer.Separation.SurjectiveColumnSharpWidth (capacity)
open LiteralWindowEnd (Window)
open scoped BigOperators

/-- Exact attainable peaks and heights for the first-rejection task, including
the obstruction at powers of two and the unrestricted subset lower bound. -/
theorem result (k : ℕ) :
    let n := k + 1
    let H := Nat.clog 2 n
    let exceptional := 4 ≤ n ∧ n = 2 ^ H
    (∀ A : Finset (Fin (k + 1)), (0 : Fin (k + 1)) ∉ A → 2 ≤ A.card →
      2 * A.card + 2 ≤ capacity (fun _ : Fin (k + 1) => Window) task (fun i => i ∈ A)) ∧
    (∀ t : TreeMessageRealization.Tree (Fin (k + 1)), Full t → leaves t = Finset.univ →
      optimum task t = (subtrees t).sup
        (fun s => capacity (fun _ : Fin (k + 1) => Window) task (fun i => i ∈ leaves s)) ∧
      n + 1 ≤ optimum task t ∧ H ≤ height t) ∧
    (∃ t : TreeMessageRealization.Tree (Fin (k + 1)), Full t ∧ leaves t = Finset.univ ∧
      optimum task t = n + 1 ∧ height t = (if exceptional then H + 1 else H)) ∧
    (∀ t : TreeMessageRealization.Tree (Fin (k + 1)), Full t → leaves t = Finset.univ →
      optimum task t = n + 1 → (if exceptional then H + 1 else H) ≤ height t) ∧
    (∃ t : TreeMessageRealization.Tree (Fin (k + 1)), Full t ∧ leaves t = Finset.univ ∧
      height t = H ∧ optimum task t = (if exceptional then n + 2 else n + 1)) ∧
    (∀ t : TreeMessageRealization.Tree (Fin (k + 1)), Full t → leaves t = Finset.univ →
      height t = H → (if exceptional then n + 2 else n + 1) ≤ optimum task t) := by
  classical
  letI : DecidableEq (Fin (k + 1)) := Classical.decEq _
  letI : Nonempty Window := ⟨.middle⟩
  dsimp only
  let n := k + 1
  let H := Nat.clog 2 n
  let exceptional := 4 ≤ n ∧ n = 2 ^ H
  let cap : Finset (Fin (k + 1)) → ℕ :=
    fun A => capacity (fun _ : Fin (k + 1) => Window) task (fun i => i ∈ A)
  have subset_lower (A : Finset (Fin (k + 1)))
      (hzero : (0 : Fin (k + 1)) ∉ A) (hcard : 2 ≤ A.card) :
      2 * A.card + 2 ≤ cap A := by
    have count : 2 * A.card = d A + 2 * (internals A).card +
        (if Fin.last k ∈ A then 1 else 0) := by
      let bit : Fin (k + 1) → ℕ := fun i => if i ∈ A then 1 else 0
      have sum_bit : ∑ i, bit i = A.card := by
        simp [bit]
      have bit_zero : bit 0 = 0 := by simp [bit, hzero]
      have pair (i : Fin k) : bit i.castSucc + bit i.succ =
          (if Cross A i then 1 else 0) + 2 * (if Internal A i then 1 else 0) := by
        by_cases hl : i.castSucc ∈ A <;> by_cases hr : i.succ ∈ A <;>
          simp [bit, Cross, Internal, FirstRejectionCutCapacity.left,
            FirstRejectionCutCapacity.right, hl, hr]
      have sum_pair := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ)
        rfl (fun i _ => pair i)
      have left_sum := Fin.sum_univ_castSucc bit
      have right_sum := Fin.sum_univ_succ bit
      have cross_sum : (∑ i : Fin k, if Cross A i then 1 else 0) = d A := by
        simp [d, crossings]
      have internal_sum : (∑ i : Fin k, if Internal A i then 1 else 0) =
          (internals A).card := by
        simp [internals]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, cross_sum, internal_sum] at sum_pair
      simp only [sum_bit, bit_zero, zero_add] at left_sum right_sum
      have bit_last : bit (Fin.last k) = (if Fin.last k ∈ A then 1 else 0) := rfl
      rw [bit_last] at left_sum
      omega
    have hA : A.Nonempty := Finset.card_pos.mp (by omega)
    let u := A.min' hA
    have hu : u ∈ A := A.min'_mem hA
    have hu0 : 0 < u.val := by
      by_contra hh
      have huv : u.val = 0 := by omega
      have he : u = 0 := Fin.ext (by simpa using huv)
      exact hzero (he ▸ hu)
    let entry : Fin k := ⟨u.val - 1, by omega⟩
    have hentry : entry ∈ crossings A := by
      have hleft : entry.castSucc ∉ A := by
        intro hh
        have hle := A.min'_le _ hh
        have hle' : u.val ≤ entry.val := hle
        dsimp [entry] at hle'
        omega
      have hright : entry.succ = u := Fin.ext (by dsimp [entry]; omega)
      simp only [crossings, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inr ⟨hleft, by simpa [FirstRejectionCutCapacity.right, hright] using hu⟩
    have hd1 : 1 ≤ d A := by
      exact Finset.card_pos.mpr ⟨entry, hentry⟩
    have sum_lower : 2 * (internals A).card ≤ ∑ j ∈ internals A, 2 ^ c A j := by
      calc
        2 * (internals A).card = ∑ _j ∈ internals A, (2 : ℕ) := by simp [Nat.mul_comm]
        _ ≤ ∑ j ∈ internals A, 2 ^ c A j := by
          apply Finset.sum_le_sum
          intro j hj
          have hjA : j.castSucc ∈ A := by
            simpa [internals, Internal, FirstRejectionCutCapacity.left,
              FirstRejectionCutCapacity.right] using (Finset.mem_filter.mp hj).2.1
          have huj : u.val ≤ j.val := A.min'_le _ hjA
          have hc : 1 ≤ c A j := by
            apply Finset.card_pos.mpr
            refine ⟨entry, Finset.mem_filter.mpr ⟨hentry, ?_⟩⟩
            dsimp [entry]
            omega
          simpa using (Nat.pow_le_pow_right (by decide : 0 < 2) hc)
    have cap_formula := (FirstRejectionCutCapacity.result k A).2.2.2.2.1
    change 2 * A.card + 2 ≤ capacity (fun _ : Fin (k + 1) => Window) task (fun i => i ∈ A)
    rw [cap_formula]
    by_cases hend : Fin.last k ∈ A
    · by_cases hdel : delta A = 0
      · have hexp := Nat.lt_pow_self (n := d A) (by decide : 1 < 2)
        simp only [hend, if_true, hdel, Nat.sub_zero] at *
        omega
      · have hk : 0 < k := by omega
        have hprev : (⟨k - 1, by omega⟩ : Fin (k + 1)) ∉ A := by
          simpa [delta, hk, FirstRejectionCutCapacity.left, hend] using hdel
        have hdelta : delta A = 1 := by
          simp [delta, hk, FirstRejectionCutCapacity.left, hend, hprev]
        have hB : (A.erase (Fin.last k)).Nonempty := by
          apply Finset.card_pos.mp
          rw [Finset.card_erase_of_mem hend]
          omega
        let v := (A.erase (Fin.last k)).max' hB
        have hv : v ∈ A.erase (Fin.last k) := Finset.max'_mem _ _
        have hvA : v ∈ A := (Finset.mem_erase.mp hv).2
        have hvk : v.val < k - 1 := by
          have hnot := (Finset.mem_erase.mp hv).1
          have hvnk : v.val ≠ k := by
            intro he
            exact hnot (Fin.ext he)
          have hvnp : v.val ≠ k - 1 := by
            intro he
            have hvp : v = ⟨k - 1, by omega⟩ := Fin.ext he
            exact hprev (hvp ▸ hvA)
          omega
        let exit : Fin k := ⟨v.val, by omega⟩
        have hexit : exit ∈ crossings A := by
          have hn : exit.succ ∉ A := by
            intro hh
            have hnlast : exit.succ ≠ Fin.last k := by
              intro he
              have := congrArg Fin.val he
              change v.val + 1 = k at this
              omega
            have hle := Finset.le_max' (A.erase (Fin.last k)) _
              (Finset.mem_erase.mpr ⟨hnlast, hh⟩)
            have hle' : v.val + 1 ≤ v.val := hle
            omega
          simp only [crossings, Finset.mem_filter, Finset.mem_univ, true_and]
          exact Or.inl ⟨hvA, hn⟩
        let final : Fin k := ⟨k - 1, by omega⟩
        have hfinal : final ∈ crossings A := by
          have he : final.succ = Fin.last k := Fin.ext (by dsimp [final]; omega)
          simp only [crossings, Finset.mem_filter, Finset.mem_univ, true_and]
          exact Or.inr ⟨hprev, by simpa [FirstRejectionCutCapacity.right, he] using hend⟩
        have hu_le_v : u.val ≤ v.val := A.min'_le _ hvA
        have hee : entry ≠ exit := by
          intro he
          have := congrArg Fin.val he
          dsimp [entry, exit] at this
          omega
        have hef : entry ≠ final := by
          intro he
          have := congrArg Fin.val he
          dsimp [entry, final] at this
          omega
        have hxf : exit ≠ final := by
          intro he
          have := congrArg Fin.val he
          dsimp [exit, final] at this
          omega
        have hd3 : 3 ≤ d A := by
          have hh : ({entry, exit, final} : Finset (Fin k)) ⊆ crossings A := by
            intro i hi
            simp only [Finset.mem_insert, Finset.mem_singleton] at hi
            rcases hi with rfl | rfl | rfl
            · exact hentry
            · exact hexit
            · exact hfinal
          simpa [d, hee, hef, hxf] using Finset.card_le_card hh
        have hexp := Nat.lt_pow_self (n := d A - 1) (by decide : 1 < 2)
        have hp : 2 ^ d A = 2 * 2 ^ (d A - 1) := by
          conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ d A by omega)]
          rw [pow_succ]
          omega
        simp only [hend, if_true, hdelta] at count ⊢
        rw [hp]
        omega
    · let v := A.max' hA
      have hvA : v ∈ A := A.max'_mem hA
      have hvk : v.val < k := by
        have hvn : v ≠ Fin.last k := by intro he; exact hend (he ▸ hvA)
        have hvnk : v.val ≠ k := by intro he; exact hvn (Fin.ext he)
        omega
      let exit : Fin k := ⟨v.val, hvk⟩
      have hexit : exit ∈ crossings A := by
        have hn : exit.succ ∉ A := by
          intro hh
          have hle : exit.succ ≤ v := A.le_max' _ hh
          have hle' : v.val + 1 ≤ v.val := hle
          omega
        simp only [crossings, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inl ⟨hvA, hn⟩
      have hu_le_v : u.val ≤ v.val := A.min'_le _ hvA
      have hee : entry ≠ exit := by
        intro he
        have := congrArg Fin.val he
        dsimp [entry, exit] at this
        omega
      have hd2 : 2 ≤ d A := by
        have hh : ({entry, exit} : Finset (Fin k)) ⊆ crossings A := by
          intro i hi
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with rfl | rfl
          · exact hentry
          · exact hexit
        simpa [d, hee] using Finset.card_le_card hh
      have hexp := Nat.mul_le_pow (by decide : (2 : ℕ) ≠ 1) (d A)
      simp only [hend, if_false, Nat.add_zero] at count ⊢
      omega

  have fork_height (L R : TreeMessageRealization.Tree (Fin (k + 1)))
      (hL : Full L) (hR : Full R) : height (fork L R) = max (height L) (height R) + 1 := by
    cases L with
    | nil => simp [Full] at hL
    | node a l r =>
      cases R with
      | nil => simp [Full] at hR
      | node b l' r' =>
        simp only [height, BinaryTree.height]
        omega
  have tree_count (t : TreeMessageRealization.Tree (Fin (k + 1))) (ht : Full t) :
      2 * (leaves t).card ≤ 2 ^ t.height ∧ 0 < t.height := by
    induction t with
    | nil => simp [Full] at ht
    | node a L R ihL ihR =>
      cases a with
      | some i =>
        obtain ⟨rfl, rfl⟩ := ht
        simp [leaves]
      | none =>
        obtain ⟨hLc, hLp⟩ := ihL ht.1
        obtain ⟨hRc, hRp⟩ := ihR ht.2.1
        have hLm : 2 ^ L.height ≤ 2 ^ max L.height R.height :=
          Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_left _ _)
        have hRm : 2 ^ R.height ≤ 2 ^ max L.height R.height :=
          Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_right _ _)
        have hcard : (leaves L ∪ leaves R).card = (leaves L).card + (leaves R).card :=
          Finset.card_union_of_disjoint ht.2.2
        change 2 * (leaves L ∪ leaves R).card ≤ 2 ^ (max L.height R.height + 1) ∧
          0 < max L.height R.height + 1
        rw [hcard, pow_succ]
        constructor <;> omega
  have height_lower (t : TreeMessageRealization.Tree (Fin (k + 1)))
      (ht : Full t) (hall : leaves t = Finset.univ) : H ≤ height t := by
    obtain ⟨hc, hp⟩ := tree_count t ht
    rw [hall, Finset.card_univ, Fintype.card_fin] at hc
    have hheight : t.height = height t + 1 := by unfold height; omega
    rw [hheight, pow_succ] at hc
    apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr
    dsimp [n] at *
    omega
  have opt_formula (t : TreeMessageRealization.Tree (Fin (k + 1)))
      (ht : Full t) (hall : leaves t = Finset.univ) :
      optimum task t = (subtrees t).sup (fun s => cap (leaves s)) := by
    obtain ⟨m, read, hm, hs, hp, ho⟩ := TreeMessageRealization.simultaneous_realization task t ht hall
    exact ho
  have opt_lower (t : TreeMessageRealization.Tree (Fin (k + 1)))
      (ht : Full t) (hall : leaves t = Finset.univ) : n + 1 ≤ optimum task t := by
    rw [opt_formula t ht hall]
    have hroot := Finset.le_sup (f := fun s => cap (leaves s))
      (FourMessageTreeRigidity.full_subtree_self k t ht)
    have hc : cap (leaves t) = n + 1 := by
      exact (FirstRejectionCutCapacity.result k (leaves t)).2.2.2.2.2.2.2.2.2.2.1 hall
    omega
  have interval_bound (l r : ℕ) (hlr : l < r) (hr : r ≤ n) :
      cap (interval k l r) ≤ if l = 0 then r + 1 else 2 * (r - l) + 2 := by
    rcases FirstRejectionCutCapacity.result k (interval k l r) with
      ⟨_, _, _, _, _, _, _, _, _, _, hfull, hprefix, hlast, _, _, _, hmiddle, hlong, _, _⟩
    by_cases hl : l = 0
    · subst l
      simp only [if_true]
      by_cases he : r = n
      · have hset : interval k 0 r = Finset.univ := by
          simpa only [he, n] using (FourMessageTreeRigidity.univ_interval k).symm
        have hc := hfull hset
        dsimp [cap, n] at *
        omega
      · exact le_of_eq (hprefix r (by omega) (by omega) rfl)
    · simp only [hl, if_false]
      by_cases hlength : l + 1 < r
      · exact le_of_eq (hlong l r (by omega) hlength hr rfl)
      · have hr1 : r = l + 1 := by omega
        by_cases hend : r = n
        · have hA : interval k l r = {Fin.last k} := by
            have hlk : l = k := by dsimp [n] at *; omega
            simpa only [hlk, hend, n, Fin.val_last] using
              (FirstRejectionCutCapacity.singleton_interval k (Fin.last k)).symm
          have hc := hlast (by dsimp [n] at *; omega) hA
          dsimp [cap] at *
          omega
        · let i : Fin (k + 1) := ⟨l, by dsimp [n] at *; omega⟩
          have hA : interval k l r = {i} := by
            simpa only [hr1] using (FirstRejectionCutCapacity.singleton_interval k i).symm
          have hc := hmiddle i (by dsimp [i]; omega) (by dsimp [i, n] at *; omega) hA
          dsimp [cap] at *
          omega
  have ordinary_balanced : ∃ t : TreeMessageRealization.Tree (Fin (k + 1)),
      Full t ∧ leaves t = Finset.univ ∧ height t = H ∧ optimum task t ≤ n + 2 := by
    obtain ⟨t, ht, hall, hh, hnodes⟩ := BalancedIntervalTree.result k 0 n (by dsimp [n]; omega) (by dsimp [n]; omega)
    have hall' : leaves t = Finset.univ := by
      rw [hall, Nat.zero_add]
      exact (FourMessageTreeRigidity.univ_interval k).symm
    refine ⟨t, ht, hall', hh, ?_⟩
    rw [opt_formula t ht hall']
    apply Finset.sup_le
    intro s hs
    obtain ⟨a, b, ha, hab, hb, hA, hshort⟩ := hnodes s hs
    rw [hA]
    have hc := interval_bound a b hab (by omega)
    by_cases ha0 : a = 0
    · subst a
      simp only [if_true] at hc
      omega
    · have hsmall : b - a ≤ n / 2 := by
        rcases hshort with hh | hh
        · exact False.elim (ha0 hh)
        · exact hh
      simp only [ha0, if_false] at hc
      omega
  have peak_balanced (hn : 3 ≤ n) : ∃ t : TreeMessageRealization.Tree (Fin (k + 1)),
      Full t ∧ leaves t = Finset.univ ∧ optimum task t = n + 1 ∧
        height t = 1 + Nat.clog 2 ((n + 2) / 2) := by
    let a := (n + 2) / 2
    let b := n - a
    have ha : 0 < a := by dsimp [a]; omega
    have hb : 0 < b := by dsimp [a, b]; omega
    have hb_le_a : b ≤ a := by dsimp [a, b]; omega
    have ha_half : a / 2 ≤ b := by dsimp [a, b]; omega
    have hsum : a + b = n := by dsimp [a, b]; omega
    have hbudget : 2 * b + 2 ≤ n + 1 := by dsimp [a, b]; omega
    obtain ⟨L, hL, hLA, hLH, hLS⟩ := BalancedIntervalTree.result k 0 a ha (by dsimp [n] at *; omega)
    obtain ⟨R, hR, hRA, hRH, hRS⟩ := BalancedIntervalTree.result k a b hb (by dsimp [n, b] at *; omega)
    have hdisjoint : Disjoint (leaves L) (leaves R) := by
      rw [hLA, hRA]
      apply Finset.disjoint_left.mpr
      intro i hi hj
      simp only [interval, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      omega
    have ht : Full (fork L R) := ⟨hL, hR, hdisjoint⟩
    have hall : leaves (fork L R) = Finset.univ := by
      change leaves L ∪ leaves R = Finset.univ
      rw [hLA, hRA]
      ext i
      simp only [Finset.mem_union, interval, Finset.mem_filter, Finset.mem_univ, true_and]
      have hi : i.val < n := i.isLt
      simp only [Nat.zero_add, hsum, iff_true]
      by_cases h : i.val < a
      · exact Or.inl ⟨Nat.zero_le _, h⟩
      · exact Or.inr ⟨Nat.le_of_not_gt h, hi⟩
    have hupper : optimum task (fork L R) ≤ n + 1 := by
      rw [opt_formula (fork L R) ht hall]
      apply Finset.sup_le
      intro s hs
      simp only [fork, subtrees, Finset.mem_insert, Finset.mem_union] at hs
      rcases hs with rfl | hs | hs
      · exact le_of_eq ((FirstRejectionCutCapacity.result k _).2.2.2.2.2.2.2.2.2.2.1 hall)
      · obtain ⟨l, r, hl, hlr, hr, hA, hshort⟩ := hLS s hs
        rw [hA]
        have hc := interval_bound l r hlr (by omega)
        by_cases hl0 : l = 0
        · subst l
          simp only [if_true] at hc
          omega
        · have hsmall : r - l ≤ b := by
            rcases hshort with he | he
            · exact False.elim (hl0 he)
            · omega
          simp only [hl0, if_false] at hc
          omega
      · obtain ⟨l, r, hl, hlr, hr, hA, _⟩ := hRS s hs
        rw [hA]
        have hc := interval_bound l r hlr (by dsimp [b] at *; omega)
        have hl0 : l ≠ 0 := by omega
        simp only [hl0, if_false] at hc
        omega
    refine ⟨fork L R, ht, hall, le_antisymm hupper (opt_lower _ ht hall), ?_⟩
    rw [fork_height L R hL hR, hLH, hRH,
      max_eq_left (Nat.clog_mono_right 2 hb_le_a)]
    simp only [a, Nat.add_comm]
  have saturation (t : TreeMessageRealization.Tree (Fin (k + 1)))
      (ht : Full t) (hall : leaves t = Finset.univ)
      (hex : exceptional) (hh : height t = H) : n + 2 ≤ optimum task t := by
    have hn4 : 4 ≤ n := hex.1
    have hpow : n = 2 ^ H := hex.2
    cases t with
    | nil => simp [Full] at ht
    | node label L R =>
      cases label with
      | some i =>
        have hcard := congrArg Finset.card hall
        simp only [leaves, Finset.card_singleton, Finset.card_univ, Fintype.card_fin] at hcard
        dsimp [n] at hn4
        omega
      | none =>
        have hmax : max L.height R.height = H := by
          simpa only [height, BinaryTree.height, Nat.add_sub_cancel] using hh
        have hLpow : 2 ^ L.height ≤ 2 ^ H :=
          Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
        have hRpow : 2 ^ R.height ≤ 2 ^ H :=
          Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
        have hLc := (tree_count L ht.1).1
        have hRc := (tree_count R ht.2.1).1
        have hcard : (leaves L).card + (leaves R).card = n := by
          have hc := congrArg Finset.card hall
          simpa only [leaves, Finset.card_union_of_disjoint ht.2.2,
            Finset.card_univ, Fintype.card_fin] using hc
        have hLhalf : 2 * (leaves L).card = n := by omega
        have hRhalf : 2 * (leaves R).card = n := by omega
        have hcapL : cap (leaves L) ≤ optimum task (fork L R) := by
          rw [opt_formula (fork L R) ht hall]
          apply Finset.le_sup (f := fun s => cap (leaves s)) (b := L)
          simp only [fork, subtrees, Finset.mem_insert, Finset.mem_union]
          exact Or.inr (Or.inl (FourMessageTreeRigidity.full_subtree_self k L ht.1))
        have hcapR : cap (leaves R) ≤ optimum task (fork L R) := by
          rw [opt_formula (fork L R) ht hall]
          apply Finset.le_sup (f := fun s => cap (leaves s)) (b := R)
          simp only [fork, subtrees, Finset.mem_insert, Finset.mem_union]
          exact Or.inr (Or.inr (FourMessageTreeRigidity.full_subtree_self k R ht.2.1))
        by_cases hz : (0 : Fin (k + 1)) ∈ leaves L
        · have hzR : (0 : Fin (k + 1)) ∉ leaves R := by
            intro hzR
            exact Finset.disjoint_left.mp ht.2.2 hz hzR
          have hc := subset_lower (leaves R) hzR (by omega)
          change n + 2 ≤ optimum task (fork L R)
          omega
        · have hc := subset_lower (leaves L) hz (by omega)
          change n + 2 ≤ optimum task (fork L R)
          omega
  have small (hn : n ≤ 2) : ∃ t : TreeMessageRealization.Tree (Fin (k + 1)),
      Full t ∧ leaves t = Finset.univ ∧ optimum task t = n + 1 ∧ height t = H := by
    have hk : k = 0 ∨ k = 1 := by dsimp [n] at hn; omega
    rcases hk with rfl | rfl
    · let t : TreeMessageRealization.Tree (Fin 1) := leaf 0
      have ht : Full t := by simp [t, Full]
      have hall : leaves t = Finset.univ := by
        ext i
        simp only [t, leaves, Finset.mem_singleton, Finset.mem_univ, iff_true]
        apply Fin.ext
        have hi := i.isLt
        simp only [Fin.val_zero]
        omega
      have ho : optimum task t = 2 := by
        rw [opt_formula t ht hall]
        simp only [t, subtrees, Finset.sup_singleton]
        exact (FirstRejectionCutCapacity.result 0 _).2.2.2.2.2.2.2.2.2.2.1 hall
      exact ⟨t, ht, hall, ho, by simp [t, height, H, n]⟩
    · let L : TreeMessageRealization.Tree (Fin 2) := leaf 0
      let R : TreeMessageRealization.Tree (Fin 2) := leaf (Fin.last 1)
      let t := fork L R
      have ht : Full t := by
        simp [t, L, R, Full, leaves]
      have hall : leaves t = Finset.univ := by
        ext i
        simp only [t, L, R, leaves, Finset.mem_union, Finset.mem_singleton,
          Finset.mem_univ, iff_true, Fin.ext_iff, Fin.val_zero, Fin.val_last]
        have hi := i.isLt
        omega
      have hupper : optimum task t ≤ 3 := by
        rw [opt_formula t ht hall]
        apply Finset.sup_le
        intro s hs
        simp only [t, L, R, subtrees, Finset.mem_insert, Finset.mem_union,
          Finset.mem_singleton] at hs
        rcases hs with rfl | rfl | rfl
        · exact le_of_eq ((FirstRejectionCutCapacity.result 1 _).2.2.2.2.2.2.2.2.2.2.1 hall)
        · have hc := (FirstRejectionCutCapacity.result 1 _).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl
          dsimp [cap]
          exact (le_of_eq hc).trans (by omega)
        · exact le_of_eq ((FirstRejectionCutCapacity.result 1 _).2.2.2.2.2.2.2.2.2.2.2.2.1 (by omega) rfl)
      refine ⟨t, ht, hall, le_antisymm hupper (opt_lower t ht hall), ?_⟩
      simp [t, L, R, height, H, n, Nat.clog_of_one_lt]
  have peak_attained : ∃ t : TreeMessageRealization.Tree (Fin (k + 1)),
      Full t ∧ leaves t = Finset.univ ∧ optimum task t = n + 1 ∧
        height t = (if exceptional then H + 1 else H) := by
    by_cases hn : n ≤ 2
    · obtain ⟨t, ht, hall, ho, hh⟩ := small hn
      have he : ¬ exceptional := by intro he; omega
      refine ⟨t, ht, hall, ho, ?_⟩
      simpa only [he, if_false] using hh
    · obtain ⟨t, ht, hall, ho, hh⟩ := peak_balanced (by omega)
      have hsuccessor : height t = Nat.clog 2 (n + 1) := by
        rw [hh]
        have hrec := Nat.clog_of_one_lt (by decide : 1 < 2) (show 1 < n + 1 by omega)
        rw [show n + 1 + 2 - 1 = n + 2 by omega] at hrec
        omega
      have hH2 : 2 ≤ H := by
        by_contra hlow
        have he : Nat.clog 2 n ≤ 1 := by omega
        have he' := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp he
        norm_num at he'
        omega
      refine ⟨t, ht, hall, ho, ?_⟩
      rw [hsuccessor]
      by_cases he : exceptional
      · simp only [he, if_true]
        have hlo : H < Nat.clog 2 (n + 1) :=
          (Nat.clog_lt_clog_succ_iff (by decide : 1 < 2)).mpr he.2.symm
        have hup : Nat.clog 2 (n + 1) ≤ H + 1 := by
          apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr
          rw [pow_succ, ← he.2]
          omega
        omega
      · simp only [he, if_false]
        have hne : 2 ^ H ≠ n := by
          intro hp
          have hfour : 4 ≤ n := by
            have hbound := Nat.pow_le_pow_right (by decide : 0 < 2) hH2
            norm_num at hbound
            omega
          exact he ⟨hfour, hp.symm⟩
        exact ((Nat.clog_eq_clog_succ_iff (by decide : 1 < 2)).mpr hne).symm
  have peak_height_lower (t : TreeMessageRealization.Tree (Fin (k + 1)))
      (ht : Full t) (hall : leaves t = Finset.univ) (ho : optimum task t = n + 1) :
      (if exceptional then H + 1 else H) ≤ height t := by
    have hmin := height_lower t ht hall
    by_cases he : exceptional
    · simp only [he, if_true]
      by_contra hl
      have hh : height t = H := by omega
      have hs := saturation t ht hall he hh
      omega
    · simpa only [he, if_false] using hmin
  have height_attained : ∃ t : TreeMessageRealization.Tree (Fin (k + 1)),
      Full t ∧ leaves t = Finset.univ ∧ height t = H ∧
        optimum task t = (if exceptional then n + 2 else n + 1) := by
    by_cases he : exceptional
    · obtain ⟨t, ht, hall, hh, ho⟩ := ordinary_balanced
      refine ⟨t, ht, hall, hh, ?_⟩
      simp only [he, if_true]
      exact le_antisymm ho (saturation t ht hall he hh)
    · obtain ⟨t, ht, hall, ho, hh⟩ := peak_attained
      refine ⟨t, ht, hall, ?_, ?_⟩
      · simpa only [he, if_false] using hh
      · simpa only [he, if_false] using ho
  have height_peak_lower (t : TreeMessageRealization.Tree (Fin (k + 1)))
      (ht : Full t) (hall : leaves t = Finset.univ) (hh : height t = H) :
      (if exceptional then n + 2 else n + 1) ≤ optimum task t := by
    by_cases he : exceptional
    · simpa only [he, if_true] using saturation t ht hall he hh
    · simpa only [he, if_false] using opt_lower t ht hall
  exact ⟨subset_lower, fun t ht hall => ⟨opt_formula t ht hall, opt_lower t ht hall,
    height_lower t ht hall⟩, peak_attained, peak_height_lower, height_attained, height_peak_lower⟩

end D5.S3.Arith.FibonacciAtomic.TreePeakHeightFrontier
