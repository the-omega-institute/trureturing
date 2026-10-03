/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenNineAuxiliaryCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenNineAuxiliaryCount
   mirror-E: none(waiver:auxiliary-class-disjoint-counting-construction)
   anchors: [mathlib/module/Mathlib.Data.List.Sort, mathlib/module/Mathlib.Data.List.Permutation]
   utility: none
   digest: Splitting at the maximum counts 231 and 123 avoiders by two inverse constructions. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenNineAuxiliary
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Permutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenNineAuxiliaryCount

open D5.S3.Combinatorics Nonnesting FishburnClassicalDefs
open FishburnTenNineAuxiliary FishburnTenNineClassicalSplit

theorem auxiliary_count (size : ℕ) :
    (classicalAvoiders size [[2, 3, 1], [1, 2, 3]]).ncard = 1 + size.choose 2 := by
  classical
  have hfinite (n : ℕ) : (classicalAvoiders n [[2, 3, 1], [1, 2, 3]]).Finite := by
    apply (List.finite_toSet (List.range' 1 n).permutations).subset
    intro p hp
    exact List.mem_permutations.mpr hp.1
  induction size with
  | zero =>
    have heq : classicalAvoiders 0 [[2, 3, 1], [1, 2, 3]] = {[]} := by
      ext p
      constructor
      · intro hp
        have hlen := hp.1.length_eq
        simp only [List.length_range'] at hlen
        simpa using List.length_eq_zero_iff.mp hlen
      · intro hp
        have heq : p = [] := Set.mem_singleton_iff.mp hp
        subst p
        refine ⟨by simp, ?_⟩
        intro pattern hpattern hocc
        obtain ⟨_, _, _, hsub, _⟩ := hocc
        have hl := hsub.length_le
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
        rcases hpattern with rfl | rfl <;> simp at hl
    simp [heq]
  | succ n ih =>
    let template : ℕ → List ℕ := fun cut => (List.range' 1 cut).reverse ++
      (n + 1) :: (List.range' (cut + 1) (n - cut)).reverse
    let front : Set (List ℕ) := (List.cons (n + 1)) ''
      classicalAvoiders n [[2, 3, 1], [1, 2, 3]]
    let extra : Set (List ℕ) := template '' (↑(Finset.Icc 1 n) : Set ℕ)
    have hfront (p : List ℕ) : (n + 1) :: p ∈
        classicalAvoiders (n + 1) [[2, 3, 1], [1, 2, 3]] ↔
        p ∈ classicalAvoiders n [[2, 3, 1], [1, 2, 3]] := by
      have hper : ((n + 1) :: p).Perm (List.range' 1 (n + 1)) ↔
          p.Perm (List.range' 1 n) := by
        rw [List.range'_1_concat]
        have hp : (List.range' 1 n ++ [1 + n]).Perm
            ((n + 1) :: List.range' 1 n) := by
          simpa only [List.append_nil, Nat.add_comm] using
            (List.perm_middle : (List.range' 1 n ++ (n + 1) :: []).Perm
              ((n + 1) :: (List.range' 1 n ++ [])))
        exact ⟨fun h => (h.trans hp).cons_inv,
          fun h => (h.cons (n + 1)).trans hp.symm⟩
      constructor
      · intro hp
        refine ⟨hper.mp hp.1, ?_⟩
        intro pattern hpattern hocc
        apply hp.2 pattern hpattern
        obtain ⟨values, hstep, hmem, hsub, _⟩ := hocc
        refine ⟨values, hstep, ?_, hsub.cons (n + 1), by simp⟩
        intro rank hlo hhi
        exact List.mem_cons_of_mem _ (hmem rank hlo hhi)
      · intro hp
        have hperm := hper.mpr hp.1
        have hnodup : ((n + 1) :: p).Nodup :=
          hperm.nodup_iff.mpr (List.nodup_range' 1)
        have hbound (value : ℕ) (hm : value ∈ p) : value < n + 1 := by
          have hr := hp.1.mem_iff.mp hm
          simp only [List.mem_range'_1] at hr
          omega
        refine ⟨hperm, ?_⟩
        intro pattern hpattern
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
        rcases hpattern with rfl | rfl
        · have h231 := hp.2 [2, 3, 1] (by simp)
          exact (avoids231_maxSplit_iff [] p (n + 1)
            (by simpa using hbound) hnodup).mpr
            ⟨by
              rintro ⟨_, _, _, hsub, _⟩
              have hl := hsub.length_le
              simp at hl, h231, by simp⟩
        · rintro ⟨values, hstep, _, hsub, _⟩
          have h12 : values 1 < values 2 := hstep 1 (by omega) (by decide)
          rcases List.sublist_cons_iff.mp hsub with hwhole | ⟨rest, heq, hrest⟩
          · apply hp.2 [1, 2, 3] (by simp)
            refine ⟨values, hstep, ?_, hwhole, by simp⟩
            intro rank hlo hhi
            have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 := by
              change rank ≤ 3 at hhi; omega
            apply hwhole.subset
            rcases hc with rfl | rfl | rfl <;> simp
          · change [values 1, values 2, values 3] = (n + 1) :: rest at heq
            obtain ⟨hfirst, heq⟩ := List.cons.inj heq
            have hm := hrest.subset
              (heq ▸ (show values 2 ∈ [values 2, values 3] by simp))
            have hb := hbound (values 2) hm
            omega
    have htemplatePerm (cut : ℕ) (hcut : cut ≤ n) :
        (template cut).Perm (List.range' 1 (n + 1)) := by
      have hrange : List.range' 1 cut ++ List.range' (cut + 1) (n - cut) =
          List.range' 1 n := by
        symm
        apply List.range'_eq_append_iff.mpr
        exact ⟨cut, hcut, rfl, by simp [Nat.add_comm]⟩
      have hparts := (List.reverse_perm (List.range' 1 cut)).append
        (List.reverse_perm (List.range' (cut + 1) (n - cut)))
      change ((List.range' 1 cut).reverse ++
        (n + 1) :: (List.range' (cut + 1) (n - cut)).reverse).Perm _
      apply List.Perm.trans List.perm_middle
      have hpartsPerm : ((List.range' 1 cut).reverse ++
          (List.range' (cut + 1) (n - cut)).reverse).Perm (List.range' 1 n) := by
        simpa only [hrange] using hparts
      apply List.Perm.trans (hpartsPerm.cons (n + 1))
      rw [List.range'_1_concat]
      simpa [Nat.add_comm] using
        (List.perm_middle : (List.range' 1 n ++ (n + 1) :: []).Perm
          ((n + 1) :: (List.range' 1 n ++ []))).symm
    have htemplate (cut : ℕ) (hcut : cut ∈ Finset.Icc 1 n) :
        template cut ∈ classicalAvoiders (n + 1) [[2, 3, 1], [1, 2, 3]] := by
      obtain ⟨hpositive, hle⟩ := Finset.mem_Icc.mp hcut
      have hperm := htemplatePerm cut hle
      have hmax : ∀ value ∈ (List.range' 1 cut).reverse ++
          (List.range' (cut + 1) (n - cut)).reverse, value < n + 1 := by
        intro value hm
        simp only [List.mem_append, List.mem_reverse, List.mem_range'_1] at hm
        rcases hm with hm | hm <;> omega
      have hleftne : (List.range' 1 cut).reverse ≠ [] := by
        intro heq
        have hl := congrArg List.length heq
        simp at hl
        omega
      have hparts := (auxiliary_noninitial_maxSplit_iff
        (List.range' 1 cut).reverse (List.range' (cut + 1) (n - cut)).reverse
        (n + 1) hmax (hperm.nodup_iff.mpr (List.nodup_range' 1)) hleftne).mpr
        ⟨List.pairwise_reverse.mpr List.pairwise_lt_range',
          List.pairwise_reverse.mpr List.pairwise_lt_range', by
            intro lower hlower upper hupper
            simp only [List.mem_reverse, List.mem_range'_1] at hlower hupper
            omega⟩
      refine ⟨hperm, ?_⟩
      intro pattern hpattern
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl
      · exact hparts.1
      · exact hparts.2
    have hrecover (p : List ℕ)
        (hp : p ∈ classicalAvoiders (n + 1) [[2, 3, 1], [1, 2, 3]]) :
        p ∈ front ∪ extra := by
      have hmaximum : n + 1 ∈ p := hp.1.mem_iff.mpr (by simp)
      obtain ⟨left, right, heq, _⟩ := List.eq_append_cons_of_mem hmaximum
      subst p
      by_cases hleft : left = []
      · subst left
        apply Set.mem_union_left
        exact ⟨right, (hfront right).mp (by simpa using hp), by simp⟩
      · apply Set.mem_union_right
        have hnodup : (left ++ (n + 1) :: right).Nodup :=
          hp.1.nodup_iff.mpr (List.nodup_range' 1)
        have hmax (value : ℕ) (hm : value ∈ left ++ right) : value < n + 1 := by
          have hv : value ∈ left ++ (n + 1) :: right := by
            rcases List.mem_append.mp hm with hl | hr
            · exact List.mem_append_left _ hl
            · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
          have hb := hp.1.mem_iff.mp hv
          simp only [List.mem_range'_1] at hb
          have hne : value ≠ n + 1 := by
            intro heq
            subst value
            rcases List.mem_append.mp hm with hl | hr
            · exact (List.nodup_append.mp hnodup).2.2 (n + 1) hl
                (n + 1) (by simp) rfl
            · exact (List.nodup_cons.mp (List.nodup_append.mp hnodup).2.1).1 hr
          omega
        obtain ⟨hleftDesc, hrightDesc, hsep⟩ :=
          (auxiliary_noninitial_maxSplit_iff left right (n + 1) hmax hnodup hleft).mp
            ⟨hp.2 [2, 3, 1] (by simp), hp.2 [1, 2, 3] (by simp)⟩
        have hparentPerm : (left ++ right).Perm (List.range' 1 n) := by
          have hcons := List.perm_middle.symm.trans hp.1
          rw [List.range'_1_concat] at hcons
          have hm : (List.range' 1 n ++ [1 + n]).Perm
              ((n + 1) :: List.range' 1 n) := by
            simpa only [List.append_nil, Nat.add_comm] using
              (List.perm_middle : (List.range' 1 n ++ (n + 1) :: []).Perm
                ((n + 1) :: (List.range' 1 n ++ [])))
          exact (hcons.trans hm).cons_inv
        have hsort : (left.reverse ++ right.reverse).Pairwise (· ≤ ·) := by
          apply List.pairwise_append.mpr
          refine ⟨(List.pairwise_reverse.mpr hleftDesc).imp (fun h => le_of_lt h),
            (List.pairwise_reverse.mpr hrightDesc).imp (fun h => le_of_lt h), ?_⟩
          intro lower hlower upper hupper
          exact le_of_lt (hsep lower (List.mem_reverse.mp hlower)
            upper (List.mem_reverse.mp hupper))
        have hsorted : left.reverse ++ right.reverse = List.range' 1 n := by
          apply List.Perm.eq_of_pairwise' hsort List.pairwise_le_range'
          exact ((List.reverse_perm left).append (List.reverse_perm right)).trans hparentPerm
        obtain ⟨cut, hcut, hleftEq, hrightEq⟩ :=
          List.range'_eq_append_iff.mp hsorted.symm
        have hlength : left.length = cut := by
          have hl := congrArg List.length hleftEq
          simpa using hl
        have hpositive : 1 ≤ cut := by
          have hl := List.length_pos_iff.mpr hleft
          omega
        refine ⟨cut, Finset.mem_Icc.mpr ⟨hpositive, hcut⟩, ?_⟩
        have hl := congrArg List.reverse hleftEq
        have hr := congrArg List.reverse hrightEq
        simp only [List.reverse_reverse, Nat.mul_one] at hl hr
        simp only [template, hl, hr, Nat.add_comm]
    have hclass : classicalAvoiders (n + 1) [[2, 3, 1], [1, 2, 3]] = front ∪ extra := by
      apply Set.Subset.antisymm hrecover
      intro p hp
      rcases hp with ⟨parent, hparent, rfl⟩ | ⟨cut, hcut, rfl⟩
      · exact (hfront parent).mpr hparent
      · exact htemplate cut hcut
    have hsite (cut : ℕ) (hcut : cut ≤ n) : (template cut).idxOf (n + 1) = cut := by
      have hnot : n + 1 ∉ (List.range' 1 cut).reverse := by
        simp only [List.mem_reverse, List.mem_range'_1, not_and]
        omega
      simp [template, List.idxOf_append_of_notMem hnot]
    have hinj : Set.InjOn template (↑(Finset.Icc 1 n) : Set ℕ) := by
      intro first hfirst second hsecond heq
      have hi := congrArg (fun p : List ℕ => p.idxOf (n + 1)) heq
      rw [hsite first (Finset.mem_Icc.mp hfirst).2,
        hsite second (Finset.mem_Icc.mp hsecond).2] at hi
      exact hi
    have hdisjoint : Disjoint front extra := by
      apply Set.disjoint_left.mpr
      rintro p ⟨parent, _, heq⟩ ⟨cut, hcut, htemplateEq⟩
      have hi := congrArg (fun word : List ℕ => word.idxOf (n + 1))
        (heq.trans htemplateEq.symm)
      rw [hsite cut (Finset.mem_Icc.mp hcut).2] at hi
      simp only [List.idxOf_cons_self] at hi
      have hpositive := (Finset.mem_Icc.mp hcut).1
      omega
    have hfrontCard : front.ncard =
        (classicalAvoiders n [[2, 3, 1], [1, 2, 3]]).ncard := by
      exact Set.ncard_image_of_injective _ (fun _ _ heq => List.cons.inj heq |>.2)
    have hextraCard : extra.ncard = n := by
      rw [hinj.ncard_image, Set.ncard_coe_finset]
      simp
    rw [hclass, Set.ncard_union_eq hdisjoint
      ((hfinite n).image _) ((Finset.finite_toSet _).image _), hfrontCard, hextraCard, ih]
    rw [Nat.choose_succ_succ' n 1, Nat.choose_one_right]
    change 1 + n.choose 2 + n = 1 + (n + n.choose 2)
    omega

end D5.S3.Combinatorics.Fishburn.FishburnTenNineAuxiliaryCount
