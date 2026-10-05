/- GID: D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceFibonacciGap
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RotationAvoidance/RotationAvoidanceFibonacciGap
   mirror-E: none(waiver:uniform-endpoint-convolution-gap)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Fibonacci convolution growth strictly separates the two endpoint totals. -/

import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceMixed
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceMixedEmptyCount
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceSlices
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceAlternatingContraction
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceAlternating
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceLayeredCount
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceLayeredEmpty
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceFibonacciGap

open D5.S3.Combinatorics Nonnesting.NonnestingDefs
open RotationAvoidanceDefs RotationAvoidanceCircular

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 4096 in
theorem fibonacci_lt_layered (size : ℕ) (hsize : 7 ≤ size) :
    (singleBadCircles size [1, 3, 2, 4]).ncard <
      (singleBadCircles size [1, 4, 2, 3]).ncard := by
  classical
  let N := size - 2
  have hN : 5 ≤ N := by dsimp [N]; omega
  have sizeEq : size = N + 2 := by dsimp [N]; omega
  let C := fun t : ℕ => Nat.fib (2 * t - 1)
  let S := fun t : ℕ => ∑ h ∈ Finset.Ico 1 (t + 1), C h
  let T := fun t : ℕ => ∑ h ∈ Finset.Ico 1 t, C h * C (t - h)
  let d := fun t : ℕ => 2 ^ (t - 1) - 1
  let A := fun t : ℕ => d t + 2 * ∑ h ∈ Finset.Ico 1 (t - 1), C h * d (t - h)
  let B := fun t : ℕ =>
    ∑ h ∈ Finset.Ico 1 t, (t - h + S (t - h - 1)) * C h
  have sStep (t : ℕ) : S (t + 1) = S t + C (t + 1) := by
    dsimp [S]; rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ t + 1)]
  have sFib (t : ℕ) : S t = Nat.fib (2 * t) := by
    induction t with
    | zero => simp [S]
    | succ t ih =>
      rw [sStep, ih]; dsimp [C]; rw [show 2 * (t + 1) - 1 = 2 * t + 1 by omega,
        show 2 * (t + 1) = 2 * t + 2 by omega, Nat.fib_add_two]
  have cStep (t : ℕ) (ht : 1 ≤ t) : C (t + 1) = 2 * C t + S (t - 1) := by
    rw [sFib]; dsimp [C]
    have h1 := Nat.fib_add_two (n := 2 * t - 2); have h2 := Nat.fib_add_two (n := 2 * t - 1)
    rw [show 2 * t - 2 + 2 = 2 * t by omega,
      show 2 * t - 2 + 1 = 2 * t - 1 by omega] at h1
    rw [show 2 * t - 1 + 2 = 2 * t + 1 by omega,
      show 2 * t - 1 + 1 = 2 * t by omega] at h2
    rw [show 2 * (t + 1) - 1 = 2 * t + 1 by omega,
      show 2 * (t - 1) = 2 * t - 2 by omega]
    omega
  have sPrev (t : ℕ) (ht : 1 ≤ t) : S t = S (t - 1) + C t := by
    simpa only [show t - 1 + 1 = t by omega] using sStep (t - 1)
  have tGrowth (t : ℕ) (ht : 2 ≤ t) : 2 * T t + C t ≤ T (t + 1) := by
    have each (h : ℕ) (hh : h ∈ Finset.Ico 1 t) :
        2 * (C h * C (t - h)) ≤ C h * C (t + 1 - h) := by
      have hh' := Finset.mem_Ico.mp hh; have step := cStep (t - h) (by omega)
      rw [show t - h + 1 = t + 1 - h by omega] at step; nlinarith
    have bound := Finset.sum_le_sum each; dsimp [T] at bound ⊢
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ t)]; have cOne : C 1 = 1 := by decide
    rw [Nat.add_sub_cancel_left, cOne, mul_one]; rw [Finset.mul_sum]; omega
  have bStep (t : ℕ) (ht : 2 ≤ t) : B (t + 1) = B t + S t + T t := by
    have each (h : ℕ) (hh : h ∈ Finset.Ico 1 t) :
        (t + 1 - h + S (t + 1 - h - 1)) * C h =
          (t - h + S (t - h - 1)) * C h + C h + C h * C (t - h) := by
      have hh' := Finset.mem_Ico.mp hh; rw [show t + 1 - h - 1 = t - h by omega,
        sPrev (t - h) (by omega), show t + 1 - h = t - h + 1 by omega]
      ring
    dsimp [B]; rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ t), Finset.sum_congr rfl each]
    simp only [Finset.sum_add_distrib]; have hs : (∑ h ∈ Finset.Ico 1 t, C h) + C t = S t := by
      dsimp [S]; rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ t)]
    change _ + (t + 1 - t + S (t + 1 - t - 1)) * C t = _
    simp only [show t + 1 - t = 1 by omega, Nat.sub_self, S,
      Finset.Ico_self, Finset.sum_empty, add_zero, one_mul]
    change (∑ h ∈ Finset.Ico 1 t, C h) + C t = S t at hs
    change _ = _ + S t + (∑ h ∈ Finset.Ico 1 t, C h * C (t - h))
    omega
  have dStep (t : ℕ) (ht : 1 ≤ t) : d (t + 1) = 2 * d t + 1 := by
    have hp : 1 ≤ 2 ^ (t - 1) := Nat.one_le_pow _ _ (by decide); dsimp [d]
    conv_lhs => rw [show t = t - 1 + 1 by omega, pow_succ]
    omega
  have aStep (t : ℕ) (ht : 2 ≤ t) : A (t + 1) = 2 * A t + 1 + 2 * S (t - 1) := by
    have each (h : ℕ) (hh : h ∈ Finset.Ico 1 (t - 1)) :
        C h * d (t + 1 - h) = 2 * (C h * d (t - h)) + C h := by
      have hh' := Finset.mem_Ico.mp hh
      rw [show t + 1 - h = t - h + 1 by omega, dStep (t - h) (by omega)]; ring
    have hs : (∑ h ∈ Finset.Ico 1 (t - 1), C h) + C (t - 1) = S (t - 1) := by
      dsimp [S]; rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ t - 1)]
    dsimp [A]; rw [dStep t (by omega)]
    have split := Finset.sum_Ico_succ_top (f := fun h => C h * d (t + 1 - h))
      (by omega : 1 ≤ t - 1)
    rw [show t - 1 + 1 = t by omega] at split
    rw [split, Finset.sum_congr rfl each, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [show t + 1 - (t - 1) = 2 by omega]
    norm_num only [d, Nat.reduceSub, pow_one, Nat.reduceSub, mul_one] at ⊢
    nlinarith
  have convolutionGap : ∀ t : ℕ, 4 ≤ t → B t + 1 + S (t - 1) < C t + T t := by
    intro t ht; induction t, ht using Nat.le_induction with
    | base => decide
    | succ t ht ih =>
      rw [bStep t (by omega), cStep t (by omega),
        show t + 1 - 1 = t by omega, sPrev t (by omega)]
      have hg := tGrowth t (by omega); omega
  have countGap : ∀ t : ℕ, 4 ≤ t → A t ≤ B t ∧ (5 ≤ t → A t < B t) := by
    intro t ht; induction t, ht using Nat.le_induction with
    | base => exact ⟨by decide, by omega⟩
    | succ t ht ih =>
      have hg := convolutionGap t ht
      rw [aStep t (by omega), bStep t (by omega), sPrev t (by omega)]; constructor <;> omega
  have band (F : ℕ → ℕ → ℕ) :
      (∑ a ∈ Finset.range (size + 1), ∑ b ∈ Finset.range (size + 1),
        if 1 ≤ a ∧ a + 2 < b ∧ b ≤ size then F a b else 0) =
      ∑ t ∈ Finset.range (size + 1), ∑ a ∈ Finset.range (size + 1),
        if 2 ≤ t ∧ 1 ≤ a ∧ a + t < size then F a (a + t + 1) else 0 := by
    let domain := ((Finset.range (size + 1)) ×ˢ (Finset.range (size + 1))).filter
      (fun ab : ℕ × ℕ => 1 ≤ ab.1 ∧ ab.1 + 2 < ab.2 ∧ ab.2 ≤ size)
    let target := ((Finset.range (size + 1)) ×ˢ (Finset.range (size + 1))).filter
      (fun ta : ℕ × ℕ => 2 ≤ ta.1 ∧ 1 ≤ ta.2 ∧ ta.2 + ta.1 < size)
    have hm (ab : ℕ × ℕ) : ab ∈ domain ↔
        ab.1 < size + 1 ∧ ab.2 < size + 1 ∧
          1 ≤ ab.1 ∧ ab.1 + 2 < ab.2 ∧ ab.2 ≤ size := by
      simp only [domain, Finset.mem_filter, Finset.mem_product, Finset.mem_range]; tauto
    have ht (ta : ℕ × ℕ) : ta ∈ target ↔
        ta.1 < size + 1 ∧ ta.2 < size + 1 ∧
          2 ≤ ta.1 ∧ 1 ≤ ta.2 ∧ ta.2 + ta.1 < size := by
      simp only [target, Finset.mem_filter, Finset.mem_product, Finset.mem_range]; tauto
    have reindex : (∑ ab ∈ domain, F ab.1 ab.2) =
        ∑ ta ∈ target, F ta.2 (ta.2 + ta.1 + 1) := by
      apply Finset.sum_bij (fun ab _ => (ab.2 - ab.1 - 1, ab.1))
      · intro ab hab
        have hab' := (hm ab).mp hab; apply (ht _).mpr; dsimp; omega
      · intro ab hab cd hcd he
        have hab' := (hm ab).mp hab; have hcd' := (hm cd).mp hcd
        have h1 := congrArg Prod.fst he; have h2 := congrArg Prod.snd he
        apply Prod.ext <;> dsimp at * <;> omega
      · intro ta hta
        have hta' := (ht ta).mp hta; refine ⟨(ta.2, ta.2 + ta.1 + 1), (hm _).mpr ?_, ?_⟩
        · dsimp; omega
        · apply Prod.ext <;> dsimp <;> omega
      · intro ab hab
        have hab' := (hm ab).mp hab; dsimp; congr 1; omega
    simpa only [domain, target, Finset.sum_filter, Finset.sum_product] using reindex
  have ascendingTotal : (singleBadCircles size [1, 3, 2, 4]).ncard = A N := by
    have fibonacci_single_bad_count (size : ℕ) (hsize : 5 ≤ size) :
        (singleBadCircles size [1, 3, 2, 4]).ncard =
          ∑ first ∈ Finset.range (size + 1), ∑ last ∈ Finset.range (size + 1),
            if 1 ≤ first ∧ first + 2 < last ∧ last ≤ size then
              if first = 1 then
                (if last = size then 1 else Nat.fib (2 * (size - last) - 1)) *
                  (2 ^ (last - 3) - 1)
              else if last = size then Nat.fib (2 * (first - 1) - 1) *
                (2 ^ (size - first - 2) - 1) else 0
            else 0 := by
      classical
      let q : List ℕ := [1, 3, 2, 4]
      let words := {p : List ℕ | p.Perm (List.range' 1 size) ∧
        ∀ cut < size, Occurs q (p.rotate cut) ↔ cut = 0}
      have lengthEq (p : List ℕ) (hp : p.Perm (List.range' 1 size)) : p.length = size := by
        simpa using hp.length_eq
      have rotateSum (p : List ℕ) (hp : p.Perm (List.range' 1 size)) (a b : ℕ) :
          (p.rotate a).rotate b = p.rotate ((a + b) % size) := by
        rw [List.rotate_rotate, ← List.rotate_mod, lengthEq p hp]
      have shiftZero (a b : ℕ) (ha : a < size) (hb : b < size) :
          (a + b) % size = a ↔ b = 0 := by
        by_cases hs : a + b < size
        · rw [Nat.mod_eq_of_lt hs]; omega
        · have hh : size ≤ a + b := by omega
          rw [Nat.mod_eq_sub_mod hh, Nat.mod_eq_of_lt (by omega : a + b - size < size)]; omega
      let bad := fun (p : List ℕ) (hp : p ∈ singleBadCircles size q) =>
        Classical.choose hp.2.2
      have badSpec (p : List ℕ) (hp : p ∈ singleBadCircles size q) :
          bad p hp < size ∧ ∀ cut < size, Occurs q (p.rotate cut) ↔ cut = bad p hp :=
        Classical.choose_spec hp.2.2
      let emit := fun (p : List ℕ) (hp : p ∈ singleBadCircles size q) => p.rotate (bad p hp)
      have emitMember (p : List ℕ) (hp : p ∈ singleBadCircles size q) : emit p hp ∈ words := by
        have hs := badSpec p hp; refine ⟨(List.rotate_perm _ _).trans hp.1, ?_⟩
        intro cut hc; change Occurs q ((p.rotate (bad p hp)).rotate cut) ↔ cut = 0
        rw [rotateSum p hp.1, hs.2 _ (Nat.mod_lt _ (by omega))]; exact shiftZero _ _ hs.1 hc
      have rootUnique (u v : List ℕ) (hu : u.Perm (List.range' 1 size))
          (headU : u.head? = some 1) (headV : v.head? = some 1)
          (hr : List.IsRotated u v) : u = v := by
        obtain ⟨cut, he⟩ := hr
        have hb : cut % u.length < u.length := by rw [lengthEq u hu]; exact Nat.mod_lt _ (by omega)
        have hz : 0 < u.length := by rw [lengthEq u hu]; omega
        have hg : u[cut % u.length]? = u[0]? := by
          rw [← List.head?_rotate hb, List.rotate_mod, he, ← List.head?_eq_getElem?, headU, headV]
        rw [List.getElem?_eq_getElem hb, List.getElem?_eq_getElem hz, Option.some.injEq] at hg
        have hzero := (hu.nodup_iff.mpr List.nodup_range').getElem_inj_iff.mp hg
        rw [← List.rotate_mod u cut, hzero, List.rotate_zero] at he; exact he
      have emitInjective (u v : List ℕ) (hu : u ∈ singleBadCircles size q)
          (hv : v ∈ singleBadCircles size q) (he : emit u hu = emit v hv) : u = v := by
        apply rootUnique u v hu.1 hu.2.1 hv.2.1
        have hrU : List.IsRotated u (emit u hu) := (List.IsRotated.forall u (bad u hu)).symm
        have hrV : List.IsRotated (emit v hv) v := List.IsRotated.forall v (bad v hv)
        exact hrU.trans (he.symm ▸ hrV)
      have emitSurjective (p : List ℕ) (hp : p ∈ words) :
          ∃ (circle : List ℕ) (hc : circle ∈ singleBadCircles size q), emit circle hc = p := by
        have hm : 1 ∈ p := hp.1.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
        have hi : p.idxOf 1 < size := by
          have hh := List.idxOf_lt_length_iff.mpr hm; rw [lengthEq p hp.1] at hh; exact hh
        let root := p.rotate (p.idxOf 1)
        let back := (size - p.idxOf 1) % size
        have reverseRoot : root.rotate back = p := by
          rw [rotateSum p hp.1]; have he : (p.idxOf 1 + back) % size = 0 := by
            dsimp [back]; rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
              show p.idxOf 1 + (size - p.idxOf 1) = size by omega, Nat.mod_self]
          rw [he, List.rotate_zero]
        have rootMember : root ∈ singleBadCircles size q := by
          refine ⟨(List.rotate_perm _ _).trans hp.1, ?_, back, Nat.mod_lt _ (by omega), ?_⟩
          · rw [List.head?_rotate (by rwa [lengthEq p hp.1])]
            exact List.getElem?_idxOf hm
          · intro cut hc
            rw [rotateSum p hp.1, hp.2 _ (Nat.mod_lt _ (by omega))]
            change (p.idxOf 1 + cut) % size = 0 ↔ cut = (size - p.idxOf 1) % size
            by_cases hz : p.idxOf 1 = 0
            · simp [hz, Nat.mod_eq_of_lt hc]
            · have hb : size - p.idxOf 1 < size := by omega
              rw [Nat.mod_eq_of_lt hb]; by_cases hs : p.idxOf 1 + cut < size
              · rw [Nat.mod_eq_of_lt hs]; omega
              · rw [Nat.mod_eq_sub_mod (by omega : size ≤ p.idxOf 1 + cut),
                  Nat.mod_eq_of_lt (by omega : p.idxOf 1 + cut - size < size)]; omega
        have badEq : bad root rootMember = back := by
          have ho : Occurs q (root.rotate back) := by
            rw [reverseRoot]; simpa using (hp.2 0 (by omega)).mpr rfl
          exact ((badSpec root rootMember).2 _ (Nat.mod_lt _ (by omega))).mp ho |>.symm
        exact ⟨root, rootMember, by simp only [emit, badEq, reverseRoot]⟩
      have rootCard := Set.ncard_congr (s := singleBadCircles size q) (t := words)
        emit emitMember emitInjective emitSurjective
      have endpoints (p : List ℕ) (hp : p ∈ words) :
          ∃ first last interior, p = first :: interior ++ [last] ∧
            1 ≤ first ∧ first + 2 < last ∧ last ≤ size ∧ last < size + 1 := by
        have hl := lengthEq p hp.1
        obtain ⟨first, tail, split⟩ : ∃ first tail, p = first :: tail := by
          cases p with
          | nil => simp at hl; omega
          | cons first tail => exact ⟨first, tail, rfl⟩
        obtain ⟨last, interior, splitP⟩ : ∃ last interior, p = first :: interior ++ [last] := by
          have ht : tail.length = size - 1 := by rw [split] at hl; simp at hl; omega
          cases hr : tail.reverse with
          | nil => have hh := congrArg List.length hr; simp [ht] at hh; omega
          | cons last rest =>
            have hh := congrArg List.reverse hr
            simp only [List.reverse_reverse, List.reverse_cons] at hh
            exact ⟨last, rest.reverse, by rw [split, hh]; rfl⟩
        have criterion := (unique_bad_cut_iff size (by omega) q p (by decide) hp.1).mp hp.2
        obtain ⟨chosen, hi, hm, selected, _⟩ := criterion.1
        have h12 : chosen 1 < chosen 2 := by simpa [q] using hi 1 (by omega) (by decide)
        have h23 : chosen 2 < chosen 3 := by simpa [q] using hi 2 (by omega) (by decide)
        have h34 : chosen 3 < chosen 4 := by simpa [q] using hi 3 (by omega) (by decide)
        have firstUsed : chosen 1 = first := by
          by_contra hn
          apply criterion.2.2.1; have ht : (q.map chosen).Sublist p.tail := by
            rw [splitP] at selected ⊢; exact List.Sublist.of_cons_of_ne hn selected
          refine ⟨chosen, hi, ?_, ht, by simp⟩
          intro rank hlo hhi; apply ht.subset
          have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by change rank ≤ 4 at hhi; omega
          rcases hh with rfl | rfl | rfl | rfl <;> simp [q]
        have lastUsed : chosen 4 = last := by
          by_contra hn
          apply criterion.2.2.2; have selected' : [chosen 4, chosen 2, chosen 3, chosen 1].Sublist
              (last :: (first :: interior).reverse) := by
            simpa [q, splitP, List.reverse_append] using selected.reverse
          have ht := List.Sublist.of_cons_of_ne hn selected'
          have dropP : p.dropLast = first :: interior := by
            rw [splitP]; change ((first :: interior) ++ [last]).dropLast = _
            rw [List.dropLast_append_cons]; simp
          have ht : (q.map chosen).Sublist p.dropLast := by simpa [q, dropP] using ht.reverse
          refine ⟨chosen, hi, ?_, ht, by simp⟩
          intro rank hlo hhi; apply ht.subset
          have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by change rank ≤ 4 at hhi; omega
          rcases hh with rfl | rfl | rfl | rfl <;> simp [q]
        have lowBound := List.mem_range'_1.mp (hp.1.mem_iff.mp (hm 1 (by omega) (by decide)))
        have highBound := List.mem_range'_1.mp (hp.1.mem_iff.mp (hm 4 (by omega) (by decide)))
        exact ⟨first, last, interior, splitP, by omega, by omega, by omega, by omega⟩
      let slice := fun first last : Fin (size + 1) => {p : List ℕ | p ∈ words ∧
        p.head? = some first.val ∧ p.getLast? = some last.val}
      have finiteSlice (a b : Fin (size + 1)) : (slice a b).Finite := by
        apply (List.finite_toSet (List.range' 1 size).permutations).subset
        intro p hp; exact List.mem_permutations.mpr hp.1.1
      letI (a b : Fin (size + 1)) : Finite (slice a b) := (finiteSlice a b).to_subtype
      let family := Σ a : Fin (size + 1), Σ b : Fin (size + 1), slice a b
      let forget := fun element : family => element.2.2.val
      have forgetMember (element : family) : forget element ∈ words := element.2.2.property.1
      have forgetInjective : Function.Injective forget := by
        rintro ⟨a, b, p, hp⟩ ⟨c, d, r, hr⟩ he
        change p = r at he
        subst r; have hab : a = c := Fin.ext (Option.some.inj (hp.2.1.symm.trans hr.2.1))
        have hbd : b = d := Fin.ext (Option.some.inj (hp.2.2.symm.trans hr.2.2))
        subst c; subst d; rfl
      have forgetSurjective (p : List ℕ) (hp : p ∈ words) : ∃ element : family,
        forget element = p := by
        obtain ⟨a, b, interior, he, ha, hab, hu, hb⟩ := endpoints p hp
        have ah : p.head? = some a := by simp [he]
        have bh : p.getLast? = some b := by
          rw [he]; change ((a :: interior) ++ [b]).getLast? = some b
          rw [List.getLast?_append_cons]; rfl
        exact ⟨⟨⟨a, by omega⟩, ⟨b, hb⟩, ⟨p, hp, ah, bh⟩⟩, rfl⟩
      let f : family → words := fun element => ⟨forget element, forgetMember element⟩
      have fBijective : Function.Bijective f := by
        constructor
        · intro a b he; exact forgetInjective (congrArg Subtype.val he)
        · rintro ⟨p, hp⟩
          obtain ⟨element, he⟩ := forgetSurjective p hp
          exact ⟨element, Subtype.ext he⟩
      have familyCard := Nat.card_congr (Equiv.ofBijective f fBijective)
      have sliceCounts (a b : Fin (size + 1)) : (slice a b).ncard =
          if 1 ≤ a.val ∧ a.val + 2 < b.val ∧ b.val ≤ size then
            if a.val = 1 then
              (if b.val = size then 1 else Nat.fib (2 * (size - b.val) - 1)) *
                (2 ^ (b.val - 3) - 1)
            else if b.val = size then Nat.fib (2 * (a.val - 1) - 1) *
              (2 ^ (size - a.val - 2) - 1) else 0
          else 0 := by
        by_cases hh : 1 ≤ a.val ∧ a.val + 2 < b.val ∧ b.val ≤ size
        · rw [if_pos hh]
          have he : slice a b = {p : List ℕ | p.Perm (List.range' 1 size) ∧
              p.head? = some a.val ∧ p.getLast? = some b.val ∧
              ∀ cut < size, Occurs q (p.rotate cut) ↔ cut = 0} := by
            ext p; simp only [slice, words, Set.mem_setOf_eq]; tauto
          rw [he]; by_cases hc : a.val = 1
          · rw [if_pos hc]
            have count := RotationAvoidanceSlices.fibonacci_least_endpoint_count
              size b.val (by omega) hh.2.2
            simpa only [hc, q] using count
          · rw [if_neg hc]
            by_cases ht : b.val = size
            · rw [if_pos ht, ← he]
              let reflect := fun p : List ℕ => (p.map (fun value => size + 1 - value)).reverse
              have reflectPerm (word : List ℕ) (hp : word.Perm (List.range' 1 (size))) :
                  (reflect word).Perm (List.range' 1 (size)) := by
                have hr : (List.range' 1 (size)).map (fun value => (size + 1) - value) =
                    (List.range' 1 (size)).reverse := by
                  rw [List.reverse_range', List.range'_eq_map_range, List.map_map]
                  apply List.map_congr_left; intro value hv; dsimp; omega
                exact (List.reverse_perm _).trans
                  (((hp.map ((size + 1) - ·)).trans (List.Perm.of_eq hr)).trans
                    (List.reverse_perm _))
              have reflectTwice (word : List ℕ) (hp : word.Perm (List.range' 1 (size))) :
                  reflect (reflect word) = word := by
                simp only [reflect, List.map_reverse, List.reverse_reverse, List.map_map]
                conv_rhs => rw [← List.map_id word]
                apply List.map_congr_left; intro value hv
                have hh := List.mem_range'_1.mp (hp.mem_iff.mp hv); dsimp; omega
              have reflectOccurrence (width : ℕ) (pattern word : List ℕ)
                  (hp : pattern.Perm (List.range' 1 width)) (hl : letters pattern = width)
                  (hr : letters ((pattern.map (fun rank => width + 1 - rank)).reverse) = width)
                  (hw : word.Perm (List.range' 1 (size))) :
                  Occurs pattern word →
                    Occurs ((pattern.map (fun rank => width + 1 - rank)).reverse) (reflect
                      word) := by
                rintro ⟨witness, hi, hm, hs, _⟩
                let chosen := fun rank : ℕ => (size + 1) - witness (width + 1 - rank)
                have witnessBounds (rank : ℕ) (hlo : 1 ≤ rank) (hhi : rank ≤ width) :
                    1 ≤ witness rank ∧ witness rank < (size + 1) := by
                  have hh := List.mem_range'_1.mp (hw.mem_iff.mp (hm rank hlo (by rwa [hl]))); omega
                refine ⟨chosen, ?_, ?_, ?_, by simp⟩
                · intro rank hlo hhi
                  rw [hr] at hhi; have hh := hi (width - rank) (by omega) (by rw [hl]; omega)
                  have hb := witnessBounds (width + 1 - rank) (by omega) (by omega)
                  have he : width - rank + 1 = width + 1 - rank := by omega
                  rw [he] at hh; dsimp [chosen]
                  have he' : width + 1 - (rank + 1) = width - rank := by omega
                  rw [he']; omega
                · intro rank hlo hhi
                  rw [hr] at hhi; apply List.mem_reverse.mpr
                  exact List.mem_map.mpr ⟨witness (width + 1 - rank),
                    hm _ (by omega) (by rw [hl]; omega), rfl⟩
                · have ht := (hs.map (fun value => (size + 1) - value)).reverse
                  convert ht using 1
                  simp only [List.map_reverse, List.map_map]; congr 1
                  apply List.map_congr_left; intro rank hk
                  have hb := List.mem_range'_1.mp (hp.mem_iff.mp hk); dsimp [chosen]; congr 2; omega
              have reflectOccurs (p : List ℕ) (hp : p.Perm (List.range' 1 size)) :
                  Occurs q (reflect p) ↔ Occurs q p := by
                constructor
                · intro ho
                  have hh := reflectOccurrence 4 q (reflect p) (by decide) rfl rfl
                    (reflectPerm p hp) ho
                  rwa [reflectTwice p hp] at hh
                · exact reflectOccurrence 4 q p (by decide) rfl rfl hp
              have reflectWords (p : List ℕ) (hp : p ∈ words) : reflect p ∈ words := by
                refine ⟨reflectPerm p hp.1, ?_⟩
                intro cut hcut
                have he : (reflect p).rotate cut = reflect (p.rotate (size - cut)) := by
                  simp only [reflect, List.rotate_reverse, List.length_map, lengthEq p hp.1,
                    Nat.mod_eq_of_lt hcut, List.map_rotate]
                rw [he, reflectOccurs _ ((List.rotate_perm _ _).trans hp.1),
                  ← List.rotate_mod, lengthEq p hp.1, hp.2 _ (Nat.mod_lt _ (by omega))]
                by_cases hz : cut = 0
                · simp [hz]
                · rw [Nat.mod_eq_of_lt (by omega : size - cut < size)]
                  omega
              let left : Fin (size + 1) := ⟨1, by omega⟩
              let right : Fin (size + 1) := ⟨size + 1 - a.val, by omega⟩
              have mapMember (p : List ℕ) (hp : p ∈ slice a b) : reflect p ∈ slice left right := by
                refine ⟨reflectWords p hp.1, ?_, ?_⟩
                · simp [reflect, List.head?_reverse, List.getLast?_map, hp.2.2, ht, left]
                · simp [reflect, List.getLast?_reverse, List.head?_map, hp.2.1, right]
              have mapBack (p : List ℕ) (hp : p ∈ slice left right) : reflect p ∈ slice a b := by
                refine ⟨reflectWords p hp.1, ?_, ?_⟩
                · have hb : size + 1 - (size + 1 - a.val) = a.val := by omega
                  simp [reflect, List.head?_reverse, List.getLast?_map, hp.2.2, right, hb]
                · simp [reflect, List.getLast?_reverse, List.head?_map, hp.2.1, left, ht]
              have card := Set.ncard_congr (s := slice a b) (t := slice left right)
                (fun p _ => reflect p) mapMember (by
                  intro p r hp hr he; have hh := congrArg reflect he
                  rwa [reflectTwice p hp.1.1, reflectTwice r hr.1.1] at hh) (by
                  intro p hp; exact ⟨reflect p, mapBack p hp, reflectTwice p hp.1.1⟩)
              have refSlice : slice left right = {p : List ℕ | p.Perm (List.range' 1 size) ∧
                  p.head? = some 1 ∧ p.getLast? = some (size + 1 - a.val) ∧
                  ∀ cut < size, Occurs q (p.rotate cut) ↔ cut = 0} := by
                ext p; simp only [slice, words, left, right, Set.mem_setOf_eq]; tauto
              rw [card, refSlice]
              have count := RotationAvoidanceSlices.fibonacci_least_endpoint_count
                size (size + 1 - a.val) (by omega) (by omega)
              have outside : size + 1 - a.val ≠ size := by omega
              have high : size - (size + 1 - a.val) = a.val - 1 := by omega
              have middle : size + 1 - a.val - 3 = size - a.val - 2 := by omega
              simpa only [q, if_neg outside, high, middle] using count
            · rw [if_neg ht]
              have empty : {p : List ℕ | p.Perm (List.range' 1 size) ∧
                  p.head? = some a.val ∧ p.getLast? = some b.val ∧
                  ∀ cut < size, Occurs q (p.rotate cut) ↔ cut = 0} = ∅ := by
                apply Set.eq_empty_iff_forall_notMem.mpr; intro p hp
                obtain ⟨first, last, interior, split, ha, hab, hu, hb⟩ :=
                  endpoints p ⟨hp.1, hp.2.2.2⟩
                have head : first = a.val := by simpa [split] using hp.2.1
                have tail : last = b.val := by
                  have he : p.getLast? = some last := by
                    rw [split]; change ((first :: interior) ++ [last]).getLast? = some last
                    rw [List.getLast?_append_cons]; rfl
                  exact Option.some.inj (he.symm.trans hp.2.2.1)
                have form := RotationAvoidanceSlices.fibonacci_endpoint_extremality
                  size first last interior (by omega) (split ▸ hp.1) (split ▸ hp.2.2.2)
                rcases form with hfirst | hlast
                · exact hc (by omega)
                · exact ht (by omega)
              rw [empty, Set.ncard_empty]
        · rw [if_neg hh]
          have he : slice a b = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr; intro p hp
            obtain ⟨first, last, interior, split, ha, hab, hu, hb⟩ := endpoints p hp.1
            have head : first = a.val := by simpa [split] using hp.2.1
            have tail : last = b.val := by
              have he : p.getLast? = some last := by
                rw [split]; change ((first :: interior) ++ [last]).getLast? = some last
                rw [List.getLast?_append_cons]; rfl
              exact Option.some.inj (he.symm.trans hp.2.2)
            exact hh (by omega)
          rw [he, Set.ncard_empty]
      change (singleBadCircles size q).ncard = _
      rw [rootCard, ← Nat.card_coe_set_eq, ← familyCard]
      change Nat.card (Σ a : Fin (size + 1), Σ b : Fin (size + 1), slice a b) = _
      rw [Nat.card_sigma]; simp only [Nat.card_sigma, Nat.card_coe_set_eq, sliceCounts]
      let term := fun first last : ℕ =>
        if 1 ≤ first ∧ first + 2 < last ∧ last ≤ size then
          if first = 1 then
            (if last = size then 1 else Nat.fib (2 * (size - last) - 1)) *
              (2 ^ (last - 3) - 1)
          else if last = size then Nat.fib (2 * (first - 1) - 1) *
            (2 ^ (size - first - 2) - 1) else 0
        else 0
      change (∑ a : Fin (size + 1), ∑ b : Fin (size + 1), term a.val b.val) =
        ∑ a ∈ Finset.range (size + 1), ∑ b ∈ Finset.range (size + 1), term a b
      calc
        _ = ∑ a : Fin (size + 1), ∑ b ∈ Finset.range (size + 1), term a.val b := by
          apply Finset.sum_congr rfl; intro a ha
          exact Fin.sum_univ_eq_sum_range (term a.val) (size + 1)
        _ = _ := Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ Finset.range (size + 1),
          term a b) (size + 1)
    rw [fibonacci_single_bad_count size (by omega)]; have reindex := band (fun a b =>
      if a = 1 then (if b = size then 1 else C (size - b)) * d (b - 2)
      else if b = size then C (a - 1) * d (size - a - 1) else 0)
    have original : (∑ a ∈ Finset.range (size + 1),
        ∑ b ∈ Finset.range (size + 1),
        if 1 ≤ a ∧ a + 2 < b ∧ b ≤ size then
          if a = 1 then (if b = size then 1 else C (size - b)) * d (b - 2)
          else if b = size then C (a - 1) * d (size - a - 1) else 0 else 0) =
        (∑ a ∈ Finset.range (size + 1), ∑ b ∈ Finset.range (size + 1),
        if 1 ≤ a ∧ a + 2 < b ∧ b ≤ size then
          if a = 1 then (if b = size then 1 else Nat.fib (2 * (size - b) - 1)) *
            (2 ^ (b - 3) - 1)
          else if b = size then Nat.fib (2 * (a - 1) - 1) *
            (2 ^ (size - a - 2) - 1) else 0 else 0) := by
      simp only [C, d, Nat.sub_sub]
    rw [← original, reindex]; have row (t : ℕ) (ht : t < size + 1) :
        (∑ a ∈ Finset.range (size + 1),
          if 2 ≤ t ∧ 1 ≤ a ∧ a + t < size then
            if a = 1 then
              (if a + t + 1 = size then 1 else C (size - (a + t + 1))) * d (a + t - 1)
            else if a + t + 1 = size then C (a - 1) * d (size - a - 1) else 0 else 0) =
          if t = N then d N else if 2 ≤ t ∧ t < N then 2 * (C (N - t) * d t) else 0 := by
      by_cases hn : t = N
      · subst t
        have each (a : ℕ) :
            (if 2 ≤ N ∧ 1 ≤ a ∧ a + N < size then
              if a = 1 then
                (if a + N + 1 = size then 1 else C (size - (a + N + 1))) * d (a + N - 1)
              else if a + N + 1 = size then C (a - 1) * d (size - a - 1) else 0 else 0) =
              if a = 1 then d N else 0 := by
          by_cases ha : a = 1
          · subst a
            simp only [if_pos (by omega : 2 ≤ N ∧ 1 ≤ 1 ∧ 1 + N < size),
              if_true, if_pos (by omega : 1 + N + 1 = size), one_mul]
            rw [show 1 + N - 1 = N by omega]
          · rw [if_neg (by omega : ¬ (2 ≤ N ∧ 1 ≤ a ∧ a + N < size)), if_neg ha]
        simp_rw [each]
        simp [Finset.sum_ite_eq', show 1 < size + 1 by omega]
      · rw [if_neg hn]
        by_cases hi : 2 ≤ t ∧ t < N
        · rw [if_pos hi]
          have each (a : ℕ) :
              (if 2 ≤ t ∧ 1 ≤ a ∧ a + t < size then
                if a = 1 then
                  (if a + t + 1 = size then 1 else C (size - (a + t + 1))) * d (a + t - 1)
                else if a + t + 1 = size then C (a - 1) * d (size - a - 1) else 0 else 0) =
                (if a = 1 then C (N - t) * d t else 0) +
                  (if a = size - t - 1 then C (N - t) * d t else 0) := by
            by_cases ha : a = 1
            · subst a
              simp only [if_pos (by omega : 2 ≤ t ∧ 1 ≤ 1 ∧ 1 + t < size),
                if_true, if_neg (by omega : 1 + t + 1 ≠ size),
                if_neg (by omega : 1 ≠ size - t - 1), add_zero]
              rw [show size - (1 + t + 1) = N - t by omega,
                show 1 + t - 1 = t by omega]
            · by_cases hb : a = size - t - 1
              · subst a
                simp only [if_pos (by omega :
                    2 ≤ t ∧ 1 ≤ size - t - 1 ∧ size - t - 1 + t < size),
                  if_neg ha, if_pos (by omega : size - t - 1 + t + 1 = size),
                  if_true, zero_add]
                rw [show size - t - 1 - 1 = N - t by omega,
                  show size - (size - t - 1) - 1 = t by omega]
              · simp only [if_neg ha, if_neg hb, zero_add]
                split_ifs with hh hh
                · omega
                · rfl
                · rfl
          rw [Finset.sum_congr rfl (fun a _ => each a), Finset.sum_add_distrib]
          simp [Finset.sum_ite_eq', show 1 < size + 1 by omega,
            show size - t - 1 < size + 1 by omega, two_mul]
        · rw [if_neg hi]
          apply Finset.sum_eq_zero; intro a ha
          have impossible : ¬ (2 ≤ t ∧ 1 ≤ a ∧ a + t < size) := by omega
          simp [impossible]
    simp only [show ∀ a t : ℕ, a + t + 1 - 2 = a + t - 1 by omega]
    change (∑ t ∈ Finset.range (size + 1), _) = _
    rw [Finset.sum_congr rfl (fun t ht => row t (Finset.mem_range.mp ht))]
    have filterEq : (Finset.range (size + 1)).filter (fun t => 2 ≤ t ∧ t < N) =
        Finset.Ico 2 N := by
      ext t; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    have each (t : ℕ) :
        (if t = N then d N else if 2 ≤ t ∧ t < N then 2 * (C (N - t) * d t) else 0) =
          (if t = N then d N else 0) +
            (if 2 ≤ t ∧ t < N then 2 * (C (N - t) * d t) else 0) := by
      split_ifs <;> omega
    rw [Finset.sum_congr rfl (fun t _ => each t), Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_range, show N < size + 1 by omega, if_true]
    rw [← Finset.sum_filter, filterEq, ← Finset.mul_sum]
    have reflected : (∑ t ∈ Finset.Ico 2 N, C (N - t) * d t) =
        ∑ h ∈ Finset.Ico 1 (N - 1), C h * d (N - h) := by
      apply Finset.sum_bij (fun t _ => N - t)
      · intro t ht; have ht' := Finset.mem_Ico.mp ht
        apply Finset.mem_Ico.mpr; omega
      · intro t ht u hu he
        have ht' := Finset.mem_Ico.mp ht; have hu' := Finset.mem_Ico.mp hu; omega
      · intro h hh; have hh' := Finset.mem_Ico.mp hh
        exact ⟨N - h, Finset.mem_Ico.mpr (by omega), by omega⟩
      · intro t ht; have ht' := Finset.mem_Ico.mp ht
        rw [show N - (N - t) = t by omega]
    rw [reflected]
  have layeredTotal : (singleBadCircles size [1, 4, 2, 3]).ncard = B N := by
    have layered_single_bad_count (size : ℕ) (hsize : 5 ≤ size) :
        (singleBadCircles size [1, 4, 2, 3]).ncard =
          ∑ first ∈ Finset.range size, ∑ last ∈ Finset.range size,
            if 1 ≤ first ∧ first + 1 < last then
              if first = 1 then (last - 2) * Nat.fib (2 * (size - last) - 1)
              else Nat.fib (2 * (first - 1) - 1) * Nat.fib (2 * (size - last) - 1)
            else 0 := by
      classical
      let q : List ℕ := [1, 4, 2, 3]
      let words := {p : List ℕ | p.Perm (List.range' 1 size) ∧
        ∀ cut < size, Occurs q (p.rotate cut) ↔ cut = 0}
      have lengthEq (p : List ℕ) (hp : p.Perm (List.range' 1 size)) : p.length = size := by
        simpa using hp.length_eq
      have rotateSum (p : List ℕ) (hp : p.Perm (List.range' 1 size)) (a b : ℕ) :
          (p.rotate a).rotate b = p.rotate ((a + b) % size) := by
        rw [List.rotate_rotate, ← List.rotate_mod, lengthEq p hp]
      have shiftZero (a b : ℕ) (ha : a < size) (hb : b < size) :
          (a + b) % size = a ↔ b = 0 := by
        by_cases hs : a + b < size
        · rw [Nat.mod_eq_of_lt hs]; omega
        · have hh : size ≤ a + b := by omega
          rw [Nat.mod_eq_sub_mod hh, Nat.mod_eq_of_lt (by omega : a + b - size < size)]; omega
      let bad := fun (p : List ℕ) (hp : p ∈ singleBadCircles size q) =>
        Classical.choose hp.2.2
      have badSpec (p : List ℕ) (hp : p ∈ singleBadCircles size q) :
          bad p hp < size ∧ ∀ cut < size, Occurs q (p.rotate cut) ↔ cut = bad p hp :=
        Classical.choose_spec hp.2.2
      let emit := fun (p : List ℕ) (hp : p ∈ singleBadCircles size q) => p.rotate (bad p hp)
      have emitMember (p : List ℕ) (hp : p ∈ singleBadCircles size q) : emit p hp ∈ words := by
        have hs := badSpec p hp; refine ⟨(List.rotate_perm _ _).trans hp.1, ?_⟩
        intro cut hc; change Occurs q ((p.rotate (bad p hp)).rotate cut) ↔ cut = 0
        rw [rotateSum p hp.1, hs.2 _ (Nat.mod_lt _ (by omega))]; exact shiftZero _ _ hs.1 hc
      have rootUnique (u v : List ℕ) (hu : u.Perm (List.range' 1 size))
          (headU : u.head? = some 1) (headV : v.head? = some 1)
          (hr : List.IsRotated u v) : u = v := by
        obtain ⟨cut, he⟩ := hr
        have hb : cut % u.length < u.length := by rw [lengthEq u hu]; exact Nat.mod_lt _ (by omega)
        have hz : 0 < u.length := by rw [lengthEq u hu]; omega
        have hg : u[cut % u.length]? = u[0]? := by
          rw [← List.head?_rotate hb, List.rotate_mod, he, ← List.head?_eq_getElem?, headU, headV]
        rw [List.getElem?_eq_getElem hb, List.getElem?_eq_getElem hz, Option.some.injEq] at hg
        have hzero := (hu.nodup_iff.mpr List.nodup_range').getElem_inj_iff.mp hg
        rw [← List.rotate_mod u cut, hzero, List.rotate_zero] at he; exact he
      have emitInjective (u v : List ℕ) (hu : u ∈ singleBadCircles size q)
          (hv : v ∈ singleBadCircles size q) (he : emit u hu = emit v hv) : u = v := by
        apply rootUnique u v hu.1 hu.2.1 hv.2.1
        have hrU : List.IsRotated u (emit u hu) := (List.IsRotated.forall u (bad u hu)).symm
        have hrV : List.IsRotated (emit v hv) v := List.IsRotated.forall v (bad v hv)
        exact hrU.trans (he.symm ▸ hrV)
      have emitSurjective (p : List ℕ) (hp : p ∈ words) :
          ∃ (circle : List ℕ) (hc : circle ∈ singleBadCircles size q), emit circle hc = p := by
        have hm : 1 ∈ p := hp.1.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
        have hi : p.idxOf 1 < size := by
          have hh := List.idxOf_lt_length_iff.mpr hm; rw [lengthEq p hp.1] at hh; exact hh
        let root := p.rotate (p.idxOf 1)
        let back := (size - p.idxOf 1) % size
        have reverseRoot : root.rotate back = p := by
          rw [rotateSum p hp.1]; have he : (p.idxOf 1 + back) % size = 0 := by
            dsimp [back]; rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
              show p.idxOf 1 + (size - p.idxOf 1) = size by omega, Nat.mod_self]
          rw [he, List.rotate_zero]
        have rootMember : root ∈ singleBadCircles size q := by
          refine ⟨(List.rotate_perm _ _).trans hp.1, ?_, back, Nat.mod_lt _ (by omega), ?_⟩
          · rw [List.head?_rotate (by rwa [lengthEq p hp.1])]
            exact List.getElem?_idxOf hm
          · intro cut hc
            rw [rotateSum p hp.1, hp.2 _ (Nat.mod_lt _ (by omega))]
            change (p.idxOf 1 + cut) % size = 0 ↔ cut = (size - p.idxOf 1) % size
            by_cases hz : p.idxOf 1 = 0
            · simp [hz, Nat.mod_eq_of_lt hc]
            · have hb : size - p.idxOf 1 < size := by omega
              rw [Nat.mod_eq_of_lt hb]; by_cases hs : p.idxOf 1 + cut < size
              · rw [Nat.mod_eq_of_lt hs]; omega
              · rw [Nat.mod_eq_sub_mod (by omega : size ≤ p.idxOf 1 + cut),
                  Nat.mod_eq_of_lt (by omega : p.idxOf 1 + cut - size < size)]; omega
        have badEq : bad root rootMember = back := by
          have ho : Occurs q (root.rotate back) := by
            rw [reverseRoot]; simpa using (hp.2 0 (by omega)).mpr rfl
          exact ((badSpec root rootMember).2 _ (Nat.mod_lt _ (by omega))).mp ho |>.symm
        exact ⟨root, rootMember, by simp only [emit, badEq, reverseRoot]⟩
      have rootCard := Set.ncard_congr (s := singleBadCircles size q) (t := words)
        emit emitMember emitInjective emitSurjective
      have endpoints (p : List ℕ) (hp : p ∈ words) :
          ∃ first last interior, p = first :: interior ++ [last] ∧
            1 ≤ first ∧ first + 1 < last ∧ last < size := by
        have hl := lengthEq p hp.1
        obtain ⟨first, tail, split⟩ : ∃ first tail, p = first :: tail := by
          cases p with
          | nil => simp at hl; omega
          | cons first tail => exact ⟨first, tail, rfl⟩
        obtain ⟨last, interior, splitP⟩ : ∃ last interior, p = first :: interior ++ [last] := by
          have ht : tail.length = size - 1 := by rw [split] at hl; simp at hl; omega
          cases hr : tail.reverse with
          | nil => have hh := congrArg List.length hr; simp [ht] at hh; omega
          | cons last rest =>
            have hh := congrArg List.reverse hr
            simp only [List.reverse_reverse, List.reverse_cons] at hh
            exact ⟨last, rest.reverse, by rw [split, hh]; rfl⟩
        have criterion := (unique_bad_cut_iff size (by omega) q p (by decide) hp.1).mp hp.2
        obtain ⟨chosen, hi, hm, selected, _⟩ := criterion.1
        have h12 : chosen 1 < chosen 2 := by simpa [q] using hi 1 (by omega) (by decide)
        have h23 : chosen 2 < chosen 3 := by simpa [q] using hi 2 (by omega) (by decide)
        have h34 : chosen 3 < chosen 4 := by simpa [q] using hi 3 (by omega) (by decide)
        have firstUsed : chosen 1 = first := by
          by_contra hn
          apply criterion.2.2.1; have ht : (q.map chosen).Sublist p.tail := by
            rw [splitP] at selected ⊢; exact List.Sublist.of_cons_of_ne hn selected
          refine ⟨chosen, hi, ?_, ht, by simp⟩
          intro rank hlo hhi; apply ht.subset
          have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by change rank ≤ 4 at hhi; omega
          rcases hh with rfl | rfl | rfl | rfl <;> simp [q]
        have lastUsed : chosen 3 = last := by
          by_contra hn
          apply criterion.2.2.2; have selected' : [chosen 3, chosen 2, chosen 4, chosen 1].Sublist
              (last :: (first :: interior).reverse) := by
            simpa [q, splitP, List.reverse_append] using selected.reverse
          have ht := List.Sublist.of_cons_of_ne hn selected'
          have dropP : p.dropLast = first :: interior := by
            rw [splitP]; change ((first :: interior) ++ [last]).dropLast = _
            rw [List.dropLast_append_cons]; simp
          have ht : (q.map chosen).Sublist p.dropLast := by simpa [q, dropP] using ht.reverse
          refine ⟨chosen, hi, ?_, ht, by simp⟩
          intro rank hlo hhi; apply ht.subset
          have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by change rank ≤ 4 at hhi; omega
          rcases hh with rfl | rfl | rfl | rfl <;> simp [q]
        have lowBound := List.mem_range'_1.mp (hp.1.mem_iff.mp (hm 1 (by omega) (by decide)))
        have highBound := List.mem_range'_1.mp (hp.1.mem_iff.mp (hm 4 (by omega) (by decide)))
        exact ⟨first, last, interior, splitP, by omega, by omega, by omega⟩
      let slice := fun first last : Fin size => {p : List ℕ | p ∈ words ∧
        p.head? = some first.val ∧ p.getLast? = some last.val}
      have finiteSlice (a b : Fin size) : (slice a b).Finite := by
        apply (List.finite_toSet (List.range' 1 size).permutations).subset
        intro p hp; exact List.mem_permutations.mpr hp.1.1
      letI (a b : Fin size) : Finite (slice a b) := (finiteSlice a b).to_subtype
      let family := Σ a : Fin size, Σ b : Fin size, slice a b
      let forget := fun element : family => element.2.2.val
      have forgetMember (element : family) : forget element ∈ words := element.2.2.property.1
      have forgetInjective : Function.Injective forget := by
        rintro ⟨a, b, p, hp⟩ ⟨c, d, r, hr⟩ he
        change p = r at he
        subst r; have hab : a = c := Fin.ext (Option.some.inj (hp.2.1.symm.trans hr.2.1))
        have hbd : b = d := Fin.ext (Option.some.inj (hp.2.2.symm.trans hr.2.2))
        subst c; subst d; rfl
      have forgetSurjective (p : List ℕ) (hp : p ∈ words) : ∃ element : family,
        forget element = p := by
        obtain ⟨a, b, interior, he, ha, hab, hb⟩ := endpoints p hp
        have ah : p.head? = some a := by simp [he]
        have bh : p.getLast? = some b := by
          rw [he]; change ((a :: interior) ++ [b]).getLast? = some b
          rw [List.getLast?_append_cons]; rfl
        exact ⟨⟨⟨a, by omega⟩, ⟨b, hb⟩, ⟨p, hp, ah, bh⟩⟩, rfl⟩
      let f : family → words := fun element => ⟨forget element, forgetMember element⟩
      have fBijective : Function.Bijective f := by
        constructor
        · intro a b he; exact forgetInjective (congrArg Subtype.val he)
        · rintro ⟨p, hp⟩
          obtain ⟨element, he⟩ := forgetSurjective p hp
          exact ⟨element, Subtype.ext he⟩
      have familyCard := Nat.card_congr (Equiv.ofBijective f fBijective)
      have sliceCounts (a b : Fin size) : (slice a b).ncard =
          if 1 ≤ a.val ∧ a.val + 1 < b.val then
            if a.val = 1 then (b.val - 2) * Nat.fib (2 * (size - b.val) - 1)
            else Nat.fib (2 * (a.val - 1) - 1) * Nat.fib (2 * (size - b.val) - 1)
          else 0 := by
        by_cases hh : 1 ≤ a.val ∧ a.val + 1 < b.val
        · rw [if_pos hh]
          have he : slice a b = {p : List ℕ | p.Perm (List.range' 1 size) ∧
              p.head? = some a.val ∧ p.getLast? = some b.val ∧
              ∀ cut < size, Occurs q (p.rotate cut) ↔ cut = 0} := by
            ext p; simp only [slice, words, Set.mem_setOf_eq]; tauto
          rw [he]; by_cases hc : a.val = 1
          · rw [if_pos hc]
            have count := RotationAvoidanceLayeredEmpty.layered_empty_lower_endpoint_count
              size b.val (by omega) b.isLt
            simpa only [hc, q] using count
          · rw [if_neg hc]
            have count := RotationAvoidanceLayeredCount.layered_nonempty_lower_endpoint_count
              size a.val b.val (by omega) hh.2 b.isLt
            simpa only [q, Nat.mul_comm] using count
        · rw [if_neg hh]
          have he : slice a b = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr; intro p hp
            obtain ⟨first, last, interior, split, ha, hab, hb⟩ := endpoints p hp.1
            have head : first = a.val := by simpa [split] using hp.2.1
            have tail : last = b.val := by
              have he : p.getLast? = some last := by
                rw [split]; change ((first :: interior) ++ [last]).getLast? = some last
                rw [List.getLast?_append_cons]; rfl
              exact Option.some.inj (he.symm.trans hp.2.2)
            exact hh (by omega)
          rw [he, Set.ncard_empty]
      change (singleBadCircles size q).ncard = _
      rw [rootCard, ← Nat.card_coe_set_eq, ← familyCard]
      change Nat.card (Σ a : Fin size, Σ b : Fin size, slice a b) = _
      rw [Nat.card_sigma]; simp only [Nat.card_sigma, Nat.card_coe_set_eq, sliceCounts]
      let term := fun first last : ℕ =>
        if 1 ≤ first ∧ first + 1 < last then
          if first = 1 then (last - 2) * Nat.fib (2 * (size - last) - 1)
          else Nat.fib (2 * (first - 1) - 1) * Nat.fib (2 * (size - last) - 1)
        else 0
      change (∑ a : Fin size, ∑ b : Fin size, term a.val b.val) =
        ∑ a ∈ Finset.range size, ∑ b ∈ Finset.range size, term a b
      calc
        _ = ∑ a : Fin size, ∑ b ∈ Finset.range size, term a.val b := by
          apply Finset.sum_congr rfl; intro a ha; exact Fin.sum_univ_eq_sum_range (term a.val) size
        _ = _ := Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ Finset.range size, term a b) size
    rw [layered_single_bad_count size (by omega)]
    let term := fun a b : ℕ => if 1 ≤ a ∧ a + 1 < b then
      if a = 1 then (b - 2) * C (size - b) else C (a - 1) * C (size - b) else 0
    change (∑ a ∈ Finset.range size, ∑ b ∈ Finset.range size, term a b) = _
    rw [Finset.sum_comm]; have row (b : ℕ) (hb : b < size) : (∑ a ∈ Finset.range size, term a b) =
        if 3 ≤ b then (b - 2 + S (b - 3)) * C (size - b) else 0 := by
      by_cases hi : 3 ≤ b
      · rw [if_pos hi]
        have each (a : ℕ) : term a b =
            (if a = 1 then (b - 2) * C (size - b) else 0) +
              (if 2 ≤ a ∧ a < b - 1 then C (a - 1) * C (size - b) else 0) := by
          dsimp [term]; by_cases ha : a = 1
          · subst a
            simp only [if_pos (by omega : 1 ≤ 1 ∧ 1 + 1 < b), if_true,
              if_neg (by omega : ¬ (2 ≤ 1 ∧ 1 < b - 1)), add_zero]
          · have hc : (1 ≤ a ∧ a + 1 < b) ↔ (2 ≤ a ∧ a < b - 1) := by omega
            simp only [if_neg ha, zero_add, hc]
        rw [Finset.sum_congr rfl (fun a _ => each a), Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq', Finset.mem_range, show 1 < size by omega, if_true]
        have filterEq : (Finset.range size).filter (fun a => 2 ≤ a ∧ a < b - 1) =
            Finset.Ico 2 (b - 1) := by
          ext a; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
        rw [← Finset.sum_filter, filterEq, ← Finset.sum_mul]
        have shift : (∑ a ∈ Finset.Ico 2 (b - 1), C (a - 1)) = S (b - 3) := by
          dsimp [S]; apply Finset.sum_bij (fun a _ => a - 1)
          · intro a ha; have ha' := Finset.mem_Ico.mp ha
            apply Finset.mem_Ico.mpr; omega
          · intro a ha c hc he
            have ha' := Finset.mem_Ico.mp ha; have hc' := Finset.mem_Ico.mp hc; omega
          · intro h hh; have hh' := Finset.mem_Ico.mp hh
            exact ⟨h + 1, Finset.mem_Ico.mpr (by omega), by omega⟩
          · intro a ha; rfl
        rw [shift]; ring
      · rw [if_neg hi]
        apply Finset.sum_eq_zero; intro a ha; have impossible : ¬ (1 ≤ a ∧ a + 1 < b) := by omega
        simp [term, impossible]
    rw [Finset.sum_congr rfl (fun b hb => row b (Finset.mem_range.mp hb))]
    have filterEq : (Finset.range size).filter (fun b => 3 ≤ b) = Finset.Ico 3 size := by
      ext b; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    rw [← Finset.sum_filter, filterEq]; dsimp [B]; apply Finset.sum_bij (fun b _ => size - b)
    · intro b hb; have hb' := Finset.mem_Ico.mp hb
      apply Finset.mem_Ico.mpr; omega
    · intro b hb c hc he
      have hb' := Finset.mem_Ico.mp hb; have hc' := Finset.mem_Ico.mp hc; omega
    · intro h hh; have hh' := Finset.mem_Ico.mp hh
      exact ⟨size - h, Finset.mem_Ico.mpr (by omega), by omega⟩
    · intro b hb; have hb' := Finset.mem_Ico.mp hb
      rw [show N - (size - b) = b - 2 by omega,
        show b - 2 - 1 = b - 3 by omega]
  rw [ascendingTotal, layeredTotal]; exact (countGap N (by omega)).2 hN

end D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceFibonacciGap
