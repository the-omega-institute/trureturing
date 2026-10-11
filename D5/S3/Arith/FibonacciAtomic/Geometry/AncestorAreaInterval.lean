/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInterval
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInterval
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Native ancestor coordinates characterize complete addressed subtree intervals. -/

import D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity
import D5.S3.Arith.FibonacciAtomic.ActualJointResponseCostCore
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Algebra.BigOperators.Group.List.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInterval
open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address leaves)
open ActualLeafHistoryRigidity (subtree)

/-- Inorder gap coordinates: the root gap follows every left-child gap. -/
def coordinates : Source → List ℕ
  | .of _ => []
  | .mul l r => coordinates l ++ [l.length * r.length] ++ coordinates r

/-- Sum of the actual gap coordinates from a through b-1, with one-based leaves. -/
def area (t : Source) (a b : ℕ) : ℕ :=
  (((coordinates t).drop (a-1)).take (b-a)).sum

/-- Number of ambient leaves strictly before an addressed occurrence. -/
def offset : Source → Address → ℕ
  | _, [] => 0
  | .of _, _ :: _ => 0
  | .mul l _, false :: u => offset l u
  | .mul l r, true :: u => l.length + offset r u

/-- An actual addressed occurrence occupies exactly this ordered leaf interval.
The list equation retains the ambient leaf addresses, even when labels repeat. -/
def CompleteSubtree (t : Source) (a b : ℕ) : Prop :=
  ∃ (u : Address) (s : Source), subtree u t = some s ∧
    a = offset t u + 1 ∧ b = offset t u + s.length ∧
    ((leaves t).drop (a-1)).take (b-a+1) = (leaves s).map (u ++ ·)

/-- Recursive evaluation of an interval sum by its position relative to the root gap. -/
private def splitArea : Source → ℕ → ℕ → ℕ
  | .of _, _, _ => 0
  | .mul l r, a, b =>
    if b ≤ l.length then splitArea l a b
    else if l.length < a then splitArea r (a-l.length) (b-l.length)
    else splitArea l a l.length + l.length*r.length + splitArea r 1 (b-l.length)

set_option maxHeartbeats 1600000 in
-- Native interval and occurrence inductions share the proof budget.
/-- Every nonempty native interval has the binomial lower bound, with equality
exactly at the complete leaf interval of an actual subtree occurrence. -/
theorem ancestor_area_interval (t : Source) (a b : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ t.length) :
    Nat.choose (b-a+1) 2 ≤ area t a b ∧
    (area t a b = Nat.choose (b-a+1) 2 ↔ CompleteSubtree t a b) := by
  have leafLength (s : Source) : (leaves s).length = s.length := by
    rw [← List.toFinset_card_of_nodup (ActualJointResponseCostCore.cost_foundation.1 s).1]
    exact (ActualImageSevenLeafSeparation.seven_leaf_separation.1 s).1
  have occurrence : ∀ (u : Address) (t s : Source), subtree u t = some s →
      offset t u + s.length ≤ t.length ∧
      ((leaves t).drop (offset t u)).take s.length = (leaves s).map (u ++ ·) := by
    intro u
    induction u with
    | nil =>
      intro t s h
      have he : t = s := Option.some.inj h
      subst s
      simp [offset, leafLength]
    | cons d u ih =>
      intro t s h
      cases t with
      | of c => simp [subtree] at h
      | mul l r =>
        cases d with
        | false =>
          obtain ⟨hn, he⟩ := ih l s h
          refine ⟨by simpa [offset, FreeMagma.length] using hn.trans (Nat.le_add_right _ _), ?_⟩
          simp only [offset, leaves]
          rw [List.drop_append_of_le_length (by simp only [List.length_map, leafLength]; omega),
            List.take_append_of_le_length (by
              simp only [List.length_drop, List.length_map, leafLength]; omega),
            ← List.map_drop, ← List.map_take, he, List.map_map]
          rfl
        | true =>
          obtain ⟨hn, he⟩ := ih r s h
          refine ⟨by simp only [offset, FreeMagma.length]; omega, ?_⟩
          simp only [offset, leaves]
          rw [List.drop_append,
            List.drop_eq_nil_of_le (by simp only [List.length_map, leafLength]; omega),
            List.nil_append]
          simp only [List.length_map, leafLength, Nat.add_sub_cancel_left]
          rw [← List.map_drop, ← List.map_take, he, List.map_map]
          rfl
  have coordLength : ∀ s : Source, (coordinates s).length = s.length-1 := by
    intro s
    induction s with
    | of c => rfl
    | mul l r hl hr =>
      have hp := FreeMagma.length_pos l
      have hq := FreeMagma.length_pos r
      simp only [coordinates, List.length_append, List.length_singleton, hl, hr, FreeMagma.length]
      omega
  have evaluation : ∀ (s : Source) (a b : ℕ), 1 ≤ a → a ≤ b → b ≤ s.length →
      area s a b = splitArea s a b := by
    intro s
    induction s with
    | of c => intro a b ha hab hb; simp [area, coordinates, splitArea]
    | mul l r hl hr =>
      intro a b ha hab hb
      have hp := FreeMagma.length_pos l
      have hq := FreeMagma.length_pos r
      simp only [FreeMagma.length] at hb
      by_cases hleft : b ≤ l.length
      · have ht : (((coordinates (.mul l r)).drop (a-1)).take (b-a)) =
            ((coordinates l).drop (a-1)).take (b-a) := by
          simp only [coordinates, List.append_assoc]
          rw [List.drop_append_of_le_length (by rw [coordLength]; omega),
            List.take_append_of_le_length (by rw [List.length_drop, coordLength]; omega)]
        simp only [area, ht, splitArea, if_pos hleft]
        exact hl a b ha hab hleft
      · by_cases hright : l.length < a
        · have ht : (((coordinates (.mul l r)).drop (a-1)).take (b-a)) =
              ((coordinates r).drop ((a-l.length)-1)).take ((b-l.length)-(a-l.length)) := by
            rw [coordinates, List.drop_append,
              List.drop_eq_nil_of_le (by
                simp only [List.length_append, List.length_singleton, coordLength]; omega),
              List.nil_append]
            simp only [List.length_append, List.length_singleton, coordLength]
            have hn : a-1-(l.length-1+1) = a-l.length-1 := by omega
            have hm : b-a = b-l.length-(a-l.length) := by omega
            rw [hn,hm]
          simp only [area, ht, splitArea, if_neg hleft, if_pos hright]
          exact hr _ _ (by omega) (by omega) (by omega)
        · have ht : (((coordinates (.mul l r)).drop (a-1)).take (b-a)) =
              (coordinates l).drop (a-1) ++ [l.length*r.length] ++
                (coordinates r).take (b-l.length-1) := by
            simp only [coordinates, List.append_assoc]
            rw [List.drop_append_of_le_length (by rw [coordLength]; omega),
              List.take_append,
              List.take_of_length_le (by rw [List.length_drop, coordLength]; omega)]
            have hn : b-a-((coordinates l).drop (a-1)).length = (b-l.length-1)+1 := by
              rw [List.length_drop, coordLength]; omega
            rw [hn]
            simp only [List.singleton_append, List.take_succ_cons]
          have hls := hl a l.length ha (by omega) (by omega)
          have hrs := hr 1 (b-l.length) (by omega) (by omega) (by omega)
          simp only [area, Nat.sub_self, List.drop_zero] at hrs
          simp only [area] at hls
          rw [List.take_of_length_le (by rw [List.length_drop, coordLength]; omega)] at hls
          simp only [area, ht, List.sum_append, List.sum_singleton, splitArea,
            if_neg hleft, if_neg hright]
          rw [hls, hrs]
  have binomial (x y : ℕ) : Nat.choose (x+y) 2 =
      Nat.choose x 2 + Nat.choose y 2 + x*y := by
    rw [Nat.add_choose_eq]
    simp [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
      Nat.choose_one_right]
    ring
  have bounds : ∀ (s : Source) (a b : ℕ), 1 ≤ a → a ≤ b → b ≤ s.length →
      Nat.choose (b-a+1) 2 ≤ splitArea s a b ∧
      (splitArea s a b = Nat.choose (b-a+1) 2 ↔
        ∃ (u : Address) (v : Source), subtree u s = some v ∧
          a = offset s u+1 ∧ b = offset s u+v.length) := by
    intro s
    induction s with
    | of c =>
      intro a b ha hab hb
      have ha' : a = 1 := by simp only [FreeMagma.length] at hb; omega
      have hb' : b = 1 := by simp only [FreeMagma.length] at hb; omega
      subst a; subst b
      simp only [splitArea, Nat.sub_self, Nat.zero_add,
        Nat.choose_eq_zero_of_lt (by decide : 1 < 2)]
      exact ⟨by omega, iff_of_true trivial ⟨[], .of c, rfl, rfl, rfl⟩⟩
    | mul l r hl hr =>
      intro a b ha hab hb
      have hp := FreeMagma.length_pos l
      have hq := FreeMagma.length_pos r
      simp only [FreeMagma.length] at hb
      by_cases hleft : b ≤ l.length
      · rw [splitArea, if_pos hleft]
        obtain ⟨hn, he⟩ := hl a b ha hab hleft
        refine ⟨hn, he.trans ?_⟩
        constructor
        · rintro ⟨u,v,hu,ha,hb⟩
          exact ⟨false :: u,v,hu,ha,hb⟩
        · rintro ⟨u,v,hu,ha,hb⟩
          cases u with
          | nil =>
            simp only [subtree, Option.some.injEq] at hu
            subst v
            simp only [offset, FreeMagma.length] at hb
            omega
          | cons d u =>
            cases d with
            | false => exact ⟨u,v,hu,ha,hb⟩
            | true => simp only [offset] at ha; omega
      · by_cases hright : l.length < a
        · rw [splitArea, if_neg hleft, if_pos hright]
          obtain ⟨hn, he⟩ := hr (a-l.length) (b-l.length) (by omega) (by omega) (by omega)
          have hk : b-l.length-(a-l.length)+1 = b-a+1 := by omega
          rw [hk] at hn he
          refine ⟨hn, he.trans ?_⟩
          constructor
          · rintro ⟨u,v,hu,ha',hb'⟩
            refine ⟨true :: u,v,hu,?_,?_⟩ <;> simp only [offset] <;> omega
          · rintro ⟨u,v,hu,ha',hb'⟩
            cases u with
            | nil => simp [offset] at ha'; omega
            | cons d u =>
              cases d with
              | false =>
                have hv := (occurrence u l v hu).1
                simp only [offset] at hb'
                omega
              | true =>
                exact ⟨u,v,hu,by simp only [offset] at ha'; omega,
                  by simp only [offset] at hb'; omega⟩
        · rw [splitArea, if_neg hleft, if_neg hright]
          obtain ⟨hnl, hel⟩ := hl a l.length ha (by omega) (by omega)
          obtain ⟨hnr, her⟩ := hr 1 (b-l.length) (by omega) (by omega) (by omega)
          let x := l.length-a+1
          let y := b-l.length
          have hx : 0 < x := by dsimp [x]; omega
          have hy : 0 < y := by dsimp [y]; omega
          have hxp : x ≤ l.length := by dsimp [x]; omega
          have hyq : y ≤ r.length := by dsimp [y]; omega
          have hk : b-a+1 = x+y := by dsimp [x,y]; omega
          have hprod : x*y ≤ l.length*r.length := Nat.mul_le_mul hxp hyq
          have hbin := binomial x y
          change Nat.choose x 2 ≤ splitArea l a l.length at hnl
          have hyn : b-l.length-1+1 = y := by dsimp [y]; omega
          rw [hyn] at hnr
          rw [hk, hbin]
          refine ⟨by omega, ?_⟩
          have heq : splitArea l a l.length + l.length*r.length + splitArea r 1 (b-l.length) =
              Nat.choose x 2 + Nat.choose y 2 + x*y ↔ a = 1 ∧ b = l.length+r.length := by
            constructor
            · intro he
              have hmul : l.length*r.length = x*y := by omega
              have hp' : l.length = x := by nlinarith
              have hq' : r.length = y := by nlinarith
              dsimp [x,y] at hp' hq'
              omega
            · rintro ⟨rfl,rfl⟩
              have el := (hl 1 l.length (by omega) (by omega) (by omega)).2.mpr
                ⟨[],l,rfl,by simp [offset],by simp [offset]⟩
              have er := (hr 1 r.length (by omega) (by omega) (by omega)).2.mpr
                ⟨[],r,rfl,by simp [offset],by simp [offset]⟩
              have hpl : l.length-1+1 = l.length := by omega
              have hqr : r.length-1+1 = r.length := by omega
              rw [hpl] at el
              rw [hqr] at er
              dsimp [x,y]
              simp only [Nat.add_sub_cancel_left, hpl]
              rw [el,er]
              omega
          refine heq.trans ?_
          constructor
          · rintro ⟨ha',hb'⟩
            exact ⟨[],.mul l r,rfl,by simpa [offset] using ha',
              by simpa [offset,FreeMagma.length] using hb'⟩
          · rintro ⟨u,v,hu,ha',hb'⟩
            cases u with
            | nil =>
              simp only [subtree, Option.some.injEq] at hu
              subst v
              simpa [offset,FreeMagma.length] using And.intro ha' hb'
            | cons d u =>
              cases d with
              | false =>
                have hv := (occurrence u l v hu).1
                simp only [offset] at hb'
                omega
              | true => simp only [offset] at ha'; omega
  rw [evaluation t a b ha hab hb]
  obtain ⟨hn,he⟩ := bounds t a b ha hab hb
  refine ⟨hn, he.trans ?_⟩
  constructor
  · rintro ⟨u,s,hs,ha',hb'⟩
    refine ⟨u,s,hs,ha',hb',?_⟩
    obtain ⟨_,hleaves⟩ := occurrence u t s hs
    rw [ha',hb']
    have hp := FreeMagma.length_pos s
    convert hleaves using 1 <;> (congr 1; omega)
  · rintro ⟨u,s,hs,ha',hb',_⟩
    exact ⟨u,s,hs,ha',hb'⟩

end D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInterval

#print axioms D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInterval.ancestor_area_interval
