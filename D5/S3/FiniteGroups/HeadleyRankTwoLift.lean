/- GID: D5/S3/FiniteGroups/HeadleyRankTwoLift
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/HeadleyRankTwoLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two oppositely directed row tracks lift the native circular-length path. -/

import D5.S3.FiniteGroups.HeadleyRankTwoPath
import D5.S3.FiniteGroups.HeadleyExtension
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.FiniteGroups.HeadleyRankTwoLift
open HeadleyRankTwoPath

private theorem path_vertices (m : ℕ) (p : LengthPath m) :
    p.tail.Nodup ∧ (∀ x, x ∈ p.tail ↔ 1 ≤ x ∧ x < 2*m) ∧
      p.tail.length + 1 = 2*m := by
  have hN : (0 :: p.tail).Nodup := p.vertex_inventory.nodup_iff.mpr List.nodup_range
  have hM (x : ℕ) : x = 0 ∨ x ∈ p.tail ↔ x < 2*m := by
    simpa only [List.mem_cons, List.mem_range] using p.vertex_inventory.mem_iff (a := x)
  have hC := p.vertex_inventory.length_eq
  simp only [List.length_cons,List.length_range] at hC
  refine ⟨hN.of_cons, ?_, hC⟩
  intro x
  have h0 : 0 ∉ p.tail := hN.not_mem
  have hx := hM x
  by_cases he : x = 0
  · subst x
    simp only [h0, false_iff]
    omega
  · omega

private theorem steps_length (n x : ℕ) (l : List ℕ) :
    (steps n x l).length = l.length := by
  induction l generalizing x with
  | nil => rfl
  | cons y ys ih => simp only [steps,List.length_cons,ih]

private theorem steps_adjacent (n x : ℕ) (l : List ℕ) (i : ℕ) (hi : i < l.length) :
    (steps n x l)[i]'(by simpa only [steps_length] using hi) =
      circularLength n ((x::l)[i]'(by simp only [List.length_cons]; omega))
        ((x::l)[i+1]'(by simpa only [List.length_cons] using Nat.succ_lt_succ hi)) := by
  induction l generalizing x i with
  | nil => simp at hi
  | cons y ys ih =>
    cases i with
    | zero => rfl
    | succ i => simpa only [steps,List.getElem_cons_succ] using ih y i (by simpa using hi)

private theorem two_occurrences (l : List ℕ) (d : ℕ) (hc : l.count d = 2) :
    ∃ i j : Fin l.length, i ≠ j ∧ l[i] = d ∧ l[j] = d := by
  induction l with
  | nil => simp at hc
  | cons x xs ih =>
    by_cases he : x = d
    · subst x
      have hpos : 0 < xs.count d := by
        have ht : xs.count d + 1 = 2 := by simpa using hc
        omega
      have hm : d ∈ xs := List.count_pos_iff.mp hpos
      obtain ⟨j,hj,hjv⟩ := List.getElem_of_mem hm
      refine ⟨0, ⟨j+1, by simpa using Nat.succ_lt_succ hj⟩, ?_, rfl, ?_⟩
      · intro h
        have := congrArg Fin.val h
        simp only [Fin.val_zero,Fin.val_mk] at this
        omega
      · simpa only [List.getElem_cons_succ] using hjv
    · have hct : xs.count d = 2 := by simpa [he] using hc
      obtain ⟨i,j,hij,hi,hj⟩ := ih hct
      refine ⟨i.succ,j.succ,?_,?_,?_⟩
      · exact fun h => hij (Fin.succ_injective _ h)
      · simpa only [Fin.val_succ,List.getElem_cons_succ] using hi
      · simpa only [Fin.val_succ,List.getElem_cons_succ] using hj

/-- Preserve rows on the first occurrence, and swap rows on the other one. -/
private def mark (l : List ℕ) (i : Fin l.length) : ZMod 2 :=
  if i.val = l.idxOf l[i] then 0 else 1

private theorem marked_occurrences (l : List ℕ) (d : ℕ) (hc : l.count d = 2) :
    ∃ i j : Fin l.length, l[i] = d ∧ mark l i = 0 ∧ l[j] = d ∧ mark l j = 1 := by
  obtain ⟨u,v,huv,hu,hv⟩ := two_occurrences l d hc
  have hm : d ∈ l := by rw [← hu]; exact List.getElem_mem _
  let k : Fin l.length := ⟨l.idxOf d, List.idxOf_lt_length_of_mem hm⟩
  have hk : l[k] = d := List.getElem_idxOf k.isLt
  have hk0 : mark l k = 0 := by simp [mark,hk,k]
  by_cases hku : u = k
  · refine ⟨k,v,hk,hk0,hv,?_⟩
    have hne : v.val ≠ l.idxOf d := by
      intro h
      apply huv
      rw [hku]
      exact (Fin.ext h).symm
    simp [mark,hv,hne]
  · refine ⟨k,u,hk,hk0,hu,?_⟩
    have hne : u.val ≠ l.idxOf d := fun h => hku (Fin.ext h)
    simp [mark,hu,hne]

private def rowPotential (l : List ℕ) (i : ℕ) : ZMod 2 :=
  ((List.range i).map fun k => if hk : k < l.length then mark l ⟨k,hk⟩ else 0).sum

private theorem rowPotential_zero (l : List ℕ) : rowPotential l 0 = 0 := by
  simp [rowPotential]

private theorem rowPotential_step (l : List ℕ) (i : Fin l.length) :
    rowPotential l (i.val+1) = rowPotential l i.val + mark l i := by
  simp [rowPotential,List.range_succ,i.isLt]

private theorem rowPotential_difference (l : List ℕ) (i : Fin l.length) :
    rowPotential l (i.val+1) - rowPotential l i.val = mark l i := by
  rw [rowPotential_step]
  abel


/-- Phase zero is the connector (1,0); ascending phases traverse the row-one
track, and the remaining phases traverse the other track in reverse. -/
private def chart (n N : ℕ) (v : Fin (N+1) → ZMod n) (l : List ℕ)
    (i : Fin (2*N+3)) : ZMod 2 × ZMod n :=
  if h0 : i.val = 0 then (1,0)
  else if h1 : i.val ≤ N+1 then
    (1 + rowPotential l (i.val-1), v ⟨i.val-1,by omega⟩)
  else (rowPotential l (2*N+2-i.val),v ⟨2*N+2-i.val,by omega⟩)

private theorem chart_ne_zero (n N : ℕ) (v : Fin (N+1) → ZMod n)
    (hz : ∀ i, v i ≠ 0) (l : List ℕ) (i : Fin (2*N+3)) :
    chart n N v l i ≠ 0 := by
  intro he
  unfold chart at he
  split_ifs at he with h0 h1
  · have h := congrArg Prod.fst he
    norm_num at h
  · exact hz _ (congrArg Prod.snd he)
  · exact hz _ (congrArg Prod.snd he)

private theorem chart_injective (n N : ℕ) (v : Fin (N+1) → ZMod n)
    (hz : ∀ i, v i ≠ 0) (hv : Function.Injective v) (l : List ℕ) :
    Function.Injective (chart n N v l) := by
  intro i j he
  unfold chart at he
  split_ifs at he with hi0 hiA hj0 hjA hj0 hjA hj0 hjA
  all_goals simp only [Prod.mk.injEq] at he
  · exact Fin.ext (by omega)
  · exact False.elim (hz _ he.2.symm)
  · exact False.elim (hz _ he.2.symm)
  · exact False.elim (hz _ he.2)
  · have hi := congrArg Fin.val (hv he.2)
    exact Fin.ext (by simp only [Fin.val_mk] at hi; omega)
  · have hi := congrArg Fin.val (hv he.2)
    simp only [Fin.val_mk] at hi
    have hr := he.1
    rw [← hi] at hr
    have h10 : (1 : ZMod 2) = 0 :=
      add_right_cancel (show 1 + rowPotential l (i.val-1) =
        0 + rowPotential l (i.val-1) by simpa using hr)
    exact False.elim (one_ne_zero h10)
  · exact False.elim (hz _ he.2)
  · have hi := congrArg Fin.val (hv he.2)
    simp only [Fin.val_mk] at hi
    have hr := he.1
    rw [← hi] at hr
    have h10 : (1 : ZMod 2) = 0 :=
      add_right_cancel (show 1 + rowPotential l (2*N+2-i.val) =
        0 + rowPotential l (2*N+2-i.val) by simpa using hr.symm)
    exact False.elim (one_ne_zero h10)
  · have hi := congrArg Fin.val (hv he.2)
    exact Fin.ext (by simp only [Fin.val_mk] at hi; omega)

private theorem chart_zero (n N : ℕ) (v : Fin (N+1) → ZMod n) (l : List ℕ) :
    chart n N v l 0 = (1,0) := by simp [chart]

private theorem chart_ascending (n N : ℕ) (v : Fin (N+1) → ZMod n)
    (l : List ℕ) (i : Fin (N+1)) :
    chart n N v l ⟨i.val+1,by omega⟩ = (1+rowPotential l i.val,v i) := by
  simp only [chart, show ¬ i.val+1=0 by omega,
    show i.val+1 ≤ N+1 by omega, ↓reduceDIte, Nat.add_sub_cancel]

private theorem chart_descending (n N : ℕ) (v : Fin (N+1) → ZMod n)
    (l : List ℕ) (i : Fin (N+1)) :
    chart n N v l ⟨2*N+2-i.val,by omega⟩ = (rowPotential l i.val,v i) := by
  have h0 : 2*N+2-i.val ≠ 0 := by omega
  have hA : ¬ 2*N+2-i.val ≤ N+1 := by omega
  have he : 2*N+2-(2*N+2-i.val) = i.val := by omega
  simp only [chart,h0,hA,↓reduceDIte,he]

private theorem chart_triple (n N : ℕ) (v : Fin (N+1) → ZMod n) (l : List ℕ) :
    chart n N v l (Fin.last (2*N+2)) = (0,v 0) ∧
      chart n N v l 0 = (1,0) ∧ chart n N v l 1 = (1,v 0) := by
  have hlast := chart_descending n N v l (0 : Fin (N+1))
  have hfirst := chart_ascending n N v l (0 : Fin (N+1))
  simpa [rowPotential_zero] using And.intro hlast (And.intro (chart_zero n N v l) hfirst)


private theorem chart_up_difference (n N : ℕ) (v : Fin (N+1) → ZMod n)
    (l : List ℕ) (hL : l.length = N) (i : Fin N) :
    chart n N v l ⟨i.val+2,by omega⟩ - chart n N v l ⟨i.val+1,by omega⟩ =
      (mark l ⟨i.val,by omega⟩,v i.succ-v i.castSucc) := by
  have h0 := chart_ascending n N v l i.castSucc
  have h1 := chart_ascending n N v l i.succ
  simp only [Fin.val_castSucc,Fin.val_succ] at h0 h1
  rw [show i.val+2 = (i.val+1)+1 by omega,h1,h0]
  apply Prod.ext
  · simp only [Prod.sub_fst,Prod.fst]
    have he := rowPotential_difference l ⟨i.val,by omega⟩
    simpa only [add_sub_add_left_eq_sub] using he
  · rfl

private theorem chart_down_difference (n N : ℕ) (v : Fin (N+1) → ZMod n)
    (l : List ℕ) (hL : l.length = N) (i : Fin N) :
    chart n N v l ⟨2*N+2-i.val,by omega⟩ - chart n N v l ⟨2*N+1-i.val,by omega⟩ =
      (mark l ⟨i.val,by omega⟩,-(v i.succ-v i.castSucc)) := by
  have h0 := chart_descending n N v l i.castSucc
  have h1 := chart_descending n N v l i.succ
  simp only [Fin.val_castSucc,Fin.val_succ] at h0 h1
  have he : 2*N+2-(i.val+1) = 2*N+1-i.val := by omega
  rw [he] at h1
  rw [h0,h1]
  apply Prod.ext
  · simp only [Prod.sub_fst,Prod.fst]
    rw [← ZMod.neg_eq_self_mod_two (mark l ⟨i.val,by omega⟩),
      ← rowPotential_difference l ⟨i.val,by omega⟩]
    abel
  · simp only [Prod.sub_snd,Prod.snd]
    abel

private theorem circular_sign (n x y d : ℕ) (hx : x < n) (hy : y < n)
    (hd : 0 < d) (h2 : 2*d < n) (he : circularLength n x y = d) :
    (y : ZMod n)-(x : ZMod n) = (d : ZMod n) ∨
      (y : ZMod n)-(x : ZMod n) = -(d : ZMod n) := by
  have hdist : Nat.dist x y = d ∨ Nat.dist x y = n-d := by
    dsimp [circularLength] at he
    omega
  have hc : y=x+d ∨ x=y+d ∨ y+n=x+d ∨ x+n=y+d := by
    simp only [Nat.dist] at hdist
    omega
  rcases hc with hc | hc | hc | hc
  · left
    rw [hc,Nat.cast_add]
    abel
  · right
    rw [hc,Nat.cast_add]
    abel
  · left
    have h := congrArg (fun k : ℕ => (k : ZMod n)) hc
    simp only [Nat.cast_add,ZMod.natCast_self,add_zero] at h
    linear_combination h
  · right
    have h := congrArg (fun k : ℕ => (k : ZMod n)) hc
    simp only [Nat.cast_add,ZMod.natCast_self,add_zero] at h
    linear_combination -h

private theorem signed_representative (m : ℕ) (hm : 0 < m)
    (u : ZMod (2*m)) (hu : u ≠ 0) (hum : u ≠ (m : ZMod (2*m))) :
    ∃ d : ℕ, 1 ≤ d ∧ d < m ∧
      (u = (d : ZMod (2*m)) ∨ u = -(d : ZMod (2*m))) := by
  letI : NeZero (2*m) := ⟨by omega⟩
  have hb := u.val_lt
  have h0 : u.val ≠ 0 := (ZMod.val_eq_zero u).not.mpr hu
  have hmid : u.val ≠ m := by
    intro he
    apply hum
    rw [← ZMod.natCast_zmod_val u,he]
  by_cases h : u.val < m
  · exact ⟨u.val,by omega,h,Or.inl (ZMod.natCast_zmod_val u).symm⟩
  · refine ⟨2*m-u.val,by omega,by omega,Or.inr ?_⟩
    have he : (2*m-u.val)+u.val=2*m := by omega
    have hc := congrArg (fun k : ℕ => (k : ZMod (2*m))) he
    simp only [Nat.cast_add,ZMod.natCast_zmod_val,ZMod.natCast_self] at hc
    exact (eq_neg_iff_add_eq_zero).mpr (by simpa [add_comm] using hc)

end D5.S3.FiniteGroups.HeadleyRankTwoLift
