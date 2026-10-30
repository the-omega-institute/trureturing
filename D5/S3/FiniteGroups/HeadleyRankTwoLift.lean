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
import Mathlib.GroupTheory.Perm.Fin

/-! The two directed row tracks construct the actual full nonzero cycle and
its difference permutation, including the connector and the terminal cap. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.FiniteGroups.HeadleyRankTwoLift
open HeadleyRankTwoPath

private theorem path_vertices (m : ℕ) (p : LengthPath m) :
    p.tail.Nodup ∧ (∀ x, x ∈ p.tail ↔ 1 ≤ x ∧ x < 2 * m) ∧
      p.tail.length + 1 = 2 * m := by
  have hN : (0 :: p.tail).Nodup := p.vertex_inventory.nodup_iff.mpr List.nodup_range
  have hM (x : ℕ) : x = 0 ∨ x ∈ p.tail ↔ x < 2 * m := by
    simpa only [List.mem_cons, List.mem_range] using p.vertex_inventory.mem_iff (a := x)
  have hC := p.vertex_inventory.length_eq
  simp only [List.length_cons,List.length_range] at hC
  refine ⟨hN.of_cons, ?_, hC⟩
  intro x
  have h0 : 0 ∉ p.tail := (List.nodup_cons.mp hN).1
  have hx := hM x
  by_cases he : x = 0
  · subst x
    simp only [h0, false_iff]
    omega
  · simp only [he, false_or] at hx
    exact ⟨fun h => ⟨by omega, hx.mp h⟩, fun h => hx.mpr h.2⟩

private theorem steps_length (n x : ℕ) (l : List ℕ) :
    (steps n x l).length = l.length := by
  induction l generalizing x with
  | nil => rfl
  | cons y ys ih => simp only [steps,List.length_cons,ih]

private theorem steps_adjacent (n x : ℕ) (l : List ℕ) (i : ℕ) (hi : i < l.length) :
    (steps n x l)[i]'(by simpa only [steps_length] using hi) =
      circularLength n ((x::l)[i]'(by simp only [List.length_cons]; omega))
        ((x::l)[i + 1]'(by simpa only [List.length_cons] using Nat.succ_lt_succ hi)) := by
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
      refine ⟨0, ⟨j + 1, by simpa using Nat.succ_lt_succ hj⟩, ?_, rfl, ?_⟩
      · intro h
        have := congrArg Fin.val h
        simp only [Fin.val_zero] at this
        omega
      · simpa only [Fin.getElem_fin, List.getElem_cons_succ] using hjv
    · have hct : xs.count d = 2 := by simpa [he] using hc
      obtain ⟨i,j,hij,hi,hj⟩ := ih hct
      refine ⟨i.succ,j.succ,?_,?_,?_⟩
      · exact fun h => hij (Fin.succ_injective _ h)
      · simpa only [Fin.getElem_fin, Fin.val_succ,List.getElem_cons_succ] using hi
      · simpa only [Fin.getElem_fin, Fin.val_succ,List.getElem_cons_succ] using hj

private theorem row_cases (e : ZMod 2) : e = 0 ∨ e = 1 := by
  have hb := e.val_lt
  have h : e.val = 0 ∨ e.val = 1 := by omega
  rcases h with h | h
  · exact Or.inl ((ZMod.val_eq_zero e).mp h)
  · right
    calc
      e = ((e.val : ℕ) : ZMod 2) := (ZMod.natCast_zmod_val e).symm
      _ = 1 := by rw [h]; rfl

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
    rowPotential l (i.val + 1) = rowPotential l i.val + mark l i := by
  simp [rowPotential,List.range_succ,i.isLt]

private theorem rowPotential_difference (l : List ℕ) (i : Fin l.length) :
    rowPotential l (i.val + 1) - rowPotential l i.val = mark l i := by
  rw [rowPotential_step]
  abel


/-- Phase zero is the connector (1,0); ascending phases traverse the row-one
track, and the remaining phases traverse the other track in reverse. -/
private def chart (n N : ℕ) (v : Fin (N + 1) → ZMod n) (l : List ℕ)
    (i : Fin (2 * N + 3)) : ZMod 2 × ZMod n :=
  if h0 : i.val = 0 then (1,0)
  else if h1 : i.val ≤ N + 1 then
    (1 + rowPotential l (i.val - 1), v ⟨i.val - 1,by omega⟩)
  else (rowPotential l (2 * N + 2 - i.val),v ⟨2 * N + 2 - i.val,by omega⟩)

private theorem chart_ne_zero (n N : ℕ) (v : Fin (N + 1) → ZMod n)
    (hz : ∀ i, v i ≠ 0) (l : List ℕ) (i : Fin (2 * N + 3)) :
    chart n N v l i ≠ 0 := by
  intro he
  unfold chart at he
  split_ifs at he with h0 h1
  · have h := congrArg Prod.fst he
    norm_num at h
  · exact hz _ (congrArg Prod.snd he)
  · exact hz _ (congrArg Prod.snd he)

private theorem chart_injective (n N : ℕ) (v : Fin (N + 1) → ZMod n)
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
    dsimp only at hi
    exact Fin.ext (by omega)
  · have hi := congrArg Fin.val (hv he.2)
    dsimp only at hi
    have hr := he.1
    rw [← hi] at hr
    have h10 : (1 : ZMod 2) = 0 :=
      add_right_cancel (show 1 + rowPotential l (i.val - 1) =
        0 + rowPotential l (i.val - 1) by simpa using hr)
    exact False.elim (one_ne_zero h10)
  · exact False.elim (hz _ he.2)
  · have hi := congrArg Fin.val (hv he.2)
    dsimp only at hi
    have hr := he.1
    rw [← hi] at hr
    have h10 : (1 : ZMod 2) = 0 :=
      add_right_cancel (show 1 + rowPotential l (2 * N + 2 - i.val) =
        0 + rowPotential l (2 * N + 2 - i.val) by simpa using hr.symm)
    exact False.elim (one_ne_zero h10)
  · have hi := congrArg Fin.val (hv he.2)
    dsimp only at hi
    exact Fin.ext (by omega)

private theorem chart_zero (n N : ℕ) (v : Fin (N + 1) → ZMod n) (l : List ℕ) :
    chart n N v l 0 = (1,0) := by simp [chart]

private theorem chart_ascending (n N : ℕ) (v : Fin (N + 1) → ZMod n)
    (l : List ℕ) (i : Fin (N + 1)) :
    chart n N v l ⟨i.val + 1,by omega⟩ = (1 + rowPotential l i.val,v i) := by
  simp only [chart, show ¬ i.val + 1=0 by omega,
    show i.val + 1 ≤ N + 1 by omega, ↓reduceDIte, Nat.add_sub_cancel]

private theorem chart_descending (n N : ℕ) (v : Fin (N + 1) → ZMod n)
    (l : List ℕ) (i : Fin (N + 1)) :
    chart n N v l ⟨2 * N + 2 - i.val,by omega⟩ = (rowPotential l i.val,v i) := by
  have h0 : 2 * N + 2 - i.val ≠ 0 := by omega
  have hA : ¬ 2 * N + 2 - i.val ≤ N + 1 := by omega
  have he : 2 * N + 2 - (2 * N + 2 - i.val) = i.val := by omega
  simp only [chart,h0,hA,↓reduceDIte,he]

private theorem chart_triple (n N : ℕ) (v : Fin (N + 1) → ZMod n) (l : List ℕ) :
    chart n N v l (Fin.last (2 * N + 2)) = (0,v 0) ∧
      chart n N v l 0 = (1,0) ∧ chart n N v l 1 = (1,v 0) := by
  have hlast := chart_descending n N v l (0 : Fin (N + 1))
  have hfirst := chart_ascending n N v l (0 : Fin (N + 1))
  simpa [rowPotential_zero, Fin.last] using And.intro hlast (And.intro (chart_zero n N v l) hfirst)


private theorem chart_up_difference (n N : ℕ) (v : Fin (N + 1) → ZMod n)
    (l : List ℕ) (hL : l.length = N) (i : Fin N) :
    chart n N v l ⟨i.val + 2,by omega⟩ - chart n N v l ⟨i.val + 1,by omega⟩ =
      (mark l ⟨i.val,by omega⟩,v i.succ-v i.castSucc) := by
  have h0 := chart_ascending n N v l i.castSucc
  have h1 := chart_ascending n N v l i.succ
  simp only [Fin.val_castSucc,Fin.val_succ] at h0 h1
  simp only [Nat.add_assoc, Nat.reduceAdd] at h1
  rw [h1,h0]
  apply Prod.ext
  · change (1 + rowPotential l (i.val + 1)) - (1 + rowPotential l i.val) = _
    have he := rowPotential_difference l ⟨i.val,by omega⟩
    simpa only [add_sub_add_left_eq_sub] using he
  · rfl

private theorem chart_down_difference (n N : ℕ) (v : Fin (N + 1) → ZMod n)
    (l : List ℕ) (hL : l.length = N) (i : Fin N) :
    chart n N v l ⟨2 * N + 2 - i.val,by omega⟩ - chart n N v l ⟨2 * N + 1 - i.val,by omega⟩ =
      (mark l ⟨i.val,by omega⟩,-(v i.succ-v i.castSucc)) := by
  have h0 := chart_descending n N v l i.castSucc
  have h1 := chart_descending n N v l i.succ
  simp only [Fin.val_castSucc,Fin.val_succ] at h0 h1
  have he : 2 * N + 2 - (i.val + 1) = 2 * N + 1 - i.val := by omega
  simp only [he] at h1
  rw [h0,h1]
  apply Prod.ext
  · change rowPotential l i.val - rowPotential l (i.val + 1) = _
    rw [← ZMod.neg_eq_self_mod_two (mark l ⟨i.val,by omega⟩),
      ← rowPotential_difference l ⟨i.val,by omega⟩]
    abel
  · change v i.castSucc - v i.succ = -(v i.succ - v i.castSucc)
    abel

private theorem circular_sign (n x y d : ℕ) (hx : x < n) (hy : y < n)
    (hd : 0 < d) (h2 : 2 * d < n) (he : circularLength n x y = d) :
    (y : ZMod n) - (x : ZMod n) = (d : ZMod n) ∨
      (y : ZMod n) - (x : ZMod n) = -(d : ZMod n) := by
  have hdist : Nat.dist x y = d ∨ Nat.dist x y = n - d := by
    dsimp [circularLength] at he
    omega
  have hc : y=x + d ∨ x=y + d ∨ y + n=x + d ∨ x + n=y + d := by
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
    (u : ZMod (2 * m)) (hu : u ≠ 0) (hum : u ≠ (m : ZMod (2 * m))) :
    ∃ d : ℕ, 1 ≤ d ∧ d < m ∧
      (u = (d : ZMod (2 * m)) ∨ u = -(d : ZMod (2 * m))) := by
  let : NeZero (2 * m) := ⟨by omega⟩
  have hb := u.val_lt
  have h0 : u.val ≠ 0 := (ZMod.val_eq_zero u).not.mpr hu
  have hmid : u.val ≠ m := by
    intro he
    apply hum
    rw [← ZMod.natCast_zmod_val u,he]
  by_cases h : u.val < m
  · exact ⟨u.val,by omega,h,Or.inl (ZMod.natCast_zmod_val u).symm⟩
  · refine ⟨2 * m - u.val,by omega,by omega,Or.inr ?_⟩
    have he : (2 * m - u.val) + u.val=2 * m := by omega
    have hc := congrArg (fun k : ℕ => (k : ZMod (2 * m))) he
    simp only [Nat.cast_add,ZMod.natCast_zmod_val,ZMod.natCast_self] at hc
    exact (eq_neg_iff_add_eq_zero).mpr (by simpa [add_comm] using hc)


private noncomputable def chartEquiv (n N : ℕ) [NeZero n] (hn : n = N + 2)
    (v : Fin (N + 1) → ZMod n) (hz : ∀ i, v i ≠ 0)
    (hv : Function.Injective v) (l : List ℕ) :
    Fin (2 * N + 3) ≃ {x : ZMod 2 × ZMod n // x ≠ 0} := by
  let f : Fin (2 * N + 3) → {x : ZMod 2 × ZMod n // x ≠ 0} :=
    fun i => ⟨chart n N v l i,chart_ne_zero n N v hz l i⟩
  have hi : Function.Injective f := by
    intro i j he
    exact chart_injective n N v hz hv l (congrArg Subtype.val he)
  have hc : Fintype.card (Fin (2 * N + 3)) =
      Fintype.card {x : ZMod 2 × ZMod n // x ≠ 0} := by
    simp only [Fintype.card_fin,Fintype.card_subtype_compl,Fintype.card_prod,
      ZMod.card,Fintype.card_unique]
    omega
  exact Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hi,hc⟩)

private noncomputable def cycleSuccessor (n N : ℕ) [NeZero n] (hn : n = N + 2)
    (v : Fin (N + 1) → ZMod n) (hz : ∀ i, v i ≠ 0)
    (hv : Function.Injective v) (l : List ℕ) : Equiv.Perm (ZMod 2 × ZMod n) :=
  (finRotate (2 * N + 3)).extendDomain (chartEquiv n N hn v hz hv l)

private theorem cycle_zero (n N : ℕ) [NeZero n] (hn : n = N + 2)
    (v : Fin (N + 1) → ZMod n) (hz : ∀ i, v i ≠ 0)
    (hv : Function.Injective v) (l : List ℕ) :
    cycleSuccessor n N hn v hz hv l 0 = 0 := by
  exact Equiv.Perm.extendDomain_apply_not_subtype _ _ (by simp)

private theorem cycle_chart (n N : ℕ) [NeZero n] (hn : n = N + 2)
    (v : Fin (N + 1) → ZMod n) (hz : ∀ i, v i ≠ 0)
    (hv : Function.Injective v) (l : List ℕ) (i : Fin (2 * N + 3)) :
    cycleSuccessor n N hn v hz hv l (chart n N v l i) =
      chart n N v l (finRotate (2 * N + 3) i) := by
  exact Equiv.Perm.extendDomain_apply_image _ _ i

private theorem cycle_one_orbit (n N : ℕ) [NeZero n] (hn : n = N + 2)
    (v : Fin (N + 1) → ZMod n) (hz : ∀ i, v i ≠ 0)
    (hv : Function.Injective v) (l : List ℕ) :
    (cycleSuccessor n N hn v hz hv l).IsCycleOn {x | x ≠ 0} := by
  have hf := (isCycle_finRotate_of_le (by omega : 2 ≤ 2 * N + 3)).isCycleOn
  have hset : {i : Fin (2 * N + 3) | finRotate (2 * N + 3) i ≠ i} = Set.univ := by
    ext i
    have hi : i ∈ (finRotate (2 * N + 3)).support := by
      rw [support_finRotate_of_le (by omega)]
      exact Finset.mem_univ i
    exact iff_true_intro (Equiv.Perm.mem_support.mp hi)
  rw [hset] at hf
  let e := chartEquiv n N hn v hz hv l
  have himage : ((↑) ∘ e '' Set.univ) = {x : ZMod 2 × ZMod n | x ≠ 0} := by
    ext x
    constructor
    · rintro ⟨i,_,rfl⟩
      exact (e i).property
    · intro hx
      obtain ⟨i,hi⟩ := e.surjective ⟨x,hx⟩
      exact ⟨i,Set.mem_univ i,congrArg Subtype.val hi⟩
  change ((finRotate (2 * N + 3)).extendDomain e).IsCycleOn {x | x ≠ 0}
  rw [← himage]
  exact hf.extendDomain e

private theorem cycle_up (n N : ℕ) [NeZero n] (hn : n = N + 2)
    (v : Fin (N + 1) → ZMod n) (hz : ∀ i, v i ≠ 0)
    (hv : Function.Injective v) (l : List ℕ) (hL : l.length = N) (i : Fin N) :
    cycleSuccessor n N hn v hz hv l (chart n N v l ⟨i.val + 1,by omega⟩) -
      chart n N v l ⟨i.val + 1,by omega⟩ =
        (mark l ⟨i.val,by omega⟩,v i.succ-v i.castSucc) := by
  rw [cycle_chart]
  have hr : finRotate (2 * N + 3) (⟨i.val + 1,by omega⟩ : Fin (2 * N + 3)) =
      ⟨i.val + 2,by omega⟩ := by
    exact finRotate_of_lt (by omega)
  rw [hr]
  exact chart_up_difference n N v l hL i

private theorem cycle_down (n N : ℕ) [NeZero n] (hn : n = N + 2)
    (v : Fin (N + 1) → ZMod n) (hz : ∀ i, v i ≠ 0)
    (hv : Function.Injective v) (l : List ℕ) (hL : l.length = N) (i : Fin N) :
    cycleSuccessor n N hn v hz hv l (chart n N v l ⟨2 * N + 1 - i.val,by omega⟩) -
      chart n N v l ⟨2 * N + 1 - i.val,by omega⟩ =
        (mark l ⟨i.val,by omega⟩,-(v i.succ-v i.castSucc)) := by
  rw [cycle_chart]
  have hr : finRotate (2 * N + 3) (⟨2 * N + 1 - i.val,by omega⟩ : Fin (2 * N + 3)) =
      ⟨2 * N + 2 - i.val,by omega⟩ := by
    apply Fin.ext
    rw [coe_finRotate_of_ne_last (by intro he; have := congrArg Fin.val he; simp at this; omega)]
    dsimp only
    omega
  rw [hr]
  exact chart_down_difference n N v l hL i


private noncomputable def ofLengthPath (n m : ℕ) [NeZero n] (hn : n = 2 * m)
    (hm : 4 ≤ m) (p : LengthPath m) :
    HeadleyExtension.RStar (ZMod 2 × ZMod n) := by
  subst n
  classical
  obtain ⟨hND,hMem,hCard⟩ := path_vertices m p
  let r := p.tail.tail
  have ht : p.tail = m::r := by
    cases he : p.tail with
    | nil => have h := p.start; simp [he] at h
    | cons x xs =>
      have h : x = m := by simpa only [he,List.head?_cons,Option.some.injEq] using p.start
      simp [r,he,h]
  let N := r.length
  have hN : 2 * m = N + 2 := by rw [ht] at hCard; simp only [List.length_cons] at hCard; omega
  have hR : (m::r).Nodup := ht ▸ hND
  have hb (i : Fin (N + 1)) : 1 ≤ (m::r)[i] ∧ (m::r)[i] < 2 * m := by
    apply (hMem _).mp
    rw [ht]
    exact List.getElem_mem _
  let v : Fin (N + 1) → ZMod (2 * m) := fun i => ((m::r)[i] : ZMod (2 * m))
  have hz : ∀ i, v i ≠ 0 := by
    intro i he
    have hv := congrArg ZMod.val he
    simp only [v,ZMod.val_natCast_of_lt (hb i).2,ZMod.val_zero] at hv
    have hbi := hb i
    omega
  have hv : Function.Injective v := by
    intro i j he
    have he' := congrArg ZMod.val he
    simp only [v,ZMod.val_natCast_of_lt (hb i).2,ZMod.val_natCast_of_lt (hb j).2] at he'
    exact Fin.ext (hR.getElem_inj_iff.mp he')
  have hv0 : v 0 = (m : ZMod (2 * m)) := rfl
  let l := steps (2 * m) m r
  have hL : l.length = N := steps_length (2 * m) m r
  have hP : l.Perm (List.range' 1 (m - 1) ++ List.range' 1 (m - 1)) := by
    have he := p.length_inventory
    rw [ht] at he
    have hc : circularLength (2 * m) 0 m = m := by simp only [circularLength,Nat.dist]; omega
    simp only [steps,hc] at he
    exact he.cons_inv
  have hCount (d : ℕ) (hd : 1 ≤ d) (hdm : d < m) : l.count d = 2 := by
    rw [hP.count_eq,List.count_append]
    have hmem : d ∈ List.range' 1 (m - 1) := by simp only [List.mem_range'_1]; omega
    rw [List.count_eq_one_of_mem List.nodup_range' hmem]
  have hMarked (e : ZMod 2) (d : ℕ) (hd : 1 ≤ d) (hdm : d < m) :
      ∃ i : Fin N, mark l ⟨i.val,by omega⟩ = e ∧ l[i.val]'(by omega) = d := by
    obtain ⟨i,j,hi,hiM,hj,hjM⟩ := marked_occurrences l d (hCount d hd hdm)
    rcases row_cases e with he | he
    · subst e
      exact ⟨Fin.cast hL i,by simpa using hiM,by simpa using hi⟩
    · subst e
      exact ⟨Fin.cast hL j,by simpa using hjM,by simpa using hj⟩
  have hSign (i : Fin N) (d : ℕ) (hd : 1 ≤ d) (hdm : d < m)
      (he : l[i.val]'(by omega) = d) :
      v i.succ-v i.castSucc = (d : ZMod (2 * m)) ∨
        v i.succ-v i.castSucc = -(d : ZMod (2 * m)) := by
    apply circular_sign (2 * m) ((m::r)[i.castSucc]) ((m::r)[i.succ]) d
      (hb i.castSucc).2 (hb i.succ).2 (by omega) (by omega)
    have hs := steps_adjacent (2 * m) m r i.val i.isLt
    exact hs.symm.trans he
  let S := cycleSuccessor (2 * m) N hN v hz hv l
  let A : ZMod 2 × ZMod (2 * m) := (0,m)
  let B : ZMod 2 × ZMod (2 * m) := (1,0)
  let C : ZMod 2 × ZMod (2 * m) := (1,m)
  have hS : ∀ i, S (chart (2 * m) N v l i) = chart (2 * m) N v l (finRotate (2 * N + 3) i) :=
    cycle_chart (2 * m) N hN v hz hv l
  have hTriple := chart_triple (2 * m) N v l
  have hA : chart (2 * m) N v l (Fin.last (2 * N + 2)) = A := by simpa [A,hv0] using hTriple.1
  have hB : chart (2 * m) N v l 0 = B := hTriple.2.1
  have hC : chart (2 * m) N v l 1 = C := by simpa [C,hv0] using hTriple.2.2
  have hAB : S A = B := by rw [← hA,hS,finRotate_last,hB]
  have hBC : S B = C := by
    rw [← hB,hS]
    have hr : finRotate (2 * N + 3) (0 : Fin (2 * N + 3)) = 1 := by
      exact finRotate_apply_zero
    rw [hr,hC]
  have hMM : (m : ZMod (2 * m)) + (m : ZMod (2 * m)) = 0 := by
    calc
      (m : ZMod (2 * m)) + m = ((2 * m : ℕ) : ZMod (2 * m)) := by push_cast; ring
      _ = 0 := ZMod.natCast_self _
  have hNegM : -(m : ZMod (2 * m)) = m := (eq_neg_iff_add_eq_zero.mpr hMM).symm
  have hCap : S (chart (2 * m) N v l ⟨N + 1,by omega⟩) -
      chart (2 * m) N v l ⟨N + 1,by omega⟩ = (1,0) := by
    rw [hS]
    have hr : finRotate (2 * N + 3) (⟨N + 1,by omega⟩ : Fin (2 * N + 3)) = ⟨N + 2,by omega⟩ :=
      finRotate_of_lt (by omega)
    rw [hr]
    have hUp := chart_ascending (2 * m) N v l (Fin.last N)
    have hDn := chart_descending (2 * m) N v l (Fin.last N)
    simp only [Fin.val_last] at hUp hDn
    have he : 2 * N + 2 - N=N + 2 := by omega
    simp only [he] at hDn
    rw [hUp,hDn]
    apply Prod.ext
    · change rowPotential l N - (1 + rowPotential l N) = (1 : ZMod 2)
      calc
        rowPotential l N - (1 + rowPotential l N) = -(1 : ZMod 2) := by abel
        _ = 1 := ZMod.neg_eq_self_mod_two 1
    · simp
  have hSurj : Function.Surjective (fun x => S x - x) := by
    rintro ⟨e,u⟩
    by_cases hu : u = 0
    · subst u
      rcases row_cases e with he | he
      · subst e
        refine ⟨0,?_⟩
        change S 0 - 0 = (0,0)
        rw [show S 0 = 0 from cycle_zero (2 * m) N hN v hz hv l]
        exact (sub_self _).trans Prod.zero_eq_mk
      · subst e
        exact ⟨chart (2 * m) N v l ⟨N + 1,by omega⟩,hCap⟩
    by_cases hum : u = (m : ZMod (2 * m))
    · subst u
      rcases row_cases e with he | he
      · subst e
        refine ⟨B,?_⟩
        change S B - B = ((0 : ZMod 2),(m : ZMod (2 * m)))
        rw [hBC]
        simp [B,C]
      · subst e
        refine ⟨A,?_⟩
        change S A - A = ((1 : ZMod 2),(m : ZMod (2 * m)))
        rw [hAB]
        simp [A,B,hNegM]
    · obtain ⟨d,hd,hdm,huD⟩ := signed_representative m (by omega) u hu hum
      obtain ⟨i,hMark,hLen⟩ := hMarked e d hd hdm
      have hSig := hSign i d hd hdm hLen
      have hU : u = v i.succ-v i.castSucc ∨ u = -(v i.succ-v i.castSucc) := by
        rcases huD with huD | huD <;> rcases hSig with hSig | hSig <;>
          simp [huD,hSig]
      rcases hU with hU | hU
      · refine ⟨chart (2 * m) N v l ⟨i.val + 1,by omega⟩,?_⟩
        change cycleSuccessor (2 * m) N hN v hz hv l _ - _ = _
        rw [cycle_up (2 * m) N hN v hz hv l hL i,hMark,← hU]
      · refine ⟨chart (2 * m) N v l ⟨2 * N + 1 - i.val,by omega⟩,?_⟩
        change cycleSuccessor (2 * m) N hN v hz hv l _ - _ = _
        rw [cycle_down (2 * m) N hN v hz hv l hL i,hMark,← hU]
  have hBij : Function.Bijective (fun x => S x - x) :=
    (Finite.surjective_iff_bijective).mp hSurj
  refine {
    successor := S
    successor_zero := cycle_zero (2 * m) N hN v hz hv l
    nonzero_cycle := cycle_one_orbit (2 * m) N hN v hz hv l
    difference := Equiv.ofBijective (fun x => S x - x) hBij
    difference_spec := fun _ => rfl
    even_card := ?_
    a := A
    b := B
    c := C
    a_ne_zero := ?_
    b_ne_zero := ?_
    c_ne_zero := ?_
    pairwise_distinct := ?_
    successor_a := hAB
    successor_b := hBC
    triple_sum := ?_ }
  · simp only [Nat.card_eq_fintype_card,Fintype.card_prod,ZMod.card]
    exact ⟨2 * m,by omega⟩
  · rw [← hA]
    exact chart_ne_zero (2 * m) N v hz l _
  · rw [← hB]
    exact chart_ne_zero (2 * m) N v hz l _
  · rw [← hC]
    exact chart_ne_zero (2 * m) N v hz l _
  · have hi := chart_injective (2 * m) N v hz hv l
    refine ⟨?_,?_,?_⟩
    · intro he
      have h := congrArg Fin.val (hi (hA.trans (he.trans hB.symm)))
      simp only [Fin.val_last,Fin.val_zero] at h
      omega
    · intro he
      have h := congrArg Fin.val (hi (hA.trans (he.trans hC.symm)))
      simp only [Fin.val_last,Fin.val_one] at h
      omega
    · intro he
      have h := congrArg Fin.val (hi (hB.trans (he.trans hC.symm)))
      simp only [Fin.val_zero,Fin.val_one] at h
      omega
  · apply Prod.ext
    · simp [A,B,C]
    · exact hMM

/-- An actual R-star record for the entire rank-two power-of-two family. The
only arguments are the exponent and the bound a >= 3. All path, vertex, directed
label, cycle, seam, parity and additive-triple fields are constructed internally. -/
noncomputable def powerTwoRStar (a : ℕ) (ha : 3 ≤ a) :
    HeadleyExtension.RStar (ZMod 2 × ZMod (2 ^ a)) := by
  have hm : 4 ≤ 2 ^ (a - 1) :=
    Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 2 ≤ a - 1)
  have he : 2 * 2 ^ (a - 1) = 2 ^ a := by
    have ha1 : a = (a - 1) + 1 := by omega
    conv_rhs => rw [ha1,pow_succ]
    omega
  exact ofLengthPath (2 ^ a) (2 ^ (a - 1)) he.symm hm (powerTwoPath a ha)

end D5.S3.FiniteGroups.HeadleyRankTwoLift
