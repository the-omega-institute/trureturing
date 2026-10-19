/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/SecondHeadBound
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/SecondHeadBound
   mirror-E: none(waiver:symbolic-probability-and-counting)
   anchors: []
   utility: none
   digest: A weighted common-table certificate bounds the second-head prefix at every length. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PreselectedResidualBound
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open scoped BigOperators Classical
open MeasureTheory
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledWitnessTables
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PreselectedResidualBound
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
open private firstFalse_chain from D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PreselectedResidualBound
namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.SecondHeadBound

private def sparse (m k : ℕ) : Fin m → Bool := fun i => decide (i.val = k)
private def double (m k : ℕ) : Fin m → Bool := fun i => decide (i.val = 0 ∨ i.val = k)
private def punctured (m t : ℕ) : Fin m → Bool :=
  fun i => decide (i.val < t ∨ (t < i.val ∧ i.val < m-1))
private def lateWeight (m t : ℕ) : ℕ := if t < m-2 then m-3 else m-2

private abbrev Rows (m : ℕ) :=
  ↥(Finset.Icc (1 : ℕ) (m-2)) ⊕ Unit ⊕ ↥(Finset.Icc (2 : ℕ) (m-2)) ⊕
    ↥(Finset.Icc (2 : ℕ) (m-1)) ⊕ ↥(Finset.Icc (2 : ℕ) (m-3)) ⊕ Unit
private def rowWord (m : ℕ) : Rows m → (Fin m → Bool)
  | .inl k => sparse m k.val
  | .inr (.inl _) => sparse m 0
  | .inr (.inr (.inl k)) => double m k.val
  | .inr (.inr (.inr (.inl k))) => chainWord m k.val
  | .inr (.inr (.inr (.inr (.inl k)))) => punctured m k.val
  | .inr (.inr (.inr (.inr (.inr _)))) => chainWord m m
private def rowWeight (m : ℕ) : Rows m → ℕ
  | .inl _ => 1
  | .inr (.inl _) => 1
  | .inr (.inr (.inl _)) => 1
  | .inr (.inr (.inr (.inl k))) => lateWeight m k.val
  | .inr (.inr (.inr (.inr (.inl _)))) => 1
  | .inr (.inr (.inr (.inr (.inr _)))) => m-2
private def rowEvent (m : ℕ) : Rows m → ℕ → Prop
  | .inl _, r => r = 0 ∨ r = 1
  | .inr (.inl _), r => r = 0 ∨ r = 2
  | .inr (.inr (.inl _)), r => r = 2
  | .inr (.inr (.inr (.inl k))), r => r = k.val+1
  | .inr (.inr (.inr (.inr (.inl k)))), r => r = k.val+1
  | .inr (.inr (.inr (.inr (.inr _)))), r => r = 0

private def tableScore (m : ℕ) (f : Catalog false m) : ℕ :=
  ∑ q : Rows m, if rowEvent m q (f.val (rowWord m q)).val then rowWeight m q else 0

private def inCell (m i j : ℕ) (u v : Bool) (b : Fin m → Bool) : Prop :=
  lowReply b i = u ∧ lowReply b j = v
private def cellScore (m i j : ℕ) (u v : Bool) (r : ℕ) : ℕ :=
  ∑ q : Rows m, if inCell m i j u v (rowWord m q) ∧ rowEvent m q r
    then rowWeight m q else 0

private def sparseCount (m lo i j : ℕ) (u v : Bool) : ℕ :=
  ((Finset.Icc lo (m-2)).filter fun k =>
    decide (i = k) = u ∧ decide (j = k) = v).card

private theorem sparse_count (m lo i j : ℕ) (hij : i < j) (u v : Bool) :
    sparseCount m lo i j u v =
      match u,v with
      | false,false => (Finset.Icc lo (m-2)).card -
          (if i ∈ Finset.Icc lo (m-2) then 1 else 0) -
          (if j ∈ Finset.Icc lo (m-2) then 1 else 0)
      | false,true => if j ∈ Finset.Icc lo (m-2) then 1 else 0
      | true,false => if i ∈ Finset.Icc lo (m-2) then 1 else 0
      | true,true => 0 := by
  have ne : i ≠ j := by omega
  cases u <;> cases v
  · have sets : ((Finset.Icc lo (m-2)).filter fun k =>
        decide (i = k) = false ∧ decide (j = k) = false) =
        ((Finset.Icc lo (m-2)).erase i).erase j := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_erase, decide_eq_false_iff_not]
      grind
    rw [sparseCount,sets]
    by_cases hi : i ∈ Finset.Icc lo (m-2) <;>
      by_cases hj : j ∈ Finset.Icc lo (m-2) <;>
      simp [Finset.card_erase_eq_ite,hi,hj,ne,ne.symm] <;> omega
  · have sets : ((Finset.Icc lo (m-2)).filter fun k =>
        decide (i = k) = false ∧ decide (j = k) = true) =
        ((Finset.Icc lo (m-2)).filter (· = j)) := by
      ext k
      simp only [Finset.mem_filter, decide_eq_false_iff_not, decide_eq_true_eq]
      constructor
      · rintro ⟨h,_,rfl⟩; exact ⟨h,rfl⟩
      · rintro ⟨h,rfl⟩; exact ⟨h,ne,rfl⟩
    unfold sparseCount
    rw [sets,Finset.filter_eq']
    split_ifs <;> simp_all
  · have sets : ((Finset.Icc lo (m-2)).filter fun k =>
        decide (i = k) = true ∧ decide (j = k) = false) =
        ((Finset.Icc lo (m-2)).filter (· = i)) := by
      ext k
      simp only [Finset.mem_filter, decide_eq_false_iff_not, decide_eq_true_eq]
      constructor
      · rintro ⟨h,rfl,_⟩; exact ⟨h,rfl⟩
      · rintro ⟨h,rfl⟩; exact ⟨h,rfl,ne.symm⟩
    unfold sparseCount
    rw [sets,Finset.filter_eq']
    split_ifs <;> simp_all
  · apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro k hk
    simp only [Finset.mem_filter, decide_eq_true_eq] at hk
    omega

private theorem unique_sum_bound (s : Finset ℕ) (r C : ℕ) (F : ℕ → ℕ)
    (bound : ∀ k ∈ s, F k ≤ C) :
    (∑ k ∈ s, if r = k+1 then F k else 0) ≤ C := by
  calc
    _ ≤ ∑ k ∈ s, if r = k+1 then C else 0 := by
      apply Finset.sum_le_sum
      intro k hk
      split_ifs
      · exact bound k hk
      · exact le_rfl
    _ = ((s).filter (fun k => r = k+1)).card * C := by
      rw [← Finset.sum_filter]; simp
    _ ≤ C := by
      have hc : ((s).filter (fun k => r = k+1)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro i hi j hj
        have := (Finset.mem_filter.mp hi).2
        have := (Finset.mem_filter.mp hj).2
        omega
      exact (Nat.mul_le_mul_right C hc).trans_eq (Nat.one_mul C)

private def doubleCount (m i j : ℕ) (u v : Bool) : ℕ :=
  ((Finset.Icc 2 (m-2)).filter fun k =>
    decide (i = 0 ∨ i = k) = u ∧ decide (j = 0 ∨ j = k) = v).card

private theorem double_count (m i j : ℕ) (hij : i < j) (u v : Bool) :
    doubleCount m i j u v =
      if i = 0 then (if u = true then sparseCount m 2 i j false v else 0)
      else sparseCount m 2 i j u v := by
  have j0 : j ≠ 0 := by omega
  by_cases i0 : i = 0
  · subst i
    cases u
    · simp [doubleCount]
    · simp only [doubleCount,sparseCount,decide_true,true_or,if_true]
      congr 1
      ext k
      have hk : k ∈ Finset.Icc 2 (m-2) → k ≠ 0 := by intro h; have := (Finset.mem_Icc.mp h).1; omega
      simp [j0]
      intro h _ _
      omega
  · simp only [doubleCount,sparseCount,i0,j0,false_or,if_false]

private def lateCell (m i j : ℕ) (u v : Bool) (t : ℕ) : ℕ :=
  (if inCell m i j u v (chainWord m t) then lateWeight m t else 0) +
    (if t < m-2 ∧ inCell m i j u v (punctured m t) then 1 else 0)

private theorem subtype_sum {α : Type*} [AddCommMonoid α] (s : Finset ℕ)
    [Fintype s] (F : ℕ → α) : (∑ k : s, F k.val) = ∑ k ∈ s, F k :=
  (Finset.sum_subtype s (fun _ => Iff.rfl) F).symm

private theorem cell_score_expansion (m : ℕ) (hm : 4 ≤ m) (i j : ℕ)
    (hi : i < m) (hj : j < m) (u v : Bool) (r : ℕ) :
    cellScore m i j u v r =
      (if r = 0 ∨ r = 1 then sparseCount m 1 i j u v else 0) +
      (if (r = 0 ∨ r = 2) ∧ decide (i = 0) = u ∧ decide (j = 0) = v then 1 else 0) +
      (if r = 2 then doubleCount m i j u v else 0) +
      (∑ t ∈ Finset.Icc 2 (m-1), if r = t+1 then lateCell m i j u v t else 0) +
      (if r = 0 ∧ u = true ∧ v = true then m-2 else 0) := by
  have extend (F : ℕ → ℕ) :
      (∑ t ∈ Finset.Icc 2 (m-3), F t) =
      ∑ t ∈ Finset.Icc 2 (m-1), if t < m-2 then F t else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext t
    simp only [Finset.mem_filter,Finset.mem_Icc]
    omega
  unfold cellScore
  simp only [Fintype.sum_sum_type]
  simp only [rowWord,rowWeight,rowEvent]
  simp only [Fintype.sum_unique,inCell,lowReply,dif_pos hi,dif_pos hj,
    sparse,double,chainWord]
  rw [subtype_sum (Finset.Icc 1 (m-2)) (fun x =>
    if (decide (i=x) = u ∧ decide (j=x) = v) ∧ (r=0 ∨ r=1) then 1 else 0)]
  rw [subtype_sum (Finset.Icc 2 (m-2)) (fun x =>
    if (decide (i=0 ∨ i=x) = u ∧ decide (j=0 ∨ j=x) = v) ∧ r=2 then 1 else 0)]
  rw [subtype_sum (Finset.Icc 2 (m-1)) (fun x =>
    if (decide (i<x) = u ∧ decide (j<x) = v) ∧ r=x+1 then lateWeight m x else 0)]
  rw [subtype_sum (Finset.Icc 2 (m-3)) (fun x =>
    if (punctured m x ⟨i,hi⟩ = u ∧ punctured m x ⟨j,hj⟩ = v) ∧ r=x+1 then 1 else 0)]
  rw [extend]
  have combine :
      (∑ x ∈ Finset.Icc 2 (m-1), if (decide (i < x) = u ∧ decide (j < x) = v) ∧ r = x+1
        then lateWeight m x else 0) +
      (∑ x ∈ Finset.Icc 2 (m-1), if x < m-2 then
        (if (punctured m x ⟨i,hi⟩ = u ∧ punctured m x ⟨j,hj⟩ = v) ∧ r = x+1 then 1 else 0) else 0) =
      ∑ t ∈ Finset.Icc 2 (m-1), if r = t+1 then lateCell m i j u v t else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    unfold lateCell inCell lowReply
    simp only [dif_pos hi,dif_pos hj]
    simp only [chainWord]
    by_cases he : r=t+1 <;>
      by_cases hw : decide (i<t) = u ∧ decide (j<t) = v <;>
      by_cases hp : punctured m t ⟨i,hi⟩ = u ∧ punctured m t ⟨j,hj⟩ = v <;>
      by_cases ht2 : t < m-2 <;> simp only [he,hw,hp,ht2,ite_true,ite_false,and_true,true_and,false_and,and_false,add_zero,zero_add]
  have hcount : (∑ x ∈ Finset.Icc 1 (m-2),
      if (decide (i=x) = u ∧ decide (j=x) = v) ∧ (r=0 ∨ r=1) then 1 else 0) =
      if r=0 ∨ r=1 then sparseCount m 1 i j u v else 0 := by
    by_cases hr : r=0 ∨ r=1 <;> simp [hr,sparseCount,Finset.sum_boole]
  have gcount : (∑ x ∈ Finset.Icc 2 (m-2),
      if (decide (i=0 ∨ i=x) = u ∧ decide (j=0 ∨ j=x) = v) ∧ r=2 then 1 else 0) =
      if r=2 then doubleCount m i j u v else 0 := by
    by_cases hr : r=2 <;> simp [hr,doubleCount,Finset.sum_boole]
  rw [hcount,gcount]
  have gu : (if (decide (i=0)=u ∧ decide (j=0)=v) ∧ (r=0 ∨ r=2) then 1 else 0) =
      (if (r=0 ∨ r=2) ∧ decide (i=0)=u ∧ decide (j=0)=v then 1 else 0) := by
    congr 1
    apply propext
    tauto
  have en : (if (decide (i < m)=u ∧ decide (j < m)=v) ∧ r=0 then m-2 else 0) =
      (if r=0 ∧ u=true ∧ v=true then m-2 else 0) := by
    congr 1
    apply propext
    simp [hi,hj,eq_comm,and_comm,and_left_comm]
  rw [gu,en]
  omega

private def cellBound (m j : ℕ) (u v : Bool) : ℕ :=
  if j = m-1 then (if v = true then (if u = true then m-2 else 0) else m-2)
  else if u = true then m-2 else if v = true then 1 else m-3

private theorem late_cell_bound (m : ℕ) (hm : 4 ≤ m) (i j : ℕ)
    (hij : i < j) (hj : j < m) (u v : Bool) (t : ℕ)
    (ht : t ∈ Finset.Icc 2 (m-1)) :
    lateCell m i j u v t ≤ cellBound m j u v := by
  have hi : i < m := by omega
  obtain ⟨tlo,thi⟩ := Finset.mem_Icc.mp ht
  cases u <;> cases v <;>
    simp only [lateCell,inCell,lowReply,dif_pos hi,dif_pos hj,chainWord,punctured,
      decide_eq_false_iff_not,decide_eq_true_eq,lateWeight,cellBound,
      Bool.false_eq_true,Bool.true_eq_false,ite_false,ite_true] <;>
    split_ifs <;> omega

private theorem cell_score_bound (m : ℕ) (hm : 4 ≤ m) (i j : ℕ)
    (hij : i < j) (hj : j < m) (u v : Bool) (r : ℕ) :
    cellScore m i j u v r ≤ cellBound m j u v := by
  have hi : i < m := by omega
  rw [cell_score_expansion m hm i j hi hj]
  by_cases small : r ≤ 2
  · have late : (∑ t ∈ Finset.Icc 2 (m-1), if r = t+1 then lateCell m i j u v t else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      have := (Finset.mem_Icc.mp ht).1
      rw [if_neg (by omega)]
    rw [late,add_zero,double_count m i j hij]
    simp only [sparse_count m 1 i j hij,sparse_count m 2 i j hij,
      Nat.card_Icc,Finset.mem_Icc,cellBound]
    have j0 : j ≠ 0 := by omega
    interval_cases r <;> cases u <;> cases v <;>
      (try simp_all) <;> split_ifs <;> (try simp_all) <;> omega
  · have r0 : r ≠ 0 := by omega
    have r1 : r ≠ 1 := by omega
    have r2 : r ≠ 2 := by omega
    simp only [r0,r1,r2,false_or,false_and,ite_false,zero_add,add_zero]
    exact unique_sum_bound _ r _ _ (late_cell_bound m hm i j hij hj u v)

private theorem table_score_bound (m : ℕ) (hm : 4 ≤ m) (f : Catalog false m) :
    tableScore m f ≤ 3*(m-2) := by
  obtain ⟨xs,hlen,hlow,_,hfactor⟩ := f.property
  have sub : xs.toFinset ⊆ Finset.range m := by
    intro i hi
    exact Finset.mem_range.mpr (hlow i (List.mem_toFinset.mp hi))
  obtain ⟨Q,hxQ,hQm,hQc⟩ := Finset.exists_subsuperset_card_eq sub
    ((List.toFinset_card_le xs).trans hlen) (by simpa using (show 2 ≤ m by omega))
  let e := Q.orderEmbOfFin hQc
  let i := e 0
  let j := e 1
  have hij : i < j := e.strictMono (by decide)
  have hj : j < m := Finset.mem_range.mp (hQm (Q.orderEmbOfFin_mem hQc 1))
  have hi : i < m := by omega
  have members (k : ℕ) (hk : k ∈ xs) : k = i ∨ k = j := by
    have hkQ := hxQ (List.mem_toFinset.mpr hk)
    have hr : k ∈ Set.range e := by
      rw [Q.range_orderEmbOfFin hQc]
      exact hkQ
    obtain ⟨a,ha⟩ := hr
    fin_cases a <;> simp_all [i,j]
  let out : Bool → Bool → Fin (m+1) := fun u v =>
    f.val (fun k => if k.val = i then u else if k.val = j then v else false)
  have hout (b : Fin m → Bool) : f.val b = out (lowReply b i) (lowReply b j) := by
    apply hfactor
    apply view_congr
    intro k hk
    rcases members k hk with rfl | rfl
    · simp [lowReply,hi,show i ≠ j by omega]
    · simp [lowReply,hj,show j ≠ i by omega]
  have partition : tableScore m f = ∑ u : Bool, ∑ v : Bool,
      cellScore m i j u v (out u v).val := by
    unfold tableScore cellScore
    calc
      _ = ∑ q : Rows m, ∑ u : Bool, ∑ v : Bool,
          if inCell m i j u v (rowWord m q) ∧ rowEvent m q (out u v).val
          then rowWeight m q else 0 := by
        apply Finset.sum_congr rfl
        intro q _
        rw [hout]
        cases hu : lowReply (rowWord m q) i <;>
          cases hv : lowReply (rowWord m q) j <;> simp [inCell,hu,hv]
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro u _
        exact Finset.sum_comm
  rw [partition]
  calc
    _ ≤ ∑ u : Bool, ∑ v : Bool, cellBound m j u v := by
      apply Finset.sum_le_sum
      intro u _
      exact Finset.sum_le_sum (fun v _ => cell_score_bound m hm i j hij hj u v _)
    _ = 3*(m-2) := by
      simp [cellBound]
      split_ifs <;> omega

private def rowTarget (m : ℕ) (a : ℕ → ℝ) : Rows m → ℝ
  | .inl _ => 1
  | .inr (.inl _) => 1
  | .inr (.inr (.inl _)) => a 1
  | .inr (.inr (.inr (.inl k))) => a k.val
  | .inr (.inr (.inr (.inr (.inl k)))) => a k.val
  | .inr (.inr (.inr (.inr (.inr _)))) => 1

private theorem first_false_eq {m : ℕ} (b : Fin m → Bool) (t : ℕ)
    (hz : lowReply b t = false) (hp : ∀ i < t, lowReply b i = true) :
    firstFalse b = t := by
  apply (Nat.find_eq_iff _).mpr
  exact ⟨hz,fun i hi => by rw [hp i hi]; decide⟩

private theorem first_sparse {m k : ℕ} (hm : 0 < m) (hk : 0 < k) :
    firstFalse (sparse m k) = 0 := by
  apply first_false_eq
  · simp [lowReply,hm,sparse,show 0 ≠ k by omega]
  · omega
private theorem first_single {m : ℕ} (hm : 1 < m) :
    firstFalse (sparse m 0) = 1 := by
  apply first_false_eq
  · simp [lowReply,hm,sparse]
  · intro i hi
    have iz : i = 0 := by omega
    subst i
    simp [lowReply,sparse,show 0 < m by omega]
private theorem first_double {m k : ℕ} (hm : 1 < m) (hk : 2 ≤ k) :
    firstFalse (double m k) = 1 := by
  apply first_false_eq
  · simp [lowReply,hm,double,show 1 ≠ k by omega]
  · intro i hi
    have iz : i = 0 := by omega
    subst i
    simp [lowReply,double,show 0 < m by omega]
private theorem first_punctured {m t : ℕ} (ht : t < m-1) :
    firstFalse (punctured m t) = t := by
  apply first_false_eq
  · simp [lowReply,punctured,show t < m by omega]
  · intro i hi
    simp [lowReply,punctured,hi,show i < m by omega]

private theorem row_target_mass (m : ℕ) (hm : 4 ≤ m) (a : ℕ → ℝ)
    (pos : ∀ i, 0 ≤ a i) (upper : ∀ i, a i ≤ 1) (q : Rows m) :
    ((finiteTarget m a (rowWord m q)) {r | rowEvent m q r.val}).toReal =
      rowTarget m a q := by
  have mass (i : ℕ) : ENNReal.ofReal (1-a i) + ENNReal.ofReal (a i) = 1 := by
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr (upper i)) (pos i)]
    simp
  rcases q with k | (_ | (k | (k | (k | _))))
  · have hk := Finset.mem_Icc.mp k.property
    simp [rowWord,rowEvent,rowTarget,finiteTarget,first_sparse (m:=m) (k:=k.val) (by omega) (by omega),
      show 0 < m by omega,mass]
  · simp [rowWord,rowEvent,rowTarget,finiteTarget,first_single (m:=m) (by omega),
      show 1 < m by omega,mass]
  · have hk := Finset.mem_Icc.mp k.property
    simp [rowWord,rowEvent,rowTarget,finiteTarget,first_double (m:=m) (k:=k.val) (by omega) (by omega),
      show 1 < m by omega,ENNReal.toReal_ofReal (pos 1)]
  · have hk := Finset.mem_Icc.mp k.property
    simp [rowWord,rowEvent,rowTarget,finiteTarget,firstFalse_chain m k.val (by omega),
      show k.val < m by omega,show k.val+1 ≠ 0 by omega,ENNReal.toReal_ofReal (pos k.val)]
  · have hk := Finset.mem_Icc.mp k.property
    simp [rowWord,rowEvent,rowTarget,finiteTarget,first_punctured (m:=m) (t:=k.val) (by omega),
      show k.val < m by omega,show k.val+1 ≠ 0 by omega,ENNReal.toReal_ofReal (pos k.val)]
  · simp [rowWord,rowEvent,rowTarget,finiteTarget,firstFalse_chain m m le_rfl]

private theorem late_pair (m : ℕ) (hm : 4 ≤ m) (F : ℕ → ℝ) :
    (∑ t ∈ Finset.Icc 2 (m-1), (lateWeight m t : ℝ)*F t) +
      (∑ t ∈ Finset.Icc 2 (m-3), F t) =
      (m-2 : ℕ) * ∑ t ∈ Finset.Icc 2 (m-1), F t := by
  have extend : (∑ t ∈ Finset.Icc 2 (m-3), F t) =
      ∑ t ∈ Finset.Icc 2 (m-1), if t < m-2 then F t else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext t
    simp only [Finset.mem_filter,Finset.mem_Icc]
    omega
  rw [extend,← Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases h : t < m-2
  · simp only [lateWeight,h,ite_true]
    have eq : ((m-3 : ℕ) : ℝ)+1 = (m-2 : ℕ) := by
      exact_mod_cast (show m-3+1 = m-2 by omega)
    rw [← eq]
    ring
  · simp [lateWeight,h]

private theorem weight_total (m : ℕ) (hm : 4 ≤ m) :
    (∑ q : Rows m, (rowWeight m q : ℝ)) = ((m-2)*(m+1) : ℕ) := by
  simp only [Fintype.sum_sum_type]
  simp only [rowWeight,Fintype.sum_unique,Nat.cast_one]
  rw [subtype_sum _ (fun _ => (1 : ℝ)),subtype_sum _ (fun _ => (1 : ℝ)),
    subtype_sum _ (fun t => (lateWeight m t : ℝ)),subtype_sum _ (fun _ => (1 : ℝ))]
  have lp := late_pair m hm (fun _ => 1)
  simp only [mul_one,Finset.sum_const,Nat.card_Icc,nsmul_eq_mul] at lp ⊢
  have c1 : m-2+1-1 = m-2 := by omega
  have c2 : m-2+1-2 = m-3 := by omega
  have c3 : m-3+1-2 = m-4 := by omega
  have c4 : m-1+1-2 = m-2 := by omega
  simp only [c1,c2,c3,c4,mul_one] at lp ⊢
  have a2 : ((m-2 : ℕ) : ℝ) = (m : ℝ)-2 := by rw [Nat.cast_sub (by omega)]; norm_num
  have a3 : ((m-3 : ℕ) : ℝ) = (m : ℝ)-3 := by rw [Nat.cast_sub (by omega)]; norm_num
  have a4 : ((m-4 : ℕ) : ℝ) = (m : ℝ)-4 := by rw [Nat.cast_sub (by omega)]; norm_num
  push_cast
  simp only [a2,a3,a4] at lp ⊢
  nlinarith [lp]

private theorem target_total (m : ℕ) (hm : 4 ≤ m) (a : ℕ → ℝ) :
    (∑ q : Rows m, (rowWeight m q : ℝ)*rowTarget m a q) =
      2*m-3 + (m-3 : ℕ)*a 1 + (m-2 : ℕ)*(∑ t ∈ Finset.Icc 2 (m-1), a t) := by
  simp only [Fintype.sum_sum_type]
  simp only [rowWeight,rowTarget,Fintype.sum_unique,Nat.cast_one,one_mul,mul_one]
  rw [subtype_sum _ (fun _ => (1 : ℝ)),subtype_sum _ (fun _ => a 1),
    subtype_sum _ (fun t => (lateWeight m t : ℝ)*a t),subtype_sum _ a]
  have lp := late_pair m hm a
  simp only [Finset.sum_const,Nat.card_Icc,nsmul_eq_mul,mul_one]
  have c1 : m-2+1-1 = m-2 := by omega
  have c2 : m-2+1-2 = m-3 := by omega
  rw [c1,c2]
  have a2 : ((m-2 : ℕ) : ℝ) = (m : ℝ)-2 := by rw [Nat.cast_sub (by omega)]; norm_num
  simp only [a2] at lp ⊢
  linarith [lp]

private def eventMass {m : ℕ} (w : PMF (Catalog false m)) (q : Rows m) : ℝ :=
  (w.toMeasure.map (fun f => f.val (rowWord m q)) {r | rowEvent m q r.val}).toReal

private theorem average_score_bound (m : ℕ) (hm : 4 ≤ m) (w : PMF (Catalog false m)) :
    (∑ q : Rows m, (rowWeight m q : ℝ)*eventMass w q) ≤ (3*(m-2) : ℕ) := by
  letI : Fintype (Catalog false m) := Fintype.ofFinite _
  have expansion (q : Rows m) : eventMass w q =
      ∑ f : Catalog false m, (w f).toReal *
        (if rowEvent m q (f.val (rowWord m q)).val then 1 else 0) := by
    unfold eventMass
    rw [Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet,
      PMF.toMeasure_apply w (Set.to_countable _).measurableSet,tsum_fintype,ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro f _
      by_cases h : rowEvent m q (f.val (rowWord m q)).val <;> simp [Set.indicator,h]
    · intro f _
      by_cases h : rowEvent m q (f.val (rowWord m q)).val <;>
        simp [Set.indicator,h,w.apply_ne_top]
  have weights : ∑ f : Catalog false m, (w f).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun f _ => w.apply_ne_top f)]
    have hs : (∑ f : Catalog false m, w f) = 1 :=
      (tsum_fintype _).symm.trans w.tsum_coe
    rw [hs]
    norm_num
  simp_rw [expansion,Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ f : Catalog false m, (w f).toReal * (tableScore m f : ℝ) := by
      apply Finset.sum_congr rfl
      intro f _
      simp only [tableScore,Nat.cast_sum,apply_ite,Nat.cast_zero]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      split_ifs <;> simp_all <;> ring
    _ ≤ ∑ f : Catalog false m, (w f).toReal * (3*(m-2) : ℕ) := by
      apply Finset.sum_le_sum
      intro f _
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      exact_mod_cast table_score_bound m hm f
    _ = _ := by rw [← Finset.sum_mul,weights,one_mul]

/-- The uniform second-head inequality under one all-word common catalog cap. -/
theorem second_head_bound (m : ℕ) (hm : 4 ≤ m) (a : ℕ → ℝ)
    (pos : ∀ i, 0 ≤ a i) (upper : ∀ i, a i ≤ 1) (eps : ℝ) (heps : 0 ≤ eps)
    (w : PMF (Catalog false m))
    (cap : ∀ b, measurableTotalVariation (w.toMeasure.map (fun f => f.val b))
      (finiteTarget m a b) ≤ ENNReal.ofReal eps) :
    ((m-2)*(m+1) : ℕ)*eps ≥ (m-3 : ℕ)*a 1 +
      (m-2 : ℕ)*(∑ t ∈ Finset.Icc 2 (m-1), a t) - (m-3 : ℕ) := by
  have row_lower (q : Rows m) : rowTarget m a q - eps ≤ eventMass w q := by
    let E : Set (Fin (m+1)) := {r | rowEvent m q r.val}
    let law := w.toMeasure.map (fun f => f.val (rowWord m q))
    have hlaw : IsProbabilityMeasure law := inferInstance
    have h := (le_iSup (fun E : {E : Set (Fin (m+1)) // MeasurableSet E} =>
      max (law E.1 - finiteTarget m a (rowWord m q) E.1)
        (finiteTarget m a (rowWord m q) E.1 - law E.1))
      ⟨E,(Set.to_countable E).measurableSet⟩).trans (cap (rowWord m q))
    have hb := tsub_le_iff_right.mp ((le_max_right _ _).trans h)
    have hc := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,measure_ne_top law E⟩) hb
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (measure_ne_top law E),
      ENNReal.toReal_ofReal heps] at hc
    have mass := row_target_mass m hm a pos upper q
    change rowTarget m a q - eps ≤ (law E).toReal
    change (finiteTarget m a (rowWord m q) E).toReal = rowTarget m a q at mass
    linarith
  have lower := Finset.sum_le_sum (fun q (_ : q ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (row_lower q) (Nat.cast_nonneg (rowWeight m q)))
  simp_rw [mul_sub] at lower
  rw [Finset.sum_sub_distrib,← Finset.sum_mul,weight_total m hm,target_total m hm a] at lower
  have bound := average_score_bound m hm w
  have cast3 : ((3*(m-2) : ℕ) : ℝ) = 3*(m : ℝ)-6 := by
    rw [Nat.cast_mul,Nat.cast_sub (by omega)]
    norm_num
    ring
  have castm : ((m-3 : ℕ) : ℝ) = (m : ℝ)-3 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [cast3] at bound
  simp only [castm] at lower ⊢
  linarith

#print axioms second_head_bound
end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.SecondHeadBound
