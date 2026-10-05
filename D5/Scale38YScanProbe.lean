import D5.Scale38FirstExitProbe

open D5.S3.Arith.FibonacciAtomic
open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply readout leaves vector chi)
open ActualImageSevenLeafSeparation (leafAddresses leafLabel seven_leaf_separation)
open Scale38NestedCompensation (family query)
open RawEndpointPeeling (Peels)

set_option autoImplicit false
local notation "Index" => fun k : Nat => Unit ⊕ (Fin k ⊕ Fin k)

namespace YScanAttempt

def count (k : Nat) (i : Fin k) : Nat := i.val+1 + if i.val+1=k then 1 else 3
def queryAt (k : Nat) (i : Fin k) (t : Nat) : Address :=
  if t < i.val+1 then query t else true :: query (if i.val+1=k then 1 else t-(i.val+1))
def exitAt (k : Nat) (i : Fin k) : Index k → Nat
  | .inl _ => k
  | .inr (.inl j) => j.val
  | .inr (.inr j) => if j.val < i.val then j.val+1 else if i.val < j.val then i.val+3 else count k i
def replyAt (k : Nat) (i : Fin k) : Index k → Reply
  | .inr (.inl j) => if j.val < i.val+1 then .branch else .absent
  | _ => .absent

theorem attempt (k : Nat) (hk : 1 ≤ k) (i : Fin k) (hi : k ≤ i.val+2) :
    let e := Fintype.equivFin (Index k)
    Peels (family k ∘ e.symm) (e (.inr (.inr i))) Finset.univ
      ((List.range (count k i)).map (queryAt k i)) ∧
      ∀ U : Index k, U ≠ .inr (.inr i) →
        ((List.range (count k i)).map (queryAt k i)).find? (fun a => decide (chi (readout a (family k U)) = 1)) =
          some ((queryAt k i) ((exitAt k i) U)) := by
  classical
  let z : Index k := .inr (.inr i)
  let e := Fintype.equivFin (Index k)
  let F := family k ∘ e.symm
  have base := Scale38NestedCompensation.result k hk
  have rawP := base.2.2.2.2.1
  have rawX := base.2.2.2.2.2.1
  have rawY := base.2.2.2.2.2.2.1
  have right_match (j : Fin k) (h : Nat) (hh : h ≤ k-j.val) :
      readout (true :: query h) (family k (.inr (.inr j))) = .alpha := by
    have hpositive : 1 ≤ k-j.val := by omega
    exact (Scale38NestedCompensation.result (k-j.val) hpositive).2.2.2.2.1 h hh
  have right_absent (j : Fin k) :
      readout (true :: query (k-j.val+1)) (family k (.inr (.inr j))) = .absent := by
    let n := k-j.val
    exact (Scale38NestedCompensation.result (n+1) (by omega)).2.2.2.2.2.2.1
      ⟨n,by omega⟩ |>.2
  have target (t : Nat) (ht : t < count k i) :
      readout (queryAt k i t) (family k z) = .alpha := by
    by_cases htl : t < i.val+1
    · simpa only [queryAt, if_pos htl] using (rawY i).1 t (by omega)
    · simp only [queryAt, if_neg htl]
      apply right_match
      unfold count at ht
      split_ifs at ht ⊢ <;> omega
  have target_leaf (t : Nat) (ht : t < count k i) :
      queryAt k i t ∈ leaves (family k z) ∧ chi (readout (queryAt k i t) (family k z)) = 0 := by
    have hr := target t ht
    have hm := ((seven_leaf_separation.1 (family k z)).2 (queryAt k i t)).mpr
      ⟨true, by simp only [leafLabel, hr]⟩
    exact ⟨by simpa only [leafAddresses, List.mem_toFinset] using hm, by rw [hr]; rfl⟩
  have before (U : Index k) (t : Nat) (ht : t < count k i) (hb : t < exitAt k i U) :
      readout (queryAt k i t) (family k U) = readout (queryAt k i t) (family k z) := by
    rw [target t ht]
    cases U with
    | inl u =>
      have htk : t < k := hb
      by_cases htl : t < i.val+1
      · simpa only [queryAt, if_pos htl] using rawP t (by omega)
      · have he : t = i.val+1 := by omega
        have hlast : i.val+1 ≠ k := by omega
        rw [queryAt, if_neg htl, if_neg hlast, he, Nat.sub_self]
        rfl
    | inr v =>
      cases v with
      | inl j =>
        have htj : t < j.val := hb
        have htl : t < i.val+1 := by omega
        simpa only [queryAt, if_pos htl] using (rawX j).1 t htj
      | inr j =>
        by_cases hji : j.val = i.val
        · have he : j = i := Fin.ext hji
          simpa only [he] using target t ht
        · by_cases hjlt : j.val < i.val
          · have htj : t < j.val+1 := by simpa only [exitAt, if_pos hjlt] using hb
            have htl : t < i.val+1 := by omega
            simpa only [queryAt, if_pos htl] using (rawY j).1 t (by omega)
          · have hilt : i.val < j.val := by omega
            have htj : t < i.val+3 := by simpa only [exitAt, if_neg hjlt, if_pos hilt] using hb
            by_cases htl : t < i.val+1
            · simpa only [queryAt, if_pos htl] using (rawY j).1 t (by omega)
            · have hlast : i.val+1 ≠ k := by omega
              simp only [queryAt, if_neg htl, if_neg hlast]
              apply right_match
              omega
  have exiting (U : Index k) (hu : U ≠ z) : exitAt k i U < count k i ∧
      readout (queryAt k i (exitAt k i U)) (family k U) = replyAt k i U := by
    cases U with
    | inl u =>
      have htl : ¬ k < i.val+1 := by omega
      have tail : (if i.val+1=k then 1 else k-(i.val+1)) = 1 := by split_ifs <;> omega
      refine ⟨by change k < count k i; unfold count; split_ifs <;> omega, ?_⟩
      simp only [exitAt, queryAt, if_neg htl, tail, replyAt]
      rfl
    | inr v =>
      cases v with
      | inl j =>
        refine ⟨by change j.val < count k i; unfold count; split_ifs <;> omega, ?_⟩
        by_cases hjl : j.val < i.val+1
        · change readout (queryAt k i j.val) (family k (.inr (.inl j))) =
            if j.val < i.val+1 then .branch else .absent
          simp only [queryAt, if_pos hjl]
          exact (rawX j).2
        · have he : j.val = i.val+1 := by omega
          have hlast : i.val+1 ≠ k := by omega
          simp only [exitAt, queryAt, replyAt, if_neg hjl, if_neg hlast, he, Nat.sub_self, Nat.lt_irrefl, if_false]
          rfl
      | inr j =>
        have hji : j.val ≠ i.val := by intro h; apply hu; congr 2; exact Fin.ext h
        by_cases hjlt : j.val < i.val
        · have htl : j.val+1 < i.val+1 := by omega
          simp only [exitAt, if_pos hjlt, queryAt, if_pos htl, replyAt]
          exact ⟨by unfold count; split_ifs <;> omega, (rawY j).2⟩
        · have hilt : i.val < j.val := by omega
          have hlast : i.val+1 ≠ k := by omega
          have htl : ¬ i.val+3 < i.val+1 := by omega
          have hdelta : i.val+3-(i.val+1) = k-j.val+1 := by omega
          simp only [exitAt, if_neg hjlt, if_pos hilt, queryAt, if_neg htl,
            if_neg hlast, hdelta, replyAt]
          exact ⟨by unfold count; rw [if_neg hlast]; omega, right_absent j⟩
  have unique (U V : Index k) (hu : U ≠ z) (hv : V ≠ z)
      (he : exitAt k i U = exitAt k i V)
      (hr : readout (queryAt k i (exitAt k i U)) (family k U) =
        readout (queryAt k i (exitAt k i V)) (family k V)) : U = V := by
    rw [(exiting U hu).2, (exiting V hv).2] at hr
    cases U with
    | inl u =>
      cases V with
      | inl v => cases u; cases v; rfl
      | inr v =>
        cases v with
        | inl j => simp only [exitAt, count] at he; omega
        | inr j =>
          have hji : j.val ≠ i.val := by intro h; apply hv; congr 2; exact Fin.ext h
          simp only [exitAt, count] at he
          split_ifs at he <;> omega
    | inr u =>
      cases u with
      | inl j =>
        cases V with
        | inl u => simp only [exitAt, count] at he; omega
        | inr v =>
          cases v with
          | inl l => congr 2; exact Fin.ext he
          | inr l =>
            simp only [exitAt, count] at he
            simp only [replyAt] at hr
            split_ifs at he hr <;> cases hr <;> omega
      | inr j =>
        cases V with
        | inl u =>
          have hji : j.val ≠ i.val := by intro h; apply hu; congr 2; exact Fin.ext h
          simp only [exitAt, count] at he
          split_ifs at he <;> omega
        | inr v =>
          cases v with
          | inl l =>
            simp only [exitAt, count] at he
            simp only [replyAt] at hr
            split_ifs at he hr <;> cases hr <;> omega
          | inr l =>
            have hji : j.val ≠ i.val := by intro h; apply hu; congr 2; exact Fin.ext h
            have hli : l.val ≠ i.val := by intro h; apply hv; congr 2; exact Fin.ext h
            simp only [exitAt, count] at he
            congr 2
            apply Fin.ext
            split_ifs at he <;> omega
  constructor
  ·
    change Peels F (e z) Finset.univ _
    apply safe_scan F (e z) (queryAt k i) (fun j => exitAt k i (e.symm j))
    · simpa only [F, Function.comp_apply, Equiv.symm_apply_apply] using target_leaf
    · intro j t ht hb
      exact (before (e.symm j) t ht hb).trans (by simp only [F, Function.comp_apply, Equiv.symm_apply_apply])
    · intro j hj
      have hn : e.symm j ≠ z := by
        intro h; apply hj; exact (e.apply_symm_apply j).symm.trans (congrArg e h)
      have hx := exiting (e.symm j) hn
      refine ⟨hx.1, ?_⟩
      change chi (readout (queryAt k i (exitAt k i (e.symm j))) (family k (e.symm j))) = 1
      rw [hx.2]
      generalize e.symm j = U
      cases U with
      | inl u => rfl
      | inr v => cases v with
        | inl l => simp only [replyAt]; split_ifs <;> rfl
        | inr l => rfl
    · intro a b ha hb he hr
      apply e.symm.injective
      apply unique (e.symm a) (e.symm b)
      · intro h; apply ha; exact (e.apply_symm_apply a).symm.trans (congrArg e h)
      · intro h; apply hb; exact (e.apply_symm_apply b).symm.trans (congrArg e h)
      · exact he
      · exact hr
  · intro U hu
    have hfirst := first_exit F (e z) (e U) (queryAt k i) (fun j => (exitAt k i) (e.symm j))
      (fun h => hu (e.injective h))
      (fun t ht => by simpa only [F, Function.comp_apply, Equiv.symm_apply_apply]
        using (target_leaf t ht).2)
      (fun j t ht hb => (before (e.symm j) t ht hb).trans
        (by simp only [F, Function.comp_apply, Equiv.symm_apply_apply]))
      (fun j hj => by
        have hn : e.symm j ≠ z := by
          intro h; apply hj; exact (e.apply_symm_apply j).symm.trans (congrArg e h)
        have hx := exiting (e.symm j) hn
        refine ⟨hx.1, ?_⟩
        change chi (readout ((queryAt k i) ((exitAt k i) (e.symm j))) (family k (e.symm j))) = 1
        rw [hx.2]
        generalize e.symm j = V
        cases V with
        | inl u => rfl
        | inr v =>
          cases v with
          | inl l => simp only [replyAt]; split_ifs <;> rfl
          | inr l => rfl
      )
    simpa only [F, Function.comp_apply, Equiv.symm_apply_apply] using hfirst

end YScanAttempt
