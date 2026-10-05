import D5.Scale38FirstExitProbe

open D5.S3.Arith.FibonacciAtomic
open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply readout leaves vector chi)
open ActualImageSevenLeafSeparation (A C E leafAddresses leafLabel seven_leaf_separation)
open ActualJointResponseCostCore (survivors)
open FourExitRawEndpointSpectrum (comb comb_slot_readout comb_tail_readout)
open Scale38NestedCompensation (family query)
open RawEndpointPeeling (Peels)

set_option autoImplicit false
local notation "Index" => fun k : Nat => Unit ⊕ (Fin k ⊕ Fin k)
local notation "B" => FourExitRawEndpointSpectrum.B

namespace XScanAttempt

def queryAt (k t : Nat) : Address := if t < k then query (t+1) else [true,true]
def exitAt (k : Nat) : Index k → Nat
  | .inl _ => k
  | .inr (.inl j) => if j.val = 0 then k+1 else j.val-1
  | .inr (.inr i) => i.val

def replyAt {k : Nat} : Index k → Reply
  | .inr (.inr _) => .absent
  | _ => .branch

theorem attempt (k : Nat) (hk : 1 ≤ k) :
    let e := Fintype.equivFin (Index k)
    Peels (family k ∘ e.symm) (e (.inr (.inl ⟨0,by omega⟩))) Finset.univ
      ((List.range (k+1)).map (queryAt k)) ∧
      ∀ U : Index k, U ≠ .inr (.inl ⟨0,by omega⟩) →
        ((List.range (k+1)).map (queryAt k)).find? (fun a => decide (chi (readout a (family k U)) = 1)) =
          some ((queryAt k) ((exitAt k) U)) := by
  classical
  let z : Index k := .inr (.inl ⟨0,by omega⟩)
  let e := Fintype.equivFin (Index k)
  let F := family k ∘ e.symm
  have base := Scale38NestedCompensation.result k hk
  have rawP := base.2.2.2.2.1
  have rawX := base.2.2.2.2.2.1
  have rawY := base.2.2.2.2.2.2.1
  have normal (j : Fin k) (s : Nat) (hs : s ≤ k) (hne : s ≠ j.val) :
      readout (query s) (family k (.inr (.inl j))) = .alpha := by
    change readout (List.replicate s true ++ [false,false,true])
      (comb k (fun l => if l = j then B else A) C) = .alpha
    by_cases hsk : s < k
    · have hfin : (⟨s,hsk⟩ : Fin k) ≠ j := fun h => hne (congrArg Fin.val h)
      have h := comb_slot_readout k (fun l => if l = j then B else A) C ⟨s,hsk⟩ [false,true]
      rw [if_neg hfin] at h
      exact h.trans rfl
    · have he : s = k := by omega
      subst s
      exact (comb_tail_readout k (fun l => if l = j then B else A) C [false,false,true]).trans rfl
  have target (t : Nat) (ht : t < k+1) :
      readout (queryAt k t) (family k z) = if t < k then .alpha else .beta := by
    by_cases htk : t < k
    · simp only [queryAt, htk, ite_true]
      exact normal ⟨0,by omega⟩ (t+1) (by omega) (by change t+1 ≠ 0; omega)
    · simp only [queryAt, htk, ite_false]
      rfl
  have target_leaf (t : Nat) (ht : t < k+1) :
      queryAt k t ∈ leaves (family k z) ∧ chi (readout (queryAt k t) (family k z)) = 0 := by
    have hr := target t ht
    have hl : ∃ b, leafLabel (family k z) (queryAt k t) = some b := by
      by_cases htk : t < k
      · exact ⟨true, by simp [leafLabel, hr, htk]⟩
      · exact ⟨false, by simp [leafLabel, hr, htk]⟩
    have hm := ((seven_leaf_separation.1 (family k z)).2 (queryAt k t)).mpr hl
    refine ⟨by simpa only [leafAddresses, List.mem_toFinset] using hm, ?_⟩
    rw [hr]
    split_ifs <;> rfl
  have before (U : Index k) (t : Nat) (ht : t < k+1) (hb : t < exitAt k U) :
      readout (queryAt k t) (family k U) = readout (queryAt k t) (family k z) := by
    cases U with
    | inl u =>
      have htk : t < k := by simpa only [exitAt] using hb
      rw [target t ht, if_pos htk]
      simpa only [queryAt, if_pos htk] using rawP (t+1) (by omega)
    | inr v =>
      cases v with
      | inl j =>
        by_cases hj : j.val = 0
        · have he : j = ⟨0,by omega⟩ := Fin.ext hj
          rw [he]
        · have hsmall : t < j.val-1 := by simpa only [exitAt, if_neg hj] using hb
          have htk : t < k := by omega
          rw [target t ht, if_pos htk]
          simpa only [queryAt, if_pos htk] using (rawX j).1 (t+1) (by omega)
      | inr i =>
        have hsmall : t < i.val := hb
        have htk : t < k := by omega
        rw [target t ht, if_pos htk]
        simpa only [queryAt, if_pos htk] using (rawY i).1 (t+1) (by omega)
  have exiting (U : Index k) (hu : U ≠ z) : exitAt k U < k+1 ∧
      readout (queryAt k (exitAt k U)) (family k U) =
        replyAt U := by
    cases U with
    | inl u =>
      refine ⟨by simp [exitAt], ?_⟩
      simp only [exitAt, queryAt, Nat.lt_irrefl, if_false, replyAt]
      rfl
    | inr v =>
      cases v with
      | inl j =>
        have hj : j.val ≠ 0 := by
          intro h
          apply hu
          have he : j = ⟨0,by omega⟩ := Fin.ext h
          simp only [he]
          rfl
        have hsmall : j.val-1 < k := by omega
        have he : j.val-1+1 = j.val := by omega
        simp only [exitAt, if_neg hj, queryAt, if_pos hsmall, he]
        exact ⟨by omega, (rawX j).2⟩
      | inr i =>
        refine ⟨by dsimp only [exitAt]; omega, ?_⟩
        change readout (queryAt k i.val) (family k (.inr (.inr i))) = .absent
        rw [queryAt, if_pos i.isLt]
        exact (rawY i).2
  have unique (U V : Index k) (hu : U ≠ z) (hv : V ≠ z)
      (he : exitAt k U = exitAt k V)
      (hr : readout (queryAt k (exitAt k U)) (family k U) =
        readout (queryAt k (exitAt k V)) (family k V)) : U = V := by
    rw [(exiting U hu).2, (exiting V hv).2] at hr
    cases U with
    | inl u =>
      cases V with
      | inl v => cases u; cases v; rfl
      | inr v =>
        cases v with
        | inl j => simp only [exitAt] at he; split_ifs at he <;> omega
        | inr i => cases hr
    | inr u =>
      cases u with
      | inl j =>
        cases V with
        | inl u => simp only [exitAt] at he; split_ifs at he <;> omega
        | inr v =>
          cases v with
          | inl l =>
            have hj : j.val ≠ 0 := by intro h; apply hu; congr 2; exact Fin.ext h
            have hl : l.val ≠ 0 := by intro h; apply hv; congr 2; exact Fin.ext h
            simp only [exitAt, if_neg hj, if_neg hl] at he
            congr 2
            apply Fin.ext
            omega
          | inr i => cases hr
      | inr i =>
        cases V with
        | inl u => cases hr
        | inr v =>
          cases v with
          | inl j => cases hr
          | inr l =>
            congr 2
            exact Fin.ext he
  constructor
  ·
    change Peels F (e z) Finset.univ _
    apply safe_scan F (e z) (queryAt k) (fun i => exitAt k (e.symm i))
    · simpa only [F, Function.comp_apply, Equiv.symm_apply_apply] using target_leaf
    · intro i t ht hb
      exact (before (e.symm i) t ht hb).trans (by simp only [F, Function.comp_apply, Equiv.symm_apply_apply])
    · intro i hi
      have hn : e.symm i ≠ z := by
        intro h
        apply hi
        exact (e.apply_symm_apply i).symm.trans (congrArg e h)
      have hx := exiting (e.symm i) hn
      refine ⟨hx.1, ?_⟩
      change chi (readout (queryAt k (exitAt k (e.symm i))) (family k (e.symm i))) = 1
      rw [hx.2]
      generalize e.symm i = U
      cases U with
      | inl u => rfl
      | inr v => cases v <;> rfl
    · intro i j hi hj he hr
      apply e.symm.injective
      apply unique (e.symm i) (e.symm j)
      · intro h; apply hi; exact (e.apply_symm_apply i).symm.trans (congrArg e h)
      · intro h; apply hj; exact (e.apply_symm_apply j).symm.trans (congrArg e h)
      · exact he
      · exact hr
  · intro U hu
    have hfirst := first_exit F (e z) (e U) (queryAt k) (fun j => (exitAt k) (e.symm j))
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
        change chi (readout ((queryAt k) ((exitAt k) (e.symm j))) (family k (e.symm j))) = 1
        rw [hx.2]
        generalize e.symm j = V
        cases V with
        | inl u => rfl
        | inr v =>
          cases v <;> rfl
      )
    simpa only [F, Function.comp_apply, Equiv.symm_apply_apply] using hfirst

end XScanAttempt
