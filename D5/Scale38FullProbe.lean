import D5.Scale38PScanProbe
import D5.Scale38XScanProbe
import D5.Scale38YScanProbe
import D5.S3.Arith.FibonacciAtomic.Scale38RawEndpointSpectrum

open D5.S3.Arith.FibonacciAtomic
open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply readout leaves chi Strategy terminal paid cost)
open ActualImageSevenLeafSeparation (leafAddresses)
open ActualJointResponseCostCore (controllerPolicy controllerOutcome)
open Scale38NestedCompensation (family query)
open RawEndpointPeeling (Peels peelController)
set_option autoImplicit false
local notation "Index" => fun k : Nat => Unit ⊕ (Fin k ⊕ Fin k)

namespace FullSpectrumProbe

def endpointTargets (k : Nat) : Set (Index k) := {Z |
  match Z with
  | .inl _ => True
  | .inr (.inl j) => j.val = 0
  | .inr (.inr i) => k ≤ i.val+2}

def scanLength (k : Nat) : Index k → Nat
  | .inl _ | .inr (.inl _) => k+1
  | .inr (.inr i) => i.val+1 + if i.val+1=k then 1 else 3

def scanAddress (k : Nat) : Index k → Nat → Address
  | .inl _, t => query t
  | .inr (.inl _), t => if t < k then query (t+1) else [true,true]
  | .inr (.inr i), t => if t < i.val+1 then query t else
      true :: query (if i.val+1=k then 1 else t-(i.val+1))

def exitAddress (k : Nat) : Index k → Index k → Address
  | .inl _, .inl _ => query k
  | .inl _, .inr (.inl j) => query j.val
  | .inl _, .inr (.inr i) => query (i.val+1)
  | .inr (.inl _), .inl _ => [true,true]
  | .inr (.inl _), .inr (.inl j) => query j.val
  | .inr (.inl _), .inr (.inr i) => query (i.val+1)
  | .inr (.inr _), .inl _ => true :: query 1
  | .inr (.inr i), .inr (.inl j) => if j.val ≤ i.val then query j.val else true :: query 0
  | .inr (.inr i), .inr (.inr j) => if j.val < i.val then query (j.val+1) else true :: query 2

theorem full (k : Nat) (hk : 1 ≤ k) :
    let e := Fintype.equivFin (Index k)
    let F := family k ∘ e.symm
    (∀ Z : Index k, (∃ qs, Peels F (e Z) Finset.univ qs) ↔ Z ∈ endpointTargets k) ∧
    (∀ Z : Index k, Z ∈ endpointTargets k →
      let qs := (List.range (scanLength k Z)).map (scanAddress k Z)
      Peels F (e Z) Finset.univ qs ∧
      (∀ U : Index k, U ≠ Z →
        qs.find? (fun a => decide (chi (readout a (family k U)) = 1)) = some (exitAddress k Z U)) ∧
      ∃ π : Strategy,
        π.policy = controllerPolicy (peelController F (e Z) Finset.univ qs) ∧
        (∀ U, terminal π U = controllerOutcome (peelController F (e Z) Finset.univ qs) U) ∧
        (∀ U : Index k, cost π (family k U) = 3*k+14 - (if U = Z then 1 else 0)) ∧
        (∀ U : Index k, paid (terminal π (family k U)).1 = leafAddresses (family k U) ∪
          if U = Z then ∅ else {exitAddress k Z U})) := by
  classical
  let e := Fintype.equivFin (Index k)
  let F := family k ∘ e.symm
  have pschedule : scanAddress k (.inl ()) = query := rfl
  have xschedule (j : Fin k) : scanAddress k (.inr (.inl j)) = XScanAttempt.queryAt k := rfl
  have yschedule (i : Fin k) : scanAddress k (.inr (.inr i)) = YScanAttempt.queryAt k i := rfl
  have certificate (Z : Index k) (hZ : Z ∈ endpointTargets k) :
      Peels F (e Z) Finset.univ ((List.range (scanLength k Z)).map (scanAddress k Z)) ∧
      (∀ U : Index k, U ≠ Z →
        ((List.range (scanLength k Z)).map (scanAddress k Z)).find?
          (fun a => decide (chi (readout a (family k U)) = 1)) = some (exitAddress k Z U)) := by
    cases Z with
    | inl u =>
      cases u
      obtain ⟨hp, hf⟩ := PScanAttempt.attempt k hk
      refine ⟨by simpa [F, e, scanLength, pschedule] using hp, ?_⟩
      intro U hu
      have hfirst := hf U hu
      cases U with
      | inl u => cases u; exact (hu rfl).elim
      | inr p => cases p <;> simpa [scanLength, pschedule, PScanAttempt.exitAt, exitAddress] using hfirst
    | inr p => cases p with
      | inl j =>
        have hj : j.val = 0 := hZ
        have he : j = ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hk⟩ := Fin.ext hj
        rw [he]
        obtain ⟨hp, hf⟩ := XScanAttempt.attempt k hk
        refine ⟨by simpa [F, e, scanLength, xschedule] using hp, ?_⟩
        intro U hu
        have hfirst := hf U hu
        cases U with
        | inl u =>
          simpa [scanLength, xschedule, XScanAttempt.queryAt, XScanAttempt.exitAt,
            Nat.lt_irrefl, if_false, exitAddress] using hfirst
        | inr p => cases p with
          | inl l =>
            have hl : l.val ≠ 0 := by intro h; apply hu; congr 2; exact Fin.ext h
            have hbound : l.val-1 < k := by omega
            have hplus : l.val-1+1=l.val := by omega
            simpa [scanLength, xschedule, XScanAttempt.queryAt, XScanAttempt.exitAt,
              if_neg hl, if_pos hbound, hplus, exitAddress] using hfirst
          | inr l =>
            simpa [scanLength, xschedule, XScanAttempt.queryAt, XScanAttempt.exitAt,
              if_pos l.isLt, exitAddress] using hfirst
      | inr i =>
        have hi : k ≤ i.val+2 := hZ
        obtain ⟨hp, hf⟩ := YScanAttempt.attempt k hk i hi
        refine ⟨by simpa [F, e, scanLength, yschedule, YScanAttempt.count] using hp, ?_⟩
        intro U hu
        have hfirst := hf U hu
        have he : YScanAttempt.queryAt k i (YScanAttempt.exitAt k i U) = exitAddress k (.inr (.inr i)) U := by
          cases U with
          | inl u =>
            have htl : ¬ k < i.val+1 := by omega
            have tail : (if i.val+1=k then 1 else k-(i.val+1)) = 1 := by split_ifs <;> omega
            simp only [YScanAttempt.exitAt, YScanAttempt.queryAt, if_neg htl, tail, exitAddress]
          | inr p => cases p with
            | inl l =>
              by_cases hli : l.val ≤ i.val
              · have htl : l.val < i.val+1 := by omega
                simp [YScanAttempt.exitAt, YScanAttempt.queryAt, htl, exitAddress, hli]
              · have hl : l.val = i.val+1 := by omega
                have hlast : i.val+1 ≠ k := by omega
                simp [YScanAttempt.exitAt, YScanAttempt.queryAt, exitAddress, hl, hlast]
            | inr l =>
              have hli : l.val ≠ i.val := by intro h; apply hu; congr 2; exact Fin.ext h
              by_cases hlt : l.val < i.val
              · have htl : l.val+1 < i.val+1 := by omega
                simp only [YScanAttempt.exitAt, if_pos hlt, YScanAttempt.queryAt, if_pos htl,
                  exitAddress, if_pos hlt]
              · have hil : i.val < l.val := by omega
                have hlast : i.val+1 ≠ k := by omega
                have htl : ¬ i.val+3 < i.val+1 := by omega
                have hsub : i.val+3-(i.val+1)=2 := by omega
                simp only [YScanAttempt.exitAt, if_neg hlt, if_pos hil, YScanAttempt.queryAt,
                  if_neg htl, if_neg hlast, hsub, exitAddress, if_neg hlt]
        rw [he] at hfirst
        simpa only [scanLength, yschedule, YScanAttempt.count] using hfirst
  constructor
  · intro Z
    constructor
    · intro hp
      have excluded := Scale38RawEndpointSpectrum.result k hk
      cases Z with
      | inl u => trivial
      | inr p => cases p with
        | inl j =>
          change j.val = 0
          by_contra h
          exact excluded.1 j (by omega) hp
        | inr i =>
          change k ≤ i.val+2
          by_contra h
          exact excluded.2 i (by omega) hp
    · intro hZ
      exact ⟨_, (certificate Z hZ).1⟩
  · intro Z hZ
    dsimp only
    let qs := (List.range (scanLength k Z)).map (scanAddress k Z)
    obtain ⟨hp,hfirst⟩ := certificate Z hZ
    refine ⟨hp, hfirst, ?_⟩
    obtain ⟨π,hpolicy,hterminal,hcost,hpaid,hother⟩ := (RawEndpointPeeling.result k hk (e Z)).2 qs hp
    refine ⟨π,hpolicy,hterminal,?_,?_⟩
    · intro U
      have hc := hcost (e U)
      simpa only [F, e, qs, Function.comp_apply, Equiv.symm_apply_apply, Equiv.apply_eq_iff_eq] using hc
    · intro U
      by_cases hu : U = Z
      · subst U
        simpa only [F, e, qs, Function.comp_apply, Equiv.symm_apply_apply, if_true,
          Finset.union_empty] using hpaid
      · obtain ⟨q,hfind,hnot,hbill⟩ := hother (e U) (fun h => hu (e.injective h))
        have hf := hfirst U hu
        have he : q = exitAddress k Z U := Option.some.inj (hfind.symm.trans (by
          simpa only [F, e, qs, Function.comp_apply, Equiv.symm_apply_apply] using hf))
        simpa only [F, e, qs, Function.comp_apply, Equiv.symm_apply_apply, if_neg hu, he] using hbill
end FullSpectrumProbe
