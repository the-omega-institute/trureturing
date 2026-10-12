/- GID: D5/S3/Arith/FibonacciAtomic/Observer/OriginalAbsenceDoubleZero
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/OriginalAbsenceDoubleZero
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Both even-epoch label probes vanish at every originally absent native address. -/

import D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout
import D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.OriginalAbsenceDoubleZero

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualLeafHistoryRigidity (subtree)
open DelayedOriginalReadout (rights)

/-- Originally absent addresses cannot acquire either even-epoch label probe. -/
theorem original_absence_double_zero (u : Source) (k : Nat) (p : Address)
    (positive : 1 ≤ k) (absent : readout p u = .absent) :
    readout (p ++ rights (k-1) ++ [false, false]) (substitution^[2*k] u) = .absent ∧
    readout (p ++ rights k ++ [false]) (substitution^[2*k] u) = .absent := by
  let T : Nat → Source := fun n => substitution^[n] (.of true)
  have Tzero : T 0 = .of true := rfl
  have Tone : T 1 = .of false := rfl
  have Tstep (n : Nat) : substitution (T n) = T (n+1) := by
    exact (Function.iterate_succ_apply' substitution n (.of true)).symm
  have Tpair (n : Nat) : T (n+2) = .mul (T (n+1)) (T n) := by
    change substitution^[n+2] (.of true) = _
    rw [Function.iterate_add_apply]
    change substitution^[n] (.mul (.of false) (.of true)) = _
    rw [Function.Semiconj₂.iterate
      (show Function.Semiconj₂ substitution FreeMagma.mul FreeMagma.mul from
        fun s t => substitution.map_mul s t) n (.of false) (.of true)]
    congr 1
  have newborn (a : Address) (v y : Source) :
      subtree a v = none → subtree a (substitution v) = some y →
      ∃ j, j ≤ 1 ∧ y = T j := by
    induction a generalizing v with
    | nil => simp [subtree]
    | cons d a ih =>
      cases v with
      | of b =>
        cases b with
        | true => simp [subtree, substitution]
        | false =>
          change none = none →
            subtree (d :: a) (.mul (.of false) (.of true)) = some y → _
          intro _ hy
          cases d <;> cases a with
          | nil =>
            simp only [subtree, Option.some.injEq] at hy
            subst y
            first | exact ⟨1, by omega, Tone.symm⟩ | exact ⟨0, by omega, Tzero.symm⟩
          | cons e a => simp [subtree] at hy
      | mul l r =>
        change subtree (d :: a) (.mul l r) = none →
          subtree (d :: a) (.mul (substitution l) (substitution r)) = some y → _
        cases d <;> exact ih _
  have born_rank (N : Nat) (a : Address) (v y : Source) :
      subtree a v = none → subtree a (substitution^[N] v) = some y →
      ∃ j, j ≤ N ∧ y = T j := by
    induction N generalizing y with
    | zero => intro hn hy; simp only [Function.iterate_zero, id_eq, hn] at hy; cases hy
    | succ N ih =>
      intro hn hy
      rw [Function.iterate_succ_apply'] at hy
      cases hz : subtree a (substitution^[N] v) with
      | none =>
        obtain ⟨j, hj, he⟩ := newborn a (substitution^[N] v) y hz hy
        exact ⟨j, by omega, he⟩
      | some z =>
        obtain ⟨j, hj, he⟩ := ih z hn hz
        have ht := NativeDepthPatterns.original_present_transport 1 a
          (substitution^[N] v) z hz
        change subtree a (substitution (substitution^[N] v)) = some (substitution z) at ht
        have hyz : y = substitution z := Option.some.inj (hy.symm.trans ht)
        exact ⟨j+1, by omega, by rw [hyz, he, Tstep]⟩
  have endpoints (s j : Nat) (bound : j ≤ 2*(s+1)) :
      readout (rights s ++ [false, false]) (T j) = .absent ∧
      readout (rights (s+1) ++ [false]) (T j) = .absent := by
    induction s generalizing j with
    | zero =>
      have cases_j : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases cases_j with rfl | rfl | rfl
      · simp [rights, Tzero, readout]
      · simp [rights, Tone, readout]
      · rw [Tpair 0, Tone, Tzero]
        simp [rights, readout]
    | succ s ih =>
      cases j with
      | zero => simp [rights, List.replicate_succ, Tzero, readout]
      | succ j =>
        cases j with
        | zero => simp [rights, List.replicate_succ, Tone, readout]
        | succ j =>
          rw [show j+1+1 = j+2 by omega, Tpair]
          simpa only [rights, List.replicate_succ, List.cons_append, readout] using
            ih j (by omega)
  have readAt := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have original_none : subtree p u = none := by
    have hr := readAt p [] u
    simp only [List.append_nil] at hr
    cases h : subtree p u with
    | none => rfl
    | some v =>
      rw [h] at hr
      rw [hr] at absent
      cases v with
      | of b => cases b <;> simp [readout] at absent
      | mul l r => simp [readout] at absent
  have hs : k-1+1 = k := by omega
  rw [List.append_assoc, List.append_assoc, readAt, readAt]
  cases h : subtree p (substitution^[2*k] u) with
  | none => exact ⟨rfl, rfl⟩
  | some y =>
    obtain ⟨j, hj, he⟩ := born_rank (2*k) p u y original_none h
    rw [he]
    simpa only [hs] using endpoints (k-1) j (by omega)

#print axioms original_absence_double_zero
end D5.S3.Arith.FibonacciAtomic.Observer.OriginalAbsenceDoubleZero
