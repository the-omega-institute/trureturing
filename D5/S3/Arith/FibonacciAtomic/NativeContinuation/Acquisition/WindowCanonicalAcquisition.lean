/- GID: D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowCanonicalAcquisition
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowCanonicalAcquisition
   mirror-E: none(waiver:unbounded-operational-correspondence)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   utility: none
   digest: One execution obtains the exact original column, height and positive numeral. -/

import D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.WindowRegisterResources

namespace PhysicalWindowContinuation.CanonicalAcquisition
open RegisterHandoff
open D5.S3.Arith.FibonacciAtomic

/-- The sole original input is acquired into four separate canonical registers
by one fixed local-action program, with one attained time and persistent-space bound. -/
theorem original_canonical_acquisition :
    Function.Injective (finiteCode (α := Symbol)) ∧
    ∃ A B : ℕ, 0 < A ∧ 0 < B ∧
    ∀ (w : List Window) (e : Bool),
      D5.S3.Arith.ZeckendorfFutureKernel.legal false
        (NativeContinuation.NullReplyFiber.highBits (w.map Original.letter) ++ [e]) →
      0 < Original.numeral w e →
    ∃ T : ℕ, T ≤ A*(w.length+1)^2 ∧
      run (initial w e) T = registerEnd w e ∧
      program (registerEnd w e).control = .halt ∧
      RegisterRep (registerEnd w e) 0 (value1 (Original.finalColumns w e)) ∧
      RegisterRep (registerEnd w e) 1 (value2 (Original.finalColumns w e)) ∧
      RegisterRep (registerEnd w e) 2 w.length ∧
      RegisterRep (registerEnd w e) 3 (Original.numeral w e) ∧
      Original.pair (Original.finalColumns w e) =
        NativeContinuation.JointLaw.composition (w.map Original.letter) ∧
      Original.pair (Original.finalColumns w e) = Original.columnSum w ∧
      Original.maximumColumn [] = 0 ∧
      (∀ b, Original.maximumColumn (w ++ [b]) ≤ 5*Original.maximumColumn w+2) ∧
      2*Original.maximumColumn w+1 ≤ 5^w.length ∧
      Original.maximumColumn w ≤ (5^w.length-1)/2 ∧
      Original.numeral w e < Nat.fib (3*w.length+3) ∧
      (∀ n ≤ T, charged w e n ≤ B*(w.length+1)) ∧
      (∀ n ≤ T, ∀ t, 0 ≤ (run (initial w e) n).head t ∧
        (run (initial w e) n).head t ≤ 3*w.length+6) := by
  obtain ⟨hinj,A,B,hA,hB,hall⟩ := Original.original_accepting_packed_resources
  refine ⟨hinj,A+1000,code.length+Fintype.card State+80*(Fintype.card Symbol+1),
    by omega,by omega,?_⟩
  intro w e hg hp
  obtain ⟨t,ht,he,hh,hpair,hcount,hN,hsum,hm0,hmstep,hmp,hmg,hcap,hlen,_,hframe⟩ :=
    hall w e hg hp
  have hc : (PhysicalWindowContinuation.run (PhysicalWindowContinuation.initial w e) t).control =
      .done := by rw [he]; rfl
  obtain ⟨s,hs,hse,hpre⟩ := first_done_lift (PhysicalWindowContinuation.initial w e) t hc
  have hseam : run (initial w e) s = base (packedEnd w e) := by
    simpa only [initial,he,packedEnd] using hse
  obtain ⟨u,hu,huend,hhalt,hport,hregs⟩ := packed_port w e hlen
  have hfirst : ∀ n ≤ s, ∀ k, 0 ≤ (run (initial w e) n).head k ∧
      (run (initial w e) n).head k ≤ 3*w.length+6 := by
    intro n hn k
    change (0 ≤ (run (base (PhysicalWindowContinuation.initial w e)) n).head k ∧
      (run (base (PhysicalWindowContinuation.initial w e)) n).head k ≤ 3*w.length+6)
    rw [hpre n hn]
    obtain ⟨h0,h1⟩ := PhysicalWindowContinuation.frame_heads _ w.length (3*w.length+5) _
      (by omega) (hframe n (hn.trans hs)) k
    change (0 ≤ (PhysicalWindowContinuation.run (PhysicalWindowContinuation.initial w e) n).head k ∧
      (PhysicalWindowContinuation.run (PhysicalWindowContinuation.initial w e) n).head k ≤ 3*w.length+6)
    exact ⟨h0,by omega⟩
  have hfull := heads_join (3*w.length+6) s (u+1) _ _ hseam hfirst hport
  have htime : u+1+s ≤ (A+1000)*(w.length+1)^2 := by
    have hpoly : 128*(3*w.length+5)+5 ≤ 1000*(w.length+1)^2 := by nlinarith
    calc
      u+1+s ≤ t+(128*(3*w.length+5)+5) := by omega
      _ ≤ A*(w.length+1)^2+1000*(w.length+1)^2 := Nat.add_le_add ht hpoly
      _ = (A+1000)*(w.length+1)^2 := by ring
  have hrun : run (initial w e) (u+1+s) = registerEnd w e := by
    rw [run,Function.iterate_add_apply]
    change run (run _ s) (u+1)=_
    rw [hseam]
    exact huend
  have hrep0 : RegisterRep (registerEnd w e) 0 (value1 (Original.finalColumns w e)) := by
    simpa [bitValue,select,value1] using register_rep w e 0
  have hrep1 : RegisterRep (registerEnd w e) 1 (value2 (Original.finalColumns w e)) := by
    simpa [bitValue,select,value2] using register_rep w e 1
  have hrep2 : RegisterRep (registerEnd w e) 2 w.length := by
    rw [← hcount]
    simpa [bitValue,select,valueCount] using register_rep w e 2
  have hrep3 : RegisterRep (registerEnd w e) 3 (Original.numeral w e) := by
    rw [← hN]
    simpa [bitValue,select,valueN] using register_rep w e 3
  exact ⟨u+1+s,htime,hrun,hhalt,hrep0,hrep1,hrep2,hrep3,hpair,hsum,hm0,hmstep,hmp,hmg,
    by rwa [hN] at hcap,charged_bound w e (u+1+s) hfull,hfull⟩

end PhysicalWindowContinuation.CanonicalAcquisition
