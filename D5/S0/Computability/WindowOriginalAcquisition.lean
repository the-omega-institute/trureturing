/- GID: D5/S0/Computability/WindowOriginalAcquisition
   generality: I
   mirror-B: D5/B/S0/Computability/WindowOriginalAcquisition
   mirror-E: none(waiver:unbounded-original-input-local-execution)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   utility: none
   digest: Original padded inputs have attained acquisition and joint resource bounds. -/

import D5.S0.Computability.WindowOriginalEncoder
import D5.S0.Computability.WindowCanonicalPrefixes

namespace PhysicalWindowContinuation.CanonicalAcquisition
open RegisterHandoff
open D5.S3.Arith.FibonacciAtomic

/-- The only input is the independently encoded original word and its unit.
All prefixes, the literal return frame, and both resource bounds belong to one run. -/
theorem original_window_acquisition :
    Function.Injective (finiteCode (α := Symbol)) ∧
    ∃ A B : ℕ, 0 < A ∧ 0 < B ∧
    ∀ (h N : ℕ), 1 ≤ N → OriginalEncoder.L N ≤ h →
    let w := OriginalEncoder.localWord h N
    let e := OriginalEncoder.bit N 0
    ∃ T : ℕ, T ≤ A*(h+1)^2 ∧
      run (initial w e) T = registerEnd w e ∧
      program (registerEnd w e).control = .halt ∧
      RegisterRep (registerEnd w e) 0 (value1 (Original.finalColumns w e)) ∧
      RegisterRep (registerEnd w e) 1 (value2 (Original.finalColumns w e)) ∧
      RegisterRep (registerEnd w e) 2 h ∧
      RegisterRep (registerEnd w e) 3 N ∧
      Original.pair (Original.finalColumns w e) =
        NativeContinuation.JointLaw.composition (OriginalEncoder.W h N) ∧
      Original.pair (Original.finalColumns w e) = Original.columnSum w ∧
      Original.maximumColumn [] = 0 ∧
      (∀ b, Original.maximumColumn (w ++ [b]) ≤ 5*Original.maximumColumn w+2) ∧
      2*Original.maximumColumn w+1 ≤ 5^h ∧
      Original.maximumColumn w ≤ (5^h-1)/2 ∧
      N < Nat.fib (3*h+3) ∧
      (∀ n ≤ T, charged w e n ≤ B*(h+1)) ∧
      (∀ n ≤ T, ∀ t, 0 ≤ (run (initial w e) n).head t ∧
        (run (initial w e) n).head t ≤ 3*h+6) ∧
      (∀ n, (run (initial w e) n).cell sourceTrack=inputSource w e) ∧
      (registerEnd w e).cell workTrack=word (Original.finalColumns w e) ∧
      (∀ t : Track,(∀ j : Lane,t ≠ target j) → t ≠ sourceTrack → t ≠ workTrack →
        (registerEnd w e).cell t=fun _=>.blank) ∧
      (∀ t : Track,(registerEnd w e).head t=if t=sourceTrack then h else 0) ∧
      (∀ j : Lane,(normalized ((Original.finalColumns w e).map (select j))).length ≤
        (Original.finalColumns w e).length+1) ∧
      (∀ pre suf : List Window, pre++suf=w →
        ∃ q : ℕ, q ≤ T ∧ q ≤ 4+pre.length*(15*h+46) ∧
          run (initial w e) q =
            base (boundary (inputSource w e) pre.length
              (columnsAfter [zeros] pre) 0 (.source (seamAfter false pre))) ∧
          Original.pair (columnsAfter [zeros] pre) =
            NativeContinuation.JointLaw.composition (pre.map Original.letter) ∧
          valueCount (columnsAfter [zeros] pre) = pre.length ∧
          (columnsAfter [zeros] pre).length ≤ 1+3*pre.length) := by
  obtain ⟨hinj,A,B,hA,hB,hall⟩ := original_canonical_acquisition
  refine ⟨hinj,A,B,hA,hB,?_⟩
  intro h N hN hh
  dsimp only
  let w := OriginalEncoder.localWord h N
  let e := OriginalEncoder.bit N 0
  obtain ⟨hlen,hlegal,hnum⟩ := OriginalEncoder.local_source h N hh
  change w.length=h at hlen
  change Original.numeral w e=N at hnum
  have hmap : w.map Original.letter=OriginalEncoder.W h N := by
    simp only [w,OriginalEncoder.localWord,List.map_map]
    have he : Original.letter ∘ OriginalEncoder.localLetter=id := by
      funext b; cases b <;> rfl
    simp [he]
  obtain ⟨T,hT,hr,halt,r0,r1,r2,r3,hpair,hsum,hm0,hmstep,hmp,hmg,hcap,hspace,hheads⟩ :=
    hall w e hlegal (by change 0<Original.numeral _ _; omega)
  obtain ⟨hsrc,hwork,hblank,hhead,hnorm⟩ := endpoint_frame w e
  refine ⟨T,by simpa only [hlen] using hT,hr,halt,r0,r1,?_,?_,?_,hsum,hm0,hmstep,
    by simpa only [hlen] using hmp,by simpa only [hlen] using hmg,
    by simpa only [hlen,hnum] using hcap,by simpa only [hlen] using hspace,
    by simpa only [hlen] using hheads,?_,hwork,hblank,
    by simpa only [hlen] using hhead,hnorm,?_⟩
  · simpa only [hlen] using r2
  · simpa only [hnum] using r3
  · simpa only [hmap] using hpair
  · intro n
    exact (run_source (initial w e) n).trans (by
      funext z
      simp [initial,base,PhysicalWindowContinuation.initial,
        PhysicalWindowContinuation.inputSource,sourceTrack,w,e])
  · intro pre suf hs
    have hg : D5.S3.Arith.ZeckendorfFutureKernel.legal false
        (NativeContinuation.NullReplyFiber.highBits ((pre++suf).map Original.letter)) := by
      rw [hs]
      exact ((D5.S3.Arith.ZeckendorfFutureKernel.legal_append _ _ false).mp hlegal).1
    have hp := source_prefix_registers pre suf e T hg (by simpa only [hs] using hr)
    simpa only [hs,w,e,show (OriginalEncoder.localWord h N).length=h from hlen] using hp

end PhysicalWindowContinuation.CanonicalAcquisition
