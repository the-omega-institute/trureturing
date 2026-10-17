/- GID: D5/S0/Computability/WindowCanonicalPrefixes
   generality: I
   mirror-B: D5/B/S0/Computability/WindowCanonicalPrefixes
   mirror-E: none(waiver:unbounded-operational-correspondence)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   utility: none
   digest: Every original input prefix occurs in the same extended accepting execution. -/

import D5.S0.Computability.WindowAcquisitionFidelity

namespace PhysicalWindowContinuation.CanonicalAcquisition
open D5.S3.Arith.FibonacciAtomic

/-- Every reached nonterminal original state occurs before the paid extension. -/
theorem lift_nonterminal (c : Configuration) (q : ℕ)
    (hq : (PhysicalWindowContinuation.run c q).control ≠ .done) :
    ∀ n ≤ q, run (base c) n = base (PhysicalWindowContinuation.run c n) := by
  apply base_prefix c q
  intro k hk hdone
  have he : PhysicalWindowContinuation.run c q=PhysicalWindowContinuation.run c k := by
    rw [show q=(q-k)+k by omega,PhysicalWindowContinuation.run,Function.iterate_add_apply]
    change PhysicalWindowContinuation.run (PhysicalWindowContinuation.run c k) (q-k)=_
    exact base_done_stutter _ hdone _
  exact hq (by rw [he]; exact hdone)

theorem halt_stutter (c : Config) (hc : program c.control=.halt) (n : ℕ) : run c n=c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run,Function.iterate_succ_apply']
    change step (run c n)=_
    rw [ih]
    simp [step,hc]

/-- At every actual source-prefix boundary the original Horner column and
actual padding-inclusive counter are present in the very same extended run. -/
theorem source_prefix_registers (pre suf : List Window) (e : Bool) (T : ℕ)
    (hg : D5.S3.Arith.ZeckendorfFutureKernel.legal false
      (NativeContinuation.NullReplyFiber.highBits ((pre ++ suf).map Original.letter)))
    (hfinal : run (initial (pre++suf) e) T = registerEnd (pre++suf) e) :
    ∃ q : ℕ, q ≤ T ∧ q ≤ 4+pre.length*(15*(pre++suf).length+46) ∧
      run (initial (pre++suf) e) q =
        base (boundary (inputSource (pre++suf) e) pre.length
          (columnsAfter [zeros] pre) 0 (.source (seamAfter false pre))) ∧
      Original.pair (columnsAfter [zeros] pre) =
        NativeContinuation.JointLaw.composition (pre.map Original.letter) ∧
      valueCount (columnsAfter [zeros] pre) = pre.length ∧
      (columnsAfter [zeros] pre).length ≤ 1+3*pre.length := by
  obtain ⟨q,hq,he,hpair,hcount,hlen,hframe⟩ := Original.source_prefix_registers pre suf e hg
  have hn : (PhysicalWindowContinuation.run (PhysicalWindowContinuation.initial (pre++suf) e) q).control ≠
      .done := by rw [he]; simp [boundary]
  have hrun : run (initial (pre++suf) e) q =
      base (boundary (inputSource (pre++suf) e) pre.length
        (columnsAfter [zeros] pre) 0 (.source (seamAfter false pre))) := by
    change run (base (PhysicalWindowContinuation.initial (pre++suf) e)) q=_
    rw [lift_nonterminal _ q hn q (by rfl),he]
  have hqT : q ≤ T := by
    by_contra hbad
    have hlate : run (initial (pre++suf) e) q = registerEnd (pre++suf) e := by
      rw [show q=(q-T)+T by omega,run,Function.iterate_add_apply]
      change run (run _ T) (q-T)=_
      rw [hfinal]
      exact halt_stutter _ (by rfl) _
    have hcontrol := congrArg Config.control (hrun.symm.trans hlate)
    simp [base,boundary,registerEnd,port,RegisterHandoff.startAt] at hcontrol
  exact ⟨q,hqT,hq,hrun,hpair,hcount,hlen⟩

end PhysicalWindowContinuation.CanonicalAcquisition
