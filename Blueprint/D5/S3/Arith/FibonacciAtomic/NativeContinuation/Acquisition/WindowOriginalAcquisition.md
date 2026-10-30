# Original-input physical acquisition and simultaneous resources

## Abstract

Original-input physical acquisition and simultaneous resources.

For every positive N and every h at least its canonical window count L, only the independently encoded original W at that height and its unit initialize the machine. There is one fixed finite-alphabet eight-track program and two absolute positive constants before all those inputs. No number, height, width or external clock is supplied separately.

One attained run terminates with exact binary registers for both original Horner coordinates, h and N, and with the original composition and matrix column sum. The coordinate growth and strict Fibonacci capacity hold. Every original prefix occurs within that same run with the exact seam, physical counter and Horner column.

The same execution has quadratic local-action time and linear all-prefix persistent charge. The read-only input stays literal at every time; its final head is at the unit position h. The packed tape is retained, all work heads are zero, and unused tracks stay blank. The exact canonical registers have paid copies, trimming, end markers and rewinds.

The zero-window positive case is N=1 with its independent unit. Every extra high null remains an actual input position and a paid counted step. This is acquisition alone: three dependent H calls, including repeated addresses, and six original-height output rows remain separate requirements.

**Theorem 1.1 (original window acquisition).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowOriginalAcquisition.original_window_acquisition`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowOriginalAcquisition.original_window_acquisition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With all declared parameters and hypotheses, the exact statement is: original_window_acquisition : Function.Injective (finiteCode (α := Symbol)) ∧ ∃ A B : ℕ, 0 < A ∧ 0 < B ∧ ∀ (h N : ℕ), 1 ≤ N → OriginalEncoder.L N ≤ h → let w := OriginalEncoder.localWord h N let e := OriginalEncoder.bit N 0 ∃ T : ℕ, T ≤ A*(h+1)^2 ∧ run (initial w e) T = registerEnd w e ∧ program (registerEnd w e).control = .halt ∧ RegisterRep (registerEnd w e) 0 (value1 (Original.finalColumns w e)) ∧ RegisterRep (registerEnd w e) 1 (value2 (Original.finalColumns w e)) ∧ RegisterRep (registerEnd w e) 2 h ∧ RegisterRep (registerEnd w e) 3 N ∧ Original.pair (Original.finalColumns w e) = NativeContinuation.JointLaw.composition (OriginalEncoder.W h N) ∧ Original.pair (Original.finalColumns w e) = Original.columnSum w ∧ Original.maximumColumn [] = 0 ∧ (∀ b, Original.maximumColumn (w ++ [b]) ≤ 5*Original.maximumColumn w+2) ∧ 2*Original.maximumColumn w+1 ≤ 5^h ∧ Original.maximumColumn w ≤ (5^h-1)/2 ∧ N < Nat.fib (3*h+3) ∧ (∀ n ≤ T, charged w e n ≤ B*(h+1)) ∧ (∀ n ≤ T, ∀ t, 0 ≤ (run (initial w e) n).head t ∧ (run (initial w e) n).head t ≤ 3*h+6) ∧ (∀ n, (run (initial w e) n).cell sourceTrack=inputSource w e) ∧ (registerEnd w e).cell workTrack=word (Original.finalColumns w e) ∧ (∀ t : Track,(∀ j : Lane,t ≠ target j) → t ≠ sourceTrack → t ≠ workTrack → (registerEnd w e).cell t=fun _=>.blank) ∧ (∀ t : Track,(registerEnd w e).head t=if t=sourceTrack then h else 0) ∧ (∀ j : Lane,(normalized ((Original.finalColumns w e).map (select j))).length ≤ (Original.finalColumns w e).length+1) ∧ (∀ pre suf : List Window, pre++suf=w → ∃ q : ℕ, q ≤ T ∧ q ≤ 4+pre.length*(15*h+46) ∧ run (initial w e) q = base (boundary (inputSource w e) pre.length (columnsAfter [zeros] pre) 0 (.source (seamAfter false pre))) ∧ Original.pair (columnsAfter [zeros] pre) = NativeContinuation.JointLaw.composition (pre.map Original.letter) ∧ valueCount (columnsAfter [zeros] pre) = pre.length ∧ (columnsAfter [zeros] pre).length ≤ 1+3*pre.length)

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowOriginalAcquisition.original_window_acquisition`
- Dependency: [D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowCanonicalPrefixes](WindowCanonicalPrefixes.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowOriginalEncoder](WindowOriginalEncoder.md)
