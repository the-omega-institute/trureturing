# Actual Cloitre Right Fibonacci Profiles

## Abstract

The actual Cloitre sequence has every fixed right Fibonacci profile under its full golden and orbit hypotheses.

F denotes the Fibonacci sequence with F(0)=0 and F(1)=1. G(n) is the natural floor of (n+1) divided by the golden ratio. All indices and offsets are natural numbers; C has positive indices and an exterior zero convention.

**Definition 1.1 (The actual Cloitre sequence).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualRightProfile.C`

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualRightProfile.C` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

C(1)=C(2)=1. For N at least three, form the map x to N-C(x) on the already defined positive prefix, start at N-1, apply it exactly C(N-1) times, and call the selected point g(N). Then C(N)=C(g(N))+C(N-g(N)). The immutable finite-prefix construction keeps every iterate and both children between one and N-1.

**Definition 1.2 (The legal prefix domain).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualRightProfile.D`

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualRightProfile.D` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D(N) is the closed natural interval from one to N-1.

**Definition 1.3 (The actual inner map).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualRightProfile.T`

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualRightProfile.T` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

T(N,x)=N-C(x), with N fixed throughout each orbit.

**Definition 1.4 (The actual orbit).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualRightProfile.X`

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualRightProfile.X` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

X(N,i) is the i-th iterate of T(N) at the prescribed origin N-1.

**Definition 1.5 (The actual depth).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualRightProfile.d`

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualRightProfile.d` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

d(N)=C(N-1); it varies with the actual sequence output.

**Definition 1.6 (The actual selected point).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualRightProfile.g`

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualRightProfile.g` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

g(N)=X(N,d(N)).

**Definition 1.7 (The right Fibonacci collar).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualRightProfile.I`

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualRightProfile.I` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

I(q,t) is the closed natural interval from F(q-1) to F(q-1)+t.

**Definition 1.8 (Entry before the prescribed depth).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualRightProfile.DepthEntry`

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualRightProfile.DepthEntry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There is an earliest time mu at which X(N,mu) is a periodic point of the actual map T(N), and mu is at most d(N). All earlier times are outside Function.periodicPts(T(N)).

**Definition 1.9 (Conditional finite foundations).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualRightProfile.SourceFoundations`

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualRightProfile.SourceFoundations` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For 16384 through 131071, 22877*C(n) is at most 15225*n. For positive n through 65535, G(n) is at most C(n), and equality requires a Fibonacci number or its successor at an index at least two, the predecessor of an odd-index Fibonacci number at an index at least three, or one of 11, 24, 25, 59. DepthEntry holds for N from three through 52. These are conditional premises, not independent finite certificates.

**Definition 1.10 (The complete conditional premise bundle).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualRightProfile.Hyp21_1`

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualRightProfile.Hyp21_1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

SourceFoundations holds. For every positive n, 1<=C(n) and G(n)<=C(n)<=U(n)<=n. U(1)=1. For j at least three and F(j)<=n<F(j+1), U(n)=min(n-F(j-2),F(j)). U is nondecreasing on positive indices and U(n)<=U(n+1)<=U(n)+1. For every j at least two, U(F(j))=C(F(j))=G(F(j))=F(j-1). For every j at least three, G(F(j)+1)=C(F(j)+1)=F(j-1)+1. For every q at least six and every t, I(q,t) lies in D(F(q)+t), is invariant, captures the orbit of every point of that domain, and contains all its periodic points. DepthEntry holds for every N at least three. No monotonicity of C or arbitrary-width seed is assumed.

**Theorem 1.11 (Every fixed right width).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualRightProfile.full21_3`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CloitreActualRightProfile.full21_3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every function U from natural numbers to natural numbers satisfying Hyp21_1, and for all natural t and k with 6*t+6<=k, C(F(k)+t)=F(k-1)+t. The proof uses strong induction on the offset. A positive profile deficit forces the actual selected lower endpoint, a positive deficit two orders below, and an odd actual depth. Three such orders contradict Fibonacci parity. The parity step directly uses GoldenFibDivisibility.fib_dvd_iff at index three. All finite source foundations remain conditional.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualRightProfile.C`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualRightProfile.D`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualRightProfile.DepthEntry`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualRightProfile.Hyp21_1`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualRightProfile.I`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualRightProfile.SourceFoundations`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualRightProfile.T`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualRightProfile.X`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualRightProfile.d`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualRightProfile.full21_3`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualRightProfile.g`
- Dependency: [D5/S1/Phase/SelfReference/GoldenShellRecurrence](../../Phase/SelfReference/GoldenShellRecurrence.md)
- Dependency: [D5/S1/Recurrence/GoldenFibDivisibility](../GoldenFibDivisibility.md)
