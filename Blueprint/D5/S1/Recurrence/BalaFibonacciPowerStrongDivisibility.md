# Fibonacci Power Strong Divisibility

## Abstract

Fibonacci minus one at powers of any positive odd base is a strong divisibility sequence.

Write F for the Fibonacci sequence with F(0)=0 and F(1)=1, and a(t)=F(t)-1 for positive t. All indices and the base k are natural numbers. Odd k implies k is positive. The gcd is the nonnegative greatest common divisor, and subtraction in the formal statement is natural subtraction. Every k^r is positive, so F(k^r) is at least one and that subtraction agrees with integer subtraction. The case k=1 gives zero on both sides.

**Theorem 1.1 (Strong divisibility at odd-base powers).**

$$\forall k \in \mathbb{N}, n \in \mathbb{N}, m \in \mathbb{N},\; \left(\operatorname{Odd}\left(k\right) \land \left(0 < n \land 0 < m\right)\right) \Rightarrow \operatorname{gcd}\left(\operatorname{F}\left(k^{n}\right) - 1, \operatorname{F}\left(k^{m}\right) - 1\right) = \operatorname{F}\left(k^{\operatorname{gcd}\left(n, m\right)}\right) - 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/BalaFibonacciPowerStrongDivisibility.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a000071-bala-strong-divisibility` (proved) by `D5/S1/Recurrence/BalaFibonacciPowerStrongDivisibility.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a000071-bala-strong-divisibility","declaration_gid":"D5/S1/Recurrence/BalaFibonacciPowerStrongDivisibility.result","resolution_kind":"proved"} -->

*Citation.* Peter Bala (2022). *OEIS A000071: Bala's strong divisibility conjecture for Fibonacci minus one at odd-base powers*. URL: <https://oeis.org/A000071>.

*Commentary.*

The statement is the cited conjecture; the following proof is a repository derivation. For a prime p and e>0, work over ZMod(p^e) with Q=[[1,1],[1,0]]. The frozen Lucas recurrence identifies its lower-left entry at power t with F(t). The frozen companion-power shape and determinant give, for odd t and F(t)=1, the matrix [[x+1,1],[1,x]] and x(x+1)=0, where x=F(t+1)-1.

Take the natural representative a of x. The prime power divides a(a+1). If p divides a, it does not divide a+1, so coprimality puts the entire prime power in a. Otherwise it goes into a+1. Thus x=0 or x=-1, giving Q^t=Q or Q^t=Q inverse. Conversely, either equality gives F(t)=1 by the lower-left entry. This equivalence includes p=2 and p=5 and uses no division by either prime.

On sets of matrix units, let T send a set to its image under g↦g^k and let S={Q,Q inverse}. Mathlib's power iteration and set-image iteration identities show that T iterated r times returns S exactly when Q^(k^r) is Q or Q inverse. The pair argument allows coinciding elements. The preceding equivalence therefore identifies these return times with p^e dividing F(k^r)-1.

The existing periodic-point gcd theorem proves the forward divisibility; preservation under multiples proves the reverse one. The prime-power divisibility criterion reconstructs divisibility of natural numbers in both directions. Exponent e=0 contributes only the divisor one. All auxiliary assertions occur inside the single public result and supply no extra formal premise.

## References

- Truth anchor: `D5/S1/Recurrence/BalaFibonacciPowerStrongDivisibility.result`
- Dependency: [D5/S1/Recurrence/LucasCompanion](LucasCompanion.md)
