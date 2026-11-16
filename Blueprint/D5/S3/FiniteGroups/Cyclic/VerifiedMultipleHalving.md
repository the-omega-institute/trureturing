# Halving a verified returning exponent

## Abstract

An executable same-element halving loop reaches an odd order quotient and, at even order, preserves the true-order half-power.

Let G be any monoid with decidable equality. The function stripTwos x m tests whether m is positive, m modulo two is zero, and x raised to the natural quotient m/2 is one. If all three tests pass, it calls itself at m/2; otherwise it returns m. The positive branch strictly decreases the natural measure m, so this is a total executable definition, including m equal to zero. Its only inputs are the element and the supplied exponent; the unknown order is not an input. Computability of concrete monoid operations and equality is needed for actual evaluation.

**Theorem 1.1 (Complete halving specification).**

$$\forall G \in \mathit{Typeu},\; [\operatorname{Monoid}\left(G\right)] [\operatorname{DecidableEq}\left(G\right)] \forall x \in G,\; \forall m \in \mathit{Nat},\; 0 < m \Rightarrow \left(x^{m} = 1 \Rightarrow \left(0 < \operatorname{stripTwos}\left(x, m\right) \land \left(\operatorname{Dvd}\left(\operatorname{stripTwos}\left(x, m\right), m\right) \land \left(x^{\operatorname{stripTwos}\left(x, m\right)} = 1 \land \left(\left(\exists k \in \mathit{Nat},\; m = 2^{k} \cdot \operatorname{stripTwos}\left(x, m\right)\right) \land \left(\operatorname{Odd}\left(\operatorname{natDiv}\left(\operatorname{stripTwos}\left(x, m\right), \operatorname{orderOf}\left(x\right)\right)\right) \land \left(\left(\operatorname{Even}\left(\operatorname{orderOf}\left(x\right)\right) \Rightarrow \left(\operatorname{Even}\left(\operatorname{stripTwos}\left(x, m\right)\right) \land x^{\operatorname{natDiv}\left(\operatorname{stripTwos}\left(x, m\right), 2\right)} = x^{\operatorname{natDiv}\left(\operatorname{orderOf}\left(x\right), 2\right)}\right)\right) \land \left(\operatorname{Odd}\left(\operatorname{orderOf}\left(x\right)\right) \Rightarrow \operatorname{Odd}\left(\operatorname{stripTwos}\left(x, m\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Cyclic/VerifiedMultipleHalving.stripTwos_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the display, natDiv is natural-number division and Dvd is natural divisibility. Write M=stripTwos x m and r=orderOf x. The theorem assumes only m positive and x^m=1. It gives M positive, M dividing m, x^M=1, an actual natural k with m=2^k*M, an odd quotient M/r, preservation of the true half-power when r is even, and an odd output when r is odd. A positive returning exponent implies r is positive by the existing order-divisibility theorem. Neither finiteness of the monoid nor cancellation, cyclicity or commutativity is assumed.

Strong induction on the current exponent n proves a simultaneous run invariant: the output is positive, n is a power of two times that output, the output still returns x to one, and the quotient by the order is odd. In the recursive branch n/2 is positive and strictly below n. The recursive equality n/2=2^k*M combines with n=2*(n/2) to give n=2^(k+1)*M. These equalities are used to obtain the stated output divisibility.

In a terminal branch the output is n itself. The existing orderOf_dvd_iff_pow_eq_one gives r dividing n. If n/r were twice some k, then n=2*(r*k), so n is even and x^(n/2)=(x^r)^k=1. With n positive all continuation tests would pass, contradicting termination at that branch. Thus the quotient is odd. This terminal reasoning uses standard order divisibility and parity; it is not an additional order-finding oracle.

Write the odd output quotient as 2*t+1. If r is even, M=r*(2*t+1) is even and natural division gives M/2=r*t+r/2. Power addition and x^r=1 therefore give x^(M/2)=x^(r/2). If r is odd, the same product expression makes M odd. All powers belong to the same element, so these identities need no exchange of distinct monoid factors.

For the modular application use G=ZMod N, x equal to the residue of the original natural base a, and a positive exponent m passing Nat.powMod a m N=1, with N at least two. Nat.powMod_def, Nat.cast_pow and the residue equality convert that test to x^m=1. The loop continues to use the same base. For N=21 and a=2, input 12 returns 6, whereas input 132 returns 66. The true order is 6 in both cases; the corresponding terminal half-powers are both the residue 8. The output 66 has odd quotient 11 by the order, so the theorem does not promise exact-order recovery. Before reduction, the passing exponent 12 has half-power one, illustrating why a raw order multiple cannot simply replace the true order in half-power factor extraction.

Odd order supplies no even half-power route: for N=2 and a=1 the input 8 returns 1. An even terminal output need not give a nontrivial factor either: for N=15 and a=14, input 2 remains 2 and its half-power is -1; the two gcds are 1 and 15. Proper factors still require the separate true-order Good condition. The zero input is defined but excluded from the correctness premise, since every element satisfies x^0=1, including elements of infinite order.

The construction uses the pinned Mathlib orderOf and natural parity APIs. The terminal odd-quotient fact also appears as div_orderOf_odd_of_pow_ne_one in SymbolicQuantum/Shor/ReductionLemmas.lean; no novelty of that group-theoretic fact is asserted. Ekerå, On completely factoring any integer efficiently in a single run of an order finding algorithm, Section 3.2 (https://arxiv.org/html/2007.10044), instead uses newly sampled bases and a squaring chain. That distinct algorithm supplies no sampling or complexity assumption here. This specification proves deterministic loop correctness, not efficient acquisition of the original returning exponent, exact order, a probability bound, a factorization algorithm or a bit or gate cost.

## References

- Truth anchor: `D5/S3/FiniteGroups/Cyclic/VerifiedMultipleHalving.stripTwos_correct`
