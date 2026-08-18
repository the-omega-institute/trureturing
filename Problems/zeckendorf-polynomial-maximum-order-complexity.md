---
slug: zeckendorf-polynomial-maximum-order-complexity
bibkey: jametpopolistoll2021maximum
arxiv_id: 2106.09959
triage: window
motivation_gids:
  - D5/S0/Conventions/WDigits
  - D5/S1/Digit/Raw
  - D5/S1/Digit/Carry
  - D5/S1/Digit/Normalize
  - D5/S1/Scale/Fibonacci
  - D5/S1/Words/GoldenSubstFixed
  - D5/S1/Words/Complexity/MorseHedlund
  - D5/S1/Words/Complexity/MechanicalComplexityCharacterization
---

# Maximum order complexity along polynomial Zeckendorf subsequences

## Problem

Let `s_Z(n)` be the sum of the digits in the Zeckendorf representation, and set
`S_Z = (s_Z(n) mod 2)` for `n >= 0` and `S_{Z,P} = (s_Z(P(n)) mod 2)` for
`n >= 0`. For a binary sequence `S`, `M(S,N)` is the least feedback-register
length needed to generate its first `N` values, as defined in the paper.

Conjecture 3, quoted from arXiv:2106.09959v1:

> “The sequence \(\mathcal S_Z\) along polynomial subsequences, denoted by
> \(\mathcal S_{Z,P}\) for a polynomial \(P\) of degree \(d\geq2\),
> verifies \(M(\mathcal S_{Z,P},N)\asymp N^{1/(2d)}\), i.e. there are
> \(c,C>0\) such as for all \(N\) large enough we have
> \(cN^{1/(2d)}\leq M(\mathcal S_{Z,P},N)\leq CN^{1/(2d)}\).”

The paper has already proved the matching lower bound for monic `P` in `Z[X]` of
degree `d >= 2` with `P(N_0)` contained in `N_0`; the new mathematical content is
the upper bound. A safe first formal target is the concrete case `P(X) = X^2`:

```text
∃ C > 0, ∃ N0, ∀ N ≥ N0,
  maximumOrderComplexity (fun n => zeckendorfDigitSum (n^2) % 2) N ≤ C * N^(1/4)
```

The real-valued bound must be encoded with explicit ceilings and floors.

The paper states the difficulty:

> “The maximum order complexity of \(\mathcal S_\varphi\) is algorithmically
> more difficult to handle.”

> “With our program and our machine, it is not possible to compute the maximum
> order complexity of a sequence any further than \(10^9\) terms.”

The authors say the square plot supports the conjecture but the cube plot does
not clarify it; proving the conjecture would show their lower bound is sharp.

## Motivation

- `WDigits` already gives the exact canonical digit set, so `s_Z` is a finite
  cardinality/sum on a frozen object rather than a new numeral system.
- `Carry` and `Normalize` give a local, terminating way to study how polynomial
  increments change digits; any upper bound must control how far those carries
  propagate.
- The frozen word-complexity layer supplies definitions and techniques for
  repeated factors, but maximum order complexity is a different invariant. The
  needed bridge is the collision criterion: every repeated length-`M` block in
  the first `N` positions must have the same successor bit.
- The exponent `1/(2d)` suggests a two-sided noninterference window for
  polynomial values; this matches the paper's explanation that Lucas expansions
  around a center affect both sides.

## Gap

- No `zeckendorfDigitSum mod 2` sequence is declared.
- No maximum-order-complexity, feedback-register, or DAWG API exists.
- Frozen factor complexity does not imply the required successor determinism.
- There is no quantitative carry-propagation theorem for `P(n+h) - P(n)` at
  polynomial scale.

## Route

1. Define `s_Z` directly from `wdigits`; prove compatibility with the raw-digit
   normalizer.
2. Replace the existential feedback-polynomial definition by the equivalent
   repeated-block criterion used by maximum order complexity: two equal
   length-`M` blocks before `N` must have equal next bit.
3. For `P = X^2`, decompose `(n+h)^2 - n^2 = 2nh + h^2` into separated
   Fibonacci/Lucas blocks. Use normalization to isolate a bounded carry zone
   around each block.
4. Show that an `M`-bit history with `M = O(N^(1/4))` determines the relevant
   boundary state of the carry automaton, hence determines the next parity bit.
5. Generalize the separation lemma to degree `d`; the already-proved paper lower
   bound can remain an external target until formalized.

## Falsifier

The asymptotic claim has no single finite falsifier because `c`, `C`, and `N0`
are existential. A proposed effective upper bound `M <= C ceil(N^(1/(2d)))` is
falsified by an exact `N` above its stated threshold where the inequality fails.

The key successor-determinism lemma is sharply falsifiable: find `i < j` with
identical length-`M` blocks of `S_{Z,P}` but different following bits. Every
computational certificate should emit this pair, not only a complexity value.

## Evidence

Build two independent exact implementations of `M(S,N)`: naive repeated-block
checking for small `N`, and a suffix-array or DAWG method for larger `N`. For
`P = X^2` and `P = X^3`:

1. compute `s_Z(P(n)) mod 2` from exact greedy WDigits;
2. cross-check the two complexity implementations through at least `N = 10^6`;
3. sample at Fibonacci-scale `N` and record `M/N^(1/(2d))`, local log-log
   slopes, and witness pairs causing every step increase;
4. separately measure the maximum changed digit index under
   `P(n) -> P(n+1)` to test the proposed carry-window lemma.

The result must not be reported as proof of an asymptotic exponent.

## Triage

`window`. The lower bound and numerical shape are known, and the repository can
formalize exact finite complexity and carry behavior; the uniform upper bound
needs a new quantitative noninterference theorem.

## ASSUMED-UNVERIFIED

- Conjecture 3 inherits the earlier monic/integer/nonnegative scope for `P`; the
  quoted conjecture itself abbreviates that context.
- The repeated-block characterization will be the most useful formal definition
  for the chosen edge cases of `M(S,N)`.
- Carry propagation admits a uniform state bound of the conjectured scale.
- Whether the conjecture was resolved after arXiv v1 is unverified; novelty of
  any proposed carry lemma is unassessed.
