---
slug: joshi-rust-2025-thue-morse-first-longest-start
bibkey: joshirust2025monochromatic
doi: 10.1016/j.tcs.2025.115391
url: https://arxiv.org/html/2501.05830v2
triage: theorem
motivation_gids:
  - D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd
---

# First longest Thue-Morse progressions at power-of-two differences

## Problem

Joshi and Rust, *Monochromatic arithmetic progressions in the Fibonacci,
Thue-Morse, and Rudin-Shapiro words*, Theoretical Computer Science 1050
(2025), 115391, arXiv:2501.05830v2, Section 3.2.2, Conjecture 3.8:

> We have i(2^n+1)=3·2^(2n)-2^n-1,
> i(2^(2n)-1)=3·2^(4n)-2^(2n)+1,
> i(2^(2n+1)-1)=2^(2n+1)-1.

The display omits ranges. The contextual interpretation, from the preceding
maximum-length formulas, is `n>=2` in the first equation and `n>=1` in the
other two. Equivalently, for every natural `e>=2`, with `q=2^e`,
`i(q+1)=3q^2-q-1`, `i(q-1)=3q^2-q+1` for even `e`, and
`i(q-1)=q-1` for odd `e`. This range is an explicitly disclosed
interpretation, not a printed quantifier. The previously known `i(3)=45`
excludes the plus-family extension to `e=1`; it is not a new refutation.

The word is the zero-indexed Thue-Morse word `0110100110010110...`, with
`t(0)=0`, `t(2u)=t(u)` and `t(2u+1)=1-t(u)`. Definitions 2.2, 2.3 and
2.5 make `A(d)` the global maximum length over every nonnegative start
and either letter, and `i(d)` the least start attaining it.

## Motivation

This 2025 specialist conjecture concerns three unbounded families. The
source explains that its Walnut method cannot handle the variable product
needed when the maximum length varies with the difference. The existing
ThueMorseReducedAbelianOdd module supplies the actual binary digit-parity
word and its binary identities.

## Gap

A progression at the proposed start alone does not establish maximality
or firstness. The statement requires positive attainment, a bound on all
lengths at all starts for either letter, and exclusion of every earlier
start. The exceptional half-block possibilities at exponent two also
require treatment.

## Route

Write each start as `aq+b`, `0<=b<q`. Binary block parity and complementary
residues express progression letters through carries or borrows. Block
recognition forces any length `q+2` progression at difference `q+1` to
satisfy `s+q+1=kq^2`, `k>=3`, with an opposite next letter. For even `e`,
a length `q+4` progression at difference `q-1` satisfies
`s+q=kq^2+1`, `k>=3`, again with an opposite next letter. The explicit
starts with `k=3` attain those lengths.

For odd `e`, putting `b=s mod q` gives opposite letters at progression
indices `b` and `b+1`. This bounds every length by `q`; the start `q-1`
attains `q`. For `s<q-1`, both opposite letters lie within that length,
excluding an earlier maximum. Aedo, Grimm, Nagai and Staynova's known
recognition and maxima are prerequisites, not additional new results.

## Falsifier

A natural `e>=2` whose first attaining start differs from any applicable
formula refutes the contextual conjunction. An earlier run of either
letter attaining the stated maximum, a longer run at any start, or a
mismatch with the actual zero-indexed word would invalidate the claimed
source correspondence.

## Evidence

- Formal source: `D5/S1/Words/ThueMorseMapFirstStart.lean`.
- Public declarations: `MAP`, `FirstLongest`, `claim`, and `result : claim`.
- `FirstLongest(d,s)` is `exists L>0, MAP(d,s,L)` together with
  `forall a N, MAP(d,a,N) -> N<=L` and
  `forall a<s, not MAP(d,a,L)`.
- The source proves the full conjunction for every `e>=2`, using maximum
  lengths `q+2`, `q+4`, and `q` in the respective branches.
- The result's axiom closure is `propext`, `Classical.choice`, `Quot.sound`.
- Exact source: https://arxiv.org/html/2501.05830v2#S3.Thmtheorem8.
- Preregistered target and bounded literature audit:
  https://github.com/the-omega-institute/trureturing/issues/13307.

## Triage

`theorem`. The source result establishes the contextual conjunction through
attainment, global maximality and least-start exclusion. The binary
carry/borrow and block-recognition mechanism supplies all-start exclusions;
the known maximum formulas are recovered within that argument. The source
does not assert a classification of all maximizing starts as a separate
public theorem. Other Thue-Morse questions in Joshi and Rust, including
Question 3.7, remain unresolved by this result.

## ASSUMED-UNVERIFIED

The preregistration's bounded audit on 5 October 2026 found no identified
exact resolution in the checked adjacent literature, OEIS A342827, arXiv
and OpenAlex searches, formal-conjectures, and repository ownership checks.
The unavailable thesis and unreadable search/index results supplied no
negative evidence. Coverage and freshness are bounded; worldwide priority
is unverified. The parameter range is the contextual interpretation
explained above.
