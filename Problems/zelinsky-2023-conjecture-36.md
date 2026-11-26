---
slug: zelinsky-2023-conjecture-36
bibkey: zelinsky2023nondeficient
doi: null
url: https://math.colgate.edu/~integers/x13/x13.pdf
triage: theorem
motivation_gids:
  - D5/S3/Arith/Abundancy/ZelinskyFactorialPower.result
---

# Zelinsky's factorial-power Euler product

## Problem

Zelinsky, page 17, Conjecture 36:

> We have lim_{n→∞} H((n!)^n + 1) = 1.

For a positive integer m, the definition on page 3 is

$$
H(m)=\prod_{p\mid m,\ p\text{ prime}}\frac p{p-1},
$$

with each prime counted once. The parameter n ranges over natural numbers.
The Lean target is the limit at infinity of this exact finite product,
evaluated at m=(n!)^n+1, with value one.

## Motivation

The product bounds the abundancy ratio of a positive integer from above.
The conjecture tests whether factorial powers plus one approach the smallest
possible value of that product. It is a named conjecture in a published
paper, the first-tier basis of preregistration #31542.

## Gap

Every prime divisor exceeds n, but that fact alone is insufficient:
the logarithm of (n!)^n+1 has order n² log n, so a prime-counting bound
using only the least prime factor need not make the reciprocal sum vanish.
The missing control comes from the multiplicative order of n! modulo
each prime divisor, which must divide 2n.

## Route

Put a=n!, N=a^n+1, and S=Σ_{p|N}1/p. For n≥2 and p|N,
the inequality p≤n would imply p|a and then p|1. Thus p>n.
In the field modulo p, a^n=−1; its positive multiplicative order d
divides both 2n and p−1.

Fix 0<ε<1/4, and set T=n^ε, Y=n^{1+3ε}, and Z=n³.
Partition the prime divisors into four classes:

1. For n<p≤Y, Mertens' reciprocal-prime estimate bounds the sum by
   log(1+3ε)+o(1).
2. For Y<p≤Z and d≤T, all such primes divide
   Q=∏_{1≤j≤⌊T⌋}(a^j−1). The distinct-prime product divides Q, hence
   their reciprocal sum is at most log Q/(Y log Y).
   Since log Q≤T² log a≤T² n log n, this is at most
   n^{−ε}/(1+3ε).
3. For Y<p≤Z and d>T, use p=1+kd and the harmonic estimate.
   For each d the reciprocal sum is at most (1+log Z)/d.
   Summing over divisors of 2n gives at most
   τ(2n)(1+3 log n)/n^ε, which tends to zero by the divisor subpower bound
   with exponent ε/2.
4. For p>Z, the distinct-prime product divides N. The reciprocal sum is
   at most log N/(Z log Z). The inequalities
   log N≤n² log n+log 2 and Z=n³ show that this tends to zero.

Thus limsup S≤log(1+3ε) for every such ε, so S tends to zero.
For p≥2, the elementary logarithm inequality gives
0≤log(p/(p−1))≤1/(p−1)≤2/p. Consequently
0≤log H(N)≤2S, and continuity of the exponential gives H(N)→1.

## Falsifier

Replacing the distinct-prime product by a product with multiplicities would
change the source definition. The bound p>n alone does not complete the
proof. The order argument requires that a is nonzero modulo p, and the
product-divisibility estimates require nonzero Q and N. The four classes
must cover every prime divisor. A fixed positive ε gives only a positive
upper bound for the limiting reciprocal sum; ε must subsequently be
allowed to approach zero.

## Evidence

**Proved in Lean:** `ZelinskyFactorialPower.result` states exactly
`Tendsto (fun n : ℕ => H (n.factorial ^ n + 1)) atTop (𝓝 1)`.
The definition of H uses all distinct prime factors. The proof bounds
their complete reciprocal sum by the Mertens window plus terms tending
to zero, then bounds the logarithm of H by twice that sum.

The finite estimates use a nonnegative cover, allowing overlaps:
the small-order class may contain primes larger than Z, and the
large-order class may contain primes at most Y. Each enlargement
preserves the required upper bounds.

The literature assessment in preregistration #31542 reports no proof or
refutation in its nyxid-oracle and WebSearch searches. Its repository scope
was D5, Problems, Library, issues, and pull requests; the related result
identified there was Zelinsky–Zhang Conjecture 22, not Conjecture 36.
This is a bounded search conclusion, not a worldwide priority claim.

## Triage

**Proved in Lean through the displayed estimates:**
The useful mechanism is the divisibility d|2n of multiplicative orders,
together with d|p−1. Small orders force many primes into a product of
small powers of a minus one; large orders force sparse arithmetic
progressions. These complementary constraints overcome the insufficient
bound from the least prime factor alone.

**Proved on paper; not formalized in this module:**
Let k(n) be positive integers with k(n)≤n^C eventually, for a fixed C≥0.
The same argument yields H((n!)^{k(n)}±1)→1. Every prime divisor still
exceeds n. Its order divides 2k(n) for the plus sign and k(n) for the
minus sign. Keep T=n^ε and Y=n^{1+3ε}, and replace Z by n^{C+2}.
The small-order estimate is unchanged. The large-order estimate is
bounded by τ(2k(n))(1+(C+2)log n)/n^ε. Choose the divisor-bound exponent
δ=ε/(2(C+1))>0. Then Cδ<ε and τ(2k(n))=O(n^{Cδ}), so this term vanishes.
Finally, log((n!)^{k(n)}+1)≤n^{C+1}log n+log 2, so the far tail
vanishes as well.
For the minus sign, n≥2 and k(n)≥1 ensure positivity; its logarithm has
the same upper bound. This extension is not a Lean claim of the module.

**Proved mathematically from the limit; not separately formalized:**
For every positive integer m,

$$
1\le\frac{\sigma(m)}m
=\prod_{p^v\parallel m}(1+p^{-1}+\cdots+p^{-v})
\le H(m).
$$

Therefore the limit H(N)→1 implies σ(N)/N→1. In particular H(N)<2
eventually, so σ(N)<2N eventually: these integers are eventually deficient.
This conclusion uses an eventual strict bound obtained from convergence,
not an assertion that H(N) equals one at any finite n.

**Proved in the source; unchanged: Theorem 31 (page 16).**
Let g(n) be an increasing positive-integer-valued function such that,
for all sufficiently large n, gcd(p,g(n))=1 for every prime p≤n.
Suppose also that a constant C satisfies g(n)<n^{Cn} for all sufficiently
large n. Then H(g(n))→1. This theorem does not cover g(n)=(n!)^n+1:
log((n!)^n+1)∼n² log n, exceeding Cn log n for every fixed C eventually.
The present result settles this faster-growing sequence without changing
Theorem 31 or proving its conclusion for every function of that size.

On page 16, with h(m)=σ(m)/m, the paper defines
A(n)=h(n!+1), B(n)=h(n!−1), C(n)=H(n!+1), and D(n)=H(n!+1).
The printed definition of D repeats C; H(n!−1) is the suspected intended
definition. The following statements retain the printed definitions;
their unresolved status here means not settled by the present result:

- **Unresolved; unchanged: Conjecture 32.** There are arbitrarily large n
  such that A(n)<A(n+1). The factorial-power limit gives no such comparison.
- **Unresolved; unchanged: Conjecture 33.** There are arbitrarily large n
  such that B(n)<B(n+1). The factorial-power limit gives no such comparison.
- **Unresolved; unchanged: Conjecture 34.** There are arbitrarily large n
  such that C(n)<C(n+1). The factorial-power limit gives no such comparison.
- **Unresolved; unchanged: Conjecture 35.** There are arbitrarily large n
  such that D(n)<D(n+1). This is identical to Conjecture 34 as printed;
  the factorial-power limit settles neither reading of D.

These are assertions of infinitely many strict increases for functions of
n!±1, not the limit assertion for (n!)^n+1. Neither type of assertion
implies the other: a limit does not determine the signs of successive
differences, and these comparisons do not control the factorial-power
sequence. No implication to Conjectures 32–35 is used in the present proof.

**Conditional in the source; unresolved unconditionally:** Page 16 states
that standard prime conjectures imply Conjectures 32–35. Its explicit
example is that n!+1 prime and (n+1)!+1 composite give both
A(n)<A(n+1) and C(n)<C(n+1). Infinitely many factorial-plus-one primes,
together with infinitely many composite values (from Wilson's theorem),
would force infinitely many prime-to-composite transitions. This explains
the plus-case implication; it does not assert that the plus-case prime
conjecture alone settles B or the suspected minus-case definition of D.
The present limit proves none of these prime conjectures.

**Computed in the source; finite evidence only:** A(3)=8/7 and A(4)=31/25,
so A(3)<A(4). This disproves monotone decrease, not Conjecture 32.

**Unresolved; unchanged:** Page 17 asks for the densities of the sets
S_X={n≥1 : X(n)<X(n+1)}, for X=A,B,C,D, and conjectures density 1/2
for S_A. The factorial-power limit settles neither their densities nor
the existence of those densities.

**Proved in the cited work; verified at abstract level:**
P. Kiss and B. M. Phong, *Reciprocal sum of prime divisors of Lucas
numbers*, Acta Academiae Paedagogicae Agriensis, Nova Series,
Tom. 19 (1989), 47–54 ([scan][kiss-phong]). For each fixed nondegenerate
Lucas sequence (u_n), the abstract states

$$
\sum_{p\mid u_n,\ p\text{ prime}}\frac1p
<\log\log\log n+c\qquad(n>n_0),
$$

where c and n_0 depend on the sequence. The abstract identifies this as
a generalization of Erdős's Mersenne result:
Σ_{p|2^n−1}1/p<log log log n+c for all sufficiently large n,
with a constant c.

This fixed-sequence theorem does not imply the present limit. Here the
base a=n! changes with n, so applying a different fixed-sequence theorem
at each n supplies no uniform c or n_0. Moreover, log log log n+c grows
with n; even a uniform bound of this form would not force the reciprocal
sum to zero. The present proof instead combines the growing lower bound
p>n with d|2n, d|p−1, and τ(2n)=n^{o(1)}.

[kiss-phong]: https://library.hungaricana.hu/en/view/EKTFK_tanarkepzo_eszterhazy_19_09/?pg=46

## ASSUMED-UNVERIFIED

Worldwide priority and completeness of subsequent literature remain
unverified. Verification of Kiss–Phong is limited to its bibliographic
identity and abstract-level statement, including its attribution to Erdős;
its proof details have not been checked.
