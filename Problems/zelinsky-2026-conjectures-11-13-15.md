---
slug: zelinsky-2026-conjectures-11-13-15
bibkey: zelinsky2026smallcomponent
doi: 10.48550/arXiv.2005.12115
url: https://arxiv.org/abs/2005.12115v5
triage: theorem
motivation_gids:
  - D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture11.result
  - D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture13.result
  - D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture15.result
---

# The component condition has relative density one in primitive non-deficient families

## Problem

Joshua Zelinsky, *Must a Primitive Non-Deficient Number Always Have a Small
Component?*, Journal of Integer Sequences 29 (2026), Article 26.4.3,
arXiv:2005.12115v5, section 3, pages 9–10, defines B by

$$
B=\{n\ge2:p^{v_p(n)+1}<2\operatorname{rad}(n)
                 \text{ for every prime }p\mid n\}.
$$

C is the set of primitive non-deficient integers: sigma(n)≥2n, while
sigma(d)<2d for each positive proper divisor d of n. C_O is its odd
subfamily. For a set M of primes, C_M consists of members of C divisible
by no prime in M. The source writes S(x)=|{n∈S:n≤x}| and states:

> Conjecture 11. lim (B ∩ C)(x)/C(x) = 0.

> Conjecture 13. lim (B ∩ C_O)(x)/C_O(x) = 0.

> Conjecture 15. Let M be a non-empty finite set of primes. Then lim (B ∩ C_M)(x)/C_M(x) = 0.

The formal claims use inclusive natural bounds X and positive counts.
Every strict component inequality, each family's denominator, and the
universal quantifier over nonempty finite prime sets in Conjecture 15
are retained. In fact, each displayed ratio tends to one.

## Motivation

These conjectures ask whether the component condition is rare within
primitive non-deficient numbers, rather than within all positive integers.
A density-zero numerator among all integers does not answer this question:
its denominator also has density zero. The relevant comparison is between
the exceptional count C\B and the count of the same primitive family.

## Gap

An exceptional-set upper bound must be smaller than an independently
established lower bound for C, C_O and each C_M. Equal exponents do not
suffice. The required lower bound must count actual distinct integers,
retain primitivity and avoid the prescribed primes. Separate existence
statements or a count for a larger family cannot supply that bound.

## Route

Write h(n)=sigma(n)/n. For a deficient squarefree prime product m, put
alpha=h(m)/(2-h(m)). A minimal finite prime product crossing h=2 supplies
a starting core. Adjoining a prime p in (2alpha,3alpha] preserves
deficiency and changes the parameter to

$$
\alpha'=\frac{\alpha(p+1)}{p-\alpha},\qquad
\frac32\alpha\le\alpha'\le3\alpha.
$$

Consequently the core can satisfy exp(t)≤alpha≤3exp(t), with all its
prime factors above a prescribed cutoff and below 2alpha, and with
log(m)≤Ct² for a fixed C. Choose k distinct primes in
((k−1)(alpha+1),k alpha]. Strict Bernoulli gives an abundant product
n=m product(p). Removing any selected prime gives a deficient integer;
removing a core prime decreases the ratio further. Every proper divisor
divides one of these deficient products, proving primitivity.

The quantitative prime number theorem supplies at least
alpha/(4 log(k alpha)) primes in this window. Unique factorization makes
distinct k-element subsets produce distinct integers. Put
D=1000(|C|+1), a=99D/100, t=sqrt(log(X)/D), k=floor(a t).
The inequalities C+a<D and 79D/80<a give the simultaneous size and count
bounds. Thus, for every finite prime set M, eventually

$$
X^{79/80}\le
\#\{1\le n\le X:n\text{ odd, squarefree, in }C_M\}.
$$

For the exceptions, first count to X=M^40 with M≥100. Removing n≤M^39
and integers with a square divisor b² for b>M costs at most 3M^39.
Write each remaining n as b²u with u squarefree and b≤M. Failure of B
forces a prime factor above M^18. Splitting off the part shared with b
leaves a squarefree unitary part. Its small-prime portion must be large:
otherwise deficiency of the complementary proper divisor and

$$
\left(1-\sum_{p\in V}\frac1p\right)
       \prod_{p\in V}\left(1+\frac1p\right)\le1
$$

contradict non-deficiency. A finite packing argument then selects a
squarefree unitary divisor d with M≤d≤M^8. The map n↦n/d is injective
on these exceptions. Primitivity and the large prime confine h(n) to an
interval narrower than the gap between distinct fractions with these
denominators; equality of the fractions and squarefreeness force equality
of d. This contributes at most M^39 more integers. Replacing M by
ceil(X^(1/40))+100 gives

$$
(C\setminus B)(X)\le K X^{39/40}.
$$

For any S⊆C with S(X)≥X^(79/80) eventually, the same exceptional bound gives

$$
0\le1-\frac{(B\cap S)(X)}{S(X)}
\le KX^{39/40-79/80}=KX^{-1/80}\longrightarrow0.
$$

The denominator is positive eventually. Take S=C, C_O and C_M.
Uniqueness of limits refutes each source claim separately. The threshold
for the lower bound may depend on M; no uniformity over all M is required.

## Falsifier

Replacing the denominator by B(X) gives different conjectures.
The finite prime set in the lower bound and in C_M must be identical.
An exceptional estimate O(X^(39/40)) and a lower bound X^(39/40)
would not establish a vanishing quotient. Divisors selected for
compression must be unitary as well as squarefree. All simultaneous
bounds must refer to the same integers and the same parameter X.
Numerical trends cannot prove any of the asserted limits.

## Evidence

The exact claims and their literal negations are
`ZelinskyRadicalComponentConjecture11.claim` and `.result`,
`ZelinskyRadicalComponentConjecture13.claim` and `.result`, and
`ZelinskyRadicalComponentConjecture15.claim` and `.result` in
`D5/S3/Arith/Abundancy/`. Their shared `OpenProblemResolutionClaim`
is **Refuted**. The external problem is preregistered in #31919.

`ZelinskyZhangKLPrimitive.rough_deficient_core` supplies the cores.
`ZelinskyZhangDoublePrimitive.rough_primitive_lower_bound` gives the
odd squarefree counting bound, including empty M.
`ZelinskyRadicalComponentConjecture11.exceptional_bound` bounds C\B,
and `.relative_density_one` proves the comparison for any suitable
subfamily S of C.

Bounded literature assessment supplied with the problem: the journal
version and arXiv v5 still list Conjectures 11, 13 and 15 as conjectures.
Avidon (1996), Lichtman (2018), and Pollack–Pomerance (2016) study counts
of primitive non-deficient integers and large prime factors; those
results do not impose B's component condition. Lichtman's Lemma 2.2
provides the squarefree-divisor compression method. No earlier dossier
for these three denominator-C-family statements occurs in the repository;
the separate radical-component-density dossier treats Conjectures 10,
12 and 14. This bounded assessment does not establish worldwide priority.

## Triage

### What the settlement shows

- **Proved:** the mechanism already holds for every squarefree member
  of C. If n=pm is squarefree and p²≥2n, then p≥2m. Primitivity gives
  sigma(m)≤2m−1, and multiplicativity gives
  sigma(n)≤(p+1)(2m−1)<2pm, a contradiction. Thus squarefree C lies in B.
  This is an elementary consequence of
  `ZelinskyZhangDoublePrimitive.PrimitiveNonDeficient` and
  `ZelinskyZhangKLPrimitive.sig_prime_mul`; no separate classification
  of all squarefree primitive integers is needed.
- **Proved:** `ZelinskyRadicalComponentConjecture11.exceptional_bound`
  gives a power saving for C\B, while
  `ZelinskyZhangDoublePrimitive.rough_primitive_lower_bound` gives a
  near-linear lower bound for every C_M, even after retaining only odd
  squarefree members.
- **Proved:** `ZelinskyRadicalComponentConjecture11.relative_density_one`
  gives the nearest surviving statements: all three proposed zero limits
  become one. The three `.result` declarations refute the respective
  source conjectures.
- **Computed:** exact integer divisor-sum sieves give the following
  inclusive counts and ratios. The computation uses Python 3.12
  (`python3.12`): sieve sigma(n), test sigma(n)≥2n and
  sigma(n/p)<2n/p for every prime p dividing n, then test each strict
  inequality p^(v_p(n)+1)<2rad(n). A second divisor-sum and
  proper-multiple sieve independently verifies the odd count at 10^6.

  | X | C(X) | (B∩C)(X) | C_O(X) | (B∩C_O)(X) | (B∩C)/C | (B∩C_O)/C_O |
  |---:|---:|---:|---:|---:|---:|---:|
  | 10^4 | 102 | 70 | 18 | 17 | 0.686 | 0.944 |
  | 10^5 | 445 | 347 | 88 | 86 | 0.780 | 0.977 |
  | 10^6 | 1738 | 1432 | 324 | 318 | 0.824 | 0.981 |
  | 3×10^6 | 3406 | 2846 | 557 | 551 | 0.836 | 0.989 |

- **Proved (comparison):** #31907 concerns denominators B(X).
  `ZelinskyRadicalComponentDensity.result` gives B(X)/X→1−log2>0,
  while `ZelinskyRadicalComponentConjectures.primitive_density_zero`
  gives C(X)/X→0. Consequently Conjectures 10, 12 and 14 have limit
  zero, consistently with the limit one for the different denominators
  here. No theorem settled in that dossier is invalidated.
- **Open:** a sharper exceptional-set exponent. Pollack–Pomerance's
  x^(11/12) bound motivates a stronger comparison, but that exponent
  has not been proved here for C\B.
- **Open:** the asymptotic behaviour of C_O(X)/C(X). The common lower
  bounds and density-zero statements do not determine this ratio.

## ASSUMED-UNVERIFIED

The bounded literature assessment above is supplied rather than a fresh
online verification. Worldwide priority, exhaustive later literature
coverage, and the applicability of sharper published estimates to the
specific set C\B remain unverified. Finite sieve values are explanatory
results and are not inputs to the Lean proofs.
