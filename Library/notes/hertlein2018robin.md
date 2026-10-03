---
bibkey: hertlein2018robin
authors: Alexander Hertlein
year: 2018
title: Robin's inequality for new families of integers
doi: null
url: https://arxiv.org/pdf/1612.05186v2
claim: An explicit totient-ratio upper bound and a verified finite interval give a joint sufficient condition on several prime valuations.
strata_touched: []
license: citation-only
triage: anchor
---

# Robin's inequality for new families of integers

The [published paper](https://math.colgate.edu/~integers/s71/s71.pdf) is
Alexander Hertlein, *Integers* 18 (2018), A71. The
[author version v2](https://arxiv.org/pdf/1612.05186v2), Lemmas 1–3, pp. 2–4,
is the source inspected for the formulas below.

Put $Z(n)=\sigma(n)/n$ and $B(n)=e^\gamma\log\log n$.
Lemma 2 states the unconditional strict bound

$$
\frac n{\varphi(n)}<\frac{1771561}{1771560}B(n)
\quad\text{for }n>c_0:=\exp(\exp(23.762143)).
$$

Lemma 3 states Robin's inequality for $5040<n\le10^{10^{10}}$.
The ranges overlap because
$\log\log(10^{10^{10}})>23.8598>23.762143$.
The first bound uses Hertlein's explicit computation based on the algorithm
of Akbary, Friggstad and Juricevic; the finite range uses Briggs and Robin's
interpolation between colossally abundant numbers. These published analytic
and computational inputs have not been re-executed or formalized here.

## Joint use of the local factors

Choose a finite set $P$ of primes that actually divide $n>5040$ and upper
bounds $1\le v_p(n)\le a_p$. Define

$$
\eta_P(a)=\prod_{p\in P}(1-p^{-(a_p+1)}),\qquad
T=\frac{1771560}{1771561}.
$$

If $\eta_P(a)\le T$, the published results imply strict Robin for $n$.
Indeed, for $n>c_0$, Lemma 1 and monotonicity in the exponents give

$$
Z(n)=\frac n{\varphi(n)}
\prod_{p\mid n}(1-p^{-(v_p(n)+1)})
\le\eta_P(a)\frac n{\varphi(n)}
<\eta_P(a)T^{-1}B(n)\le B(n).
$$

For $5040<n\le c_0$, Lemma 3 applies. Equality in the rational condition is
allowed because the totient bound is strict. An absent prime cannot be
inserted as an extra factor in this argument. The paper's proofs of
Theorems 1–2 retain one local factor; retaining several factors is their
direct joint application, with no claim of a new analytic theorem.

## The exact five-direction core and its remaining boundary

For the exact core

$$
M=2^{21}3^{13}5^97^711^6,
\qquad
\eta_M=\frac{72365886696479164830959537}
{72365942756627122680000000},
$$

the exact comparison is

$$
1-T^{-1}\eta_M
=\frac{15211459847969040463}{72365901907939012800000000}>0.
$$

Consequently the literature already covers every $n=Mt$ whose remaining
prime factors exceed 11, without a bound on their number or exponents.
The finite support calculations in the FIB report are weaker certificates
for this family; they do not extend the known Robin verification range.
This statement requires the displayed core valuations to remain exact.
For $C=M\cdot2310$, all five valuations increase by one and

$$
T^{-1}\eta_C-1
=\frac{938607291436754075743}{2882283433033132800000000000}>0.
$$

This failure is a limit of the sufficient condition, not a counterexample.

The accompanying [exact program](../../docs/reports/fib-robin-boundary/valuation_slices.py)
classifies the entire exponent orthant above $(21,13,9,7,6)$, in prime order
$(2,3,5,7,11)$. Its caps $(25,15,11,9,7)$ have a precise meaning: the last
bin in coordinate $p$ contains every exponent $a_p$ at least its cap $c_p$.
On that bin the local factor lies in $[1-p^{-(c_p+1)},1]$.
For smaller exponents the factor is exact. Multiplication gives a rational
lower and upper bound for every bin, including its unbounded part.

All 270 bins are decided: 17 have product upper bound at most $T$; 253 have
product lower bound greater than $T$; none straddles the threshold.
Thus the finite computation classifies this entire unbounded exponent
orthant for this particular sufficient condition. The 12 minimal vectors
outside the condition are

```text
(21,13, 9,9,7)  (21,13,10,8,6)  (21,14, 9,8,6)
(21,14,10,7,6)  (21,15, 9,7,7)  (22,13, 9,8,6)
(22,13,10,7,7)  (22,13,11,7,6)  (22,14, 9,7,6)
(23,13, 9,7,7)  (23,13,10,7,6)  (25,13, 9,7,6)
```

The product is increasing in each exponent. Every profile outside the
condition dominates one of these vectors; decreasing any available
coordinate of one of these vectors returns to the condition. In combination
with the five separate valuation stopping rules, any hypothetical
Robin counterexample must therefore be divisible by at least one of the
12 corresponding prime-power cores. This is a union of divisibility regions,
not their intersection, and membership is only necessary.

Equivalently, with

$$
\mathcal A=\{6,14,15,16,20,21,35,44,50,99,110,539\},
$$

a hypothetical counterexample must satisfy $Mr\mid n$ for some
$r\in\mathcal A$. These multipliers are obtained by subtracting the lower
corner from each minimal exponent vector and taking the corresponding prime
product. They form a divisibility antichain.

The lower corner uses Hertlein's Theorem 2 for the primes 3, 7 and 11, and
Christian Axler, *On Robin's inequality*, The Ramanujan Journal 61 (2023),
909–919, [Theorem 3](https://doi.org/10.1007/s11139-022-00683-0), for 2 and 5.
These are the five literature conditions already recorded in §86 of
[the FIB theory volume](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md).

For an authenticated standard Fibonacci source $n=5040F_j$, $j\ge3$, this
also gives a smaller source-index search region without constructing $F_j$.
The rank and lifting formulas cited in §95 of that volume give

$$
D=2^{15}3^{10}5^87^511^5,
\qquad j=Dk
\Longrightarrow
\bigl(v_2(n),v_3(n),v_5(n),v_7(n),v_{11}(n)\bigr)
=(21,13,9,7,6)+\bigl(v_2(k),v_3(k),v_5(k),v_7(k),v_{11}(k)\bigr).
$$

Thus any counterexample in this particular source family must satisfy
$Dr\mid j$ for some $r\in\mathcal A$. If $D\nmid j$, a separate valuation
stop already applies. This transport uses the actual source equality and
the cited Fibonacci valuation formulas; a claimed index label alone is
insufficient. Other published prime directions can still certify integers
within these 12 index regions.

The result supplies a joint prime-resolution test for a common integer
source. FIB window addresses may be used to compute its modular data, but
the geometric interval lengths are not the weights in this Euler product.
The unbounded tails already included in the bins do not settle the 12
remaining regions, where this particular local-factor criterion fails.

This note records an application of existing literature and an exact rational
classification, not a new RH criterion or a new Lean proof. The retained
[result](../../docs/reports/fib-robin-boundary/valuation_slices.json) identifies
the program bytes and the explicit parameters; `outside` never means that
Robin's inequality itself fails.
