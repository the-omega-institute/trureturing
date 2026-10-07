# Actual Fibonacci prefix cut by odd prime kernels

This consumer examines a new partition of the actual raw Möbius–Binet
prefix. It reuses the project's dyadic endpoint identity, classical PNT,
and the existing unconditional Mertens transfer. Its result is a paper
application and four exact finite cut enclosures, with no Lean verification
or originality certification.

Put $q=(3-\sqrt5)/2$, $\beta_d=\log(1-(-q)^d)$, $e=\mu*\beta$, and
$H_{\rm raw}(X)=\sum_{n\le X}e_n$. The unit $e_1=\beta_1$ remains included.
For an odd prime $p\le X$, set $A=\lfloor\log_2(X/p)\rfloor$. The existing
chain formula gives its whole finite contribution as

$$
P_A(p)=\beta_{2^Ap}-\beta_{2^A}.
$$

The cut here is $\mathcal P_q(X)=\sum_{p\le X,\ p\ {\rm odd}}P_{A_X(p)}(p)$.
The word “prime” concerns the odd kernel of the atom index, not prime
divisors of a Robin host integer. The experiment does not calculate
$\sigma(n)/n$, composite-kernel sums, or CA profiles.

## Signed leading terms at the same cutoff

The [theory, §421](../../develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
derives, using existing PNT, the absolutely convergent coefficient

$$
c_q=-\sum_{a\ge0}\frac{\beta_{2^a}}{2^{a+1}},
\qquad
\mathcal P_q(X)=(c_q+o(1))\frac X{\log X}.
$$

Fixed dyadic bands supply weights $2^{-a-1}$; a uniform prime-count bound
handles bands through $\sqrt X$, and double exponential decay handles the
remaining bands. Terminal terms satisfy $2^{A_X(p)}p>X/2$, so their complete
error is exponentially small. This uniform tail argument, rather than the
finite observations below, supplies the asymptotic conclusion.

The remaining cutoff partitions into the unit kernel and odd composite
kernels. The exact common-prefix identity is
$H_{\rm raw}=U_q+\mathcal P_q+\mathcal C_q$. The already established
$H_{\rm raw}=O(X/(\log X)^6)$ and exponentially small $U_q$ therefore give
$\mathcal C_q(X)=(-c_q+o(1))X/\log X$. This is an aggregate compensation on
the same actual array and cutoff, not termwise positivity or an improved
Mertens bound. The finer signed remainder needed for RH remains unresolved.

## Exact coefficient and finite data

The coefficient enclosure certifies $-0.12<c_q<-0.119$; its descriptive
midpoint is about $-0.11960955335978204$. The four normalized cut enclosures
have these descriptive midpoints:

| Cutoff $X$ | Odd primes counted | Midpoint of $\mathcal P_q(X)\log X/X$ |
| --- | --- | --- |
| 1000 | 167 | -0.11392348921619842 |
| 10000 | 1228 | -0.11972453294275753 |
| 100000 | 9591 | -0.11984573438942869 |
| 1000000 | 78497 | -0.11961777241170388 |

Each finite cut has a negative upper endpoint. These observations do not
assert monotone convergence, a threshold for all later cuts, a Robin-safe
integer range, or a full Robin/RH proof.

The source supplier is the computational companion pinned in the
[Mantovanelli note](../../../Library/Analytic/mantovanelli2026primeworkload.md).
The program calls the existing source-local consumer's supplier loader,
which checks SHA-256
e77735e9fd3dac38ca36933c3ac36776c70b0a1fe52d278256f4d7e507f3f58a
before loading the author's original code. It directly uses that code's
primes_up_to, log_interval, Interval and dyadic_enclosure. The MIT-licensed
sieve and rational logarithm implementation are reused, not copied or
rewritten. No CA event enumeration or original root verification runs.

Integer-square-root bounds enclose $q$. The consumer retains $\beta_{2^a}$
for $0\le a\le6$. The positive coefficient tail is bounded by
$q^{128}/[128(1-q^2)]$. For a finite cutoff $X\ge256$, both the omitted
positive even-beta contribution and the absolute terminal error are at
most $\pi_{\rm odd}(X)2^{-128}/(1-q_{\rm upper})$. All retained dyadic
intervals and exact band counts are in [results.json](results.json).
The displayed decimal midpoints are not the certificates.

## Reproduce

Use the existing supplier archive from that note and run from the repository
root:

    python3 docs/reports/fib-prime-kernel-partition/certify_partition.py \
      --archive /path/to/zenodo-archive.zip \
      --output docs/reports/fib-prime-kernel-partition/results.json

The consumer requires Python 3.9 or later. Other cutoff inputs inherit the
arithmetic enclosure method, not the four retained sign conclusions.
