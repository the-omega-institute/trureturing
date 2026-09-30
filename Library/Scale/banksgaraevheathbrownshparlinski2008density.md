---
bibkey: banksgaraevheathbrownshparlinski2008density
authors: W. D. Banks, M. Z. Garaev, D. R. Heath-Brown, and I. E. Shparlinski
year: 2008
title: Density of non-residues in Burgess-type intervals and applications
doi: 10.1112/blms/bdm111
url: https://arxiv.org/pdf/math/0607692v3
claim: The proof of Theorem 2.1 gives fixed positive reciprocal-prime weight at a Burgess-type cutoff for prime moduli, but that weight includes the prime two and does not automatically survive the actual FIB exceptions.
strata_touched: []
license: citation-only
triage: anchor
---

# Prime-conductor weights with the low-end exceptions retained

The article appeared in *Bulletin of the London Mathematical Society*
40 (2008), 88–96, [DOI:10.1112/blms/bdm111](https://doi.org/10.1112/blms/bdm111).
The inspected source is [arXiv:math/0607692v3](https://arxiv.org/abs/math/0607692v3),
dated 25 September 2007. The following bound is an explicit intermediate
conclusion in §3.1, printed pp.4–5, in the proof of Theorem 2.1; the main
theorem concerns the density of integer nonresidues. No independent full
proof audit, numerical threshold or Lean verification is claimed here.

## The weighted statement actually available

For every fixed $0<\varepsilon\le0.01$ and every sufficiently large
**prime** $P$, the proof states

$$
\sum_{\substack{\ell\le R(P)\\(\ell/P)=-1}}\frac1\ell\ge\varepsilon,
\qquad R(P)=P^{1/(4\sqrt e)+\varepsilon/2},
$$

where $\ell$ ranges over primes, including two. The threshold depends
only on $\varepsilon$, not a chosen subsequence of $P$. There is no
growing lower cutoff in this statement. It applies to the Legendre
character of prime modulus; inducing that character to a composite modulus
does not make this a theorem for all composite quadratic characters.

## Actual-source application and its limits

Use the [FIB theory volume](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
§§181,202 and the [same-integer Euler budget](bourgainlindenstrauss2003entropy.md).
Let the primitive quadratic character associated with the actual nonsquare
$D$ have **odd prime conductor $P$**. It is then the Legendre character
$\chi_P(\ell)=(\ell/P)$. On odd primes not dividing $D$, this agrees with
the actual symbol $(D/\ell)$. A positive example is $D=Pt^2$ with
$P\equiv1\pmod4$. Positive $D=P\equiv3\pmod4$ instead has conductor
$4P$ and does not meet this prime-conductor hypothesis.

For §202's actual affine $n=h+gU$ and $Y=\log n$, require $R(P)\le Y$.
Every odd supplied prime not dividing $D$ is excluded from $n$. Set

$$
E_D(P)=\sum_{\substack{\ell\le R(P)\\\chi_P(\ell)=-1\\\ell\mid2D}}\frac1\ell.
$$

Then the conservative paper-level interface is
$J_{\rm miss}(n;Y)\ge\varepsilon-E_D(P)$.
Square-part primes absent from the primitive conductor remain in this
cost. For §181's primitive multiplicative source $n=Cu$, every odd
negative-character prime is excluded from $u$, including primes in the
square part: an odd prime dividing $D$ cannot divide the primitive $u$.
Its corresponding cost is the same sum with $\ell\mid2C$, rather than
an independently charged ramification factor.

The upper cutoff can meet $Y$ when
$P\le(\log n)^{4\sqrt e-\delta}$ for fixed $0<\delta<4\sqrt e$, after
choosing fixed $\varepsilon>0$ small enough that
$(4\sqrt e-\delta)(1/(4\sqrt e)+\varepsilon/2)<1$.
This is a **cutoff range**, not an automatic Robin-safe family: the
exception-adjusted weight must still pay
$M(Y)+T(Y)-D_{\rm pow}(n)$ for that same $n$.

In particular, if $\chi_P(2)=-1$, deleting two already costs $1/2$, larger
than the guaranteed $\varepsilon$. A fixed exceptional set does not lose
its reciprocal weight merely because $P\to\infty$. Proving that an
exceptional prime actually misses $n$ can restore its contribution, but
that is an additional arithmetic certificate.

The [Bourgain–Lindenstrauss window](bourgainlindenstrauss2003entropy.md)
has a different advantage: its lower cutoff eventually exceeds two and
its original $D$ retains square-part zeros. The
[Pollack input](pollack2017nonresidues.md) covers arbitrary nonprincipal
characters but gives a prime count rather than this stated fixed harmonic
weight. Reuse these distinct existing statements according to their actual
hypotheses; none of these interfaces settles all Robin candidates or RH.
