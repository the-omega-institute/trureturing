---
bibkey: pollack2017nonresidues
authors: Paul Pollack
year: 2017
title: Bounds for the first several prime character nonresidues
doi: null
url: https://arxiv.org/pdf/1508.05035v2
claim: Theorem 1.1 supplies many prime nonresidues for every nonprincipal character to an arbitrary sufficiently large modulus; its power-scale cutoff does not by itself reach the actual Robin prime prefix.
strata_touched: []
license: citation-only
triage: anchor
---

# Prime nonresidues with the actual exceptions retained

The [author publication list](https://www.pollack-math.net/research.html)
identifies the article as *Proceedings of the American Mathematical Society*
145 (2017), 2815–2826. The inspected sources are
[arXiv:1508.05035v2](https://arxiv.org/abs/1508.05035v2), dated 24 August
2015 in its submission history, and the [author-hosted manuscript](https://www.pollack-math.net/hudson.pdf).
Theorem 1.1 appears on p.1 of v2 and p.2 of the author manuscript;
Proposition 2.1 and Theorem 1.2 were also inspected. This is a source and
applicability check, not an independent verification of the full proof or a
Lean verification. No claim of a complete current literature survey is made.

## The existing uniform supply

For every fixed $\varepsilon>0$, Theorem 1.1 gives constants
$m_0(\varepsilon)$ and $\kappa(\varepsilon)>0$ such that every integer
$m>m_0$ and every nonprincipal Dirichlet character $\chi$ modulo $m$ have
more than $m^\kappa$ primes $\ell$ satisfying

$$
\ell\le m^{\beta},\qquad
\chi(\ell)\notin\{0,1\},\qquad
\beta=\frac1{4\sqrt e}+\varepsilon.
$$

For quadratic characters the nonresidue value is $-1$. The statement is not
restricted to prime moduli or primitive characters. Its threshold and count
exponent are not supplied here as numerical constants, so it is not a
finite numerical certificate. The theorem is unconditional; GRH and a
zero-free-region assumption are absent from its hypotheses.

For a reciprocal-prime weight supply, directly reuse
[Bourgain–Lindenstrauss, Theorem 5.1](bourgainlindenstrauss2003entropy.md).
Its cutoff is $Y\ge D^{1/4+\varepsilon}$ for sufficiently large positive
nonsquare $D$. The linked note records its exact weighted Robin budget
and actual-source exceptions; the prime-count theorem here does not
automatically supply that weight at $Y=\log N$.

Theorem 1.2 strengthens the cutoff for characters of higher order, using
the Dickman-function parameter $u_k$. Quadratic characters have order two,
so their parameter is $u_2=\sqrt e$; increasing the modulus does not increase
their order. Proposition 2.1 records Norton's Burgess estimate. Its extra
factor is $R_k(m)=\min\{M(m)^{3/4},Q(k)^{9/8}\}$; for $k=2$, $Q(k)=1$.
Thus the source already handles composite quadratic moduli. Reproving a
prime-modulus Burgess estimate would not improve this interface.

## What is required at the same arithmetic source

The [FIB theory volume](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
already owns the norm identities and character Euler-product estimates in
§§178,181,202. They are reused here.

For §181's actual $N=Cu$, an odd prime with $\chi(\ell)=-1$ is excluded from
the primitive factor $u$, but may still divide the multiplier $C$. To obtain
a prime missing from $N$, the supplied prime must also satisfy
$\ell\nmid C$ and $\ell\ne2$. The multiple-prime statement can survive
deleting a finite exceptional set $E$ when $|E|<m^\kappa$; the source's
full cutoff must still lie in the required actual prime prefix. A bound
for the first nonresidue alone does not remove the multiplier cost.
The actual-source examples in §§183,186 already show why that cost matters.

For §202's affine $N=h+gU$, the induced character modulo $4|D|$, with
$D=5h^2-4g^2Q$ nonsquare, takes only values $0,1$ at primes dividing $N$.
A prime where that induced character is $-1$ is consequently missing from
$N$. If instead one uses the primitive character of conductor $q$, all
primes dividing $2D$ remain exceptions: primes in the square part of $D$
may disappear from $q$ without disappearing from the original certificate.
Square $D$ gives a principal character and is outside Theorem 1.1's scope.

One standard way to retain a finite exceptional set is to induce the
primitive character to a modulus $M$ divisible by $q$ and by every prime
in $E$. Theorem 1.1 applies to that nonprincipal induced character and its
nonresidue primes automatically avoid $E$. The cutoff then involves
$M^\beta$, not merely $q^\beta$. Alternatively, retaining modulus $q$
requires enough supplied primes to survive deletion of $E$. These are
applications of the cited result, not new character estimates.

For a CA integer with support containing every prime through
$P=P^+(N)$, exclusion by a missing prime requires the supplied prime to be
at most **that actual $P$**. The Euler-product split $x=\log N$ in
§§178,181,202 is a different parameter. A usable source application must
establish its cutoff below $P$; it cannot substitute $x$ for $P$ without
the required comparison.

The existing canonical norm estimate $q<4N/g^2$ in §182.2 does not ensure
that $q^\beta\le\log N$, much less that the exceptions-adjusted cutoff is
at most $P$. A fixed positive power of a modulus comparable to a positive
power of $N$ exceeds $\log N$ asymptotically. This is a limitation of the
available bound at those parameters, not a lower bound on the actual first
nonresidue and not a counterexample to Robin. Restricted families with a
sufficiently small actual modulus may use the theorem, while all-candidate
conductor, exception and weighted-deficit control remains missing.

Finding one omitted prime is also not, for a general integer, a complete
Robin certificate. Its contribution must pay the actual remaining Euler
budget using the same source. No general Robin or RH conclusion, new
analytic theorem, or new Lean declaration is claimed here.
