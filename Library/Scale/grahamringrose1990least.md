---
bibkey: grahamringrose1990least
authors: S. W. Graham and C. J. Ringrose
year: 1990
title: Lower Bounds for Least Quadratic Non-Residues
doi: 10.1007/978-1-4612-3464-7_18
url: https://page-one.springer.com/pdf/preview/10.1007/978-1-4612-3464-7_18
claim: Theorem 1 gives infinitely many prime moduli whose least nonresidue exceeds a constant times log p times log log log p, ruling out a uniform positive negative-character prime weight at a fixed logarithmic cutoff for unrestricted quadratic characters.
strata_touched: []
license: citation-only
triage: anchor
---

# The generic logarithmic nonresidue route has a classical obstruction

The chapter appeared in *Analytic Number Theory*, Progress in Mathematics
85 (1990), 269–309,
[DOI:10.1007/978-1-4612-3464-7_18](https://doi.org/10.1007/978-1-4612-3464-7_18).
The inspected primary source is the publisher's
[two-page preview](https://page-one.springer.com/pdf/preview/10.1007/978-1-4612-3464-7_18).
Theorem 1 is on printed p.269. The full chapter was not obtained; this is
a check of the original statement and its parameter consequence, not an
independent audit of the full proof or a Lean verification.

## The actual lower-bound quantifiers

Let $n_p$ be the least positive integer that is a quadratic nonresidue
modulo the prime $p$. Theorem 1 unconditionally states

$$
n_p=\Omega(\log p\,\log\log\log p).
$$

The introduction explains this lower-bound convention as the existence of
an absolute $c>0$ and infinitely many primes satisfying
$n_p\ge c\log p\,\log\log\log p$. It is not a lower bound for every
prime and does not specify a congruence class modulo four.

For every fixed $A>0$, the same unbounded sequence eventually has
$n_p>A\log p$. There is then no prime, or integer, nonresidue up to
$A\log p$, and hence

$$
\sum_{\substack{\ell\le A\log p\\(\ell/p)=-1}}\frac1\ell=0
$$

for infinitely many prime conductors. Thus an assertion of uniformly
positive negative-character prime weight at $A\log q$ for all large
quadratic conductors is false. This does not conflict with the much larger
cutoffs of [Bourgain–Lindenstrauss](bourgainlindenstrauss2003entropy.md),
[Banks et al.](banksgaraevheathbrownshparlinski2008density.md), or
[Pollack](pollack2017nonresidues.md).

## What this does and does not exclude in FIB

The [FIB theory volume](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
§182's $q_D<4N/g^2$ does not, on its own, exclude a conductor comparable
to $N$. At that scale a cutoff $\log N$ is comparable to $\log q_D$,
so a generic conductor-only nonresidue supply cannot fill the gap.

Applying this obstruction to actual FIB sources would additionally require
realizing these quadratic characters in actual FIB sources and retaining
the needed relation between $N$ and $q_D$. No such realization is established
here. The theorem also does not imply that the actual integer has no missing
small primes: missing primes may have positive character value.

The unresolved task is therefore to exploit a restriction of the **same
actual FIB source**, control its conductor relative to $N$, or supply a
different actual weighted deficit. This source refutes the unrestricted
logarithmic character assertion, not Robin, RH, or every family-specific
FIB route.
