---
bibkey: matijasevick2026forbiddensubsets
authors: "Mateo Matijasevick"
year: 2026
title: "Forbidden subset sums in a linear range: an inverse theorem and the Erdős-Graham irregularity problem"
doi: 10.48550/arXiv.2611.17205
url: https://arxiv.org/html/2611.17205v1#S9
claim: "Problems 9.1 and 9.2 ask for limits on additional least-nondivisor classes and for the optimal range constant in the inverse theorem."
strata_touched:
  - D5/S3/Combinatorics/SubsetSums/Erdos361InverseRange
license: citation-only
triage: anchor
---

<!-- GID: D5/L/ArithUnits/matijasevick2026forbiddensubsets -->

# The range in the forbidden-subset-sum inverse theorem

## Verified locator

DOI <https://doi.org/10.48550/arXiv.2611.17205>

Source <https://arxiv.org/html/2611.17205v1#S9>, Problems 9.1–9.3.

## The range question

Let \(q\) be the least positive nondivisor of a fixed positive integer \(s\).
Theorem 1.2 asks when density greater than \(1/q\) in an initial interval
\([1,E]\) forces a subset sum of \(sT\), with an additive density margin
of \(\varepsilon T\) and \(T\) sufficiently large. Problem 9.2 asks for the
optimal range constant \(\theta_q\) in \(\theta_q E\le sT\).
[Matijasevick, §9](https://arxiv.org/html/2611.17205v1#S9)

## A linear bound

Fix \(K=2s/\varepsilon\) and \(m=\lceil K\rceil+2(q-1)\).
Matijasevick's Lemma 2.2 and Roth's theorem give a core \(G\) of size
at least \(E/q+\varepsilon T/2\), every element of which centers at
least \(m\) three-term progressions in the original set. Write
\(d=\gcd(G)\), \(L=\max(G)/d\), and \(B=\{0\}\cup(G/d)\).
The core size forces \(d<q\), hence \(d\mid s\). If \((q-1)E\le sT\),
then \(y=sT/d\) lies in \([(q-1)L,KL]\). The same size bound gives
\(|B|\ge (1/q+\varepsilon(q-1)/(2s))L\).

Write \(L-1=k(|B|-2)+r\) with \(0\le r<|B|-2\).
For large \(T\) the density margin implies \(k\le q-1\).
Lev's interval theorem puts \([b,mL-b]\) inside \(mB\), with
\(b=kL-k(|B|-1-r)\le(q-1)L\). Thus \(y\in mB\).
Multiplying by \(d\) and using Lemma 2.2(a) to replace repeats proves
the distinct-element statement and \(\theta_q\le q-1\).
[Lev, Theorem 10(i)](https://arxiv.org/html/2110.03554v2#Thmtheorem10)

## Sharpness

If \(q\) or \(q+1\) is prime, choose such a prime \(\ell\) and set
\(s=\operatorname{lcm}(1,\ldots,q-1)\). Take the multiples of \(\ell\)
in \([1,E]\) and the numbers congruent to one modulo \(\ell\) in
\((\alpha E,E]\). For \(\alpha<2-\ell/q\) the density is greater
than \(1/q\). With \(sT\equiv-1\pmod\ell\), a representation needs
at least \(\ell-1\) of the terminal terms. Their sum is greater
than \((\ell-1)\alpha E\). Since
\((\ell-1)(2-\ell/q)=q-1\), any proposed constant below \(q-1\)
fails. This gives \(\theta_q=q-1\) in these cases.
The Lean module proves the sharp lower bound for \(q=4\), using
\(s=6\) and \(\ell=5\). In particular the proposed \(9/4\) differs
from the exact ordinary value \(\theta_4=3\).

## Limit consequences

The new range replaces the hypothesis of Theorem 1.4(ii) by
\((q-1)\min(c,1-c)\le1\). Its limits along the class of least
nondivisor \(q\) are \(c/q\) for \(c\le1/2\) and
\(c-1/2+(1-c)/q\) for \(c>1/2\). For the latter case apply the
inverse bound below \(n-\lfloor cn\rfloor\) and pair \(x\) with
\(n-x\) in the remaining interval. The modular constructions in
Proposition 5.3 give the matching lower bounds.

For \(c=2/3\), an avoiding set has size at least \(n/4-O(1)\)
by Proposition 5.3(d). The new bound with \(q=4\) matches that
on the entire class of least nondivisor at least four. The limit
along \(n\equiv6\pmod{12}\) is \(1/4\), and the complete set of
limit points at \(c=2/3\) is \(\{1/4,5/18,1/3\}\). For
\(c=1/(q-1)\) with prime power \(q\ge3\), the avoiding interval
\((n/q,n/(q-1)]\) gives a matching lower bound on the class of
least nondivisor at least \(q\). Together with the smaller classes,
the limit set is
\(\{1/((q-1)r): r\le q,\ r\text{ a prime power}\}\).
These upper bounds and limits use Lev's ordinary theorem.
[Matijasevick, Theorem 1.4 and §9](https://arxiv.org/html/2611.17205v1)
