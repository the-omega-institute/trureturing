---
bibkey: tenenbaumwang2026largefriablecomponent
authors: Gérald Tenenbaum and Xiangyu Wang
year: 2026
title: On integers whose friable component is large
doi: null
url: https://arxiv.org/abs/2609.37507v2
claim: "Theorem 1 gives a uniform logarithmic estimate for integers up to x whose largest y-friable divisor exceeds z; it can sharpen a population bound only after a same-candidate FIB bridge supplies the required y and z, and it does not estimate the signed Robin remainder."
strata_touched: []
license: citation-only
triage: anchor
---

# A uniform population estimate for large friable components

The inspected source is Gérald Tenenbaum and Xiangyu Wang, *On integers
whose friable component is large*, [arXiv:2609.37507v2](https://arxiv.org/abs/2609.37507v2),
submitted 28 September 2026 and revised 11 October 2026. The paper is a
four-page preprint; its proof and the cited Hildebrand--Tenenbaum inputs
were not independently formalized here.

For (y\ge2), let (n_y) be the largest divisor of (n) all of whose
prime factors are at most (y), and put

$$
\Theta(x,y,z)=\#\{n\le x:n_y>z\},
\qquad v=\frac{\log z}{\log y}.
$$

Theorem 1 states, uniformly for

$$
\max\{2,\log z\}\le y\le z\le x/2,
$$

that

$$
\boxed{
\Theta(x,y,z)
=x\exp\!\left(-v\log\!\bigl(v\log(3v)\bigr)+O(v)\right),
}
$$

with an absolute implied constant. The result sharpens the earlier
estimate from Tenenbaum's 2006 paper and Ford's sieve-lecture problem.

## The FIB/Robin interface

The current FIB reduction has a subpolynomial count for the exact
near-extremal pairs

$$
N=uv=1+F_rg,
\qquad v\mid C,
\qquad Cu\equiv v\pmod {F_r}.
$$

Theorem 1 could replace or sharpen a population estimate only after a
new same-source lemma proves, for every pair in a specified exceptional
subfamily, a lower bound

$$
N_y>z
$$

with parameters satisfying the theorem's displayed range. The congruence
condition must then be retained while counting that subfamily; an
unrestricted count of all integers with (N_y>z) does not certify the
absence or presence of a hit in the particular Fibonacci residue class.

Even if this bridge were supplied, the theorem controls only the number of
integers. It does not control the complete prime-power weight of the same
(N), the CA price defect (D^*(a)), or the signed Robin tail
(H_a). Thus it is a possible refinement of the sparse candidate count,
not the missing joint estimate and not a Robin or RH proof.

