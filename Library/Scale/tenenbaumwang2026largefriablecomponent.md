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

For $y\ge2$, let $n_y$ be the largest divisor of $n$ all of whose
prime factors are at most $y$, and put

$$
\Theta(x,y,z)=\#\{n\le x:n_y>z\},
\qquad \nu=\frac{\log z}{\log y}.
$$

Theorem 1 states, uniformly for

$$
\max\{2,\log z\}\le y\le z\le x/2,
$$

that

$$
\boxed{
\Theta(x,y,z)
=x\exp\!\left(-\nu\log\!\bigl(\nu\log(3\nu)\bigr)+O(\nu)\right),
}
$$

with an absolute implied constant. The result sharpens the earlier
estimate from Tenenbaum's 2006 paper and Ford's sieve-lecture problem.

## The FIB/Robin interface

The existing FIB reduction has exact near-extremal pairs

$$
N=uv=1+F_rg,
\qquad v\mid C,
\qquad Cu\equiv v\pmod {F_r},
\qquad E=\log(uv).
$$

There is a same-source smooth-core implication. Put
$g_0=\gcd(N,C)=C/v$. If every prime factor of $C$ is at most $y$, then
$g_0$ is a $y$-friable divisor of $N$. Hence

$$
N_y\ge g_0=\frac Cv,
\qquad
E\le L\Longrightarrow N_y\ge C e^{-L}.
$$

Consequently, whenever the parameters satisfy Theorem 1's range, the
original candidate set obeys the independent bound

$$
\#\{N\text{ in the window}:E\le L\}
\le
\min\left\{\tau(C),
\Theta\left(x,y,C e^{-L}\right)\right\},
$$

where $x$ is any upper endpoint with the window below $x$ and
$C e^{-L}\le x/2$. This is a genuine same-candidate population estimate;
it preserves the Fibonacci residue condition because the left-hand set is
still the original set. The theorem's conditions, including
$\max\{2,\log(Ce^{-L})\}\le y\le Ce^{-L}$, must be checked rather
than assumed.

The estimate still controls only the number of integers. It does not
control the complete prime-power weight of the same $N$, the CA price
 defect $D^*(a)$, or the signed Robin tail $H_a$. Thus it is a new sparse
counting interface, not the missing joint estimate and not a Robin or RH
proof.

