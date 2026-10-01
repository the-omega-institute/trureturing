---
bibkey: axler2024primorialcounting
authors: Christian Axler
year: 2024
title: Inequalities involving the primorial counting function
doi: null
url: https://arxiv.org/abs/2406.04018v1
claim: The paper applies Nicolas's fixed-price finite low-benefit screening to arbitrary integers in a specific finite interval; that screening supplies neither a growing-price efficiency guarantee nor the FIB host's signed Robin budget.
strata_touched: []
license: citation-only
triage: anchor
---

# Inequalities involving the primorial counting function

Primary text: [arXiv:2406.04018v1](https://arxiv.org/pdf/2406.04018v1),
version dated 6 June 2024. The relevant definitions and Lemma 5.2 are
on printed p.7; Proposition 5.3 and its computation are on pp.7–8.
Those statements have been inspected in this version. This note does
not verify all proofs or rerun its Maple enumeration.

## Fixed-price finiteness and the actual finite application

For a CA reference $C$ at parameter $\varepsilon>0$, equation (5.5)
defines the classical benefit

$$
\operatorname{ben}_\varepsilon(n)
=\log\frac{\sigma(C)}{C^{1+\varepsilon}}
-\log\frac{\sigma(n)}{n^{1+\varepsilon}}
=\varepsilon\log(n/C)-\log\frac{Z(n)}{Z(C)}.
$$

Lemma 5.2 states: for every fixed $\varepsilon>0$ and every
$\beta>0$, the set of positive integers $k$ satisfying
$\operatorname{ben}_\varepsilon(k)\le\beta$ is finite.
The source explicitly attributes the result to Proposition 4.14 of
Jean-Louis Nicolas, *The sum of divisors function and the Riemann
hypothesis*, *The Ramanujan Journal* **58** (2022), 1113–1157,
[DOI 10.1007/s11139-021-00491-y](https://doi.org/10.1007/s11139-021-00491-y).
The original 2022 proof has not been inspected here: the publisher's
PDF endpoint returned an access page. The theorem statement recorded
above is the exact restatement read in Axler's primary text.

The following paragraph says the algorithm computing these sublevel
sets is efficient when $\beta$ is not too large, specifically “not much
larger than $\varepsilon$”. This is the author's qualitative efficiency
statement, not a stated uniform complexity theorem.

Proposition 5.3 applies the method to all integers in the particular
interval $(SA_{425},N_{39})$, where $N_{39}$ is the 39th primorial.
With $\varepsilon=0.00133$ and $\beta=0.000594$, the reported Maple
intersection of the benefit sublevel set with this interval has the two elements

$$
\frac{151}{149}SA_{425},\qquad
\frac{157}{149}SA_{425}.
$$

The proposition concludes that only the first has $Z(n)>8.8272$ in
that interval. These are the source's finite computations, not new
certificates by this project. No superabundant hypothesis is imposed
on the tested integer $n$; the reference $SA_{425}$ is certified CA by
Lemma 5.1 at the chosen price.

## Transported FIB threshold and the remaining host obligation

Use [FIB §§230.2 and 234](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
with $y\to\infty$, $\ell=\log y$, $s=y\ell$,
$\varepsilon=1/s$ and $R=y/\ell^2$. For fixed $K>0$, the existing
comparison gives, for every positive integer $d$ with $J_s(d)\le KR$,

$$
\operatorname{Ben}_{C_s,1/s}(d)
\le\frac{J_s(d)+\log(C_s/\varphi(C_s))}{s}
\le\beta_y,
\qquad
\beta_y:=\frac{KR+\log(C_s/\varphi(C_s))}{s}.
$$

Here $C_s$ is the same-price CA reference. Thus the classical finite
sublevel set at $(\varepsilon,\beta)=(1/s,\beta_y)$ contains the entire
low-loss divisor set. The parameter ratio of this **chosen uniform
threshold**, not the actual benefit of every $d$, is

$$
\boxed{
\frac{\beta_y}{\varepsilon}
=KR+\log(C_s/\varphi(C_s))
=\frac{Ky}{(\log y)^2}+O(\log\log y)
\longrightarrow\infty.
}
$$

The source's stated efficient-parameter regime consequently does not
supply a uniform efficiency guarantee for this transported threshold.
This does not prove that a particular enumeration is slow; its runtime
has not been measured. Nor does finite cardinality at every fixed price
give a bound uniform in $y$ or pay a signed Robin margin.

If $d\mid N$ is the low-loss witness for the actual host in §233.5,
this upper bound concerns $d$. It does not state
$\operatorname{Ben}_{C_s,1/s}(N)\le\beta_y$; the host cofactor requires
its own transfer. The [whole-host reconstruction application](../Arith/monagan2004reconstruction.md)
already carries that cofactor into the reduced host ratio, without
enumerating the entire benefit sublevel set.

For the actual $N$, use the [same-host loss certificate](erdosnicolas1975repartition.md)
with $g=\gcd(N,C_s)$ and the actual resources
$E_+=\log(N/g)$, $E_-=\log(C_s/g)$. Its lower bound still has to exceed

$$
T_s(N)=\log\mathcal Q_s+\log N
-s\log(e^\gamma\log\log N).
$$


A finite whole-host screen can instead start from the actual signed budget,
without transferring the divisor's benefit. In the prescribed window
$N\in[A,X]$, use $s=\log A\log\log A$ and $A>5040$. If that host fails
the strict Robin test, then

$$
\operatorname{Ben}_{C_s,1/s}(N)\le\frac{T_s(N)}s.
$$

The endpoint step in Axler's proof directly supplies a uniform finite
cutoff here. Writing $L=\log N\ge\log A$, the budget has derivative
$1-s/(L\log L)\ge0$ with respect to $L$, so $T_s(N)\le T_s(X)$.
If $T_s(X)<0$, the nonnegative benefit already pays every host in this
window. Otherwise any fixed positive cutoff

$$
\beta_{\mathrm{host}}\ge\frac{T_s(X)}s
$$

contains every possible host failure. This includes the endpoint
$T_s(X)=0$ by choosing a positive cutoff and retaining all zero-benefit
ties. The parameter ratio for this host screen is
$\beta_{\mathrm{host}}/\varepsilon=s\beta_{\mathrm{host}}$;
its behavior is not determined by the divisor cutoff $\beta_y$.
After enumeration, the original window, Fibonacci residue, qualifying
source divisor and exact strict budget still require their own checks.
This is the source's fixed-price endpoint method applied to the existing
budget, not a new finiteness proof or a uniform tail certificate.

Lemma 5.2 and Proposition 5.3 supply neither that joint signed estimate
nor an exclusion of all actual growing-price FIB hosts. Their definitions,
finiteness theorem and reported numerical interval are reused directly;
no new finiteness proof, Maple enumeration or RH conclusion is claimed.
