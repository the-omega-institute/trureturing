---
bibkey: zimov2025leastca
authors: Bruce Zimov
year: 2025
title: On the Least Colossally Abundant Exception to Robin's Inequality
doi: null
url: https://arxiv.org/abs/2510.23889v1
claim: The preprint claims that, if RH is false, the least colossally abundant Robin counterexample lies in a narrow asymptotic excess band; this band is much wider than the explicit FIB §250 gap and does not identify a FIB source.
strata_touched: []
license: citation-only
triage: anchor
---

# On the Least Colossally Abundant Exception to Robin's Inequality

The source is [arXiv:2510.23889v1](https://arxiv.org/pdf/2510.23889v1), submitted 27 October 2025. This card records the stated result and its hypotheses, with a scoped paper applicability analysis below; no full independent proof audit or formalization is claimed.

Write

$$
G(n)=\frac{\sigma(n)/n}{\log\log n}.
$$

Using the classical reduction to consecutive colossally abundant numbers, their prime or semiprime quotients, and Robin's oscillation theorem under $\lnot\mathrm{RH}$, Theorem 8 claims that the least CA counterexample satisfies

$$
e^\gamma<G(n)<e^\gamma\left(1+\frac{c}{(\log n)^b}\right),
\qquad 0<b<\frac12,
$$

for a positive constant $c$ depending on the chosen $b$. The paper distinguishes this least CA counterexample from the least integer counterexample; the former is a sufficient test set only through the classical CA reduction.

## Relation to the current FIB estimates

The upper band is of order $(\log n)^{-b}$, whereas the explicit §250 same-source gap is of order $1/(\sqrt n(\log n)^3)$. These scales do not contradict one another, and the band does not control the signed $\Phi$ term in the FIB decomposition. Applying it would additionally require proving that a FIB candidate is CA and that the consecutive-CA quotient is the same source used by the FIB price model. Neither implication follows from a five-window address or its congruence.

## Applicability of the claimed least-counterexample band

The inspected [abstract and submission history](https://arxiv.org/abs/2510.23889)
list only v1. The following is a scoped paper analysis of Theorem 8,
proof Step 1, the “Existing Primes” and “Double Logarithm Ratio” bullets,
and Step 2 in the [primary HTML](https://arxiv.org/html/2510.23889v1).
It does not independently audit the full preprint or establish a
Lean-verified result. The displayed band above remains a preprint claim.

### A fixed-prime activation tests the asserted per-layer rate

The “Existing Primes” bullet writes

$$
\frac{Z(n)}{Z(m)}=1+\frac1{p\sigma(p^{a_p})}
$$

and uses $p\sim\log n$ to assert an increment
$O((\log n)^{-2})$. Theorem 5 supplies that asymptotic for the
**largest** prime factor, not for every prime whose exponent increases.
Here $Z(n)=\sigma(n)/n$, as in the existing Euler inventory.

Reuse the [strict layer inventory and marginal prices](nicolas2025comparison.md#same-actual-state-finite-support-and-endpoint-correction)
and the [existing full-real inventory normal form](../Analytic/mantovanelli2026primeworkload.md#the-full-real-normal-form-also-controls-strict-inventory-at-events).
Write $\lambda(x)=1/(x\log x)$ and
$r_{p,j}=\log(1+1/(p+\cdots+p^j))/\log p$.
For $k\ge2$, let $a_k>1$ solve

$$
\lambda(a_k)=r_{2,k}
=\frac{\log(1+1/(2^{k+1}-2))}{\log2},\qquad
m_k=N_{a_k}^{\rm str},\qquad n_k=2m_k.
\tag{Z1}
$$

The decreasing price has a unique such root and $a_k\to\infty$.
The exponent of 2 in $m_k$ is exactly $k-1$. Both integers maximize
$Z(v)v^{-\lambda(a_k)}$: the strict inventory takes every positive
marginal layer, and the additional 2-layer has zero marginal cost.
Other simultaneous equality layers remain optional and are not assumed
absent. This uses the source's Definition 2.1, which allows every
maximizer, including tied choices.

These are also consecutive CA integers under that all-maximizer
definition. At a price larger than $\lambda(a_k)$ every maximizing
integer divides $m_k$; at a smaller price it is divisible by $2m_k$.
At the equal price it is $m_k$ times a product of optional tied primes;
every nonempty product is at least 2. There is therefore no CA integer
strictly between $m_k$ and $2m_k$. No assertion is made that $m_k$
satisfies Robin or $n_k$ violates it.

Put $A_k=\log n_k$. The reused full-real normal form and ordinary PNT
give $K(a_k)\sim a_k$, so $A_k=K(a_k)+\log2\sim a_k$. Exact Euler
telescoping gives

$$
\Delta_k:=\frac{Z(n_k)}{Z(m_k)}-1
=\frac1{2\sigma(2^{k-1})}
=\frac1{2^{k+1}-2}
=e^{\lambda(a_k)\log2}-1
\sim\frac{\log2}{a_k\log a_k}.
\tag{Z2}
$$

Consequently $A_k^2\Delta_k\sim(\log2)a_k/\log a_k\to\infty$.
The stated $O(A_k^{-2})$ per-layer rate does not hold on this actual
consecutive-CA family. This identifies a defective rate in Step 1,
not a counterexample to Theorem 8 or to Robin's inequality. The family
does not supply the paper's additional first-crossing hypothesis.

### A weaker activation-price bound repairs the local upper estimate

The stronger per-layer rate is unnecessary for an $O(1/\log n)$
upper bound. Reuse the full-real normal form for the maximal and strict
prefixes and the [existing first-cutoff enclosure](nicolas2025comparison.md#same-actual-state-finite-support-and-endpoint-correction),
$a-1<q_1(a)<a$. If a transition adds $h$ tied layers at the same price
$\epsilon=\lambda(a)$, with $h$ bounded independently of $a$, every
added prime is at most $q_1(a)<a$. The complete equality-prefix mass
is retained; the existing normal forms give $\log n\sim a$ for every
tied CA choice at that price. The exact layer identities give

$$
\frac{Z(n)}{Z(m)}
=\exp\!\left(\lambda(a)\sum_{\text{added layers}}\log p\right)
\le e^{h/a}=1+O_h(1/a)=1+O_h(1/\log n).
\tag{Z3}
$$

This covers the prime and two-prime transitions when their
common-price, bounded-layer representation is supplied. It does not
prove that the nonlinear FIB selector's adjacent cores are classical
adjacent CA numbers: those cores have different own prices.

For $e<m<n$, the double-log factor lies strictly between zero and one.
Thus Z3 supplies the required **one-sided** upper estimate

$$
\frac{G(n)}{G(m)}
\le\frac{Z(n)}{Z(m)}\le1+\frac C{\log n}
\tag{Z4}
$$

eventually. The primary's equality
$(1+O(1/\log n))(1+o(1))=1+O(1/\log n)$ is not justified by those
two rates alone; monotonicity of the double-log factor suffices for
the upper inequality Z4. No new generic CA or benefit theorem is
claimed for this application.

### The least-counterexample quantifier still needs a threshold

Suppose the local upper estimate is valid for $n\ge N_0$ and
$G(m)<e^\gamma$. For fixed $c>0$ and $0<b<1/2$, simultaneous validity
of $G(n)>e^\gamma(1+c/(\log n)^b)$ would require

$$
c(\log n)^{1-b}<C.
\tag{Z5}
$$

Hence the two bounds are incompatible once both $n\ge N_0$ and
$(\log n)^{1-b}\ge C/c$ hold. The paper's Step 2 establishes an
eventual comparison, but does not supply constants and a threshold
that place the fixed least CA counterexample in this range.
Its stated finite Robin-verification range does not give that
comparison without a bound on $N_0$ and $C/c$.

Infinitely many RH-failure oscillation witnesses cannot replace this
missing statement about the **least** witness. They also do not turn
the possible boundary value $G(n)=e^\gamma$, allowed by the paper's
counterexample definition, into its strict lower band endpoint.
Neither issue establishes that Theorem 8's conclusion is false.

Accordingly Theorem 8 is not used as a proved supplier for the
[original signed Robin comparison](../Estimation/trureturing2026pricegapconvexity.md).
The actual-source $G_a$ integral, its common cofinal full windows,
all maximizing ties and original weights still require a signed
estimate. The local repair Z3--Z4 pays none of that estimate. The
reused CA structure, inventory asymptotics and elementary rate
calculations are credited existing inputs; the scoped applicability
finding is a paper derivation, with no originality or kernel claim.
