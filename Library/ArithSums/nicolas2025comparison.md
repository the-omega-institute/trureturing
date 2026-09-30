---
bibkey: nicolas2025comparison
authors: Jean-Louis Nicolas
year: 2025
title: Comparison of large values of n/φ(n) and σ(n)/n
doi: null
url: https://hal.science/hal-05389053v1
claim: The manuscript gives unconditional asymptotic and effective comparisons between the two separate extremal envelopes Φ(X) and Σ(X); it does not identify common maximizers, arbitrary near-extremal prime profiles, or source-weighted concentration in a prescribed residue class.
strata_touched: []
license: citation-only
triage: anchor
---

# Comparison of large values of n/φ(n) and σ(n)/n

The primary manuscript is Jean-Louis Nicolas's single-author [HAL hal-05389053v1](https://hal.science/hal-05389053v1), with [versioned full text](https://hal.science/hal-05389053v1/document). Its title page is dated **15 July 2025**; the HAL cover and submission record say **29 November 2025**. The PDF has 38 numbered manuscript pages plus the HAL cover. These dates are distinct from later changes to the record's metadata. No journal publication or DOI is asserted here.

This source is not Axler–Nicolas, *Large values of n/φ(n) and σ(n)/n*, *Acta Arithmetica* **209** (2023), 357–383, DOI [10.4064/aa220705-12-10](https://doi.org/10.4064/aa220705-12-10). The latter is reference [2] in the 2025 manuscript and supplies an earlier effective comparison.

This card records the definitions, main theorem statements and relevant proof interfaces checked in the primary manuscript. It is not a full verification of all analytic proofs, external estimates or Maple computations, and supplies no Lean verification.

## The two envelopes and the actual quantifiers

For real $X\ge1$, equation (1.7), printed p.3, defines

$$
\Phi(X)=\max_{1\le n\le X}\frac n{\varphi(n)},
\qquad
\Sigma(X)=\max_{1\le n\le X}\frac{\sigma(n)}n.
$$

The maxima range over positive integers and are taken **separately**. The strict record holders for $n/\varphi(n)$ are the primorials; those for $\sigma(n)/n$ are the superabundant integers. Remark 1.1 reports that the only integers that are both primorial and superabundant are 2 and 6. This observation concerns strict records: because $n/\varphi(n)$ can tie, it does not imply that the two sets of maximizers are always disjoint. No common maximizing integer is supplied for a general $X$.

Theorem 1.2, printed p.4, states that for every fixed integer $J\ge1$, as real $X\to\infty$,

$$
\frac{\Phi(X)}{\Sigma(X)}
=1+\sum_{j=1}^{J}
\frac{c_j\sqrt2}{\sqrt{\log X}(\log\log X)^j}
+O_J\!\left(\frac1{\sqrt{\log X}(\log\log X)^{J+1}}\right),
$$

where, with $a=\log2$,

$$
c_1=2,\qquad c_2=-(2+a),\qquad c_3=8+4a+\frac{3a^2}{4}.
$$

The statement is **unconditional**. The error constant may depend on $J$; there is no uniform assertion for $J$ growing with $X$, and this is not a moment asymptotic with exponent $s$.

Equation (1.10) defines $\tau(X)$ by the exact equality, for $X>e$,

$$
\frac{\Phi(X)}{\Sigma(X)}
=1+\frac{2\sqrt2}{\sqrt{\log X}\log\log X}
-\frac{(2+\log2)\sqrt2}{\sqrt{\log X}(\log\log X)^2}
+\frac{\tau(X)}{\sqrt{\log X}(\log\log X)^3}.
$$

Theorem 1.3, on the same page, supplies **unconditional effective bounds**:

- $6.78\le\tau(X)\le94.73$ for every real $X\ge N^{(0)}$;
- $0.153\le\tau(X)\le129.08$ for every real $4\le X\le N^{(0)}$.

Here $N^{(0)}$ is the specific CA integer defined by its prime factorization in (3.13), with $\log N^{(0)}=1000014552.11\ldots$ in (3.14). The displayed decimal is a description of the threshold, not its definition. The finite part of the proof uses bounds from Axler–Nicolas 2023; this source inspection has not independently rerun that computation.

## What prime-profile information the argument uses

Section 3 parametrizes **CA reference integers** by the usual decreasing prime-power thresholds $F(\xi_k,k)=\epsilon$. Lemmas 3.2–3.4 estimate these thresholds, particularly the square layer $\xi_2$. Lemmas 3.5–3.6 compare $\xi$ with $\log X$ after choosing adjacent parameter-defined CA integers $N'\le X<N$.

Section 4, printed pp.23–24, then uses

$$
\frac{\sigma(N')}{N'}\le\Sigma(X)<\frac{\sigma(N)}N
$$

and the primorial attaining $\Phi(X)$ to compare the envelopes. Its “excess” is

$$
E(X)=\log N-\vartheta(\xi)
=\sum_{k\ge2}\vartheta(\xi_k),
$$

which measures the higher-prime-power content of that CA reference. It is not the deficit $J_s(d)$ of an arbitrary actual divisor from the FIB source.

These are forward estimates of extremizers and their envelopes. The checked theorem and lemma statements do not give an inverse assertion that every integer whose abundancy is close to the envelope shares a specified common core. They also do not preserve the original integer or its residue class when replacing it by a CA or primorial extremizer.

## Relation to the current actual-divisor estimates

| Current object or goal | What this source supplies | Additional obligation |
|---|---|---|
| Replacing $Z(n)=\sigma(n)/n$ by $n/\varphi(n)$ | Quantifies the discrepancy of the two **maxima up to the same $X$**, including its leading $2\sqrt2/(\sqrt{\log X}\log\log X)$ term. | It is not a lower bound for $[n/\varphi(n)]/Z(n)$ at the same integer. Separate maximizers cannot be treated as jointly realized. |
| A bound for an actual $n\le X$ | Any positive lower bound $L(X)$ for $\Phi(X)/\Sigma(X)$ gives the valid global bound $Z(n)\le\Sigma(X)\le\Phi(X)/L(X)$. | Proving this bound below the actual Robin budget requires an additional comparison with $e^\gamma\log\log n$; the envelope theorem does not already make that comparison. |
| The low-loss divisor set $J_s(d)\le O(R)$ for $w_s(d)=b_s(d)/d$ | CA prime-layer estimates provide related extremal arithmetic background. | No stated comparison identifies its CA reference objective with $b_s=\mu*Z^s$, its normalized weights, or $J_s=\log(\max w_s/w_s)$. |
| Uniform editing/common-core bounds for every low-loss divisor | No directly matching inverse theorem was located in the inspected statements. | The source-specific uniform bound remains to be justified; the unweighted §232 count already has the separate classical benefit/PNT simplification. |
| $s=\log A\log\log A$, $R=\log A/(\log\log A)^2$, and the full complementary moment | The paper studies fixed-order expansions of extremal envelopes. | It supplies no $s$-uniform source power sum, $J_s$-tail estimate, or actual-divisor incidence count. |
| Every prescribed growing reduced residue class | No progression or residue-class hypothesis is present in its main results. | A map to an extremizer is not a map preserving $n\equiv c\pmod m$, divisor incidence, or the candidate's complete joint weight. |

The unconditional status of Theorems 1.2–1.3 should be kept separate from RH-conditional bounds in Nicolas's other work. In particular, the frequently quoted bound with a $0.095/\sqrt{\log n}$ subtraction is **not** Theorem 1.2 or Theorem 1.3 of this manuscript; no such corollary is stated here. This card does not reclassify any result from the distinct 2022 paper.

The useful addition is an explicit comparison between the global Euler and divisor-sum envelopes. It does not by itself remove the possible singleton in §232, establish the missing FIB-to-CA transfer, or certify originality of the actual-source weighted concentration argument. The remaining common-implementation and uniformity requirements must not be erased by the shared terminology “large values.”
