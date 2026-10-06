---
bibkey: wu2019subsets
authors: Xiaolong Wu
year: 2019
title: Subsets of colossally abundant numbers
doi: null
url: https://arxiv.org/abs/1903.03490v1
claim: The preprint states quantitative improvements from CA3 sources to later CA prefixes; this starting domain excludes the eligible one-step critical sources whose logarithms lie between their own largest prime and the next prime.
strata_touched: []
license: citation-only
triage: anchor
---

# Existing CA3 improvements and the source domain

The inspected primary is
[arXiv:1903.03490v1](https://arxiv.org/pdf/1903.03490v1), 23 pages,
with PDF SHA-256
`64dd95754591cfd0c114516eccbef1efd577ed42ad7bd3f2c44ba4acff2dc6e2`.
The definitions on printed p.2, Lemma 2, Theorem 2 on p.13 and its
argument, and Corollaries 3–4 on pp.14–15 were inspected. The definitions
and quantitative statement were also read in page images. This is a
preprint citation and applicability assessment, without a full proof
audit, reproduction of its finite computations, or Lean verification.

Put $G(n)=\sigma(n)/(n\log\log n)$, $P=P^+(n)$, and let $P^+$ be the
next prime. The paper's critical-parameter construction includes all
threshold layers according to equations (3)–(6). Its three classes are

$$
\mathrm{CA1}:\log n<P,\qquad
\mathrm{CA2}:P<\log n<P^+,\qquad
\mathrm{CA3}:P^+<\log n.
$$

The label CA2 describes this location of $\log n$. It is distinct from
the [Caveney–Nicolas–Sondow GA2 property](caveney2012sacaga.md), which
compares $G(n)$ with every integer multiple's value.

Theorem 2 takes an actual CA3 prefix $n_i$, puts $p=P^+$, and constructs
$n_j$ from the critical parameter

$$
\epsilon_j=F(p,1)=\frac{\log(1+1/p)}{\log p}.
$$

With $t_0>e$ the minimum point of $t^{\epsilon_j}/\log\log t$, so that
$\epsilon_j\log t_0\log\log t_0=1$, its stated quantitative comparison is

$$
G(n_j)>G(n_i)\left(1+
\frac{3.2961}{(\log t_0)^2\log\log t_0}\right).
$$

Corollary 3 states that a CA3 source has a later CA2 source with larger
$G$; Corollary 4 states the reduction of Robin's criterion to CA2.
These are existing source comparisons and a published test-set
reduction, not a new improving-multiplier construction or criterion.

For the current source problem, reuse the
[Kalyabin endpoint conditions](../Analytic/kalyabin2026maximalgronwall.md)
at the same actual integer $N\in U_1$, with $P=P^+(N)=p_k$ and $k>4$.
They already give $P<\log N<P^+$. Thus, when the required CA-prefix
identification is present, this source lies in Wu's CA2 class. The
starting condition $P^+<\log N$ of Theorem 2 is incompatible with those
endpoints. Its improving comparison cannot be used at that source by
changing the class label or selecting another CA integer.

This excludes that particular supplier on the eligible source class;
it does not prove a Robin sign on CA2 or settle the remaining small
support cases. A quantitative comparison on CA3 and the reduction to
CA2 do not estimate the selected source's signed prime-error remainder.
The source's finite tables and checks are cited rather than rerun.
