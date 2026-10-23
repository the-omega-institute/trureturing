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
argument, Corollaries 3–4 on pp.14–15, and Theorem 4 on pp.21–22
were inspected. The definitions
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
it does not prove a Robin sign on CA2. For the selected counterexample-level
global maximizer, the linked Kalyabin note separately excludes small
supports by the existing seven-smooth theorem and Axler valuation stop,
giving $k\ge6$; this does not extend Wu's CA3 starting domain.
A quantitative comparison on CA3 and the reduction to
CA2 do not estimate the selected source's signed prime-error remainder.
The source's finite tables and checks are cited rather than rerun.


## The adjacent-CA allowance also excludes actual shifted contacts

Theorem 4, equation (4.1), printed pp.21–22, assumes an actual
CA3 source $n_i$, with $p$ the next prime after $P^+(n_i)$ and
$10^8<p<\log n_i$. It also assumes the next classical transition
$n_{i+1}=n_iq$ and $\epsilon_{i+1}=F(q,j)$, where

$$
F(q,j)=\frac{\log(1+(q+\cdots+q^j)^{-1})}{\log q}.
$$

Its stated upper comparison is

$$
\log\frac{G(n_{i+1})}{G(n_i)}
<\frac{0.12646\log q}{p(\log p)^3}.
$$

This is another CA3 starting-domain comparison, not an estimate for
an arbitrary pair of nonlinear envelope cores or their accumulated
moving-price cost. Its proof and numerical ingredients have not been
independently audited here.

For the actual shifted contacts in
[PG1](../Estimation/trureturing2026pricegapconvexity.md#real-parameter-active-cores-retain-the-actual-strict-inventory),
keep $t>1$, $B=\log u$, $A=B+t$, $u=N_A^{\rm str}$ and
$\lambda(w)=1/(w\log w)$. Let $p$ be the next prime after the
largest prime factor of this same core $u$. Here $p$ is the next
support prime and $t$ is the real source shift. At an original prime
label $r$, $t=\log r$; the intervening real-parameter argument does
not require such a label. PG1 makes $A$ a nonactivation clock, so the
absent first layer satisfies $F(p,1)<\lambda(A)$.

Reuse the existing
[first-layer cutoff before AVB24](../ArithSums/nicolas2025comparison.md#last-label-uniform-constants-and-the-actual-stieltjes-representation):
$r_{q_1(A),1}=\lambda(A)$ and $A-1<q_1(A)<A$.
Since $r_{p,1}=F(p,1)$ is strictly decreasing with its prime argument,
the same absent-layer condition gives $p>q_1(A)$. Hence

$$
p>A-1=B+t-1>B.
$$

This applies at every such actual contact, including every maximizing
tie supplied by PG1 on the original windows. This extends the domain check to
these shifted contacts without assuming they belong to Kalyabin's
$U_1$. It excludes CA3, while it does not establish $P^+(u)<B$ or
classify every contact as CA2.

Consequently neither Theorem 2 nor Theorem 4 applies at these
contacts through its CA3 starting hypothesis. A classical next-CA
transition and its activation parameter are also not identified with
a nonlinear switch or its nonactivation contact clock by PG1.
The complete lag, anchored exterior and corrected credit in BV4–BV5
remain together and unpaid at the required $M_XL_X$ scale.

This is a paper applicability consequence of the existing inventory
interface and first-layer cutoff. It supplies no new
CA criterion, arithmetic sign, Lean/kernel result or literature
priority claim, and does not repeat the source's CA proofs or tables.
