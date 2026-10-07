---
bibkey: musin2026higherorder
authors: Oleg R. Musin
year: 2026
title: Higher-order colossally abundant numbers
doi: null
url: https://arxiv.org/abs/2609.33794v1
claim: The preprint gives explicit hypotheses for coordinate changes and nested contact sets to preserve Robin's criterion; nesting and empty intersection alone do not imply RH.
strata_touched: []
license: citation-only
triage: anchor
---

# Higher-order colossally abundant numbers

The inspected source is [arXiv:2609.33794v1](https://arxiv.org/pdf/2609.33794v1), submitted 27 September 2026, 21 pages. This card records statements and hypotheses from that version. It is a preprint; this inspection is not peer review, a Lean verification, or verification of every proof and numerical example. The contact construction and theorems below are attributed to that source, not claimed as new FIB results.

## The common arithmetic source and the contact construction

Musin works on the same comparison set at every level,

$$
D=\{n\text{ colossally abundant}:n\ge55440\}.
$$

Put $\rho(n)=\sigma(n)/n$, $u(n)=\log\log n$, $G(n)=\rho(n)/u(n)$ and $E=e^\gamma$. The reference $n_*=55440$ is included in every support comparison but excluded from the selected contact sets. Formula (10) defines a contact by an attained global minimum of $Y(n)+\lambda X(n)$ over $D$, with $\lambda\ge0$. Horizontal supports and all ties are retained; limiting hull points are not integer contacts.

Theorem 2.2 states that increasing concave differentiable changes of both coordinates, with positive derivatives on their ranges, give nested contact sets. Its tangent-line argument transports a support at the finer level to a support at the earlier level. The selected points still refer to the same actual integers; changing coordinates does not authorize changing the divisor sum or replacing a global comparison with a finite sample.

## Preserving the full Robin criterion needs additional hypotheses

For one arithmetic coordinate pair $(F(u),-H(\rho))$, Theorem 3.1 assumes that $F,H$ are positive, increasing, unbounded $C^2$ functions with positive first derivatives, and

$$
\frac{H(Eu+0.6483/u)}{F(u)}\longrightarrow0,
\qquad
\frac{F''(u)}{F'(u)}\ge E\frac{H''(Eu)}{H'(Eu)}
\quad\text{eventually}.
$$

The first condition makes the relevant supported extrema attain their values at actual integers. The second gives eventual concavity of the transported Robin boundary. The theorem then states that the contact set is infinite and testing Robin on that set is equivalent to testing it on $D$; if RH is false, it contains infinitely many strict violations. Theorem 3.2 applies this at each fixed level together with the coordinate-transition hypotheses. Its eventual conditions are for each fixed level; no uniformity in the level is asserted or required for that theorem.

This is a ready-made conditional bridge for a coordinate-based reduction. Before applying it to a FIB construction, one must identify the same source $D$, actual objective, attained supports, transition maps, and the displayed growth and concavity conditions. A unique Zeckendorf encoding or a reversible change of composition coordinates alone supplies none of these analytic hypotheses.

## Two different kinds of recursive thinning

| Construction in the preprint | Stated conclusion | What it does not establish |
|---|---|---|
| Arithmetic families, Theorem 3.2 and Corollary 3.4 | Each fixed level retains an RH-equivalent Robin test; suitable families have infinite levels, empty intersection, and least members tending to infinity unconditionally. | Empty intersection does not prove RH: under its negation each level still contains violations, with their locations escaping. |
| Families retaining every global maximum of $G$, Theorem 4.1 | The nested intersection is exactly $\arg\max_D G$; empty intersection and escape of the least contacts are equivalent to RH under the stated hypotheses. | Escape for these families is not an unconditional conclusion; proving it would settle the original problem. |
| Nonempty maximum-preserving families, Theorem 4.3 | The least-contact values of $G$ are nondecreasing and tend to $\sup_D G$; Robin at every least contact is equivalent to RH. | A contact computed from a finite hull is not automatically a global contact; the uncomputed tail needs control. |

For Theorem 4.1 the coordinates are $(-q_k,-G^{s_k})$: $q_k(n)>0$ decreases strictly to zero with $n$, $s_k>0$ is nondecreasing, the abscissa transitions are increasing concave maps with positive derivatives, and $q_k(n)/q_k(n_*)\to0$ for every fixed $n>n_*$. The source gives concrete power and fractional-linear choices. These conditions distinguish this construction from the unconditional arithmetic families. The paper explicitly leaves monotonicity of the least-contact Robin quotients, and reduction to those least members, unproved for its arithmetic families.

## Consequences for the FIB research direction

The author's earlier [highest-abundant construction](musin2020strongramanujan.md)
uses the all-integer domain $n\ge5040$, abscissa $n$, and the weighted
absolute Robin defect. Its Theorem 3(b) makes the square-root logarithmic
contact set empty if RH is false. This differs from the unconditional
infinite arithmetic contact families above. A finite supported hull or a
normalized Robin maximizer cannot be identified with such a global
highest-abundant contact without proving the missing attainment claim.

The supporting-line description of classical colossally abundant numbers is older than this preprint: the introduction cites Alaoglu–Erdős for the prime-increment optimization and Musin's earlier work for the convex-envelope description. The new version develops higher-order contacts and the stated preservation and growth theorems. A local FIB reformulation must not relabel either body of work as an original geometric discovery.

For the [project's theory](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md), this source addresses a gap that the restricted family $N_g=1+F_r g$ does not fill: an explicit theorem retaining the full RH test when the observed family is reduced. It does not itself prove Robin on that Fibonacci family, or control the project's increment-source loss $J_s(d)$ and its complementary weighted moments.

The current finite-window certificate is inside previously published verification ranges and serves as a method check. The current progression-concentration deduction needs a separate comparison against existing near-extremal and spacing results; not finding it in this paper establishes no originality. Further work should start from the applicable contact and transfer theorems and state the exact unproved tail or joint estimate that a FIB observation would add. Reproving the supporting-line construction, recursive nesting, or another already-covered finite Robin interval is not by itself progress beyond these sources.

## Quantitative contact restrictions that may be reused

The following are stated in the same v1 primary, §§3.5–3.7, printed
pp.9–14. They are literature suppliers, rather than new recursive FIB
results. Let

$$
S_j(p)=p+\cdots+p^j,\qquad
\eta(p,j)=\frac{\log(1+1/S_j(p))}{\log p}\quad(j\ge1).
$$

For an actual arithmetic contact $n$ of order $k$ in Theorem 3.9, the
additional hypothesis is that $t\mapsto F(\log t)$ is increasing and
concave on $t\ge\log n_*$. At the same contact, with $b_p=v_p(n)$, one
common positive parameter obeys

$$
\frac{(1+1/S_{b_p+1}(p))^k-1}{k\log p}
\le\varepsilon
\le\frac{1-(1+1/S_{b_p}(p))^{-k}}{k\log p};
\tag{Q1}
$$

the left inequality is for every prime, and the right is only for
$p\mid n$. The theorem also makes this $n$ a unique classical CA
maximizer at that parameter. Thus these are joint restrictions on one
actual exponent vector, not independently attainable per-prime extrema.

Write

$$
\varepsilon_-(n)=\max_{q\ \mathrm{prime}}\eta(q,b_q+1),\qquad
\varepsilon_+(n)=\min_{p\mid n}\eta(p,b_p),\qquad
w_{\rm CA}(n)=\varepsilon_+(n)-\varepsilon_-(n).
$$

Proposition 3.11, printed p.12, states, for a prime $q$ attaining the
first maximum,

$$
w_{\rm CA}(n)>
\frac{k}{2}\varepsilon_-(n)^2\log q.
\tag{Q2}
$$

This width bounds the possible contact orders of a fixed integer. It is
not a lower separation bound on every pair of classical critical
parameters. In particular, it does not resolve coincident parameters;
Remark 3.14 explicitly notes that intermediate tied CA maximizers are
excluded from these concave arithmetic families.

Corollaries 3.8 and 3.10 give eventual divisibility by every fixed integer
and, under the concavity condition, a divisibility chain of first
contacts. Theorem 3.12 is specifically about changing the order: for
$0<\alpha\le1$, $m_k=\min A_k(\alpha,1)$ and $R_k=m_{k+1}/m_k$,

$$
\limsup_{k\to\infty}\frac{\log(1+\omega(R_k))}{k}
=\limsup_{k\to\infty}\frac{\log(1+\Omega(R_k))}{k}
=\frac1\alpha.
$$

The paper leaves unbounded prime counts between consecutive members of
one fixed level unresolved. None of these conclusions transfers merely
by calling the [selected global Robin maximizer](../Arith/caveney2012sacaga.md)
a higher-order contact. Maximum preservation is supplied by the different
construction in §4; the growth and exponent conclusions above are not
stated for that construction.

## A claimed convex-hull proof does not supply the positive margin

A separate preprint by Wonbin Seo, *On the Asymptotic Stability of the
Robin Inequality via the Convexity of Colossally Abundant Numbers*,
[Zenodo record 17919096](https://doi.org/10.5281/zenodo.17919096),
published 13 December 2025, claims an unconditional proof of Robin on
all CA integers above 5040. The inspected nine-page PDF has SHA-256
`36efc7dc4342973954f39d6cb1a45b4c99b0a90006b5ea218cbd27e42bea9f46`;
its MD5 matches the record metadata. The relevant passages are Table 1,
printed p.3, Theorem 5.1, p.6, and Theorem 8.1 and Appendix A.2,
pp.7–8. This assessment concerns those printed definitions and proof
steps; it does not certify the cited Dusart estimates, figures or
claimed interval computations, and adds no Lean result.

Theorem 8.1 defines $R(n)=\sigma(n)/n$, but Table 1 gives
$R(5040)=1.7909$. The exact divisor response at that integer is

$$
R(5040)=\frac{31}{16}\frac{13}{9}\frac65\frac87
=\frac{403}{105}>3.
$$

Thus the table does not use its theorem's stated quantity. Its printed
positive gap cannot be used as a certificate with those definitions.
In particular, a different normalization must also transport the budget
and the comparison; changing the response alone does not preserve a
Robin margin.

Appendix A.2, equation (5), asserts an Euler-product upper bound

$$
\prod_{p\le x}(1-p^{-1})^{-1}
<e^\gamma\log x\left(1+\frac{0.2}{(\log x)^2}\right).
$$

The positive error term lies above $e^\gamma\log x$. Besides needing a
justified relation between this cutoff $x$ and the actual CA integer,
this upper bound does not yield the positive safety margin claimed in
equation (6) and Theorem 5.1. Even an already-transported upper bound
$R(n)<B(n)+\varepsilon(n)$, with $\varepsilon(n)>0$, gives only

$$
B(n)-R(n)>-\varepsilon(n),
\qquad B(n)=e^\gamma\log\log n.
$$

It supplies no positive lower bound. Theorem 8.1's induction invokes a
positive initial margin and a transition justified by decreasing prime
reciprocals; the inspected argument gives no quantitative comparison
that pays the missing signed error at every transition. The convex-hull
description alone does not pay that comparison. The claimed proof
therefore supplies neither the required positive Robin margin nor the
[selected source's complete signed-tail estimate](polak2026finiterobinca.md).
This identifies a gap in the source's justification, without settling
Robin or RH.
