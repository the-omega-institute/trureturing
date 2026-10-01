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

The supporting-line description of classical colossally abundant numbers is older than this preprint: the introduction cites Alaoglu–Erdős for the prime-increment optimization and Musin's earlier work for the convex-envelope description. The new version develops higher-order contacts and the stated preservation and growth theorems. A local FIB reformulation must not relabel either body of work as an original geometric discovery.

For the [project's theory](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md), this source addresses a gap that the restricted family $N_g=1+F_r g$ does not fill: an explicit theorem retaining the full RH test when the observed family is reduced. It does not itself prove Robin on that Fibonacci family, or control the project's increment-source loss $J_s(d)$ and its complementary weighted moments.

The current finite-window certificate is inside previously published verification ranges and serves as a method check. The current progression-concentration deduction needs a separate comparison against existing near-extremal and spacing results; not finding it in this paper establishes no originality. Further work should start from the applicable contact and transfer theorems and state the exact unproved tail or joint estimate that a FIB observation would add. Reproving the supporting-line construction, recursive nesting, or another already-covered finite Robin interval is not by itself progress beyond these sources.
