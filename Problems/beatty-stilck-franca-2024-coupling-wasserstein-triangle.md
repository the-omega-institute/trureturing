---
slug: beatty-stilck-franca-2024-coupling-wasserstein-triangle
bibkey: beatty2025couplingwasserstein
doi: 10.1007/s00023-025-01557-z
url: https://arxiv.org/abs/2402.16477v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/CouplingWassersteinTriangleRefutation.result
---

# An order-one pure-state coupling distance violates the triangle inequality

## Problem

E. Beatty and D. Stilck França, *Order p quantum Wasserstein distances from
couplings*, arXiv:2402.16477v2, Annales Henri Poincaré, define countable
pure-state transport plans in Definition 8 and the distances in Definition 9.
The introduction states:

> Although many desirable properties of these W_p^d are proven in Sec. IV, establishing a triangle inequality remains a difficult open problem.

Appendix C states:

> the triangle inequality eludes us.

The settled assertion is the triangle inequality for every finite complex
dimension and all density matrices, with order one and the pure-state trace
distance of equation (81). It is the closed proposition `claim`; its negation
is `result`. Issue [#30901](https://github.com/the-omega-institute/trureturing/issues/30901)
is the preregistration. Definitions and versioned quotations are in the
[literature note](../Library/Convexity/beatty2025couplingwasserstein.md).

## Motivation

The problem distinguishes a transportation infimum over common pure-state
decompositions from the dual norm lower bound in Proposition 23, equation
(62). A triangle inequality for the first quantity does not follow merely
from the triangle inequality for that lower bound.

## Gap

The supplied source information records the original open question, Borsoni
arXiv:2512.01722v5 Section 3.3.3, and Miller arXiv:2609.03769. The Borsoni
quotation is: "the cases p≠2 or other ground distances remain open."
Miller's positive result concerns order two and the Hilbert–Schmidt ground
distance. No additional webpage retrieval or exhaustive literature screen
is claimed. The source-screen conclusion is `not-found-in-searched-scope`.

## Route

In dimension three put

$$
p=(4/5,3/5,0),\quad q=(3/5,4/5,0),\quad
P=|p\rangle\langle p|,\quad Q=|q\rangle\langle q|,\quad
R=(P+Q)/2,\quad s=1/100,
$$

and let $E_k$ project onto coordinate $k$, numbered from zero. Define

$$
B=R-sE_0=
\begin{pmatrix}49/100&12/25&0\\12/25&1/2&0\\0&0&0\end{pmatrix},
\qquad\sigma=B+sE_2.
$$

The plan $\{(1/2,p,p),(1/2,p,q)\}$ gives $W_1(P,R)\le7/50$.
For a decomposition with rational unit vectors, take

$$
u=(119/169,120/169,0),\qquad
B=\frac{28561}{29750}|u\rangle\langle u|
  +\frac7{500}E_0+\frac{19}{1190}E_1.
$$

The three positive coefficients sum to $99/100$. Match these three pure
components to themselves and transport the remaining weight $s$ from
$e_0$ to $e_2$. This gives $W_1(R,\sigma)\le1/100$.

For any plan with pure source $P$, every positive-weight source projector
is $P$. For a unit target vector $v$, writing
$t=|v_0|^2+|v_1|^2$ and $h=7/50$, the pointwise estimate is

$$
\sqrt{1-|\langle p,v\rangle|^2}
\ge th-\frac{|v_0|^2-|v_1|^2}{2}+|v_2|^2.
$$

The target marginal fixes the weighted coordinate masses to
$49/100,1/2,1/100$. Summing the estimate therefore gives

$$
T_1(Q)\ge-\frac9{25}\frac{49}{100}
 +\frac{16}{25}\frac12+\frac1{100}
 =\frac{96}{625}>\frac3{20}=\frac7{50}+\frac1{100}.
$$

Taking the infimum proves the strict triangle violation. Explicit plans
supply nonemptiness of each infimum used; costs are nonnegative.

The Lean encoding uses unit vectors in `Fin n → ℂ` and the existing
`rankOneDensity`. Its ground distance is the square-root expression in
equation (81). Plans have natural-number indices and nonnegative weights.
Removing zero-weight entries gives strictly positive countable plans;
conversely an enumeration of a finite or countable plan, padded by zeros,
gives the natural-index form without changing either marginal or cost.
The explicit `HasSum weight 1` field is redundant for density marginals:
apply the matrix trace to either marginal sum and use trace one for every
unit-vector projector. This is an explanation of the encoding equivalence,
not a separately claimed formal equivalence theorem.

Every ground cost lies in $[0,1]$, so nonnegative weighted costs are bounded
termwise by the summable weight sequence. Thus the real `tsum` is the
ordinary convergent plan cost. The distance is the real `sInf` of these
costs, exactly the order-one specialization of equation (16).

## Falsifier

A restriction to finitely supported plans, omission of pure-source
rigidity, or a mismatch between the square-root ground distance and
source equation (81) would invalidate this route. The claim quantifies
over all natural dimensions and all positive semidefinite trace-one
matrices. The long-side estimate must hold for every admissible countable
plan, including complex amplitudes; an optimization over a chosen finite
family alone would not suffice.

## Evidence

The formal source is
`D5/S3/Quantum/QuantumChannels/CouplingWassersteinTriangleRefutation.lean`.
Its terminal statement is `result : ¬ claim`, with matching Blueprint
Scribe. The associated formalization concerns the order-one trace-distance
specialization, rather than a finite-plan approximation or a different
quantum coupling metric. Compilation, axiom and freeze evidence are read
from the current scoped report and canonical state rather than copied here.

## Triage

Tier 1 published open question, preregistered in #30901. The module's
admission basis is `open-problem-resolution`; the designated refutation
result is exempt from four-slot escape registration. Auxiliary lemmas are
private and have active consumers in the terminal proof.

| Statement | Evidence and boundary |
| --- | --- |
| The displayed matrices are density matrices and violate the order-one triangle inequality. | Proved in Lean by `result`, using `rho_density`, `tau_density`, `sigma_density`, `short_bound`, `middle_bound` and `long_bound`. |
| The rational decomposition of $B$, its coefficient sum $99/100$, and $96/625>3/20$. | Proved in Lean through the exact rational identities in `shared_left`, `shared_right`, `shared_mass` and the terminal strict comparison. |
| A positive-weight source term has the same ground cost as the pure source, for every target vector in the plan. | Proved in Lean by `pure_source_ground`, using the vanishing weighted orthogonal quadratic form and third-coordinate mass. |
| Ground costs lie in $[0,1]$, and every weighted plan cost is summable. | Proved in Lean by `ground_bounds` and `cost_summable`, with the normalized summable weight sequence as the dominating sequence. |
| The two short legs may choose different pure-state decompositions of the mixed midpoint. | The explicit plans are proved in Lean; the failure of a classical gluing argument is the structural interpretation. A shared quantum marginal does not identify the two midpoint decompositions term by term. |
| Equation (62) is strict in the trace-distance case for this pair. | Proved on paper, not separately formalized: $P-\sigma=\operatorname{diag}(3/20,-7/50,-1/100)$, hence $\frac12\|P-\sigma\|_1=3/20<96/625\le W_1(P,\sigma)$. Proposition 26 identifies the dual norm with the same $3/20$. |
| The order-two Hilbert–Schmidt triangle theorem remains valid. | Literature result supplied by the Miller reference. On pure-state projectors the Hilbert–Schmidt distance is √2 times the trace distance, so scaling Miller's order-two result also gives the order-two trace-distance triangle inequality; it does not settle order one. |
| The triangle inequality for $1<p<2$. | Unresolved here; this order-one counterexample supplies no conclusion for that range. |
| Exhaustive priority or absence of other resolutions. | Unverified; the source screen is bounded by the supplied quotations. |

## ASSUMED-UNVERIFIED

The cited manuscript and follow-up references were not independently
retrieved. The projective-vector and natural-index encoding correspondences
are explained in Route rather than established by separate Lean bridge
theorems. The trace-norm and dual-norm consequence in Triage is a paper
derivation and is not an additional formal terminal result. No exact value
of $W_1(P,\sigma)$ is asserted.
