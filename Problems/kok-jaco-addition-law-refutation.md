---
slug: kok-jaco-addition-law-refutation
bibkey: kok2014finitejaco
doi: 10.48550/arXiv.1404.0484
triage: theorem
motivation_gids:
  - D5/S3/ConceptDynamics/GraphColoring/JacoMaximumDegree.result
---

# Refutation of the complete original Jaco addition law

## Problem

Kok, Fisher, Wilkens, Mabula and Mukungunugwa,
*Characteristics of Finite Jaco Graphs, J_n(1), n in N*,
arXiv:1404.0484v1, printed page 7, Theorem 2.10 (Conjectured), states:

> For the Jaco Graphs J_n(1), J_m(1) with n>=3, m>=3, n!=m we have
> Delta(J_(n+m)(1))=Delta(J_n(1))+Delta(J_m(1)), if J_n(1) or J_m(1)
> has a unique Jaconian vertex; Delta(J_n(1))+Delta(J_m(1))+1 otherwise.

This quotation normalizes only mathematical typography. Printed page 11
explicitly asks: “Prove Theorem (conjectured) 2.10.”
Definitions 1.1--1.4 and 1.7, printed page 2, give positive vertices,
the recursion i<j<=2i-d^-(v_i), finite truncation, ordinary total degree,
and Jaconian vertices as all maximizing vertices.

Write Delta_n=(jaco n).maxDegree and
U(n) iff exactly one v in Vertex n has degree Delta_n. The complete claim is

$$
\forall n,m\in\mathbb N,\quad 3\le n\Rightarrow3\le m\Rightarrow n\ne m\Rightarrow
\left[
 ((U(n)\lor U(m))\Rightarrow\Delta_{n+m}=\Delta_n+\Delta_m)
 \land
 ((\neg U(n)\land\neg U(m))\Rightarrow\Delta_{n+m}=\Delta_n+\Delta_m+1)
\right].
$$

Both branches and every admissible ordered pair are one assertion. OR is
inclusive. Unique means a unique vertex within that graph, not a unique
degree value across orders. The source's prime Jaconian designation alone
does not imply this uniqueness.

## Motivation

This is the explicit author-posed addition question. The existing exact
recursive graph and its all-order degree suppliers permit a direct test
without changing its carrier or treating a positive finite prefix as a proof.

## Gap

The primary TeX, PDF, definitions and open prompt authenticate this exact
question. Bounded screens of arXiv:1506.06538v1, arXiv:1404.1714v1,
arXiv:2507.16500v1, *On Deg-centric Jaco Graphs*
(DOI 10.17654/0974165825048), an arXiv title query returning 18 records,
and a public MathDB-backup manifest did not identify a specific complete
resolution in the inspected passages. Live MathDB contents were not acquired;
citation enumeration returned HTTP 429; *Reflections on Jaco Graphs*, the
named domination research note and unindexed sources remain explicit gaps.
Repository issue screening identified no matching old-addition settlement
in its bounded inspected scope. These readings certify neither worldwide
openness nor first-publication priority.

The exact event and both source-only forecasts were registered in
[issue #25870](https://github.com/the-omega-institute/trureturing/issues/25870#issuecomment-6590611674).
The graph suppliers are prior results. No specific earlier full resolution
is claimed absent beyond the inspected sources.

## Route

Reuse JacoDomPathDiameterRefutation.Vertex and jaco, the positive-label
finite truncation of JacoExponentialDominationRefutation's recursive
adjacency. JacoEndpointBeatty.endpoint_recurrence connects that array to
the source recursion. Forgetting orientation preserves ordinary total degree
because every unordered edge has exactly one forward arc.

JacoMaximumDegree.degree_formula gives
$d_n(i)=\min(i,n-\lfloor(i+1)/\phi\rfloor)$, and its result gives
$\Delta_n=\lfloor(n+2)/\phi\rfloor-1$ for every $n\ge2$.
Here $\phi=(1+\sqrt5)/2$ and natural subtraction is used.
Exact bounds $8/5<\phi<13/8$ yield the required floors.
For $n=3$, the degrees on the entire carrier are $1,2,1$, so $v_2$ is the
unique maximizing vertex and $\Delta_3=2$. The same supplier gives
$\Delta_{11}=7$ and $\Delta_{14}=8$. At $(3,11)$ the first branch would
require $8=2+7=9$. Thus the literal negation of the whole claim follows.
No assertion about the otherwise branch at this pair is needed.

The values are prior published data in arXiv:2507.16500v1, Table 1.
Their exact derivation here is an application of existing suppliers, not a
new numerical discovery. Conservative classification is
`proof_shape: bind-only`, `escape_witness: none`,
`admission_basis: open-problem-resolution` for the complete original question.
There is one public theorem, result; local arithmetic facts are used in its
proof. No supplier is reproved and no companion theorem is claimed.

## Falsifier

A mismatch in the positive-label source recursion, ordinary degree,
within-graph uniqueness, either branch, inclusive OR or the universal
ordered-pair domain invalidates the source correspondence. A contrary
exact computation of the degrees of J_3 or the three maximum degrees would
invalidate the proposed contradiction. The Lean proof discharges those
finite numerical obligations through the original graph suppliers.

## Evidence

The settling declaration is
`D5/S3/ConceptDynamics/GraphColoring/JacoAdditionLawRefutation.result`,
whose literal type is `Not claim`; claim has literal type `Prop`.
The owning Scribe attaches the typed `Refuted` resolution only to result,
using this dossier and the resolvable
[kok2014finitejaco source note](../Library/Certificates/kok2014finitejaco.md).
The full formula above includes both original branches and all admissible
orders. Source statement and attribution use CC BY 3.0; no executable code is copied from the article.

Current scoped compilation and declaration reports supply exact statement,
input identities and accepted axiom evidence. The typed resolution is
validated against current frozen membership and exact compiled declaration
identity. Local validation does not establish remote publication or
complete-delivery credit.

## Triage

The complete universal assertion is refuted by the pair (3,11). This does
not assert that every pair fails or settle a corrected addition law. The
existing degree formulas survive unchanged. A classification of pairs on
which either addition identity holds is a separate unresolved question.

## ASSUMED-UNVERIFIED

Source-to-formal correspondence is a reading of the published definitions,
not a kernel theorem about author intent. Literature coverage and priority
remain bounded by the gaps above. Existing supplier audit limitations remain
those disclosed at
[issue #25698](https://github.com/the-omega-institute/trureturing/issues/25698#issuecomment-6582601274);
this refutation neither repairs nor asserts completion of those registrations.
Remote publication and required remote checks remain outside this dossier.
