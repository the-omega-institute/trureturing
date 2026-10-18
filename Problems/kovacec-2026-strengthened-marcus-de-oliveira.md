---
slug: kovacec-2026-strengthened-marcus-de-oliveira
bibkey: kovacec2026strongermoc
doi: null
url: https://www.mat.uc.pt/preprints/ps/p2611.pdf
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/KovacecStrengthenedMarcusDeOliveiraRefutation.result
---

# The strengthened Marcus–de Oliveira conjecture has a three-dimensional counterexample

## Problem

A. Kovačec, *A conjecture more precise and stronger than the one by Marcus and de Oliveira*,
DMUC Preprint 26-11, v1, Conjecture 7, p. 5:

> Given any two n-multisets of complex numbers A, B such that a Jordan curve J and the bounded component J(A, B) are defined, there holds ∆(A, B) ⊆ closure(J(A, B)).

[The source note](../Library/Eigenstructure/kovacec2026strongermoc.md) gives the
definitions and URL. [Preregistration #17803](https://github.com/the-omega-institute/trureturing/issues/17803)
specifies the exact witness and the literal Lean conventions. The resolution is **Refuted**.

### Statement echo

| Source clause | Lean counterpart | Fidelity and scope |
| --- | --- | --- |
| Any two $n$-multisets of complex numbers | `claim` quantifies over every natural `n` and `a b : Fin n → ℂ` | Functions retain multiplicities; no restriction on the spectra is added. |
| $z_\sigma=\prod_i(a_i+b_{\sigma(i)})$ | `sigmaPoint` | The product ranges over all `Fin n`; permutations are `Equiv.Perm (Fin n)`. |
| $\Delta=\{\det(D_A+UD_BU^*):U\in U(n)\}$ | `detRange` | `Matrix.diagonal`, `Matrix.unitaryGroup`, `star` and determinant give the literal expression. |
| Permutations differing by one transposition | `graph` | Union of the real closed segments for `sigma` and `sigma * Equiv.swap i j`, with `i ≠ j`. |
| Every positive prescribed distance admits an unobstructed segment | `exterior` | All real `M > 0`, a complex endpoint at distance `M`, and disjointness from the whole graph. |
| Exterior boundary is a Jordan curve | `IsJordanCurve` applied to the exterior frontier | The entire boundary is the range of a continuous injective map from `Circle`. |
| The bounded component of the complement of the boundary | `connectedComponentIn` at each point outside that frontier, with `Bornology.IsBounded` | Every bounded component is quantified. Under Jordan separation this is the source's unique bounded component; no Jordan curve theorem is assumed in Lean. |
| $\Delta\subseteq\overline{J(A,B)}$ | The inclusion in `claim`; `result` proves its negation | One bounded component containing zero suffices to refute the universal claim. |

The endpoint parameter and boundedness hypothesis identify the source's component;
they do not restrict the counterexample's determinant range. No source clause is dropped.

## Motivation

The transposition graph is a smaller geometric object than the convex hull of all
permutation products. A strengthened containment in its exterior-boundary region
would constrain determinants more sharply than the original Marcus–de Oliveira conjecture.
Three-coordinate orthogonal mixing separates those two proposed bounds.

## Gap

The preregistration's source reading and the supplied literature screen locate no
settlement of Conjecture 7 in the searched sources. The live preprint was read as
byte-identical to v1; the checked DMUC listing contains no later version. The
OpenProblemsInNLA MI-05 entry concerns the original convex-hull conjecture.
These are bounded literature readings, with completeness **ASSUMED-UNVERIFIED**.
They do not establish exhaustive novelty clearance.

## Route

Use
$a=(-3-i,-5-2i,4-3i)$, $b=(-2+i,4+3i,-2-5i)$ and

$$Q=\frac17\begin{pmatrix}-3&-2&6\\-2&-6&-3\\-6&3&-2\end{pmatrix}.$$

The determinant is $d=(2864+1840i)/49$. The six permutation products, in
lexicographic permutation order, are
$z_1=-30-50i$, $z_2=280+280i$, $z_3=-130+10i$,
$z_4=-28-56i$, $z_5=232+376i$, $z_6=24-20i$.
The nine transposition edges are $12,13,16,24,25,34,35,46,56$.

The closed x-monotone hexagon $P$ has cyclic vertices
$z_3,z_5,z_2,r,z_6,z_4$, where $r=(7672+4424i)/155$ is the intersection
of edges $24$ and $56$. Its lower boundary has successive affine pieces
$(-11x-1260)/17$, $(9x-476)/13$, $(99x-3416)/52$, $(12x-280)/11$;
its upper boundary has pieces $(183x+25600)/181$ and $-2x+840$.
All graph edges lie in $P$ and its frontier lies on graph edges.

The exterior is $P^c$, and its frontier admits a continuous injective circle
parametrization. The component containing zero is bounded, and its closure lies
in $P$. But $7672/155<\operatorname{Re}d<280$ and
$12\operatorname{Re}d-280-11\operatorname{Im}d=408/49>0$,
so $d$ lies below the lower boundary and outside $P$.

## Falsifier

This refutation would fail if the specified matrix were not unitary, the
determinant value were incorrect, the exterior boundary failed to be Jordan,
or the chosen component were unbounded or contained the determinant in its closure.
The private theorems named below discharge each obligation. Equality of the entire
component with the polygon interior, or of its closure with $P$, is unnecessary
and is not claimed as a separate kernel-checked statement.

## Evidence

The settling declaration is
`D5/S3/Quantum/Matrix/KovacecStrengthenedMarcusDeOliveiraRefutation.result`.
Its type is the literal negation of `claim`. Private `q_unitary`,
`determinant_exact`, `d_mem_detRange`, `graph_eq_edges`, `graph_subset_P`,
`frontier_subset_graph`, `exterior_eq`, `exterior_frontier`, `jordan_frontier_P`,
`component_bounded`, `component_closure_subset_P` and `d_not_mem_P` supply the
matrix, graph, topology and exclusion on the result's proof path.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
There is no other public theorem and no Reg mirror or claim of `declared_validated` registration.

### Experiment

[The pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/d78aded435ed2f855c3fcdeefb9c5c46b20fb994/docs/reports/kovacec-2026-strengthened-marcus-de-oliveira)
contains `check.py`, SHA-256
`86064b685700056de3980d55d30dee520609991d06899a3061eaeed4515ce205`.
Command: `python3 -I docs/reports/kovacec-2026-strengthened-marcus-de-oliveira/check.py`;
exit 0, `ALL_OK`; the executed file is byte-identical to that committed blob.
Exact rational arithmetic checks $QQ^T=I$, the determinant, the six permutation
products, nine edges, polygon breakpoints and segment containment, and the
separation $408/49$ (vertical gap $408/539$).
The family checks cover exactly $s=9,3481/400,13689/1600$; each has rational
$\sqrt{s}$, an orthogonal matrix and a determinant below $P$.
This program does not verify a uniform interval or perturbations of the spectra.

## Triage

Tier 1; **Refuted**;
`admission_basis: open-problem-resolution (#17803; Refuted)`.
The computational utility is `kind=certified-instance; basis=refutes`.

### What the settlement shows

1. **Mechanism — kernel-checked at the witness.** `exterior_eq` and
   `exterior_frontier` identify the exterior with $P^c$ and its frontier with
   $\partial P$; `frontier_subset_graph` puts every boundary side on graph edges.
   `jordan_frontier_P` constructs the Jordan parametrization.
   `component_closure_subset_P`, `d_mem_detRange` and `d_not_mem_P` yield `result`.
   The rational determinant escapes the region determined by the transposition graph.
   The displayed crossing coordinate is also an exact arithmetic fact: substituting
   $x=7672/155$ into both $(99x-3416)/52$ and $(12x-280)/11$ gives $4424/155$.

2. **Original MOC — proved in prose for this witness; general problem open.**
   The determinant remains in the convex hull, since
   $d=(1796/3479)z_1+(121/497)z_2+(836/3479)z_6$.
   All three coefficients are positive, their sum is one, and substitution gives
   real and imaginary parts $2864/49$ and $1840/49$.
   This exact convex combination separates Conjecture 7 from the original
   convex-hull assertion; it is not a new Lean theorem. The original MOC in
   unrestricted dimension remains open.

3. **Family — computed at three parameters; uniform extension open here.**
   The experiment verifies the reordered Householder construction with
   $v_s=(1,\sqrt{s},2)$ and $H_s=I-2v_sv_s^T/(s+5)$ at exactly
   $s=9,3481/400,13689/1600$. The preregistered formulas are
   $X(s)=8(29s^2-102s+1)/(s+5)^2$ and
   $Y(s)=8(47s^2-370s+443)/(s+5)^2$.
   Their separation identity is
   $12X-280-11Y=-96(17s^2-208s+478)/(s+5)^2$.
   **Sign criterion — proved in prose:** on $[17/2,9]$ the polynomial
   $17s^2-208s+478$ is increasing, because its derivative is at least $81$,
   and its value at $9$ is $-17$; hence the displayed separation is positive.
   The uniform determinant identity, location on the requisite polygon piece,
   and a full interval-family theorem are not kernel-checked or verified by
   the finite experiment. Stability under small perturbations of all six
   eigenvalues is a proposed extension and remains open here.

4. **Nearest surviving statements and consequences — source reading and prose.**
   The source's containment of individual transposition segments in the determinant
   range is not contradicted. The witness's convex-hull containment also survives.
   Neither implies containment in this smaller polygon. An argument requiring
   Conjecture 7's universal inclusion needs an additional hypothesis or a revised
   region; the source's independent results are not invalidated by this refutation.

5. **Corrected strengthenings — open.** Containment in a region selected by a
   different outer-cycle rule, containment for unitaries near permutation matrices,
   and the original MOC are not settled by this module. A corrected region must
   first be defined precisely; identifying it with $P$ would retain this counterexample.

6. **Literature — bounded reading, completeness ASSUMED-UNVERIFIED.**
   The supplied source screen identifies the live preprint with v1, no later
   version in the checked DMUC listing, and MI-05 as the original MOC.
   These readings do not certify completeness of the literature search.

7. **Experiment — computed.** The pinned program in the Evidence experiment
   entry verifies the exact witness, graph and polygon checks, and the three
   listed family parameters, with exit 0 and the stated SHA-256. The finite
   readings do not cover a uniform interval or perturbations of the spectra.

## ASSUMED-UNVERIFIED

Literature completeness remains unverified. The kernel result concerns the one
explicit three-dimensional witness. The finite experiment covers three family
parameters, not an interval, perturbed spectra or all unitary matrices. The
uniform family and perturbation extension, corrected strengthenings, and the
general original Marcus–de Oliveira conjecture remain open in this delivery.
