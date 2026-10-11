---
slug: aloy-mullerrigat-tura-fadel-2024-three-outcome-pibi-validity
bibkey: aloy2024threeoutcomepibi
doi: 10.3390/e26100816
url: https://arxiv.org/abs/2406.11792v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/ThreeOutcomePermutationallyInvariantBell.result
---

# Validity of the five three-outcome PI Bell inequalities

## Problem

A. Aloy, G. Müller-Rigat, J. Tura and M. Fadel, *Deriving three-outcome
permutationally invariant Bell inequalities*, arXiv:2406.11792v1,
Entropy 26 (2024), 816, Section III.A:

> To give a concrete example, we propose for any $N>3$ the five 3PIBIs shown in Tab. III.

> At this point, for each conjectured inequality we have to prove that it is indeed valid for arbitrary number of parties $N$, or at least for all $N$ larger than a minimum number.

There are $N$ parties, inputs $x_i\in\{0,1\}$ and outcomes
$a_i\in\{0,1,2\}$. The one-party observables sum marginal probabilities;
the two-party observables sum products over ordered distinct parties.
The five symmetrized observables and all six coefficients of each
Table III row are retained literally in `P1`, `P2`, `Pt0`, `Pt00`,
`Pt01`, `Pt10`, `Pt11`, `bell` and `table`.

| Row | $(\alpha_1,\alpha_2,\alpha_3,\alpha_4,\alpha_5,\beta_c)$ |
| --- | --- |
| 1 | $(1,1,0,-2,0,0)$ |
| 2 | $(1,1,-2,-2,2,0)$ |
| 3 | $(-2,1,2,2,0,4)$ |
| 4 | $(-6,1,4,4,2,12)$ |
| 5 | $(-6,1,4,0,0,24)$ |

## Motivation

The settling node is
`D5/S3/Quantum/Entanglement/ThreeOutcomePermutationallyInvariantBell.result`.
It proves `claim`, the normalized finite-hidden-variable formulation
specified in [#15121](https://github.com/the-omega-institute/trureturing/issues/15121).
`G_nonneg`, `row3_small`, `row3poly_nonneg`, `countBell_nonneg`,
`deterministic_validity`, `model_nonneg` and `result` have
`proof_shape: content` after inlining the same-delivery helpers. The other
declarations are `bind-only` definitions, finite-sum bookkeeping or
polynomial identities, each with its named live consumer in the module
ledger. The module has `admission_basis: open-problem-resolution (#15121; Proved)`,
`escape_witness: G_nonneg, row3poly_nonneg` and `utility: none`. The integer
case estimates establish new nonnegative polynomials and survive the
normalization-only bypass test.
The theorem is uniform in the party count and probabilities, rather
than a fixed numerical instance.

## Gap

The source proposes all five rows. Row 1 is proved in the authors'
companion work; rows 2–5 are unsettled in the source and the literature
scope recorded in #15121. The preregistration names the question,
full quantifiers, tier-1 classification, literature readings and
finite-hidden-variable convention. No worldwide-priority claim follows
from this bounded literature screen.

## Route

For each hidden variable, choose both local responses independently.
The frozen `GreenClassWindowEntropy.windowLaw` is the actual product
mass; `windowLaw_sum_eq_one` supplies its normalization. The consumed
moment identities reproduce the one-party and distinct-party
two-party probabilities. `bell_average` expresses the Bell value as
an average of deterministic values with nonnegative normalized weights.

For deterministic counts $c_{ab}\in\mathbb N$, write
$A=c_{00}+c_{01}+c_{02}$, $B=c_{10}+c_{11}+c_{12}$,
$C=c_{00}+c_{10}+c_{20}$, $D=c_{01}+c_{11}+c_{21}$,
$R=A+B$, $S=C+D$ and $K=c_{00}+c_{01}+c_{10}+c_{11}$.
`deterministic_count_formula` gives the source's Table II expressions.
The row certificates reduce their signs to squares and nonnegative
products, with the integer case splits stated below.

## Falsifier

A normalized nonnegative finite local hidden-variable model with
$N>3$ and a negative Table III Bell value would refute `claim`.
A changed coefficient, exchanged input/outcome index or inclusion of
the equal-party terms would invalidate source fidelity.

## Evidence

`result : claim` is kernel-checked. The axiom closure of every public
declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},
\mathrm{Quot.sound}\}$. The canonical Blueprint has one
`OpenProblemResolutionClaim` with outcome Proved on this node.
The [Library note](../Library/QuantumBounds/aloy2024threeoutcomepibi.md)
provides the DOI, source URL and section/table locators.

The escape audit for the only new public theorem, `result`, is unfinished
under [#15148](https://github.com/the-omega-institute/trureturing/issues/15148):
exact `SourceSelection`, successful report decoding and current binding
evidence are missing. No Reg file or `declared_validated` claim is delivered.

## Triage

### What the settlement shows

| Item | Status | Evidence |
| --- | --- | --- |
| Deterministic reduction and the row mechanism | proved | Kernel-checked `bell_average`, `deterministic_count_formula`, `row1_certificate` through `row5_certificate`, `G_nonneg`, `row3poly_nonneg` and `countBell_nonneg`; all are consumed private declarations of this module. |
| Each bound is attained for every $N\ge2$ | proved in scratch Lean and by the row-1 argument below | The four saturating-strategy examples for rows 2–5 in the supplied `Exactness.lean` compile with exit 0; no exactness declaration is added to the module. |
| Validity for every $N\ge1$, including $1\le N\le3$ | proved | Private `model_nonneg` quantifies over every natural $N$ without a lower-bound hypothesis. |
| Count-vector, deterministic-strategy and symbolic readings | computed | The pinned experiment entry below, `python3 check.py 12`, exit 0. |
| Facetness for every $N$ | open | Neither `claim` nor a row certificate establishes affine dimension of a tight face. |
| Quantum violations | open | The local-model theorem does not estimate quantum correlations; the source refers their study to companion work. |

Row 1 has certificate $B_1=(A-C)^2+(B-D)^2+2(c_{00}+c_{11})$.
Row 2 has $B_2=(R-S)^2+2K$.
For row 3, `row3_small` handles $R\le1$, and its symmetric application
handles $S\le1$. For $R,S\ge2$ the identity is

$$
2B_3=(A-B)^2+(C-D)^2+(R-2)^2+(S-2)^2
 +4(R-2)(S-2)+2(R-2)+6(S-2)+4(R-K).
$$

The count relation $K\le R$ gives the last term's sign. With $t=u+v$,

$$
G(k,u,v)=6(k-1)(k-2)+t^2+(6k-7)t+2uv.
$$

For $k=0$ this is $(t-3)(t-4)+2uv$, for $k=1$ it is
$t(t-1)+2uv$, and for $k\ge2$ all displayed terms are nonnegative.
The consecutive-integer factors are nonnegative on natural inputs.
Rows 4 and 5 are

$$
B_4=G(K,c_{02}+c_{12},c_{20}+c_{21}),
$$

$$
B_5=G(c_{01},c_{00}+c_{02},c_{11}+c_{21})
 +G(c_{10},c_{11}+c_{12},c_{00}+c_{20}).
$$

For exactness, row 1 is saturated by assigning outcome 2 at both
inputs to every party: all five observables and its constant are zero.
For rows 2–5 use respectively $c_{02}=c_{20}=1$,
$c_{00}=c_{11}=1$, $c_{00}=c_{11}=1$ and $c_{01}=c_{10}=1$,
with $c_{22}=N-2$ and all other counts zero. For $N\ge2$ these
counts are realized by assigning the two displayed outcome pairs to the
first two parties and outcome pair $(2,2)$ to every remaining party.
Their total count is $N$. Substitution into the certificates gives
$R=S=1$ and $K=0$ for row 2; $A=B=C=D=1$ and $R=S=K=2$
for row 3; $G(2,0,0)=0$ for row 4; and two copies of $G(1,0,0)=0$
for row 5. Thus each Bell value equals zero. The four scratch Lean
examples quantify over every $N\ge2$. Their formulas are exactly the
literal `bell` and `table` expressions. These statements assert
attainment, not facetness.

The settlement supplies all-party validity for rows 2–5 and includes
the already known row 1 in the source's joint claim. Subsequent uses
of these rows as local bounds no longer require finite-$N$ enumeration
within the encoded finite local model. Facet claims and quantum
optimization still require separate arguments.

### Numerical readings

Experiment entry:
[check.py](https://github.com/the-omega-institute/trureturing-experiments/tree/3a78ba94e1293532c1584ec5f8bba4cc869a05ee/docs/reports/aloy-mullerrigat-tura-fadel-2024-three-outcome-pibi-validity).
Run `python3 check.py 12` from that directory with SymPy; exit code 0.
Script SHA-256: `d9353d6363b3a27bcaf8f64485cd19c2d98306289b4b2f580de81b06e3bdbd33`.

The tested scope is every nine-component count vector for
$1\le N\le12$, every deterministic strategy for $1\le N\le4$,
and the four certificate identities by symbolic algebra.
The final reading is
`NMAX=12 minima(N=1..4)=[[0, 0, 0, 0, 12], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]] identities_ok=True bad=0`.
These finite computations support the checks; the uniform validity
statement is supplied by the kernel-checked theorem.

## ASSUMED-UNVERIFIED

Literature-index completeness and worldwide priority are unverified.
The finite-hidden-variable convention is binding in #15121; an
integral-representation theorem for arbitrary measurable hidden-variable
spaces is not formalized here. Four-slot escape registration remains
unfinished under #15148. Facetness and quantum violations are open.
