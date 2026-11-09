---
slug: op-grsz2023mrd
bibkey: gruica2023mrdcolumnlimit
doi: 10.1137/22M1486893
url: https://arxiv.org/abs/2201.07193v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnLimit.result
---

# The fixed-field column limit of MRD code density

## Problem

Gruica, Ravagnani, Sheekey and Zullo, *Rank-Metric Codes, Semifields, and
the Average Critical Problem*, arXiv:2201.07193v1, Problem A; published
Problem 2.6, SIAM Journal on Discrete Mathematics 37(2), 1079–1117,
asks, in part, for the asymptotic density of maximum rank distance codes
as the column count tends to infinity. The
[source note](../Library/FiniteGeometry/gruica2023mrdcolumnlimit.md)
contains the verbatim question and locators. The supplied fixed-field
claim is preregistered in [#26598](https://github.com/the-omega-institute/trureturing/issues/26598).

For a finite field of cardinality $q$, fixed $n\ge2$ and $1\le d\le n$,
the answer is

$$
\lim_{m\to\infty}\delta_q^{\rm rk}(n\times m,m(n-d+1),d)
=\begin{cases}1&d=1,\\P(q)^{{n\brack d-1}_q}&2\le d\le n,\end{cases}
\qquad P(q)=\prod_{j=1}^{\infty}(1-q^{-j}).
$$

The exact density is one when $d=1$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Fixed prime power $q$ | A finite field carrier with `q = Fintype.card 𝔽` | All finite fields |
| $n\ge2$, $1\le d\le n$ | The three inequalities in `claim` | No additional limiting hypothesis |
| $k=m(n-d+1)$ | `mrdDimension` | Natural subtraction agrees under $d\le n$ |
| Matrices over the field | `Matrix (Fin n) (Fin m) 𝔽` | Literal ambient space |
| Minimum distance at least $d$ | `MinDistanceAtLeast` quantifies over every nonzero matrix of the subspace | Literal rank condition |
| Density in Notation 2.5 | `density`, using `GoodCodes` and `AllCodes` | Ratio of the two finite cardinalities |
| Gaussian coefficient | `gaussian` | Literal finite product over $0\le h<b$ |
| Euler product | `P` | Index $j+1$ enumerates positive integers |
| Fixed-parameter column limit | `Filter.Tendsto` at `Filter.atTop` in `result` | The tail $m\ge n$ is unchanged |
| Distance-one case | `density_one` and the corresponding branch of `result` | Exact density and its limit |

The source defines codes to be nonzero. The convention extends counting to
zero-dimensional subspaces, including the $m=0$ prefix. For the source tail
$m\ge n\ge2$, the prescribed dimension is positive; that extension changes
neither the source density nor its limit. All named declarations in this
echo belong to the four `MRDDensityColumn*` modules in
`D5.S3.Combinatorics.SubspaceCodes`.

## Motivation

The settling declaration is
`D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnLimit.result`.
Each of the four new modules has `generality: G`, `utility: none`, and
`admission_basis: escape-witness`. Their respective witnesses are
`MRDDensityColumnSampling.MRDDensityCounting.noninjective_map_count`,
`MRDDensityColumnTensor.MRDDensityTensor.tensor_dimension_equality`,
`MRDDensityColumnReduction.MRDDensityMobius.prod_error`, and
`MRDDensityColumnLimit.MRDDensityMoments.kernel_frame_moment_limit`, under
the common namespace above. These are general counting, tensor and limit
arguments. The finite experiment is supporting evidence.

## Gap

The literature screen in #26598 distinguishes the fixed-field column limit
from large-field limits, extension-field samples and known upper bounds.
It reads the source, its published version, the earlier exact $n=d=2$
case, Gruica–Ravagnani's column-growth bounds, Gruica's thesis, and the
related works named there. No settlement of the full supplied formula was
found in that searched scope. The case $n=d=2$ is prior work, rather than a
new special case. Citation completeness is `ASSUMED-UNVERIFIED`.

## Route

Write $r=n-d+1$. A generator is a linear map to the matrix space.
Conditioned on injectivity, its image is uniform among subspaces of dimension
$mr$. The rank-distance condition is equivalent to injectivity of its
restrictions associated to every $r$-dimensional subspace of the row space.
There are ${n\brack r}_q={n\brack d-1}_q$ such subspaces.

For distinct $r$-dimensional left subspaces $U_i$, and right subspaces $V_i$,
put $W=\sum_i V_i$ and $T=\sum_i(U_i\otimes V_i)$. The tensor argument
gives $\dim T\ge r\dim W$, with equality exactly for an independent
family $(V_i)$. Thus dependent frames incur a strict dimension surplus.
For every fixed moment tuple this bounds their total weight by a constant
times $q^{-m}$. The direct-frame contribution tends to one.

The normalized mixed Gaussian kernel moments consequently tend to the
product of inverse general-linear-group cardinalities. Finite multivariate
Möbius truncation bounds the difference between the joint zero-nullity
indicator and a polynomial in those moments. The limiting error tends to
zero with the truncation level. The scalar series is identified with
$P(q)$ by finite Gaussian identities and a dominated limit. Joint
injectivity therefore has limit $P(q)^L$ for a fixed family of size $L$.
The generator's injectivity probability tends to one for $d\ge2$;
conditioning gives the claimed density. The distance-one identity is
handled separately.

## Falsifier

The settling claim quantifies over every finite field and every admissible
fixed $n,d$. A counterexample to that quantified limit would contradict
`result` in the checked formal system. Finite small-column densities need
not equal the limit. The statement gives no limit with moving parameters
and no full joint distribution at nonzero nullities.

## Evidence

The four modules and the published Gaussian owner have corresponding
Blueprint Scribes. The settling result displays the complete proposition.
Its axiom closure, and that of every public declaration, is contained in
`{propext, Classical.choice, Quot.sound}` subject to the current compiled
readings reported by the delivery. Lean is the mathematical evidence;
the dossier is exposition.

The escape audit is unfinished:
[#27411](https://github.com/the-omega-institute/trureturing/issues/27411).
It covers all new public theorems and the published owner declarations.
The missing evidence is the typed source reconstruction and statement-to-law
bridge, together with variation, sensitivity and observational dependence.
No validated four-slot registration is claimed.

### Finite experiment

[Pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/87c2172ec43c2a70ceaf9d0ddc77363694a4b20a/docs/reports/grss-mrd-density-fixed-field-column-limit).
The checked program is `check.py`, SHA-256
`1ff617c874dfe76ce3ffec33c4a6afe7971bcfe0e0fa098ea211d748e1e94967`.
An exact copy from that commit was run with
`python3 /Users/auric/.sshx/93f2f8d6510a80c9d190d440/attempt-1/experiments-check.py`,
exit 0, terminal result `ALL_CHECKS_OK`.

| Tested parameters $(q,n,d,m)$ | Exact density | Counted objects |
| --- | --- | --- |
| $(2,2,2,2)$ | $2/35$ | 12 MRD generator maps among 210 injections |
| $(2,2,2,3)$ | $16/465$ | 8064 MRD generator maps among 234360 injections |
| $(2,3,2,3)$ | $192/788035$ | 192 good codes among 788035 subspaces |

The checker also verifies ${2\brack1}_2=3$, ${3\brack1}_2=7$ and rational
partial-product brackets. This is finite evidence in exactly the listed
scope, and supplies no asymptotic or moving-parameter theorem.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Evidence |
| --- | --- | --- |
| Exact supplied fixed-$q,n,d$ column-limit claim, including density exactly one for $d=1$ | Proved; kernel-checked | `MRDDensityColumnLimit.result`; private `MRDDensityColumnReduction.density_one` |
| Tensor lower bound and directness equality criterion over arbitrary fields, finite-dimensional ambient spaces and distinct equal-dimensional left subspaces | Proved; kernel-checked | Private `MRDDensityColumnTensor.MRDDensityTensor.tensor_dimension_lower_bound` and `tensor_dimension_equality` |
| Explicit constant times $q^{-m}$ bound for each fixed dependent-frame moment tuple | Proved; kernel-checked | `MRDDensityColumnTensor.MRDDensityTuples.nondirect_tensor_weight_sum` |
| Joint zero-nullity probability tends to $P(q)^L$ for each fixed finite family | Proved; kernel-checked | Private `MRDDensityColumnLimit.blocks_probability_limit`, for positive common dimension |
| Mixed Gaussian moments tend to the product of inverse GL cardinalities, with vanishing multivariate Möbius truncation error | Proved; kernel-checked | Private `MRDDensityColumnLimit.MRDDensityMoments.kernel_frame_moment_limit`, `MRDDensityJoint.joint_zero_limit_of_moments`, and `MRDDensityColumnReduction.MRDDensityAnalysis.mobius_tail_limit` |
| Listed small densities and `ALL_CHECKS_OK` | Computed; finite experiment | The pinned program, command, exit code and SHA-256 above |
| Full joint distribution at arbitrary nonzero nullities | Open | No delivered theorem establishes it |
| Parameters $q,n$, family size or moment order growing with $m$ | Open | All limit theorems fix these parameters |

The decisive mechanism is the strict tensor dimension surplus for dependent
frames, followed by finite Möbius truncation. The tensor statement extends
to arbitrary fields; the probability and counting limits use finite fields.
The joint-probability item has the theorem's explicit positive-common-dimension
hypothesis $r\ge1$. At dimension zero the source and target of each block
map are zero, so every block map is injective and its probability is one;
this elementary explanation is not an additional Lean theorem. That case
does not have the asserted $P(q)^L$ limit for a nonempty family. The MRD
application has $r=n-d+1\ge1$ throughout.
The fixed-family joint zero-nullity result applies beyond the family of all
subspaces used for MRD codes. These extensions have the hypotheses stated
in the corresponding declarations. No quantitative convergence rate for
the complete density is asserted. The source's other questions, including
arbitrary dimensions and the large-field direction, retain their own
evidence and are not settled by this result. No source theorem is retracted.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The screen's citation
census is incomplete because the recorded OpenAlex and Semantic Scholar
requests were unavailable or rate-limited, and some later publisher pages
exposed metadata without full text. The claimed mathematical settlement is
limited to the stated fixed-field column-growth formula. The unfinished
escape audit is tracked in #27411 and is not a validated registration.
