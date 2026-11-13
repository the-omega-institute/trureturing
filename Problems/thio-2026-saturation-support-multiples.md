---
slug: thio-2026-saturation-support-multiples
bibkey: thio2026tight
doi: null
url: https://arxiv.org/abs/2611.04009v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Magic/ThioSaturationRefutation.result
---

# Saturation outside dimension-multiple coordinate supports

## Problem

Jonathan J. Thio, Stephan De Bièvre, Crispin H. W. Barnes and David R. M.
Arvidsson-Shukur, *Tight Quasiprobabilistic Entropic Uncertainty Relations for
Discrete Quantum Systems*, arXiv:2611.04009v1, Appendix A, A1.p8.1, after the
construction with $D=\delta d$, $1\le\delta\le d$, ask:

> Whether these are the only possible D-values for which saturation occurs is not clear in general. We do have the following result, nevertheless.

The binary assertion registered in
[#28204, comment 6725761488](https://github.com/the-omega-institute/trureturing/issues/28204#issuecomment-6725761488)
is the following complete universal statement. For every positive finite total
Hilbert dimension $d$, every allowed representation $R$, every
$\tau\in[1/d,1]$, and every actual complex $d$-by-$d$ Hermitian
positive-semidefinite trace-one matrix $\rho$ with
$\operatorname{Tr}(\rho^2)=\tau$ and real nonnegative coordinates,

$$
H_R(\rho)=-\ln\tau+\ln d
\quad\Longrightarrow\quad
\exists\delta\in\mathbb Z,\quad
1\le\delta\le d\quad\text{and}\quad D_R(\rho)=\delta d.
$$

The allowed representations are every MUB Kirkwood–Dirac representation from
two orthonormal bases with $|\langle a|b\rangle|^2=1/d$, and precisely the
paper's odd-local-dimensional Gross–Wigner representations of Eqs. (19)–(20)
and their stated $n$-fold tensor extensions, with total dimension $d=q^n$.
Arbitrary strongly self-dual frames and other Wigner conventions are excluded.
The coordinate carrier $\Lambda$ has $d^2$ elements. In the convention of
Eq. (9),

$$
Q_\lambda^R(\rho)=\operatorname{Tr}(\rho S_\lambda^\dagger),\qquad
D_R(\rho)=\#\{\lambda:Q_\lambda^R(\rho)\ne0\},\qquad
H_R(\rho)=-\sum_{\lambda\in\Lambda}Q_\lambda^R(\rho)\ln Q_\lambda^R(\rho).
$$

Every complex coordinate must be real and nonnegative, including zero. The
logarithms are natural and the entropy contribution at zero is zero. $D$ is
coordinate support cardinality, never matrix rank. Both purity endpoints are
included. Empty purity levels receive no invented minimum or infimum
convention. An actual allowed counterexample answers this entire binary
question NO. The wider Appendix A objective of classifying all actual bound
attainments at every purity in every stated representation remains unresolved.

## Motivation

The middle inequality in Eq. (21), restated in Eq. (39), bounds entropy using
purity. Appendix A gives dimension-multiple supports as sufficient examples of
attainment and explicitly asks whether they exhaust the possibilities. A
nonmultiple support attained by an actual allowed density matrix distinguishes
that binary necessity question from the broader classification problem.

## Gap

The source explicitly leaves the only-$D=\delta d$ question unclear in general.
The registered event fixes this necessity question independently of the wider
attainment classification. The preregistration comment precedes the mathematical
execution and retains the entire quantified statement.

The bounded literature scope is the primary preprint and the passages credited
in [the source note](../Library/Entropy/thio2026tight.md): Gross
quant-ph/0602001v3; Prakash–Singhal 2408.00436v2, II.B,
Eqs. (II.14)–(II.19); Prakash 2003.02717v2, Section 3,
Eqs. (14), (21)–(24), and Sections 5 and 7; and Bozzetto–Hance
2605.09558v3, III.2, Eqs. (7)–(9), Table 2 and XI.4. These passages supply
known parity, antisymmetric-qutrit, depolarized-Strange and Wigner-positivity
ingredients. An explicit settlement of Thio's binary support question was
`not-found-in-searched-scope`. This is an attributed bounded source reading,
not an exhaustive literature, priority or worldwide-openness claim.

## Route

Use the paper's exact Gross convention at $q=d=3$, $n=1$, with basis
$\mathbb Z/3\mathbb Z$. Write $P|j\rangle=|-j\rangle$ and $v=(0,1,-1)$.
The witness is

$$
\rho=\begin{pmatrix}
1/4&0&0\\
0&3/8&-1/8\\
0&-1/8&3/8
\end{pmatrix}
=\frac{3I-P}{8}=\frac I4+\frac{vv^\dagger}{8}.
$$

The last expression supplies complex positive semidefiniteness; the trace is
one. The source-defined origin sum is $P/3$. Its displaced operators give

$$
Q_{ab}(\rho)=
\begin{cases}0&(a,b)=(0,0),\\1/8&(a,b)\ne(0,0).\end{cases}
$$

Thus $\tau=3/8\in[1/3,1]$, $D=8$, and
$H=\ln8=-\ln(3/8)+\ln3$. There is no integer $\delta$ with
$1\le\delta\le3$ and $8=3\delta$. These are the witness calculations used by
the Lean proof of the literal negation; no numerical experiment or inferred
physical realization is substituted for them.

## Falsifier

The refutation would fail to answer the registered event if the operators used
another phase or normalization, if the coordinate pattern had no actual complex
density matrix, if entropy omitted zero or used another logarithm, or if only a
restricted source assertion had been negated. The following source map identifies
the corresponding definitions in
`D5/S3/Quantum/Magic/ThioSaturationRefutation.lean`.

| Source clause | Lean correspondence |
| --- | --- |
| Eq. (9), complex trace with conjugate transpose | `coordinate`; realness and nonnegativity remain explicit in `claim` |
| Eq. (17), both complete orthonormal MUB bases | `columnProjector`, `IsMUBKD` |
| Eqs. (19)–(20), positive-phase displacement and normalized origin sum | `grossDisplacement`, `grossOrigin`, `grossLocal` |
| Stated odd-local tensor extensions, $d=q^n$ | `grossTensor`, `IsGross`, with positive odd $q$, positive $n$, basis and label bijections, and unitary change of basis |
| Exactly the union of the two source classes | `IsSourceFrame` |
| Actual Hermitian PSD trace-one state | `Matrix.PosSemidef` and trace-one premises of `claim`; `rho_density` supplies the witness |
| Coordinate support, including tests against complex zero | `coordinateSupport` |
| Natural-log Shannon sum and zero contribution at zero | `coordinateEntropy`, reusing `shannonEntropy` and `Real.negMulLog` |
| Eqs. (21)/(39), purity-dependent equality and both endpoints | `claim` defines $\tau$ from $\rho$ and includes $1/d\le\tau\le1$ |
| Appendix A A1.p8.1, only dimension-multiple supports | `claim` and `result : ¬ claim` |

The use of a natural-number $\delta$ is equivalent to the registered integer
quantifier under $1\le\delta\le d$. Defining $\tau$ from the matrix instead of
quantifying a redundant variable retains every registered purity. No convex-hull
premise from Lemma 2 is added. The witness uses the allowed Gross branch; a
counterexample in this branch refutes the universal assertion over the union.

## Evidence

The mathematical source is
`D5/S3/Quantum/Magic/ThioSaturationRefutation.lean`; the exposition and typed
resolution binding are in its Blueprint Scribe. `claim` has compiled type
`Prop`, and `result` has literal compiled type `Not claim`. The existing scoped
compiled evidence covers the selected target, its utility inputs and import
closure, with only `Classical.choice`, `Quot.sound` and `propext`. This scope is
not a whole-project build or required-CI result.

The source directly reuses the repository's Weyl displacements, window roots
and phase arithmetic, `EntropyEquality.entropy_eq_log_card_iff_uniform`, and
Mathlib's complex Gram positive-semidefinite constructions and root-of-unity
identities. The source-defined qutrit origin, coordinates, purity, support and
entropy are supplied on the live proof path of `result`. The refutation does
not assume its own witness certificates as premises.

The primary source version is arXiv:2611.04009v1, distributed under CC BY 4.0.
The brief quotation and bibliographic citations provide attribution; no
third-party document or code is reproduced. The unchanged source note records
Gross's parity/antisymmetric-qutrit construction, the noisy Strange literature,
the distinct six-support Gross mixture, and the distinguished-entry sign
discrepancy in Prakash–Singhal Eq. (II.15). The convention used in the proof is
Thio's explicit sum. No new-state or priority claim is made.

## Triage

Tier 1 explicit source question. The typed
`OpenProblemResolutionClaim` on `result` binds this one dossier with
`ResolutionKind.Refuted`. `proof_shape: bind-only`;
`admission_basis: open-problem-resolution`; `escape_witness: none`. This is the
designated literal refutation of the utility header and has the §3.9
refutation exemption. No Reg wrapper or companion theorem is required or
claimed. No corresponding theory volume or digestion atom is used.

All fourteen authored proof declarations are honestly bind-only after inlining
the same-delivery helpers and normalization. Thirteen are private consumed
helpers, and `result` is the sole authored public theorem. Their live consumers
are:

| Proof declaration | Live consumers |
| --- | --- |
| `root_cube` | `root_star`, `origin_qutrit` |
| `root_sum` | `origin_qutrit`, `qutrit_coordinates` |
| `root_star` | `qutrit_coordinates` |
| `sum_three` | `origin_qutrit`, `rho_density`, `rho_purity`, `qutrit_coordinates`, `law_sum` |
| `origin_qutrit` | `qutrit_coordinates` |
| `rho_density` | `result` |
| `rho_purity` | `result` |
| `qutrit_frame_allowed` | `result` |
| `qutrit_coordinates` | `result` |
| `law_nonneg` | `law_entropy`, `result` |
| `law_sum` | `law_entropy` |
| `law_support` | `result` |
| `law_entropy` | `result` |
| `result` | designated external-question refutation; no auxiliary-consumer claim |

Proof-shape is not applicable to the fifteen authored definitions. The thirteen
public definitions are the fourteen Scribe handles other than `result`; the two
private definitions are `singleEquiv` and `law`. Their consumers are:

| Definition | Live consumers |
| --- | --- |
| `grossDisplacement` | `grossOrigin`, `grossLocal` |
| `grossOrigin` | `grossLocal`, `origin_qutrit` |
| `grossLocal` | `grossTensor`, `qutrit_frame_allowed`, `qutrit_coordinates` |
| `grossTensor` | `IsGross` |
| `columnProjector` | `IsMUBKD` |
| `IsMUBKD` | `IsSourceFrame` |
| `IsGross` | `IsSourceFrame`, `qutrit_frame_allowed` |
| `IsSourceFrame` | `claim`, `qutrit_frame_allowed` |
| `coordinate` | `claim`, `qutrit_coordinates` |
| `coordinateSupport` | `claim`, `law_support` |
| `coordinateEntropy` | `claim`, `law_entropy` |
| `claim` | `result` |
| `rho` | `rho_density`, `rho_purity`, `qutrit_coordinates`, `result` |
| `singleEquiv` | `qutrit_frame_allowed` |
| `law` | `qutrit_coordinates`, `law_nonneg`, `law_sum`, `law_support`, `law_entropy`, `result` |

### What the settlement shows

**Proved by the literal refutation:** an actual allowed Gross qutrit at purity
$3/8$ attains the middle entropy bound with coordinate support eight. Therefore
the complete universal only-$D=\delta d$ assertion is false. This is one
resolved binary question, not several problems obtained by recounting witness
consequences.

**Failure mechanism, as exhibited by the proof:** entropy equality is compatible
with a distribution uniform on its nonzero coordinates. The actual density
matrix above realizes such a distribution on eight coordinates. The source's
dimension-multiple sufficient construction does not impose divisibility on
every physically realizable attaining support. The counterexample supplies the
missing distinction between a probability pattern and an actual state.

**Nearest surviving source statements:** the paper's dimension-multiple examples
remain sufficient examples; necessity is what fails. The entropy lower bound is
attained here, not violated. Lemma 2 concerns its separately restricted MUB-KD
convex-hull setting; this Gross witness does not refute that lemma. The pure-state
global bound $H\ge\ln d$ is not claimed to be saturated: here $\ln8>\ln3$.
These are source-scope comparisons, not additional Lean theorems or additional
resolved problems.

**Effect and open boundary:** the answer to Appendix A A1.p8.1's binary question
is NO. Classifying all actual attainments at every purity and for every stated
representation remains open here. The result neither classifies MUB-KD
attainments nor asserts a larger family of Gross counterexamples. No other
source result, including the separate Appendix B questions, is settled by this
binding.

## ASSUMED-UNVERIFIED

The bounded literature reading does not establish worldwide absence of a prior
solution, priority, a new state, or exhaustive current openness. The wider
fixed-purity attainment classification and any strengthened counterexample
family are unproved here. Independent source/form/mirror approval covers the
unchanged mathematics and exposition; it does not establish full CI, final
tests/quality/architecture review, merge, dev delivery or resolution-KPI credit.
