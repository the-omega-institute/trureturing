---
slug: daly-2022-superchannel-minimal-extension-extremality
bibkey: daly2022axiomatic
doi: 10.48550/arXiv.2210.00370
url: https://arxiv.org/abs/2210.00370v1
triage: theorem
motivation_gids:
  - D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.result
---

# A non-extreme minimum-rank superchannel extension

## Problem

P. C. Daly, *Axiomatic Approach to Quantum Superchannels*,
arXiv:2210.00370v1, Remark 4.1, asks:

> The set of possible superchannel extensions of a QSC is a convex set. In the example given the extensions with minimal e are extreme points. A natural question to ask is whether it is generally true that the extensions which give minimal dimensions e are extreme points.

The [Library note](../Library/QuantumContext/daly2022axiomatic.md) quotes
the definitions and locators. Here $e$ is exactly the source's rank of the
Choi matrix after tracing out both output factors. Convexity and extremality
use real scalars. This question is the universal assertion about **every**
minimizer; existence of **some** extreme minimizer is a weaker assertion.

### Statement echo

All names in this table belong to
`D5.S3.QuantumChannels.DalySuperchannelMinimalExtension`.

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Definition 3.1: complex span of CPTP maps | `SCPTP` | `Submodule.span` of completely positive maps satisfying trace preservation on every matrix |
| Remark 3.3: tensor product of matrix maps | `kronBilin`, `kronLift` | Bilinear `MatrixMap.kron`, lifted to all tensors |
| Definition 3.4, conditions (1) and (2) | `IsQSC` | CPTP preservation and complete CP preservation on channel spans, for every auxiliary dimension and tensor |
| Remark 3.7, all three bullets | `IsQuantumSuperchannel` | CP preservation, complete CP preservation and TP preservation on the full map spaces |
| Full superchannels agreeing with the QSC | `extensions` | Equality of matrix maps on every element of the channel span |
| Section 2: $C_L=(L(E_{ij}))$ | `choi`, `choiEquiv` | Input-first block entries and the double-sum inverse |
| Induced map $\widetilde S=R_2SR_1^{-1}$ | `induced` | Composition with the two Choi equivalences |
| Section 4: $e=\operatorname{rank}(\operatorname{Tr}_{r_1}\operatorname{Tr}_{r_2}C_{\widetilde S})$ | `e` | Reindex to input-pair/output-pair order and trace out the output pair |
| All positive dimensions, all QSCs, every minimizing extension is extreme | `claim` | Four lower bounds, QSC hypothesis, membership, comparison with every extension, real extreme points |
| Negative answer | `result` | Exact negation of `claim` |

`Fin n` uses zero-based indices. Complex-linear spaces and real convex
combinations express the two different scalar roles in the source; neither
adds a hypothesis to the question. The input-first Choi owner used in `e`
has the same matrix-unit expression as `choi`.

## Motivation

In dimensions $(d_1,r_1,d_2,r_2)=(2,2,2,2)$, set $Z=\operatorname{diag}(1,-1)$, $\Omega=|00\rangle+|11\rangle$,
and $P=|\Omega\rangle\langle\Omega|$. Define

$$
F_s(X)=\frac X2+\frac{I\otimes\operatorname{Tr}_A X}{8}
 +\frac{\operatorname{Tr}(X)I}{16}
 +\frac{s\operatorname{Tr}((Z\otimes I)X)(Z\otimes I)}{32}.
$$

Write $S_s=R^{-1}F_sR$, and let $\Gamma$ be the restriction of $S_0$ to
$\operatorname{SCPTP}(2,2)$. Every extension of $\Gamma$ has $e=4$.
The distinct extensions $S_1$ and $S_{-1}$ have midpoint $S_0$; hence this
minimizer is not extreme.

## Gap

Preregistration [#19620](https://github.com/the-omega-institute/trureturing/issues/19620)
identifies Remark 4.1 as a tier-1 published question and fixes the full
quantifiers, tensor maps and reduced-Choi-rank definition. Its literature
screen reports the question also in Remark 3.3.1 of Daly's thesis.
Bibliographic completeness is `ASSUMED-UNVERIFIED`.

## Route

The private theorem `Rank.coherent_block_full_rank` supplies the rank
obstruction. For a positive semidefinite block matrix $J$, a kernel vector
of its partial trace gives a positive semidefinite compression of trace
zero. That compression is zero, while its prescribed off-diagonal entry
is the strictly positive quadratic form of a positive definite matrix
$K$. The contradiction gives full reduced rank.

`extension_fixed_coherence` identifies the shared block; `all_extensions_e`
applies the obstruction to every legal extension. `super_extension`
provides the interval of legal extensions, and `super_not_extreme` uses
the distinct endpoints and their midpoint. These are private proof
components consumed by `result`.

## Falsifier

The refutation requires a legal QSC, two distinct legal endpoint
extensions, midpoint equality and minimum rank for **every** extension.
A CP-only construction, a statement only about the displayed family, or
an alternative memory-cost definition would not refute this question.
The theorem `result` proves the negation of the full `claim`.

## Evidence

Kernel evidence is
[DalySuperchannelMinimalExtension.lean](../D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.lean),
with its
[Blueprint](../Blueprint/D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.md).
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
There are no other public theorems or published owner declarations.

The experiment is
[the pinned numerical check](https://github.com/the-omega-institute/trureturing-experiments/tree/84a0d88a51337614a756c6041af291b307929afb/docs/reports/daly-2022-superchannel-minimal-extension-extremality).
Command: `/opt/homebrew/bin/python3 /Users/auric/trureturing-experiments/docs/reports/daly-2022-superchannel-minimal-extension-extremality/check.py`;
exit 0, `RESULT PASS`. Script SHA-256:
`cb6c4837fee13e9104a8c34e8e979230820189b2b8283b135406161fd294f394`.
Exact computations concern the two-qubit matrices and $s=-1,0,1$;
the numerical sampling concerns 300 boundary extensions. Neither finite
computation replaces the universal rank proof.

## Triage

### What the settlement shows

| Item | Evidence kind and result |
| --- | --- |
| Universal all-minimizers assertion in Remark 4.1 | Kernel-checked: `result` refutes `claim` with dimensions $2,2,2,2$ and the source's $e$ |
| Legal extensions for $-1\le s\le1$ | Kernel-checked: `super_extension`, with `gamma_qsc` for the common QSC |
| Counterexample maps and restriction | Kernel-checked: `gamma_qsc` and `super_extension` use the displayed $F_s$ (`ftilde`), $S_s=R^{-1}F_sR$ and $\Gamma=S_0\vert_{\operatorname{SCPTP}(2,2)}$ (`gamma`) in dimensions $2,2,2,2$ |
| Witness parameters $-1,0,1$ | Kernel-checked: the three legal extensions and their minimizing midpoint occur in the proof of `result` |
| Every extension has $e=4$ | Kernel-checked: `all_extensions_e`, quantified over all of `extensions gamma` |
| Fixed positive coherence block forces full reduced rank | Kernel-checked: `Rank.coherent_block_full_rank` and its application in `all_extensions_e` |
| Perturbation vanishes on the CPTP span | Kernel-checked: `charge_zero_on_span` and `super_agrees_on_span` |
| $S_0=(S_1+S_{-1})/2$ and $S_1\ne S_{-1}$ | Kernel-checked: `super_midpoint` and `super_distinct`; `super_not_extreme` draws the extremality consequence |
| Dimension of the two-qubit channel span | Computed: the experiment gives 13 and checks vanishing on a basis |
| Exact Choi eigenvalues at the three witness parameters | Computed: $J_{-1}$ has $1/32$ (six), $3/32$ (six), $9/32$ (one), $11/32$ (two), $73/32$ (one); $J_0$ has $1/16$ (twelve), $5/16$ (three), $37/16$ (one); $J_1$ has $1/32$ (six), $3/32$ (six), $9/32$ (two), $11/32$ (one), $75/32$ (one) |
| Reduced matrix and coherence-block spectrum | Computed: $R_s=P+I/2+(s/8)Z\otimes Z$ with characteristic polynomial $(\lambda-5/2-s/8)(\lambda-1/2-s/8)(\lambda-1/2+s/8)^2$; $K=P/2+I/8$ has eigenvalues $9/8,1/8,1/8,1/8$ |
| TP identity and nonzero perturbation | Computed: symbolic $\operatorname{Tr}_B X=I$ implies $\operatorname{Tr}_C F_s(X)=I$, and the perturbation at $Z\otimes I$ has diagonal $(1/8,1/8,-1/8,-1/8)$ |
| Boundary sample | Computed: 300 sampled extensions have minimum reduced eigenvalue $0.324350$; this is only the tested sample |
| Existence of an extreme minimizer | Open as a general follow-up; it is not refuted by this example |
| Every extreme extension of this example is a minimizer | Proved in prose: `all_extensions_e` gives $e=4$ for that extension and every competitor, so the required comparison is equality |
| A memory cost allowing arbitrary mixed preprocessing | Open; it is a different quantity from the binding $e$ |
| Source's Remark 3.9 example | Proved in the source (paper argument, as recorded in #19620): its target dimensions $d_2=r_2=1$ have no nontrivial output coherence block, so the positive-coherence obstruction used here does not apply; the source gives extreme minimizers and larger rank for nontrivial mixtures in its displayed family, compatible with this refutation |
| Consequences for the source's other results | Open (an independent dependency audit is not supplied): the literature reading recorded in #19620 covers Theorems 3.2, 3.5 and 3.8; no invalidation of those results is asserted |
| Bibliographic novelty | Open: literature completeness is `ASSUMED-UNVERIFIED`, not an exhaustive novelty claim |

Proved in prose from the source's convexity assertion: when the shared-block
condition forces the same reduced rank for every extension, any two distinct
extensions have a legal midpoint. That midpoint minimizes the rank and is
not extreme. This conditional argument does not classify which QSCs have
two extensions or which ones satisfy the shared-block condition.

The rank obstruction is stated for arbitrary finite carriers and a prescribed
positive definite block in the private theorem; the public settlement is
only the named universal question. The numerical sample makes no claim
about all boundary points or all dimensions. Repository admission is
separately determined by the required CI check.

## ASSUMED-UNVERIFIED

The literature screen is the partial screen recorded in #19620: the
preprint is read; Daly's thesis repetition is reported there, while the
published Lie–Jeong article and Wilson's complete thesis are not verified.
The inability to independently retrieve the thesis and the partial citing-work
screen do not establish exhaustive novelty. No later-proof absence beyond
that searched scope is asserted.

The exhaustive theorem/local-fact reuse sweep and current helper-deletion
retest are `ASSUMED-UNVERIFIED`; the bounded searches establish only their
searched scope. Compilation and
the refutation statement do not certify that those searches are exhaustive.
