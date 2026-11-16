---
slug: op-zveryk2609c48
bibkey: zveryk2026virasoroextensions
doi: 10.48550/arXiv.2609.15729
triage: theorem
motivation_gids:
  - D5/S3/VertexAlgebra/Sectors/ZverykIdealRigidityRefutation.result
url: https://arxiv.org/abs/2609.15729v2
---

## Problem

Zveryk, *Virasoro extensions of generalized Kac-Moody algebras*, arXiv:2609.15729v2, Conjecture 4.8, page 18, asserts: “The statement of Theorem 4.5 holds for any $x\in\mathbb P^1$ for which the corresponding VBKM algebra satisfies (4.3). In other words, the VBKM algebra $\tilde\mathfrak{g}(\mathcal F_x)$ contains no ideals not intersecting $\mathfrak h$.” The settlement is **Refuted**; preregistration [#27461](https://github.com/the-omega-institute/trureturing/issues/27461).

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| Enhanced generalized Cartan datum, Definition 3.1 | `VBKMPresentation.EnhancedCartanData`, `IsEnhanced` | Pairing, ordinary roots and coroots, Virasoro roots, central and degree elements, integrality, finite decompositions and zero-pairing compatibility. |
| Symmetrizability, Definition 4.1 | `Symmetrizable` | Rescaling linear automorphism and all symmetric/cross pairings. |
| Condition (4.3) | `Condition43` | Both ordinary-root and distinct Virasoro-root zero-pairing equivalences. |
| Projective fibre $x\in\mathbb P^1$ | `claim` | Every nonzero homogeneous pair $(s,t)$; $s=0$ uses `heisenberg`, otherwise `deform`. The counterexample is $[1:0]$. |
| Presentation of Section 3.2 and local quotient of Section 3.3 | `presentationRelations`, `Presented`, `HighestProper`, `localRelations`, `localIdeal`, `VBKM` | Explicit free-Lie quotient; proper highest vectors include the Cartan eigenvector condition. |
| No nonzero ideal disjoint from Cartan | `IdealRigidity` and `cartanSubspace` | Every Lie ideal and the actual Cartan generator image; its injectivity and a triangular decomposition are not assumptions. |
| Negation of the universal assertion | `ZverykIdealRigidityRefutation.result` | Closed `¬ claim`, with no additional hypotheses. |

The conventions fix positive mode indices, unordered finitely supported root multiplicities, the off-diagonal real-root integrality clause and $c_{\rm usual}=12C$. These resolve the source's printed zero-mode and diagonal-integrality conventions as specified in #27461; they add no unproved premise. The seven new modules have `generality: I` and `utility: none`; the published existing owner retains `generality: G` and `utility: none`.

## Motivation

Condition (4.3) does not exclude the singular-vector obstruction to ideal rigidity. The settling GID is `D5/S3/VertexAlgebra/Sectors/ZverykIdealRigidityRefutation.result`; its admission basis is `open-problem-resolution (#27461; Refuted)`. The six supporting modules use `escape-witness`.

## Gap

Singularity alone does not establish a nonzero Cartan-disjoint ideal in the full presentation. One must verify every presentation relation in a representation, prove that the singular vector survives, control the local defining ideal and prove stability and spectral separation of the negative-descendant span. These obligations are discharged by the delivered Lean proof.

## Route

For $q=1$, use the symmetric ordinary matrix
$A=\left(\begin{smallmatrix}-4/3&-1\\-1&-2/3\end{smallmatrix}\right)$,
$C=H_1-H_2$, $B=-81H_1/8+105H_2/8$, and $\gamma(H_1)=\gamma(H_2)=-1/3$.
The datum is enhanced and symmetrizable and satisfies (4.3), as proved by `VBKMPresentation.datum_enhanced`, `datum_symmetrizable` and `datum_condition43`.

Write $D_r=\operatorname{ad}L_{-r}$. The level-four vector is
$v=(D_1^4-3D_2D_1^2-\tfrac74D_2^2+3D_3D_1+\tfrac32D_4)f_1$.
The positive modes kill it; the Cartan cancellation also makes the ordinary positive generators kill it. Recursive operators descend through all contextual Witt relations and give a representation of the full presentation. A Laurent evaluation sends the negative word, applied to its vacuum, to $(0,\tfrac14t^{-3})$, proving survival.

The span of negative descendants of $v$ is an ideal. Its spanning eigenweights are strictly separated from the zero Cartan weight, so this nonzero ideal has zero intersection with the actual Cartan image. The rank-one primitive-kernel argument shows that the local defining relations are empty. Thus the local **ideal** is zero; the locally quotiented algebra is not asserted to be zero.

## Falsifier

A failed source relation, a nonzero local relation killing $v$, an unsatisfied datum hypothesis or a mismatch between `claim` and the source would invalidate the proposed settlement. The Lean result constructs the counterexample without a PBW assumption, an assumed Cartan injection, a triangular-decomposition hypothesis or a private axiom.

## Evidence

The seven modules are `VBKMPresentation`, `VBKMPrimitiveKernel`, `VBKMSingularVector`, `VBKMWeightIdeal`, `VBKMVirasoroBootstrap`, `VBKMRecursiveAction` and `ZverykIdealRigidityRefutation`, under `D5/S3/VertexAlgebra/Sectors/`, with corresponding Blueprint Scribes. The reused public diagonal construction belongs to `D5/S1/Words/WeakShuffleNormalization`.

### Exact finite checks

Experiment: [immutable directory](https://github.com/the-omega-institute/trureturing-experiments/tree/20d3d32d53576636c50a705d088d84beaadf05ac/docs/reports/zveryk2609c48-virasoro-gkm-ideal).
The program is `check.py`, SHA-256 `685d868c3d71b9497bb2070bd41d37af5458655f87bc2643448152ad591bcd11`. Command: `git -C /Users/auric/trureturing-experiments show 20d3d32d53576636c50a705d088d84beaadf05ac:docs/reports/zveryk2609c48-virasoro-gkm-ideal/check.py | python3 -`; exit 0, final result `ALL_CHECKS_OK`.

The exact rational computation checks $q=1,\ldots,100$ for the finite datum conditions; 300 commutators on PBW levels $0,\ldots,4$, modes $-2,\ldots,2$; and 3,654 full-presentation relations for words of length at most two, modes $-3,\ldots,3$, at two highest weights. It also checks annihilation by $L_1,\ldots,L_8$, the one-dimensional joint level-four kernel and the Laurent value. These computations provide finite evidence and are not used as a Lean certificate.

## Triage

### What the settlement shows

| Target item | Status and evidence kind | Result and boundary |
| --- | --- | --- |
| Condition (4.3) permits a surviving level-four singular vector at $q=1$ | Proved; kernel-checked `ZverykIdealRigidityRefutation.result`, using `presentedSingular_ne_zero`, `presented_positive_singular`, `presented_e_singular` and `VBKMPresentation.datum_condition43` | The generated nonzero ideal is Cartan-disjoint; admissibility does not enforce rigidity. |
| Both the printed presentation and locally quotiented reading | Proved; kernel-checked private `datum_localRelations_empty`, `datum_localIdeal_zero`, `localQuotientMap_injective` on the result's proof path | The local defining ideal is zero, so the nonzero vector survives both readings. |
| Independent exact finite checks | Computed; the immutable experiment and command above, exit 0, with the stated SHA-256 | $q=1,\ldots,100$ datum checks, 300 commutators and 3,654 bounded presentation checks; no infinite-family theorem follows from these counts. |
| Uniform $q\ge1$ family and pairwise nonisomorphism | Open for this Lean delivery | Only $q=1$ is formalized; no pairwise nonisomorphism result. The family argument in #27461 is a paper argument, not a uniform kernel theorem. |
| Surviving neighbouring claims | Open for this delivery | All-fibres dimension assertions, a new proof of countably generic rigidity and a necessary-and-sufficient corrected rigidity criterion are not settled. |

The source's countably generic rigidity theorem is not contradicted by a special fibre. Conjecture 4.8 cannot justify an extension to every fibre satisfying (4.3); consequences requiring that extension need another hypothesis or argument. No all-fibres dimension conclusion is derived here.

The literature screen on #27461 covers the source, author records, arXiv, DataCite/Crossref, OpenAlex, MathOverflow and formalization inventories. It located no prior settlement in that searched scope. Citation inventories and exhaustive coverage remain **ASSUMED-UNVERIFIED**.

## ASSUMED-UNVERIFIED

Literature completeness and the absence of every semantic duplicate are ASSUMED-UNVERIFIED. Bounded search failure is not a nonexistence theorem. The uniform family and neighbouring questions retain the open scope stated in Triage.

The four-slot escape audit is unfinished for the public theorems and the published owner definition `D5.S1.Words.WeakShuffleNormalization.diagonal`, including `ZverykIdealRigidityRefutation.result`, under [#30339](https://github.com/the-omega-institute/trureturing/issues/30339). No Reg registration is delivered. `utility: none` grants no designated-refutation exemption; a faithful observation/realization and sensitivity bridge is missing. No `declared_validated` status is claimed.
