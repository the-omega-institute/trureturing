---
slug: akella-2026-stabilizer-multi-entropy-n3-collapse
bibkey: akella2026genuine
doi: 10.48550/arXiv.2607.06050
url: https://arxiv.org/abs/2607.06050v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.result
---

# The n = 3 collapse of the genuine four-party multi-entropy for stabilizer states

## Problem

S. Akella, N. Iizuka and A. Miyata, *Genuine Multi-Entropy in the Toric Code*,
arXiv:2607.06050v1, state for stabilizer states the reduction
$\mathrm{GM}^{(4)}_{3}(A:B:C:D)=-\left(a-\tfrac19\right)I_3$ (Eq. (3)), where $I_3$ is the Rényi
tripartite information and $a$ the convention parameter of the genuine multi-entropy, note that
"this reduction is not a consequence of the Coxeter structure", and ask in §6 "Whether there is a
similar counting argument for $n = 3$ case is an open question." The verbatim definitions are in
[the literature note](../Library/QuantumStates/akella2026genuine.md).

Issue [#13575](https://github.com/the-omega-institute/trureturing/issues/13575) reads Eq. (3) as a
theorem about every normalized pure qubit stabilizer state and every assignment of its qubits to
four labelled parties (parties may be empty), for every real $a$, together with positivity of every
replica partition function $Z_3^{(\mathtt q)}$ so that every logarithm is defined.

## Motivation

For a Kitaev–Preskill partition $I_3$ is the negative topological entanglement entropy, so the
collapse says the $n=3$ genuine multi-entropy of a stabilizer state carries no four-partite
information beyond it. The paper establishes the $n=2$ case by a Coxeter counting argument and
the $n=3$ case by computation; `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.result`
proves it for all stabilizer states with an explicit counting argument.

## Gap

Issue #13575 records the literature check before any Lean: the follow-up arXiv:2608.29627 reports
the $n=3$ case as established numerically for qubit stabilizer states; arXiv:2601.16258 gives the
$n=2$ argument only; abstract searches for "multi-entropy" with "stabilizer" found no proof; the
repository had no result. `not-found-in-searched-scope`.

## Route

1. Every stabilizer state is $c\,(U_1\otimes\cdots\otimes U_N)$ applied to a graph amplitude
   $(-1)^{\sum_{i<j}\Gamma_{ij}x_ix_j}$, and $Z$ is unchanged by identical local unitaries on all
   replicas (`BinaryStabilizerGraphNormalForm.stabilizer_graph_normal_form`).
2. For a graph amplitude the replica product is $(-1)^{F(\Gamma,\delta,x)}$, with $\delta_u$ the
   colour vector of qubit $u$ in $G=(\mathbb Z/3)^{\mathtt q-1}$.
3. The $\mathbb F_4$ Fourier transform over $G$ splits $F$ into bilinear blocks $y_t^{\mathsf T}C_tz_t$
   over representatives $t$ of $\{t,-t\}$ (`TernaryTranslationQuadraticNormalForm`); each block
   sums to $2^{2N-\operatorname{rank}C_t}$, so $Z_3^{(\mathtt q)}=2^{-\sum_t\operatorname{rank}C_t}$.
4. $S_3^{(\mathtt q)}=\frac{\log2}{2\cdot3^{\mathtt q-2}}\sum_t\operatorname{rank}C_t$, and
   $\operatorname{rank}C_t$ depends only on the partition of the parties into the classes of
   $c\mapsto t\cdot\delta_c$; collecting the coefficients of the partitions over the 13, 4 and 1
   representatives for $\mathtt q=4,3,2$ gives $\mathrm{GM}^{(4)}_3+(a-\tfrac19)I_{3,3}=0$ for every
   rank function.

## Falsifier

The settlement is stated for the replica convention of the paper's Appendix A. Other
conventions (for example, shifting the last party) and mixed or non-stabilizer states are outside
the claim and are not addressed.

## Evidence

The canonical sources are `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.lean`
(public `shift`, `Z`, `S`, `I3`, `GM4`, `claim`, `result`) and its helper modules
`D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.lean` (public `complex_sign_val`,
`graphAmp`, `stabilizer_graph_normal_form`) and
`D5/S3/QuadraticForms/TernaryTranslationQuadraticNormalForm.lean` (public `F`, `C`,
`ternary_translation_quadratic_normal_form`). They reuse the frozen `StabilizedBy`, `pauliSet`,
`tensorOp`, `pauliMatrix`, `s2`, `hadamard`, the frozen `BinaryLagrangianGraphForm.sp`,
`swapAt`, `swapAt_involutive` and `lagrangian_graph_form`, and, of the frozen
`D5/S3/VertexAlgebra/LatticeTwistedGroundRealization`, the sign `SignQuotient.complexSign` with
`complexSign_add`, the sign laws `sign_zero`, `sign_one`, `sign_square`, `sign_nonzero` and
`sign_sum`, and the binary quadratic exponent `normalExponent` with `normal_exponent_add` and
`symmetric_pairing_split`. The axiom closure of `result` is exactly `propext`,
`Classical.choice` and `Quot.sound`; there is no `sorry`, `native_decide`, or new axiom.
The settlement module statement is `sha256:66bb7b09e5459cd8efabbfdfa34a5f80a927227c135f2a1f07720856af3467c3`,
the `result` statement `sha256:22e959e28055a09148222953a819dd9ed1c924acc40720eeb4b40849663a8058` and the
`claim` statement `sha256:d03e6b2def7dac64eebedf5658fa68874521789aa2d7db8ec375a93d7f9f3dc2`; its Freeze event is
`sha256:e7cc50fa88839ce0c5f608e87468ca2a5351eff427a5239064db634c87f7ce41`, with the two helper modules as
project-level prerequisites. The helper `BinaryStabilizerGraphNormalForm` has module statement
`sha256:689b31c1238a39bc0b4635018d5bba4f6ea9aaae0f430517aed413bae442a25d` and Freeze event
`sha256:5680f65f23e7c7424be9539b788cfb3e0a306d5172204e1ccd84655fae916897`, with the frozen prerequisites
`BinaryStabilizerLocalInequivalence`, `BinaryLagrangianGraphForm` and `LatticeTwistedGroundRealization`;
the helper `TernaryTranslationQuadraticNormalForm` has module statement
`sha256:ad5c634ce99317530919c1b96b82781a4886f19aa96ba17d32de5894cefd56cb` and Freeze event
`sha256:aa9f115cc367f3df30554f95efd2c447fdba777ad866069b19b5ab0bad91c55b`, with no project-level prerequisite.

## Triage

Tier 1 open question of a July 2026 paper, preregistered in issue #13575 before any Lean;
pursued as a research line with layered modules.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none | open-problem-resolution |

The other theorems of the three modules are bind-only and lie on the proof path of `result`
(CLAUDE.md §3.2 「有消费的辅助声明」); each has free arguments. Utility is `none`. There is no
digestion atom.

### What the settlement shows

**Proved by `result`:** for every normalized pure qubit stabilizer state $\psi$ and every
$\mathrm{party}:\mathrm{Fin}\,N\to\mathrm{Fin}\,4$, every $Z_3^{(\mathtt q)}$ is a positive real and
$\mathrm{GM}^{(4)}_3=-(a-\tfrac19)I_{3,3}$ for every real $a$.

**Established inside the proof.** $Z_3^{(\mathtt q)}=2^{-\sum_{t\in P}\operatorname{rank}C_t}$ for every
number of colours $\mathtt q$ and every colouring, with $C_t$ the graph matrix masked to pairs of
qubits whose colours $t$ separates.

**Argued, not formalized.**

- *Mechanism.* At $n=3$ the replica group $(\mathbb Z/3)^{\mathtt q-1}$ has odd order, so the
  replica form diagonalizes over $\mathbb F_4$ into one bilinear block per pair of opposite
  characters; each character $t$ sees only the partition of the parties by $t\cdot\delta_c$, a
  partition into at most three blocks. The collapse is a linear identity among the multiplicities
  with which the characters of $(\mathbb Z/3)^3$, $(\mathbb Z/3)^2$ and $\mathbb Z/3$ realize each
  partition of four parties, and it holds for every rank function, not only for those of graphs.
- *Why $n=4$ fails.* For $n=4$ the group $(\mathbb Z/4)^3$ has even order, the Fourier transform
  over a field of characteristic two is not invertible, and characters of order four see
  four-block partitions; the counting identity has no analogue, consistent with the paper's
  threshold $n=\mathtt q$.
- *Other $\mathtt q$ at $n=3$.* Steps 1–3 of the route hold for every $\mathtt q$; whether the
  collapse holds for $\mathtt q\ge5$, $n=3$ reduces to the corresponding coefficient identity over
  partitions into at most three blocks (not checked here).
- *Other odd $n$ (candidate, open).* For $n=5$ the characters of $(\mathbb Z/5)^{\mathtt q-1}$ take
  values in $\mathbb F_{16}$, and multiplication by $2$ permutes the nonzero characters in orbits of
  length four, so the pairing $\{t,-t\}$ of the $n=3$ argument is replaced by Frobenius orbits; the
  block form of the replica quadratic form and its Gauss sum over the splitting field would have to
  be established first. No claim beyond $n=3$ is made.

**Open.** The general conjecture of the abstract ($\mathtt q\ge4$, $n<\mathtt q$) beyond
$\mathtt q=4$, $n=3$, and the qudit (level $k$) analogues, are not settled here.

**Effect on the paper.** Eq. (3) holds for every qubit stabilizer state, and the §6 question has
an affirmative answer: the $n=3$ collapse follows from a counting argument over the characters of
$(\mathbb Z/3)^{\mathtt q-1}$.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty, priority, or
the absence of an independent proof.
