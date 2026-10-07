---
slug: chruscinski-2022-qdeformed-commutator-traceless-refutation
bibkey: chruscinski2022qdeformed
doi: 10.48550/arXiv.2202.11520
url: https://arxiv.org/abs/2202.11520v2
triage: theorem
motivation_gids:
  - D5/S3/QuantumBounds/QDeformedCommutatorTracelessRefutation.result
---

# A traceless counterexample to the q-deformed Böttcher–Wenzel bound

## Problem

D. Chruściński, G. Kimura, H. Ohno and T. Singal, *Bounding the Frobenius norm of a q-deformed
commutator*, arXiv:2202.11520v2, prove $\|AB-qBA\|_F^2\le(1+q^2)\|A\|_F^2\|B\|_F^2$ for $q>0$ when
$A$ or $B$ is normal, note that it fails in general, and state Conjecture 1: "For any $q > 0$, if
$A$ or $B$ is traceless, the inequality ... holds and is sharp." They prove it for $n=2$. The
verbatim statements are in [the literature note](../Library/QuantumBounds/chruscinski2022qdeformed.md).

Issue [#13930](https://github.com/the-omega-institute/trureturing/issues/13930) reads the inequality
clause for every $n$, every $q>0$ and all $A,B\in M_n(\mathbb C)$ with $\mathrm{tr}A=0$ or
$\mathrm{tr}B=0$.

## Motivation

The conjecture would extend the Böttcher–Wenzel inequality, which is the case $q=1$, to
deformed commutators by the same trace condition under which the ordinary commutator is
insensitive to traces.

## Gap

Issue #13930 records the literature check before any Lean: the follow-up arXiv:2608.03897 does
not treat the traceless case; the Zenodo records on the same authors' one-parameter
Böttcher–Wenzel functional concern a different conjecture; the repository had no result.
`not-found-in-searched-scope`.

## Route

At $q=2$ and $n=5$, the pair $A=\begin{bmatrix}6&42\\0&-3\end{bmatrix}\oplus(-I_3)$,
$B=\begin{bmatrix}6&0\\-42&-3\end{bmatrix}\oplus(-I_3)$ is traceless, $\|A\|_F^2=\|B\|_F^2=1812$, and
$\|AB-2BA\|_F^2=16417164>16416720=5\cdot1812^2$.

## Falsifier

The refutation would fail if the conjecture were read for $n=2$ only; the paper states it for
general $n$ and proves only $n=2$.

## Evidence

The canonical source is `D5/S3/QuantumBounds/QDeformedCommutatorTracelessRefutation.lean`, with
public `claim` and `result : ¬ claim`. The squared Frobenius norm is the existing `mass` of
`D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation`, the only import. The
axiom closure of `result` is exactly `propext`, `Classical.choice` and `Quot.sound`; there is no
`sorry`, `native_decide`, or new axiom.
The module statement is `sha256:f4d28dfa9e64a255bf7676cc918bda5b227d569a443c0f50bd8f8b4981052a2a`,
the `result` statement `sha256:bcddb28149b4dceac91841750aabb71d24dd118a582bbf4db8c2f5936a356ff9` and the
`claim` statement `sha256:61f533309ab5da634cf0b059cb95cf42e68bd5e2e618f40afd51a8e2dff37331`. The Freeze
event is `sha256:7570e47bab63b7eede934aad91f3ad4652bde1f20e9d34ffbac64080f1fdaacc`; its project-level
prerequisite is the Moreau–Yosida module
(`sha256:5ba5226c1d185e37836d461616c2928638177220bb70a5360c8d549ad8283566`).

## Triage

Tier 1 conjecture of a 2022 paper, preregistered in issue #13930 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none | open-problem-resolution |

Utility is `kind=certified-instance; basis=refutes` (the claim and its refutation). There is no
digestion atom.

### What the refutation shows

**Proved by `result`:** Conjecture 1 fails at $q=2$ for a pair of traceless $5\times5$ integer
matrices; both traces vanish, so even the stronger hypothesis "both traceless" does not rescue it.

**Argued, not formalized.**

- *Mechanism (trace dilution).* For any $A,B\in M_r(\mathbb C)$ with traces $a,b$, put
  $A_m=A\oplus(-\tfrac amI_m)$ and $B_m=B\oplus(-\tfrac bmI_m)$. Then $\mathrm{tr}A_m=\mathrm{tr}B_m=0$,
  $\|A_m\|_F^2=\|A\|_F^2+|a|^2/m$, $\|B_m\|_F^2=\|B\|_F^2+|b|^2/m$ and
  $\|[A_m,B_m]_q\|_F^2=\|[A,B]_q\|_F^2+(1-q)^2|ab|^2/m^3$. As $m\to\infty$ the ratio
  $\|[A_m,B_m]_q\|_F^2/(\|A_m\|_F^2\|B_m\|_F^2)$ tends to that of $(A,B)$, so for every $q>0$ the
  traceless condition does not lower the optimal constant of the unrestricted problem uniformly
  in $n$. With the pair $A=\begin{bmatrix}2&14\\0&-1\end{bmatrix}$,
  $B=\begin{bmatrix}2&0\\-14&-1\end{bmatrix}$ at $q=2$ (the paper's non-normal family
  $A=\begin{bmatrix}q&\sqrt t\\0&-1\end{bmatrix}$, $B=\begin{bmatrix}q&0\\-\sqrt t&-1\end{bmatrix}$ at
  $t=196$; the paper's displayed example is $t=64$), the excess is $676-2010/m-5/m^2+1/m^3>0$ for
  every $m\ge3$ (exact rational evaluation in #13930), so the conjecture fails in every dimension
  $n\ge5$.
- *What survives.* The bound holds when one matrix is normal (the paper's Proposition 1) and for
  $n=2$; the trace condition is the wrong replacement for normality, because a trace can be moved
  into a block where it costs only $O(1/m)$ in norm.

**Open.** Whether Conjecture 1 holds for $n=3$ and $n=4$, and the optimal constant of the traceless
problem in fixed dimension, are not determined here.

**Effect on the paper.** Conjecture 1 is false for $n\ge5$; the traceless case does not give a
q-deformed Böttcher–Wenzel inequality with constant $1+q^2$.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty, priority, or
the absence of an independent proof.
