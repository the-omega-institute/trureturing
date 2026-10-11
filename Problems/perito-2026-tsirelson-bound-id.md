---
slug: perito-2026-tsirelson-bound-id
bibkey: perito2026bell
doi: 10.48550/arXiv.2606.21362
url: https://arxiv.org/abs/2606.21362v3
triage: theorem
motivation_gids:
  - D5/S3/QuantumBounds/PeritoTsirelson.result
---

# The Tsirelson bound of the d-outcome Bell functional of Perito et al.

## Problem

I. Perito, R. D'Avino, M. Jung, P. Mironowicz, A. Acín and R. Augusiak, *Bell inequalities tailored
to optimal global randomness certification*, arXiv:2606.21362v3, §III.2, define for $d$-outcome
measurements in unitary notation ($A_x=\sum_a\omega^a\Pi_{a|x}$, $\omega=e^{2\pi i/d}$)
$\mathcal I_d=\frac12\sum_{x<2}\sum_{y<d}\omega^{xy}A_x\otimes B_y+\text{h.c.}$ and state:

> **Conjecture 1.** The Tsirelson bound of $\mathcal{I}_d$ is given by Eq. (tsir_bound) [$2/\sin(\pi/(2d))$]
> and is attained by taking $A_0=Z$, $A_1=X$; the state $\ket{\psi_d} = \frac{1}{\sqrt d} \sum_k \ket{kk}$;
> and $B_y$ defined by Eq. (optbob).

The verbatim statements are in [the literature note](../Library/QuantumBounds/perito2026bell.md).
Issue [#14106](https://github.com/the-omega-institute/trureturing/issues/14106) reads it for every
$d\ge2$, every pair of finite dimensions, every density matrix and every projective strategy
($A_x$, $B_y$ unitary with $A_x^d=B_y^d=I$), together with the validity and the value of the stated
strategy.

## Motivation

The maximal quantum violation of $\mathcal I_d$ is the input of the paper's global randomness
certification; the paper confirms the bound by NPA only for $d\le6$, and its analytic bound
$d\sqrt2$ is tight only at $d=2$.

## Gap

Issue #14106 records the literature check before any Lean: three arXiv versions of the source; arXiv,
web, Zenodo and citation searches found no proof of the upper bound for general $d$; the repository
had no result. `not-found-in-searched-scope`.

## Route

Write $U=A_0^*A_1$. The Bell operator is
$S=\sum_{x,y}\omega^{xy}A_x\otimes B_y=(A_0\otimes I)\sum_y(1+\omega^yU)\otimes B_y$. Diagonalizing the
unitary $U$ (eigenvalues $z$ with $|z|=1$) splits the second factor into blocks
$\sum_y(1+\omega^yz)\,B_y$, of norm at most $\sum_y|1+\omega^yz|$. With $z=e^{2is}$,
$|1+\omega^yz|=2|\cos(s+\pi y/d)|$; after reducing $s$ modulo $\pi/d$ every cosine is nonnegative and the
finite cosine sum gives $\sum_y|1+\omega^yz|\le 2/\sin(\pi/(2d))$. Hence
$\operatorname{Re}\operatorname{tr}(\rho S)\le\|S\|\le2/\sin(\pi/(2d))$ for every density $\rho$.

## Falsifier

The settlement covers projective strategies on finite-dimensional spaces, which contain every
finite-dimensional POVM strategy after Naimark dilation; commuting-operator strategies on
infinite-dimensional spaces are not covered by the formal statement.

## Evidence

The canonical source is `D5/S3/QuantumBounds/PeritoTsirelson.lean`, with public `IsDObservable`,
`bellOperator`, `bellValue`, `peritoLambda`, `peritoB`, `maxEntangledVector`, `maxEntangled`, `claim`
and `result : claim`; `maxEntangledVector ι` and `maxEntangled ι` are defined for every finite index type
`ι`; `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation` uses them at `ι = Fin d`. It also proves the validity and the trace identities of `peritoB` (the source's
appendix result, entered as a literature prerequisite) and the upper bound `bell_value_le`. Its
helper modules are `D5/S3/QuantumBounds/PeritoUnitCircleSum.lean` (the scalar bound
`unit_circle_sum_le`) and `D5/S3/QuantumBounds/PeritoTensorBlockBound.lean` (the tensor block bound
`tensor_block_bound`). They reuse the frozen `FiniteStateChannel.DensityState`; the frozen
`WindowRegister` declarations `windowRoot`, `clockMatrix`, `shiftMatrix`, `window_weyl`,
`window_unitary` and the power laws; the frozen `WeylDisplacementPowers` and `WeylDisplacementTrace`
laws; the frozen `RankTrace`; and two declarations made public at their frozen origins,
`Matrix.exists_mem_unitaryGroup_star_mul_mul_eq_diagonal` (`D5/S3/Quantum/BlockNorm/EssentiallyHermitian`)
and `clockMatrix_pow_mod` (`D5/S3/Quantum/Algebra/WeylDisplacement`). The axiom closure of `result` is
exactly `propext`, `Classical.choice` and `Quot.sound`; there is no `sorry`, `native_decide`, or new
axiom.
The settlement module statement is `sha256:9c2aa5574b319e98453d9c0136976488e5e6d030fcb67e39c1cf3cdb622a2afb`,
the `result` statement `sha256:363a0f58a9d6e1baa6e693b122677fecd4c0535ef9c46a3521846d22e7be3ffa` and the
`claim` statement `sha256:56118dfac5f94c452ae0d7c32ead8d0d0eb3eb887a0ec3b3679cacb2b0cc2549`; its Freeze event
is `sha256:b111c88ce9bf9b5281943cae258c5bbbaaaa7918ea13263c2bbd14983aa4b751`. The helper
`PeritoUnitCircleSum` has module statement
`sha256:e212a2924a6c8301a2c581eba5bfb187b6e4c57daa47621d137d6cefbdc16819` and Freeze event
`sha256:388281363036f72892ba4e831c19d7bbd86bf3adc80120a79440f0c55600d093`; the helper
`PeritoTensorBlockBound` has module statement
`sha256:e906b38fc26180c68fb340ec5b5a4461255cdbf6e90dcd9620d3360468c13488` and Freeze event
`sha256:909a9bc5a555ce5e5fe0297a47174ed725f13b2a76ef145ccdb99ef4e70ad35f`.

## Triage

Tier 1 conjecture of a June 2026 paper, preregistered in issue #14106 before any Lean and run as a
research line with layered modules. `theorem`; resolution `proved`.

| module | declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- | --- |
| `PeritoUnitCircleSum` | `unit_circle_sum_le` | content | the public conclusion (phase reduction and nonnegative-cosine control) | escape-witness |
| `PeritoTensorBlockBound` | `norm_diagonal_tensor_sum_le`, `tensor_block_bound` | content | `norm_diagonal_tensor_sum_le` | escape-witness |
| `PeritoTsirelson` | `result` | content | the scalar and tensor bounds of the two helper modules, first frozen in the same delivery | open-problem-resolution |

The other theorems of the three modules lie on the proof path of `result` (CLAUDE.md §3.2
「有消费的辅助声明」); each has free arguments. Utility is `none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every $d\ge2$, every pair of finite dimensions $n,m$, every density
matrix $\rho$ on $\mathbb C^n\otimes\mathbb C^m$ and all unitaries $A_0,A_1$, $B_0,\dots,B_{d-1}$
with $A_x^d=B_y^d=I$,
$\operatorname{Re}\operatorname{tr}\big(\rho\sum_{x,y}\omega^{xy}A_x\otimes B_y\big)\le2/\sin(\pi/(2d))$;
the clock and shift matrices and the operators $B_y$ of Eq. (optbob) are unitary with $d$-th power
the identity; the maximally entangled matrix is a density matrix; and the strategy attains
$2/\sin(\pi/(2d))$.

**Established inside the proof, for general data.** The bound uses only unitarity: the powers
$A_x^d=B_y^d=I$ are not needed. For every unit complex $z$, $\sum_y|1+\omega^yz|\le2/\sin(\pi/(2d))$
(`unit_circle_sum_le`); and for every unitary $U$, unitaries $B_y$ and every $K$ with
$\sum_y|1+\omega^yz|\le K$ for all unit $z$, $\|\sum_y(1+\omega^yU)\otimes B_y\|\le K$
(`tensor_block_bound`). Bob's operators factor as $B_y=\omega^{-y}X\,g(u_y)$ with $u_y=-\omega^{1-y}XZ$,
$u_y^d=-1$ and $g(t)=\sum_{k<d}t^k/(d\sin(\pi(k+\frac12)/d))$, and
$g(e^{i\pi(2j+1)/d})=e^{i\pi(d-1-2j)/(2d)}$.

**Argued, not formalized.**

- *Mechanism.* After the factorization $S=(A_0\otimes I)\sum_y(1+\omega^yU)\otimes B_y$ with
  $U=A_0^*A_1$, the problem decouples into one scalar problem per eigenvalue $z$ of $U$, and on each
  block the operator norm is at most $\sum_y|1+\omega^yz|$ because every $B_y$ is unitary. Only the
  unit-circle maximum of this scalar sum enters, which is why the bound holds in every dimension.
- *Where the scalar maximum sits.* Numerically ($d\le12$) $\sum_y|1+\omega^yz|$ reaches
  $2/\sin(\pi/(2d))$ at $z=1$ for odd $d$ and at $z=e^{i\pi/d}$ for even $d$.
- *What else follows.* The same argument bounds every functional $\sum_y(A_0+c_yA_1)\otimes B_y$
  with $|c_y|=1$ by $\max_{|z|=1}\sum_y|1+c_yz|$; this extension is not formalized.

**Open.** The tightness of the bound for the extended functional $\bar{\mathcal I}_d$ (with Bob's
extra setting) and the randomness-certification statements of the paper are not settled here.

**Effect on the paper.** Conjecture 1 holds for every $d$: the Tsirelson bound of $\mathcal I_d$ is
$2/\sin(\pi/(2d))$ in every finite dimension, attained by the stated strategy.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty, priority, or the
absence of an independent proof.
