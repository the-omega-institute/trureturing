---
slug: zhu-wang-2026-characteristic-three-uniform-stability
bibkey: zhu2026uniformly
doi: 10.48550/arXiv.2608.11850
url: https://arxiv.org/abs/2608.11850v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/CharacteristicThreeUniformWeylHeisenbergStability.result
---

# A uniformly stable minimal Weyl–Heisenberg measurement in characteristic three

## Problem

X. Zhu and Y. Wang, *Uniformly Stable Minimal Weyl–Heisenberg Measurements
Approaching the SIC Benchmark*, arXiv:2608.11850v1, measure the stability of a
minimal Weyl–Heisenberg measurement $\{\Pi_u=D_u|\phi\rangle\langle\phi|D_u^\dagger\}$
by $\eta(\phi)=\frac{d+1}{d}\lambda(\phi)$, where $\lambda(\phi)$ is the smallest
eigenvalue of the projector Gram matrix $G[u,v]=\mathrm{Tr}(\Pi_u\Pi_v)$ on the
complement of the constant vector, and call a dimension-indexed family uniformly
stable when $\inf_d\eta(\phi_d)>0$. On $\mathbb C^{\mathbb F_q}$ they use
$\psi(x)=\exp[\frac{2\pi i}{p}\mathrm{Tr}(x)]$, $X_a|x\rangle=|x+a\rangle$,
$Z_b|x\rangle=\psi(bx)|x\rangle$, $D_{a,b}=X_aZ_b$. They construct uniformly
stable families for $q=2^m$ and for characteristic $p\ge5$, and state twice
(Sections IV.B and VI) that a uniformly stable finite-field construction in
characteristic three remains open. The verbatim statements and definitions are
in [the literature note](../Library/QuantumStates/zhu2026uniformly.md).

Issue [#13556](https://github.com/the-omega-institute/trureturing/issues/13556)
fixes the reading: a constant $c>0$ and, for every $r\ge1$ and $q=3^r$, a unit
vector $\phi$ with $\lambda(\phi)\ge c\,q/(q+1)$, i.e. $\eta(\phi)\ge c$, where
$\lambda(\phi)\ge c'$ is stated in its Rayleigh-quotient form
$c'\sum_g|w_g|^2\le\mathrm{Re}\,w^*Gw$ for every $w$ with $\sum_gw_g=0$.

## Motivation

Stability is what makes a minimal informationally complete measurement usable
for tomography: the nonidentity Gram floor controls the error of linear
inversion and the shadow bounds. The paper's cubic Alltop mechanism excludes
characteristics two and three, and its characteristic-two family is a separate
construction; characteristic three was the remaining gap among prime powers.
`D5/S3/Quantum/Measurement/CharacteristicThreeUniformWeylHeisenbergStability.result`
closes it with $c=1/8$.

## Gap

Issue #13556 records the literature check before any Lean: the paper has a
single version (2026-08-12); the two later works found by the search seat use
its characteristic-two and characteristic-$\ge5$ families and give no
characteristic-three family (seat-reported); no Weyl–Heisenberg stability
construction exists in the repository. `not-found-in-searched-scope`.

## Route

Let $q=3^r$, $s=\sqrt q$ and $\zeta=e^{2\pi i/3}$.

1. **Witness.** $\phi(x)=(1/s+[x=0])/\sqrt{2+2/s}$, the normalized sum of the
   uniform vector and $|0\rangle$; it is the paper's characteristic-two family
   $\phi_{q,\theta}$ at $\theta=0$, now in characteristic three.
2. **Character sums.** $\psi$ is an additive character with values in
   $\{1,\zeta,\zeta^2\}$, and $\sum_x\psi(cx)=0$ for $c\neq0$ because the trace
   is a nonzero functional.
3. **Ambiguity.** $A(a,b)=\langle\phi,D_{a,b}\phi\rangle=
   [\delta_{b,0}+\delta_{a,0}+(1+\psi(-ab))/s]/(2+2/s)$. Off the axes
   $|1+\psi|\ge1$ since $\psi$ is a cube root of unity, and on the axes
   $|A|=(s+2)/(2(s+1))$; so $|A(h)|^2\ge1/(4(s+1)^2)$ for $h\ne0$.
4. **Gram form.** Expanding $|\phi\rangle\langle\phi|$ in the orthogonal
   displacement basis and using $D_gD_hD_g^\dagger=\kappa_h(g)D_h$,
   $w^*Gw=\frac1q\sum_h|A(h)|^2|\hat w(h)|^2$ with $\hat w$ the symplectic Fourier
   transform; Parseval and $\hat w(0)=\sum_gw_g=0$ give
   $w^*Gw\ge\frac q{4(s+1)^2}\sum_g|w_g|^2$.
5. **Constant.** $\frac q{4(s+1)^2}\ge\frac18\frac q{q+1}$ because
   $2(q+1)-(s+1)^2=(s-1)^2\ge0$.

## Falsifier

The proof would fail if $1+\psi$ could vanish off the axes (it does in
characteristic two, where $\psi=\pm1$) or if some nonzero frequency had a
nonvanishing character sum.

## Evidence

The canonical source is
`D5/S3/Quantum/Measurement/CharacteristicThreeUniformWeylHeisenbergStability.lean`.
Its public declarations are `F`, the instance `fintypeF`, `psi`, `D`, `proj`,
`gram`, `StableWith`, `claim` and `result`. The proof builds $\psi$ from
Mathlib's `ZMod.stdAddChar` composed with the trace and applies
`AddChar.sum_mulShift`, `traceForm_nondegenerate`, `GaloisField.card`, the
orthonormal-basis Parseval identity and `Matrix.trace_mul_comm`. It uses only
the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom. The module statement is
`sha256:6b98a01dbb5f24d3071f5048812bd2fd36c0074752bcb44a6aa12bff7586d20c`, the
`result` statement `sha256:f461f734bf73b6c5b279acf7f6527241edb19fb4676436b83e8f4bd1c95d7074`
and the `claim` statement
`sha256:760d63285d6b521710743306868649ee78c081a997fb9b0da46b4ffae396c6ca`. The Freeze event is
`sha256:41fbee72a3e45796fec1cc3f6ea457a7a35fecb104e1d88f9e88bd9ff73db5d0`; it
has no project-level frozen prerequisite.

Numerical check (exact $\mathrm{GF}(3^r)$ arithmetic, full $q^2\times q^2$ Gram
matrix): the smallest nonidentity eigenvalue equals $q/(4(\sqrt q+1)^2)$ at
$q=3,9,27$ (0.100481, 0.140625, 0.175816), so $\eta=0.134,0.156,0.182$.
Negative control: the same fiducial in characteristic two ($q=4$) has a zero
nonidentity eigenvalue.

## Triage

Tier 1 open item of a 2026 paper, preregistered in issue #13556 before any
Lean. `theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none | open-problem-resolution |

Every private theorem is bind-only and lies on the proof path of `result`
(CLAUDE.md §3.2 「有消费的辅助声明」); the list is in the source's judgement
comment. The instance `fintypeF` is a definition (`Fintype.ofFinite`), needed to
state the sums. The Freeze event also records two congruence lemmas,
`ZMod.stdAddChar.congr_simp` and `basisOfOrthonormalOfCardEqFinrank.congr_simp`,
that Lean realizes while `simp` elaborates in this module; they are
machine-generated restatements of the congruence of Mathlib constants, not
authored declarations, and no proof term of the module refers to them. Utility is `none`: the module proves a universal statement and
contains no finite enumeration, checker, numeric reduction or certified
instance. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the existential `claim`. Its proof takes $c=1/8$
and, for every $r\ge1$, the normalized fiducial $\phi\propto u+|0\rangle$ on
$\mathbb C^{\mathrm{GF}(3^r)}$, for which $\lambda(\phi)\ge\frac18\frac q{q+1}$, so
$\eta(\phi)\ge1/8$ uniformly.

**Established inside the proof.** The decisive fact is arithmetic: in
characteristic three the character takes only the cube roots of unity, so
$|1+\psi|\ge1$ and the spike never cancels off the axes; in characteristic two
$1+\psi$ vanishes, which is why the paper needs $\theta\ne0$ there. The Gram
form equals $\frac1q\sum_h|A(h)|^2|\hat w(h)|^2$ (`gram_fourier`).

**Argued, not formalized.**

- The bound is attained: the Gram eigenvalues on the complement of the
  constant vector are $q|A(h)|^2$, namely $\nu=\mu(s+2)^2$ on the $2(q-1)$
  axis labels, $4\mu$ on the $(q-1)(q/3-1)$ off-axis labels with
  $\mathrm{Tr}(-ab)=0$, and $\mu=q/(4(s+1)^2)$ on the remaining $2q(q-1)/3$; so
  $\lambda=\mu$ exactly and $\eta=(q+1)/(4(\sqrt q+1)^2)$, which tends to $1/4$
  (multiplicities computed at $q=3,9$; values at $q=3,9,27$ above), not to the
  SIC value 1.
- The same fiducial is uniformly stable in every fixed odd characteristic $p$:
  off the axes $|1+\psi|^2\ge4\sin^2(\pi/2p)$, so
  $\eta\ge(q+1)\sin^2(\pi/2p)/(\sqrt q+1)^2\ge\frac12\sin^2(\pi/2p)$ for all
  $q=p^r$; at $p=3$ this is the constant $1/8$. The middle bound is attained at
  $q=5,25,7$ (computed). The bound degrades as $p$ grows,
  so it is not uniform over all odd characteristics, and for $p\ge5$ the paper's
  balanced Alltop family is better.

**Open.** Whether characteristic three admits a family with $\eta\to1$ (the
SIC-normalized endpoint the paper reaches for $p\ge5$) is not addressed.

**Effect on the paper.** The open item of Sections IV.B and VI is settled: the
paper's uniform-stability conclusion now covers every prime power. Its
characteristic-$\ge5$ asymptotic optimality and its other results are
unaffected.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent construction. The search seat's
readings of the two citing works are seat-reported.
