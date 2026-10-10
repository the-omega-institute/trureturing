---
slug: kopel-2026-eb-norm-coefficient
bibkey: kopel2026sharpnorm
doi: 10.48550/arXiv.2609.27906
url: https://arxiv.org/abs/2609.27906v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/EntanglementBreakingNormCoefficient.result
---

# Optimality of the coefficient in the entanglement-breaking norm inequality

## Problem

E. Kopel, *A sharp norm inequality for entanglement-breaking channels*, arXiv:2609.27906v1, fixes
a Hermitian traceless basis $\lambda_1,\dots,\lambda_{d^2-1}$ of $M_d$ with
$\mathrm{Tr}[\lambda_i\lambda_j]=2\delta_{ij}$, writes a channel in Bloch form $r\mapsto Ar+c$ and
proves (Theorem 1) that every entanglement-breaking channel satisfies
$\|A\|_*^2+\tfrac{d(d-1)}{2}|c|^2\le(d-1)^2$. Item 3 of its open questions asks: "Is the
coefficient $d(d-1)/2$ optimal?" The verbatim statements are in
[the literature note](../Library/QuantumChannels/kopel2026sharpnorm.md).

Issue [#14492](https://github.com/the-omega-institute/trureturing/issues/14492) reads the
question as: for every $d\ge2$, every admissible basis and every real $B>d(d-1)/2$, some
entanglement-breaking channel has $\|A\|_*^2+B|c|^2>(d-1)^2$. The inequality with a coefficient
$\kappa$ becomes stronger as $\kappa$ grows, so this says that $d(d-1)/2$ is the largest admissible
coefficient.

## Motivation

The inequality is a necessary condition for entanglement breaking that uses both the linear part
and the translation part of the Bloch representation; the coefficient of $|c|^2$ measures how
much the translation part costs. `D5/S3/Quantum/QuantumChannels/EntanglementBreakingNormCoefficient.result`
proves that the coefficient cannot be increased in any dimension.

## Gap

Issue #14492 records the literature check before any Lean: the arXiv abstract page lists only v1
with no correction note; a search seat reported one citing work on INSPIRE (arXiv:2609.09350,
which uses the qubit bound and does not address the coefficient), no statement about the
coefficient in the antecedents arXiv:0803.0757 and arXiv:0709.3766, and no entry in MathDB or
google-deepmind/formal-conjectures; the repository had no result on this inequality.
`not-found-in-searched-scope`.

## Route

1. **Witness.** $\Phi(X)=\mathrm{tr}(X)\,P$ with $P=E_{00}$ has the Holevo form with the
   one-element measurement $\{I\}$ and the state $P$.
2. **Bloch data.** $\Phi(\lambda_j)=0$ because $\lambda_j$ is traceless, so $A=0$ and
   $\|A\|_*=0$; $\Phi(I/d)=P$, so $c_i=\mathrm{Tr}[\lambda_iP]=(\lambda_i)_{00}$.
3. **Parseval.** $\{I/\sqrt d,\ \lambda_i/\sqrt2\}$ is orthonormal for
   $\langle M,N\rangle=\mathrm{tr}(M^\dagger N)$ and has $d^2$ members, hence is an orthonormal basis
   of $M_d$; Parseval for $P$ gives $1=\tfrac1d+\tfrac12\sum_i(\lambda_i)_{00}^2$, so
   $|c|^2=\tfrac{2(d-1)}{d}$.
4. **Comparison.** $\|A\|_*^2+B|c|^2=\tfrac{2(d-1)}{d}B>(d-1)^2$ exactly when $B>\tfrac{d(d-1)}{2}$.

## Falsifier

The settlement would not stand under a reading of "optimal" that excludes channels with $A=0$.
The measure-and-prepare channel that measures in an orthonormal basis and prepares $d$
equiangular pure states with common squared overlap $q$ has
$\|A\|_*^2=(d-1)^2(1-q)$ and $\tfrac{d(d-1)}{2}|c|^2=(d-1)^2q$, so it attains equality in Theorem 1
with $A\ne0$ and $c\ne0$ for $0<q<1$; this family is argued and checked numerically for
$d=2,\dots,5$, not formalized.

## Evidence

- Lean owner: `D5/S3/Quantum/QuantumChannels/EntanglementBreakingNormCoefficient.lean`, module
  statement id `sha256:df0cc26319be0f9d34437c9b5cb97aba74dd8a57f625ee3bcfcaabe58d1ad123`.
- `claim` (statement id
  `sha256:bb80525c03f1330bbf5a5a3f44f62bef1bc218a38fe1672c27c4dbf2495a8875`) states the existence of a violating
  entanglement-breaking channel for every $d\ge2$, every admissible basis and every real
  $B>d(d-1)/2$; `result : claim` (statement id
  `sha256:47fd0d7eba6910fba2e3049425435d14a9d019826c96e85bc08aea5bd20d3c15`) proves it.
- Freeze event `sha256:8233a32af11dc7b5ef9ea546c8a5acad2f915ee4808970542c0545e9152dc654`, with the
  frozen prerequisites `D5/S3/Quantum/Foundation/FiniteTraceDistance`
  (`sha256:acba73dc960a507d71dd7cef5de9c284070f64bfdb6ff23e448d932d18189f73`) and
  `D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation`
  (`sha256:77e392d1fa6a77588e1471e1bc03a7bfe508df4aa5797f635942f8e5993a0bd3`).
- `#print axioms result`: `propext`, `Classical.choice`, `Quot.sound`.

## Triage

Tier 1 open question of an August 2026 paper, preregistered in issue #14492 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none | open-problem-resolution |

The private theorems are bind-only and used on the proof path of `result` (CLAUDE.md §3.2
「有消费的辅助声明」); the consumer list is in the module's judgement comment. Utility is `none`.
There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every $d\ge2$, every Hermitian traceless family with
$\mathrm{Tr}[\lambda_i\lambda_j]=2\delta_{ij}$ and every real $B>d(d-1)/2$ there is an
entanglement-breaking $\Phi$ with $(d-1)^2<\|A\|_*^2+B|c|^2$.

**Established inside the proof.** For every admissible basis,
$\sum_i(\mathrm{Re}\,(\lambda_i)_{00})^2=\tfrac{2(d-1)}{d}$ (`sum_sq_diag`): the Bloch vector of a
rank-one projection has squared length $2(d-1)/d$ in any admissible basis, not only in the
generalised Gell-Mann basis.

**Argued, not formalized.**

- *Mechanism.* At $A=0$ the inequality of Theorem 1 reads $|c|^2\le2(d-1)/d$, the bound on the
  Bloch vector of a state, which is attained exactly by pure states. A constant channel onto a
  pure state therefore sits on the boundary, and the coefficient of $|c|^2$ is fixed by this
  single point.
- *Item 2 of the source.* The same channel has $c\ne0$ and equality in Theorem 1 for every $d$,
  so equality with $c\ne0$ is achievable for $d\ge3$; the equality conditions (i)–(iv) of Section 4
  of the source are not all necessary when every output state equals the same pure state, because
  the centred outputs $s_k-c$ vanish.
- *Non-degenerate equality.* The equiangular family of the Falsifier section attains equality with
  $A\ne0$ and $c\ne0$, so the two bounds combined in the proof of Theorem 1 are simultaneously
  saturable in every dimension.

**Open.** Item 1 of the source (the exact entanglement-breaking body between Theorem 1 and the
sufficient condition $\|A\|_*+|c|\le1$ at $d=2$) and item 4 (a basis-free formulation) are not
addressed. Theorem 1 itself is not formalized here.

**Effect on the paper.** Item 3 of the open questions is answered affirmatively, and the remark of
Section 4 that equality with $c\ne0$ for $d\ge3$ is not settled is answered by the constant
channel.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty, priority, or the
absence of an independent proof. The INSPIRE, MathDB and formal-conjectures readings are
seat-reported.
