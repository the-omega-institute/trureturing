---
slug: garcia-velo-2026-product-unitary-choi-spectrum
bibkey: garciavelo2026schwarz
doi: 10.48550/arXiv.2601.02282
url: https://arxiv.org/abs/2601.02282v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.result
---

# The Choi spectrum of unital product-unitary-equivariant maps

## Problem

A. García-Velo and A. Ibort, *Schwarz maps with symmetry*, arXiv:2601.02282v1, classify the
unital, Hermiticity-preserving maps on $M_{n_1}(\mathbb C)\otimes M_{n_2}(\mathbb C)$ that commute
with conjugation by $U\otimes V$: they are
$\Phi=D_1\otimes D_2+\lambda_{01}D_1\otimes Q_2+\lambda_{10}Q_1\otimes D_2+\lambda_{11}Q_1\otimes Q_2$
with real weights, where $D_i(X)=\mathrm{tr}(X)\,I/n_i$ and $Q_i=\mathrm{id}-D_i$. Lemma V.8 gives
the eigenvalues of the Choi matrix $C_\Phi=\sum_{p,q}E_{pq}\otimes\Phi(E_{pq})$ for
$n_1,n_2\in\{2,3\}$, and Remark V.2 conjectures the same four values, with multiplicities $1$,
$n_1^2-1$, $n_2^2-1$ and $(n_1^2-1)(n_2^2-1)$, in every dimension. The verbatim statements are in
[the literature note](../Library/QuantumChannels/garciavelo2026schwarz.md).

Issue [#14200](https://github.com/the-omega-institute/trureturing/issues/14200) reads the
conjecture as an identity of characteristic polynomials, which records the eigenvalues with
their algebraic multiplicities, for $n_1,n_2\ge1$ and complex weights.

## Motivation

The Choi spectrum decides complete positivity of $\Phi$ (Choi's theorem), and the paper uses it to
describe the completely positive region and to check the PPT² property for $(n_1,n_2)=(2,2)$ and
$(2,3)$. `D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.result` proves the conjectured
spectrum for all $n_1,n_2\ge1$.

## Gap

Issue #14200 records the literature check before any Lean: arXiv lists only v1; arXiv API searches
for the title, for product-unitary and local-unitary covariant Choi eigenvalues and for $U(n_1)$
with $U(n_2)$ return this paper and arXiv:2404.10895 (qubit $DU(2)$ maps); arXiv:1811.08193 treats
single-$U(n)$ equivariant maps and does not state this spectrum; a search seat reported zero
INSPIRE citations and no entry in google-deepmind/formal-conjectures; the repository had no
result on these maps. `not-found-in-searched-scope`.

## Route

1. **Sector form.** The Choi matrix of $D$ is $I/n$ and that of $Q$ is $K-I/n$, where $K=\omega\omega^{\mathsf T}$ and
   $\omega=\sum_je_j\otimes e_j$. Grouping the indices of $C_\Phi$ by factor gives
   $aI+b\,(I\otimes K_2)+c\,(K_1\otimes I)+d\,(K_1\otimes K_2)$ with the source's $a,b,c,d$.
2. **Shear.** With $u=\omega-e_{00}$, $S=I+ue_{00}^{\mathsf T}$ has inverse $I-ue_{00}^{\mathsf T}$ because
   $e_{00}^{\mathsf T}u=0$, and $S^{-1}KS=e_{00}(\omega+(n-1)e_{00})^{\mathsf T}$ has a single nonzero row with
   diagonal entry $n$.
3. **Blocks.** After conjugation by $S_1\otimes S_2$ the matrix is block upper triangular for the
   four blocks "first index $=(0,0)$ or not, second index $=(0,0)$ or not", each block a multiple
   of the identity: values $a+bn_2+cn_1+dn_1n_2$, $a+cn_1$, $a+bn_2$, $a$ on blocks of sizes $1$,
   $n_2^2-1$, $n_1^2-1$, $(n_1^2-1)(n_2^2-1)$.

## Falsifier

The settlement would change under a reading of the eigenvalues other than as the roots of the
characteristic polynomial counted with algebraic multiplicity, or under a Choi convention other
than $\sum_{p,q}E_{pq}\otimes\Phi(E_{pq})$; for real weights $C_\Phi$ is Hermitian, so algebraic and
geometric multiplicities agree.

## Evidence

- Lean owner: `D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.lean`, module statement id
  `sha256:c8832dbe0412e1a29f77d85253d4e998ebc7907c8121e7ceaafc7db22e0c3bf2`.
- `claim` (statement id `sha256:187a9b5607d6a7db1552ea74e2ce603c7ca3efe2991912bc3553e30dfd581f24`)
  states the characteristic-polynomial identity for all $n_1,n_2\ge1$ and complex weights;
  `result : claim` (statement id
  `sha256:f58ed2d9e28956c96241bb85b52e5d77590f78f5beb6a1ce72e9a9d24d7ab21c`) proves it.
- Freeze event `sha256:910a2b2de39f9a730f0a9cc501d442b4d1730e9f33fb28607f033f28aadd543e`, with the
  frozen prerequisite `D5/S3/Quantum/Foundation/FiniteKrausChannel`
  (`sha256:260af10ef3dd71e5df80b276fb86150bfeac5abf14a7b2ee3dda7ce20167d26a`).
- `#print axioms result`: `propext`, `Classical.choice`, `Quot.sound`.

## Triage

Tier 1 conjecture of a January 2026 paper, preregistered in issue #14200 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none | open-problem-resolution |

The other public declarations (`omega`, `kmat`, `dmat`, `qmat`, `omega_dot_omega`,
`choi_reindex`) and the private theorems are bind-only or definitions used on the proof path of
`result` (CLAUDE.md §3.2 「有消费的辅助声明」); the consumer list is in the module's judgement
comment. Utility is `none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for all $n_1,n_2\ge1$ and complex $\lambda_{01},\lambda_{10},\lambda_{11}$, the
characteristic polynomial of $C_\Phi$ is
$(X-e_1)(X-e_2)^{n_1^2-1}(X-e_3)^{n_2^2-1}(X-e_4)^{(n_1^2-1)(n_2^2-1)}$ with the four values of
Lemma V.8.

**Established inside the proof.** The reindexed Choi matrix equals
$D_1^{C}\otimes D_2^{C}+\lambda_{01}D_1^{C}\otimes Q_2^{C}+\lambda_{10}Q_1^{C}\otimes D_2^{C}+\lambda_{11}Q_1^{C}\otimes Q_2^{C}$
with $D^C=I/n$ and $Q^C=K-I/n$ (`choi_reindex`), and the shear conjugation of $K$ (`conj_kmat`).

**Argued, not formalized.**

- *Mechanism.* $C_\Phi$ is a polynomial in the two commuting operators $K_1\otimes I$ and
  $I\otimes K_2$; each single-factor $K_i$ has eigenvalues $n_i$ (multiplicity $1$) and $0$
  (multiplicity $n_i^2-1$), and tensoring with the identity multiplies these multiplicities by the
  dimension of the other factor.
  Each eigenvalue of $C_\Phi$ is $\sum_{\alpha,\beta}\lambda_{\alpha\beta}\,c_\alpha^{(1)}c_\beta^{(2)}$ with
  $c_0^{(i)}=1/n_i$ and $c_1^{(i)}\in\{n_i-1/n_i,\,-1/n_i\}$; this is why the values Lemma V.8
  computed in dimensions $2$ and $3$ keep their form.
- *Extension.* The same argument gives the Choi spectrum of $\sum_{S}\lambda_S\bigotimes_iP^{(i)}_{[i\in S]}$
  on any number $m$ of tensor factors: $2^m$ values indexed by subsets $T$ of the factors, with
  multiplicity $\prod_{i\in T}(n_i^2-1)$.
- *Complete positivity.* For real weights and $n_1,n_2\ge2$ all four multiplicities are positive,
  so by Choi's theorem $\Phi$ is completely positive iff $e_1,e_2,e_3,e_4\ge0$: four linear
  inequalities in every dimension, the form the paper found for $(2,2)$ and $(2,3)$.

**Open.** The Schwarz-map region for general $(n_1,n_2)$ is not addressed here. The PPT² property
of this family in every dimension is the subject of issue #14289.

**Effect on the paper.** Remark V.2 holds in every dimension, and the complete-positivity
description of Propositions V.6 and V.7 extends to all $n_1,n_2\ge2$ through Choi's theorem.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty, priority, or the
absence of an independent proof.
