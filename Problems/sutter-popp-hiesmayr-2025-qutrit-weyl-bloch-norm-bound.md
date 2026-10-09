---
slug: sutter-popp-hiesmayr-2025-qutrit-weyl-bloch-norm-bound
bibkey: sutter2026grouptheoretic
doi: 10.1103/z7jn-4try
url: https://arxiv.org/abs/2508.18393v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/QutritWeylBlochNormSeparableBound.result
---

# A sharp Weyl–Bloch ℓ1 entanglement criterion for two qutrits

## Problem

T. C. Sutter, C. Popp and B. C. Hiesmayr, Phys. Rev. A 113, 032440 (2026); arXiv:2508.18393v2,
Section VI (p. 10):

> Going forward, it is furthermore an open problem whether for general bipartite qudit states, an
> entanglement criterion based on the entry-wise 1-norm of the Bloch vector, similar to Thm. IV.1, can
> be derived. … A quick numerical optimization for $d=3$ yields $\Vert\beta\Vert_1 \lesssim 25.9735$ for
> general pure states $|\psi\rangle\in\mathbb C^3\otimes\mathbb C^3$, whereas separable pure states seem
> to satisfy $\Vert \beta\Vert_1 \leq 25$.

Here $\beta_{ij,kl}={\rm tr}(\rho\,(W_{i,j}\otimes W_{k,l})^\dagger)$ with the Weyl–Heisenberg operators
$W_{k,l}=\sum_j\omega^{jk}|j\rangle\langle j+l|$, $\omega=e^{2\pi i/3}$, and $\Vert\beta\Vert_1=\sum|\beta_{ij,kl}|$.
The verbatim texts are in [the literature note](../Library/QuantumChannels/sutter2026grouptheoretic.md).
Issue [#14780](https://github.com/the-omega-institute/trureturing/issues/14780) preregisters the reading
and the proof plan.

## Motivation

The source characterizes PPT and realignment entanglement for Bell-diagonal qutrit states through the
entry-wise 1-norm of their Bloch vectors and asks whether the same norm yields an entanglement
criterion for arbitrary bipartite states. A sufficient condition for separability ($\Vert\beta\Vert_1\le2$)
is known; the naive entanglement threshold $d^3$ is vacuous because no state exceeds it.

## Gap

The source reports only numerics. The literature check in #14780 found no proof of the separable bound
and no entanglement criterion of this form; `not-found-in-searched-scope`.

## Route

1. ${\rm tr}(W_{k,l}W_{k',l'}^\dagger)=3\delta_{kk'}\delta_{ll'}$, so a qutrit density matrix $\sigma$ with
   $a_{kl}={\rm tr}(\sigma W_{k,l}^\dagger)$ has $\sum|a_{kl}|^2=3\,{\rm tr}\,\sigma^2\le3$ and $a_{00}=1$; Cauchy–Schwarz
   over the other eight coefficients gives $\sum|a_{kl}|\le1+\sqrt{8\cdot2}=5$.
2. $\beta(\sigma\otimes\tau)_{ij,kl}=a_{ij}b_{kl}$ gives $\Vert\beta\Vert_1\le25$ on products, and linearity of $\beta$ with
   the triangle inequality extends it to every separable state.
3. $u=(0,1,-1)/\sqrt2$ has coefficient moduli $1$ and eight times $1/2$, so $|u\rangle\langle u|^{\otimes2}$ attains $25$.
4. $\psi=(2|00\rangle+|02\rangle+|11\rangle-|20\rangle)/\sqrt7$ has $\Vert\beta\Vert_1=(169+2\sqrt{13})/7>25$.

## Falsifier

An error in the orthogonality relation, the purity bound, the product factorization or the exact value of
step 4, or a reading of $W_{k,l}$, $\beta$ or separability different from the source. Positive controls in
#14780: the product of step 3 gives exactly $25$; numerical maximization over pure states reproduces the
source's $25.9735$.

## Evidence

`D5/S3/Quantum/Entanglement/QutritWeylBlochNormSeparableBound.lean` defines `omega`, `W` (eq. (7)), `bloch`
(eq. (16)), `l1`, `IsSeparable` (the source's finite convex combination of products of density
matrices, with the frozen `GHZMeasureBiseparableBound.IsDensity`) and `claim`, and proves `result : claim`, the conjunction of the separable bound, its attainment
and a normalized pure state exceeding it. It reuses the frozen `HesseSicCertificate.omega_cubed`, which this
delivery makes public, and the frozen `RHLinalg.frobSq_hermitian_eq_sum_sq_eigenvalues`. The axiom closure
of `result` is exactly `propext`, `Classical.choice` and `Quot.sound`; there is no `sorry` or `native_decide`.
The module statement is `sha256:170c8f0aefa2f62dfe725896ee4e9c14d12e6873a424b9997d87ab1d04c70c46`; `result` is
`sha256:f16841e49be3cb6ba08c2cef14402d257ec0befa5040a022aaddd1f6bd3957f9` and `claim` is
`sha256:ad3ad8a012ae2bf4364b72126235796c70144e551e3d255cc70bf2f4759198cd`. The Freeze event is
`sha256:f8df9428c7b4dc915de755fd083e109ebd1ad7cfc76f074ee80a1d36b59eea52`.

## Triage

Tier 1: an open problem and a numerical observation of a 2025 paper, retained in its 2026 journal
version, preregistered in #14780 before any Lean. `theorem`; resolution `proved` for $d=3$. `result` is
bind-only by CLAUDE.md §3.2 (orthogonality and Parseval by normalization, instantiation of the frozen
eigenvalue identity, Cauchy–Schwarz, and explicit coefficient tables); admission basis
`open-problem-resolution`. Utility `none`: the fixed matrices of steps 3–4 are private ingredients of the
universal statement. There is no digestion atom. Escape audit: the registration attempt for `result` is
unresolved (#14821).

### What the proof shows

- **Proved by `result`:** every separable two-qutrit state has Weyl–Bloch ℓ1-norm at most $25$, the bound is
  attained by a product state, and a pure state exceeds it; so $\Vert\beta\Vert_1>25$ is a sound, sharp and
  non-vacuous entanglement criterion for two qutrits, and the source's numerical observation for
  separable pure states holds.
- **Mechanism:** the bound factorizes into two local bounds, each a Cauchy–Schwarz estimate between the
  ℓ1 and ℓ2 norms of the eight nontrivial Weyl coefficients, whose ℓ2 norm is fixed by purity.
- **Derived, not formalized:** for qudits of dimension $d$ the same argument gives
  $\Vert\beta\Vert_1\le\bigl(1+(d-1)\sqrt{d+1}\bigr)^2$ for every separable state, with equality for a product
  state exactly when all $d^2-1$ nontrivial coefficients of both factors have modulus $1/\sqrt{d+1}$, that
  is, when both factors are Weyl–Heisenberg SIC fiducials. The bound is therefore attained in every
  dimension in which such a fiducial exists. For $d=3$ the attaining $u$ above is such a fiducial.
- **Open:** whether some state exceeds $\bigl(1+(d-1)\sqrt{d+1}\bigr)^2$ for $d\ge4$ (that is, whether the
  criterion is non-vacuous in higher dimensions), and the exact maximum of $\Vert\beta\Vert_1$ over pure
  two-qutrit states (numerically $\approx25.9735$).

## ASSUMED-UNVERIFIED

The literature check in #14780 is bounded and does not establish worldwide novelty or priority; the
single-qutrit inequality of step 1 is the Cauchy–Schwarz bound used for stabilizer-entropy maxima and is
not claimed as new.
