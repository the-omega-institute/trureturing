---
slug: huynh-vu-zaw-scarani-2023-precession-separable-bound
bibkey: huynhvu2024precession
doi: null
url: https://arxiv.org/abs/2311.00806
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.result
---

# Spin-1 tensor spin-K/2 precession separable bound

## Problem

Khoi-Nguyen Huynh-Vu, Lin Htoo Zaw and Valerio Scarani,
*Certification of genuine multipartite entanglement in spin ensembles with
measurements of total angular momentum*, arXiv:2311.00806v2, §III,
Conjecture 2, Eq. (32), PDF p. 8:

> The separable bound for {ȷ̃, ȷ̃′} = {1, K/2} with K ≥ 7 is
> Psep_K({1, K/2}) = ½ [1 + 2^{−(K−1)} binom(K−1, (K−1)/2) (K−1)/(K+1)].

The protocol takes odd K, J_k = cos(2πk/K)J_x + sin(2πk/K)J_y,
and Q_K = (1/K) Σ_k pos(J_k), where 2 pos acts on an eigenvalue m
as 1+sgn(m), including half weight at zero. Eqs. (7) and (10) express
the separable bound as the maximum over unit product pure states.
The two factors here have dimensions 3 and K+1. Preregistration:
https://github.com/the-omega-institute/trureturing/issues/11873.

## Motivation

`D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.result`
proves the quantified product-pure form of Conjecture 2. The public
spin matrices, precession observable and spectral projector follow the
source definitions; the compression is a proved identity, not a definition
of the observable. The literature anchor is
`Library/QuantumStates/huynhvu2024precession.md`.

## Gap

The paper states that it could not prove Eq. (32), and reports agreement
with numerics through K=101. The preregistered literature reading checks
the paper and the related works arXiv:2311.00805, 2405.17966, 2411.03132,
2401.16147, 2401.14328 and 2509.03166. It records no proof of Eq. (32)
in that searched scope; this is not a claim of literature priority.
The published journal version is not verified here.

## Route

The spectral projectors use Mathlib’s `Matrix.IsHermitian.cfc` with
`positiveWeight` and `Real.sign`; the finite spectrum requires no
continuity hypothesis. The proof constructs the binomial/Krawtchouk
eigenbasis of J_x and its inverse by polynomial homogenization. A root-of-unity filter computes the
rotation average. The half-integer sign decomposition retains the
nonzero endpoint contribution (−1)^L c_K, with K=2L+1.

For a unit spin-1 state a, the compression of 2Q_K−I is supported on
indices {0,1,2,K−2,K−1,K}. Its off-diagonal block is
(−1)^L c_K M/(K+1), where y=|a₁|², w=conj(a₀)a₁+conj(a₁)a₂,
z=conj(a₀)a₂ and

$$
M=\begin{pmatrix}
1-Ky & \sqrt{2K}\,w & \sqrt{K(K-1)/2}\,z\\
\sqrt{2K}\,w & -z & 0\\
\sqrt{K(K-1)/2}\,z & 0 & 0
\end{pmatrix}.
$$

The squared Frobenius bound uses |w|²≤2y(1−y) and
|z|²≤(1−y)²/4. Its scalar remainder is

$$
f_K(y)=(1-Ky)^2+8Ky(1-y)+\frac{K^2-K+1}{4}(1-y)^2-(K-1)^2.
$$

For K≥7, its quadratic coefficient (5K²−33K+1)/4 is nonnegative;
f_K(0)≤0 and f_K(1)=0 imply f_K(y)≤0 on [0,1]. Cauchy–Schwarz
then bounds the full product quadratic form. The spin-1 middle state
and a phase-adjusted superposition of the two endpoint states attain
that bound. Every auxiliary proof is local to the single public `result`.

## Falsifier

The claim would fail if a unit product state at any odd K≥7 exceeded
the formula, or if the stated value were not attained. `IsGreatest`
proves both the universal upper bound and attainment. Numerical examples
are outside the proof premises. Even K and K<7 are outside this statement.

## Evidence

The canonical module is
`D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.lean`;
its Scribe mirror displays every public definition and `claim`/`result`.
The imports are pinned Mathlib; there are no frozen D5 prerequisites.
The Lean kernel axiom closure of `result` is `propext`, `Classical.choice`
and `Quot.sound`.

Boundary computations use NumPy 2.2.5 / SciPy 1.16.0 with the literal
spin matrices and spectral projector. Run the following program with `python3`.
It diagonalizes Q compressed by
$a=(\sin\alpha/\sqrt2,\cos\alpha,\sin\alpha/\sqrt2)$ and maximizes
only this one-parameter family. Its outputs are numerical lower bounds,
not certified global maxima. Eigenvalues within $10^{-10}$ of zero receive
the half weight; this numerical tolerance is not part of the Lean definition.

```python
import numpy as np
from scipy.optimize import minimize_scalar

def spin(n):
    j = n / 2
    raising = np.zeros((n + 1, n + 1), dtype=complex)
    for r in range(1, n + 1):
        m = j - r
        raising[r - 1, r] = np.sqrt(j * (j + 1) - m * (m + 1))
    return (raising + raising.conj().T) / 2, (raising - raising.conj().T) / (2j)

def boundary(k):
    ax, ay = spin(2)
    bx, by = spin(k)
    x = np.kron(ax, np.eye(k + 1)) + np.kron(np.eye(3), bx)
    y = np.kron(ay, np.eye(k + 1)) + np.kron(np.eye(3), by)
    q = np.zeros_like(x)
    for r in range(k):
        angle = 2 * np.pi * r / k
        values, vectors = np.linalg.eigh(np.cos(angle) * x + np.sin(angle) * y)
        weights = np.where(values > 1e-10, 1, np.where(values < -1e-10, 0, 0.5))
        q += (vectors * weights) @ vectors.conj().T / k
    def score(alpha):
        a = np.array([np.sin(alpha) / np.sqrt(2), np.cos(alpha), np.sin(alpha) / np.sqrt(2)])
        compressed = np.einsum('p,piqj,q->ij', a.conj(), q.reshape(3, k + 1, 3, k + 1), a)
        return np.linalg.eigvalsh(compressed)[-1]
    optimum = minimize_scalar(lambda alpha: -score(alpha), bounds=(0, np.pi / 2),
                              method='bounded', options={'xatol': 1e-14})
    print(k, 'alpha', optimum.x, 'score', -optimum.fun, 'middle_score', score(0))

for k in (3, 5):
    boundary(k)
```

## Triage

Conjecture 2 is proved in its preregistered product-pure form.
`proof_shape: content`; `admission_basis: open-problem-resolution`
(#11873; Proved); `utility: none`. This is an unbounded analytic proof,
not a bounded enumeration or certified finite instance. Registration is
paused under CLAUDE.md §3.9. No atom or coverage edge is used.

### What the settlement shows

- **Proved in this module:** The decisive mechanism is the exact six-index
  compression, including the sign operator's endpoint term, followed by
  the Frobenius estimate and an explicit attaining state. The equality
  holds for every odd K≥7, rather than just the paper's numerical range.
  The middle-state construction establishes sharpness for this product
  score; it does not classify all optimizers.
- **Computed with the Evidence command:** K=3 gives a product score
  0.6603513979123848 at α=0.6945473082666525, exceeding the extrapolated
  formula 0.625. This explains why a statement covering all odd K≥3
  would need a different bound. At K=3 the two sets of three edge indices
  also overlap; the disjoint six-index block argument does not apply.
  The value is a numerical witness, not a Lean refutation or a certified
  claim of global optimality.
- **Computed by exact rational coefficient expansion:** At K=5 the
  coefficients of f_K, in ascending powers of y, are
  (−39/4,39/2,−39/4), so f_5(y)=−(39/4)(1−y)²≤0.
  Command: `python3 -c 'from fractions import Fraction as F; k=5; print(F(-3*k*k+7*k+1,4), F(-k*k+13*k-1,2), F(5*k*k-33*k+1,4))'`.
  The calculation uses exact `fractions.Fraction` coefficients
  ((−3K²+7K+1)/4,(−K²+13K−1)/2,(5K²−33K+1)/4).
  Thus the nonnegative-quadratic-coefficient shortcut requires K≥7,
  but the scalar Frobenius estimate itself also permits K=5. The
  numerical middle-state score at K=5 is 0.625. **Open:** extending the
  matrix compression and attainment proofs to K=5; this module's local
  identities require L≥3 and do not establish that extension.
- **Open:** Other spin pairs need a new sign decomposition and compression
  estimate. The spin-1 factor is used through its three eigenlevels;
  the present proof supplies no uniform bound for other first spins,
  nor a classification of even-K protocols.
- **Proved in this module / source interpretation:** For the pair {1,K/2}
  the exact threshold in Eq. (32) is available without a numerical
  cutoff, so the source's criterion that exceeding the separable bound
  certifies entanglement has this analytic threshold. **Open:** a separate
  formalization of mixed separable density matrices and their convex
  reduction to product pure states. Eq. (10) already supplies that source
  reading. The paper's results for other spin pairs and its other
  conjectures receive no additional formal conclusion here.

## ASSUMED-UNVERIFIED

The external literature reading is the preregistration's searched scope;
completeness and the published journal version are not verified. The
source-to-Lean interpretation and mixed-state convex reduction are
semantic review obligations, distinct from the kernel-checked pure-product
statement. Numerical boundary values are floating-point computations;
they carry neither exact certification nor a global-optimality claim.
