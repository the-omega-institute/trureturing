---
slug: debrota-2020-orthocross-nonorthogonality
bibkey: debrota2020varieties
doi: 10.1142/S0219749920400055
url: https://arxiv.org/abs/1812.08762v5
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/OrthocrossNonorthogonality.result
---

# Orthocross MIC elements are never orthogonal, and their Gram entries tend to zero

## Problem

J. B. DeBrota, C. A. Fuchs and B. C. Stacey (arXiv:1812.08762v5, quant-ph; Int. J. Quantum Inf. 19
(2021) 2040005) define the orthocross MIC of an orthonormal basis $\{|j\rangle\}$ of $\mathbb C^d$:
- $\Pi_\alpha$ runs over the $d^2$ projectors onto $|j\rangle$, $(|j\rangle+|k\rangle)/\sqrt2$ and
  $(|j\rangle+i|k\rangle)/\sqrt2$ ($j<k$);
- $\Omega=\sum_\alpha\Pi_\alpha$;
- $E_\alpha=\Omega^{-1/2}\Pi_\alpha\Omega^{-1/2}$;
- the Gram matrix is $G_{\alpha\beta}=\operatorname{tr}E_\alpha E_\beta$.

The paper states:

> The entries in $G$ for orthocross MICs can become arbitrarily small with increasing $d$, but no two
> elements of an orthocross MIC can be exactly orthogonal.

The verbatim statements are in [the literature note](../Library/QuantumStates/debrota2020varieties.md).
Issue [#14213](https://github.com/the-omega-institute/trureturing/issues/14213) reads the conjecture
as two clauses, both for every $d$ and every orthonormal basis:
- (A) every off-diagonal Gram entry is a strictly positive real number;
- (B) every Gram entry tends to zero uniformly as $d\to\infty$.

## Motivation

The orthocross MICs, introduced by Caves, Fuchs and Schack for the quantum de Finetti theorem, are the
standard reference measurements built from a single basis. The authors report that the conjecture
came from numerical investigations and that its proof had eluded them. Stacey (arXiv:1911.07386)
notes that open conjectures about orthocross MICs remain.

## Gap

Issue #14213 records the literature check before any Lean:
- arXiv metadata search for "orthocross": 0 records;
- full-text search: only the source and Stacey's two notes, which do not settle the conjecture;
- the 10 arXiv citers of 2024–2026 do not mention orthocross MICs;
- Zenodo: 0 records.

`not-found-in-searched-scope`.

## Route

1. $G_{\alpha\beta}=w_\alpha w_\beta\,\lvert v_\alpha^\dagger M v_\beta\rvert^2$ with $M=\Omega^{-1}$ in the standard
   basis, the weights $w$ equal to $1$ or $\frac12$, and $v_\alpha$ the unnormalized vectors. This uses
   basis covariance from the frozen half-integrality module.
2. Clause (B): Gershgorin gives $\Omega\ge\frac d4 I$, hence $\|M\|\le 4/d$ and $\lvert G_{\alpha\beta}\rvert\le 256/d^2$.
3. Closed form: with $L=d-\frac{1-i}2$ and $q=\bar L/L$ ($\lvert q\rvert=1$),
   $M_{jk}=u\,q^{j-k+1}$ for $j<k$, the conjugate entries below the diagonal, and a positive real diagonal
   $t$. The constants are explicit, and $\Omega M=I$ is proved by geometric sums.
4. Clause (A):
   - multiplying by $(1-q)q^{d-2}/u$ turns $v_\alpha^\dagger Mv_\beta$ into the value at $q$ of a polynomial
     with Gaussian-integer coefficients of norm at most $16$;
   - its value and derivative at $1$ show that this polynomial is never zero;
   - $q=A/B$ with $A=(d-1)-di$ and $B=d-(d-1)i$, coprime by an explicit Bézout identity; a root at $q$
     would make $B$ divide the leading coefficient, impossible for $d\ge4$ since $N(B)=2d^2-2d+1>16$;
   - $d=2,3$ are checked exactly.

## Falsifier

The statement concerns the orthocross vectors with phases $1$ and $i$ and the inverse square root
$\Omega^{-1/2}$. The proof uses the specific Toeplitz-like structure of $\Omega$ ($d$ on the diagonal,
$\frac{1\mp i}2$ off it). Other cross phases change $\Omega$ and are outside the claim.

## Evidence

The canonical sources are:
- `D5/S3/Quantum/Measurement/OrthocrossNonorthogonality.lean` (public `claim` and `result : claim`);
- `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.lean` (the closed inverse);
- `D5/S3/Quantum/Measurement/OrthocrossPairingPolynomial.lean` (the polynomial obstruction).

They reuse the frozen `vec`, `weight`, `proj`, `frame`, `mic` and `gram` of
`D5/S3/Quantum/Measurement/OrthocrossGramHalfInteger`. That module exposes its basis covariance and
trace reduction (`proj_eq`, `frame_eq`, `posDef_one`, `gram_eq`, `frame_one`) at their origin. The power-difference estimate `norm_pow_sub_pow_le`, previously a private theorem of
`D5/S3/AnalyticClosure/Polylogarithm/CompositionBanksLeadingClosure`, now lives in the shared module
`D5/S3/AnalyticClosure/ComplexPowerDifference`, used by both modules, with its statement and proof unchanged.

The axiom closure of `result` is exactly `propext`, `Classical.choice` and `Quot.sound`. There is no
`sorry`, no `native_decide` and no new axiom.

Module statements:
- `OrthocrossNonorthogonality` `sha256:f67dc87390a9c3aa80d2828495a74ac6df603d509f7e31176f589f9a79bdd29c`, with `result` statement `sha256:8643867bae425e6c54b5407b1010840f216c158c9fabdaa8e5b05360823d3efb` and `claim` statement `sha256:980463579004c56b5623f152b47e96fe5b8c5a7b8b4b0cbbeb028762100acd72`;
- `OrthocrossPairingPolynomial` `sha256:c081137237c75a072446bd68a26a574130bd89911498095c16b01fa3fa2078ad`;
- `OrthocrossInverseFrame` `sha256:fbf6675b37ea4634ae8326a91a34e11ce83e006b08822e5f62b80dc0ad9fa263`.

Freeze events:
- `OrthocrossNonorthogonality` `sha256:59d256a8952623235046390a724cee7423e042b7ea93f92625d21008964b41a8` (prerequisite: the pairing module);
- `OrthocrossPairingPolynomial` `sha256:bd31a093508ad4fc75b55620f1dbf39411bae4cec64f737f02c5c358138b444c` (prerequisite: the inverse module);
- `OrthocrossInverseFrame` `sha256:b271cefafcc9f26c6d243d8108f5eee918c00ce4dbb600d39d09ff63fc689405` (prerequisites: the re-pinned `OrthocrossGramHalfInteger`, Freeze event `sha256:5ffeb9a36ac6534935003bc70cb8e9bc0ab12173f5f19a1e4b7f75b6e9362d03`, and `ComplexPowerDifference`, Freeze event `sha256:5093366ae5c13b7912901d46ce6956c8acac00dfd98ac3eae30f255adefeb704`, module statement `sha256:b7edbb5cf79561007f44e5c761060c2fa581c7aaa1052a2f07ab94afa744ef71`).

## Triage

Tier 1 conjecture of a 2018 paper (still stated in v5), preregistered as research line #14213 before any
Lean. `theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| `OrthocrossNonorthogonality.result` | content | `gram_pos` (the positivity of every Gram entry) | open-problem-resolution |
| `OrthocrossInverseFrame.frame_mul_candidate` | content | the closed geometric inverse, $\Omega M=I$ | escape-witness |
| `OrthocrossPairingPolynomial.pairingPolynomial_ne_zero` | content | the nonvanishing of every pairing polynomial | escape-witness |

The other public theorems of the three modules lie on the proof path of `result`. Utility is `none`
for all three. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every dimension $d$ and every orthonormal basis, every off-diagonal Gram entry
of the orthocross MIC is a strictly positive real number, and every Gram entry tends to zero uniformly in
the basis as $d$ grows.

**Proved inside the proof, for every $d$.**
- Every Gram entry, the diagonal included, is a strictly positive real number (`gram_pos`).
- Every Gram entry is at most $256/d^2$ in modulus (`gram_norm_bound`).
- $\Omega^{-1}$ has the closed form above: all off-diagonal entries have the same modulus $\lvert u\rvert$,
  their phases are powers of the unit $q=\bar L/L$, and the diagonal is a positive constant.
- No inverse-frame pairing $v_\alpha^\dagger\Omega^{-1}v_\beta$ vanishes, equal indices included.

**Argued, not formalized.**
- *Mechanism.* Orthogonality would need a cancellation among at most four entries of $\Omega^{-1}$. After
  scaling, it becomes an algebraic relation for $q$ over $\mathbb Z[i]$ with small coefficients. The
  denominator $B$ of $q=A/B$ has norm $2d^2-2d+1$, so for $d\ge4$ no such relation holds. The decay is
  the elementary fact that every eigenvalue of $\Omega$ is at least of order $d$, which the paper's
  eigenvalue formula also shows.
- *Sharper decay.* The paper's eigenvalues give $\lambda_{\min}(\Omega)=d-\frac12(1+\cot\frac{3\pi}{4d})$ (the
  value in the paper's bound on outcome probabilities), which is asymptotic to $(1-\frac{2}{3\pi})d$, so the constant $256$ is far
  from optimal. Numerically $d^2\max G$ equals $1.31$, $1.23$, $1.18$, $1.14$ and $1.12$ for $d=2,\dots,6$;
  whether $d^2\max G$ has a positive limit is not determined here.
- *Other phases.* The obstruction uses that $q$ is a ratio of two coprime Gaussian integers of large
  norm. Replacing the phase $i$ by another root of unity changes the ring of coefficients; whether the
  non-orthogonality survives is not addressed.

**Open.** The exact asymptotics of the smallest Gram entry are not determined here: numerically
$\min G\approx$ $4.1\times10^{-2}$, $3.8\times10^{-3}$, $7.8\times10^{-4}$, $2.4\times10^{-4}$ and
$9.6\times10^{-5}$ for $d=2,\dots,6$. These finite values do not determine the asymptotic rate.

**Effect on the paper.** Both clauses of the conjecture hold. Together with the frozen half-integrality
result, both orthocross conjectures of the paper are settled.

## ASSUMED-UNVERIFIED

The published journal text was not read. The bounded literature check does not establish exhaustive
worldwide novelty, priority, or the absence of an independent proof.
