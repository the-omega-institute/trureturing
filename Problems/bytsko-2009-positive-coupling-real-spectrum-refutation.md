---
slug: bytsko-2009-positive-coupling-real-spectrum-refutation
bibkey: bytsko2011nonhermitian
doi: 10.1090/S1061-0022-2011-01148-3
url: https://arxiv.org/abs/0911.4476v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.result
---

# Positive couplings do not force a real spectrum for U_q(sl_2)-invariant spin chains

## Problem

A. G. Bytsko, *Non-Hermitian spin chains with inhomogeneous coupling*, arXiv:0911.4476v3 (St. Petersburg Math. J. 22, 393–410, 2011), Conjecture 3:

> For $|\gamma| < \frac{\pi}{2S}$, the Hamiltonian (22) of a spin chain with inhomogeneous coupling has a real spectrum if all $a_n >0$.

Here:
- **The chain:** $N$ sites, each carrying the spin-$S$ representation of $U_q(sl_2)$ with $q=e^{i\gamma}$, in the source's normalization.
- **The Hamiltonian (22):** $H=\sum_{n=1}^{N-1}a_nP^{S,s}_{n,n+1}$, where $P^{S,s}$ is the non-orthogonal projector onto the spin-$s$ summand of $V^S\otimes V^S$, given by the source's Casimir polynomial.

The definitions are quoted in [the literature note](../Library/QuantumContext/bytsko2011nonhermitian.md).

Issue [#20040](https://github.com/the-omega-institute/trureturing/issues/20040) fixes the reading: for every $S$, $s\in\{0,\dots,2S\}$, $N\ge2$, $0<|\gamma|<\pi/(2S)$ away from projector poles, and positive couplings, every eigenvalue of $H$ is real. This is refuted.

## Motivation

For $|q|=1$ the $U_q(sl_2)$-invariant chains are non-Hermitian but pseudo-Hermitian, and a real spectrum is the condition under which they define a unitary quantum theory with a modified inner product. The source constructs universal metric operators for these chains and determines the ranges of $\gamma$ with real spectra for short chains; Conjecture 3 would guarantee physical reality of the spectrum throughout the standard range whenever the couplings are positive.

## Gap

The literature check before any Lean is recorded in #20040:
- the five works citing the paper on INSPIRE cite it only for non-Hermitian chains, quasi-Hermiticity or projector examples;
- the author's later papers do not revisit the spectrum of (22);
- the source's own $N=4$ evidence covers only $s=0$ (the subsection "$N=4$ and $N=5$ for $s=0$");
- the repository had no record.

`not-found-in-searched-scope`.

## Route

Take $S=s=1$, $N=4$, $\gamma=\arccos(4/5)$ (so $q=(4+3i)/5$ and $2\gamma<\pi$), and $a=(1,1,1)$.
1. **The projector.** $14P^{1,1}$ is an explicit Gaussian-integer $9\times9$ matrix.
2. **An invariant plane.** An explicit $81\times2$ matrix $W$, supported on nine of the ten configurations of total weight $+2$, satisfies $(P_{12}+P_{34})W=WA$ and $P_{23}W=WB$ with $A=\begin{pmatrix}-11/14&1\\-275/196&25/14\end{pmatrix}$ and $B=\begin{pmatrix}1&0\\0&0\end{pmatrix}$.
3. **A non-real eigenvalue.** $A+B$ has characteristic polynomial $\lambda^2-2\lambda+25/14$, with roots $1\pm i\sqrt{11/14}$. For an eigenvector $y$ of $A+B$, $Wy$ is a nonzero eigenvector of $H$ with a non-real eigenvalue.

## Falsifier

The counterexample would not answer the conjecture if the module's chain differed from the source's. The module:
- defines $E,F,K$ and the projectors $P^{S,s}$ by the source's formulas, and the tensor Casimir as $(\pi_S\otimes\pi_S)\Delta(C)$ from Eqs. (C) and (DelEFK), the definitional left side of Eq. (dC2); the expanded right side of (dC2) does not commute with $\Delta(E)$ and is read as a misprint ([#20040](https://github.com/the-omega-institute/trureturing/issues/20040));
- defines $H$ by the source's equation (22);
- places the witness inside the conjecture's hypotheses: $2S|\gamma|<\pi$, $\gamma\ne0$, nonzero projector denominators and positive couplings.

## Evidence

The canonical source is `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.lean` (425 lines).
- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.lean.json`, statement `sha256:c24d3f502c28788ed74f556becefd1e53c201e8c406d76d980355f524ef56f73`.

Declaration statements:
- `result`: `sha256:3b91017ebba5ac1c974f029ba65608f932e05ad87426abfaa6909087aef0aba3`;
- `claim`: `sha256:d4e384aff69fa671d8b0d7a7d57950de08e2a1bd63e1f15a54e0c5eed4331dc8`.

## Triage

Tier 1 conjecture of a 2009 preprint kept in the journal versions, preregistered in issue #20040 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. `utility: kind=certified-instance; basis=refutes`. There is no digestion atom.

### What the settlement shows

**Proved in the module:** the homogeneous spin-1 chain of four sites with the spin-1 projector at $q=(4+3i)/5$ has the non-real eigenvalue $1+i\sqrt{11/14}$, inside the range $|\gamma|<\pi/2$.

**Computed, not formalized** (orchestrator, numpy, recorded in #20040):
- *A cone of couplings.* On the invariant plane, $H(a,b)=a(P_{12}+P_{34})+bP_{23}$ has characteristic polynomial $\lambda^2-(a+b)\lambda+\tfrac{25}{14}ab$, so the spectrum is non-real whenever $(18-5\sqrt{11})/7<b/a<(18+5\sqrt{11})/7$; for $a=(1,2,1)$ the eigenvalue $(21+i\sqrt{259})/14$ appears.
- *Other projectors.* The spin-2 projector at the same $\gamma$ also gives a non-real spectrum; the spin-0 projector gives real spectra, consistent with the source's $s=0$ analysis.
- *Dependence on $\gamma$.* For $s=1$ and $a=(1,1,1)$, non-real eigenvalues occur for $\gamma$ between about $0.58$ and $1.12$, and the spectrum is real near $0$ and near $\pi/2$.

**Argued, not formalized.**
- *Mechanism.* On the invariant plane, $P_{12}+P_{34}$ and $P_{23}$ are two oblique rank-one idempotents with negative overlap $\mathrm{tr}(AB)=-11/14$. For two rank-one idempotents, $\det(\lambda-aA-bB)=\lambda^2-(a+b)\lambda+ab(1-\mathrm{tr}AB)$, whose discriminant $(a-b)^2+4ab\,\mathrm{tr}AB$ is nonnegative for all positive $a,b$ exactly when $\mathrm{tr}AB\ge0$. The non-orthogonality of the $q$-projectors makes the overlap negative and opens a complex pair for a range of coupling ratios.
- *Scope.* The conjecture fails for $s=1$ and $s=2$ at $S=1$. Whether it holds for $s=0$, the case the source analyzed for $N=4,5$, is not settled here.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized; the eigenvalue range in $\gamma$ is a numerical scan.
