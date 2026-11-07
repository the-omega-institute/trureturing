---
slug: camilo-landi-eliens-2019-bosonic-gaussian-renyi-strong-subadditivity
bibkey: camilolandieliens2019renyissa
doi: 10.1103/PhysRevB.99.045155
url: https://arxiv.org/abs/1810.07070v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Thermal/GaussianRenyiStrongSubadditivity.result
---

# Strong subadditivity of bosonic Gaussian Rényi entropy for $0<\alpha\le2$, $\alpha\ne1$

## Problem

G. Camilo, G. T. Landi and S. Eliëns, *On the Strong Subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states*, arXiv:1810.07070v2 (Phys. Rev. B 99, 045155, 2019), Section IV.A, `RenyiGaussian_v2.tex`, line 463:

> It provides clear evidence that SSA is violated for all $\alpha>2$, while no violation is found for $0\le\alpha\le2$. We conjecture that this result holds true in general.

Section V, line 532, requests:

> An obvious continuation of this work is to prove the conjectured domains of validity of the SSA for the R\'enyi-$\alpha$ entropies.

For $n$ modes, put $\Omega=\bigoplus_{j=1}^n\begin{pmatrix}0&1\\-1&0\end{pmatrix}$. The covariance formulation takes a real symmetric $2n\times2n$ matrix $V$ with $V+i\Omega\succeq0$. For a mode set $X$, retain both quadratures to obtain $V_X$ and $\Omega_X$. The module defines

$$s_\alpha(\nu)=\frac{\log\left[((\nu+1)/2)^\alpha-((\nu-1)/2)^\alpha\right]}{\alpha-1},\qquad
S_\alpha(V_X)=\frac12\sum_{\lambda\in\operatorname{spec}(V_X^{1/2}(i\Omega_X)V_X^{1/2})}s_\alpha(|\lambda|),$$

with eigenvalues counted with multiplicity. This is the covariance entropy formula of Eq. `renyi_bosonic_1` (TeX lines 216–220), using both signs of the symplectic spectrum. The empty sum is zero.

Issue [#26322](https://github.com/the-omega-institute/trureturing/issues/26322) fixes the statement: for every $n$, every such physical $V$, every pairwise disjoint mode sets $A,B,C$, and every $0<\alpha\le2$ with $\alpha\ne1$,

$$S_\alpha(V_{A\cup B})+S_\alpha(V_{B\cup C})\ge S_\alpha(V_{A\cup B\cup C})+S_\alpha(V_B).$$

This statement is proved. The settlement excludes order zero, order one, the existence of violations at every order above two, fermions and non-Gaussian states.

## Motivation

The source studies when Rényi entropy combinations can quantify correlations. Its Eq. `RCMI` (TeX lines 122–125) defines the Rényi conditional mutual information as the left side of the displayed inequality minus the right side. Nonnegativity for all finite bosonic Gaussian covariances gives the proposed validity range a mathematical basis beyond a search over three- and four-mode examples.

The source identifies order two as a determinant case and treats the remaining orders through symplectic eigenvalues. The issue is whether a uniform relation among four reduced covariances exists, rather than whether individual entropy functions are concave. See [the literature note](../Library/Entropy/camilolandieliens2019renyissa.md).

## Gap

The bounded literature check in #26322 records:

- the explicit conjecture in arXiv v2;
- the search contributor's reading of 14 of 20 INSPIRE citing records with arXiv versions, with no proof of the interval found;
- the orchestrator's web searches, including the known order-two result of Adesso, Girolami and Serafini (2012), arXiv:1203.5116, and an abstract reading of Liu, Ge and Cheng (Results in Physics, 2024) describing the interval between one and two as conjectural;
- no existing repository entry for this conjecture in the preregistration's searches.

`not-found-in-searched-scope`. The conjecture quotation is independently checked against the source TeX; the citing-work and 2024 abstract readings remain attributed to #26322.

## Route

Write $\operatorname{Phys}(V,\omega)$ for `physicalOn`: $V$ is real symmetric and $V+i\omega$ is positive semidefinite. All generic finite matrix index types below have decidable equality.

1. **Physical reductions.** For every $n$ and real covariance $V$, `physicalCovariance_iff` identifies `physicalCovariance V` with $\operatorname{Phys}(V,\Omega)$. Under this physicality hypothesis, `physical_posDef` gives positive definiteness of the complex embedding of $V$, and `reduced_physical` gives $\operatorname{Phys}(V_X,\Omega_X)$ for every mode set $X$. The same reductions are positive definite by principal restriction; `reduced_square` gives $\Omega_X^2=-I$ for every $X$, including the empty set. For arbitrary finite real $V,\omega$ satisfying $\operatorname{Phys}(V,\omega)$ and positive definiteness of $V$, `symplecticOperator_hermitian` makes $M=V^{1/2}(i\omega)V^{1/2}$ Hermitian. Under these same hypotheses, `shifted_posDef` makes $H_x=V+ix\omega$ positive definite for $0\le x<1$.
2. **Spectral bridge.** On a finite index set, assume $\operatorname{Phys}(V,\omega)$, positive definiteness of the complex embedding of $V$, $\omega^2=-I$, and Hermiticity of $M$. Then `symplectic_spectrum_lower_bound` gives $|\lambda_i|\ge1$ for every eigenvalue of $M$, and `determinant_spectral_identity`, for $0\le x<1$, gives

   $$\log\det H_x=\frac12\sum_i\log(\lambda_i^2-x^2).$$

   Here and below the determinant is positive real, so its logarithm agrees with the module's logarithm of its real part. `principal_block_identity` commutes interpolation with principal restriction for arbitrary real $V,\omega$, any finite index subset and every real $x$. For mode matrices, `mode_interpolation_det` identifies the determinants whenever the quadrature index set $Y$ satisfies $p\in Y\iff p.1\in X$ for every $p$; it imposes no condition on $x$.
3. **Positive mixture.** For $0<\alpha<2$, $\alpha\ne1$, and $\nu\ge1$, `BosonicRenyiStieltjes.stieltjes_representation` proves integrability and

   $$s_\alpha(\nu)=c_\alpha+\int_0^1w_\alpha(x)\log(\nu^2-x^2)\,dx,$$

   where $c_\alpha=\log\alpha/(\alpha-1)-\log2$ and $w_\alpha$ is `renyiWeight`. Under the same order hypotheses, `BosonicRenyiStieltjes.weight_pos` gives $w_\alpha(x)>0$ for $0\le x<1$. For finite real $V,\omega$ with $\operatorname{Phys}(V,\omega)$, positive definiteness of $V$, $\omega^2=-I$ and Hermiticity of $M$, `entropy_mixture` proves integrability of the weighted log determinant and

   $$S_\alpha(V,\omega)=\frac{|\iota|}{2}c_\alpha+\int_0^1w_\alpha(x)\log\det(V+ix\omega)\,dx.$$

   The spectral endpoint $\nu=1$ is included; no strict mixedness assumption is needed.
4. **Determinant inequality.** For a complex positive definite matrix on a finite sum of two finite index types, `schur_factor` proves that its Schur complement is positive definite and factors its determinant; `fischer`, with the same hypothesis, bounds its determinant by the product of the two diagonal-block determinants. For a complex positive definite matrix $H$ and pairwise disjoint finite index sets $A,B,C$, `log_koteljanskii` gives

   $$\log\det H_{A\cup B\cup C}+\log\det H_B\le\log\det H_{A\cup B}+\log\det H_{B\cup C}.$$

   Empty blocks are allowed. Apply this to $H_x$ and the full quadrature sets of the three mode sets.
5. **Integration and endpoint.** Under all the hypotheses of `claim`, `settlement_main` integrates this inequality for $0<\alpha<2$, $\alpha\ne1$, using the integrability in `entropy_mixture` and positivity in `weight_pos`. Pairwise disjointness gives $|A\cup B|+|B\cup C|=|A\cup B\cup C|+|B|$, cancelling the constant terms. For finite real $V,\omega$ with $\operatorname{Phys}(V,\omega)$, positive definiteness of $V$ and $\omega^2=-I$, `alpha_two_entropy` gives $S_2(V,\omega)=\tfrac12\log\det V$. At $\alpha=2$, the same determinant inequality at $x=0$ completes `result : claim`.

## Falsifier

A mismatch between the covariance model and the source, an additional strict mixedness hypothesis, or failure to justify integrability would prevent this proof from settling the registered statement.

- The source uses $\Gamma-i\Omega\succeq0$ in Eq. `bona_fide_boson` (TeX lines 194–198), whereas the module uses $V+i\Omega\succeq0$. For real matrices, entrywise conjugation interchanges these Hermitian matrices and preserves positive semidefiniteness: conjugating the test vector conjugates the corresponding nonnegative real quadratic form. The sign conventions therefore give the same physicality condition.
- `reducedCovariance` retains both quadratures of each selected mode. It restricts $\Omega$ as well as $V$; it does not select arbitrary single quadratures as subsystems.
- `gaussianRenyiEntropy` is half the sum of `renyiFunction` over the absolute eigenvalues of `symplecticOperator` when that operator is Hermitian, and zero otherwise. Physical covariances and their reductions satisfy the Hermitian branch by `symplecticOperator_hermitian` under the physicality and positive-definiteness hypotheses stated in Route.
- `claim` has no lower bound on $n$, no nonemptiness condition on the three mode sets, no requirement that their union exhaust all modes, and no exclusion of pure symplectic eigenvalues. The covariance formula is formalized; a Gaussian density operator and its operator Rényi entropy are not.

## Evidence

The canonical source is `D5/S3/Quantum/Thermal/GaussianRenyiStrongSubadditivity.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** `#print axioms` gives only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Thermal/GaussianRenyiStrongSubadditivity.lean.json`.

Declaration statements:

- `result`: `sha256:e38f4e14b22d6e48df50c559cd154161c69a9a1da62722ee2d959e96760db105`;
- `claim`: `sha256:9658864fac511857a327a795b8e364fc83c5c712fbce78b114de401fe58c9398`.

## Triage

Tier 1 conjecture of a 2018 preprint with a 2019 journal publication, preregistered in issue #26322 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural number $n$, every physical real covariance $V$ on $n$ modes, every pairwise disjoint mode sets $A,B,C$, and every real $\alpha$ with $0<\alpha\le2$ and $\alpha\ne1$, the covariance entropies defined by `gaussianRenyiEntropy` satisfy $S_\alpha(V_{A\cup B})+S_\alpha(V_{B\cup C})\ge S_\alpha(V_{A\cup B\cup C})+S_\alpha(V_B)$.

**Computed, not formalized:** None.

**Argued, not formalized.**

- *Decisive mechanism and extension.* Positive mixtures preserve the four-term inequality: if $F(X)=a|X|+\int f_x(X)\,d\mu(x)$ for a common positive measure, all four integrands are integrable, and $f_x(A\cup B)+f_x(B\cup C)-f_x(A\cup B\cup C)-f_x(B)\ge0$ almost everywhere, then the same difference for $F$ is the integral of this nonnegative difference, because the cardinality terms cancel for pairwise disjoint $A,B,C$. Thus any other entropy functional admitting such a representation inherits the inequality. Existence of a representation for another entropy is a separate obligation.
- *Boundary of this route.* The explicit `renyiWeight` is negative for $2<\alpha<3$ and $0<x<1$: its numerator has sign $-\sin(\pi\alpha)<0$, and its denominator is positive. Indeed, writing $a=(1+x)^\alpha>b=(1-x)^\alpha>0$, the denominator apart from the positive factor $\pi(\alpha-1)$ is $(a-b)^2+2ab(1-\cos(\pi\alpha))>0$. Multiplication by this weight cannot preserve the pointwise determinant inequality. This observation neither supplies a representation outside the proved interval nor proves an SSA violation there. Sharpness of the upper endpoint, in the sense of a certified counterexample at every $\alpha>2$, is not settled by `result`.
- *Excluded limits.* If the four entropy terms have finite limits as $\alpha\to1$, their four-term difference has a nonnegative limit by the proved inequality and closedness of the nonnegative real half-line. Identifying those limits with operator von Neumann entropy is not formalized here. At order zero, a limiting conditional combination needs its own definition and convergence argument; the source discusses divergent individual entropies and cancellation in Section II.A (TeX lines 239–243). No order-zero conclusion is claimed.
- *Effect on the source.* For the covariance formula and the proved orders, the bosonic nonnegative-RCMI regime in Section IV.A and its summary in Section V have a proof, answering that part of the request at line 532. The source's order-two result remains the endpoint case. Its separate subadditivity results and min-entropy discussion receive no additional proof here; the violation claim for every order above two and the fermionic conjecture remain outside this settlement. An extension to non-Gaussian correlation measures requires an additional connection to their operator entropies, which is not supplied here.

## ASSUMED-UNVERIFIED

The literature check is bounded to the searches and readings attributed in #26322; it establishes neither exhaustive worldwide novelty nor priority. The 14 citing-work readings, the 2024 abstract reading and the prior-art readings reported there are not independently reproduced. The orchestrator's scalar quadrature and random-covariance computations reported in that issue are not reproduced here.

The statements under "Argued, not formalized" are not Lean conclusions. The correspondence between the covariance entropy formula and an operator Gaussian-state Rényi entropy, including the paired-spectrum interpretation, is not formalized as a density-operator bridge. Order-zero and order-one limits, violations at all orders above two, equality cases, and extensions to fermionic or non-Gaussian states are not settled by `result`.
