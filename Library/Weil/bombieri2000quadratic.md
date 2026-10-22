---
bibkey: bombieri2000quadratic
authors: Enrico Bombieri
year: 2000
title: Remarks on Weil's quadratic functional in the theory of prime numbers, I
doi: null
url: https://www.bdim.eu/item?id=RLIN_2000_9_11_3_183_0
claim: Finite spectral approximations have one negative eigenvalue per distinct nonreal conjugate pair. Passage to the complete form retains a zero-limit and linear-dependence alternative; finite inertia is not an all-support positivity certificate.
strata_touched: []
license: citation-only
triage: anchor
---

# Finite inertia and the complete-form sign obligation

## Primary source and normalization

Bombieri, *Remarks on Weil's quadratic functional in the theory of prime
numbers, I*, Rendiconti Lincei, Matematica e Applicazioni, series 9,
**11** (2000), no. 3, 183–233. The [BDIM record](https://www.bdim.eu/item?id=RLIN_2000_9_11_3_183_0)
links the [original PDF](https://www.bdim.eu/item?fmt=pdf&id=RLIN_2000_9_11_3_183_0).
The statements and surrounding arguments cited below were inspected in that
scan. This is a source comparison, not an independent audit of its full
proof, a new inertia theorem, or Lean certification.

The source writes $\rho=1/2+i\gamma$. Thus its nonreal $\gamma$ means an
off-critical zero; its $\gamma$ is not merely the real ordinate of $\rho$.
Section 8, printed p.208, starts with a **finite multiset** $\Gamma$ invariant
under complex conjugation and multiplication by $-1$, with positive integral
multiplicities preserved. The source's matrices and norms are retained;
no identity with the project's complete physical operator is assumed.

## Reuse the finite results with their finite quantifier

Theorem 8, printed p.213, gives one negative eigenvalue of
$\mathcal H(\Gamma;t)$ per **distinct nonreal conjugate pair** in $\Gamma$.
Theorem 9, printed p.217, gives the corresponding count for
$\mathcal K_E(\Gamma)$, where $E$ is a finite union of bounded closed
intervals, and separate even and odd counts when $E=-E$.

The paragraph preceding Theorem 8, printed p.213, and Lemma 12, printed
p.216, keep multiplicity separate from this count. Repeating the same spectral node
adds null copy directions; the nonzero spectrum is obtained from the
matrix on distinct nodes with their positive multiplicity weights.
A zero's analytic multiplicity therefore does not create independently
interpolable copies of the same scalar evaluation.

These are finite spectral approximation theorems. They do not state that
an arbitrary cutoff has the same negative index as the complete Weil
form on its test-function domain.

## The infinite passage keeps the vanishing-synthesis alternative

Sections 10–11 retain the standing hypotheses on the infinite multiset:
$\Gamma=\overline\Gamma=-\Gamma$, with symmetry-preserved positive integral
multiplicities, and
$$
 \sum_{\gamma\in\Gamma}(1+|\gamma|)^{-1-\varepsilon}<\infty
 \quad\text{for every }\varepsilon>0,
$$
counting multiplicity. They additionally assume finitely many, but at
least one, off-critical zeros. Theorem 10, printed p.221, concerns the
first eigenvalue problem and states the alternative
$T[f*f^*]=\lambda\|Df\|^2<0$ or $f\equiv0$. It also states that $f\equiv0$
for every sufficiently small positive $t$, below an explicitly computable
$t_0$. This is distinct from Theorem 11, printed pp.223–224, for the
$L^2$ eigenvalue problem on a finite union of intervals.

In Theorem 11 the limiting coefficients have unit $\ell^2$ norm and at
least half their $\ell^2$ mass on the off-critical set. Their synthesis
$F(u)=\sum_\gamma z_\gamma e^{-i\gamma u}$ is locally in $L^2$.
The theorem retains two alternatives: a nonzero synthesized test with
strictly negative complete Weil energy, or $\lambda=0$ with that test
identically zero. Nonzero coefficient mass does not exclude a zero
synthesis on the chosen observation window.

The corollary on p.224 consequently says that positivity for every smooth
compact test in a fixed multiplicative interval union implies **one of**:
RH; infinitely many off-critical zeros; or an $\ell^2$ linear dependence
of the $x^{-\rho}$ there with at least half the coefficient mass on the
off-critical set. It does not eliminate the third alternative or prove
that finitely many off-critical zeros would imply none.

## Application to the project's index estimate

The project's [full mixed Gram](../../D5/S3/Weil/BurnolGram/WeilFullGramInertia.lean)
and [common-support negative family](../../D5/S3/Weil/BurnolGram/WeilBurnolFixedScaleTransport.lean)
already handle actual compact even tests for a specified finite separated
off-line orbit frame, including the complete summable zero tail. These
interfaces should be reused. Their frame-dependent finite realization
supplies no lower growth rate for the number of negative directions as
the support grows.

There is also a direct finite-rank upper implication of the complete
spectral pairing, separate from passing a finite matrix to its limit.
**If** the actual zero set had only $k<\infty$ distinct nonreal conjugate
pairs, let $f$ be the compact-test root variable in $T[f*f^*]$ and put
$u_j=\widehat f(\gamma_j)$, $v_j=\widehat f(\overline\gamma_j)$. The $j$th
paired term is $2m_j\operatorname{Re}(u_j\overline{v_j})$, with equal
positive multiplicities $m_j>0$ at the two conjugate nodes. Imposing the
$k$ complex-linear conditions $u_j=v_j$ makes these terms
$2m_j|u_j|^2\ge0$ and leaves the whole critical-line sum with its positive
weights. The antisymmetric pair-evaluation map is consequently injective
on every strictly negative complex subspace of compact-test roots, so
its **complex dimension** is at most $k$. This does not posit an actual
exceptional zero configuration. Transport to a completed physical
operator requires form-core identification and continuity of these
evaluations in its form-domain topology.

Under that domain identification, this conditional bounded index is
consistent with the [complete-form Fourier estimate](frankliebseiringer2006hardy.md#logarithmic-fourier-localization-for-the-complete-negative-index),
whose upper exponential rate is $1/2$, even when $k>0$.
The estimate alone therefore does not exclude this conditional case.
This is a scope check using existing spectral structure, not a claim
that such zeros exist, that they are possible for the actual zeta
function, or that no additional theorem could exclude them.

The remaining RH obligation is a sign certificate excluding the residual
negative directions, with the original source and domain preserved.
Neither the finite inertia count nor this source comparison supplies
that certificate or the same-integer Robin signed estimate.
