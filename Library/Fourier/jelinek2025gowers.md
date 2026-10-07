---
bibkey: jelinek2025gowers
authors: Pascal Jelinek
year: 2025
title: Gowers norms for linearly recurrent numeration systems
doi: 10.48550/arXiv.2510.16947
url: https://arxiv.org/abs/2510.16947v1
claim: "Remark 1.5 supplies a Rauzy-fractal/torus direction for digital observations. The general decay statement in Theorem 1.4 has unresolved resonance and truncation discrepancies in v1; it is not admitted here as a weighted FIB or Robin estimate."
strata_touched: []
license: citation-only
triage: anchor
---

# Recursive digital geometry and the missing arithmetic transport

The inspected source is [arXiv:2510.16947v1](https://arxiv.org/pdf/2510.16947v1),
submitted 2025-10-19. Its [author TeX](https://arxiv.org/src/2510.16947v1)
was also inspected. The arXiv abstract and API identify v1 as the latest
version in the retrieval on 2026-10-05 UTC. This is a version check of this
paper, not a claim to have surveyed every recent result. The source check
covers Definition 1.2, Theorem 1.4, Remark 1.5, Lemmas 2.1–2.2,
Proposition 3.1 and the final displayed estimate in the proof of Theorem 1.4;
the complete proof has not been independently certified or Lean-verified.

## What the geometric direction preserves

Definition 1.2 requires the finiteness property, Property F, of the
associated beta-expansion. Being Pisot alone does not discharge this
condition. Lemmas 2.1–2.2 use this property to separate digit blocks by
sufficient zero buffers before addition. The buffers depend on the
addition problem; the two-state rule forbidding adjacent Zeckendorf ones
is not by itself a uniform carry bound for every arithmetic operation.

Remark 1.5 explicitly distinguishes the displayed digital cube average
from a genuine Gowers norm in most noninteger-base systems. It outlines
an observation on a Rauzy fractal, passage to a torus using a tiling, and
integration against a suitable measure. The remark does not specify a
ready-to-use weighted norm inequality for the project's arithmetic input.
An interval image of legal addresses does not, by itself, supply that
tiling, group operation, measure, or transport of arithmetic weights.

For the project's five-mode address, the digit-count observable is

$$
\nu(null)=0,\qquad \nu(2)=\nu(3)=\nu(5)=1,
\qquad \nu(2\,5)=2.
$$

Use $G_i=F_{i+2}$, so $G_0=1$, and retain the unit digit separately.
The first $L$ windows occupy positions $1,\ldots,3L$. With the inclusive
cutoff in the paper's equation (1.1), their truncated digit count at
$\lambda=3L$ is the unit digit plus the sum of these window counts.
This parameter identification concerns a digit phase. The paper's
dominant root, also called $\beta$, is distinct from the Binet error
coefficients $\beta_d$ in FIB §384.

## The displayed general phase estimate cannot be imported unchanged

Theorem 1.4, equation (1.3), prints decay with $\|\theta\|^2$ in the
exponent. Proposition 3.1 and the last displayed line of the proof instead
contain $\|h\theta\|^2$. The source prints $h=a_0-1+a_1+\cdots+a_d$
although Definition 1.1 names the recurrence coefficients
$a_1,\ldots,a_d$. These are discrepancies in the original TeX, not only
in PDF extraction. No corrected general theorem is asserted here.

The classical integer-base resonance is a necessary source check.
In base three, $s_3(n)\equiv n\pmod2$. Take $s=2$, $\theta=1/2$,
$G_\lambda=3^\lambda$, and the paper's inclusive truncation
$s_{3,\lambda}(n)=\sum_{i=0}^{\lambda}\delta_i(n)$. Every cube vertex
for $0\le n_0,n_1,n_2<3^\lambda$ is below $3^{\lambda+1}$, so this
truncation retains all its digits. Consequently the four phases multiply
to one:

$$
\frac1{3^{3\lambda}}\sum_{n_0,n_1,n_2<3^\lambda}
(-1)^{s_{3,\lambda}(n_0)-s_{3,\lambda}(n_0+n_1)
-s_{3,\lambda}(n_0+n_2)+s_{3,\lambda}(n_0+n_1+n_2)}=1.
$$

This tests equation (1.3) with its cube dimension read as $s$; the
display also uses a different letter $k$ in the product index. Thus the
literal nonresonant-looking factor $\|\theta\|^2=1/4$ cannot give the
printed decay in this specialization. Direct integer evaluations at
$\lambda=1,2,3$ give respectively $27/27$, $729/729$ and
$19683/19683$. The all-scale observation is the classical congruence
above, not an inference from these finite checks. It is not claimed as
new mathematics, a Lean result, or a counterexample to RH.

For comparison, Nathan Toumi's
[arXiv:2504.02784v1](https://arxiv.org/abs/2504.02784v1),
*The level of distribution of the sum-of-digits function in arithmetic
progressions*, retains the condition $\gcd(b,q-1)=1$ for the phase
$e(\ell s_q(n)/b)$ with $0<\ell<b$ (Introduction, equation labelled
`hypob` and the Gowers estimate labelled `NDGG` in the
[author TeX](https://arxiv.org/src/2504.02784v1)). The latter estimate
has fixed order $k\ge3$. This condition excludes the base-three
digit-parity resonance. Its truncation is explicitly reduction modulo
$q^\rho$, rather than the inclusive cutoff printed in Jelinek's (1.1).
Toumi's result is a comparison of source conditions, not a substitute
theorem for Fibonacci numeration or the actual FIB input.

## Reuse and the remaining same-source obligation

The Zeckendorf digit-parity Möbius orthogonality result is already
recorded in [FIB §148.2](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md).
The prime digit-sum distribution and its modulus restriction are already
recorded in the [Drmota–Müllner–Spiegelhofer note](drmotamullnerspiegelhofer2025primes.md).
Those results are reused; no new proof, replacement scan or claim of
priority is supplied here.

The actual input in FIB §384 is the cumulative convolution
$e=\mu*\beta$, with
$H_N=\sum_{d\le N}\beta_d\mathfrak M(\lfloor N/d\rfloor)$.
A digital phase estimates a different observable. Transport must keep
these weights and divisor arguments on the same arithmetic source and
must retain the constant mode. Taking an integral phase supplies no
digital oscillation; small nonconstant digital correlations do not
settle that missing mode. The claimed norm must also belong to the
specified group and measure before any Gowers duality is used.

The Rauzy/carry framework is therefore a geometric lead. A repaired,
applicable phase statement, its precise group model, and a bound for the
required same-source weighted divisor response remain separate
obligations. No actual-$H$ square-root growth, signed Robin remainder,
or RH proof follows from this source audit.
