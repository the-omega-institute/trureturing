---
bibkey: jia2026vacuumcorrelations
authors: Hewei Frederic Jia
year: 2026
title: Vacuum correlation measures as CFT partition functions
doi: 10.48550/arXiv.2611.34922
url: https://arxiv.org/abs/2611.34922v1
claim: "Equation (14) identifies integer-order vacuum sandwiched Rényi mutual information with a partition function. The Discussion asks for a direct operator-algebraic proof."
strata_touched:
  - D5/S3/Quantum/Analysis/TraceClass/ModularTransferTensor
  - D5/S3/Quantum/Analysis/TraceClass/ModularTransferReadout
license: citation-only
triage: anchor
---

# Vacuum correlation measures as CFT partition functions

## Verified locator

- [Pinned arXiv record](https://arxiv.org/abs/2611.34922v1) and [DOI](https://doi.org/10.48550/arXiv.2611.34922).
- [Equations (14) and (15)](https://arxiv.org/html/2611.34922v1#S0.E14) identify the replica partition function and its temperature.
- The [Discussion](https://arxiv.org/html/2611.34922v1#p22.1) asks for an operator-algebraic proof.

## Order-two derivation

The v1 Discussion asks for a direct algebraic proof of Eq. (14) for split
Type III₁ algebras. The calculation below treats order two for concentric
conformal diamonds with geometric vacuum modular action, Haag duality for
the outer diamond, and a finite vacuum-normalized partition function at
the specified inverse temperature. The specialization identifies the
positive-energy cylinder generator with the radial dilatation generator
of the CFT in Eq. (15). It also gives a Hilbert–Schmidt
finiteness criterion for standard split pairs. [Eq. (14)](https://arxiv.org/html/2611.34922v1#S0.E14) ·
[Discussion](https://arxiv.org/html/2611.34922v1#p22.1)

Let $M,N$ commute and form a split pair with a common vector
$\Omega$ cyclic and separating for each algebra. Put $P=N'$, let
$\omega$ be the joint vacuum functional and let $\sigma$ be the product
of its two marginal states, transported by the split isomorphism. Set
$X=\overline{\Delta_P^{1/4}\Delta_M^{-1/4}}$ and $T=X^*$. The inclusion
$M\subset P$ has the same cyclic and separating vector, so the product
is densely defined and its closure $X$ is a contraction.
[Buchholz–D’Antoni–Longo, §5.1](https://arxiv.org/html/math-ph/0603083#S5.SS1)

The symmetric embeddings are
$j_M(a)=\Delta_M^{1/4}a\Omega$ and $j_N(b)=\Delta_N^{1/4}b\Omega$.
For $b\in N$, the vector $j_N(b)$ belongs to the domain of
$\Delta_M^{-1/4}\Delta_P^{1/4}$. Indeed,
$\Delta_P^{1/4}j_N(b)=b\Omega$ and $b\Omega$ is in the domain of
$\Delta_M^{-1/2}$ by the commutant Tomita operator. The reversed product
is contained in $X^*$ on this domain. In fact, for $u$ in the domain of
the original product, moving each self-adjoint power across the inner
product shows $\langle X u,j_N(b)\rangle=\langle u,\Delta_M^{-1/4}b\Omega\rangle$.
The equality persists on the closure. Moving the remaining powers in
$\langle j_M(a^*),\Delta_M^{-1/4}b\Omega\rangle$ cancels them by
spectral calculus. The Tomita identity $J_M j_M(a)=j_M(a^*)$ then gives
$\omega(ab)=\langle J_M j_M(a),Tj_N(b)\rangle$ with the inner product
linear in its second variable. Compare the vacuum pairing expansion in
Ceyhan–Faulkner. [Eqs. (2), (5)](https://arxiv.org/html/2510.24042v1#S2)

In the spatial tensor product of the two standard forms, the vector
$\Omega\otimes\Omega$ represents $\sigma$. Its Tomita operator is the
closure of the tensor product of the local Tomita operators on the
algebraic core, so $\Delta_\sigma=\Delta_M\otimes\Delta_N$. Unitary
uniqueness of standard form identifies $j_M(a)\otimes j_N(b)$ with
$j_\sigma(a\otimes b)$. In Haagerup $L^2$ the modular operator acts by
left multiplication by $h_\sigma$ and right multiplication by its
inverse. Applying the quarter power to $x h_\sigma^{1/2}$ gives
$j_\sigma(x)=h_\sigma^{1/4}x h_\sigma^{1/4}$.
[Jenčová, Appendix A.1](https://arxiv.org/html/1609.08462#A1.SS1)

When $T$ is Hilbert–Schmidt, the reflected pairing has a representative
$v$ with $\|v\|^2=\operatorname{Tr}(T^*T)$. By Hölder multiplication and
trace cyclicity, $h_\sigma^{1/4}v^*h_\sigma^{1/4}$ defines a normal
functional whose values on $a\otimes b$ are $\omega(ab)$. The algebraic
tensor product is ultraweakly dense, so this density is $h_\omega$.
The isometry in Jenčová's Theorem 2.3 sends $v^*$ to $h_\omega$ at
$p=2$. Her Eq. (13) then gives
$\exp(\widetilde D_2(\omega\Vert\sigma))=\|v^*\|_2^2=\|v\|^2$. Conversely, membership
of $h_\omega$ in Kosaki $L^2(M\bar\otimes N,\sigma)$ supplies a bounded
functional on the symmetric tensor readouts by the same pairing.
Each local symmetric embedding has dense range. For example, $M\Omega$
is a core for $\Delta_M^{1/2}$, hence for $\Delta_M^{1/4}$, whose range
is dense by faithfulness. Continuity extends the readout bound to arbitrary
finite sums of elementary Hilbert tensors. The Hilbert–Schmidt criterion
therefore gives infinite divergence when $T$ fails to be Hilbert–Schmidt.
[Jenčová, Theorem 2.3](https://arxiv.org/html/1609.08462#S2.Thmthm3) ·
[Eq. (13)](https://arxiv.org/html/1609.08462#S3.E13)

For the concentric conformal geometry, restrict geometric modular
action to the Möbius subgroup preserving the time axis. The nested
diamonds correspond to symmetric time-axis intervals of lengths $2\xi$
and $2$. The interval distance in Buchholz–D’Antoni–Longo is
$s=-\log\xi$. Their Proposition 3.1 and Eq. (3.2) give $XX^*$ unitarily
equivalent to $e^{-2sL_0}$, where $L_0$ generates conformal cylinder
time and has the radial spectrum. Since $T^*T=XX^*$, the trace is the
thermal partition function at Jia's $\beta_2=-2\log\xi$. The identity
$T\Omega=\Omega$ ensures that its trace is at least one. With
$s=-\log\xi$, the geometric cross ratio is
$\eta=4\xi/(1+\xi)^2=\operatorname{sech}^2(s/2)$.
The split hypothesis provides the product reference. Splitness alone
permits noncompact modular transfer, as in the wedge example in
Buchholz–D’Antoni–Longo, §8.1. The geometric modular action
identifies the conformal generator.
[Buchholz–D’Antoni–Longo, §3.1](https://arxiv.org/html/math-ph/0603083#S3.SS1) ·
[Jia, Eq. (15)](https://arxiv.org/html/2611.34922v1#S0.E15)

The Lean results establish the Hilbert-space representation and its
sharp finite-readout criterion. The standard-form calculation and
conformal application above use the cited operator-algebraic results.
The direct identity at higher replica orders remains open. Ceyhan–Faulkner prove von Neumann mutual
information upper bounds from modular nuclearity. A targeted arXiv and
repository search on 2026-11-27 found Jia's formal replica argument and
the cited supplier results. Priority for the direct order-two argument
remains unverified.
[Ceyhan–Faulkner, §§2–5](https://arxiv.org/html/2510.24042v1#S2)
