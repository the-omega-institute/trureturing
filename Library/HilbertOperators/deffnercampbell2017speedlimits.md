---
bibkey: deffnercampbell2017speedlimits
authors: Sebastian Deffner; Steve Campbell
year: 2017
title: "Quantum speed limits: from Heisenberg's uncertainty principle to optimal quantum control"
doi: 10.1088/1751-8121/aa86c6
url: https://arxiv.org/abs/1705.08023v2
claim: "For unitary pure-state evolution, the overlap angle is bounded by the time integral of the energy standard deviation divided by hbar; a time-independent self-adjoint Hamiltonian has constant centered fluctuation."
strata_touched:
  - D5/S3/QuantumBounds/HamiltonianDisplacement
license: citation-only; source distributed under the arXiv non-exclusive distribution license
triage: anchor
---

# Hamiltonian displacement and energy fluctuation

## Verified locator

DOI: https://doi.org/10.1088/1751-8121/aa86c6

Source: https://arxiv.org/abs/1705.08023v2

The review appears in *Journal of Physics A: Mathematical and Theoretical*
**50**, 453001 (2017). Section 2.5, “Generalisations to arbitrary angles and
driven dynamics,” equation (23), defines the pure-state angle by

$$
\mathcal L(\psi_0,\psi_\tau)
=\arccos\bigl|\langle\psi_0,\psi_\tau\rangle\bigr|.
$$

Equation (28) centers the Hamiltonian at its energy expectation.
Equations (29)–(30) bound the magnitude of the angular speed by
$\Delta H_t/\hbar$. Equation (31) gives the integrated bound

$$
\mathcal L(\rho_0,\rho_\tau)
\le \frac{1}{\hbar}\int_0^\tau \Delta H_s\,ds.
$$

Equations (32)–(33) express this as a duration lower bound using the
time average of
$\sqrt{\langle H_s^2\rangle-\langle H_s\rangle^2}$.
The square root is the energy standard deviation, rather than its square.
Equation (23) identifies the pure-state specialization of the angle in
the integrated bound. The review attributes this result to the classical
Mandelstam–Tamm line of work; it supplies no originality claim for the
repository theorem.

## Exact autonomous finite-dimensional specialization

Let $E$ be any finite-dimensional complex inner product space, with its
normed additive group structure. Let $A:E\to E$ be a continuous complex
linear self-adjoint operator, let $\psi\in E$ satisfy $\|\psi\|=1$, and let
$\hbar\in\mathbb R$ satisfy $\hbar>0$. With the inner product conjugate-linear
in its first argument and linear in its second, put

$$
\mu=\operatorname{Re}\langle\psi,A\psi\rangle,
\qquad
\Delta=\|A\psi-\mu\psi\|,
\qquad
U(t)=\exp\!\left(\frac{-it}{\hbar}A\right).
$$

Here $\mu$ is embedded into $\mathbb C$ when multiplying a vector, and
the exponential is the normed-algebra exponential of the given operator.
Self-adjointness and normalization identify
$\Delta^2=\langle\psi,A^2\psi\rangle-\mu^2$; the right-hand side is real.
For the autonomous evolution this fluctuation is constant. The exact
repository statement is

$$
\forall t\in\mathbb R,\qquad
\operatorname{fsAngle}(\psi,U(t)\psi)
=\arccos\bigl|\langle\psi,U(t)\psi\rangle\bigr|
\le \frac{|t|\Delta}{\hbar}.
$$

The review states its integrated inequality for a nonnegative duration.
The repository theorem retains every real time: negative time corresponds
to reversing the Hamiltonian, with the same centered fluctuation. Its
inequality does not divide by $\Delta$, so $\Delta=0$ and $t=0$ are included.
Overlaps of modulus zero and one are also included; the proof regularizes
the inverse cosine before taking its continuous endpoint limit.

In physical units, $A$, $\mu$, and $\Delta$ have units of energy, $t$ has
units of time, and $\hbar$ has units of energy times time. Both the
exponent and $|t|\Delta/\hbar$ are dimensionless, and the angle uses radians.
There is no factor of two in the angle convention of equation (23).

The selected result controls the orbit of the actual exponential of a
bounded self-adjoint endomorphism. It does not assert an open-system,
unbounded-operator, measurement-protocol, or universal clock-tick bound.
The review's broader mixed-state and driven results are literature context;
they are not claims of this Lean declaration.
