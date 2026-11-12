---
bibkey: deffnercampbell2017speedlimits
authors: Sebastian Deffner and Steve Campbell
year: 2017
title: "Quantum speed limits: from Heisenberg's uncertainty principle to optimal quantum control"
doi: null
url: https://arxiv.org/html/1705.08023v2
claim: The pure-state overlap angle is bounded by the integral of energy fluctuation divided by hbar; an autonomous Hamiltonian gives the Mandelstam–Tamm displacement bound.
strata_touched:
  - D5/S3/QuantumBounds/HamiltonianDisplacement
license: citation-only
triage: anchor
---

# Hamiltonian displacement

## Verified locator

https://arxiv.org/html/1705.08023v2

The version identifies itself as arXiv:1705.08023v2 and names Sebastian
Deffner and Steve Campbell as its authors. Section 2.5, equation (23),
defines the pure-state angle as arccos of the absolute overlap.
Equations (29)–(31) bound its rate and accumulated displacement by the
energy fluctuation divided by hbar. Equations (32)–(33) express the same
bound through the time average of that fluctuation. These equations and
the surrounding mathematical text were retrieved and read directly.

## Formal model and scope

For a self-adjoint continuous complex linear endomorphism A of a
finite-dimensional complex inner product space and a unit vector psi,
put mu = Re inner(psi,A psi) and Delta = norm(A psi-mu psi). For hbar > 0,
the autonomous evolution is exp((-i t/hbar) A)psi. The formal statement
bounds its overlap angle from psi by abs(t) Delta/hbar for every real t.
Delta is the centered energy fluctuation in that same vector, not an
independent calibration or an assumed mean-energy resource.

The proof centers the generator, differentiates its actual unitary
exponential orbit, projects the initial vector onto a real tangent
plane, and integrates a regularized arccos inequality before taking the
regularization parameter to one. A scalar phase then identifies the
centered orbit's overlap modulus with the original evolution. The
argument includes zero fluctuation and all overlap endpoints.

The inequality is classical. The source supplies the literature
attribution; mathematical verification of the formal declaration is
separate. The statement concerns bounded autonomous Hamiltonians in
finite dimension. It does not model open-system evolution, arbitrary
measurement feedback, unbounded-operator domains, or a universal minimum
duration for software instructions or physical records. Only citation
and mathematical exposition are included; no source article text is
redistributed.
