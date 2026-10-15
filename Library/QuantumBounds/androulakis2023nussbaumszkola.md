---
bibkey: androulakis2023nussbaumszkola
authors: George Androulakis and Tiju Cherian John
year: 2023
title: Quantum f-divergences via Nussbaum-Szkoła Distributions and Applications to f-divergence Inequalities
doi: 10.48550/arXiv.2308.02929
url: https://arxiv.org/html/2308.02929
claim: Theorem 3.8 identifies quantum f-divergences with the classical divergences of the associated Nussbaum-Szkola distributions; full eigenbasis transition weights give the route to Hellinger energy bounds and quantitative entropy concavity.
strata_touched:
  - D5/S3/Quantum/Analysis/TraceClass/HellingerEnergy
  - D5/S3/Quantum/Analysis/TraceClass/EntropyConcavity
license: citation-only
triage: anchor
---

# Spectral transition weights and entropy concavity

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2308.02929

Full text: https://arxiv.org/html/2308.02929

## Correspondence and scope

The linked article's Theorem 3.8 identifies the quantum and classical
f-divergences for the associated Nussbaum-Szkola distributions. Section 4
discusses transfer of classical divergence inequalities. This is an established
correspondence, not an originality claim for the formalization.

For full orthonormal eigenbases u and v of two positive trace-one operators,
put c(i,j)=|inner(v(j),u(i))| squared. Parseval gives both marginal sums equal
to one. The two distributions have weights r(i)c(i,j) and s(j)c(i,j).
The formal proof uses unconditional sums on arbitrary Set indices, including
all zero eigenspaces; it does not enumerate a nonseparable full basis by Nat.
The article supplies the mathematical viewpoint. Its theorem is not imported
as a Lean axiom, nor is a verbatim nonseparable statement attributed to it.

The scalar logarithm bound gives

    -r log r + r + (sqrt r - sqrt s)^2 <= -r log s + s.

At r=0 the identity is interpreted with eta(0)=0. At s=0 and r>0 the
right side is infinite. Nonnegative extended sums preserve these cases and
zero times infinity equals zero. Parseval and actual square-root
Hilbert-Schmidt membership identify the double square-root defect with the
finite Hilbert-Schmidt square of sqrt(rho)-sqrt(sigma).

The identity

    rho-sigma = sqrt(rho)(sqrt(rho)-sqrt(sigma))
              + (sqrt(rho)-sqrt(sigma))sqrt(sigma)

and the Hilbert-Schmidt product trace-norm estimate give the reward
norm(rho-sigma)^2/4. The analytic ideal estimates are reused from the
repository's attributed Physlib suppliers, with their author and license
notices preserved; the functional calculus, Parseval and infinite-sum
infrastructure is reused from pinned Mathlib.

Applying the energy bound to each state relative to its actual convex mixture
and using nonnegative first-slot energy linearity yields, for a,b>=0 and a+b=1,

    S(a rho+b sigma) >= a S(rho)+b S(sigma)+a b norm(rho-sigma)^2/4.

The statement is extended valued, includes both endpoints, and assumes no
commutation, faithfulness or finite entropy. On a convex family where actual
spectral entropy is finite it yields real strong concavity with modulus 1/2
in Mathlib's convention, and midpoint reward norm(rho-sigma)^2/16.
These are established entropy inequalities. They do not resolve the Shirokov
entropy-continuity conjectures, prove relative compactness of a state family,
or construct a common full-space Hamiltonian.
