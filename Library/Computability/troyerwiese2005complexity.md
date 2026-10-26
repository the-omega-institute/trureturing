---
bibkey: troyerwiese2005complexity
authors: Matthias Troyer; Uwe-Jens Wiese
year: 2005
title: Computational Complexity and Fundamental Limitations to Fermionic Quantum Monte Carlo Simulations
doi: 10.1103/PhysRevLett.94.170201
url: https://arxiv.org/abs/cond-mat/0408370
claim: Low-temperature Boltzmann suppression can turn a discrete ground-state decision gap into a thermal estimation gap; positive weights alone do not give efficient sampling.
strata_touched: []
license: citation-only
triage: anchor
---

# Boltzmann suppression and computational access

The primary manuscript is arXiv:cond-mat/0408370, PDF pp. 2–3,
equations (3), (9), (10) and the paragraph immediately following (10).
Equation (3) defines the thermal trace and partition function. Equation (9)
specifies polynomial dependence on system size, inverse temperature and
statistical accuracy. For the three-dimensional Ising spin glass in (10),
the following paragraph chooses

$$
\beta J\ge N\ln2+\ln(12N)
$$

to suppress excited states sufficiently to separate the two cases of the
ground-energy decision problem by the thermal mean energy. The argument
balances exponentially many states against an energy penalty. The discussion
on PDF p. 3 also states that removing negative weights is insufficient when
the resulting sampling problem remains computationally hard.

The actual raw-clause application is
[finite transducers §10](../../docs/develop/theory/PREDICTIVE_THERMODYNAMIC_FINITE_TRANSDUCERS.md#10-approximate-thermodynamic-access-for-the-same-raw-clauses).
It uses a different Hamiltonian: each violated clause costs $n+1$, at fixed
$\beta=\ln2$. Its nonsolution Boltzmann mass is at most $1/2$. The specific
free-energy thresholds, the visible factor $3/2$, the ordinary input
converters and the approximate-sampling tolerances are derived there from
the repository's clause construction; they are not attributed to (10).

For the distribution, multiplying every energy by $n+1$ at fixed inverse
temperature is equivalent to multiplying inverse temperature by $n+1$ at
unit clause penalty. This equivalence preserves $\beta H$, not the numerical
free energy in a fixed energy unit. It supplies no fixed-temperature result
with bounded total interaction at each variable.

A positive, succinctly evaluable unnormalized weight does not specify an
efficient sampler, a mixing-time bound, or a physical preparation schedule.
An additive approximation to total free energy is also different from
additive approximation to free-energy density and from an exact partition
response. In the clause application, deterministic free-energy estimation,
classical randomized sampling with witness verification, and quantum state
preparation give respectively $P=NP$, $NP=RP$, and $NP\subseteq BQP$ under
their own uniform resource assumptions. These consequences use the stated
computational models; stochastic estimation is not silently treated as a
deterministic algorithm.
