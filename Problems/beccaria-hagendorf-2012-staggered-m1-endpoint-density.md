---
slug: beccaria-hagendorf-2012-staggered-m1-endpoint-density
bibkey: beccaria2012staggered
doi: 10.1088/1751-8113/45/36/365201
url: https://arxiv.org/abs/1206.4194v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/SpinChains/StaggeredM1EndpointDensity.result
---

# Beccaria–Hagendorf endpoint-density conjecture for the open staggered M1 chain

## Problem

Beccaria and Hagendorf, arXiv:1206.4194v2, §3.2.3, printed page 13:

> As similar pattern is found by probing if a particle is present on the last site. The data is consistent with $\rho_n^{(N)}(y)=y^{-2}\rho_n^{(1)}(y)$ for finite $n\leq8$. We conjecture this to hold for arbitrary system sizes.

The chain has $N=3n$, $n\geq1$, nearest-neighbour exclusion, the two inaccessible empty boundary sites, Jordan–Wigner fermionic signs, and staggering II $(y,y,1)$. The preregistration is issue #12308. The quantified formal claim covers every real $y\ne0$ and every nonzero zero-energy state, so it contains the source's ground-state assertion without an existence or uniqueness premise.

## Motivation

`D5/S3/Quantum/SpinChains/StaggeredM1EndpointDensity.result` proves the normalized endpoint-density relation for the source's operator model. The boundary sum rule relates two local occupation probabilities for arbitrary chain length.

## Gap

The source tests the endpoint relation through $n\leq8$. The settlement is universal in $n$. The bounded literature check in #12308 found no proof in its searched scope. The formal theorem does not establish exhaustive literature coverage or publication priority.

## Route

The hard-core subtype uses the existing admissible-word predicate `AdmissibleCount.Adm`. Its frozen characterization `ForbiddenNeighbourDeterminant.adm_iff_no_adjacent_true` supplies nearest-neighbour exclusion. The Jordan–Wigner tensor factors retain the parity sign.
`HardCoreModel.annihilator_number` proves that the hard-core annihilator
satisfies $c_j^\dagger c_j=n_j$ at every one-based site, with both sides
zero outside the chain; thus $P_j=1-n_j$ is the source projector. Local dressed and cubic products cancel away from their interaction sites. Period-three coefficients cancel the hopping currents, leaving an occupation diagonal on the full space. Compression to the hard-core block and a finite occupation telescope yield

$$\{Q,R\}+\{Q,R\}^{\dagger}=2b^2(c^2n_1-a^2n_N).$$

Positivity of $QQ^{\dagger}+Q^{\dagger}Q$ implies that both supercharges annihilate every zero-energy state. The anticommutator expectations therefore vanish. With $(a,b,c)=(y,y,1)$ and $y\ne0$, division by the scalar and the nonzero state norm gives the conjectured density relation.

## Falsifier

A nonzero zero-energy state in the stated hard-core model that violates the endpoint relation would contradict `result` in its formal system. A mismatch in the Jordan–Wigner sign, hard-core restriction, boundary projectors or genuine Hilbert adjoint would invalidate source fidelity. A primary publication already proving this exact conjecture would change the bounded literature assessment.

## Evidence

`StaggeredM1EndpointDensity.claim` states the complete quantified implication, and `result : claim` proves it. `SupersymmetricFermion.EndpointIdentity.endpoint_identity` proves the general period-three operator identity. The foundation chain computes the actual local operators and transfers their products to the hard-core block; no premise assumes the endpoint identity. The accepted axiom boundary is `propext`, `Classical.choice` and `Quot.sound`.

## Triage

Tier 1: a conjecture stated in the published mathematical-physics paper. The settlement is Proved for the stated model and parameter range.

### What the settlement shows

- **Proved in the foundation chain:** the operator identity holds for all real period-three couplings $(a,b,c)$, including $b=0$, and all $N=3n\geq3$. Its decisive mechanism is local-product localization followed by cancellation of the hopping currents and telescoping of the occupation diagonal.
- **Proved by `EndpointIdentity.endpoint_identity` and the local `zero_energy_weighted_sum_rule` in `StaggeredM1EndpointDensity.result`:** for $b\ne0$, every nonzero zero-energy state obeys $c^2\rho^{(1)}=a^2\rho^{(N)}$. This general sum rule is not a separate public theorem. The endpoint module's public settling result specializes it to staggering II.
- **Proved as a specialization of that sum rule:** staggering I $(y,1,y)$ gives equal endpoint densities when $y\ne0$. Other real period-three couplings with $b\ne0$ retain the weighted relation; if $a\ne0$, it gives $\rho^{(N)}=c^2a^{-2}\rho^{(1)}$. At $b=0$ the identity's scalar vanishes and this argument gives no density constraint; at $a=c=0$ the weighted relation is vacuous. These are boundaries of the implication, not counterexamples to an unasserted extension.
- **Open:** the source's companion boundary-density conjectures for $N=3n-1$, particularly §4.2.3's thermodynamic-limit agreement with the $N=3n$ expressions, are not settled here. The length hypothesis $N\equiv0\pmod3$ remains in the operator identity.
- **Open:** the first-site thermodynamic-limit formulas in §3.2.3 and the centre-density formulas for $j_c=3n/2$ when $n$ is even and $j_c=3(n+1)/2$ when $n$ is odd are not settled. The finite endpoint sum rule relates the thermodynamic endpoint limits whenever those limits exist; it does not prove their existence or the proposed generating functions.
- **Literature, not formalized here:** the source's §2.1 existence and uniqueness statement for nonzero couplings cites [14], L. Huijse and K. Schoutens, “Supersymmetry, lattice fermions, independence complexes and cohomology theory”, Adv. Theor. Math. Phys. 14 (2010), 643–694. Neither existence nor uniqueness is used in `result`.
- **Proved consequence for the source's dependent observations:** the last-site density is determined by the first-site density at each finite $N=3n$ and $y\ne0$. The source's deduction of last-site thermodynamic expressions from its conjectured first-site expressions therefore has an established finite-size algebraic relation; the analytic and first-site conjectures remain open.

## ASSUMED-UNVERIFIED

The literature conclusion is not-found-in-searched-scope as recorded in #12308; citation-index completeness and worldwide absence of a prior proof are unverified. The ground-state existence and uniqueness result is literature attribution, not a theorem of this delivery. No priority claim or settlement of the neighbouring thermodynamic and interior-density conjectures follows from the endpoint theorem.

Information-escape registration is paused under CLAUDE.md §3.9.
