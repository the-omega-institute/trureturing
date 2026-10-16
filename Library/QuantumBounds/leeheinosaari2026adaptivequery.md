---
bibkey: leeheinosaari2026adaptivequery
authors: Hanwool Lee; Teiko Heinosaari
year: 2026
title: "Perfect Discrimination of Non-Orthogonal Quantum States via Adaptive Post-Measurement Queries"
doi: null
url: https://arxiv.org/abs/2608.01167v1
claim: "In state discrimination with a one-bit query, the pre-measurement success probability is P_pre = max over binary partitions and subensemble measurements (Eq. (3)), and the adaptive post-measurement success probability is P^adap_post = max over a measurement and outcome-dependent partitions (Eq. (5)); P^adap_post = (n − 1) P_aux for the auxiliary ensemble of pairwise mixtures (Theorem 1). §VI asks whether an ensemble of four qubit states with P^adap_post > P_pre exists, and suggests that this may never occur for qubit ensembles with n ≥ 4, leaving a proof open."
strata_touched:
  - D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation
license: citation-only
triage: anchor
---

# Lee and Heinosaari, adaptive post-measurement queries

H. Lee and T. Heinosaari, *Perfect Discrimination of Non-Orthogonal Quantum States via Adaptive Post-Measurement Queries*, arXiv:2608.01167 [quant-ph] (v1 of 2 August 2026, the only version listed).

## Verified locator

DOI: null

Source: https://arxiv.org/abs/2608.01167v1

No DOI or journal reference is listed in the arXiv metadata. The text was read from the PDF https://arxiv.org/pdf/2608.01167v1:
- p. 2, the section on state discrimination with a query, Eqs. (1)–(5);
- p. 3, Theorem 1;
- p. 6, §VI (Discussion).

## Source statements

Eq. (3) (p. 2): "The success probability in the pre-measurement scenario, denoted by Ppre, is obtained by maximizing over all 2^{n−1} binary partitions P and the measurements M and N for each subensemble E0 and E1, Ppre = max_{P,M,N} Σ_{x∈X0} qx tr[ϱx Mx] + Σ_{x∈X1} qx tr[ϱx Nx] (3) where Σ_{x∈X0} Mx = Σ_{x∈X1} Nx = 1."

Eq. (5) (p. 2): "We call this an adaptive post-measurement query, and denote its success probability by P^adap_post: P^adap_post = max_M Σ_z max_{{Pz}} Σ_{ℓ=0,1} q_{f(ℓ,z)} tr[ϱ_{f(ℓ,z)} Mz] (5) where the partitions {Pz} now depend on z."

§VI (p. 6): "A relevant question is whether there exists an ensemble of four qubit states with this property. We tested two natural symmetric candidates, a symmetric informationally complete ensemble that forms a tetrahedron in the Bloch sphere and a geometrically uniform ensemble that includes the BB84 states as a special case. In both cases, we found P^adap_post < P_pre (see the Supplemental Material for the detailed calculations). These examples suggest that P^adap_post > P_pre may never occur for qubit ensembles with n ≥ 4, though we leave a proof as an open question."

## Reading used by the repository

An ensemble of n qubit states has priors q_x ≥ 0 with Σ q_x = 1 and 2 × 2 density matrices ϱ_x, as in the source's framework, which allows arbitrary priors. P_pre is the supremum of the pre-measurement strategy values of Eq. (3), over all partitions including the one with an empty cell. P^adap_post is attained by finite measurements with outcome-dependent partitions and guesses, as in Eq. (5). The suggestion of §VI is read as: for every n ≥ 4 and every ensemble of n qubit states, P^adap_post ≤ P_pre.
