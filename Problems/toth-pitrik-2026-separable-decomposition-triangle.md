---
slug: toth-pitrik-2026-separable-decomposition-triangle
bibkey: toth2026wassersteinfidelities
doi: null
url: https://arxiv.org/abs/2506.14523v6
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/SeparableDecompositionTriangleRefutation.result
---

# A mixed middle state breaks the decomposition Wasserstein triangle inequality

## Problem

G. Tóth and J. Pitrik, *Quantum Wasserstein distance and its relation to several types of fidelities*, arXiv:2506.14523v6, equation (83) and Section III.3.3, ask for the triangle inequality for the modified pure-state decomposition quantity:

> it would be important to show that these quantities fulfill the triangle inequality. Let us now examine this in the case of D̃_DPT,decomp(ϱ,σ).

Theorem 10 proves it with a pure middle state. The assertion considered here allows every middle density matrix: for every dimension, every finite Hermitian observable family, and all density matrices ρ, ω, τ, the distance from ρ to τ is at most the sum of the distances through ω. Issue [#30966](https://github.com/the-omega-institute/trureturing/issues/30966) fixes this reading. The source definitions and quotations are in the [existing literature note](../Library/QuantumContext/toth2026wassersteinfidelities.md).

## Motivation

A metric triangle inequality would allow short pure-state decomposition transports to compose through arbitrary mixed states. A density matrix admits distinct ensembles, so the same middle density matrix need not supply a common ensemble for both transports.

## Gap

The source and preregistration #30966 fix the original question. The repository's comparison refutation concerns Conjecture 1 and does not settle this triangle assertion. The literature assessment is limited to the v6 text and the bounded search recorded in preregistration #30966; worldwide priority is not established.

## Route

Use three orthogonal two-dimensional blocks A = {0,1}, B = {2,3}, C = {4,5} in dimension six, with ρᵤ = Πᵤ/2. The seven block-diagonal observables are (X,X,0), (Y,Z,0), (Z,0,0), (0,Y,X), (0,0,Y), (0,0,Z), and L = diag(0,0,1,1,2,2), where X,Y,Z are the Pauli matrices.

The normalized pure-state cost is half the sum of squared differences of observable expectations. An equal mixture of the two X eigenstates in A and the corresponding X eigenstates in B gives squared cost 1/2. An equal mixture of the two Y eigenstates in B and the corresponding X eigenstates in C also gives squared cost 1/2.

For any decomposition of ρ_A and ρ_C, a positive-weight vector is supported in its marginal's block: each outside diagonal coordinate is a sum of nonnegative weighted squared absolute values and equals zero. Each supported unit vector has a unit Bloch vector. The A and C Bloch coordinates occupy disjoint observable coordinates, contributing 1 + 1, while L contributes 4. Thus every positive-weight pair has cost 3 and the weighted sum is 3. An explicit two-term ensemble supplies a nonempty admissible set. Consequently the long distance is √3, while the sum of the short distances is at most 2√(1/2) = √2 < √3.

## Falsifier

The assertion retains all dimensions, finite observable families, Hermiticity hypotheses, and density matrices. The decompositions retain arbitrary finite ensemble length, nonnegative real weights summing to one, unit complex vectors, and both exact density-matrix marginal identities. The infimum is over the entire set of these ensembles, rather than over the explicit short-edge witnesses alone.

The identification of the pure-state cost with equation (12) requires the unique coupling of pure marginals to be their tensor product. The identity Tr(Hᵀϱᵀ) = Tr(Hϱ) preserves the relevant expectations. Expanding the quadratic cost gives half the sum of the two variances and squared expectation differences; subtracting the averaged self-costs cancels the variances. This correspondence is a mathematical explanation, not a formalized Lean theorem here.

The finite-decomposition infimum agrees with the minimum in equation (83) for density marginals and Hermitian observables by the following mathematical argument, not formalized here. The space of pairs of pure-state projectors is compact, and the map (P,Q) ↦ (P,Q,pureCost(P,Q)) is continuous in the finite-dimensional real space of two Hermitian matrices and a cost coordinate. Its convex hull is compact. The slice with the two prescribed density marginals is nonempty: spectral decompositions with product weights give a finite witness. The cost coordinate attains its minimum on this compact slice, and Carathéodory's theorem represents a minimizer by finitely many pure-state pairs. A countable decomposition has its marginal-and-cost barycenter in the same closed convex hull, so allowing countable decompositions cannot lower this minimum. Subject to this argument and the pure-state correspondence above, the definitions implement equation (83).

## Evidence

The mathematical target is `D5/S3/Quantum/QuantumChannels/SeparableDecompositionTriangleRefutation.lean`, with `claim : Prop` and `result : ¬ claim`. Its public definitions specify the cost, admissible finite decompositions, real infimum and square root; the auxiliary proof declarations are private.

The selected Lean report and canonical frozen state determine verification and axiom status. This dossier does not replace those machine artifacts.

## Triage

**Proved by `result`:** the universal triangle assertion fails with the mixed middle density matrix Π_B/2. The Lean statement concerns the finite-ensemble expectation-cost encoding above. The correspondences to equation (12) and to the minimum in equation (83), including countable decompositions, are the unformalized mathematical explanations stated under Falsifier.

**Mathematical explanation, not separately formalized:** the middle state has both the X-axis ensemble used on AB and the Y-axis ensemble used on BC. These ensembles give the same density matrix but cannot be identified as one ensemble to glue the two short transports. Therefore the pure-middle-state condition in Theorem 10 cannot be removed for the claimed extension to arbitrary mixed middle states; Theorem 10 itself is unaffected.

**Paper consequence, not formalized:** the same example also violates the triangle inequality for the modified separable quantity of equation (90). Every pure state supported in a block has total observable variance 2. Therefore every separable ensemble coupling on any of these block pairs has unmodified cost equal to 2 plus its decomposition cost, and each squared separable self-distance has infimum 2, attained by pairing a block ensemble with itself; the modification cancels that constant. This argument is stated only on paper and is not an additional Lean theorem.

**Open:** a general criterion characterizing families of observables for which the decomposition quantity does satisfy the triangle inequality.

## ASSUMED-UNVERIFIED

The source evidence is limited to the v6 text and the bounded literature assessment recorded in preregistration #30966. No exhaustive literature or priority claim is made. The pure-state correspondence to equation (12), the compactness and Carathéodory correspondence between finite sInf, the minimum in equation (83) and countable decompositions, the ensemble-gluing explanation, the effect on equation (90), and the characterization question above are not formalized.
