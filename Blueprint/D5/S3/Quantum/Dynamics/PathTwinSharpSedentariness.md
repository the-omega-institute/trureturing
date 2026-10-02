# The twin end vertex of P'_9 is not sharply 1/9-sedentary

## Abstract

In the graph P'_9, the path on vertices 1 to 9 with an extra vertex 10 joined to vertex 2, the return amplitude of the quantum walk U(t) = exp(itA) at vertex 1 satisfies |U(t)_(1,1)| >= 5/18 for every real t. So vertex 1 is not sharply 1/9-sedentary, which refutes the conjecture of H. Monterde (arXiv:2401.00362) that vertex 1 of P'_n is sharply 1/n-sedentary for every odd n >= 5.

**Definition 1.1 (The graph P'_n).**

$$(((((i + 1 = j) \land (j < n)) \lor ((j + 1 = i) \land (i < n))) \lor (((i = 1) \land (j = n)) \lor ((i = n) \land (j = 1)))) \Rightarrow \operatorname{pathTwin}\left(n\right)\left(i, j\right) = 1) \land ((\neg ((((i + 1 = j) \land (j < n)) \lor ((j + 1 = i) \land (i < n))) \lor (((i = 1) \land (j = n)) \lor ((i = n) \land (j = 1))))) \Rightarrow \operatorname{pathTwin}\left(n\right)\left(i, j\right) = 0)$$

*Formalization.* `D5/S3/Quantum/Dynamics/PathTwinSharpSedentariness.pathTwin` (`✓ std3`).

*Citation.* Hermie Monterde (2023). *New results in vertex sedentariness*. DOI: [10.1016/j.disc.2025.114959](https://doi.org/10.1016/j.disc.2025.114959). URL: <https://arxiv.org/abs/2401.00362v1>.

*Commentary.*

The adjacency matrix of P'_n on the vertices 1, ..., n + 1: the entry is 1 on the edges and 0 elsewhere, where the edges are those of the path 1, 2, ..., n and the edge between vertex 2 and vertex n + 1, so that vertices 1 and n + 1 are non-adjacent twins. In the formal statement vertex j is the index j - 1 of Fin (n + 1).

**Definition 1.2 (Sharp sedentariness).**

$$\operatorname{SharplySedentary}\left(A, u, C\right) \Leftrightarrow (((0 < C) \land (C \le 1)) \land (\operatorname{inf}\left(t > 0\right) \left\lVert \operatorname{hamiltonianPropagator}\left(A, -t, u, u\right) \right\rVert = C))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PathTwinSharpSedentariness.SharplySedentary` (`✓ std3`).

*Citation.* Hermie Monterde (2023). *New results in vertex sedentariness*. DOI: [10.1016/j.disc.2025.114959](https://doi.org/10.1016/j.disc.2025.114959). URL: <https://arxiv.org/abs/2401.00362v1>.

*Commentary.*

For the quantum walk U(t) = exp(itA), a vertex u is sharply C-sedentary when 0 < C <= 1 and the infimum over t > 0 of |U(t)_(u,u)| equals C. The formal statement writes exp(itA) as the propagator exp(-isA) at s = -t.

**Definition 1.3 (The conjecture).**

$$claim \Leftrightarrow (\forall n, (\operatorname{Odd}\left(n\right)) \Rightarrow \left((5 \le n) \Rightarrow \operatorname{SharplySedentary}\left(\operatorname{pathTwin}\left(n\right), 0, \frac{1}{n}\right)\right))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PathTwinSharpSedentariness.claim` (`✓ std3`).

*Citation.* Hermie Monterde (2023). *New results in vertex sedentariness*. DOI: [10.1016/j.disc.2025.114959](https://doi.org/10.1016/j.disc.2025.114959). URL: <https://arxiv.org/abs/2401.00362v1>.

*Commentary.*

The conjecture of the paper: for every odd n >= 5, vertex 1 of P'_n is sharply 1/n-sedentary.

**Theorem 1.4 (The conjecture fails at n = 9).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PathTwinSharpSedentariness.result` (`✓ std3`). ∎

*Resolves.* `Problems/monterde-2023-path-twin-sharp-sedentariness` (refuted) by `D5/S3/Quantum/Dynamics/PathTwinSharpSedentariness.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"monterde-2023-path-twin-sharp-sedentariness","declaration_gid":"D5/S3/Quantum/Dynamics/PathTwinSharpSedentariness.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Hermie Monterde (2023). *New results in vertex sedentariness*. DOI: [10.1016/j.disc.2025.114959](https://doi.org/10.1016/j.disc.2025.114959). URL: <https://arxiv.org/abs/2401.00362v1>.

*Commentary.*

Let A be the adjacency matrix of P'_9 and put theta_k = (2k + 1) pi/18 for k = 0, ..., 8. For each k the vector with entries 1/2, cos(theta_k), cos(2 theta_k), ..., cos(8 theta_k), 1/2 is an eigenvector of A for the eigenvalue 2 cos(theta_k); the last row uses cos(9 theta_k) = 0. The vector e_1 - e_10 lies in the kernel of A. The closed form sin(a/2) times the sum of cos(ak + b) over k < 9 equals sin(9a/2) cos(4a + b), with a = m pi/9 and b = m pi/18, gives sin(m pi/2) cos(m pi/2) = sin(m pi)/2 = 0, so the sum of cos(m theta_k) over k vanishes for m = 1, ..., 8, and so e_1 = (e_1 - e_10)/2 plus one ninth of the sum of the nine eigenvectors. The matrix exponential acts on each eigenvector by the scalar exponential, which gives U(t)_(1,1) = 1/2 + (1/18) times the sum of exp(2it cos(theta_k)). Pairing theta_k with pi - theta_k, this equals 5/9 + (1/9)(cos(alpha t) + cos(sqrt(3) t) + cos(beta t) + cos(gamma t)) with alpha = 2 cos(pi/18), beta = 2 cos(5 pi/18) and gamma = 2 cos(7 pi/18). Because cos(pi/3) = 1/2, alpha = beta + gamma. For real a and b, cos a + cos b + cos(a + b) >= -3/2, since (1 + cos a + cos b)^2 + (sin a - sin b)^2 = 3 + 2(cos a + cos b + cos(a + b)). Hence U(t)_(1,1) >= 5/9 - (1/9)(3/2 + 1) = 5/18 for every real t, and the infimum over t > 0 is at least 5/18, which is larger than 1/9.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/PathTwinSharpSedentariness.SharplySedentary`
- Truth anchor: `D5/S3/Quantum/Dynamics/PathTwinSharpSedentariness.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/PathTwinSharpSedentariness.pathTwin`
- Truth anchor: `D5/S3/Quantum/Dynamics/PathTwinSharpSedentariness.result`
- Dependency: [D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity](EnergyEigenstateStationarity.md)
- Dependency: [D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow](ProjectionProbabilityFlow.md)
