# Sharp return probabilities for conference graphs

## Abstract

Conference walks have sharp square-order floors and nonsquare vanishing infima.

**Definition 1.1 (The square-order classification and the family bound).**

$$\operatorname{D5.S3.Quantum.Dynamics.ConferenceGraphSedentariness.claim} = ((\forall (m: \mathbb{N}), ((1 \le m) \to (\forall (V: \operatorname{Type}), ([\operatorname{Fintype}\left(V\right)] ([\operatorname{DecidableEq}\left(V\right)] (\forall (G: \operatorname{SimpleGraph}\left(V\right)), ([\operatorname{DecidableRel}\left(\operatorname{SimpleGraph.Adj}\left(G\right)\right)] ((\operatorname{SimpleGraph.IsSRGWith}\left(G, 4 \cdot m + 1, 2 \cdot m, m - 1, m\right)) \to (\forall (u: V), (((\operatorname{IsSquare}\left(4 \cdot m + 1\right)) \to ((\forall (t: \mathbb{R}), (\frac{1}{(4 \cdot (\operatorname{Nat.cast}\left(m\right): \mathbb{R}) + 1)^{2}} \le \left\lVert \operatorname{D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow.hamiltonianPropagator}\left(\operatorname{SimpleGraph.adjMatrix}\left(\mathbb{C}, G\right), -t, u, u\right) \right\rVert^{2})) \land (\exists (t: \mathbb{R}), ((0 < t) \land (\left\lVert \operatorname{D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow.hamiltonianPropagator}\left(\operatorname{SimpleGraph.adjMatrix}\left(\mathbb{C}, G\right), -t, u, u\right) \right\rVert^{2} = \frac{1}{(4 \cdot (\operatorname{Nat.cast}\left(m\right): \mathbb{R}) + 1)^{2}}))))) \land ((\neg (\operatorname{IsSquare}\left(4 \cdot m + 1\right))) \to ((\forall (t: \mathbb{R}), (0 \le \left\lVert \operatorname{D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow.hamiltonianPropagator}\left(\operatorname{SimpleGraph.adjMatrix}\left(\mathbb{C}, G\right), -t, u, u\right) \right\rVert^{2})) \land (\forall (\varepsilon: \mathbb{R}), ((0 < \varepsilon) \to (\exists (t: \mathbb{R}), ((0 < t) \land (\left\lVert \operatorname{D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow.hamiltonianPropagator}\left(\operatorname{SimpleGraph.adjMatrix}\left(\mathbb{C}, G\right), -t, u, u\right) \right\rVert^{2} < \varepsilon))))))))))))))))) \land (\forall (c: \mathbb{R}), ((0 < c) \to (\exists (N: \mathbb{N}), (\forall (m: \mathbb{N}), ((1 \le m) \to ((N \le 4 \cdot m + 1) \to (\forall (V: \operatorname{Type}), ([\operatorname{Fintype}\left(V\right)] ([\operatorname{DecidableEq}\left(V\right)] (\forall (G: \operatorname{SimpleGraph}\left(V\right)), ([\operatorname{DecidableRel}\left(\operatorname{SimpleGraph.Adj}\left(G\right)\right)] ((\operatorname{SimpleGraph.IsSRGWith}\left(G, 4 \cdot m + 1, 2 \cdot m, m - 1, m\right)) \to (\forall (u: V), (\exists (t: \mathbb{R}), ((0 < t) \land (\left\lVert \operatorname{D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow.hamiltonianPropagator}\left(\operatorname{SimpleGraph.adjMatrix}\left(\mathbb{C}, G\right), -t, u, u\right) \right\rVert^{2} < c)))))))))))))))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/ConferenceGraphSedentariness.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Chris Godsil (2021). *Sedentary quantum walks*. DOI: [10.1016/j.laa.2020.08.027](https://doi.org/10.1016/j.laa.2020.08.027). URL: <https://arxiv.org/abs/1710.11192v1>.

*Commentary.*

For m at least one, a conference graph has strongly regular parameters (4m + 1, 2m, m − 1, m). Its order is n = 4m + 1. At each vertex, the squared norm of the diagonal walk entry has sharp lower bound 1/n² at square orders, with equality at a positive time. At nonsquare orders it is nonnegative and becomes smaller than every positive real number at a positive time. For each c > 0, all sufficiently large conference graphs have, at every vertex, a positive time with return probability below c. The time may depend on the vertex. The walk is hamiltonianPropagator applied at −t, hence exp(itA). Godsil defines U(t) and M(t) in the arXiv v1 TeX source conemix.tex, lines 190–207, and asks whether conference-graph diagonal entries of M(t) can be bounded away from zero at lines 1035–1038. The classification here answers that question; the source does not state this classification as a theorem. No existence of conference graphs at prescribed orders is asserted.

**Theorem 1.2 (Sharp square-order floors and vanishing nonsquare infima).**

$$(\forall (m: \mathbb{N}), ((1 \le m) \to (\forall (V: \operatorname{Type}), ([\operatorname{Fintype}\left(V\right)] ([\operatorname{DecidableEq}\left(V\right)] (\forall (G: \operatorname{SimpleGraph}\left(V\right)), ([\operatorname{DecidableRel}\left(\operatorname{SimpleGraph.Adj}\left(G\right)\right)] ((\operatorname{SimpleGraph.IsSRGWith}\left(G, 4 \cdot m + 1, 2 \cdot m, m - 1, m\right)) \to (\forall (u: V), (((\operatorname{IsSquare}\left(4 \cdot m + 1\right)) \to ((\forall (t: \mathbb{R}), (\frac{1}{(4 \cdot (\operatorname{Nat.cast}\left(m\right): \mathbb{R}) + 1)^{2}} \le \left\lVert \operatorname{D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow.hamiltonianPropagator}\left(\operatorname{SimpleGraph.adjMatrix}\left(\mathbb{C}, G\right), -t, u, u\right) \right\rVert^{2})) \land (\exists (t: \mathbb{R}), ((0 < t) \land (\left\lVert \operatorname{D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow.hamiltonianPropagator}\left(\operatorname{SimpleGraph.adjMatrix}\left(\mathbb{C}, G\right), -t, u, u\right) \right\rVert^{2} = \frac{1}{(4 \cdot (\operatorname{Nat.cast}\left(m\right): \mathbb{R}) + 1)^{2}}))))) \land ((\neg (\operatorname{IsSquare}\left(4 \cdot m + 1\right))) \to ((\forall (t: \mathbb{R}), (0 \le \left\lVert \operatorname{D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow.hamiltonianPropagator}\left(\operatorname{SimpleGraph.adjMatrix}\left(\mathbb{C}, G\right), -t, u, u\right) \right\rVert^{2})) \land (\forall (\varepsilon: \mathbb{R}), ((0 < \varepsilon) \to (\exists (t: \mathbb{R}), ((0 < t) \land (\left\lVert \operatorname{D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow.hamiltonianPropagator}\left(\operatorname{SimpleGraph.adjMatrix}\left(\mathbb{C}, G\right), -t, u, u\right) \right\rVert^{2} < \varepsilon))))))))))))))))) \land (\forall (c: \mathbb{R}), ((0 < c) \to (\exists (N: \mathbb{N}), (\forall (m: \mathbb{N}), ((1 \le m) \to ((N \le 4 \cdot m + 1) \to (\forall (V: \operatorname{Type}), ([\operatorname{Fintype}\left(V\right)] ([\operatorname{DecidableEq}\left(V\right)] (\forall (G: \operatorname{SimpleGraph}\left(V\right)), ([\operatorname{DecidableRel}\left(\operatorname{SimpleGraph.Adj}\left(G\right)\right)] ((\operatorname{SimpleGraph.IsSRGWith}\left(G, 4 \cdot m + 1, 2 \cdot m, m - 1, m\right)) \to (\forall (u: V), (\exists (t: \mathbb{R}), ((0 < t) \land (\left\lVert \operatorname{D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow.hamiltonianPropagator}\left(\operatorname{SimpleGraph.adjMatrix}\left(\mathbb{C}, G\right), -t, u, u\right) \right\rVert^{2} < c))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/ConferenceGraphSedentariness.result` (`✓ std3`). ∎

*Resolves.* `Problems/godsil-2017-conference-graph-sedentariness` (proved) by `D5/S3/Quantum/Dynamics/ConferenceGraphSedentariness.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"godsil-2017-conference-graph-sedentariness","declaration_gid":"D5/S3/Quantum/Dynamics/ConferenceGraphSedentariness.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Chris Godsil (2021). *Sedentary quantum walks*. DOI: [10.1016/j.laa.2020.08.027](https://doi.org/10.1016/j.laa.2020.08.027). URL: <https://arxiv.org/abs/1710.11192v1>.

*Commentary.*

Fix m ≥ 1 and a graph with the stated strongly regular parameters. Write n = 4m + 1, A for its complex adjacency matrix, I for the identity matrix and J for the all-ones matrix. The common-neighbor counts give A² = 2mI + (m − 1)A + m(J − I − A) = mI − A + mJ. Regularity gives AJ = JA = 2mJ, and the vertex count is n.

Set r = √n, θ = (−1 + r)/2, τ = (−1 − r)/2, P = J/n, Q = I − P and B = A − 2mP. The constant projection is idempotent. The identities BP = PB = 0, Q² = Q, BQ = QB = B and B² + B = mQ follow. Since θ + τ = −1, θ − τ = r and θτ = −m, the matrices E = (B − τQ)/r and F = (θQ − B)/r satisfy BE = θE and BF = τF. Consequently P, E and F are pairwise orthogonal idempotents, P + E + F = I and A = 2mP + θE + τF. At every vertex u, Pᵤᵤ = 1/n and Eᵤᵤ = Fᵤᵤ = 2m/n: these follow from Aᵤᵤ = 0, Bᵤᵤ = −2m/n and Qᵤᵤ = (n − 1)/n.

The three scalar multiples of the idempotents commute. Factoring the exponential of their sum and using exp(zP) = I + (exp(z) − 1)P gives exp(aP + bE + cF) = exp(a)P + exp(b)E + exp(c)F. Apply this with a = 2mit, b = iθt and c = iτt. Taking diagonal entries yields U(t)ᵤᵤ = exp(2mit)/n + (exp(iθt) + exp(iτt))2m/n. Extracting the unit phase exp(−it/2) and combining the last two exponentials as a cosine gives pᵤ(t) = |exp(int/2) + (n − 1)cos(rt/2)|²/n².

If n = q² for a natural q, then q is odd and q ≥ 3. The inequality |sin(qx)| ≤ q|sin x|, applied at x + π/2, gives |cos(qx)| ≤ q|cos x|. Put x = qt/2 and a = n − 1. Expanding the squared norm gives n²pᵤ(t) = 1 + a²cos²x + 2a cos x cos(qx). The absolute-value bound on the mixed product and a − 2q ≥ 0 give n²pᵤ(t) ≥ 1 + a(a − 2q)cos²x ≥ 1. For every order, t = π/√n is positive and makes cos(rt/2) zero, so pᵤ(t) = 1/n². In particular t = π/q attains the square-order bound.

If n is nonsquare, r = √n is irrational, and therefore the integer multiples of the angle 2π/r are dense in the circle. On that circle the continuous function f(z) = (1 + 4m cos z)²/n² vanishes at z = arccos(−1/(4m)) and satisfies f(0) = 1. For every ε > 0, density supplies an integer j with f(j·2π/r) < min(ε, 1). This j is nonzero. Choose t = 4π|j|/n > 0. Then exp(int/2) = 1, rt/2 = |j|·2π/r, and evenness of cosine identifies the return probability with f(j·2π/r), which is below ε. Squared norms are nonnegative, proving that the infimum over positive times is zero.

Finally fix c > 0 and choose a natural N with N > max(1, 1/c). For every order n ≥ N, the positive time π/√n has return probability 1/n² < c. This proves the family clause directly from the attained value, for both square and nonsquare orders.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/ConferenceGraphSedentariness.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/ConferenceGraphSedentariness.result`
- Dependency: [D5/S3/Fourier/PositiveFourierApproximationRefutation](../../Fourier/PositiveFourierApproximationRefutation.md)
- Dependency: [D5/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation](BarrigaTenModeFourierEdgeRefutation.md)
- Dependency: [D5/S3/Quantum/Dynamics/RationalWeightPathTransfer](RationalWeightPathTransfer.md)
- Dependency: [D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality](../Measurement/DetectorSensorDickeOptimality.md)
