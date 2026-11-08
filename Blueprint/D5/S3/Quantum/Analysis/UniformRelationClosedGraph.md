# Uniform relation readouts and closed graphs

## Abstract

A single finite relation formula on all actual outputs recovers the original total relation as a bounded real bilinear map on a Banach space.

**Definition 1.1 (Actual outputs).**

$$\forall E \in RealNormedSpace\left(\right),\; \forall D \in TotalBinaryMaps\left(E\right),\; outputs\left(D\right) = range\left(uncurry\left(D\right)\right)$$

*Formalization.* `D5/S3/Quantum/Analysis/UniformRelationClosedGraph.outputs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The set is the literal range of D on all pairs of original inputs. No linear span, closure or output realization is included.

**Definition 1.2 (Uniform finite readout).**

$$\forall E \in RealNormedSpace\left(\right),\; \forall P \in Subsets\left(ContinuousDual\left(E\right)\right),\; \forall D \in TotalBinaryMaps\left(E\right),\; UniformReadout\left(P, D\right) \Leftrightarrow \left(\forall alpha \in P,\; \forall eta \in PositiveReals\left(\right),\; \exists m \in Naturals\left(\right),\; \exists t \in Functions\left(Fin\left(m\right), outputs\left(D\right)\right),\; \exists beta \in Functions\left(Fin\left(m\right), P\right),\; \exists c \in Functions\left(Fin\left(m\right), Reals\left(\right)\right),\; \forall p \in outputs\left(D\right),\; abs\left(alpha\left(p\right) - \sum_{j\in Fin\left(m\right)} c\left(j\right) \cdot beta\left(j\right)\left(D\left(p, t\left(j\right)\right)\right)\right) \le eta \cdot \left\lVert p \right\rVert\right)$$

*Formalization.* `D5/S3/Quantum/Analysis/UniformRelationClosedGraph.UniformReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each original continuous evaluation alpha and positive eta choose a natural number m, tests t indexed by Fin(m), evaluations beta indexed by Fin(m), and real coefficients c indexed by Fin(m). Each test is an actual output and each beta belongs to the same original family P. The displayed bound then holds for every actual output p with those same choices. The index may be empty, and tests and evaluations may repeat. No coefficient bound is imposed.

**Theorem 1.3 (Recovery in the original Banach norm).**

$$\forall E \in RealBanachSpace\left(\right),\; \forall P \in Subsets\left(ContinuousDual\left(E\right)\right),\; \forall S \in ContinuousRealBilinearMaps\left(E, E, E\right),\; \forall D \in TotalBinaryMaps\left(E\right),\; \left(\left(\forall x \in E,\; \left(\forall alpha \in P,\; alpha\left(x\right) = 0\right) \Rightarrow x = 0\right) \land \left(\left(\forall a \in E,\; \forall b \in E,\; S\left(a, b\right) = S\left(b, a\right)\right) \land \left(\left(\forall alpha \in P,\; \forall a \in E,\; \forall b \in E,\; complex\left(alpha\left(S\left(b, a\right)\right)\right) - i \cdot complex\left(alpha\left(D\left(b, a\right)\right)\right) = conj\left(complex\left(alpha\left(S\left(a, b\right)\right)\right) - i \cdot complex\left(alpha\left(D\left(a, b\right)\right)\right)\right)\right) \land \left(\left(\forall a \in E,\; \forall b \in E,\; \forall c \in E,\; S\left(S\left(a, b\right), c\right) - S\left(a, S\left(b, c\right)\right) = D\left(D\left(a, b\right), c\right) - D\left(a, D\left(b, c\right)\right)\right) \land UniformReadout\left(P, D\right)\right)\right)\right)\right) \Rightarrow \left(\exists B \in ContinuousRealBilinearMaps\left(E, E, E\right),\; \left(\forall a \in E,\; \forall b \in E,\; B\left(a, b\right) = D\left(a, b\right)\right) \land \left(\exists K \in Reals\left(\right),\; 0 \le K \land \left(\forall a \in E,\; \forall b \in E,\; \left\lVert D\left(a, b\right) \right\rVert \le K \cdot \left\lVert a \right\rVert \cdot \left\lVert b \right\rVert\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/UniformRelationClosedGraph.bilinear_bounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

E is any real Banach space in any universe, including the zero space. P is any subset of its continuous real dual that separates points; zero evaluations are allowed. S is a continuous real bilinear map represented by E to continuous linear maps from E to E, and is symmetric. D initially is only a total map on the same E. Conjugacy uses the actual complex numbers alpha(S(a,b))-i alpha(D(a,b)), for every original alpha and both original inputs. The rebracketing identity is required on every original triple, including nested outputs. No regularity, additivity, homogeneity, measurability or boundedness of D is a hypothesis.

Conjugacy and separation give skewness. Applying the real rebracketing law to its three cyclic permutations and eliminating the three nested terms gives D(D(a,b),t)=S(b,S(a,t))-S(a,S(b,t)). This argument never expands D on a sum. A common finite readout formula reflects every finite real dependency among actual output rows back to the outputs. Apply that reflection to the three outputs D(a+b,c), D(a,c), D(b,c), and then to the two outputs D(r a,b), D(a,b). This proves real linearity in the first slot; skewness supplies the second slot.

For a fixed a take b(n) tending to x and D(a,b(n)) tending to y. Fix alpha and eta and choose one readout formula. It applies to all actual outputs D(a,b(n)) and to D(a,x), without requiring y to be an output. The nested identity expresses each finite readout as a continuous function of b(n), using only S and the original continuous evaluations. Passing to the limit yields an error at most eta times the norm of y. Comparing with the formula at D(a,x) bounds the difference of their alpha values by eta times the sum of their norms. Let eta tend to zero and use separation. Thus each original linear row has a closed graph.

The Banach closed-graph theorem makes each row continuous. Skewness bounds the rows indexed by the original closed unit ball pointwise, using the opposite row. Banach-Steinhaus gives a common operator bound. Scaling gives the displayed finite joint bound and the continuous bilinear map B, whose value equals D on every original pair. Closed graph and Banach-Steinhaus are the pinned Mathlib suppliers; no new relation is selected.

For an Archimedean order-unit application, use its original norm and original separating positive continuous evaluations. Positivity, cone and unit are unnecessary for this implication, so the theorem applies without changing them. It assumes neither complex positive tables nor a Jordan identity, finite dimension, a predual or a representation. It supplies no extension from an incomplete original domain, Leibniz law, cone preserving flow, physical preparation or instrument. The finite-dependency algebra is the dimension independent subargument of the three-label theory; the analytical bridge uses the uniform formula on actual outputs. No literature priority is asserted.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/UniformRelationClosedGraph.UniformReadout`
- Truth anchor: `D5/S3/Quantum/Analysis/UniformRelationClosedGraph.bilinear_bounded`
- Truth anchor: `D5/S3/Quantum/Analysis/UniformRelationClosedGraph.outputs`
