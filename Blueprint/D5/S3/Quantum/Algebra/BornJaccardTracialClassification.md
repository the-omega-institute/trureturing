# Born-weighted Jaccard tracial classification

## Abstract

Born-weighted Jaccard distances on all complex subspaces are metrics exactly for tracial states.

**Theorem 1.1 (Full subspace classification and faithful separation).**

$$\forall n \in \mathbb{N},\; \forall rho \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \forall c \in \mathbb{R},\; ((2 \leq n) \land ((\operatorname{PosDef}\left(rho\right)) \land ((\operatorname{Tr}\left(rho\right) = 1) \land (0 \leq c)))) \Rightarrow (((\operatorname{Tri}\left(rho, c\right)) \iff (rho = \frac{I}{n})) \land (((rho = \frac{I}{n}) \Rightarrow (\operatorname{Metric}\left(rho, c\right))) \land (\forall X \in \operatorname{Subspace}\left(\mathbb{C}^{n}\right),\; \forall Z \in \operatorname{Subspace}\left(\mathbb{C}^{n}\right),\; (\operatorname{d}\left(rho, c, X, Z\right) = 0) \iff (X = Z))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/BornJaccardTracialClassification.tracial_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let n be any integer at least two, H the usual complex Euclidean space of dimension n, rho any positive-definite Hermitian matrix of trace one, and c any nonnegative real number. All subspaces, projections and traces use this same H and rho. Write P(X) for the ordinary orthogonal projection onto X, mu(X)=Re Tr(rho P(X)), and f(X)=c+mu(X). The trace pairing is real. Join is the actual linear sum and meet is intersection. The distance d(X,Z) is 1-f(X intersect Z)/f(X+Z) whenever its denominator is nonzero, and zero when the denominator vanishes. Faithfulness makes this last case exactly c=0 and X=Z=0.

The displayed Tri means the triangle inequality for every ordered triple of actual subspaces. The displayed Metric means that a MetricSpace structure exists on this full subspace type whose real distance is exactly d. It includes symmetry, nonnegativity and the zero diagonal. The final conjunct states separation for every faithful rho, including nonscalar rho. Coincident subspaces and all triples containing zero remain in scope.

For the scalar state, the projection trace theorem gives mu(X)=dim(X)/n. Dimension is monotone and modular. The positive-offset triangle bound directly applies BadicaJaccardArbitraryLattices.result; modularity supplies its log-submodularity hypothesis. Taking the right limit of positive offsets proves the zero-offset bound for each fixed triple. For a zero join the approximating distances are identically zero.

A nonscalar Hermitian operator has unequal eigenvalues M>m>0 on orthonormal vectors e and f. The actual lines spanned by 2e+f and 2e-f have zero intersection and join span(e,f). Their common weight is (4M+m)/5 and their join has weight M+m. With the join as the middle subspace their triangle defect is 3(M-m)/(5(c+M+m)), strictly positive for every allowed c. The spectral theorem and trace one then give rho=I/n as the only all-triple case.

For separation, the difference of projections onto two strictly nested subspaces is an orthogonal projection onto a nonzero subspace. Its trace pairing with a faithful state is positive, so mu is strictly monotone. Equality of the meet and join weights therefore forces the two subspaces to coincide. These arguments formalize the tracial classification application in Corollary 4.1 of Born-weighted Jaccard projection geometry. They make no literature originality claim and do not include the separate sharp interval supremum or nonattainment assertions. All statements are general parameterized theorems, rather than finite computations or certified numerical instances.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/BornJaccardTracialClassification.tracial_classification`
- Dependency: [D5/S3/Combinatorics/Lattices/BadicaJaccardArbitraryLattices](../../Combinatorics/Lattices/BadicaJaccardArbitraryLattices.md)
