# Theta graph structure and metric dimension

## Abstract

Theta graph structure and metric dimension.

**Definition 1.1 (Distance representation).**

$$\forall n: \operatorname{Nat}, \forall G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right), \forall S: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right), \forall v: \operatorname{Fin}\left(n\right), \operatorname{distanceRepresentation}\left(G, S, v\right) = \lambda (s: S) \mapsto (G).\operatorname{dist}\left(v, (s).\operatorname{val}\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaStructure.distanceRepresentation` (`✓ std3`).

*Citation.* Monther Rashed Alfuraidan, Suliman Khan, Lorenzo Sauras-Altuzarra (2026). *Metric dimension and maximum eigenvalue multiplicity of graph Laplacians*. DOI: [10.48550/arXiv.2610.26875](https://doi.org/10.48550/arXiv.2610.26875). URL: <https://arxiv.org/abs/2610.26875v1>.

*Commentary.*

Metric dimension (p. 3): “Let S={s_1,…,s_t}⊆ V(G). The distance representation of a vertex v∈ V(G) with respect to S is defined by r(v|S)= (d(v,s_1),…,d(v,s_t)). The set S is called a resolving set if r(u|S)≠ r(v|S) for all distinct vertices u,v∈ V(G). The metric dimension of G, denoted by dim(G), is the minimum cardinality of a resolving set.” The landmark set is a Finset; its subtype indexes the coordinates.

**Definition 1.2 (Resolving sets).**

$$\forall n: \operatorname{Nat}, \forall G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right), \forall S: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right), \operatorname{ResolvingSet}\left(G, S\right) = \forall u: \operatorname{Fin}\left(n\right), \forall v: \operatorname{Fin}\left(n\right), (\operatorname{distanceRepresentation}\left(G, S, u\right) = \operatorname{distanceRepresentation}\left(G, S, v\right)) \Rightarrow (u = v)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaStructure.ResolvingSet` (`✓ std3`).

*Citation.* Monther Rashed Alfuraidan, Suliman Khan, Lorenzo Sauras-Altuzarra (2026). *Metric dimension and maximum eigenvalue multiplicity of graph Laplacians*. DOI: [10.48550/arXiv.2610.26875](https://doi.org/10.48550/arXiv.2610.26875). URL: <https://arxiv.org/abs/2610.26875v1>.

*Commentary.*

Metric dimension (p. 3): “Let S={s_1,…,s_t}⊆ V(G). The distance representation of a vertex v∈ V(G) with respect to S is defined by r(v|S)= (d(v,s_1),…,d(v,s_t)). The set S is called a resolving set if r(u|S)≠ r(v|S) for all distinct vertices u,v∈ V(G). The metric dimension of G, denoted by dim(G), is the minimum cardinality of a resolving set.” Equality of the coordinate functions gives the equivalent injectivity formulation.

**Definition 1.3 (Metric dimension).**

$$\forall n: \operatorname{Nat}, \forall G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right), \operatorname{metricDimension}\left(G\right) = \operatorname{sInf}\left(\{ m: \operatorname{Nat} \mid \exists S: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right), (\operatorname{ResolvingSet}\left(G, S\right)) \land ((S).\operatorname{card} = m) \}\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaStructure.metricDimension` (`✓ std3`).

*Citation.* Monther Rashed Alfuraidan, Suliman Khan, Lorenzo Sauras-Altuzarra (2026). *Metric dimension and maximum eigenvalue multiplicity of graph Laplacians*. DOI: [10.48550/arXiv.2610.26875](https://doi.org/10.48550/arXiv.2610.26875). URL: <https://arxiv.org/abs/2610.26875v1>.

*Commentary.*

Metric dimension (p. 3): “Let S={s_1,…,s_t}⊆ V(G). The distance representation of a vertex v∈ V(G) with respect to S is defined by r(v|S)= (d(v,s_1),…,d(v,s_t)). The set S is called a resolving set if r(u|S)≠ r(v|S) for all distinct vertices u,v∈ V(G). The metric dimension of G, denoted by dim(G), is the minimum cardinality of a resolving set.” The infimum is taken in Nat.

**Definition 1.4 (Both kinds of twins).**

$$\forall n: \operatorname{Nat}, \forall G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right), \forall u: \operatorname{Fin}\left(n\right), \forall v: \operatorname{Fin}\left(n\right), \operatorname{Twins}\left(G, u, v\right) = \left((u \ne v) \land ((G).\operatorname{neighborSet}\left(u\right) \setminus \left\{v\right\} = (G).\operatorname{neighborSet}\left(v\right) \setminus \left\{u\right\})\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaStructure.Twins` (`✓ std3`).

*Citation.* Monther Rashed Alfuraidan, Suliman Khan, Lorenzo Sauras-Altuzarra (2026). *Metric dimension and maximum eigenvalue multiplicity of graph Laplacians*. DOI: [10.48550/arXiv.2610.26875](https://doi.org/10.48550/arXiv.2610.26875). URL: <https://arxiv.org/abs/2610.26875v1>.

*Commentary.*

Twins (p. 4): “Two distinct vertices u,v∈ V(G) are called twins if N(u)∖{v}=N(v)∖{u}. They are called false twins if uv∉ E(G), equivalently N(u)=N(v), and true twins if uv∈ E(G), equivalently N[u]=N[v]. The twin relation, together with equality, is an equivalence relation on V(G). Its equivalence classes are called twin classes. A twin class is nontrivial when it contains at least two vertices. The vertices of each such class form either an independent set (a false twin class) or a clique (a true twin class). A graph is twin-free when it has no nontrivial twin classes; the twin relation is a relation between vertices.” The condition includes adjacent and nonadjacent vertices.

**Definition 1.5 (Twin-free graphs).**

$$\forall n: \operatorname{Nat}, \forall G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right), \operatorname{TwinFree}\left(G\right) = \forall u: \operatorname{Fin}\left(n\right), \forall v: \operatorname{Fin}\left(n\right), \neg (\operatorname{Twins}\left(G, u, v\right))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaStructure.TwinFree` (`✓ std3`).

*Citation.* Monther Rashed Alfuraidan, Suliman Khan, Lorenzo Sauras-Altuzarra (2026). *Metric dimension and maximum eigenvalue multiplicity of graph Laplacians*. DOI: [10.48550/arXiv.2610.26875](https://doi.org/10.48550/arXiv.2610.26875). URL: <https://arxiv.org/abs/2610.26875v1>.

*Commentary.*

Twins (p. 4): “Two distinct vertices u,v∈ V(G) are called twins if N(u)∖{v}=N(v)∖{u}. They are called false twins if uv∉ E(G), equivalently N(u)=N(v), and true twins if uv∈ E(G), equivalently N[u]=N[v]. The twin relation, together with equality, is an equivalence relation on V(G). Its equivalence classes are called twin classes. A twin class is nontrivial when it contains at least two vertices. The vertices of each such class form either an independent set (a false twin class) or a clique (a true twin class). A graph is twin-free when it has no nontrivial twin classes; the twin relation is a relation between vertices.”

**Definition 1.6 (Geometric multiplicity).**

$$\forall n: \operatorname{Nat}, \forall M: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \operatorname{Real}\right), \forall lambda: \operatorname{Real}, \operatorname{multiplicity}\left(M, lambda\right) = \operatorname{Module}.\operatorname{finrank}\left(\operatorname{Real}, \operatorname{Module}.\operatorname{End}.\operatorname{eigenspace}\left(\operatorname{Matrix}.\operatorname{toLin'}\left(M\right), lambda\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaStructure.multiplicity` (`✓ std3`).

*Citation.* Monther Rashed Alfuraidan, Suliman Khan, Lorenzo Sauras-Altuzarra (2026). *Metric dimension and maximum eigenvalue multiplicity of graph Laplacians*. DOI: [10.48550/arXiv.2610.26875](https://doi.org/10.48550/arXiv.2610.26875). URL: <https://arxiv.org/abs/2610.26875v1>.

*Commentary.*

Spectral multiplicity (p. 3): “For a real symmetric matrix M, Spec(M) is its multiset of eigenvalues, and mult_M(λ)=dim ker(M-λ I) is the multiplicity of a real number λ. It is zero when λ is not an eigenvalue. The notation λ^{(a)} in a spectrum records a copies of λ. An eigenvalue is simple when its multiplicity is one, and a spectrum is simple when every eigenvalue is simple. The nullity of a matrix is the dimension of its kernel. We write I_n for the identity matrix, M^T for the transpose, diag(a_1,…,a_n) for a diagonal matrix, and χ_M(z)=det(zI-M) for the characteristic polynomial; the order of an unsubscripted I is determined by M.” Matrix.toLin' supplies the linear operator.

**Definition 1.7 (Maximum over all eigenvalues).**

$$\forall n: \operatorname{Nat}, \forall M: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \operatorname{Real}\right), \operatorname{maximumMultiplicity}\left(M\right) = \operatorname{sSup}\left(\{ m: \operatorname{Nat} \mid \exists lambda: \operatorname{Real}, (\operatorname{Module}.\operatorname{End}.\operatorname{HasEigenvalue}\left(\operatorname{Matrix}.\operatorname{toLin'}\left(M\right), lambda\right)) \land (m = \operatorname{multiplicity}\left(M, lambda\right)) \}\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaStructure.maximumMultiplicity` (`✓ std3`).

*Citation.* Monther Rashed Alfuraidan, Suliman Khan, Lorenzo Sauras-Altuzarra (2026). *Metric dimension and maximum eigenvalue multiplicity of graph Laplacians*. DOI: [10.48550/arXiv.2610.26875](https://doi.org/10.48550/arXiv.2610.26875). URL: <https://arxiv.org/abs/2610.26875v1>.

*Commentary.*

Maximum multiplicity (pp. 1–2): “For each choice X∈{L,Q}, define the maximum multiplicity (abbreviated mm_X) by mm_X(G)= max_{λ∈Spec(X(G))} mult_{X(G)}(λ). Here mult_{X(G)}(λ) is the dimension of the eigenspace at λ. We maximize the multiplicity over all eigenvalues, rather than taking the multiplicity of the largest eigenvalue.” The supremum is over the natural eigenspace dimensions at real eigenvalues.

**Definition 1.8 (Laplacian maximum multiplicity).**

$$\forall n: \operatorname{Nat}, \forall G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right), \operatorname{mmL}\left(G\right) = \operatorname{maximumMultiplicity}\left((G).\operatorname{lapMatrix}\left(\operatorname{Real}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaStructure.mmL` (`✓ std3`).

*Citation.* Monther Rashed Alfuraidan, Suliman Khan, Lorenzo Sauras-Altuzarra (2026). *Metric dimension and maximum eigenvalue multiplicity of graph Laplacians*. DOI: [10.48550/arXiv.2610.26875](https://doi.org/10.48550/arXiv.2610.26875). URL: <https://arxiv.org/abs/2610.26875v1>.

*Commentary.*

Laplacians (p. 4): “The adjacency matrix, degree matrix, Laplacian matrix, and signless Laplacian matrix of a graph G are denoted by A(G), D(G), L(G), and Q(G), respectively, where L(G)=D(G)-A(G), Q(G)=D(G)+A(G). The signless Laplacian matrix and its basic spectral properties are discussed in~\cite{Cvetkovic2007}. Thus mm_L(G) is the largest multiplicity attained by any eigenvalue of L(G), and mm_Q(G) is defined analogously for Q(G). Neither notation denotes the multiplicity of the largest eigenvalue. Empty indexed families are omitted when taking a maximum.”

**Definition 1.9 (Signless Laplacian).**

$$\forall n: \operatorname{Nat}, \forall G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right), \operatorname{signlessLaplacian}\left(G\right) = (G).\operatorname{degMatrix}\left(\operatorname{Real}\right) + (G).\operatorname{adjMatrix}\left(\operatorname{Real}\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaStructure.signlessLaplacian` (`✓ std3`).

*Citation.* Monther Rashed Alfuraidan, Suliman Khan, Lorenzo Sauras-Altuzarra (2026). *Metric dimension and maximum eigenvalue multiplicity of graph Laplacians*. DOI: [10.48550/arXiv.2610.26875](https://doi.org/10.48550/arXiv.2610.26875). URL: <https://arxiv.org/abs/2610.26875v1>.

*Commentary.*

Laplacians (p. 4): “The adjacency matrix, degree matrix, Laplacian matrix, and signless Laplacian matrix of a graph G are denoted by A(G), D(G), L(G), and Q(G), respectively, where L(G)=D(G)-A(G), Q(G)=D(G)+A(G). The signless Laplacian matrix and its basic spectral properties are discussed in~\cite{Cvetkovic2007}. Thus mm_L(G) is the largest multiplicity attained by any eigenvalue of L(G), and mm_Q(G) is defined analogously for Q(G). Neither notation denotes the multiplicity of the largest eigenvalue. Empty indexed families are omitted when taking a maximum.” The signless matrix is D(G)+A(G).

**Definition 1.10 (Signless maximum multiplicity).**

$$\forall n: \operatorname{Nat}, \forall G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right), \operatorname{mmQ}\left(G\right) = \operatorname{maximumMultiplicity}\left(\operatorname{signlessLaplacian}\left(G\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaStructure.mmQ` (`✓ std3`).

*Citation.* Monther Rashed Alfuraidan, Suliman Khan, Lorenzo Sauras-Altuzarra (2026). *Metric dimension and maximum eigenvalue multiplicity of graph Laplacians*. DOI: [10.48550/arXiv.2610.26875](https://doi.org/10.48550/arXiv.2610.26875). URL: <https://arxiv.org/abs/2610.26875v1>.

*Commentary.*

Laplacians (p. 4): “The adjacency matrix, degree matrix, Laplacian matrix, and signless Laplacian matrix of a graph G are denoted by A(G), D(G), L(G), and Q(G), respectively, where L(G)=D(G)-A(G), Q(G)=D(G)+A(G). The signless Laplacian matrix and its basic spectral properties are discussed in~\cite{Cvetkovic2007}. Thus mm_L(G) is the largest multiplicity attained by any eigenvalue of L(G), and mm_Q(G) is defined analogously for Q(G). Neither notation denotes the multiplicity of the largest eigenvalue. Empty indexed families are omitted when taking a maximum.” The signless matrix is D(G)+A(G).

**Definition 1.11 (Oriented theta edges).**

$$\forall r: \operatorname{Nat}, \forall x: \operatorname{Nat}, \forall y: \operatorname{Nat}, \operatorname{thetaEdge}\left(r, x, y\right) = \left(((x = 0) \land (y = 2)) \lor (((x = 2) \land (y = 3)) \lor (((x = 3) \land (y = 1)) \lor (((x = 0) \land (y = 4)) \lor (((x = 4) \land (y = 5)) \lor (((x = 5) \land (y = 1)) \lor (((x = 0) \land (y = 6)) \lor (((x = r + 4) \land (y = 1)) \lor ((6 \le x) \land (y = x + 1)))))))))\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaStructure.thetaEdge` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Monther Rashed Alfuraidan, Suliman Khan, Lorenzo Sauras-Altuzarra (2026). *Metric dimension and maximum eigenvalue multiplicity of graph Laplacians*. DOI: [10.48550/arXiv.2610.26875](https://doi.org/10.48550/arXiv.2610.26875). URL: <https://arxiv.org/abs/2610.26875v1>.

*Commentary.*

The labels 0 and 1 are the terminals. The two three-edge paths have internal labels 2,3 and 4,5; the long path has internal labels 6 through r+4.

**Definition 1.12 (The theta graph).**

$$\forall r: \operatorname{Nat}, \forall h: 2 \le r, \forall x: \operatorname{Fin}\left(r + 5\right), \forall y: \operatorname{Fin}\left(r + 5\right), ((\operatorname{thetaGraph}\left(r, h\right)).\operatorname{Adj}\left(x, y\right)) \Leftrightarrow ((\operatorname{thetaEdge}\left(r, \operatorname{val}\left(x\right), \operatorname{val}\left(y\right)\right)) \lor (\operatorname{thetaEdge}\left(r, \operatorname{val}\left(y\right), \operatorname{val}\left(x\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaStructure.thetaGraph` (`✓ std3`).

*Citation.* Monther Rashed Alfuraidan, Suliman Khan, Lorenzo Sauras-Altuzarra (2026). *Metric dimension and maximum eigenvalue multiplicity of graph Laplacians*. DOI: [10.48550/arXiv.2610.26875](https://doi.org/10.48550/arXiv.2610.26875). URL: <https://arxiv.org/abs/2610.26875v1>.

*Commentary.*

Theta parameters (p. 24): “For every p,q,r∈Z_{≥2}, construct Θ_{p,q,r} from three paths with p,q,r edges, respectively, by identifying their three initial vertices as one vertex u and their three terminal vertices as one distinct vertex v. No other vertices are identified, and no additional edges are added. Thus the paths have exactly the two endpoints in common.” Here p=q=3, parameters count edges, and the graph has r+5 vertices.

**Theorem 1.13 (Adjacency of the theta graph).**

$$\forall r: \operatorname{Nat}, \forall h: 2 \le r, \forall x: \operatorname{Fin}\left(r + 5\right), \forall y: \operatorname{Fin}\left(r + 5\right), ((\operatorname{thetaGraph}\left(r, h\right)).\operatorname{Adj}\left(x, y\right)) \Leftrightarrow ((\operatorname{thetaEdge}\left(r, \operatorname{val}\left(x\right), \operatorname{val}\left(y\right)\right)) \lor (\operatorname{thetaEdge}\left(r, \operatorname{val}\left(y\right), \operatorname{val}\left(x\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaStructure.theta_adj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Monther Rashed Alfuraidan, Suliman Khan, Lorenzo Sauras-Altuzarra (2026). *Metric dimension and maximum eigenvalue multiplicity of graph Laplacians*. DOI: [10.48550/arXiv.2610.26875](https://doi.org/10.48550/arXiv.2610.26875). URL: <https://arxiv.org/abs/2610.26875v1>.

*Commentary.*

Adjacency is the symmetric closure of the displayed edge predicate.

**Theorem 1.14 (Connected twin-free graphs of metric dimension two).**

$$\forall k: \operatorname{Nat}, (1 \le k) \Rightarrow (((\operatorname{thetaGraph}\left(6 \cdot k + 4, \operatorname{by} \operatorname{omega}\right)).\operatorname{Connected}) \land ((\operatorname{TwinFree}\left(\operatorname{thetaGraph}\left(6 \cdot k + 4, \operatorname{by} \operatorname{omega}\right)\right)) \land (\operatorname{metricDimension}\left(\operatorname{thetaGraph}\left(6 \cdot k + 4, \operatorname{by} \operatorname{omega}\right)\right) = 2)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaStructure.theta_metric_certificates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Monther Rashed Alfuraidan, Suliman Khan, Lorenzo Sauras-Altuzarra (2026). *Metric dimension and maximum eigenvalue multiplicity of graph Laplacians*. DOI: [10.48550/arXiv.2610.26875](https://doi.org/10.48550/arXiv.2610.26875). URL: <https://arxiv.org/abs/2610.26875v1>.

*Commentary.*

The landmarks with graph labels 2 and 6 have distinct distance profiles at every vertex. No empty or singleton landmark set resolves the graph. The long-path length is 6k+4.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaStructure.ResolvingSet`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaStructure.TwinFree`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaStructure.Twins`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaStructure.distanceRepresentation`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaStructure.maximumMultiplicity`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaStructure.metricDimension`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaStructure.mmL`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaStructure.mmQ`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaStructure.multiplicity`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaStructure.signlessLaplacian`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaStructure.thetaEdge`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaStructure.thetaGraph`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaStructure.theta_adj`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaStructure.theta_metric_certificates`
- Dependency: [D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct](../Graph/WellCoveredPowerCliqueProduct.md)
