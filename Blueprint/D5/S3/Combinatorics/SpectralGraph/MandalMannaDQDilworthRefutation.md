# A repeated distance-signless eigenvalue in a single vicinal chain

## Abstract

Eight vertices give nonlocal distance-signless multiplicity above vicinal width.

**Definition 1.1 (Recursive vertex carrier).**

$$\begin{aligned}\operatorname{Vertices}\left(\operatorname{List}.\operatorname{nil}\right) = \operatorname{PEmpty}\\\forall a \in \operatorname{Nat},\; \forall rest \in \operatorname{List}\left(\operatorname{Nat}\right),\; \operatorname{Vertices}\left(\operatorname{List}.\operatorname{cons}\left(a, rest\right)\right) = \operatorname{Sum}\left(\operatorname{Vertices}\left(rest\right), \operatorname{Fin}\left(a\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.Vertices` (`✓ std3`).

*Citation.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

Section 1, page 2: “where ∪ denotes disjoint union and the overline denotes graph complementation. They call G = C(α₁,…,αₘ) a 𝒞-graph, and (α₁,…,αₘ) its creation sequence.” The empty carrier is PEmpty. Each new block contributes Fin a on the right of a disjoint sum; the newest block is stored first in the recursive list.

**Definition 1.2 (Complement and disjoint-union recurrence).**

$$\begin{aligned}\operatorname{reverseCGraph}\left(\operatorname{List}.\operatorname{nil}\right) = (\operatorname{Bot}.\operatorname{bot}: \operatorname{SimpleGraph}\left(\operatorname{PEmpty}\right))\\\forall a \in \operatorname{Nat},\; \forall rest \in \operatorname{List}\left(\operatorname{Nat}\right),\; \operatorname{reverseCGraph}\left(\operatorname{List}.\operatorname{cons}\left(a, rest\right)\right) = \operatorname{Compl}.\operatorname{compl}\left(\operatorname{SimpleGraph}.\operatorname{sum}\left(\operatorname{reverseCGraph}\left(rest\right), (\operatorname{Top}.\operatorname{top}: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(a\right)\right))\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.reverseCGraph` (`✓ std3`).

*Citation.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

Section 1, page 2: “where ∪ denotes disjoint union and the overline denotes graph complementation. They call G = C(α₁,…,αₘ) a 𝒞-graph, and (α₁,…,αₘ) its creation sequence.” The empty graph is auxiliary. SimpleGraph.sum is disjoint union; Top.top is the complete graph and Compl.compl complements the entire sum. Thus the first nonempty stage is the complement of the complete first block.

**Definition 1.3 (Chronological creation sequence).**

$$\forall alpha \in \operatorname{List}\left(\operatorname{Nat}\right),\; \operatorname{cGraph}\left(alpha\right) = \operatorname{reverseCGraph}\left(\operatorname{List}.\operatorname{reverse}\left(alpha\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.cGraph` (`✓ std3`).

*Citation.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

Section 1, page 2: “where ∪ denotes disjoint union and the overline denotes graph complementation. They call G = C(α₁,…,αₘ) a 𝒞-graph, and (α₁,…,αₘ) its creation sequence.” Reversing the input once makes alpha chronological while retaining structural recursion on its reverse.

**Definition 1.4 (One-based chronological block index).**

$$\begin{aligned}\forall v \in \operatorname{PEmpty},\; \operatorname{blockIndex}\left(\operatorname{List}.\operatorname{nil}, v\right) = \operatorname{nomatch}\left(v\right)\\\forall a \in \operatorname{Nat},\; \forall rest \in \operatorname{List}\left(\operatorname{Nat}\right),\; \forall v \in \operatorname{Vertices}\left(rest\right),\; \operatorname{blockIndex}\left(\operatorname{List}.\operatorname{cons}\left(a, rest\right), \operatorname{Sum}.\operatorname{inl}\left(v\right)\right) = \operatorname{blockIndex}\left(rest, v\right)\\\forall a \in \operatorname{Nat},\; \forall rest \in \operatorname{List}\left(\operatorname{Nat}\right),\; \forall i \in \operatorname{Fin}\left(a\right),\; \operatorname{blockIndex}\left(\operatorname{List}.\operatorname{cons}\left(a, rest\right), \operatorname{Sum}.\operatorname{inr}\left(i\right)\right) = \operatorname{List}.\operatorname{length}\left(rest\right) + 1\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.blockIndex` (`✓ std3`).

*Citation.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

The creation sequence (α₁,…,αₘ) in Section 1, page 2 indexes blocks from one. An old vertex retains its index; a vertex in the new block has index length rest + 1. The empty case eliminates its impossible vertex.

**Definition 1.5 (Transmission from native distances).**

$$\forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall u \in V,\; \operatorname{transmission}\left(G, u\right) = \sum_{v: V} (\operatorname{SimpleGraph}.\operatorname{dist}\left(G, u, v\right): \operatorname{Real})$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.transmission` (`✓ std3`).

*Citation.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

Section 1, page 1: “The sum of the distances between a vertex v and every other vertex in G is known as the transmission of v and denoted by Tr(v), that is,” followed by the row-sum display. Here the fixed vertex is u and the summation vertex is v, correcting the display's inconsistent dummy names using the preceding sentence. Each natural distance is coerced to Real before summation.

**Definition 1.6 (Distance signless Laplacian).**

$$\forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \operatorname{distanceSignless}\left(G\right) = \operatorname{Matrix}.\operatorname{diagonal}\left(\operatorname{transmission}\left(G\right)\right) + \operatorname{Matrix}.\operatorname{of}\left(\operatorname{fun} (u: V) \mapsto \operatorname{fun} (v: V) \mapsto (\operatorname{SimpleGraph}.\operatorname{dist}\left(G, u, v\right): \operatorname{Real})\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.distanceSignless` (`✓ std3`).

*Citation.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

Section 1, page 1: “D^Q(G) = Tr(G) + D(G)”. The diagonal contains the transmission, and the distance matrix has the native SimpleGraph.dist entries coerced to Real. Fintype and DecidableEq are implicit typeclass parameters.

**Definition 1.7 (Vicinal comparison).**

$$\forall V \in \operatorname{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall u \in V,\; \forall v \in V,\; \operatorname{vicinal}\left(G, u, v\right) = \left(\operatorname{SimpleGraph}.\operatorname{neighborSet}\left(G, u\right) \subseteq \operatorname{insert}\left(v, \operatorname{SimpleGraph}.\operatorname{neighborSet}\left(G, v\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.vicinal` (`✓ std3`).

*Citation.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

Definition 5.1, page 10: “For a graph G, define u ≼ v if N(u) ⊆ N[v] (equivalently, N[u] ⊆ N[v] when u ∼ v, and N(u) ⊆ N(v) when u ≁ v).” The closed neighborhood is insert v (G.neighborSet v).

**Definition 1.8 (Finite cover by vicinal chains).**

$$\forall V \in \operatorname{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall k \in \operatorname{Nat},\; \operatorname{HasChainCover}\left(G, k\right) = \left(\exists c \in V \to \operatorname{Fin}\left(k\right),\; \forall u \in V,\; \forall v \in V,\; c\left(u\right) = c\left(v\right) \Rightarrow \left(\operatorname{vicinal}\left(G, u, v\right) \lor \operatorname{vicinal}\left(G, v, u\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.HasChainCover` (`✓ std3`).

*Citation.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

Definition 5.1, page 10: “A set of vertices pairwise related by ≼ is a chain; a set of pairwise unrelated is an antichain.” A function c assigns each vertex a label in Fin k. Its fibers cover every vertex, and each fiber consists of pairwise comparable vertices. Unused labels are permitted.

**Definition 1.9 (Minimum number of vicinal chains).**

$$\forall V \in \operatorname{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \operatorname{dilworthNumber}\left(G\right) = \operatorname{sInf}\left(\{k: \operatorname{ENat} \mid \exists n \in \operatorname{Nat},\; k = (n: \operatorname{ENat}) \land \operatorname{HasChainCover}\left(G, n\right)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.dilworthNumber` (`✓ std3`).

*Citation.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

Definition 5.1, page 10: “The Dilworth number ∇(G) is the minimum number of chains needed to cover V(G), equivalently (by Dilworth’s theorem) the maximum size of an antichain.” The infimum is in ENat; an empty feasible set has value infinity. On the finite source graphs singleton chains give a finite cover, so this infimum is the ordinary minimum.

**Definition 1.10 (Block-local exceptional eigenvalues).**

$$\forall alpha \in \operatorname{List}\left(\operatorname{Nat}\right),\; \operatorname{localExceptions}\left(alpha\right) = \{theta: \operatorname{Real} \mid \exists i \in \operatorname{Fin}\left(\operatorname{List}.\operatorname{length}\left(alpha\right)\right),\; 2 \le alpha[i] \land \left(\exists v \in \operatorname{Vertices}\left(\operatorname{List}.\operatorname{reverse}\left(alpha\right)\right),\; \operatorname{blockIndex}\left(\operatorname{List}.\operatorname{reverse}\left(alpha\right), v\right) = \operatorname{val}\left(i\right) + 1 \land \left(\left(\operatorname{Odd}\left(\operatorname{val}\left(i\right) + 1\right) \land theta = \operatorname{transmission}\left(\operatorname{cGraph}\left(alpha\right), v\right) - 1\right) \lor \left(\operatorname{Even}\left(\operatorname{val}\left(i\right) + 1\right) \land theta = \operatorname{transmission}\left(\operatorname{cGraph}\left(alpha\right), v\right) - 2\right)\right)\right)\}$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.localExceptions` (`✓ std3`).

*Citation.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

Section 5, page 11: “𝒯^Q(G) = {Trᵢ−1 : i odd, αᵢ≥2} ∪ {Trᵢ−2 : i even, αᵢ≥2}.” A Fin alpha.length index i denotes source block i.val + 1; the block size must be at least two. A representative vertex of that block supplies its transmission. The shifts are subtraction in Real.

**Definition 1.11 (Algebraic eigenvalue multiplicity).**

$$\forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall theta \in \operatorname{Real},\; \operatorname{multiplicity}\left(G, theta\right) = \operatorname{Polynomial}.\operatorname{rootMultiplicity}\left(theta, \operatorname{Matrix}.\operatorname{charpoly}\left(\operatorname{distanceSignless}\left(G\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.multiplicity` (`✓ std3`).

*Citation.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

Conjecture 5.5, page 11 uses mult_{D^Q(G)}(θ). This is Polynomial.rootMultiplicity of theta in the native characteristic polynomial of distanceSignless G. A characteristic polynomial is monic, so its zero-polynomial totalization never enters. Algebraic multiplicity is at least eigenspace dimension, which suffices for the refutation.

**Definition 1.12 (Conjecture 5.5).**

$$\operatorname{claim} = (\forall alpha \in \operatorname{List}\left(\operatorname{Nat}\right),\; 2 \le \operatorname{List}.\operatorname{length}\left(alpha\right) \Rightarrow \left(\operatorname{Even}\left(\operatorname{List}.\operatorname{length}\left(alpha\right)\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(\operatorname{List}.\operatorname{length}\left(alpha\right)\right),\; 0 < alpha[i]\right) \Rightarrow \left(\operatorname{SimpleGraph}.\operatorname{Connected}\left(\operatorname{cGraph}\left(alpha\right)\right) \Rightarrow \left(\forall theta \in \operatorname{Real},\; \operatorname{Module}.\operatorname{End}.\operatorname{HasEigenvalue}\left(\operatorname{Matrix}.\operatorname{toLin}'\left(\operatorname{distanceSignless}\left(\operatorname{cGraph}\left(alpha\right)\right)\right), theta\right) \Rightarrow \left(\left(\neg theta \in \operatorname{localExceptions}\left(alpha\right)\right) \Rightarrow (\operatorname{multiplicity}\left(\operatorname{cGraph}\left(alpha\right), theta\right): \operatorname{ENat}) \le \operatorname{dilworthNumber}\left(\operatorname{cGraph}\left(alpha\right)\right)\right)\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.claim` (`✓ std3`).

*Citation.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

Conjecture 5.5, page 11: “For every connected 𝒞-graph G, every eigenvalue of D^Q(G) not in 𝒯^Q(G) satisfies mult_{D^Q(G)}(θ) ≤ ∇(G).” Section 2, page 3: “Throughout, G is a connected 𝒞-graph on n vertices with creation sequence (α₁,…,αₘ), nᵢ = α₁+⋯+αᵢ, and αₘᵢₙ = min₁≤ᵢ≤ₘ αᵢ and m is even.” Here alpha ranges over positive lists of even length at least two, G is cGraph alpha, theta is real, and the eigenvalue is for Matrix.toLin' of its distance signless matrix. The natural algebraic multiplicity is coerced to ENat for comparison with dilworthNumber.

**Theorem 1.13 (Refutation with eight singleton blocks).**

$$\neg (\forall alpha \in \operatorname{List}\left(\operatorname{Nat}\right),\; 2 \le \operatorname{List}.\operatorname{length}\left(alpha\right) \Rightarrow \left(\operatorname{Even}\left(\operatorname{List}.\operatorname{length}\left(alpha\right)\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(\operatorname{List}.\operatorname{length}\left(alpha\right)\right),\; 0 < alpha[i]\right) \Rightarrow \left(\operatorname{SimpleGraph}.\operatorname{Connected}\left(\operatorname{cGraph}\left(alpha\right)\right) \Rightarrow \left(\forall theta \in \operatorname{Real},\; \operatorname{Module}.\operatorname{End}.\operatorname{HasEigenvalue}\left(\operatorname{Matrix}.\operatorname{toLin}'\left(\operatorname{distanceSignless}\left(\operatorname{cGraph}\left(alpha\right)\right)\right), theta\right) \Rightarrow \left(\left(\neg theta \in \operatorname{localExceptions}\left(alpha\right)\right) \Rightarrow (\operatorname{multiplicity}\left(\operatorname{cGraph}\left(alpha\right), theta\right): \operatorname{ENat}) \le \operatorname{dilworthNumber}\left(\operatorname{cGraph}\left(alpha\right)\right)\right)\right)\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

The source recurrence with eight singleton blocks gives a connected graph with a universal vertex. Its vertices fit in one vicinal chain, and no zero-chain cover exists. Two independent global modes of its distance signless matrix have eigenvalue 8, so its algebraic multiplicity is at least two. All creation blocks have size one, making the local-exception set empty. Consequently this eigenvalue violates the proposed upper bound of one. The proof obtains the two modes from parameterized shifted matrices: their kernel identities hold for every natural R, and independence holds for R ≥ 1. Identification with native recurrence graphs is proved at R = 2 only; the uniform native-graph extension and exact multiplicity two uniformly remain open. The D^L results, local-mode and quotient formulas, and Example 5.4 are not refuted by this witness.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.HasChainCover`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.Vertices`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.blockIndex`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.cGraph`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.dilworthNumber`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.distanceSignless`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.localExceptions`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.multiplicity`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.reverseCGraph`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.transmission`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.vicinal`
