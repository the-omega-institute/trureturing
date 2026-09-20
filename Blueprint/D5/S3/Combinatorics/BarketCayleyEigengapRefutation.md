# A Five-Cycle Central-Quotient Counterexample

## Abstract

The normalised-Laplacian eigengap conjecture fails on the Cayley 5-cycle.

**Definition 1.1 (The normalised Laplacian).**

$$\forall V \in \mathrm{Type},\; (\operatorname{Fintype}\left(V\right)) \Rightarrow ((\operatorname{DecidableEq}\left(V\right)) \Rightarrow (\forall Gamma \in \operatorname{SimpleGraph}\left(V\right),\; (\operatorname{DecidableRel}\left(\operatorname{Adj}\left(Gamma\right)\right)) \Rightarrow (\forall i \in V,\; \forall j \in V,\; \operatorname{entry}\left(\operatorname{normalizedLaplacian}\left(Gamma\right), i, j\right) = \frac{\operatorname{entry}\left(\operatorname{lapMatrix}\left(Gamma\right), i, j\right)}{\operatorname{sqrt}\left(\operatorname{degree}\left(Gamma, i\right)\right) \cdot \operatorname{sqrt}\left(\operatorname{degree}\left(Gamma, j\right)\right)})))$$

*Formalization.* `D5/S3/Combinatorics/BarketCayleyEigengapRefutation.normalizedLaplacian` (`✓ std3`).

*Citation.* Rashid Barket, Enrico Grimaldi, Yacoub Hendi, Edward Hirst, Adam Onus, Harmeet Singh (2026). *Learning the Graphical Nature of Symmetries*. DOI: [10.48550/arXiv.2607.12026](https://doi.org/10.48550/arXiv.2607.12026). URL: <https://arxiv.org/abs/2607.12026v1>.

*Commentary.*

For a finite simple graph, lapMatrix is L=D-A. Division is in the real numbers, entry by entry. The paper writes: "L_N = D^{−1/2} L D^{−1/2} = I − D^{−1/2} A D^{−1/2}, (4.9)".

**Definition 1.2 (Classical adjacency selection).**

$$\forall V \in \mathrm{Type},\; (\operatorname{Fintype}\left(V\right)) \Rightarrow ((\operatorname{DecidableEq}\left(V\right)) \Rightarrow (\forall Gamma \in \operatorname{SimpleGraph}\left(V\right),\; \operatorname{normalizedLaplacianClassical}\left(Gamma\right) = \operatorname{normalizedLaplacian}\left(Gamma, Classical.decRel\left(\operatorname{Adj}\left(Gamma\right)\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/BarketCayleyEigengapRefutation.normalizedLaplacianClassical` (`✓ std3`).

*Citation.* Rashid Barket, Enrico Grimaldi, Yacoub Hendi, Edward Hirst, Adam Onus, Harmeet Singh (2026). *Learning the Graphical Nature of Symmetries*. DOI: [10.48550/arXiv.2607.12026](https://doi.org/10.48550/arXiv.2607.12026). URL: <https://arxiv.org/abs/2607.12026v1>.

*Commentary.*

Every adjacency proposition has a classical decision procedure. Selecting it supplies the implementation structure required by lapMatrix and degree; proof irrelevance makes the resulting matrix independent of that choice.

**Definition 1.3 (The ascending characteristic spectrum).**

$$\forall V \in \mathrm{Type},\; (\operatorname{Fintype}\left(V\right)) \Rightarrow ((\operatorname{DecidableEq}\left(V\right)) \Rightarrow (\forall M \in \operatorname{Matrix}\left(V, V, \mathrm{Real}\right),\; \operatorname{sortedSpectrum}\left(M\right) = Multiset.sort\left(\operatorname{roots}\left(\operatorname{charpoly}\left(M\right)\right), (\mathord{\cdot} \le \mathord{\cdot})\right)))$$

*Formalization.* `D5/S3/Combinatorics/BarketCayleyEigengapRefutation.sortedSpectrum` (`✓ std3`).

*Citation.* Rashid Barket, Enrico Grimaldi, Yacoub Hendi, Edward Hirst, Adam Onus, Harmeet Singh (2026). *Learning the Graphical Nature of Symmetries*. DOI: [10.48550/arXiv.2607.12026](https://doi.org/10.48550/arXiv.2607.12026). URL: <https://arxiv.org/abs/2607.12026v1>.

*Commentary.*

The characteristic-polynomial roots are taken with multiplicity and sorted ascending. For a normalised Laplacian the matrix is real symmetric, so all roots are real and this list is its complete spectrum.

**Definition 1.4 (One-indexed spectral access).**

$$\forall l \in \operatorname{List}\left(\mathrm{Real}\right),\; \forall i \in \mathrm{Nat},\; \operatorname{eig}\left(l, i\right) = \operatorname{getD}\left(l, i - 1, 0\right)$$

*Formalization.* `D5/S3/Combinatorics/BarketCayleyEigengapRefutation.eig` (`✓ std3`).

*Citation.* Rashid Barket, Enrico Grimaldi, Yacoub Hendi, Edward Hirst, Adam Onus, Harmeet Singh (2026). *Learning the Graphical Nature of Symmetries*. DOI: [10.48550/arXiv.2607.12026](https://doi.org/10.48550/arXiv.2607.12026). URL: <https://arxiv.org/abs/2607.12026v1>.

*Commentary.*

The index is one-based. getD reads position i-1 and returns zero outside the list; the conjecture only uses indices from one through card(G)-1.

**Definition 1.5 (Indices of gaps above one).**

$$\forall G \in \mathrm{Type},\; (\operatorname{Group}\left(G\right)) \Rightarrow ((\operatorname{Fintype}\left(G\right)) \Rightarrow ((\operatorname{DecidableEq}\left(G\right)) \Rightarrow (\forall S \in \operatorname{Finset}\left(G\right),\; \operatorname{conjectureGapSet}\left(S\right) = \{i \mid (1 \le i) \land ((i \le \operatorname{FintypeCard}\left(G\right) - 1) \land (\operatorname{eig}\left(\operatorname{sortedSpectrum}\left(\operatorname{normalizedLaplacianClassical}\left(\operatorname{mulCayley}\left(\operatorname{asSet}\left(S\right)\right)\right)\right), i + 1\right) - \operatorname{eig}\left(\operatorname{sortedSpectrum}\left(\operatorname{normalizedLaplacianClassical}\left(\operatorname{mulCayley}\left(\operatorname{asSet}\left(S\right)\right)\right)\right), i\right) > 1))\})))$$

*Formalization.* `D5/S3/Combinatorics/BarketCayleyEigengapRefutation.conjectureGapSet` (`✓ std3`).

*Citation.* Rashid Barket, Enrico Grimaldi, Yacoub Hendi, Edward Hirst, Adam Onus, Harmeet Singh (2026). *Learning the Graphical Nature of Symmetries*. DOI: [10.48550/arXiv.2607.12026](https://doi.org/10.48550/arXiv.2607.12026). URL: <https://arxiv.org/abs/2607.12026v1>.

*Commentary.*

The graph is the underlying undirected multiplicative Cayley graph. The paper writes: "given the sorted spectrum of L_N, define the consecutive eigengaps δᵢ = λ_{i+1} − λᵢ for i = 1, …, n − 1" and "k_τ = min{i : δᵢ > τ}", with τ = 1.0.

**Definition 1.6 (Conjecture 4.4 as printed).**

$$(claim) \Leftrightarrow (\forall G \in \mathrm{Type},\; (\operatorname{Group}\left(G\right)) \Rightarrow ((\operatorname{Fintype}\left(G\right)) \Rightarrow ((\operatorname{DecidableEq}\left(G\right)) \Rightarrow ((\operatorname{IsNilpotent}\left(G\right)) \Rightarrow (\forall S \in \operatorname{Finset}\left(G\right),\; (\operatorname{closure}\left(\operatorname{asSet}\left(S\right)\right) = \operatorname{top}\left(G\right)) \Rightarrow (\forall k \in \mathrm{Nat},\; (\operatorname{IsLeast}\left(\operatorname{conjectureGapSet}\left(S\right), k\right)) \Rightarrow ((k = \operatorname{FintypeCard}\left(G\right) - 1) \lor (\exists j \in \mathrm{Nat},\; (1 \le j) \land ((j \le \operatorname{nilpotencyClass}\left(G\right)) \land (k = \operatorname{NatCard}\left(\operatorname{quotient}\left(G, \operatorname{upperCentralSeries}\left(G, j\right)\right)\right)))))))))))$$

*Formalization.* `D5/S3/Combinatorics/BarketCayleyEigengapRefutation.claim` (`✓ std3`).

*Citation.* Rashid Barket, Enrico Grimaldi, Yacoub Hendi, Edward Hirst, Adam Onus, Harmeet Singh (2026). *Learning the Graphical Nature of Symmetries*. DOI: [10.48550/arXiv.2607.12026](https://doi.org/10.48550/arXiv.2607.12026). URL: <https://arxiv.org/abs/2607.12026v1>.

*Commentary.*

The paper states: "Conjecture 4.4 (Central-quotient eigengaps). Let G be a finite nilpotent group with upper central series 1 = Z₀(G) ≤ Z₁(G) ≤ · · · ≤ Z_c(G) = G, and let Γ = Cay(G, S) be the underlying undirected Cayley graph associated to a chosen generating set S. If k_{>1} = min{i : λ_{i+1} − λ_i > 1} is defined for the normalised Laplacian spectrum of Γ, then either k_{>1} = |G| − 1, or k_{>1} = |G/Z_j(G)| for some 1 ≤ j ≤ c." The DecidableEq binder is implementation structure, classically available for every type.

**Theorem 1.7 (The central-quotient eigengap conjecture is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BarketCayleyEigengapRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/barket-central-quotient-eigengap-conjecture-refutation` (refuted) by `D5/S3/Combinatorics/BarketCayleyEigengapRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"barket-central-quotient-eigengap-conjecture-refutation","declaration_gid":"D5/S3/Combinatorics/BarketCayleyEigengapRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

For G=Z/5 and S={1}, the Cayley graph is the 5-cycle. Its normalised Laplacian has characteristic polynomial X(X^2-(5/2)X+5/4)^2 and ascending spectrum [0,a,a,b,b], where a=(5-sqrt(5))/4 and b=(5+sqrt(5))/4. The consecutive gaps are [a,0,sqrt(5)/2,0], so the first gap above one has index three. The final index is four, while the only central quotient allowed by nilpotency class one has cardinality one.

## References

- Truth anchor: `D5/S3/Combinatorics/BarketCayleyEigengapRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/BarketCayleyEigengapRefutation.conjectureGapSet`
- Truth anchor: `D5/S3/Combinatorics/BarketCayleyEigengapRefutation.eig`
- Truth anchor: `D5/S3/Combinatorics/BarketCayleyEigengapRefutation.normalizedLaplacian`
- Truth anchor: `D5/S3/Combinatorics/BarketCayleyEigengapRefutation.normalizedLaplacianClassical`
- Truth anchor: `D5/S3/Combinatorics/BarketCayleyEigengapRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/BarketCayleyEigengapRefutation.sortedSpectrum`
