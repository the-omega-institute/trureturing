# The ordered connected forcing crossing is false

## Abstract

The four-vertex path followed by the four-vertex star refutes the fixed ordered crossing in Problem 5.3: their size-one connected zero forcing counts are two and zero.

**Definition 1.1 (Initial connectivity and ordinary forcing).**

$$\forall (V : Type), \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (S : \operatorname{Finset}\left(V\right)), (\operatorname{connectedForcing}\left(G, S\right)) \Leftrightarrow ((\operatorname{Connected}\left(\operatorname{induce}\left(G, (S : \operatorname{Set}\left(V\right))\right)\right)) \land (\operatorname{IsZeroForcing}\left(G, (S : \operatorname{Set}\left(V\right))\right)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroForcing/ConnectedForcingCrossingRefutation.connectedForcing` (`✓ std3`).

*Citation.* Sanjay Mukherjee; Papi Ray (2026). *On the connected zero forcing polynomial of finite trees*. DOI: [10.48550/arXiv.2611.10985](https://doi.org/10.48550/arXiv.2611.10985). URL: <https://arxiv.org/abs/2611.10985v1>.

*Commentary.*

The induced graph on the initial subset must be connected, and its ordinary Black closure must contain every vertex. Connectivity of later colored sets is not an additional rule. Black.force uses a colored source, an adjacent target and colored other neighbors; a derivation targeting an already colored vertex changes no closure membership. The existing chronological equivalence in ContingentThreshold explains the correspondence with a legal sequence of unique-white-neighbor forces.

**Definition 1.2 (Actual vertex-subset coefficients).**

$$\forall (V : Type), [\operatorname{Fintype}\left(V\right)], \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (i : \mathbb{N}), \operatorname{coefficient}\left(G, i\right) = \operatorname{card}\left(\{S : \operatorname{Finset}\left(V\right) \mid (\operatorname{card}\left(S\right) = i) \land (\operatorname{connectedForcing}\left(G, S\right))\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroForcing/ConnectedForcingCrossingRefutation.coefficient` (`✓ std3`).

*Citation.* Sanjay Mukherjee; Papi Ray (2026). *On the connected zero forcing polynomial of finite trees*. DOI: [10.48550/arXiv.2611.10985](https://doi.org/10.48550/arXiv.2611.10985). URL: <https://arxiv.org/abs/2611.10985v1>.

*Commentary.*

Enumerate every finite vertex subset once, retain exactly the subsets of size i satisfying connectedForcing, and take their cardinality. This is a subset count rather than a minimum forcing number, coefficient oracle or hardcoded polynomial. Fintype supplies only the finite carrier enumeration; the predicate retains its mathematical semantics.

**Definition 1.3 (Degree-one vertices).**

$$\forall (V : Type), \forall (G : \operatorname{SimpleGraph}\left(V\right)), \operatorname{leafCount}\left(G\right) = \operatorname{Nat.card}\left(\{v : V \mid \operatorname{Nat.card}\left(\{w : V \mid \operatorname{Adj}\left(G, v, w\right)\}\right) = 1\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroForcing/ConnectedForcingCrossingRefutation.leafCount` (`✓ std3`).

*Citation.* Sanjay Mukherjee; Papi Ray (2026). *On the connected zero forcing polynomial of finite trees*. DOI: [10.48550/arXiv.2611.10985](https://doi.org/10.48550/arXiv.2611.10985). URL: <https://arxiv.org/abs/2611.10985v1>.

*Commentary.*

Count the vertices whose neighbor subtype has cardinality one. For a finite simple graph this is exactly its number of degree-one vertices, including orders where that number is zero. The parameters p and q in the assertion are these actual counts, with no ordering or lower-bound restriction.

**Definition 1.4 (Problem 5.3 with fixed order).**

$$(claim) \Leftrightarrow (\forall (n : \mathbb{N}), \forall (p : \mathbb{N}), \forall (q : \mathbb{N}), \forall (V : Type), \forall (W : Type), [\operatorname{Fintype}\left(V\right)], [\operatorname{Fintype}\left(W\right)], \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (H : \operatorname{SimpleGraph}\left(W\right)), (\operatorname{IsTree}\left(G\right)) \Rightarrow ((\operatorname{IsTree}\left(H\right)) \Rightarrow ((\operatorname{card}\left(V\right) = n) \Rightarrow ((\operatorname{card}\left(W\right) = n) \Rightarrow ((\operatorname{leafCount}\left(G\right) = p) \Rightarrow ((\operatorname{leafCount}\left(H\right) = q) \Rightarrow (\exists (l : \mathbb{Z}), (1 \le l) \land ((l \le (n : \mathbb{Z})) \land (\forall (i : \mathbb{Z}), (((1 \le i) \land (i \le l)) \Rightarrow (\operatorname{coefficient}\left(G, \operatorname{toNat}\left(i\right)\right) \le \operatorname{coefficient}\left(H, \operatorname{toNat}\left(i\right)\right))) \land (((l + 1 \le i) \land (i \le (n : \mathbb{Z}))) \Rightarrow (\operatorname{coefficient}\left(H, \operatorname{toNat}\left(i\right)\right) \le \operatorname{coefficient}\left(G, \operatorname{toNat}\left(i\right)\right))))))))))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroForcing/ConnectedForcingCrossingRefutation.claim` (`✓ std3`).

*Citation.* Sanjay Mukherjee; Papi Ray (2026). *On the connected zero forcing polynomial of finite trees*. DOI: [10.48550/arXiv.2611.10985](https://doi.org/10.48550/arXiv.2611.10985). URL: <https://arxiv.org/abs/2611.10985v1>.

*Commentary.*

Mukherjee and Ray ask: Given two trees T₁∈𝔗ₙ,ₚ₁ and T₂∈𝔗ₙ,ₚ₂, can we always find an integer l, with 1≤l≤n, such that Z_C(T₁,i)≤Z_C(T₂,i) for 1≤i≤l and Z_C(T₁,i)≥Z_C(T₂,i) for l+1≤i≤n? The formula quantifies arbitrary finite carriers and all their tree graphs. Equal leaf counts are permitted. Integer coefficient indices in the two positive ranges are converted by toNat; this preserves their values. No initial exchange of the two trees is allowed by the literal assertion.

**Theorem 1.5 (The singleton obstruction).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ZeroForcing/ConnectedForcingCrossingRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/mukherjee-ray-2026-ordered-connected-forcing-crossing` (refuted) by `D5/S3/Combinatorics/Graph/ZeroForcing/ConnectedForcingCrossingRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mukherjee-ray-2026-ordered-connected-forcing-crossing","declaration_gid":"D5/S3/Combinatorics/Graph/ZeroForcing/ConnectedForcingCrossingRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Sanjay Mukherjee; Papi Ray (2026). *On the connected zero forcing polynomial of finite trees*. DOI: [10.48550/arXiv.2611.10985](https://doi.org/10.48550/arXiv.2611.10985). URL: <https://arxiv.org/abs/2611.10985v1>.

*Commentary.*

Take T₁=P₄ with edges 01,12,23 and T₂=K₁,₃ with edges 01,02,03. Mathlib certifies the path is a tree. The star is connected through its center and has three edges on four vertices, so it too is a tree. Every singleton induces a connected graph. Either path endpoint forces successively along the path; an interior singleton has a disjoint fort and cannot force all vertices. Every star singleton also has a disjoint fort: for the center use the three leaves, and for a leaf use the other two leaves. The imported fort invariant excludes every possible forcing derivation, including the leaf-to-center move followed by a stall. Exhausting the actual singleton subsets yields coefficients two and zero. Every permitted cutoff l includes i=1 in its low segment and would imply 2≤0. Section 4 of the source already prints this pair and its polynomials; no new example or coefficient discovery is asserted. Only the singleton coefficients are needed here. Swapping this particular pair admits cutoff two according to the source polynomials, while universal exchange-permitted, either-direction and leaf-ordered versions remain outside this result. The established source theorems and its separate Problem 5.2 are unaffected.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroForcing/ConnectedForcingCrossingRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroForcing/ConnectedForcingCrossingRefutation.coefficient`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroForcing/ConnectedForcingCrossingRefutation.connectedForcing`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroForcing/ConnectedForcingCrossingRefutation.leafCount`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroForcing/ConnectedForcingCrossingRefutation.result`
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree](../../GeneralizedPetersen/ZeroForcingThree.md)
