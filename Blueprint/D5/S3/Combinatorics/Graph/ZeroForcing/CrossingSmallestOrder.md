# Smallest order of a counterexample to the ordered crossing

## Abstract

The ordered connected forcing crossing of Mukherjee and Ray holds at every order n ≤ 3 and fails at every order n ≥ 4.

**Definition 1.1 (The crossing assertion at a fixed order).**

Lean statement: `D5/S3/Combinatorics/Graph/ZeroForcing/CrossingSmallestOrder.claimAt`

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroForcing/CrossingSmallestOrder.claimAt` (`✓ std3`).

*Citation.* Sanjay Mukherjee; Papi Ray (2026). *On the connected zero forcing polynomial of finite trees*. DOI: [10.48550/arXiv.2611.10985](https://doi.org/10.48550/arXiv.2611.10985). URL: <https://arxiv.org/abs/2611.10985v1>.

*Commentary.*

For a fixed order n: for every two trees T₁, T₂ on n vertices, with any leaf counts, there is an integer l with 1 ≤ l ≤ n such that Z_c(T₁, i) ≤ Z_c(T₂, i) for 1 ≤ i ≤ l and Z_c(T₂, i) ≤ Z_c(T₁, i) for l + 1 ≤ i ≤ n. This is Problem 5.3 of S. Mukherjee and P. Ray, On the connected zero forcing polynomial of finite trees (arXiv:2611.10985), restricted to one order; the full assertion is its conjunction over all orders.

**Theorem 1.2 (Exactly the orders up to three).**

Lean statement: `D5/S3/Combinatorics/Graph/ZeroForcing/CrossingSmallestOrder.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ZeroForcing/CrossingSmallestOrder.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sanjay Mukherjee; Papi Ray (2026). *On the connected zero forcing polynomial of finite trees*. DOI: [10.48550/arXiv.2611.10985](https://doi.org/10.48550/arXiv.2611.10985). URL: <https://arxiv.org/abs/2611.10985v1>.

*Commentary.*

The crossing assertion holds at order n exactly when n ≤ 3. Hence the smallest order of a counterexample is four.

Connected zero forcing coefficients are invariant under graph isomorphism, since an isomorphism carries forcing chains and connected induced subgraphs to forcing chains and connected induced subgraphs. A tree on one, two or three vertices is isomorphic to the path on as many vertices: on three vertices a tree has two edges and every vertex has a neighbour, so one vertex is adjacent to the other two, which are not adjacent. So two trees of order at most three have equal coefficients and l = n is a cutoff; at order zero there are no trees. For n ≥ 4 the path P_n followed by the star K_{1,n−1} has no cutoff, because P_n has two connected forcing sets of size one while the star has none, so the required inequality fails at i = 1 for every l ≥ 1.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroForcing/CrossingSmallestOrder.claimAt`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroForcing/CrossingSmallestOrder.result`
- Dependency: [D5/S3/Combinatorics/Graph/ZeroForcing/StarConnectedForcing](StarConnectedForcing.md)
