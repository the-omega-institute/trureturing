# GHZ Entanglement Across Every Nontrivial Cut

## Abstract

Every nonempty bipartition of the finite GHZ state has rank two and entropy log two.

**Theorem 1.1 (Every nontrivial GHZ cut has two equal Schmidt weights).**

$$\begin{gathered}A \neq \emptyset, B \neq \emptyset \Rightarrow\\{}\operatorname{rank}(C_{GHZ}) = 2 \land\\{}\rho = \frac{1}{2} I_{2} \land\\{}\forall i \in \{0,1\}, \rho_{ii} = \frac{1}{2} \land\\{}S_{A} = \log 2.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GhzBipartitionEntanglement.ghz_entangled_across_every_nontrivial_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two sides of the cut are arbitrary nonempty types. Their all-zero and all-one configurations are therefore distinct, and the GHZ amplitude is supported exactly on the two matching global constant configurations.

The logical coefficient matrix is diagonal with entries inverse square root of two. The proof checks its norm directly and uses the nonzero determinant criterion to obtain matrix rank two.

Multiplying by its conjugate transpose gives one half of the identity. Thus both displayed reduced weights are one half, and direct evaluation of their entropy gives log two. The construction is mathematical and does not assert that zeta data supplies a physical quantum state.

## References

- Truth anchor: `D5/S3/Quantum/GhzBipartitionEntanglement.ghz_entangled_across_every_nontrivial_cut`
