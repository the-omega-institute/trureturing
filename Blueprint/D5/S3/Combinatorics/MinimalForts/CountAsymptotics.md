# All finite residues share convergence

## Abstract

All finite residues share convergence

**Theorem 1.1 (Normalization of all actual minimal forts).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/CountAsymptotics.mixed_count_normalization`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MinimalForts/CountAsymptotics.mixed_count_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

For each r in Fin 6 and arbitrary natural-valued sequences x,y,z whose sum is k at every index, if the actual signed logarithmic error x log(2/3)+z log(4/3)-k slope-offset(r) tends to zero, then the complete minimal-fort count of MixedBlocks.graph(x(k),y(k),z(k),r), divided by (3/2)^(6k+r+3), tends to one. The count is the cardinality of the entire family of inclusion-minimal nonempty forts of that graph. Its root-containing term is the exponential of the error after normalization. Its nonnegative root-free term is bounded by 15k+choose(r+2,2), and is negligible relative to the exponential denominator. The theorem assumes the sequence error, not a graph count or its asymptotic consequence.

**Theorem 1.2 (All finite residues share convergence).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/CountAsymptotics.finite_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MinimalForts/CountAsymptotics.finite_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

For every finite type of indices, real limit l, and family f(i,k) tending to l for each index, every index selector a(n) and natural block selector b(n) tending to infinity give f(a(n),b(n)) tending to l along the entire natural sequence. Finiteness supplies one tail bound simultaneously for every index. The selectors need not converge or be monotone.

## References

- Truth anchor: `D5/S3/Combinatorics/MinimalForts/CountAsymptotics.finite_diagonal`
- Truth anchor: `D5/S3/Combinatorics/MinimalForts/CountAsymptotics.mixed_count_normalization`
- Dependency: [D5/S3/Combinatorics/MinimalForts/BlockParameters](BlockParameters.md)
- Dependency: [D5/S3/Combinatorics/MinimalForts/MixedBlocks](MixedBlocks.md)
