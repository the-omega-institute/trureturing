# Feasible integer multiplicities and vanishing error

## Abstract

Feasible integer multiplicities and vanishing error.

**Theorem 1.1 (Approximation on the entire integer tail).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/SimplexApproximation.eventual_simplex_approximation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MinimalForts/SimplexApproximation.eventual_simplex_approximation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

For real p,b,g,c with p positive, b negative, zero less than g less than p, and b divided by p irrational, every positive real epsilon admits a natural threshold K such that every natural k at least K has nonnegative natural x,y,z with x plus y plus z equal to k and absolute value of x b plus z p minus k g minus c less than epsilon. A finite rotation window is fixed for each tolerance; the interior target slope ensures nonnegative feasible coordinates on the entire tail.

**Theorem 1.2 (Actual feasible sequences for every index).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/SimplexApproximation.simplex_approximation_sequence`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MinimalForts/SimplexApproximation.simplex_approximation_sequence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

Under the same hypotheses, there are three natural-valued sequences x,y,z whose sum is k at every natural index k, and whose signed real errors x(k)b plus z(k)p minus k g minus c tend to zero as k tends to infinity. At every index a least absolute-error pair is chosen from the finite feasible simplex. The preceding tail theorem bounds these least errors for each positive tolerance. These feasible sequences supply the multiplicities in the every-order graph construction.

## References

- Truth anchor: `D5/S3/Combinatorics/MinimalForts/SimplexApproximation.eventual_simplex_approximation`
- Truth anchor: `D5/S3/Combinatorics/MinimalForts/SimplexApproximation.simplex_approximation_sequence`
- Dependency: [D5/S3/Combinatorics/MinimalForts/RotationWindow](RotationWindow.md)
