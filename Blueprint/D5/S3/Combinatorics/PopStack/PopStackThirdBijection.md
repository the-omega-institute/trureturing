# The reverse third-position construction

## Abstract

The map undoPhi(n,p) is empty for n = 0 and equals 3142 for n = 4. Otherwise, when p starts with two, delete that entry and decrease every remaining value other than one to obtain q. If q is simple, apply Phi(n-1,q), increase all values, and insert one second; if not, delete its third entry and decrease every value other than one, inflate the first entry of the resulting skeleton by 21, increase all values, and insert one second. When p does not start with two, delete its third entry and subtract one from every remaining value to obtain q. If q is simple, increase its values and insert one second. If q = R(n-1), do this to B(n-1) instead. Otherwise delete the second entry of q, standardize above its third value, inflate the first entry by 21, increase all values, and insert one second.

**Definition 1.1 (The recursive third-position construction).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackThirdBijection.Phi`

*Formalization.* `D5/S3/Combinatorics/PopStack/PopStackThirdBijection.Phi` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

The map Phi(n,p) is empty for n = 0 and equals 2413 for n = 4. Otherwise delete the second entry and subtract one from all remaining values to obtain q. If q is simple with minimum third, apply undoPhi(n-1,q), increase every value other than one, and prepend two. If q is simple with minimum elsewhere, increase its values and insert one third. If q = B(n-1), return Y(n). Otherwise let s = deflateFirst(q): if its minimum is second, inflate its second entry by 12, increase every value other than one, and prepend two; if not, inflate its second entry by 21, increase all values, and insert one third.

**Definition 1.2 (The reverse third-position construction).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackThirdBijection.undoPhi`

*Formalization.* `D5/S3/Combinatorics/PopStack/PopStackThirdBijection.undoPhi` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

The map undoPhi(n,p) is empty for n = 0 and equals 3142 for n = 4. Otherwise, when p starts with two, delete that entry and decrease every remaining value other than one to obtain q. If q is simple, apply Phi(n-1,q), increase all values, and insert one second; if not, delete its third entry and decrease every value other than one, inflate the first entry of the resulting skeleton by 21, increase all values, and insert one second. When p does not start with two, delete its third entry and subtract one from every remaining value to obtain q. If q is simple, increase its values and insert one second. If q = R(n-1), do this to B(n-1) instead. Otherwise delete the second entry of q, standardize above its third value, inflate the first entry by 21, increase all values, and insert one second.

## References

- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackThirdBijection.Phi`
- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackThirdBijection.undoPhi`
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackMinimumBijection](PopStackMinimumBijection.md)
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackThirdDecomposition](PopStackThirdDecomposition.md)
