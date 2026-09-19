# The Boundary Counterexample to CRIM Conjecture 2

## Abstract

The printed square-rectair formula gives 2 at r=1 and k=0, but the value is 1.

**Definition 1.1 (Conjecture 2 as printed).**

$$(claim) \Leftrightarrow (\forall r \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; (k < r) \Rightarrow (\operatorname{grundy}\left(\operatorname{rectair}\left(r, r, k\right)\right) = (\operatorname{if} ((\operatorname{mod}\left(r, 2\right) = 0) \lor (k < r - 1)) \operatorname{then} 0 \operatorname{else} (\operatorname{if} ((r = 3) \lor (r = 5)) \operatorname{then} 1 \operatorname{else} 2))))$$

*Formalization.* `D5/S0/Certificates/Games/CrimRectairSquareBoundaryRefutation.claim` (`✓ std3`).

*Citation.* Ina Bašić; Eric Gottlieb; Matjaž Krnc (2026). *CRIM: A Natural Game on Integer Partitions*. DOI: [10.48550/arXiv.2606.16828](https://doi.org/10.48550/arXiv.2606.16828).

*Commentary.*

Conjecture 2 states verbatim: "Let r and k be integers with 0 ≤ k < r. Then G(R^k_{r,r}) = 0 if r is even or k < r − 1; = 1 if r ∈ {3, 5}, r is odd, and k = r − 1; = 2 otherwise." The formal variables are natural numbers; k < r forces r to be positive. The statement uses the public grundy and rectair names from CrimGrundyRefutation. Here mod(r,2) is the natural-number remainder and r−1 is natural-number subtraction. In the second branch, failure of the first branch together with k < r implies that r is odd and k = r−1, so the nested conditional is equivalent to the printed three branches on the quantified domain.

**Theorem 1.2 (The value at r=1 and k=0).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Games/CrimRectairSquareBoundaryRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At r=1 and k=0, rectair(1,1,0) is the one-cell partition [1]. Its row and column deletions both reach the empty partition, so moves([1]) is [[],[]]. The empty partition has value 0, hence the least excluded option value is 1. The printed third branch gives 2. The same page's Conjecture 4 also gives the first stair value as 1. The theorem refutes only the literal printed Conjecture 2 and does not propose a corrected formula.

## References

- Truth anchor: `D5/S0/Certificates/Games/CrimRectairSquareBoundaryRefutation.claim`
- Truth anchor: `D5/S0/Certificates/Games/CrimRectairSquareBoundaryRefutation.result`
- Dependency: [D5/S0/Certificates/Games/CrimGrundyRefutation](CrimGrundyRefutation.md)
