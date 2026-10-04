# The upper-bound optimization

## Abstract

Independence budgets, clique bounds and triangle reserves give the exact prime upper bound for every cycle-clique union.

**Theorem 1.1 (Optimizing the component budgets).**

Lean statement: `D5/S3/Combinatorics/RegularInduced/DysonMcKayUpper.upper_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RegularInduced/DysonMcKayUpper.upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul W. Dyson, Brendan D. McKay (2026). *Ramsey numbers for regular induced subgraphs*. DOI: [10.48550/arXiv.2604.08215](https://doi.org/10.48550/arXiv.2604.08215). URL: <https://arxiv.org/abs/2604.08215v3>.

*Commentary.*

For every prime p at least thirteen, any finite union of C_r[K_s] with r at least three and s at least one and with no regular induced subgraph on p vertices has order N at most the stated bound. Put S = (p-1)/2. Give a component independence capacity a = 1 for r = 3 and a = floor(r/2) otherwise. Its triangle capacity is one for r = 3, floor(r/2) for r at least four and s at least three, floor(r/3) for r at least four and s = 2, and zero for r at least four and s = 1. Let A and T be the sums of these capacities, and let R be the sum of two for each r = 3 component and r otherwise. Avoiding independent p-sets gives A at most p-1, and avoiding p-cliques gives 3s at most p-1 for r = 3 and 2s at most p-1 otherwise. Consequently N is at most SR and 2N is at most 5ST+10A. If 3T is less than p+4, the latter inequality already gives the desired bound. Otherwise, full-support cycle selections can be supplemented by triangle packets. For p congruent to one modulo three this excludes every seven-cycle component and permits at most one five-cycle component; for p congruent to two it excludes every five-cycle component and permits at most one seven-cycle component. Summing 4r at most 9floor(r/2), with the corrections two at r = 5 and one at r = 7 and with contribution two at r = 3, bounds R by 27t, 27t+9, 27t+14 or 27t+22 for p = 12t+1, 12t+5, 12t+7 or 12t+11, respectively. Multiplying by S gives the four exact extremal orders.

## References

- Truth anchor: `D5/S3/Combinatorics/RegularInduced/DysonMcKayUpper.upper_bound`
- Dependency: [D5/S3/Combinatorics/RegularInduced/DysonMcKayBags](DysonMcKayBags.md)
