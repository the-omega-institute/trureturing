# Right-endpoint logistic grids

## Abstract

A finite grid sampled at its right endpoints controls logistic cost and binary entropy simultaneously.

**Theorem 1.1 (Cost and entropy on a finite logistic grid).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/LogisticGrid.rightEndpoint_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/LogisticGrid.rightEndpoint_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a strictly increasing grid from zero to U with at least one bin and maximum width at most delta. Write q(u) = 1/(1+exp(u)) and f(u) for the binary entropy of q(u). Each bin of width w and right endpoint b contributes 2*w*b*q(b) to the cost and 2*w*f(b) to the entropy.

The cost is at most twice the integral of u*q(u) on [0,U] plus twice delta times the integral of q. The deficit of the grid entropy from twice the integral of f lies between zero and 2*delta*(log(2)-f(U)), which is at most 2*delta*log(2).

For a point u in a bin, the right-endpoint occupancy is at most q(u) and the right endpoint is at most u+delta. The entropy rectangles are ordered by monotonicity on the nonnegative axis. The error in each bin is bounded by delta times the drop of f across that bin. Summing cancels the intermediate endpoint values.

The two sums use the cost and entropy inputs of the fixed-grid exchange argument. Their finite-interval bounds allow the integrated cost and missing entropy tail to be estimated before the prime-counting limit.

**Theorem 1.2 (Explicit cost and entropy estimates).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/LogisticGrid.rightEndpoint_explicit_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/LogisticGrid.rightEndpoint_explicit_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same finite grid, put A = pi squared divided by six. The cost is at most A + 2*delta*log(2). The entropy is at least 2*A - 2*(U+2)*exp(-U) - 2*delta*log(2).

The Fermi Mellin integral gives total occupancy log(2) and first moment A/2. Binary entropy is the sum of the first-moment integrand and log(1+exp(-u)). Integration by parts gives the latter term the same total mass A/2. The entropy integrand is bounded by (1+u)*exp(-u) on the nonnegative axis, so the missing entropy integral from U onward is at most (U+2)*exp(-U).

**Theorem 1.3 (A fixed uniform grid meeting both tolerances).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/LogisticGrid.exists_uniform_rightEndpoint_grid`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/LogisticGrid.exists_uniform_rightEndpoint_grid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every eta > 0 and rho > 0, there exist U at least one and a positive integer m. The uniform grid with endpoints i*U/m has cost at most A*(1+eta/2) and entropy at least 2*A-rho.

Choose U large enough for the exponential tail and then choose m large enough for both mesh errors. This supplies the cost input and the entropy input of the lower bound for the second omega threshold and for each fixed higher threshold. Both grid parameters are fixed before the prime-counting limit.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/LogisticGrid.exists_uniform_rightEndpoint_grid`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/LogisticGrid.rightEndpoint_bounds`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/LogisticGrid.rightEndpoint_explicit_bounds`
- Dependency: [D5/S3/Weil/ZetaBridge/FermiMellin](../../../../Weil/ZetaBridge/FermiMellin.md)
