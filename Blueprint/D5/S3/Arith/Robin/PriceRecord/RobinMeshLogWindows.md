# Two-sided Robin excursions in fixed logarithmic windows

## Abstract

Both critical Robin excursions carry positive gap weight in every late log window.

**Theorem 1.1 (Positive gap-weight shares for both signs).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RobinMeshLogWindows.actual_attained_canonical_critical_log_windows`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RobinMeshLogWindows.actual_attained_canonical_critical_log_windows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lee Crossley (2026). *How often the 547/727 prime race makes a large move*. DOI: [10.5281/zenodo.24412164](https://doi.org/10.5281/zenodo.24412164). URL: <https://github.com/leecrossley/theta-race-excursion-proportions/blob/b02cd1d888ef799eee54d0a878a7aa0b0e5ec065/PROOF.md>.

*Commentary.*

Suppose a nontrivial zeta zero ρ attains the zero abscissa Θ with Re(ρ)>1/2. Let N be any strictly increasing sequence in ℕ with N(0)>0 and N(k+1)/N(k) tending to 1 in ℝ. Write y(k)=log(N(k)) and s(k)=N(k)^(1−Θ)y(k) robinLogMargin(strictInteger(firstLayerPrice(N(k)+1))). There exist T in ℝ and positive H, c and d such that every window [t,t+H) with t≥T has a nonempty block of exactly the indices a≤k<b with y(k) in the window. The samples s(k)>c and s(k)<−c each carry at least a fraction d of the block's total weight y(b)−y(a). Each index receives its full gap y(k+1)−y(k).

The signed sample asymptotic and maximal-line projection give an absolutely summable phase series up to a null error. Real zeta nonvanishing makes the zero-frequency coefficient vanish. The attaining zero gives a nonzero twisted coefficient with its exact negative analytic multiplicity divided by ρ(1−ρ). The block estimates give uniform bounds for both moments on each late block. Absolute summability bounds the late samples, so a lower bound on the twisted moment and a small ordinary mean force a positive weight share on each side. The first mesh crossings of t and t+H select the block, whose span stays large as the gaps vanish.

Crossley studies the change in the 547/727 split–inert prime-ideal race when the starting height doubles. Under primitive Dirichlet GRH, in every sufficiently late interval of log length at least 250,000, more than 10% of the log starting heights give a gain above 1.9735 log 2 and more than 10% give a loss above that magnitude.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RobinMeshLogWindows.actual_attained_canonical_critical_log_windows`
- Dependency: [D5/S3/Analytic/Asymptotics/GapWeightedFourierBlocks](../../../Analytic/Asymptotics/GapWeightedFourierBlocks.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/RobinMeshFourierRecovery](RobinMeshFourierRecovery.md)
- Dependency: [D5/S3/Weil/ZetaBridge/AlternatingZetaContinuation](../../../Weil/ZetaBridge/AlternatingZetaContinuation.md)
