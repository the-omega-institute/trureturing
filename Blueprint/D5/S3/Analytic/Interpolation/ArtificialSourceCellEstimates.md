# Quartic cell estimates

## Abstract

Quartic cells control a perturbed Robin price coordinate on an adaptive grid.

**Theorem 1.1 (The Robin kernel derivative).**

Lean statement: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.kernel_has_deriv_at`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.kernel_has_deriv_at` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real x greater than one, k(x)=(log x+1)/(x squared times (log x) squared) has derivative -(2(log x) squared+3 log x+2)/(x cubed times (log x) cubed). This follows from differentiating the scaled Robin weight at scale parameter one.

**Theorem 1.2 (The two cell derivatives).**

Lean statement: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.cell_derivatives`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.cell_derivatives` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real delta, a and x with width h(delta,a) positive, cellBump(delta,a,x)=-amplitude(delta,a) eta((x-a)/h) has derivative -(amplitude/h) etaOne((x-a)/h). That derivative expression itself has derivative -(amplitude/h squared) etaTwo((x-a)/h). Here etaOne(s)=2s(1-s)(1-2s) and etaTwo(s)=2-12s+12s squared. These identities hold for the polynomial continuation at every real x, including either endpoint.

**Theorem 1.3 (Uniform control on a cell).**

Lean statement: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.cell_estimates`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.cell_estimates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let delta, a and x be arbitrary real numbers. Assume a>1, log a at least one, 0<h(delta,a)<=a, and a<=x<=a+h. Set c=1/128, epsilon(a)=log(a) exp(-(log a) to the power 1/4). Then the absolute value of cellSlope(delta,a,x)/k(x) is at most 4c epsilon(a) h. The absolute value of the derivative of y-cellSlope(delta,a,y)/k(y), evaluated at x, minus one is at most 44c epsilon(a). The estimates combine the quartic derivatives, the exact amplitude/width-squared cancellation and the Robin kernel bounds on [a,2a].

**Theorem 1.4 (The increment budget derivative).**

Lean statement: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.epsilon_has_deriv_at`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.epsilon_has_deriv_at` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each real a>1, epsilon has derivative exp(-(log a) to the power 1/4)/a times (1-(log a) to the power 1/4 divided by four). Thus epsilon decreases after its fourth-root logarithm reaches four.

**Theorem 1.5 (Decay of the increment budget).**

Lean statement: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.epsilon_tendsto_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.epsilon_tendsto_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The function epsilon(a)=log(a) exp(-(log a) to the power 1/4) tends to zero as a tends to positive infinity. Substitution u=(log a) to the power 1/4 reduces this to polynomial times exponential decay.

**Theorem 1.6 (Eventual admissible width bounds).**

Lean statement: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.width_eventually_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.width_eventually_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every fixed positive real delta, eventually as a tends to positive infinity, log a is at least one and 1<=h(delta,a)<=a. The width is h(delta,a)=a to the power 3/4 times exp((log a) to the power 1/4 divided by two), divided by sqrt(log a), times (log a) to the power delta. Taking logarithms leaves a leading term 3 log(a)/4; the fourth-root and log-log terms are smaller than log(a).

**Theorem 1.7 (Comparing the budget across a cell).**

Lean statement: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.epsilon_cell_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.epsilon_cell_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real a>1 with log a at least one and real x in [a,2a], epsilon(a)<=2 epsilon(x). The logarithmic displacement is at most log 2. The fourth-root function has derivative at most one when its argument is at least one, so its displacement is also at most log 2.

**Theorem 1.8 (The remaining exponential saving).**

Lean statement: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.epsilon_width_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.epsilon_width_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real delta and a>1, epsilon(a) h(delta,a)=a to the power 3/4 times exp(-(log a) to the power 1/4 divided by two) times (log a) to the power (delta+1/2).

**Theorem 1.9 (An admissible start is positive).**

Lean statement: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.admissible_gt_one`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.admissible_gt_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any real delta and A satisfying Admissible(delta,A), A>1. The condition log(a)>=1 for every a>=A rules out A<=1 by evaluating it at a=1.

**Theorem 1.10 (The grid escapes every bounded interval).**

Lean statement: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.grid_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.grid_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real delta and admissible A, every natural j has A+j<=grid(delta,A,j). The grid starts at A and each successive width is at least one. Induction also keeps every grid point inside the admissible half-line.

**Theorem 1.11 (Strict ordering of the grid).**

Lean statement: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.grid_strictMono`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.grid_strictMono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real delta and admissible A, grid(delta,A) is a strictly increasing function of its natural index. Every width at a grid point is at least one.

**Theorem 1.12 (The selected cell contains its point).**

Lean statement: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.cell_index_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.cell_index_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real delta, admissible A and real x>=A, x lies in [grid(delta,A,cellIndex(delta,A,x)),grid(delta,A,cellIndex(delta,A,x)+1)). The index is the greatest j whose grid point is at most x, searched up to floor(x-A) in the natural numbers. The grid lower bound makes that finite search complete.

**Theorem 1.13 (Agreement including the upper seam).**

Lean statement: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.bump_on_cell`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.bump_on_cell` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real delta, admissible A, natural j and x in the closed cell [a(j),a(j+1)], bump(delta,A,x)=cellBump(delta,a(j),x). At the upper endpoint, the next cell is selected; both polynomial values are zero.

**Theorem 1.14 (The actual assembled derivative).**

Lean statement: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.bump_has_deriv_at`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.bump_has_deriv_at` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real delta, admissible A and x>=A, the actual bump has derivative cellSlope(delta,grid(delta,A,cellIndex(delta,A,x)),x). The bump is the selected polynomial above A and is zero below A. At a seam, the adjacent first derivatives both vanish. The matching one-sided derivatives therefore give an ordinary two-sided derivative, including at A.

**Theorem 1.15 (The derivative agrees on a closed cell).**

Lean statement: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.bump_deriv_on_cell`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.bump_deriv_on_cell` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real delta, admissible A, natural j and x in [a(j),a(j+1)], the derivative of the assembled bump equals cellSlope(delta,a(j),x). At the upper seam both the selected derivative and the preceding polynomial derivative are zero.

**Theorem 1.16 (Continuity across every seam).**

Lean statement: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.bump_deriv_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.bump_deriv_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real delta and admissible A, the derivative of bump(delta,A) is continuous on [A,infinity). Inside each cell it is polynomial. At a grid point its two one-sided continuations both vanish; at A only the restriction to the half-line is needed.

**Theorem 1.17 (A C1 adaptive bump).**

Lean statement: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.bump_cont_diff_on`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.bump_cont_diff_on` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real delta and admissible A, bump(delta,A) is C1 on [A,infinity). Here admissibility means log(a)>=1, epsilon(a)<=1, 1<=width(delta,a)<=a for every a>=A, together with antitonicity of epsilon on that half-line. The function is differentiable there and its actual derivative is continuous. The construction uses a(j+1)=a(j)+width(delta,a(j)), alpha(delta,a)=(1/128)(log a) to the power (2 delta-1) divided by sqrt(a), and the quartic eta(s)=s squared times (1-s) squared.

## References

- Truth anchor: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.admissible_gt_one`
- Truth anchor: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.bump_cont_diff_on`
- Truth anchor: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.bump_deriv_continuous`
- Truth anchor: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.bump_deriv_on_cell`
- Truth anchor: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.bump_has_deriv_at`
- Truth anchor: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.bump_on_cell`
- Truth anchor: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.cell_derivatives`
- Truth anchor: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.cell_estimates`
- Truth anchor: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.cell_index_spec`
- Truth anchor: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.epsilon_cell_comparison`
- Truth anchor: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.epsilon_has_deriv_at`
- Truth anchor: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.epsilon_tendsto_zero`
- Truth anchor: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.epsilon_width_identity`
- Truth anchor: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.grid_bounds`
- Truth anchor: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.grid_strictMono`
- Truth anchor: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.kernel_has_deriv_at`
- Truth anchor: `D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.width_eventually_bounds`
- Dependency: [D5/S3/Arith/Robin/MellinWeightedVariation](../../Arith/Robin/MellinWeightedVariation.md)
