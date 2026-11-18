# The exact exponential rate of the large distinct-prime tail

## Abstract

The exact exponential rate of the large distinct-prime tail.

**Theorem 1.1 (The two-sided counting asymptotic).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/Asymptotic.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/Asymptotic.result` (`✓ std3`). ∎

*Resolves.* `Problems/luca-pomerance-sole-2025-large-omega-count-rate` (proved) by `D5/S3/Arith/Robin/Analytic/OmegaTail/Asymptotic.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"luca-pomerance-sole-2025-large-omega-count-rate","declaration_gid":"D5/S3/Arith/Robin/Analytic/OmegaTail/Asymptotic.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

As x tends to positive infinity, log(tailCount(0,x))/scale(x) tends to C0, where C0 is the infimum of rate(0,s) over s>1. For s>1 on u>0, the density q(s,u)=a(s)^s/(a(s)^s+u^s) has mass one, logarithmic moment m(s), and integrated binary entropy H(s). Moving s to the right of the unique saddle makes the moment strictly negative. Compact truncation and horizontal rescaling preserve mass one and give strict logarithmic slack; finite averaging increases entropy. The lower exponent follows from actual prime subsets, and continuity lets s decrease to the saddle. The phase-one upper_bound is applied directly at that saddle. The saddle lies strictly between one and two, C0=rate(0,saddle)=H(saddle), and C0>1. The eventual lower bound log(tailCount(0,x))/scale(x)>=C0-1/2>0 excludes tailCount(0,x)=0, so the count is eventually positive and its logarithm is meaningful. This concerns distinct prime factors. It supplies an upper-bound interpretation for Robin exceptions through the source necessary condition, and does not identify their own asymptotic count. The decimal interval 2.8054<C0<2.8055 is not certified by this theorem.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/Asymptotic.result`
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTail/Binning](Binning.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTail/Counting](Counting.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTail/Saddle](Saddle.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTail/Truncation](Truncation.md)
