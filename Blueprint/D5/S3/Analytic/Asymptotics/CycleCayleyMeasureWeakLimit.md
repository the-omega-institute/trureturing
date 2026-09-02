# Cyclic Cayley Measure Weak Limit

## Abstract

Finite cyclic Cayley measures converge weakly to the standard Cauchy law.

**Theorem 1.1 (The cyclic Cayley measures converge to the standard Cauchy law).**

$$\begin{gathered}cycleCayleyEmpiricalMeasure: \mathbb{N} \to \operatorname{ProbabilityMeasure}(\mathbb{R}),\\{}\forall n \in \mathbb{N},\quad cycleCayleyEmpiricalMeasure\left(n\right) := \operatorname{asProbabilityMeasure}(\operatorname{toMeasure}(\operatorname{map}(j \mapsto -\operatorname{cot}(\frac{\pi (j + 1)}{n + 2}), \operatorname{uniformOfFintype}(\operatorname{Fin}(n + 1))))),\\{}\operatorname{Tendsto}(cycleCayleyEmpiricalMeasure, \operatorname{atTop}(\mathbb{N}), \operatorname{nhds}(\operatorname{cauchyMeasure}(\mathbb{R}, 0, 1))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/CycleCayleyMeasureWeakLimit.cycle_cayley_measure_weak_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n in the natural numbers, the cycle size is n+2. The measure is constructed by putting the uniform probability mass on Fin(n+1), then mapping index j to -cot(pi(j+1)/(n+2)). Thus every cycle size K at least two occurs exactly once, with all K-1 nontrivial phases having mass 1/(K-1).

The proof computes each lower-interval mass exactly. The Cayley order equivalence turns the event into a finite grid count, whose size is a floor. Pinned Mathlib's floor-ratio limit makes these masses tend to the standard Cauchy distribution function.

Convergence on the pi-system of half-open intervals is then promoted by Mathlib's probability-measure convergence theorem to Tendsto in the weak topology. The target cauchyMeasure(0,1) is the probability law with density 1/(pi(1+h^2)); no affine shift or scale is introduced.

## References

- Truth anchor: `D5/S3/Analytic/Asymptotics/CycleCayleyMeasureWeakLimit.cycle_cayley_measure_weak_limit`
