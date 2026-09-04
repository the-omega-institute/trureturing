# Simple-Zero Memory Shift

## Abstract

A simple zero has a locally unique analytic branch under a quadratic closed-loop perturbation.

**Theorem 1.1 (A quadratic memory term displaces a simple zero).**

$$\forall F \in \mathbb{C} \to \mathbb{C}, A \in \mathbb{C} \to \mathbb{C}, rho \in \mathbb{C},\; \left(\operatorname{AnalyticAt}\left(\mathbb{C}, F, rho\right) \land \left(\operatorname{AnalyticAt}\left(\mathbb{C}, A, rho\right) \land \left(F\left(rho\right) = 0 \land \left(\neg \operatorname{deriv}\left(F, rho\right) = 0\right)\right)\right)\right) \Rightarrow \left(\exists branch \in \mathbb{C} \to \mathbb{C},\; branch\left(0\right) = rho \land \left(\operatorname{EventuallyAt}\left(kappa, \operatorname{nhds}\left(0\right), F\left(branch\left(kappa\right)\right) - kappa \times A\left(branch\left(kappa\right)\right)^{2} = 0\right) \land \left(\operatorname{EventuallyAt}\left(p, \operatorname{nhds}\left(\operatorname{pair}\left(0, rho\right)\right), F\left(\operatorname{snd}\left(p\right)\right) - \operatorname{fst}\left(p\right) \times A\left(\operatorname{snd}\left(p\right)\right)^{2} = 0 \Leftrightarrow branch\left(\operatorname{fst}\left(p\right)\right) = \operatorname{snd}\left(p\right)\right) \land \operatorname{IsBigOAtZero}\left((kappa \mapsto branch\left(kappa\right) - rho - kappa \times A\left(rho\right)^{2} / \operatorname{deriv}\left(F, rho\right)), (kappa \mapsto kappa^{2})\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaCompletionFlow/SimpleZeroMemoryShift.simple_zero_memory_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source formula does not state the equation that defines the displaced zero. The positive first-order sign fixes that equation as F(z) minus kappa times A(z) squared equals zero; the formal statement makes this correction explicit.

For analytic F and A and a simple zero rho of F, the complex implicit function theorem constructs a branch through rho. Near the base pair, the displayed equation holds exactly when z is the branch value, so the continuation is locally unique.

Differentiating the equation gives the coefficient A(rho) squared divided by the derivative of F at rho. Analytic Taylor factorization supplies a genuine quadratic big-O remainder. The complex parameter statement is stronger than the real small-parameter formulation and does not identify the branch with zeros of the Riemann zeta function.

## References

- Truth anchor: `D5/S3/Analytic/ZetaCompletionFlow/SimpleZeroMemoryShift.simple_zero_memory_shift`
