# The Analytic Zero Dichotomy

## Abstract

A complex-analytic relation either vanishes identically or has isolated zeros.

**Theorem 1.1 (Analytic relations vanish identically or have isolated zeros).**

$$\operatorname{AnalyticOnNhd}(\mathbb{C}, f, U) \land \operatorname{IsPreconnected}(U) \Rightarrow \\(f=0 \operatorname{on} U) \lor \operatorname{Eventually}_{\operatorname{codiscreteWithin}(U)} f(z)\neq0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Isolation/AnalyticZeroDichotomy.analytic_zero_dichotomy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f be complex analytic on a preconnected set U. Exactly the rigidity needed by the source follows: either f is zero throughout U, or f is nonzero codiscretely within U. In one complex variable, the latter is the filter formulation that the zeros are isolated.

Consequently, zeros accumulating at an interior point cannot occur in the nonzero branch. Mathlib also exposes this consequence directly as `AnalyticOnNhd.eqOn_zero_of_preconnected_of_mem_closure`; the displayed dichotomy retains both alternatives of the source atom instead of only that consequence.

Mathlib was searched before proving. Local searches of pinned `Mathlib/Analysis/Analytic/IsolatedZeros.lean` found the exact theorem `AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected` and the accumulation-point identity theorem. The Lean proof imports and applies the exact dichotomy, with no independent analytic argument.

Repository duplicate searches found applications of Mathlib's identity principle and a specialized rational-span level-set theorem, but no existing public declaration of this general complex-analytic zero dichotomy.

## References

- Truth anchor: `D5/S3/Analytic/Isolation/AnalyticZeroDichotomy.analytic_zero_dichotomy`
