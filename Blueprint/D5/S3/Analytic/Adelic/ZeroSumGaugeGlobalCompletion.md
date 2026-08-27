# Zero-Sum Gauge Invariance of Global Additive Completion

## Abstract

A zero-sum redistribution of adelic local contributions preserves their global additive completion.

**Theorem 1.1 (A zero-sum local gauge preserves the global additive completion).**

$$\begin{aligned}V:=\operatorname{Sum}\left(V_{f}, V_{\infty}\right), AdelicPlace(V_{f}, V_{\infty})=V\\L: \operatorname{AdelicLocalLedger}\left(V_{f}, V_{\infty}\right), \operatorname{Summable}\left(\operatorname{localContribution}\left(L\right)\right)\\b: \operatorname{ZeroSumGauge}\left(V_{f}, V_{\infty}\right), \operatorname{HasSum}\left(\operatorname{shift}\left(b\right), 0\right)\\\Delta_{glob}(L):=\sum_{v\in V} L_{v}\\\forall V_{f}, V_{\infty}: Type, \forall L, b, \Delta_{glob}(\operatorname{gaugeTransform}\left(L, b\right))=\sum_{v\in V} (L_{v}+b_{v})=\sum_{v\in V} L_{v}=\Delta_{glob}(L).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/ZeroSumGaugeGlobalCompletion.zero_sum_gauge_preserves_global_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The place type is the disjoint sum of finite and infinite places. An adelic local ledger consists of a real contribution at every place together with summability of that family. A zero-sum gauge consists of a shift at every place together with a HasSum witness that its total is zero.

The gauge transform replaces each local contribution L_v by L_v + b_v. Mathlib's Summable.tsum_add identifies the transformed total with the sum of the original total and the gauge total; the HasSum witness reduces the latter to zero.

This statement formalizes the section-15 additive completion reading. The source separately names an earlier quotient K(C)/G as a structural completion signature, but supplies no map or theorem connecting that quotient to this real-valued sum.

## References

- Truth anchor: `D5/S3/Analytic/Adelic/ZeroSumGaugeGlobalCompletion.zero_sum_gauge_preserves_global_completion`
