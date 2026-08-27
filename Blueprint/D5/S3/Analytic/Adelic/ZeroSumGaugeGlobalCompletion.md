# Zero-Sum Gauge Invariance of the Structural Completion Signature

## Abstract

A zero-sum redistribution preserves the global additive defect and the structural completion signature K(C)/G.

**Theorem 1.1 (A zero-sum local gauge preserves the global defect and signature).**

$$\begin{aligned}V_{f}, V_{\infty}: Type, \operatorname{Nonempty}\left(V_{f}\right), \operatorname{Nonempty}\left(V_{\infty}\right)\\D: Type, \operatorname{AddCommGroup}\left(D\right), \operatorname{TopologicalSpace}\left(D\right), \operatorname{IsTopologicalAddGroup}\left(D\right), \operatorname{T2Space}\left(D\right)\\V:=\operatorname{Sum}\left(V_{f}, V_{\infty}\right)=\operatorname{AdelicPlace}\left(V_{f}, V_{\infty}\right)\\L: \operatorname{AdelicLocalLedger}\left(V_{f}, V_{\infty}, D\right), \operatorname{Summable}\left(\operatorname{localContribution}\left(L\right)\right)\\b: \operatorname{ZeroSumGauge}\left(V_{f}, V_{\infty}, D\right), \operatorname{HasSum}\left(\operatorname{shift}\left(b\right), 0\right)\\\Delta_{glob}(L):=\sum_{v\in V} L_{v}\\N(C)=\operatorname{AdelicLocalLedger}\left(V_{f}, V_{\infty}, D\right)\\K(C)=\{L\in N(C)\mid\Delta_{glob}(L)=0\}\\G(C)=\operatorname{ZeroSumGauge}\left(V_{f}, V_{\infty}, D\right), \Sigma(C)=K(C)/G(C)\\\forall L, b, (\Delta_{glob}(\operatorname{gaugeTransform}\left(L, b\right))=\sum_{v\in V} (L_{v}+b_{v})=\sum_{v\in V} L_{v}=\Delta_{glob}(L)) \land\\{}(\forall k: K(C), \operatorname{structuralCompletionSignatureClass}\left(\operatorname{gaugeTransformCompletionPoint}\left(k, b\right)\right)=\operatorname{structuralCompletionSignatureClass}\left(k\right)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/ZeroSumGaugeGlobalCompletion.zero_sum_gauge_preserves_global_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite and infinite place types are both nonempty, and their disjoint sum is the full place type. The defect codomain is any Hausdorff topological additive commutative group. An adelic local ledger is a summable family in that codomain, while ZeroSumGauge is the additive subgroup of summable shift families with total zero.

The normalization set N is the full ledger space. GlobalCompletionPoint is the subtype K(C) of normalized ledgers whose globalAdditiveDefect vanishes. Zero-sum gauges act on K(C), and StructuralCompletionSignature is the orbit quotient K(C)/G.

Summable.tsum_add proves that a gauge transform preserves globalAdditiveDefect, so it maps completion points to completion points. Quotient.sound then proves that every transformed completion point has the same structuralCompletionSignatureClass. These are the two conjuncts of the public theorem.

## References

- Truth anchor: `D5/S3/Analytic/Adelic/ZeroSumGaugeGlobalCompletion.zero_sum_gauge_preserves_global_completion`
