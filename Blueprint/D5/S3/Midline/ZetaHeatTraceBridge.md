# The Labeled-Zeta Heat-Trace Bridge

## Abstract

Prime-axis logarithmic length derives the labeled-zeta Hilbert criterion from the universal heat-abscissa theorem.

<a id="describe-labeled-zeta-is-the-prime-axis-specialization"></a>

**Theorem 1.1 (Labeled zeta is the prime-axis specialization).**

$\forall s\in\mathbb{C},\ \operatorname{MemLp}(\operatorname{labeledZetaCoefficient}(s),2)\Leftrightarrow\frac12<\Re(s)$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/ZetaHeatTraceBridge.zeta_mem_iff_from_universal_heat_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bridge identifies the universal heat coefficient with the labeled-zeta coefficient, proves boundary-divergent abscissa one by transporting to the p-series on natural addresses, and then applies the universal strict theorem.

## References

- Truth anchor: `D5/S3/Midline/ZetaHeatTraceBridge.zeta_mem_iff_from_universal_heat_trace`
