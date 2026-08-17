# Recurrence Obstructs Continuous Coboundaries

## Abstract

A recurrent nonvanishing cocycle cannot be a continuous coboundary.

**Theorem 1.1 (A recurrent nonzero cocycle is not a continuous coboundary).**

$$\forall X, V,\ [\operatorname{TopologicalSpace}(X)] [\operatorname{AddGroup}(V)] [\operatorname{TopologicalSpace}(V)] [\operatorname{IsTopologicalAddGroup}(V)],\ \phi: \operatorname{Flow}(\mathbb{R}, X), c: \mathbb{R} \to X \to V, x: X, times: \mathbb{N} \to \mathbb{R},\ \operatorname{Tendsto}(times, \operatorname{atTop}, \operatorname{atTop}) \land \operatorname{Tendsto}((n \mapsto \phi(times(n), x)), \operatorname{atTop}, \operatorname{nhds}(x)) \land \neg\operatorname{Tendsto}((n \mapsto c(times(n), x)), \operatorname{atTop}, \operatorname{nhds}(0)) \Rightarrow\ \neg\exists h: X \to V,\ \operatorname{Continuous}(h) \land \forall t, y, c(t, y) = h(\phi(t, y)) - h(y).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HiddenFlow/RecurrentCoboundaryObstruction.recurrent_cocycle_not_continuous_coboundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Phi be a real flow on a topological space X, let c take values in a topological additive group V, and let the times tend to positive infinity. Assume the sampled orbit returns to x while the sampled cocycle does not converge to zero.

If c were the coboundary of a continuous h, continuity along the recurrent orbit would force h(Phi(times(n), x)) to converge to h(x). Subtracting the constant h(x) would then force the sampled cocycle to converge to zero, contradicting the hypothesis.

Loogle supplied the exact supporting declarations Continuous.tendsto and Filter.Tendsto.sub_const, both applied in the proof. Repository and pinned-Mathlib searches found no full-statement match. LeanSearch's API search endpoint returned HTTP 404 and yielded no result.

The natural-number times, the identity flow on Unit, and a real cocycle equal to time give checked jointly satisfiable limit hypotheses.

## References

- Truth anchor: `D5/S3/Observer/HiddenFlow/RecurrentCoboundaryObstruction.recurrent_cocycle_not_continuous_coboundary`
