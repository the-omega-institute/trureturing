# Cofinal Windows and Tail Closure

## Abstract

Cofinal finite windows and a vanishing certified tail budget close an exact reading.

**Theorem 1.1 (Cofinal windows and a vanishing budget close).**

$$\forall Atom, Window: \operatorname{Type}, \forall family: \operatorname{CofinalWindowFamily}\left(Atom, Window\right), \forall control: \operatorname{TailControl}\left(Window\right), \forall value \in \mathbb{R}, \forall certificate: \operatorname{Certificate}\left(family, control, value\right), \forall windows: \operatorname{Filter}\left(Window\right), \forall finite: \operatorname{Finset}\left(Atom\right), \operatorname{Tendsto}(\operatorname{budget}\left(certificate\right), windows, 0) \Rightarrow (\exists window, finite \subseteq \operatorname{contents}\left(family, window\right)) \land \operatorname{Tendsto}(\operatorname{reading}\left(certificate\right), windows, value)$$

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/CofinalTailDiscipline.cofinal_windows_and_vanishing_budget_close` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite set of source atoms, cofinality supplies a finite window containing it. A certificate assigns each window a reading and a nonnegative tail budget that bounds the reading error. When the budget converges to zero along the chosen window filter, the certified readings converge to the exact value.

The proof is a thin wrapper over the cofinality field of the window family and the existing certified tail-closure theorem. It packages the finite-window and tail-budget clauses into the single closure statement asserted by the source atom.

## References

- Truth anchor: `D5/S3/AnalyticClosure/CofinalTailDiscipline.cofinal_windows_and_vanishing_budget_close`
- Dependency: [D5/S3/Analytic/TailClosure](../Analytic/TailClosure.md)
