# Vanishing Tail Budgets Close

## Abstract

Vanishing tail budgets force certified readings to converge to the exact value.

**Theorem 1.1 (A vanishing tail budget closes the certified readings).**

$$\Vert v-r(W) \Vert \le b(W), b(W) \to 0 \Rightarrow r(W) \to v$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/TailClosure.vanishing_tail_budget_closes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A certificate on a cofinal family of finite windows gives an exact value, a reading at every window, and a nonnegative budget bounding the absolute reading error. When those budgets converge to zero along a chosen window filter, the readings converge to the exact value. This is the closure step asserted by the source atom: the infinite object is handled through finite readings and a budget whose disappearance is itself machine checked.

The library search found the exact analytic core in pinned Mathlib. The Lean declaration is therefore a thin honest wrapper: Certificate.error_le supplies the pointwise distance bound, squeeze_zero makes that distance converge to zero, and tendsto_iff_dist_tendsto_zero converts the distance statement into convergence of the certified readings. No independent convergence argument is re-proved here.

## References

- Truth anchor: `D5/S3/Analytic/TailClosure.vanishing_tail_budget_closes`
- Dependency: [D5/S3/Analytic/TailCertificate](TailCertificate.md)
