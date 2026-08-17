# Cassini-Fricke Log-Coordinate Specializations

## Abstract

The generic Cassini-Fricke identity specializes to signed log coordinates and a conserved absolute value.

**Theorem 1.1 (The log-coordinate quadratic value alternates in sign).**

$$u_{K} := -x\phi^{K+1} + y\psi^{K+1},\ Q(a, b) := a^{2} - ab - b^{2},\ J_{K} := Q(u_{K+1}, u_{K}) = 5 \cdot x \cdot y \cdot (-1)^{K+1}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CassiniFrickeSpecializations.cassini_fricke_log_coordinate_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first chain clause introduces u_K and Q but ends before its displayed conclusion. This declaration makes those definitions explicit in its expanded quadratic expression and supplies the signed identity needed to complete that chain stem.

It directly applies the repository theorem cassini_fricke to Mathlib's goldenRatio and goldenConj with A = -x*phi and B = y*psi. Their product is -1, which turns A*B into x*y, so no recurrence identity is reproved.

**Theorem 1.2 (The absolute quadratic value is conserved).**

$$\lvert J_{K}\rvert = 5 \cdot \lvert x \cdot y\rvert$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CassiniFrickeSpecializations.cassini_fricke_absolute_conservation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking absolute values of the signed specialization removes the factor (-1)^(K+1) and yields 5*|x*y|. Thus consecutive signed values differ by a sign, while their magnitude is independent of K.

The zero-axis and diagonal readings in the source follow by substituting y = 0 and x = y into this formula. The theorem records the common conservation law rather than duplicating those immediate leaf cases.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/CassiniFrickeSpecializations.cassini_fricke_absolute_conservation`
- Truth anchor: `D5/S1/Recurrence/Invariants/CassiniFrickeSpecializations.cassini_fricke_log_coordinate_identity`
- Dependency: [D5/S1/Recurrence/CassiniFricke](../CassiniFricke.md)
