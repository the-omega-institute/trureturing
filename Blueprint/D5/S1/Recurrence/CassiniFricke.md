# Cassini-Fricke Antiinvariant

## Abstract

The Cassini-Fricke quadratic form is an alternating invariant of Binet recurrences.

**Theorem 1.1 (Cassini-Fricke quadratic-form antiinvariant).**

$$Q(u_{K+1}, u_K)=u_{K+1}^{2}-u_{K+1}u_K-u_K^{2}=-5AB(-1)^{K}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/CassiniFricke.cassini_fricke` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let phi and psi satisfy phi^2 = phi + 1, psi^2 = psi + 1, phi + psi = 1, and phi*psi = -1 in a commutative ring. For the Binet sequence u_K = A*phi^K + B*psi^K and the quadratic form Q(a,b) = a^2 - a*b - b^2, the value Q(u_(K+1),u_K) is -5*A*B*(-1)^K. Taking A = -x*phi and B = y*psi gives A*B = x*y, so the result is 5*x*y*(-1)^(K+1), exactly the source theorem's Cassini-Fricke antiinvariant.

## References

- Truth anchor: `D5/S1/Recurrence/CassiniFricke.cassini_fricke`
