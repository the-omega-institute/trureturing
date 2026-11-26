# A shared recurrence for two middle columns

## Abstract

The middle columns T(2n,n) and T(2n-1,n-1) of the triangle T(n,k)=t(n,k)-4 satisfy one three-term recurrence.

**Definition 1.1 (The central column).**

Lean statement: `D5/S1/Recurrence/MatharA027182CentralColumns.u`

*Formalization.* `D5/S1/Recurrence/MatharA027182CentralColumns.u` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

u(n) is the integer T(2n,n), where T(n,k)=t(n,k)−4 and t(n,k)=C(n+2,k+1)+C(n+1,k)+C(n+1,k+1)+C(n,k). Its first values are 1, 10, 42, 156, 570, 2096.

**Definition 1.2 (The adjacent column).**

Lean statement: `D5/S1/Recurrence/MatharA027182CentralColumns.v`

*Formalization.* `D5/S1/Recurrence/MatharA027182CentralColumns.v` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

v(n) is the integer T(2n−1,n−1), read for n≥1; its values from n=1 are 3, 19, 76, 283, 1046.

**Theorem 1.3 (Recurrence for the central column).**

Lean statement: `D5/S1/Recurrence/MatharA027182CentralColumns.u_recurrence`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/MatharA027182CentralColumns.u_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n≥2, 2(n+1)u(n)−(7n+5)u(n−1)+2(3−2n)u(n−2)+12(1−3n)=0. By Pascal's rule t(n,k)=2C(n+2,k+1)+C(n,k), and this is at least five for k≤n, so u(n)=2c(n+1)+c(n)−4 with c(n)=C(2n,n). Substituting, the constant terms cancel, and the remaining expression is the combination 4E(n)+4E(n−1)+E(n−2) of the relations E(j): (j+1)c(j+1)=2(2j+1)c(j).

**Theorem 1.4 (Recurrence for the adjacent column).**

Lean statement: `D5/S1/Recurrence/MatharA027182CentralColumns.v_recurrence`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/MatharA027182CentralColumns.v_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n≥3, 2(n+1)v(n)−(7n+5)v(n−1)+2(3−2n)v(n−2)+12(1−3n)=0. Pascal's rule and the symmetry C(2j+1,j+1)=C(2j+1,j) give 2C(2j+1,j)=c(j+1), hence 2v(n)=u(n)−4 for n≥1. Twice the left side is then the left side of the recurrence for u, because 2(n+1)−(7n+5)+2(3−2n)=3−9n and 4(3−9n)=12(1−3n).

## References

- Truth anchor: `D5/S1/Recurrence/MatharA027182CentralColumns.u`
- Truth anchor: `D5/S1/Recurrence/MatharA027182CentralColumns.u_recurrence`
- Truth anchor: `D5/S1/Recurrence/MatharA027182CentralColumns.v`
- Truth anchor: `D5/S1/Recurrence/MatharA027182CentralColumns.v_recurrence`
- Dependency: [D5/S1/Recurrence/MatharA027182SelfConvolution](MatharA027182SelfConvolution.md)
