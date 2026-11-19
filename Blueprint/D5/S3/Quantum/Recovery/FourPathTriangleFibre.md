# Four-path closed triangle fibre

## Abstract

A coupled support inequality for the original radical on the complete attained triangle.

**Definition 1.1 (The complete attained triangle).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathTriangleFibre.Triangle`

*Formalization.* `D5/S3/Quantum/Recovery/FourPathTriangleFibre.Triangle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The domain consists of all X and Y in [0,1] with sqrt(X)+sqrt(Y) at least L. Both box and trace constraints are inclusive.

**Definition 1.2 (The original normalized trace coordinate).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathTriangleFibre.Z`

*Formalization.* `D5/S3/Quantum/Recovery/FourPathTriangleFibre.Z` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Z(L,X,Y)=(L²−X−Y)/(2 sqrt(XY)). The triangle hypotheses with L>1 imply X>0 and Y>0, so this denominator is positive.

**Definition 1.3 (The original nonnegative fibre radical).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathTriangleFibre.F`

*Formalization.* `D5/S3/Quantum/Recovery/FourPathTriangleFibre.F` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

F(L,X,Y)=sqrt((1−X)(1−Y)(1−Z(L,X,Y)²)). Its radicand is nonnegative on the complete triangle when L>1 and L²≤2.

**Definition 1.4 (The box cap).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathTriangleFibre.B`

*Formalization.* `D5/S3/Quantum/Recovery/FourPathTriangleFibre.B` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

B(u)=(2−u)².

**Definition 1.5 (The trace cap).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathTriangleFibre.D`

*Formalization.* `D5/S3/Quantum/Recovery/FourPathTriangleFibre.D` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D(a,u)=a(2u−a).

**Definition 1.6 (The central fibre width).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathTriangleFibre.W`

*Formalization.* `D5/S3/Quantum/Recovery/FourPathTriangleFibre.W` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

W(a,u)=B(u)D(a,u)/u².

**Definition 1.7 (The coupled support cap).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathTriangleFibre.T`

*Formalization.* `D5/S3/Quantum/Recovery/FourPathTriangleFibre.T` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

T(a,u)=W(a,u) when u≤1, and min(B(u),D(a,u)) when u>1. The low-half value relaxes the sharper tangent cap by using kappa≥1.

**Theorem 1.8 (The exact original radical identity).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathTriangleFibre.triangle_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/FourPathTriangleFibre.triangle_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real L,X,Y with L>1, L²≤2 and (X,Y) in the complete attained triangle, X>0, Y>0 and u=X+Y>0. Put t=Y−X and a=L². Then t²<u², t²≤B(u), t²≤D(a,u), Z(L,X,Y)²≤1, and 4F(L,X,Y)²(u²−t²)=(B(u)−t²)(D(a,u)−t²).

**Theorem 1.9 (A circular relaxation on the complete triangle).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathTriangleFibre.closed_triangle_ball`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/FourPathTriangleFibre.closed_triangle_ball` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real L,X,Y with L>1, L²≤2 and (X,Y) in the complete attained triangle, (Y−X)²+(2F(L,X,Y))²≤T(L²,X+Y). The bound includes zero-width fibres without a limiting argument.

**Theorem 1.10 (Closed triangle fibre inequality).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathTriangleFibre.closed_triangle_fibre`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/FourPathTriangleFibre.closed_triangle_fibre` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real L,X,Y with L>1, L²≤2 and (X,Y) in the complete attained triangle, set a=L² and u=X+Y. Then T(a,u) and W(a,u) are nonnegative and W(a,u)(Y−X)²+T(a,u)(2F(L,X,Y))²≤T(a,u)W(a,u). No positivity assumption on T or W is imposed. The bound therefore includes vanishing-width fibres and all triangle boundaries. The proof uses the exact identity 4F²(u²−(Y−X)²)=(B−(Y−X)²)(D−(Y−X)²). For u≤1 this yields (Y−X)²+4F²≤W; for u>1 the two possible orders of B and D give the chord bound.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/FourPathTriangleFibre.B`
- Truth anchor: `D5/S3/Quantum/Recovery/FourPathTriangleFibre.D`
- Truth anchor: `D5/S3/Quantum/Recovery/FourPathTriangleFibre.F`
- Truth anchor: `D5/S3/Quantum/Recovery/FourPathTriangleFibre.T`
- Truth anchor: `D5/S3/Quantum/Recovery/FourPathTriangleFibre.Triangle`
- Truth anchor: `D5/S3/Quantum/Recovery/FourPathTriangleFibre.W`
- Truth anchor: `D5/S3/Quantum/Recovery/FourPathTriangleFibre.Z`
- Truth anchor: `D5/S3/Quantum/Recovery/FourPathTriangleFibre.closed_triangle_ball`
- Truth anchor: `D5/S3/Quantum/Recovery/FourPathTriangleFibre.closed_triangle_fibre`
- Truth anchor: `D5/S3/Quantum/Recovery/FourPathTriangleFibre.triangle_geometry`
