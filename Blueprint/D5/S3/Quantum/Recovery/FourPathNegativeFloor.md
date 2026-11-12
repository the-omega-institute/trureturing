# Four-path negative full-triangle lower bound

## Abstract

The original negative defect is strictly greater than 23/50 on the whole closed Section 71 triangle.

**Definition 1.1 (The constant h).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathNegativeFloor.h`

*Formalization.* `D5/S3/Quantum/Recovery/FourPathNegativeFloor.h` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

h=1/sqrt(2).

**Definition 1.2 (The constant c).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathNegativeFloor.c`

*Formalization.* `D5/S3/Quantum/Recovery/FourPathNegativeFloor.c` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

c=cos(pi/8).

**Definition 1.3 (The constant s).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathNegativeFloor.s`

*Formalization.* `D5/S3/Quantum/Recovery/FourPathNegativeFloor.s` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

s=sin(pi/8).

**Definition 1.4 (The trace threshold).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathNegativeFloor.L`

*Formalization.* `D5/S3/Quantum/Recovery/FourPathNegativeFloor.L` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real q, L(q)=19/16+q/2.

**Definition 1.5 (The fixed negative-row R radical).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathNegativeFloor.R`

*Formalization.* `D5/S3/Quantum/Recovery/FourPathNegativeFloor.R` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real q,X,Y, R(q,X,Y)=sqrt(s²X+h²Y+sh(L(q)²−X−Y)). The order of X and Y is the negative row of Definition 57.1.

**Definition 1.6 (The fixed negative-row C radical).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathNegativeFloor.C`

*Formalization.* `D5/S3/Quantum/Recovery/FourPathNegativeFloor.C` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real q,X,Y, C(q,X,Y)=sqrt(c²(1−X)+h²(1−Y)+2chF(L(q),X,Y)). F retains the original normalized Z radical.

**Definition 1.7 (The shared-feedback response).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathNegativeFloor.Gamma`

*Formalization.* `D5/S3/Quantum/Recovery/FourPathNegativeFloor.Gamma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real q,X,Y, Gamma(q,X,Y)=sqrt(1−q) R(q,X,Y)+sqrt(q) C(q,X,Y). Both terms use the same X,Y and the same original fibre radical.

**Definition 1.8 (The negative-row energy).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathNegativeFloor.E`

*Formalization.* `D5/S3/Quantum/Recovery/FourPathNegativeFloor.E` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real q, E(q)=(2(h+s))²(1−q)+(2(h+c))²q. These are the original e² and d² coefficients.

**Definition 1.9 (The original negative defect).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathNegativeFloor.G`

*Formalization.* `D5/S3/Quantum/Recovery/FourPathNegativeFloor.G` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real q,X,Y, G(q,X,Y)=E(q)−4Gamma(q,X,Y)². This is the negative row G_- of Definition 57.1, with all square roots on their nonnegative branches.

**Theorem 1.10 (The full Continuation VI Theorem 71.1).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathNegativeFloor.negative_floor`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/FourPathNegativeFloor.negative_floor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real q in [11/100,23/200] and every real X,Y in [0,1] with sqrt(X)+sqrt(Y)≥19/16+q/2, G(q,X,Y)>23/50. All triangle edges and degenerate fibres remain in scope. The estimate is a strict real lower bound. The proof preserves the fixed labels: it bounds the linear term in Y−X directly, without swapping the original inputs. Young’s inequality bounds Gamma² by alpha R²+beta C² for alpha=1−q+(13/10)sqrt((1−q)q) and beta=q+(10/13)sqrt((1−q)q). The original radical identities and the closed triangle ball inequality give a support term bounded by sqrt((185961/1250000)T). The seven rational comparisons are consumed after splitting the interval [1,11/10] at 21/20. On [1,21/20], T≤539/625; on [21/20,11/10], T≤361/400 and the radical bound 367/1000 combines with the nonradical bound at 21/20. This yields Gamma²<49359/40000. The independently derived strict energy inequality 49359/40000<(E(q)−23/50)/4 then gives the result. This is an application of the repository’s original scalar defect model; no physical realization or literature novelty is asserted.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/FourPathNegativeFloor.C`
- Truth anchor: `D5/S3/Quantum/Recovery/FourPathNegativeFloor.E`
- Truth anchor: `D5/S3/Quantum/Recovery/FourPathNegativeFloor.G`
- Truth anchor: `D5/S3/Quantum/Recovery/FourPathNegativeFloor.Gamma`
- Truth anchor: `D5/S3/Quantum/Recovery/FourPathNegativeFloor.L`
- Truth anchor: `D5/S3/Quantum/Recovery/FourPathNegativeFloor.R`
- Truth anchor: `D5/S3/Quantum/Recovery/FourPathNegativeFloor.c`
- Truth anchor: `D5/S3/Quantum/Recovery/FourPathNegativeFloor.h`
- Truth anchor: `D5/S3/Quantum/Recovery/FourPathNegativeFloor.negative_floor`
- Truth anchor: `D5/S3/Quantum/Recovery/FourPathNegativeFloor.s`
- Dependency: [D5/S3/Quantum/Recovery/FourPathFloorCertificate](FourPathFloorCertificate.md)
- Dependency: [D5/S3/Quantum/Recovery/FourPathTriangleFibre](FourPathTriangleFibre.md)
