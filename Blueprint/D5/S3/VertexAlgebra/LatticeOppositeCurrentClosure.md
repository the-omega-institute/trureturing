# All-Frequency Actual Opposite-Current Closure

## Abstract

Every negative-current insertion has the exact two reversed finite opposite coefficient sums.

Let b have actual integer grade h and let r>=1. Write A_i(q) for the original neutral current and O_b(n) for the finite actual opposite coefficient. Both H*gramComplex(D)=1 and gramComplex(D)*H=1 are required. D may have indefinite signature; h may be negative. The original all-charge finite-support Carrier(D), its oscillator operators and reconstructed Y are retained. No form, primary-state condition, generator-adjoint law, occupation cutoff or arbitrary-signature finite-dimensional energy fiber is assumed.

**Definition 1.1 (Linearity of the true finite opposite coefficient).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOppositeCurrentClosure.oppositeLinear`

*Formalization.* `D5/S3/VertexAlgebra/LatticeOppositeCurrentClosure.oppositeLinear` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At fixed h and n, the actual opposite coefficient is a linear map from the original carrier to its endomorphisms. The state-dependent cutoff is removed using the proved finite descendant support; additions and scalar actions use supported sums.

**Theorem 1.2 (Every actual negative-current insertion).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOppositeCurrentClosure.opposite_current_insertion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeOppositeCurrentClosure.opposite_current_insertion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With C_r(t)=choose(t+r-1,r-1), O_(A_i(-r)b)(n)v equals minus sum_t C_r(t)O_b(n+t)A_i(t+r)v plus (-1)^r sum_s C_r(s)A_i(-s)O_b(n-s-r)v. Both sums have actual pointwise finite support on v. The second contains s=0, with the exact charged-current correction. Frequency one follows from the original residue reconstruction and actual p=0 mode commutator. The derivative identity and [T,A_i(-r)]=r A_i(-r-1) extend the result by induction. The upstream binomial coefficient recurrences normalize both reversed sums; their finite supports are established before the zero term is removed and the first tail is shifted. This closes the form-independent insertion relation, not ghost-Q adjoints, no-ghost, Monster realization or string and AdS/CFT theories.

**Theorem 1.3 (The grade of a negative-current insertion).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOppositeCurrentClosure.current_insertion_grade`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeOppositeCurrentClosure.current_insertion_grade` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If b lies in actual integer grade h, then A_i(-r)b lies in grade h+r for every r>=1. Both inverse Gram equations are retained. The actual L0 eigenformula and current commutator give this result on the full carrier, with no positive-signature restriction. It supplies the finite-word induction for native descendant contravariance.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeOppositeCurrentClosure.current_insertion_grade`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOppositeCurrentClosure.oppositeLinear`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOppositeCurrentClosure.opposite_current_insertion`
- Dependency: [D5/S3/VertexAlgebra/LatticeOppositeDerivative](LatticeOppositeDerivative.md)
