# Main-edge dominance forces transverse angle demand

## Abstract

Strict local angle demand for a paired hyper-ideal cosine tuple.

Use the local order (12,13,14,34,24,23) and the exact cosine function from FourCycleEnvelopes. The tuple is (r,a,b,o,a,b). The three cosine-range assumptions below concern the target angle and the two distinct transverse angles.

**Theorem 1.1 (A strict demand without a common transverse width).**

$$\forall r \in \mathrm{Real}, a \in \mathrm{Real}, b \in \mathrm{Real}, o \in \mathrm{Real},\; \left(1 < r \land \left(1 < a \land \left(1 < b \land \left(1 < o \land \left(1+a+b \le r \land \left(-1 < cosine\left(r, a, b, o, a, b\right) \land \left(cosine\left(r, a, b, o, a, b\right) < 1 \land \left(-1 < cosine\left(a, b, r, a, b, o\right) \land \left(cosine\left(a, b, r, a, b, o\right) < 1 \land \left(-1 < cosine\left(b, a, r, b, a, o\right) \land cosine\left(b, a, r, b, a, o\right) < 1\right)\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \pi < 2\cdot arccos\left(cosine\left(r, a, b, o, a, b\right)\right)+arccos\left(cosine\left(a, b, r, a, b, o\right)\right)+arccos\left(cosine\left(b, a, r, b, a, o\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/FourCycleLocalAngleDemand.paired_angle_demand` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For r,a,b,o>1 with r>=1+a+b, assume each of the three displayed cosine values lies strictly between -1 and 1. The target angle theta and transverse angles beta,delta then satisfy 2theta+beta+delta>pi. No acute-target restriction or bound on the ratio a/b is used.

The proof derives the paired cosine and sine identities from the six-variable formula, a strict positive slack for the half-angle tangent, and a coupled lower bound for the transverse parameter. The final comparison covers both obtuse and acute target angles.

This analytic statement assumes only the three cosine ranges it uses. It does not establish the range of the distinct opposite-edge cosine, certify a genuine geometric tetrahedron, construct face pairings, or prove global hyperbolic realization.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/FourCycleLocalAngleDemand.paired_angle_demand`
- Dependency: [D5/S3/Geometry/Hyperideal/FourCycleEnvelopes](FourCycleEnvelopes.md)
