# Paired local angle demand and flat transverse gap

## Abstract

Local angle demand and a flat-branch length gap for paired hyper-ideal lengths.

Use the local order (12,13,14,34,24,23) and the exact cosine function from FourCycleEnvelopes. The tuple is (r,a,b,o,a,b). The first result assumes three genuine angle ranges; the second uses the raw cosine inequalities of a transverse flat choice.

**Theorem 1.1 (A strict demand without a common transverse width).**

$$\forall r \in \mathrm{Real}, a \in \mathrm{Real}, b \in \mathrm{Real}, o \in \mathrm{Real},\; \left(1 < r \land \left(1 < a \land \left(1 < b \land \left(1 < o \land \left(1+a+b \le r \land \left(-1 < cosine\left(r, a, b, o, a, b\right) \land \left(cosine\left(r, a, b, o, a, b\right) < 1 \land \left(-1 < cosine\left(a, b, r, a, b, o\right) \land \left(cosine\left(a, b, r, a, b, o\right) < 1 \land \left(-1 < cosine\left(b, a, r, b, a, o\right) \land cosine\left(b, a, r, b, a, o\right) < 1\right)\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \pi < 2\cdot arccos\left(cosine\left(r, a, b, o, a, b\right)\right)+arccos\left(cosine\left(a, b, r, a, b, o\right)\right)+arccos\left(cosine\left(b, a, r, b, a, o\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/FourCycleLocalAngleDemand.paired_angle_demand` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For r,a,b,o>1 with r>=1+a+b, assume each of the three displayed cosine values lies strictly between -1 and 1. The target angle theta and transverse angles beta,delta then satisfy 2theta+beta+delta>pi. No acute-target restriction or bound on the ratio a/b is used.

The proof derives the paired cosine and sine identities from the six-variable formula, a strict positive slack for the half-angle tangent, and a coupled lower bound for the transverse parameter. The final comparison covers both obtuse and acute target angles.

This analytic statement assumes only the three cosine ranges it uses. It does not establish the range of the distinct opposite-edge cosine, certify a genuine geometric tetrahedron, construct face pairings, or prove global hyperbolic realization.

**Theorem 1.2 (The selected transverse length is larger).**

$$\forall r \in \mathrm{Real}, a \in \mathrm{Real}, b \in \mathrm{Real}, o \in \mathrm{Real},\; \left(1 < r \land \left(1 < a \land \left(1 < b \land \left(1 < o \land \left(1 \le cosine\left(r, a, b, o, a, b\right) \land \left(cosine\left(a, b, r, a, b, o\right) \le -1 \land 1 \le cosine\left(b, a, r, b, a, o\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(b < a \land sqrt\left((r+1)\cdot (o+1)\right) \le a-b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/FourCycleLocalAngleDemand.flat_transverse_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For r,a,b,o>1, selecting the a,a transverse pi pair forces a>b and a-b at least sqrt((r+1)(o+1)). Swapping a and b gives the opposite choice.

The squared gap follows from the axial cosine; the direction follows from the difference of the transverse numerators and positivity of their common denominator.

These are implications between raw cosine values. They do not construct a flat tetrahedron, a face pairing, or a global zero-curvature assignment.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/FourCycleLocalAngleDemand.flat_transverse_gap`
- Truth anchor: `D5/S3/Geometry/Hyperideal/FourCycleLocalAngleDemand.paired_angle_demand`
- Dependency: [D5/S3/Geometry/Hyperideal/FourCycleEnvelopes](FourCycleEnvelopes.md)
