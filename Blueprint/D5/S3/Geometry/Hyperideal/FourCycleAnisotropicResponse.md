# The transverse half-difference retains its sign

## Abstract

Signed transverse angle response for paired hyper-ideal lengths.

Use the six cosine-length entries (r,a,b,o,a,b) in the order (12,13,14,34,24,23). The target and both transverse cosine entries lie strictly between -1 and 1.

**Theorem 1.1 (Exact half-difference response).**

$$\forall r \in \mathrm{Real}, a \in \mathrm{Real}, b \in \mathrm{Real}, o \in \mathrm{Real},\; \left(1 < r \land \left(1 < a \land \left(1 < b \land \left(1 < o \land \left(-1 < cosine\left(r, a, b, o, a, b\right) \land \left(cosine\left(r, a, b, o, a, b\right) < 1 \land \left(-1 < cosine\left(a, b, r, a, b, o\right) \land \left(cosine\left(a, b, r, a, b, o\right) < 1 \land \left(-1 < cosine\left(b, a, r, b, a, o\right) \land cosine\left(b, a, r, b, a, o\right) < 1\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \frac{arccos\left(cosine\left(a, b, r, a, b, o\right)\right)-arccos\left(cosine\left(b, a, r, b, a, o\right)\right)}{2} = arctan\left(\frac{sqrt\left(a^{2}-1\right)-sqrt\left(b^{2}-1\right)}{a+b}\cdot sqrt\left(\frac{r-1}{r+1}\right)\cdot cot\left(\frac{arccos\left(cosine\left(r, a, b, o, a, b\right)\right)}{2}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/FourCycleAnisotropicResponse.paired_angle_half_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For r,a,b,o>1, let theta, beta and delta be the arccosine angles of the target and two transverse edges. Their signed half-difference is arctan of lambda-minus times cot(theta/2), where lambda-minus is the difference of the two positive transverse radicals divided by a+b and multiplied by sqrt((r-1)/(r+1)).

The proof obtains the signed sine difference from both distinct cosine numerator-square factorizations. The half-difference lies in (-pi/2,pi/2), so the arctangent branch preserves its sign even when a<b.

The statement uses only the displayed cosine formula and three angle-range premises. It does not certify a geometric tetrahedron, establish the half-sum response, or construct a global realization.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/FourCycleAnisotropicResponse.paired_angle_half_difference`
- Dependency: [D5/S3/Geometry/Hyperideal/FourCycleEnvelopes](FourCycleEnvelopes.md)
