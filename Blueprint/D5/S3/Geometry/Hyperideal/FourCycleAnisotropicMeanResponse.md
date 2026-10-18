# The transverse half-sum has an exact response

## Abstract

Mean transverse angle response for paired hyper-ideal lengths.

Use the six cosine-length entries (r,a,b,o,a,b) in the order (12,13,14,34,24,23). The target and both transverse cosine entries lie strictly between -1 and 1.

**Theorem 1.1 (Exact half-sum response).**

$$\forall r \in \mathrm{Real}, a \in \mathrm{Real}, b \in \mathrm{Real}, o \in \mathrm{Real},\; \left(1 < r \land \left(1 < a \land \left(1 < b \land \left(1 < o \land \left(-1 < cosine\left(r, a, b, o, a, b\right) \land \left(cosine\left(r, a, b, o, a, b\right) < 1 \land \left(-1 < cosine\left(a, b, r, a, b, o\right) \land \left(cosine\left(a, b, r, a, b, o\right) < 1 \land \left(-1 < cosine\left(b, a, r, b, a, o\right) \land cosine\left(b, a, r, b, a, o\right) < 1\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \frac{arccos\left(cosine\left(a, b, r, a, b, o\right)\right)+arccos\left(cosine\left(b, a, r, b, a, o\right)\right)}{2} = arctan\left(\frac{sqrt\left(a^{2}-1\right)+sqrt\left(b^{2}-1\right)}{a+b}\cdot sqrt\left(\frac{r-1}{r+1}\right)\cdot cot\left(\frac{arccos\left(cosine\left(r, a, b, o, a, b\right)\right)}{2}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/FourCycleAnisotropicMeanResponse.paired_angle_half_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For r,a,b,o>1, let theta, beta and delta be the arccosine angles of the target and two transverse edges. Their half-sum is arctan of lambda-plus times cot(theta/2), where lambda-plus is the sum of the two positive transverse radicals divided by a+b and multiplied by sqrt((r-1)/(r+1)).

The two transverse numerator-square factorizations give the positive sine sum. Their cosine sum is positive, which places the mean angle in (0,pi/2) and fixes the arctangent branch.

The statement uses only the displayed cosine formula and three angle-range premises. It does not certify a geometric tetrahedron, prove the parameter bounds, or construct a global realization.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/FourCycleAnisotropicMeanResponse.paired_angle_half_sum`
- Dependency: [D5/S3/Geometry/Hyperideal/FourCycleEnvelopes](FourCycleEnvelopes.md)
