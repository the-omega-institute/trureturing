# Positive interior grid obstruction

## Abstract

The reduced three by three spectral grid cannot have an interior product modulus.

**Theorem 1.1 (The algebraic grid contradiction).**

$$\forall r \in \mathbb{R}, ur \in \mathbb{R}, ui \in \mathbb{R}, vr \in \mathbb{R}, vi \in \mathbb{R}, s \in \mathbb{R}, t \in \mathbb{R},\; (((((((((0 < r) \land (r < 1)) \land (ur + vr = 2)) \land (ui + vi = 0)) \land (ur \cdot s + vr \cdot t + s \cdot t + 3 - 3 \cdot \left(s + t\right) = 0)) \land (ui \cdot s + vi \cdot t = 0)) \land (s = ur^{2} + ui^{2})) \land (t = vr^{2} + vi^{2})) \land (\left(ur \cdot vr - ui \cdot vi\right)^{2} + \left(ur \cdot vi + ui \cdot vr\right)^{2} = r^{2})) \Rightarrow False$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/PositiveInteriorGridObstruction.positive_interior_grid_algebraic_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real and imaginary coordinates of two complex parameters satisfy the displayed sum and reduced second- and third-power equations. The variables s and t are their squared norms, and the final equation is the squared norm of their product. If the first imaginary coordinate is nonzero, the imaginary equation forces s and t to agree; the sum and norm equations then force the real coordinate to be one, making the product norm exceed one. If that imaginary coordinate is zero, both parameters are real and the reduced equation forces the product to have squared modulus one. Both cases contradict a product modulus strictly between zero and one.

This result is the algebraic spectral-grid bridge. It assumes the reduced equations supplied by the preceding saturation argument; it does not assert the saturation lemma, the unitary spectral realization, or any conclusion at zero, endpoint, negative, or arbitrary-density parameters.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/PositiveInteriorGridObstruction.positive_interior_grid_algebraic_obstruction`
