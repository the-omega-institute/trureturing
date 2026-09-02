# Golden Jones Matching

## Abstract

The golden square is the first nonintegral low Jones value and the Fibonacci dimension.

**Theorem 1.1 (The golden square is the first nonintegral low Jones value).**

$$let J(n) = 4 \cdot \operatorname{cos}\left(\frac{\pi}{n}\right)^{2}; \left(\left(\left(\left(\left(\left(\left(\left(\left(\left(J\left(3\right) = 1 \land J\left(4\right) = 2\right) \land J\left(5\right) = \phi^{2}\right) \land J\left(6\right) = 3\right) \land \phi^{2} = \frac{3 + \operatorname{sqrt}\left(5\right)}{2}\right) \land 2 < \phi^{2}\right) \land \phi^{2} < 3\right) \land \frac{13}{5} < \phi^{2}\right) \land \phi^{2} < \frac{131}{50}\right) \land \left(\forall n \in \operatorname{Natural}\left(\right),\; \left(3 \le n \land n < 5\right) \Rightarrow \left(\exists m \in \operatorname{Integer}\left(\right),\; J\left(n\right) = m\right)\right)\right) \land \left(\neg \left(\exists m \in \operatorname{Integer}\left(\right),\; J\left(5\right) = m\right)\right)\right) \land \left(\forall d \in \operatorname{Real}\left(\right),\; \left(0 < d \land d^{2} = 1 + d\right) \Rightarrow \left(d = \phi \land d^{2} = \phi^{2}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenCoding/GoldenJonesMatching.golden_jones_matching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For J(n)=4 cos^2(pi/n), the four explicit values at n=3,4,5,6 are 1, 2, phi^2, and 3. The central identity uses the repository's pentagon cosine theorem rather than reproving the special value.

The radical identity phi^2=(3+sqrt(5))/2 yields both 2<phi^2<3 and the sharper enclosure 2.6<phi^2<2.62. Irrationality of phi then shows that J(5) is not an integer, while the only earlier indices n>=3 are n=3 and n=4 and have explicit integer witnesses.

The source also describes the self-dual Fibonacci fusion rule. Because the source supplies no category, tensor product, unit, or dimension map, the formal statement records its exact decategorified numerical consequence: every positive d satisfying d^2=1+d equals phi and has squared dimension phi^2.

## References

- Truth anchor: `D5/S3/Observer/GoldenCoding/GoldenJonesMatching.golden_jones_matching`
- Dependency: [D5/S1/FixedPoints/Algebraic/GoldenFixedPoint](../../../S1/FixedPoints/Algebraic/GoldenFixedPoint.md)
- Dependency: [D5/S3/Constants/PentagonCosines](../../Constants/PentagonCosines.md)
