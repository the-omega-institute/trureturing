# Robin's Inequality for the Entire 7-Smooth Family

## Abstract

Robin's strict inequality holds for every 7-smooth natural number above 5040.

**Theorem 1.1 (All four exponents are unrestricted).**

$$\forall a \in \mathbb{N}, b \in \mathbb{N}, c \in \mathbb{N}, d \in \mathbb{N},\; 5040 < 2^{a} \cdot 3^{b} \cdot 5^{c} \cdot 7^{d} \Rightarrow \frac{sigma\left(1, 2^{a} \cdot 3^{b} \cdot 5^{c} \cdot 7^{d}\right)}{2^{a} \cdot 3^{b} \cdot 5^{c} \cdot 7^{d}} < exp\left(eulerMascheroniConstant\right) \cdot log\left(log\left(2^{a} \cdot 3^{b} \cdot 5^{c} \cdot 7^{d}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/SevenSmooth.robin_seven_smooth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here sigma(1,n) is the sum of the positive divisors of n, and eulerMascheroniConstant is Euler's constant. The four exponents range over all natural numbers, including zero. The sole hypothesis is that their product n exceeds 5040, which also makes n and log n positive. No Riemann Hypothesis premise is used.

Multiplicativity and the finite geometric-sum formula bound sigma(1,n)/n strictly by 35/8. For n at least 131072, frozen logarithm bounds, a Taylor lower bound for exp of Euler's constant, and monotonicity of log log establish the analytic tail.

Below 131072, the product bound forces the exponents into a finite box. A private kernel-checked integer calculation gives ratio bounds 381/100, 197/50 and 407/100 on the intervals separated by 10000 and 20000. Private logarithm bounds finish these cases. Only this universal theorem is public; the enumeration is internal to its proof.

## References

- Truth anchor: `D5/S3/Arith/Robin/SevenSmooth.robin_seven_smooth`
- Dependency: [D5/S3/Arith/GoldenResource/RobinRationalBasis](../GoldenResource/RobinRationalBasis.md)
