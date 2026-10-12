# Robin's Inequality for the Entire 11-Smooth Family

## Abstract

Robin's strict inequality holds for every 11-smooth natural number above 5040.

**Theorem 1.1 (All five exponents are unrestricted).**

$$\forall a \in \mathbb{N}, b \in \mathbb{N}, c \in \mathbb{N}, d \in \mathbb{N}, e \in \mathbb{N},\; 5040 < 2^{a} \cdot 3^{b} \cdot 5^{c} \cdot 7^{d} \cdot 11^{e} \Rightarrow \frac{sigma\left(1, 2^{a} \cdot 3^{b} \cdot 5^{c} \cdot 7^{d} \cdot 11^{e}\right)}{2^{a} \cdot 3^{b} \cdot 5^{c} \cdot 7^{d} \cdot 11^{e}} < exp\left(eulerMascheroniConstant\right) \cdot log\left(log\left(2^{a} \cdot 3^{b} \cdot 5^{c} \cdot 7^{d} \cdot 11^{e}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ElevenSmooth.robin_eleven_smooth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here sigma(1,n) is the sum of the positive divisors of n, and eulerMascheroniConstant is Euler's constant. The five exponents range over all natural numbers, including zero. The sole hypothesis is that their product n exceeds 5040. No Riemann Hypothesis premise is used.

When the exponent of 11 is zero the statement is the frozen seven-smooth theorem, which is applied directly. Otherwise multiplicativity and the finite geometric-sum formula bound sigma(1,n)/n strictly by 77/16. For n at least 2^22, frozen rational logarithm bounds give log(log(n)) > 271/100, and a Taylor lower bound gives exp(gamma) > 89/50, so the capacity exceeds 77/16.

Below 2^22 the product bound forces the exponents into the box a<22, b<14, c<10, d<8, e<7. For each exponent 1<=e<=6 a private kernel-checked integer calculation gives ratio bounds 375/100, 387/100, 406/100, 419/100, 426/100, 440/100 and 455/100 on the intervals separated by 10000, 20000, 40000, 80000, 160000 and 640000. Private logarithm bounds 1071/500, 111/50, 229/100, 1179/500, 121/50, 62/25 and 259/100 for log(log(t)) at the left end t of each interval finish these cases. The finite range contains 3212 eleven-smooth integers above 5040, 1699 of them divisible by 11.

The theorem enlarges the certified core used by prime replacement: every integer above 5040 whose prime support has at most five primes and whose compression to the first five primes exceeds 5040 is reached from this family by replacing primes with larger ones. It does not cover integers with six or more distinct prime factors, and the Riemann hypothesis remains open.

## References

- Truth anchor: `D5/S3/Arith/Robin/ElevenSmooth.robin_eleven_smooth`
- Dependency: [D5/S3/Arith/Robin/SevenSmooth](SevenSmooth.md)
