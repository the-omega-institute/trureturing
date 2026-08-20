# Prime Blindness

## Abstract

Primality of the inputs does not determine the golden Beatty deficit.

The deficit is already known not to be determined by any fixed modulus. The companion claim is that it is equally blind to primality, and the statement here has the same shape: two witness pairs whose inputs are all prime, whose deficits differ.

Stating it as a witness rather than as a property of the definition is deliberate. The source phrases the claim as the definition containing no primes, which is a remark about how the definition is written and not a proposition about the function. A witness pair is the mathematical content of that remark: no classification by primality can pin a value that two all-prime pairs already disagree on.

**Theorem 1.1 (Primality does not determine the Beatty deficit).**

$$c(2, 2) \neq c(2, 3), \operatorname{all} \operatorname{prime}.$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Blindness/PrimeBlindness.beattyDeficit_not_determined_by_primality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The witnesses are the two smallest all-prime pairs with distinct deficits; the shift values are read through the public displacement decode bridge rather than from a square-root bracket.

## References

- Truth anchor: `D5/S1/Deficit/Blindness/PrimeBlindness.beattyDeficit_not_determined_by_primality`
- Dependency: [D5/S1/Deficit/GoldenPhaseDeficit](../GoldenPhaseDeficit.md)
- Dependency: [D5/S1/Deficit/ZeckendorfDisplacementReading](../ZeckendorfDisplacementReading.md)
