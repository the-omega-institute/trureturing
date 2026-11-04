# A centered-ceiling counterexample for the original return threshold

## Abstract

The complete original odd-wrap return criterion at p=57425 separates the true threshold from the proposed centered ceiling.

**Theorem 1.1 (The original threshold is 55310 while the centered ceiling is 55311).**

Lean statement: `D5/S3/FiniteGroups/BajnokBeattyOddWrapCenteredCeilingCounterexample.original_centered_ceiling_counterexample`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BajnokBeattyOddWrapCenteredCeilingCounterexample.original_centered_ceiling_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At p=57425 the theorem states the full original sign criterion with T=55310: for every natural 2<=t<55310, W33<W19; at t=55310, W19<=W33; and for every natural t>55310, W19<W33. Each W value is the corresponding component of original_return_pair at the original source length (p*(6t-1)).toNat, and no giant binomial enumeration is used. At T the formalized statement records only W19<=W33, so no equality at T is asserted. Meanwhile Int.ceil(alpha*57425+1/6)=55311.

The quantitative root control uses private exact 17-term exponential certificates P17(x)=sum_{m<17} x^m/m! and U17(x)=P17(x)+x^17*18/(17!*17), with P17(x)<=exp x<=U17(x) on [0,1]. For G(x)=gaussian(x), they imply P17(x)+U17(x)^(-9)<=G(x)<=U17(x)+P17(x)^(-9); strict Gaussian monotonicity then gives 963166449/1e9<alpha<963166449003/1e12. These are finite exact inequalities for the same order-nine Perron-defined alpha.

Applying the complete original threshold bracket alpha*p+1/6-1/(6p)<T<=ceil(alpha*p+1/6-1/(25p)) at p=57425, exact arithmetic gives 55309<T<=55310 and hence T=55310. Thus the centered ceiling 55311 is a counterexample to the proposed exact universal ceiling formula.

**Theorem 1.2 (The universal exact centered-ceiling formula is false).**

Lean statement: `D5/S3/FiniteGroups/BajnokBeattyOddWrapCenteredCeilingCounterexample.result`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BajnokBeattyOddWrapCenteredCeilingCounterexample.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The claim requires every odd integer p>=5 to have a natural T>2 satisfying the complete original before/at/after return criterion and T=Int.ceil(alpha*p+1/6). Its literal negation follows from the same certified p=57425 example: the claim would force T=55311 and W33<W19 at t=55310, contradicting the proved W19<=W33 there. The same exact threshold theorem supplies this contradiction.

## References

- Truth anchor: `D5/S3/FiniteGroups/BajnokBeattyOddWrapCenteredCeilingCounterexample.original_centered_ceiling_counterexample`
- Truth anchor: `D5/S3/FiniteGroups/BajnokBeattyOddWrapCenteredCeilingCounterexample.result`
- Dependency: [D5/S3/FiniteGroups/BajnokBeattyOddWrapGaussianRoot](BajnokBeattyOddWrapGaussianRoot.md)
- Dependency: [D5/S3/FiniteGroups/BajnokBeattyOddWrapThresholdBracket](BajnokBeattyOddWrapThresholdBracket.md)
