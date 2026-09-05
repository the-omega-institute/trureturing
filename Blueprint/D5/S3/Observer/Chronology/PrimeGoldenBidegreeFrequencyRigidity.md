# Prime-Golden Bidegree Frequency Rigidity

## Abstract

In one prime channel, irrational golden frequency faithfully recovers the prime-event and short-step counts.

**Theorem 1.1 (Real frequency recovers the bidegree count ledger).**

$$\begin{gathered}\forall p: Nat.Primes,\\{}\operatorname{Injective}(\operatorname{bidegreeFrequency}(p)) \land\\{}\forall u, w, \operatorname{isSinglePrimeWord}(p, u) \Rightarrow \operatorname{isSinglePrimeWord}(p, w) \Rightarrow\\{}\operatorname{totalStepFrequency}(u) = \operatorname{totalStepFrequency}(w) \Rightarrow \operatorname{primeGoldenBidegree}(u) = \operatorname{primeGoldenBidegree}(w).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/PrimeGoldenBidegreeFrequencyRigidity.prime_golden_bidegree_frequency_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For fixed prime p, the scalar frequency of bidegree (k,s) is (k phi^2 - s) log p.

The nonzero prime logarithm and irrationality of the golden ratio make this map injective on natural-number bidegrees.

The result recovers event count and short-step count, while chronology within the recovered bidegree remains outside the scalar frequency readout.

## References

- Truth anchor: `D5/S3/Observer/Chronology/PrimeGoldenBidegreeFrequencyRigidity.prime_golden_bidegree_frequency_rigidity`
- Dependency: [D5/S1/Phase/Basic](../../../S1/Phase/Basic.md)
- Dependency: [D5/S3/Observer/Chronology/PrimeGoldenBigradedChronologicalSignature](PrimeGoldenBigradedChronologicalSignature.md)
