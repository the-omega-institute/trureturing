# Lonely Runner: Fourteen of Twenty

## Abstract

A reflected finite certificate supplies a rational lonely time for every fourteen speeds chosen from one through twenty.

**Theorem 1.1 (Rational torus distance is an exact residue window).**

$$\begin{aligned}\forall s, a, d \in \mathbb{N}, 0 < d \Rightarrow \\\frac{1}{15} \leq \operatorname{torusDist}(s \cdot \frac{a}{d}) \iff \\d \leq 15 \cdot (s \cdot a \operatorname{mod} d) \land 15 \cdot (s \cdot a \operatorname{mod} d) \leq 14 \cdot d.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/LonelyRunnerFourteenOfTwenty.torusDist_nat_ratio_ge_iff_nat_residue_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural s, a, and positive d, Mathlib's fractional-part division identity rewrites the torus distance at time a/d as the residue of sa modulo d divided by d. Clearing the positive denominator gives the two natural-number window inequalities exactly.

This equivalence is the arithmetic bridge used by every reflected mask computation below; it is not a restatement of the final existence claim.

**Theorem 1.2 (Fifteen masks cover every fourteen-speed selection).**

$$\begin{aligned}\operatorname{safeMask}(\frac{1}{11}) = speedUniverse \setminus \{11\} \land\\\operatorname{safeMask}(\frac{1}{12}) = speedUniverse \setminus \{12\} \land\\\operatorname{safeMask}(\frac{1}{13}) = speedUniverse \setminus \{13\} \land\\\operatorname{safeMask}(\frac{1}{14}) = speedUniverse \setminus \{14\} \land\\\operatorname{safeMask}(\frac{1}{15}) = speedUniverse \setminus \{15\} \land\\\operatorname{safeMask}(\frac{1}{22}) = speedUniverse \setminus \{1\} \land\\\operatorname{safeMask}(\frac{11}{23}) = speedUniverse \setminus \{2\} \land\\\operatorname{safeMask}(\frac{6}{25}) = speedUniverse \setminus \{4\} \land\\\operatorname{safeMask}(\frac{8}{25}) = speedUniverse \setminus \{3\} \land\\\operatorname{safeMask}(\frac{5}{26}) = speedUniverse \setminus \{5\} \land\\\operatorname{safeMask}(\frac{4}{29}) = speedUniverse \setminus \{7\} \land\\\operatorname{safeMask}(\frac{5}{29}) = speedUniverse \setminus \{6\} \land\\\operatorname{safeMask}(\frac{11}{29}) = speedUniverse \setminus \{8\} \land\\\operatorname{safeMask}(\frac{1}{9}) = speedUniverse \setminus \{9, 18\} \land\\\operatorname{safeMask}(\frac{1}{10}) = speedUniverse \setminus \{10, 20\} \land\\\operatorname{powersetCard}(6, residualSpeeds) \subseteq residualCoveredSixSubsets \land\\\forall S: \operatorname{Finset}(\mathbb{N}), (S \subseteq speedUniverse \land \lvert S \rvert = 14) \Rightarrow \exists (t, M) \in certificate, S \subseteq M.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/LonelyRunnerFourteenOfTwenty.certificate_package` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first fifteen conjuncts are the exact safe masks at the listed rational times. Each equality is checked by kernel reduction after transport through the residue-window theorem.

The next conjunct exhausts the seven six-element subsets of the residual seven-speed set. The last conjunct lifts those computations by a complement argument to every fourteen-element subset of the full twenty-speed universe.

**Theorem 1.3 (Every fourteen of the twenty speeds have a rational lonely time).**

$$\begin{aligned}\forall S: \operatorname{Finset}(\mathbb{N}), (S \subseteq speedUniverse \land \lvert S \rvert = 14) \Rightarrow \\\exists t \in \mathbb{Q}, 0 \leq t \leq 1, \\\forall s \in S, \frac{1}{15} \leq \operatorname{torusDist}(s \cdot t).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/LonelyRunnerFourteenOfTwenty.lonely_runner_fourteen_of_twenty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every fourteen-element subset S of speeds one through twenty, the finite certificate supplies a rational time in the unit interval whose exact safe mask contains S. Membership in that mask gives torus distance at least 1/15 for every selected speed.

The theorem covers all 38,760 such subsets through the structured complement proof; it does not rely on the impractical direct powerset reduction and does not assert the unrestricted Lonely Runner conjecture.

## References

- Truth anchor: `D5/S1/Phase/LonelyRunnerFourteenOfTwenty.certificate_package`
- Truth anchor: `D5/S1/Phase/LonelyRunnerFourteenOfTwenty.lonely_runner_fourteen_of_twenty`
- Truth anchor: `D5/S1/Phase/LonelyRunnerFourteenOfTwenty.torusDist_nat_ratio_ge_iff_nat_residue_window`
