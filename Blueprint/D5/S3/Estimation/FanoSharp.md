# Sharp Finite Fano Inequality in Nats

## Abstract

Sharp finite Fano inequality replaces the frozen weak cardinality correction by the off-estimator cardinality and verifies consistency on their common range.

**Theorem 1.1 (Sharp Fano uses the off-estimator cardinality).**

$$\begin{gathered}\forall Y, X\ [\operatorname{Fintype}(Y)] [\operatorname{Fintype}(X)],\\\forall p: Y\times X\to \mathbb{R}, g: Y\to X,\\e:=\sum _{y, x: g(y)\neq x} p(y, x),\\((\forall y, x, 0\le p(y, x)) \land \sum _{y, x} p(y, x)=1) \land \operatorname{card}(X)\neq 1 \Rightarrow \\\operatorname{conditionalEntropy}(p)\le \operatorname{shannonEntropy}((b: \operatorname{Bool})\mapsto \text{if b then }e\text{ else }1-e)+ e \log (\operatorname{card}(X)-1).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/FanoSharp.fano_inequality_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This theorem sharpens the frozen weak Fano inequality by replacing log(card X) with log(card X - 1). The latter counts only values that can differ from the estimator and is the form used in converse arguments. The weak theorem and its derivation remain frozen and are referenced rather than restated.

The exclusion card X != 1 is a deliberate refusal to make the sharp statement range silently over the singleton. At card X = 1 its right-hand side contains Real.log 0, which Lean totalizes to zero. A claim over that case would therefore rest on totalization rather than on the analytic argument. This is precisely why the preceding wave declined to state the sharp form.

The hypothesis is exactly the diagnosed obstruction and nothing more. Normalization supplies Nonempty X: because the total mass is one, some summand is nonzero and hence supplies an element of Y x X. Once cardinality one is ruled out, positivity of the finite cardinality gives 1 < card X. Consequently (card X : R) - 1 is nonzero, which is the condition required for the logarithm step.

The singleton exclusion is documented by machine rather than merely by prose. A compiled witness takes Y = X = Unit, the unit-mass joint law, and the unique estimator, and evaluates the entire sharp right-hand side to zero. In particular, the witness records the totalized evaluation Real.log(card Unit - 1) = Real.log 0 = 0; it is not used to extend the theorem to the excluded case.

The proof uses the same finite, nats-valued entropy infrastructure as the frozen result, but the error reference measure is supported only on points away from the estimator. Its total mass is card X - 1, and the frozen log-sum inequality then yields the sharper correction. No derivation of the weak form is repeated.

The improvement is strict in a concrete finite model. Let Y = Unit, let X = Bool, take the uniform joint law, and use a constant estimator. Then e = 1/2 and card X = 2. The sharp correction is (1/2) log 1 = 0, whereas the weak correction is (1/2) log 2 > 0. Thus the sharp bound's correction term vanishes entirely for a binary estimand.

All quantities are measured in nats. No binary-entropy definition is introduced: the two-point term is the shannonEntropy of a Bool law, exactly as in the frozen weak statement. The repository's bits-valued binaryEntropyBits remains unused for the unit-mismatch reason recorded in the weak form's document.

The theorem claims no converse direction, minimax or sample-complexity corollary, equality characterization, or measure-theoretic analogue. Its scope is the finite sharp upper bound under the exact singleton exclusion displayed above.

**Theorem 1.2 (The sharp Fano right-hand side implies the weak one).**

$$\begin{gathered}\forall X\ [\operatorname{Fintype}(X)], \forall e \in \mathbb{R},\\0\le e \land 1< \operatorname{card}(X) \Rightarrow \\\operatorname{shannonEntropy}((b: \operatorname{Bool})\mapsto \text{if b then }e\text{ else }1-e)+ e \log (\operatorname{card}(X)-1)\le \\\operatorname{shannonEntropy}((b: \operatorname{Bool})\mapsto \text{if b then }e\text{ else }1-e)+ e \log \operatorname{card}(X).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/FanoSharp.fano_sharp_rhs_le_weak_rhs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The named theorem fano_sharp_rhs_le_weak_rhs proves that the sharp right-hand side is at most the frozen weak right-hand side whenever the error mass is nonnegative and 1 < card X. This obligation is part of the sharpening: a proposed stronger statement that failed to imply the result it sharpens would expose an error in the new statement. The overlap between old and new results is the least costly place to detect such an error, so the two bounds are proved visibly consistent rather than left merely to coexist.

## References

- Truth anchor: `D5/S3/Estimation/FanoSharp.fano_inequality_sharp`
- Truth anchor: `D5/S3/Estimation/FanoSharp.fano_sharp_rhs_le_weak_rhs`
- Dependency: [D5/S3/Estimation/Fano](Fano.md)
