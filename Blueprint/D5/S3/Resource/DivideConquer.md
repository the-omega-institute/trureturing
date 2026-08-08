# The Divide-Conquer Lemma for Resource Functionals

## Abstract

Subadditivity of infimum-defined resource functionals under feasible additive product strategies.

**Theorem 1.1 (Tensor-closed infimum resource functionals are subadditive).**

$$\begin{gathered}F(X):= \operatorname{inf}_{s: \operatorname{feasible}(s, X)} c(s),\\(\operatorname{feasible}(s_{X}, X) \land \operatorname{feasible}(s_{Y}, Y) \Rightarrow \operatorname{feasible}(\operatorname{tensorStrat}(s_{X}, s_{Y}), \operatorname{tensorObj}(X, Y))) \land \\(c(\operatorname{tensorStrat}(s_{X}, s_{Y}))=c(s_{X})+c(s_{Y})) \Rightarrow\\F(\operatorname{tensorObj}(X, Y)) \le F(X)+F(Y).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/DivideConquer.resource_functional_subadditive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Obj be a type of resource objects and Strat a type of strategies. The data include tensorObj on objects, tensorStrat on strategies, a feasibility predicate, and a cost valued in the extended nonnegative reals. The two structural hypotheses are explicit: tensorStrat(sX,sY) is feasible for tensorObj(X,Y) whenever sX and sY are feasible for X and Y, and its cost is exactly c(sX)+c(sY). The functional F is the infimum of c over the feasible-strategy subtype.

For every feasible pair sX and sY, the product strategy is an admissible competitor for tensorObj(X,Y). Therefore F(tensorObj(X,Y)) is at most c(tensorStrat(sX,sY)), which the additive-cost hypothesis identifies with c(sX)+c(sY). Mathlib's ENNReal.le_iInf_add_iInf then takes both infima and yields the displayed subadditivity inequality. Since costs lie in the extended nonnegative reals, an empty feasible class has value infinity; the same lattice lemma covers that boundary without an auxiliary nonemptiness or boundedness assumption.

## References

- Truth anchor: `D5/S3/Resource/DivideConquer.resource_functional_subadditive`
