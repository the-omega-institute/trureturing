# Conditional Complexity Floor

## Abstract

A nonempty class with bounded realizing programs gives a conditional complexity floor.

**Theorem 1.1 (A bounded realizing program gives the floor inequality).**

$$\operatorname{Nonempty}(\operatorname{BudgetedRealizers}(realizes, length, Q)) \land (\forall f, p, realizes(f, p) \Rightarrow conditionalComplexity \le length(p) + c) \Rightarrow conditionalComplexity - c \le Q.$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/ConditionalComplexityFloor.conditional_complexity_floor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

BudgetedRealizers contains exactly those class members having a realizing program whose natural-number length is at most Q. Nonemptiness therefore supplies both a member and a bounded witness program.

The fixed-overhead compiler premise records the source decoding construction: every realizing program yields a conditional description whose length is at most the program length plus c. Applying it to the extracted witness and then using the budget gives the displayed floor inequality.

The bound on the witness program lifts to the bound after adding the overhead. Subtracting that allowance by the natural-number subtraction lemma gives the floor inequality.

## References

- Truth anchor: `D5/S0/Computability/ConditionalComplexityFloor.conditional_complexity_floor`
