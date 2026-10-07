# Triple-product sum rigidity

## Abstract

Equal triple products in a sufficiently short positive integer interval have equal sums.

**Theorem 1.1 (Integer sum rigidity).**

$$\forall m \in \mathbb{Z}, h \in \mathbb{Z}, a \in \mathbb{Z}, b \in \mathbb{Z}, c \in \mathbb{Z}, d \in \mathbb{Z}, e \in \mathbb{Z}, f \in \mathbb{Z},\; \left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(0 < m \land 0 \le h\right) \land h^{2} < m\right) \land m \le a\right) \land a \le m + h\right) \land m \le b\right) \land b \le m + h\right) \land m \le c\right) \land c \le m + h\right) \land m \le d\right) \land d \le m + h\right) \land m \le e\right) \land e \le m + h\right) \land m \le f\right) \land f \le m + h\right) \land a \cdot b \cdot c = d \cdot e \cdot f\right) \Rightarrow a + b + c = d + e + f$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ShortIntervals/TripleProductSumRigidity.triple_product_sum_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All eight variables are integers. Each of the six rows lies in the same closed interval. Repetitions, shared rows and arbitrary row order are allowed; the equality of sums is a conclusion.

Choose a least member x of each triple and write the other members as x+r and x+s. The cubic defect is 9x(r^2-rs+s^2)+(r+s)^3. For positive width it lies between zero and 9mh^2+17h^3, strictly below 26m^2. Distinct integer sums at least 3m have cube difference greater than 27m^2. Equal products make that cube difference a difference of defects, which is impossible. At zero width every row equals m.

The stronger predicate m>(h+1)^2 implies the square threshold here. This theorem leaves the classification of six-row unit relations, Hall conditions, complete-hull compositeness, higher-endpoint sectors, nonunit relations, larger cores, long spans and unrestricted Grimm's conjecture unresolved.

## References

- Truth anchor: `D5/S3/Arith/ShortIntervals/TripleProductSumRigidity.triple_product_sum_rigidity`
