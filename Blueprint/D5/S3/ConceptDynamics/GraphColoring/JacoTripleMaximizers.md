# Jaco graphs with three maximum-degree vertices

## Abstract

The finite linear Jaco graphs with exactly three maximum-degree vertices are those of order 3j+1+2b_j for j at least one, with gaps 3 or 5.

**Definition 1.1 (The order recurrence p_j).**

$$(\operatorname{p}\left(0\right) = 1) \land (\forall j \in \mathrm{Nat},\; \operatorname{p}\left(j + 1\right) = \operatorname{p}\left(j\right) + 3 + 2 \cdot (\operatorname{b}\left(j + 1\right) - \operatorname{b}\left(j\right)))$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/JacoTripleMaximizers.orders` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok; Paul Fisher; Bettina Wilkens; Mokhwetha Mabula; Vivian Mukungunugwa (2014). *Characteristics of Finite Jaco Graphs, J_n(1), n in N*. DOI: [10.48550/arXiv.1404.0484](https://doi.org/10.48550/arXiv.1404.0484).

*Commentary.*

orders 0=1 and orders(j+1)=orders j+3+2(b_(j+1)-b_j), where b_i=beattyOut i=floor((i+1)/phi); this is the recurrence p_(j+1)=p_j+3+2(floor((j+2)/phi)-floor((j+1)/phi)) with seed p_0=1.

**Theorem 1.2 (Orders with three maximum-degree vertices).**

$$(\forall j \in \mathrm{Nat},\; \operatorname{p}\left(j\right) = 3 \cdot j + 1 + 2 \cdot \operatorname{b}\left(j\right)) \land ((\forall n \in \mathrm{Nat},\; (2 \le n) \Rightarrow ((\operatorname{card}\left(\operatorname{jaconian}\left(n\right)\right) = 3) \Leftrightarrow (\operatorname{b}\left(n + 3\right) = \operatorname{b}\left(n + 1\right) + 2))) \land ((\forall n \in \mathrm{Nat},\; (\operatorname{card}\left(\operatorname{jaconian}\left(n\right)\right) = 3) \Leftrightarrow (\exists j \in \mathrm{Nat},\; (1 \le j) \land (\operatorname{p}\left(j\right) = n))) \land ((\operatorname{StrictMono}\left(p\right)) \land ((\forall j \in \mathrm{Nat},\; (\operatorname{p}\left(j + 1\right) = \operatorname{p}\left(j\right) + 3) \lor (\operatorname{p}\left(j + 1\right) = \operatorname{p}\left(j\right) + 5)) \land ((\forall j \in \mathrm{Nat},\; (\operatorname{p}\left(j + 1\right) = \operatorname{p}\left(j\right) + 3) \Rightarrow (\operatorname{p}\left(j + 2\right) = \operatorname{p}\left(j + 1\right) + 5)) \land ((\forall j \in \mathrm{Nat},\; ((\operatorname{p}\left(j + 1\right) = \operatorname{p}\left(j\right) + 5) \land (\operatorname{p}\left(j + 2\right) = \operatorname{p}\left(j + 1\right) + 5)) \Rightarrow (\operatorname{p}\left(j + 3\right) = \operatorname{p}\left(j + 2\right) + 3)) \land ((\operatorname{p}\left(0\right) = 1) \land ((\operatorname{b}\left(\operatorname{p}\left(0\right) + 3\right) = \operatorname{b}\left(\operatorname{p}\left(0\right) + 1\right) + 2) \land (\operatorname{card}\left(\operatorname{jaconian}\left(\operatorname{p}\left(0\right)\right)\right) \ne 3)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/JacoTripleMaximizers.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok; Paul Fisher; Bettina Wilkens; Mokhwetha Mabula; Vivian Mukungunugwa (2014). *Characteristics of Finite Jaco Graphs, J_n(1), n in N*. DOI: [10.48550/arXiv.1404.0484](https://doi.org/10.48550/arXiv.1404.0484).

*Commentary.*

Write J_n for the set of labels of maximum-degree vertices of the finite linear Jaco graph J_n(1) and b_i=floor((i+1)/phi). The recurrence solves to p_j=3j+1+2b_j. For n at least two, J_n has exactly three vertices if and only if b_(n+3)=b_(n+1)+2: by JacoMaximumSet.result, |J_n|=floor(x_n phi^2)+1 with x_n the fractional part of (n+2)/phi, and x_n phi^2-2=(x_n-2/phi^2)phi^2 while b_(n+3)-b_(n+1)=2 exactly when x_n+2/phi is at least 2, that is x_n is at least 2-2/phi=2/phi^2. With f_j the fractional part of (j+1)/phi, which lies strictly between 0 and 1, the golden identity (p_j+2+i)/phi=(b_j+2j+1)+(1-f_j(2/phi-1))+i/phi puts p_j on the criterion and every order strictly between p_j and p_(j+1) off it; the gap p_(j+1)-p_j is 3 when f_j<1-1/phi and 5 when f_j>1-1/phi. Bracketing every positive order between consecutive p_j gives the exact enumeration: |J_n|=3 if and only if n=p_j for some j at least one, so the orders are p_1,p_2,...=6,9,14,19,22,...; these first values are stated, not separately machine-checked. The seed p_0=1 satisfies the Beatty criterion but J_1={1}. The sequence is strictly increasing with gaps 3 or 5, a gap 3 is always followed by a gap 5 because 2/phi>1, and two consecutive gaps 5 are always followed by a gap 3 because 3/phi<2. The recurrence is Corollary 6 of Ma and Zhang, Zenodo DOI 10.5281/zenodo.24369124, which reformulates Conjecture 2.16.1 of Kok, Linear Jaco Graphs: A Critical Review (2016), page 73, and Patel's classification of the maximum sets posted as the solution to MathDB problem 369424; the 2016 journal text and the MathDB answer were not inspected, and no priority is claimed. The proof here is repo-derived.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoTripleMaximizers.orders`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoTripleMaximizers.result`
- Dependency: [D5/S3/ConceptDynamics/GraphColoring/JacoMaximumSet](JacoMaximumSet.md)
