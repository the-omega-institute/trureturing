# The maximum set of a finite linear Jaco graph

## Abstract

The maximum-degree vertices of a finite linear Jaco graph form a label interval of one, two or three vertices, with exact singleton criteria.

**Definition 1.1 (The maximum set).**

$$\operatorname{jaconian}\left(n\right) = (v: \operatorname{degree}\left(\operatorname{jaco}\left(n\right), v\right) = \operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right))$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/JacoMaximumSet.jaconian` (`✓ std3`).

*Citation.* Johan Kok; Paul Fisher; Bettina Wilkens; Mokhwetha Mabula; Vivian Mukungunugwa (2014). *Characteristics of Finite Jaco Graphs, J_n(1), n in N*. DOI: [10.48550/arXiv.1404.0484](https://doi.org/10.48550/arXiv.1404.0484).

*Commentary.*

jaconian n is the finite set of labels of the vertices of jaco n whose ordinary degree equals the maximum degree p_n; the source calls this the Jaconian set J_n.

**Theorem 1.2 (Interval, size and singleton criteria).**

$$(\operatorname{jaconian}\left(1\right) = (1)) \land (\forall n \in \mathrm{Nat},\; (2 \le n) \Rightarrow (((\operatorname{jacoRight}\left(n - \operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right)\right) \le n) \land ((\operatorname{jaconian}\left(n\right) = \operatorname{Icc}\left(\operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right), \operatorname{jacoRight}\left(n - \operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right)\right)\right)) \land ((\operatorname{card}\left(\operatorname{jaconian}\left(n\right)\right) = \left\lfloor\operatorname{frac}\left(n\right) \cdot phi^{2}\right\rfloor + 1) \land ((\operatorname{card}\left(\operatorname{jaconian}\left(n\right)\right) = 1) \lor ((\operatorname{card}\left(\operatorname{jaconian}\left(n\right)\right) = 2) \lor (\operatorname{card}\left(\operatorname{jaconian}\left(n\right)\right) = 3)))))) \land ((((\operatorname{jaconian}\left(n\right) = (\operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right))) \Leftrightarrow (\operatorname{frac}\left(n\right) < \frac{1}{phi^{2}})) \land (((\operatorname{jaconian}\left(n\right) = (\operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right))) \Leftrightarrow ((n = \operatorname{jacoRight}\left(\operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right)\right)) \land (\operatorname{beattyOut}\left(\operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right) + 1\right) = \operatorname{beattyOut}\left(\operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right)\right) + 1))) \land (((\operatorname{jaconian}\left(n\right) = (\operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right))) \Leftrightarrow (\operatorname{beattyOut}\left(n + 1\right) = \operatorname{beattyOut}\left(n + 2\right))) \land ((\operatorname{jaconian}\left(n\right) = (\operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right))) \Leftrightarrow (\operatorname{maxDegree}\left(\operatorname{jaco}\left(n + 1\right)\right) = \operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right)))))) \land ((\operatorname{jaconian}\left(n\right) = (\operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right))) \Rightarrow ((\operatorname{jacoRight}\left(\operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right) + 1\right) = n + 2) \land ((\operatorname{beattyOut}\left(n\right) = \operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right)) \land ((\operatorname{degree}\left(\operatorname{jaco}\left(n\right), \operatorname{v}\left(n\right)\right) = n - \operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right)) \land ((\operatorname{jaconian}\left(n + 1\right) = \operatorname{Icc}\left(\operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right), \operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right) + 1\right)) \lor (\operatorname{jaconian}\left(n + 1\right) = \operatorname{Icc}\left(\operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right), \operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right) + 2\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/JacoMaximumSet.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok; Paul Fisher; Bettina Wilkens; Mokhwetha Mabula; Vivian Mukungunugwa (2014). *Characteristics of Finite Jaco Graphs, J_n(1), n in N*. DOI: [10.48550/arXiv.1404.0484](https://doi.org/10.48550/arXiv.1404.0484).

*Commentary.*

Write p=p_n for the maximum degree of jaco n, t=n-p, R_t=jacoRight t=t+b_t, b_i=beattyOut i=floor((i+1)/phi) and x=frac n for the fractional part of (n+2)/phi. By the existing JacoEndpointBeatty.endpoint_eq_beatty, b_i=R_i-i is the outdegree of v_i in the infinite graph J_infinity(1), written d+(v_i) in the source. J_1={1}. For n at least two: R_t<=n and J_n is the label interval [p,R_t], with exactly floor(x phi^2)+1 members, hence one, two or three. J_n={p} exactly when x<1/phi^2=1-1/phi, and equivalently when n=R_p and b_(p+1)=b_p+1, when b_(n+1)=b_(n+2), and when p_(n+1)=p_n; the last equivalence says that an unchanged least maximum label at the next order happens exactly after a unique maximum. At a unique maximum R_(p+1)=n+2, b_n=p, the last vertex v_n has degree n-p, and J_(n+1) is {p,p+1} or {p,p+1,p+2}. Proof: by the existing degree formula deg(v_i)=min(i,n-b_i), a vertex attains p exactly when p<=i and b_i<=t, and the existing Beatty threshold turns b_i<=t into i<=R_t. JacoAdditionLaw.delta_eq_floor gives p=F-1 with F=floor((n+2)/phi), and golden-ratio identities give R_t=p+floor(x phi^2), R_p=n+1+floor(-x phi), b_(p+1)-b_p=floor(1/phi-x phi)-floor(-x phi), b_(n+1)=F and b_(n+2)=p_(n+1)+1=F+floor(x+1/phi). Since phi is irrational, x avoids 0, 1/phi^2 and 1/phi, and every clause is decided by the side of 1/phi^2 on which x falls. The request credits this description to Patel's solution posted on MathDB; that page refuses automated fetches and was not inspected here.

**Theorem 1.3 (Strict outdegree growth and its converse).**

$$\forall n \in \mathrm{Nat},\; ((\operatorname{beattyOut}\left(n - 1\right) < \operatorname{beattyOut}\left(n\right)) \land (\operatorname{beattyOut}\left(n\right) < \operatorname{beattyOut}\left(n + 1\right))) \Rightarrow (\operatorname{jaconian}\left(n\right) = (\operatorname{beattyOut}\left(n\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/JacoMaximumSet.strict_out_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok; Paul Fisher; Bettina Wilkens; Mokhwetha Mabula; Vivian Mukungunugwa (2014). *Characteristics of Finite Jaco Graphs, J_n(1), n in N*. DOI: [10.48550/arXiv.1404.0484](https://doi.org/10.48550/arXiv.1404.0484).

*Commentary.*

For every n, b_(n-1)<b_n<b_(n+1) forces J_n={b_n}: the right inequality gives x<1/phi, the left one then gives x<2/phi-1<1/phi^2, so the maximum is unique and JacoDegreeShift.result gives b_n=p. For n at most one the hypothesis cannot hold, since b_0=b_(0-1) and b_1=b_2=1. This is the implication of Lemma 2.2 (Conjectured) of Kok, Fisher, Wilkens, Mabula and Mukungunugwa, arXiv:1404.0484v1, printed page 4, whose open-problem list on printed page 11 asks to prove it. Answers posted by Patel on MathDB may already settle it; that site refuses automated fetches and was not inspected, so no priority is claimed. The converse, which the source does not assert, is not formalized here; by the result above J_5={3} although b_4=b_5=3.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoMaximumSet.jaconian`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoMaximumSet.result`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoMaximumSet.strict_out_singleton`
- Dependency: [D5/S3/ConceptDynamics/GraphColoring/JacoDegreeShift](JacoDegreeShift.md)
