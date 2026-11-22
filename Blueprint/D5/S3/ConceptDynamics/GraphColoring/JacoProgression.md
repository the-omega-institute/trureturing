# Jaco maximum degrees along progressions

## Abstract

Along every arithmetic progression of orders the Jaco maximum degree is linear plus an explicit golden correction, and the multiples of five split into exact blocks.

**Definition 1.1 (The golden fractional part beta_d).**

$$\operatorname{beta}\left(d\right) = \operatorname{fract}\left(\frac{d}{phi}\right)$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/JacoProgression.beta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok; Paul Fisher; Bettina Wilkens; Mokhwetha Mabula; Vivian Mukungunugwa (2014). *Characteristics of Finite Jaco Graphs, J_n(1), n in N*. DOI: [10.48550/arXiv.1404.0484](https://doi.org/10.48550/arXiv.1404.0484).

*Commentary.*

beta d is the fractional part of d/phi, so d/phi=floor(d/phi)+beta d.

**Definition 1.2 (The block starts k_q).**

$$(\operatorname{k}\left(0\right) = 1) \land (\forall q \in \mathrm{Nat},\; (1 \le q) \Rightarrow (\operatorname{k}\left(q\right) = \left\lfloor(5 \cdot q - 1) \cdot phi\right\rfloor + 3 \cdot q))$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/JacoProgression.blockStart` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok; Paul Fisher; Bettina Wilkens; Mokhwetha Mabula; Vivian Mukungunugwa (2014). *Characteristics of Finite Jaco Graphs, J_n(1), n in N*. DOI: [10.48550/arXiv.1404.0484](https://doi.org/10.48550/arXiv.1404.0484).

*Commentary.*

blockStart 0=1 and, for q at least one, blockStart q=floor((5q-1)phi)+3q, with 5q-1 computed in the natural numbers.

**Definition 1.3 (The block P_q).**

$$(\operatorname{P}\left(0\right) = \operatorname{Icc}\left(1, 5 \cdot \operatorname{k}\left(1\right) - 1\right)) \land (\forall q \in \mathrm{Nat},\; (1 \le q) \Rightarrow (\operatorname{P}\left(q\right) = \operatorname{Icc}\left(5 \cdot \operatorname{k}\left(q\right), 5 \cdot \operatorname{k}\left(q + 1\right) - 1\right)))$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/JacoProgression.block` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok; Paul Fisher; Bettina Wilkens; Mokhwetha Mabula; Vivian Mukungunugwa (2014). *Characteristics of Finite Jaco Graphs, J_n(1), n in N*. DOI: [10.48550/arXiv.1404.0484](https://doi.org/10.48550/arXiv.1404.0484).

*Commentary.*

block q is the interval of orders from 1 (for q=0) or 5 k_q (for q at least one) up to 5 k_(q+1)-1.

**Theorem 1.4 (Progression law and the five-blocks).**

$$(\forall d \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \operatorname{delta}\left(d \cdot k\right) = \left\lfloor\frac{d}{phi}\right\rfloor \cdot k + \left\lfloor\operatorname{beta}\left(d\right) \cdot k + alpha\right\rfloor) \land ((\forall d \in \mathrm{Nat},\; (1 \le d) \Rightarrow ((0 < \operatorname{beta}\left(d\right)) \land (\operatorname{beta}\left(d\right) < 1))) \land (((\left\lfloor\frac{5}{phi}\right\rfloor = 3) \land (\operatorname{beta}\left(5\right) = \frac{5}{phi} - 3)) \land ((\forall d \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall q \in \mathrm{Int},\; ((1 \le d) \land (1 \le k)) \Rightarrow ((\left\lfloor\operatorname{beta}\left(d\right) \cdot k + alpha\right\rfloor = q) \Leftrightarrow ((\operatorname{max}\left(1, \operatorname{ceil}\left(\frac{q - alpha}{\operatorname{beta}\left(d\right)}\right)\right) \le k) \land (k < \operatorname{ceil}\left(\frac{q + 1 - alpha}{\operatorname{beta}\left(d\right)}\right))))) \land ((\forall q \in \mathrm{Nat},\; (1 \le q) \Rightarrow (\operatorname{ceil}\left(\frac{q - alpha}{\operatorname{beta}\left(5\right)}\right) = \operatorname{k}\left(q\right))) \land ((\forall m \in \mathrm{Nat},\; (1 \le m) \Rightarrow (\operatorname{ExistsUnique}\left(q, \operatorname{mem}\left(m, \operatorname{P}\left(q\right)\right)\right))) \land ((\forall q \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; (\operatorname{mem}\left(m, \operatorname{P}\left(q\right)\right)) \Rightarrow (1 \le m)) \land ((\forall q \in \mathrm{Nat},\; \operatorname{Nonempty}\left(\operatorname{P}\left(q\right)\right)) \land (\forall q \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; (\operatorname{mem}\left(5 \cdot k, \operatorname{P}\left(q\right)\right)) \Rightarrow (\operatorname{delta}\left(5 \cdot k\right) = 3 \cdot k + q)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/JacoProgression.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok; Paul Fisher; Bettina Wilkens; Mokhwetha Mabula; Vivian Mukungunugwa (2014). *Characteristics of Finite Jaco Graphs, J_n(1), n in N*. DOI: [10.48550/arXiv.1404.0484](https://doi.org/10.48550/arXiv.1404.0484).

*Commentary.*

Write delta n for the maximum degree of the finite linear Jaco graph J_n(1), alpha=sqrt(5)-2 and beta_d=beta d. For all d and k, delta(dk)=floor(d/phi)k+floor(beta_d k+alpha): JacoAdditionLaw.delta_eq_floor gives delta n=floor((n+2)/phi)-1, and (dk+2)/phi=floor(d/phi)k+1+(beta_d k+alpha) because 2/phi=1+alpha. For d at least one, beta_d lies strictly between 0 and 1 since d/phi is irrational, and for k at least one and every integer q the correction equals q exactly when max(1, ceil((q-alpha)/beta_d))<=k<ceil((q+1-alpha)/beta_d). For d=5, floor(5/phi)=3 and beta_5=5phi-8, whose inverse is 3+5phi, so (q-alpha)/beta_5=3q-1+(5q-1)phi and its ceiling is k_q=floor((5q-1)phi)+3q for q at least one. The blocks P_0=[1,5k_1-1] and P_q=[5k_q,5k_(q+1)-1] are nonempty, lie in the positive integers and partition them, and 5k in P_q gives delta(5k)=3k+q. Since k_1=9, k_2=20 and k_3=31, the first blocks are [1,44], [45,99] and [100,154]; these values are stated, not separately machine-checked. The first open problem on printed page 11 of Kok, Fisher, Wilkens, Mabula and Mukungunugwa, arXiv:1404.0484v1, records Delta(J_5k(1))=3k on P_0=[1,44] and 3k+1 on P_1=[45,99], leaves the right end of P_2 open, and asks for a partitioning that closes the pattern; the blocks P_q above answer it, and the general progression law is repo-derived. Possible answers posted on MathDB were not inspected, so no priority is claimed.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoProgression.beta`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoProgression.block`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoProgression.blockStart`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoProgression.result`
- Dependency: [D5/S3/ConceptDynamics/GraphColoring/JacoAdditionLaw](JacoAdditionLaw.md)
