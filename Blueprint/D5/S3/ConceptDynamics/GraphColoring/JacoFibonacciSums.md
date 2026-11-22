# Jaco graphs at Fibonacci orders and their sums

## Abstract

At Fibonacci orders and sums of two Fibonacci orders the Jaco maximum degree and maximum set are given exactly by the preceding Fibonacci numbers and an explicit correction c(r,s).

**Definition 1.1 (The Binet error eps_r).**

$$\operatorname{eps}\left(r\right) = \frac{\operatorname{F}\left(r\right)}{phi} - \operatorname{F}\left(r - 1\right)$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/JacoFibonacciSums.eps` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok; Paul Fisher; Bettina Wilkens; Mokhwetha Mabula; Vivian Mukungunugwa (2014). *Characteristics of Finite Jaco Graphs, J_n(1), n in N*. DOI: [10.48550/arXiv.1404.0484](https://doi.org/10.48550/arXiv.1404.0484).

*Commentary.*

eps r is F_r/phi-F_(r-1), with F_0=0 and F_1=1; in the proof it equals -(-1/phi)^r for r at least one. In the result, c(r,s) is 2 at r=s=4, 1 at r=s=5 and at the pairs containing an index 3 other than {3,4}, and 0 otherwise, and Iverson(P) is 1 when P holds and 0 otherwise.

**Theorem 1.2 (Maximum degrees and maximum sets at Fibonacci orders).**

$$(\forall r \in \mathrm{Nat},\; (3 \le r) \Rightarrow ((\operatorname{Delta}\left(\operatorname{F}\left(r\right)\right) = \operatorname{F}\left(r - 1\right)) \land (\operatorname{jaconian}\left(\operatorname{F}\left(r\right)\right) = \operatorname{Icc}\left(\operatorname{F}\left(r - 1\right), \operatorname{F}\left(r - 1\right) + \operatorname{Iverson}\left(r = 3\right)\right)))) \land ((\forall r \in \mathrm{Nat},\; \forall s \in \mathrm{Nat},\; ((3 \le r) \land (3 \le s)) \Rightarrow ((\operatorname{Delta}\left(\operatorname{F}\left(r\right) + \operatorname{F}\left(s\right)\right) = \operatorname{F}\left(r - 1\right) + \operatorname{F}\left(s - 1\right) - \operatorname{Iverson}\left((r = 4) \land (s = 4)\right)) \land (\operatorname{jaconian}\left(\operatorname{F}\left(r\right) + \operatorname{F}\left(s\right)\right) = \operatorname{Icc}\left(\operatorname{Delta}\left(\operatorname{F}\left(r\right) + \operatorname{F}\left(s\right)\right), \operatorname{Delta}\left(\operatorname{F}\left(r\right) + \operatorname{F}\left(s\right)\right) + \operatorname{c}\left(r, s\right)\right)))) \land (\forall r \in \mathrm{Nat},\; \forall s \in \mathrm{Nat},\; ((4 \le r) \land ((4 \le s) \land (\operatorname{F}\left(r\right) \ne \operatorname{F}\left(s\right)))) \Rightarrow ((\operatorname{Delta}\left(\operatorname{F}\left(r\right) + \operatorname{F}\left(s\right)\right) = \operatorname{Delta}\left(\operatorname{F}\left(r\right)\right) + \operatorname{Delta}\left(\operatorname{F}\left(s\right)\right)) \land (\operatorname{jaconian}\left(\operatorname{F}\left(r\right) + \operatorname{F}\left(s\right)\right) = \{\operatorname{Delta}\left(\operatorname{F}\left(r\right)\right) + \operatorname{Delta}\left(\operatorname{F}\left(s\right)\right)\}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/JacoFibonacciSums.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok; Paul Fisher; Bettina Wilkens; Mokhwetha Mabula; Vivian Mukungunugwa (2014). *Characteristics of Finite Jaco Graphs, J_n(1), n in N*. DOI: [10.48550/arXiv.1404.0484](https://doi.org/10.48550/arXiv.1404.0484).

*Commentary.*

Write Delta_n for the maximum degree of the finite linear Jaco graph J_n(1), J_n for its complete set of maximum-degree labels and [a,b] for the label interval. From F_(m+1)-phi F_m=psi^m, eps_r=F_r/phi-F_(r-1)=-(-1/phi)^r: eps_3=2/phi-1, eps_4=-(2-3/phi), eps_5=5/phi-3, eps_r lies in [-(5-8/phi),0) for even r at least 6 and in (0,13/phi-8] for odd r at least 7. If (n+2)/phi=(q+1)+x with x in [c(1-1/phi),(c+1)(1-1/phi)) and x<1, then JacoAdditionLaw.delta_eq_floor gives Delta_n=q, and JacoMaximumSet.result, which gives J_n=[Delta_n,R_(n-Delta_n)] with |J_n|=floor(x phi^2)+1, gives J_n=[q,q+c], because (x-c/phi^2)phi^2=x phi^2-c and 1/phi^2=1-1/phi. For n=F_r, x=2/phi+eps_r-1: for r at least 3, Delta_(F_r)=F_(r-1) and J_(F_r)=[F_(r-1),F_(r-1)+[r=3]]. For n=F_r+F_s, x=2/phi+eps_r+eps_s-1, except at r=s=4 where 2/phi+eps_4+eps_4<1 and x=2/phi+2eps_4: for r,s at least 3, Delta_(F_r+F_s)=F_(r-1)+F_(s-1)-[r=s=4] and J_(F_r+F_s)=[Delta,Delta+c] with c=2 at r=s=4, c=1 at r=s=5 and at the pairs containing an index 3 other than {3,4}, and c=0 otherwise. At the orders 6=3+3 and 10=5+5 this gives Delta_6=3, J_6={3,4,5}, Delta_10=6 and J_10={6,7}. For distinct Fibonacci orders F_r, F_s with r,s at least 4, Delta_(F_r+F_s)=Delta_(F_r)+Delta_(F_s) and J_(F_r+F_s)={Delta_(F_r)+Delta_(F_s)}. Proposition 3.2 of Kok, Fisher, Wilkens, Mabula and Mukungunugwa, arXiv:1404.0484v1, pages 10-11, takes t=F_(r-1), h=F_r and l=F_s, all at least 3 (so r at least 5, s at least 4), and asserts Delta_h=F_(r-1), J_h={v_(F_(r-1))}, Delta_(h+l)=Delta_h+Delta_l and J_(h+l)={v_(Delta_h+Delta_l)}, the last two proved there through the conjectured Theorem 2.10; on that domain the first three hold and the singleton fails exactly at h=l=5. The symmetric statement for r,s at least 4, with exceptional orders (3,3) for the degree and (3,3),(5,5) for the singleton and the exceptional values above, is Corollary 10 of Ma and Zhang, Zenodo DOI 10.5281/zenodo.24369124. The degree formula used through JacoAdditionLaw is credited there to Patel's solution of MathDB problem 369423 and to Raso and Kok, arXiv:2611.01554v1, and the maximum-set description used through JacoMaximumSet to Patel's solution of MathDB problem 369424; the MathDB answers were not inspected. The extension to indices 3 is repo-derived.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoFibonacciSums.eps`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoFibonacciSums.result`
- Dependency: [D5/S3/ConceptDynamics/GraphColoring/JacoMaximumSet](JacoMaximumSet.md)
