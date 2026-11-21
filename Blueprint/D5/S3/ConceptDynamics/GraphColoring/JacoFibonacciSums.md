# Jaco graphs at Fibonacci orders and their sums

## Abstract

At Fibonacci orders and sums of two Fibonacci orders the Jaco maximum degree is the sum of the preceding Fibonacci numbers, with exact exceptions for the degree and for the unique maximizer.

**Definition 1.1 (The Binet error eps_r).**

$$\operatorname{eps}\left(r\right) = \frac{\operatorname{F}\left(r\right)}{phi} - \operatorname{F}\left(r - 1\right)$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/JacoFibonacciSums.eps` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok; Paul Fisher; Bettina Wilkens; Mokhwetha Mabula; Vivian Mukungunugwa (2014). *Characteristics of Finite Jaco Graphs, J_n(1), n in N*. DOI: [10.48550/arXiv.1404.0484](https://doi.org/10.48550/arXiv.1404.0484).

*Commentary.*

eps r is F_r/phi-F_(r-1), with F_0=0 and F_1=1; in the proof it equals -(-1/phi)^r for r at least one.

**Theorem 1.2 (Maximum degrees and maximum sets at Fibonacci orders).**

$$(\forall r \in \mathrm{Nat},\; (3 \le r) \Rightarrow ((\operatorname{Delta}\left(\operatorname{F}\left(r\right)\right) = \operatorname{F}\left(r - 1\right)) \land ((\operatorname{jaconian}\left(\operatorname{F}\left(r\right)\right) = (\operatorname{F}\left(r - 1\right))) \Leftrightarrow (4 \le r)))) \land ((\forall r \in \mathrm{Nat},\; \forall s \in \mathrm{Nat},\; ((3 \le r) \land (3 \le s)) \Rightarrow ((\operatorname{Delta}\left(\operatorname{F}\left(r\right) + \operatorname{F}\left(s\right)\right) = \operatorname{F}\left(r - 1\right) + \operatorname{F}\left(s - 1\right)) \Leftrightarrow (not((r = 4) \land (s = 4))))) \land ((\forall r \in \mathrm{Nat},\; \forall s \in \mathrm{Nat},\; ((3 \le r) \land (3 \le s)) \Rightarrow ((\operatorname{jaconian}\left(\operatorname{F}\left(r\right) + \operatorname{F}\left(s\right)\right) = (\operatorname{F}\left(r - 1\right) + \operatorname{F}\left(s - 1\right))) \Leftrightarrow ((not((r = 4) \land (s = 4))) \land ((not((r = 5) \land (s = 5))) \land (((r = 3) \Rightarrow (s = 4)) \land ((s = 3) \Rightarrow (r = 4))))))) \land (\forall r \in \mathrm{Nat},\; \forall s \in \mathrm{Nat},\; ((4 \le r) \land ((4 \le s) \land (\operatorname{F}\left(r\right) \ne \operatorname{F}\left(s\right)))) \Rightarrow ((\operatorname{Delta}\left(\operatorname{F}\left(r\right) + \operatorname{F}\left(s\right)\right) = \operatorname{Delta}\left(\operatorname{F}\left(r\right)\right) + \operatorname{Delta}\left(\operatorname{F}\left(s\right)\right)) \land (\operatorname{jaconian}\left(\operatorname{F}\left(r\right) + \operatorname{F}\left(s\right)\right) = (\operatorname{Delta}\left(\operatorname{F}\left(r\right)\right) + \operatorname{Delta}\left(\operatorname{F}\left(s\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/JacoFibonacciSums.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok; Paul Fisher; Bettina Wilkens; Mokhwetha Mabula; Vivian Mukungunugwa (2014). *Characteristics of Finite Jaco Graphs, J_n(1), n in N*. DOI: [10.48550/arXiv.1404.0484](https://doi.org/10.48550/arXiv.1404.0484).

*Commentary.*

Write Delta_n for the maximum degree of the finite linear Jaco graph J_n(1) and J_n for its complete set of maximum-degree labels. From F_(m+1)-phi F_m=psi^m, eps_r=F_r/phi-F_(r-1)=-(-1/phi)^r: eps_3=2/phi-1, eps_4=-(2-3/phi), eps_5=5/phi-3, eps_r lies in [-(5-8/phi),0) for even r at least 6 and in (0,13/phi-8] for odd r at least 7. If (n+2)/phi=p+2/phi+E with 0<=2/phi+E<2, then JacoAdditionLaw.delta_eq_floor gives Delta_n=p exactly when 2/phi+E>=1, and JacoMaximumSet.result gives J_n={p} exactly when moreover E<2-3/phi=1/phi^4, because the fractional part of (n+2)/phi is then 2/phi+E-1 and Delta_n lies in J_n. Taking n=F_r gives E=eps_r: for r at least 3, Delta_(F_r)=F_(r-1), and J_(F_r)={F_(r-1)} exactly when r is at least 4. Taking n=F_r+F_s gives E=eps_r+eps_s: for r,s at least 3, Delta_(F_r+F_s)=F_(r-1)+F_(s-1) except at r=s=4 (order 6), and J_(F_r+F_s)={F_(r-1)+F_(s-1)} exactly when (r,s) is not (4,4) or (5,5) and any index equal to 3 is paired with 4. In particular, for r,s at least 4 the only exceptions are (4,4) for the degree and (4,4),(5,5) for the singleton, so for distinct Fibonacci orders F_r, F_s with r,s at least 4 both Delta_(F_r+F_s)=Delta_(F_r)+Delta_(F_s) and J_(F_r+F_s)={Delta_(F_r)+Delta_(F_s)}. Proposition 3.2 of Kok, Fisher, Wilkens, Mabula and Mukungunugwa, arXiv:1404.0484v1, pages 10-11, takes t=F_(r-1), h=F_r and l=F_s, all at least 3 (so r at least 5, s at least 4), and asserts Delta_h=F_(r-1), J_h={v_(F_(r-1))}, Delta_(h+l)=Delta_h+Delta_l and J_(h+l)={v_(Delta_h+Delta_l)}, the last two proved there through the conjectured Theorem 2.10; on that domain the first three hold and the singleton fails exactly at h=l=5. The symmetric r,s at least 4 statement with the exceptions (3,3) and (3,3),(5,5) in terms of orders is Corollary 10 of Ma and Zhang, Zenodo DOI 10.5281/zenodo.24369124; the extension to indices 3 is repo-derived.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoFibonacciSums.eps`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoFibonacciSums.result`
- Dependency: [D5/S3/ConceptDynamics/GraphColoring/JacoMaximumSet](JacoMaximumSet.md)
