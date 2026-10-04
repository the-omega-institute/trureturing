# Integral Legendre Odd-Power Telescopers

## Abstract

Integral coefficient polynomials provide telescopers for every positive odd-power Legendre sum.

The identity is an equality in Q[X], with X the indeterminate. C embeds a rational number as a constant polynomial. rat and int cast naturals to Q and Z; zrat casts integers to Q. val extracts a natural index from a Fin element or an attached range element. range(p) contains the naturals below p, and attach carries each such index with its membership proof. ltRange(i) extracts the bound from that proof, and finMk (Fin.mk) inserts the index and bound. natSub is natural subtraction truncated at zero. eval2 uses the indicated coefficient homomorphism and evaluation point. intCastRingHom is Int.castRingHom. The lower coefficients are chosen once for each m and then used for every p.

**Definition 1.1 (The Legendre polynomials).**

$$(P\left(0\right) = 1) \land ((P\left(1\right) = X) \land (\forall n \in \mathbb{N},\; P\left(n + 2\right) = \left(C\left(rat\left(2 \cdot \left(n + 1\right) + 1\right)\right) \cdot X \cdot P\left(n + 1\right) - C\left(rat\left(n + 1\right)\right) \cdot P\left(n\right)\right) \cdot C\left(\frac{1}{rat\left(n + 2\right)}\right)))$$

*Formalization.* `D5/S1/Recurrence/Sun/LegendreOddPowerTelescoper.P` (`✓ std3`).

*Citation.* Li-Li Cui and Zhi-Hong Sun (2026). *Curious identities involving Legendre polynomials and Apéry-like numbers*. DOI: [10.48550/arXiv.2607.12330](https://doi.org/10.48550/arXiv.2607.12330). URL: <https://arxiv.org/abs/2607.12330v1>.

*Commentary.*

Equation (1.1), page 1: "The famous Legendre polynomials {P_n(x)} are given by P_0(x) = 1, P_1(x) = x and (n + 1)P_{n+1}(x) = (2n + 1)xP_n(x) − nP_{n−1}(x) (n ≥ 1)." The definition solves this recurrence in Q[X] at index n+1 for n at least one. Its successor form is displayed with n starting at zero. The fraction is rational division, and its denominator is nonzero.

**Definition 1.2 (The source polynomial L).**

$$\forall m \in \mathbb{N},\; \forall f \in Fin\left(m\right) \to Polynomial\left(\mathbb{Z}\right),\; \forall p \in \mathbb{Z},\; \forall t \in Polynomial\left(\mathbb{Q}\right),\; L\left(m, f, p, t\right) = C\left(zrat\left(2 \cdot p + 1\right)^{2 \cdot m}\right) \cdot t^{m} + \sum_{i \in attach\left(range\left(m\right)\right)} (C\left(eval2\left(intCastRingHom\left(\mathbb{Q}\right), zrat\left(2 \cdot p + 1\right)^{2}, f\left(finMk\left(val\left(i\right), ltRange\left(i\right)\right)\right)\right)\right) \cdot t^{val\left(i\right)})$$

*Formalization.* `D5/S1/Recurrence/Sun/LegendreOddPowerTelescoper.L` (`✓ std3`).

*Citation.* Li-Li Cui and Zhi-Hong Sun (2026). *Curious identities involving Legendre polynomials and Apéry-like numbers*. DOI: [10.48550/arXiv.2607.12330](https://doi.org/10.48550/arXiv.2607.12330). URL: <https://arxiv.org/abs/2607.12330v1>.

*Commentary.*

Conjecture 2.1, page 10: "Suppose that m, p ∈ Z^+. Then there are integral polynomials f_i(t) with degree i (i = 0, 1, …, m − 1) such that (1 − x)^{m+1} Σ_{n=0}^{p−1} (2n + 1)^{2m+1} P_n(x) = pL_m(p, 1 − x)P_{p−1}(x) − pL_m(−p, 1 − x)P_p(x), where L_m(p, t) = (2p + 1)^{2m} t^m + f_{m−1}((2p + 1)^2) t^{m−1} + · · · + f_1((2p + 1)^2) t + f_0." L(m,f,p,t) is the displayed L_m(p,t) with the coefficient family f made explicit. For a positive m and a family satisfying claim, f at index zero is a nonzero integer constant polynomial; its evaluation supplies the lower t^0 term. The sum uses the attached range below m and evaluates every lower coefficient at the same square (2p+1)^2. The parameter p is an integer, so the negative endpoint is part of the same definition.

**Definition 1.3 (Cui-Sun Conjecture 2.1).**

$$(claim) \Leftrightarrow (\forall m \in \mathbb{N},\; (1 \le m) \Rightarrow (\exists f \in Fin\left(m\right) \to Polynomial\left(\mathbb{Z}\right),\; (\forall i \in Fin\left(m\right),\; (natDegree\left(f\left(i\right)\right) = val\left(i\right)) \land (f\left(i\right) \ne 0)) \land (\forall p \in \mathbb{N},\; (1 \le p) \Rightarrow (\left(1 - X\right)^{m + 1} \cdot \sum_{n \in range\left(p\right)} (C\left(rat\left(2 \cdot n + 1\right)\right)^{2 \cdot m + 1} \cdot P\left(n\right)) = C\left(rat\left(p\right)\right) \cdot L\left(m, f, int\left(p\right), 1 - X\right) \cdot P\left(natSub\left(p, 1\right)\right) - C\left(rat\left(p\right)\right) \cdot L\left(m, f, -int\left(p\right), 1 - X\right) \cdot P\left(p\right)))))$$

*Formalization.* `D5/S1/Recurrence/Sun/LegendreOddPowerTelescoper.claim` (`✓ std3`).

*Citation.* Li-Li Cui and Zhi-Hong Sun (2026). *Curious identities involving Legendre polynomials and Apéry-like numbers*. DOI: [10.48550/arXiv.2607.12330](https://doi.org/10.48550/arXiv.2607.12330). URL: <https://arxiv.org/abs/2607.12330v1>.

*Commentary.*

Conjecture 2.1, page 10: "Suppose that m, p ∈ Z^+. Then there are integral polynomials f_i(t) with degree i (i = 0, 1, …, m − 1) such that (1 − x)^{m+1} Σ_{n=0}^{p−1} (2n + 1)^{2m+1} P_n(x) = pL_m(p, 1 − x)P_{p−1}(x) − pL_m(−p, 1 − x)P_p(x), where L_m(p, t) = (2p + 1)^{2m} t^m + f_{m−1}((2p + 1)^2) t^{m−1} + · · · + f_1((2p + 1)^2) t + f_0." The encoding quantifies m and p over positive naturals and places the existential coefficient family before the quantifier over p. Every coefficient lies in Z[X], is nonzero, and has natural degree equal to its index. This includes the nonzero degree-zero coefficient. The indeterminate is X; no restriction or division by 1-X is imposed.

**Theorem 1.4 (The identity for every m).**

$$\forall m \in \mathbb{N},\; (1 \le m) \Rightarrow (\exists f \in Fin\left(m\right) \to Polynomial\left(\mathbb{Z}\right),\; (\forall i \in Fin\left(m\right),\; (natDegree\left(f\left(i\right)\right) = val\left(i\right)) \land (f\left(i\right) \ne 0)) \land (\forall p \in \mathbb{N},\; (1 \le p) \Rightarrow (\left(1 - X\right)^{m + 1} \cdot \sum_{n \in range\left(p\right)} (C\left(rat\left(2 \cdot n + 1\right)\right)^{2 \cdot m + 1} \cdot P\left(n\right)) = C\left(rat\left(p\right)\right) \cdot L\left(m, f, int\left(p\right), 1 - X\right) \cdot P\left(natSub\left(p, 1\right)\right) - C\left(rat\left(p\right)\right) \cdot L\left(m, f, -int\left(p\right), 1 - X\right) \cdot P\left(p\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Sun/LegendreOddPowerTelescoper.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A degree-lowering integer operator produces the coefficient family. Binomial expansion identifies its evaluation with a symmetric difference at r+2 and r-2. Its iterates on the monomial of degree m are nonzero of successive degrees m,m-1,...,0 and then vanish. Alternating these iterates gives a finite inverse for multiplication by t plus the operator. The Legendre recurrence turns this inverse identity into a boundary difference, and induction sums the differences over all indices below p.

## References

- Truth anchor: `D5/S1/Recurrence/Sun/LegendreOddPowerTelescoper.L`
- Truth anchor: `D5/S1/Recurrence/Sun/LegendreOddPowerTelescoper.P`
- Truth anchor: `D5/S1/Recurrence/Sun/LegendreOddPowerTelescoper.claim`
- Truth anchor: `D5/S1/Recurrence/Sun/LegendreOddPowerTelescoper.result`
