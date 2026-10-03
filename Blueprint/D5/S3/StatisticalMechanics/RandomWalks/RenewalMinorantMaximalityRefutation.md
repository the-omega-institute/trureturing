# Q_4 is not a maximal renewal minorant

## Abstract

Nikolov and Savov's Conjecture 3.7 fails at k = 4: the polynomial x^2(x+y+z)+xy is a degree-three renewal minorant strictly above Q_4 at interior points of the probability simplex.

**Definition 1.1 (The probability simplex).**

$$\forall k \in \mathbb{N},\; \operatorname{Ak}\left(k\right) = \{p:\operatorname{Fin}\left(k - 1\right) \to \mathbb{R} \mid (\forall i \in \operatorname{Fin}\left(k - 1\right),\; 0 \le p\left(i\right)) \land (\sum_{i:\operatorname{Fin}\left(k - 1\right)} p\left(i\right) \le 1)\}$$

*Formalization.* `D5/S3/StatisticalMechanics/RandomWalks/RenewalMinorantMaximalityRefutation.Ak` (`✓ std3`).

*Citation.* N. Nikolov and M. Savov (2024). *Properties and conjectures regarding discrete renewal sequences*. DOI: [10.53656/math2024-2-1-pro](https://doi.org/10.53656/math2024-2-1-pro). URL: <https://arxiv.org/abs/2307.00545v2>.

*Commentary.*

Equation (2.6), p. 3: "A_k = {(p_1, ···, p_{k−1}) : p_l ≥ 0, 1 ≤ l ≤ k − 1; ∑_{l=1}^{k−1} p_l ≤ 1} ⊆ R^{k−1}." Coordinates are indexed by Fin(k−1): coordinate i represents the source's p_(i+1). Natural-number subtraction in Fin(k−1) is truncated subtraction. The claim uses only k ≥ 3.

**Definition 1.2 (The step distribution).**

$$\forall k \in \mathbb{N},\; \forall p \in \operatorname{Fin}\left(k - 1\right) \to \mathbb{R},\; \forall l \in \mathbb{N},\; \operatorname{stepMass}\left(p, l\right) = \operatorname{ite}\left(((1 \le l) \land (l < k)), p_{l - 1}, \operatorname{ite}\left((l = k), 1 - \sum_{i:\operatorname{Fin}\left(k - 1\right)} p\left(i\right), 0\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/RandomWalks/RenewalMinorantMaximalityRefutation.stepMass` (`✓ std3`).

*Citation.* N. Nikolov and M. Savov (2024). *Properties and conjectures regarding discrete renewal sequences*. DOI: [10.53656/math2024-2-1-pro](https://doi.org/10.53656/math2024-2-1-pro). URL: <https://arxiv.org/abs/2307.00545v2>.

*Commentary.*

Section 2, p. 2: "P(X_1 = l) = p_l ≥ 0, 1 ≤ l ≤ k, and ∑_{l=1}^k p_l = 1." "Extend p_n = 0 for n ≥ k + 1." The first k−1 coordinates determine p_k = 1 − ∑_{l<k} p_l. The displayed ite is if-then-else; p_(l−1) is the Fin(k−1) coordinate formed from the natural number l−1 when 1 ≤ l < k. The value at l = 0 is outside the recurrence for k ≥ 1.

**Definition 1.3 (The renewal recurrence).**

$$\begin{aligned}\forall k \in \mathbb{N},\; \forall p \in \operatorname{Fin}\left(k - 1\right) \to \mathbb{R},\; \operatorname{renewal}\left(p, 0\right) = 1\\\forall k \in \mathbb{N},\; \forall p \in \operatorname{Fin}\left(k - 1\right) \to \mathbb{R},\; \forall n \in \mathbb{N},\; \operatorname{renewal}\left(p, n + 1\right) = \sum_{l:\operatorname{Fin}\left(\operatorname{min}\left(n + 1, k\right)\right)} \operatorname{stepMass}\left(p, \operatorname{val}\left(l\right) + 1\right) \cdot \operatorname{renewal}\left(p, n + 1 - \left(\operatorname{val}\left(l\right) + 1\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/StatisticalMechanics/RandomWalks/RenewalMinorantMaximalityRefutation.renewal` (`✓ std3`).

*Citation.* N. Nikolov and M. Savov (2024). *Properties and conjectures regarding discrete renewal sequences*. DOI: [10.53656/math2024-2-1-pro](https://doi.org/10.53656/math2024-2-1-pro). URL: <https://arxiv.org/abs/2307.00545v2>.

*Commentary.*

Equation (2.2), p. 2: "Obviously u_0 = 1 and the well-known recurrent relation holds u_n = ∑_{l=1}^n p_l u_{n−l} = ∑_{l=1}^{min{n,k}} p_l u_{n−l}." Here u_n = renewal(p,n). The Fin(min(n+1,k)) index l denotes the source's step l+1; val exposes its natural-number value. The difference of time indices is natural-number truncated subtraction, agreeing with ordinary subtraction on the summation range.

**Definition 1.4 (The pointwise polynomial ordering).**

$$\forall k \in \mathbb{N},\; \forall P \in \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(k - 1\right), \mathbb{R}\right),\; \forall R \in \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(k - 1\right), \mathbb{R}\right),\; (\operatorname{polynomialLE}\left(P, R\right)) \Leftrightarrow (\forall p \in \operatorname{Fin}\left(k - 1\right) \to \mathbb{R},\; (p \in \operatorname{Ak}\left(k\right)) \Rightarrow (\operatorname{eval}\left(p, P\right) \le \operatorname{eval}\left(p, R\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/RandomWalks/RenewalMinorantMaximalityRefutation.polynomialLE` (`✓ std3`).

*Citation.* N. Nikolov and M. Savov (2024). *Properties and conjectures regarding discrete renewal sequences*. DOI: [10.53656/math2024-2-1-pro](https://doi.org/10.53656/math2024-2-1-pro). URL: <https://arxiv.org/abs/2307.00545v2>.

*Commentary.*

Section 2, p. 3: "We set P_k for the set of polynomials of k − 1 variables. We introduce partial ordering in P_k in the following manner: we say that P_1 ≺ P_2, P_1, P_2 ∈ P_k, if and only if P_1 ≤ P_2 on A_k." P_k is MvPolynomial(Fin(k−1), R) with real coefficients, and polynomialLE is this non-strict ordering.

**Definition 1.5 (The class of polynomial minorants).**

$$\forall k \in \mathbb{N},\; \operatorname{minorantClass}\left(k\right) = \{P:\operatorname{MvPolynomial}\left(\operatorname{Fin}\left(k - 1\right), \mathbb{R}\right) \mid (\operatorname{totalDegree}\left(P\right) \le k - 1) \land (\forall p \in \operatorname{Fin}\left(k - 1\right) \to \mathbb{R},\; (p \in \operatorname{Ak}\left(k\right)) \Rightarrow (\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow (\operatorname{eval}\left(p, P\right) \le \operatorname{renewal}\left(p, n\right))))\}$$

*Formalization.* `D5/S3/StatisticalMechanics/RandomWalks/RenewalMinorantMaximalityRefutation.minorantClass` (`✓ std3`).

*Citation.* N. Nikolov and M. Savov (2024). *Properties and conjectures regarding discrete renewal sequences*. DOI: [10.53656/math2024-2-1-pro](https://doi.org/10.53656/math2024-2-1-pro). URL: <https://arxiv.org/abs/2307.00545v2>.

*Commentary.*

Equations (2.4) and (2.7), pp. 2–3: "M_k = max_{l≥1}{u_l} and m_k = min_{l≥1}{u_l}." "𝒜_k := {P ∈ P_k : deg(P) ≤ k − 1, P ≺ m_k}," where "deg(P) is the power of P, i.e. the highest combined power of every monomial constituting P." Degree is totalDegree. P ≺ m_k is encoded as eval(p,P) ≤ u_n for every p in A_k and every n ≥ 1; this lower-bound formulation does not assume attainment of a minimum.

**Definition 1.6 (The product of partial sums).**

$$\forall k \in \mathbb{N},\; \operatorname{Q}\left(k\right) = \prod_{j:\operatorname{Fin}\left(k - 1\right)} (\sum_{l:\operatorname{Fin}\left(k - 1\right)} \operatorname{ite}\left((l \le j), \operatorname{X}\left(l\right), 0\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/RandomWalks/RenewalMinorantMaximalityRefutation.Q` (`✓ std3`).

*Citation.* N. Nikolov and M. Savov (2024). *Properties and conjectures regarding discrete renewal sequences*. DOI: [10.53656/math2024-2-1-pro](https://doi.org/10.53656/math2024-2-1-pro). URL: <https://arxiv.org/abs/2307.00545v2>.

*Commentary.*

Equation (2.5), p. 2: "Q_n(p_1, p_2, ···, p_{n−1}) = ∏_{j=1}^{n−1} ∑_{l=1}^j p_l." The empty product is 1. Q(k) is the corresponding polynomial in the variables X_l indexed from zero; the inner sum selects l ≤ j. The displayed ite is if-then-else.

**Definition 1.7 (The maximality clause of Conjecture 3.7).**

$$(claim) \Leftrightarrow (\forall k \in \mathbb{N},\; (3 \le k) \Rightarrow ((\operatorname{Q}\left(k\right) \in \operatorname{minorantClass}\left(k\right)) \land (\forall P \in \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(k - 1\right), \mathbb{R}\right),\; (P \in \operatorname{minorantClass}\left(k\right)) \Rightarrow ((\operatorname{polynomialLE}\left(\operatorname{Q}\left(k\right), P\right)) \Rightarrow (P = \operatorname{Q}\left(k\right))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/RandomWalks/RenewalMinorantMaximalityRefutation.claim` (`✓ std3`).

*Citation.* N. Nikolov and M. Savov (2024). *Properties and conjectures regarding discrete renewal sequences*. DOI: [10.53656/math2024-2-1-pro](https://doi.org/10.53656/math2024-2-1-pro). URL: <https://arxiv.org/abs/2307.00545v2>.

*Commentary.*

Conjecture 3.7, p. 5: "For any k ≥ 3, Q_k is a maximal element in 𝒜_k and it is largest in 𝒜̂_k." Equation (2.8), p. 3: "We say that P ∈ 𝒜_k is maximal if and only if P̃ ∈ 𝒜_k and P̃ ≻ P ⇒ P̃ = P." The claim encodes the first clause with polynomial equality and the pointwise non-strict order. Conjecture 3.7 implies claim, so ¬ claim refutes the conjecture. The separate hatted class is not used.

**Theorem 1.8 (Refutation at k = 4).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/RandomWalks/RenewalMinorantMaximalityRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Nikolov and M. Savov (2024). *Properties and conjectures regarding discrete renewal sequences*. DOI: [10.53656/math2024-2-1-pro](https://doi.org/10.53656/math2024-2-1-pro). URL: <https://arxiv.org/abs/2307.00545v2>.

*Commentary.*

Write x=p_1, y=p_2, z=p_3 and w=1−x−y−z. Set P=x^2(x+y+z)+xy. Then P−Q_4=xyw ≥ 0 on A_4. Its degree is at most 3, and it differs from Q_4: at x=y=z=w=1/4 the values are P=7/64 and Q_4=6/64. The initial renewal masses are u_1=x, u_2=x^2+y and u_3=x^3+2xy+z. The certificates u_1−P=x(z+(1+x)w), u_2−P=x^2w+y(1−x), and u_3−P=xy(1−x)+z(1−x^2) are nonnegative on A_4. Also P ≤ u_1 ≤ 1=u_0. For n ≥ 4 the recurrence is a convex combination of the preceding four masses, so strong induction gives P ≤ u_n for every positive n. Thus P belongs to 𝒜_4 and contradicts maximality of Q_4.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/RenewalMinorantMaximalityRefutation.Ak`
- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/RenewalMinorantMaximalityRefutation.Q`
- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/RenewalMinorantMaximalityRefutation.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/RenewalMinorantMaximalityRefutation.minorantClass`
- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/RenewalMinorantMaximalityRefutation.polynomialLE`
- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/RenewalMinorantMaximalityRefutation.renewal`
- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/RenewalMinorantMaximalityRefutation.result`
- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/RenewalMinorantMaximalityRefutation.stepMass`
