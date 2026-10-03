---
bibkey: nikolovsavov2024renewal
authors: N. Nikolov and M. Savov
year: 2024
title: "Properties and conjectures regarding discrete renewal sequences"
doi: 10.53656/math2024-2-1-pro
url: https://arxiv.org/abs/2307.00545v2
claim: "Conjecture 3.7. For any k ≥ 3, Q_k is a maximal element in 𝒜_k and it is largest in 𝒜̂_k."
strata_touched:
  - D5/S3/StatisticalMechanics/RandomWalks/RenewalMinorantMaximalityRefutation
license: citation-only
triage: anchor
---

# Discrete renewal minorants

N. Nikolov and M. Savov, *Properties and conjectures regarding discrete
renewal sequences*, Mathematics and Informatics 67 (2024), 111–118;
arXiv:2307.00545v2. Page numbers below refer to the seven-page arXiv version.

Section 2, p. 2, fixes a positive integer-valued step distribution:

> P(X_1 = l) = p_l ≥ 0, 1 ≤ l ≤ k, and ∑_{l=1}^k p_l = 1.

> Extend p_n = 0 for n ≥ k + 1.

Equation (2.2), p. 2:

> Obviously u_0 = 1 and the well-known recurrent relation holds
> u_n = ∑_{l=1}^n p_l u_{n−l} = ∑_{l=1}^{min{n,k}} p_l u_{n−l}.

Equations (2.4)–(2.6), pp. 2–3:

> M_k = max_{l≥1}{u_l} and m_k = min_{l≥1}{u_l}.

> Q_n(p_1, p_2, ···, p_{n−1}) = ∏_{j=1}^{n−1} ∑_{l=1}^j p_l.

> A_k = {(p_1, ···, p_{k−1}) : p_l ≥ 0, 1 ≤ l ≤ k − 1;
> ∑_{l=1}^{k−1} p_l ≤ 1} ⊆ R^{k−1}.

Section 2, p. 3:

> We set P_k for the set of polynomials of k − 1 variables. We introduce
> partial ordering in P_k in the following manner: we say that P_1 ≺
> P_2, P_1, P_2 ∈ P_k, if and only if P_1 ≤ P_2 on A_k.

Equation (2.7), p. 3:

> 𝒜_k := {P ∈ P_k : deg(P) ≤ k − 1, P ≺ m_k},

> where deg(P) is the power of P, i.e. the highest combined power of
> every monomial constituting P.

Equation (2.8), p. 3:

> We say that P ∈ 𝒜_k is maximal if and only if
> P̃ ∈ 𝒜_k and P̃ ≻ P ⇒ P̃ = P.

Conjecture 3.7, p. 5:

> For any k ≥ 3, Q_k is a maximal element in 𝒜_k and it is largest in 𝒜̂_k.

Proposition 3.8, p. 5:

> Conjecture 3.7 is valid for k = 3.

The formal claim uses only the maximality clause. The coordinates have real
coefficients, p_k is the remaining mass, and totalDegree is the combined
monomial degree. A polynomial below every positive-time renewal mass is
the lower-bound reading of P ≺ m_k. The hatted class is not needed.

Theorem 3.6, p. 4, states that there is no **largest** element in 𝒜_k for
k ≥ 3. This does not state that no **maximal** element exists. Proposition
3.8 and its proof on pp. 6–7 address k = 3 separately.
