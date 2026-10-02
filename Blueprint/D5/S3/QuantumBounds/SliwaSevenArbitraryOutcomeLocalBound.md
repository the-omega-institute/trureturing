# The local bound of the arbitrary-output Sliwa seventh inequality

## Abstract

For every number K >= 2 of measurement outcomes, the deterministic expression in (B1) has minimum 6(K-1). This settles the local-bound clause alone.

**Definition 1.1 (The twelve-term deterministic expression).**

$$\forall K \in \mathbb{N},\; \forall a \in \operatorname{ZMod}\left(K\right),\; \forall b \in \operatorname{ZMod}\left(K\right),\; \forall c \in \operatorname{ZMod}\left(K\right),\; \forall A \in \operatorname{ZMod}\left(K\right),\; \forall B \in \operatorname{ZMod}\left(K\right),\; \forall C \in \operatorname{ZMod}\left(K\right),\; \operatorname{J}\left(K, a, b, c, A, B, C\right) = 2 \cdot \operatorname{val}\left(a + b + c\right) + 2 \cdot \operatorname{val}\left(-(a + b + c) - 1\right) + \operatorname{val}\left(-(a + b + c)\right) + 3 \cdot \operatorname{val}\left(-(A + B + C) - 1\right) + \operatorname{val}\left(A + B + C - 1\right) + \operatorname{val}\left(A + B + C\right) + \operatorname{val}\left(-(A) + b + c\right) + \operatorname{val}\left(-(B) + a + c\right) + \operatorname{val}\left(-(C) + a + b\right) + \operatorname{val}\left(-(a) + B + C\right) + \operatorname{val}\left(-(b) + A + C\right) + \operatorname{val}\left(-(c) + A + B\right)$$

*Formalization.* `D5/S3/QuantumBounds/SliwaSevenArbitraryOutcomeLocalBound.J` (`✓ std3`).

*Citation.* B. Grandjean; Y.-C. Liang; J.-D. Bancal; N. Brunner; N. Gisin (2012). *Bell inequalities for three systems and arbitrarily many measurement outcomes*. DOI: [10.1103/PhysRevA.85.052113](https://doi.org/10.1103/PhysRevA.85.052113). URL: <https://arxiv.org/abs/1204.3829v2>.

*Commentary.*

Appendix B, PDF p. 5, states: “A possible symmetric generalization of Sliwa’s 7th inequality [46] to an arbitrary number of outputs reads as:” The outputs a, b, c encode A_1, B_1, C_1 and A, B, C encode A_2, B_2, C_2, respectively, in ZMod K. The operator val is the least nonnegative residue for K > 0. With S = a+b+c and T = A+B+C, the definition retains all terms and coefficients of (B1). The six mixed brackets completing the party permutations are [-A+b+c]_K, [-B+a+c]_K, [-C+a+b]_K, [-a+B+C]_K, [-b+A+C]_K and [-c+A+B]_K. The first and fourth are the two displayed mixed terms in the source; the other four complete their party permutations. J is natural-valued, and the subtraction K-1 in the bound is natural truncated subtraction; for K >= 2 it agrees with integer subtraction.

**Definition 1.2 (The local-bound clause of the conjecture).**

$$(claim) \Leftrightarrow (\forall K \in \mathbb{N},\; (2 \le K) \Rightarrow (\operatorname{IsLeast}\left(\{z : \mathbb{N} \mid \exists a \in \operatorname{ZMod}\left(K\right),\; \exists b \in \operatorname{ZMod}\left(K\right),\; \exists c \in \operatorname{ZMod}\left(K\right),\; \exists A \in \operatorname{ZMod}\left(K\right),\; \exists B \in \operatorname{ZMod}\left(K\right),\; \exists C \in \operatorname{ZMod}\left(K\right),\; z = \operatorname{J}\left(K, a, b, c, A, B, C\right)\}, 6 \cdot (K - 1)\right)))$$

*Formalization.* `D5/S3/QuantumBounds/SliwaSevenArbitraryOutcomeLocalBound.claim` (`✓ std3`).

*Citation.* B. Grandjean; Y.-C. Liang; J.-D. Bancal; N. Brunner; N. Gisin (2012). *Bell inequalities for three systems and arbitrarily many measurement outcomes*. DOI: [10.1103/PhysRevA.85.052113](https://doi.org/10.1103/PhysRevA.85.052113). URL: <https://arxiv.org/abs/1204.3829v2>.

*Commentary.*

Appendix B, PDF p. 5, gives (B1) verbatim: “2⟨[A_1 + B_1 + C_1]_K⟩ + 2⟨[−A_1 − B_1 − C_1 − 1]_K⟩ + ⟨[−A_1 − B_1 − C_1]_K⟩ + 3⟨[−A_2 − B_2 − C_2 − 1]_K⟩ + ⟨[A_2 + B_2 + C_2 − 1]_K⟩ + ⟨[A_2 + B_2 + C_2]_K⟩ + ⟨[−A_2 + B_1 + C_1]_K⟩ + ⟨[−A_1 + B_2 + C_2]_K⟩ + ⋄ ≥ 6(K − 1), (B1)”. PDF p. 6 states verbatim: “We conjecture that both the local bound and the facet-defining property of inequality (B1) hold for general K.” Only the local-bound clause is encoded and settled here; the facet-defining clause remains open. IsLeast means both that 6(K-1) belongs to the set of deterministic values and that it is no larger than any such value. In Section II, PDF p. 2, fact 1 reads: “It suffices to consider deterministic classical strategies for determining the minimal value of S^{(K)} allowed in a local theory”. A deterministic strategy makes ⟨[X]_K⟩ equal to the residue [X]_K. Local correlations are convex combinations of deterministic strategies, so their values are averages of J and have the same attainable minimum. The convex-mixture interpretation uses the source’s fact 1; the formal statement concerns exactly the deterministic minimum.

**Theorem 1.3 (The sharp bound for every K).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/SliwaSevenArbitraryOutcomeLocalBound.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Grandjean; Y.-C. Liang; J.-D. Bancal; N. Brunner; N. Gisin (2012). *Bell inequalities for three systems and arbitrarily many measurement outcomes*. DOI: [10.1103/PhysRevA.85.052113](https://doi.org/10.1103/PhysRevA.85.052113). URL: <https://arxiv.org/abs/1204.3829v2>.

*Commentary.*

Put s = val(S), t = val(T), u_1 = val(-A+b+c), u_2 = val(-B+a+c), u_3 = val(-C+a+b). Work with their integer representatives. The remaining mixed residues are v_i = (u_i+t-s) mod K, and the sum U of the first three satisfies U = 2s-t+Kq for an integer q. If t >= s, let h count the residues with u_i+t-s >= K. Then L = sum_i(u_i+v_i) = s+t+K(2q-h); for h = 0, 1, 2, 3, the residue ranges force q >= 0, 1, 2, 2. When s = 0 < t and h = 0, q >= 1. If s > t, let h count the residues with u_i < s-t. Then L = s+t+K(2q+h), with q >= 0, 0, 0, -1 for h = 0, 1, 2, 3. Thus L >= s+t, with L >= s+t+K at s = 0 < t. The pure residues give the integer identity J-6(K-1) = L-s-t+K(1_{t=0}-1_{s=0}). The strengthened estimate handles its only negative correction, proving the lower bound. The all-zero strategy attains 6(K-1). The result supplies the all-K local bound used to compare classical and quantum values of (B1); it establishes no facet, quantum optimum or visibility optimum.

## References

- Truth anchor: `D5/S3/QuantumBounds/SliwaSevenArbitraryOutcomeLocalBound.J`
- Truth anchor: `D5/S3/QuantumBounds/SliwaSevenArbitraryOutcomeLocalBound.claim`
- Truth anchor: `D5/S3/QuantumBounds/SliwaSevenArbitraryOutcomeLocalBound.result`
