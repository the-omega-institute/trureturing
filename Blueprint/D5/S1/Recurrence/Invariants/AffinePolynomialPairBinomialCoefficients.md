# The affine polynomial pair of OEIS A208509

## Abstract

The affine polynomial pair has Werner's all-column binomial formula.

The pair takes natural stages to pairs of polynomials in Z[X]. The functions first and second select its polynomial components; coeff selects a natural degree. The function natSub is truncated natural subtraction, binomial is Nat.choose, and intCast casts a natural number to an integer. Constants one and X in the defining equations are polynomials.

**Definition 1.1 (The actual affine polynomial recursion).**

$$\begin{aligned}\operatorname{first}\left(\operatorname{pair}\left(0\right)\right) = 1 \land \operatorname{second}\left(\operatorname{pair}\left(0\right)\right) = 1\\\forall m \in Nat, \operatorname{first}\left(\operatorname{pair}\left(m + 1\right)\right) = \operatorname{first}\left(\operatorname{pair}\left(m\right)\right) + X \cdot \operatorname{second}\left(\operatorname{pair}\left(m\right)\right) \land \operatorname{second}\left(\operatorname{pair}\left(m + 1\right)\right) = \operatorname{first}\left(\operatorname{pair}\left(m\right)\right) + \operatorname{second}\left(\operatorname{pair}\left(m\right)\right) + 1\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Invariants/AffinePolynomialPairBinomialCoefficients.pair` (`✓ std3`).

*Citation.* Knud Werner (2022). *Conjectured coefficient formula in OEIS A208509*. URL: <https://oeis.org/A208509>.

*Commentary.*

Source index n>=1 corresponds to stage n-1: u(n,X)=first(pair(n-1)) and v(n,X)=second(pair(n-1)). Thus u(1,X)=v(1,X)=1, and for every n>=2 the source laws are u(n,X)=u(n-1,X)+X*v(n-1,X) and v(n,X)=u(n-1,X)+v(n-1,X)+1. These are the laws in A208509 revision 28 and its companion A208508 revision 10.

**Theorem 1.2 (Werner's binomial coefficient formula).**

$$\forall n \in Nat, 1 \le n \Rightarrow \forall k \in Nat, \operatorname{coeff}\left(\operatorname{second}\left(\operatorname{pair}\left(\operatorname{natSub}\left(n, 1\right)\right)\right), k\right) = \operatorname{intCast}\left(\operatorname{binomial}\left(\operatorname{natSub}\left(n, 1\right), 2 \cdot k + 1\right)\right) + \operatorname{intCast}\left(\operatorname{binomial}\left(n, 2 \cdot k + 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/AffinePolynomialPairBinomialCoefficients.werner_a208509` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a208509-affine-polynomial-pair-binomial-coefficients` (proved) by `D5/S1/Recurrence/Invariants/AffinePolynomialPairBinomialCoefficients.werner_a208509`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a208509-affine-polynomial-pair-binomial-coefficients","declaration_gid":"D5/S1/Recurrence/Invariants/AffinePolynomialPairBinomialCoefficients.werner_a208509","resolution_kind":"proved"} -->

*Citation.* Knud Werner (2022). *Conjectured coefficient formula in OEIS A208509*. URL: <https://oeis.org/A208509>.

*Commentary.*

The coefficient of X^k in the actual second polynomial equals the two displayed integer binomial coefficients for every n>=1 and every k>=0. There is no degree or column bound; zero tails are included. The n=0 extension introduced by truncated subtraction is outside the conclusion. Simultaneous induction proves the odd-binomial formula for the second component and the even-binomial formula for the first component, with the degree-zero correction subtracted from the latter. The odd step uses both preceding components; the even step uses the shifted odd component. Pascal identities normalize these coupled steps and cancel the affine constant. The conjecture is attributed to Knud Werner, Jan 11 2022; Clark Kimberling authored the OEIS entry. The bounded supplier and literature screen establishes neither worldwide openness nor publication priority. The distinct frozen JointPolynomialPairBinomialCoefficients uses v_next=X*u+X*v and does not identify this affine second family.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/AffinePolynomialPairBinomialCoefficients.pair`
- Truth anchor: `D5/S1/Recurrence/Invariants/AffinePolynomialPairBinomialCoefficients.werner_a208509`
