# Feldman's Balance-Only Conjecture 9.3

## Abstract

Both parity equivalences and finite Laurent coefficients give closed formulas for Feldman's actual balance-only count and the complete three-clause Conjecture 9.3.

The published Section 5 equation (2) determines the six directed forms, the four admissible labels at k=2, and balance at every nonzero residue. Only Conjecture 9.3 is the target: neither all of Open Problem 13.1 nor Conjecture 9.2, cycle closure, or Hamiltonian existence follows from this count.

**Theorem 1.1 (All positive even parameters).**

$$\forall r \in \mathrm{Nat},\; 1 \le r \Rightarrow \operatorname{balancedCount}\left(2 \cdot r\right) = 4 \cdot 6^{r - 1} \cdot \operatorname{choose}\left(2 \cdot r - 2, r - 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/FeldmanConjectureNineThree.balancedCount_even_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David V. Feldman (2026). *The Missing Zigzag: Cycles of Semitone Trichords and a Conservation Law in Equal Temperament*. URL: <https://arxiv.org/html/2609.26114v1>.

*Commentary.*

For every r>=1, the literal count balancedCount(2r) is 4*6^(r-1)*choose(2r-2,r-1). The proof converts the finite Balanced subtype through evenBalancedChoicesEquiv, uses explicit sector reflection, and extracts Laurent coefficient zero at depth 3r-3. Thus the transfer polynomial counts the actual source objects.

**Theorem 1.2 (All positive odd parameters).**

$$\forall r \in \mathrm{Nat},\; 1 \le r \Rightarrow \operatorname{balancedCount}\left(2 \cdot r + 1\right) = 2 \cdot 6^{r} \cdot \operatorname{choose}\left(2 \cdot r - 1, r\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/FeldmanConjectureNineThree.balancedCount_odd_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David V. Feldman (2026). *The Missing Zigzag: Cycles of Semitone Trichords and a Conservation Law in Equal Temperament*. URL: <https://arxiv.org/html/2609.26114v1>.

*Commentary.*

For every r>=1, balancedCount(2r+1) is 2*6^r*choose(2r-1,r). This uses oddBalancedChoicesEquiv and the independently proved singleton charge shift, extracting coefficient -1 at depth 3r-1. Its validity is not inferred from the even antipodal geometry.

**Theorem 1.3 (The three original clauses).**

$$\operatorname{balancedCount}\left(2\right) = 4 \land \left(\left(\forall r \in \mathrm{Nat},\; 2 \le r \Rightarrow \operatorname{balancedCount}\left(2 \cdot r\right) = 4 \cdot \operatorname{balancedCount}\left(2 \cdot r - 1\right)\right) \land \left(\forall r \in \mathrm{Nat},\; 1 \le r \Rightarrow 2 \cdot r \cdot \operatorname{balancedCount}\left(2 \cdot r + 1\right) = 6 \cdot \left(2 \cdot r - 1\right) \cdot \operatorname{balancedCount}\left(2 \cdot r\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/FeldmanConjectureNineThree.feldman_conjecture_nine_three` (`✓ std3`). ∎

*Resolves.* `Problems/feldman-zigzag-conjecture-nine-three` (proved) by `D5/S3/Combinatorics/Zigzag/FeldmanConjectureNineThree.feldman_conjecture_nine_three`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"feldman-zigzag-conjecture-nine-three","declaration_gid":"D5/S3/Combinatorics/Zigzag/FeldmanConjectureNineThree.feldman_conjecture_nine_three","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* David V. Feldman (2026). *The Missing Zigzag: Cycles of Semitone Trichords and a Conservation Law in Equal Temperament*. URL: <https://arxiv.org/html/2609.26114v1>.

*Commentary.*

The sole result states balancedCount 2=4; for every r>=2, balancedCount(2r)=4*balancedCount(2r-1); and for every r>=1, (2r)*balancedCount(2r+1)=6*(2r-1)*balancedCount(2r). The proof specializes the exact even and odd formulas and uses central-binomial and adjacent-choose identities. Every parameter range is preserved.

The typed open-problem resolution claim binds this frozen theorem to the Problems dossier for Conjecture 9.3. It does not assert a resolution of the broader Open Problem 13.1 or publication priority.

## References

- Truth anchor: `D5/S3/Combinatorics/Zigzag/FeldmanConjectureNineThree.balancedCount_even_closed`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/FeldmanConjectureNineThree.balancedCount_odd_closed`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/FeldmanConjectureNineThree.feldman_conjecture_nine_three`
- Dependency: [D5/S3/Combinatorics/Zigzag/EvenPaths](EvenPaths.md)
- Dependency: [D5/S3/Combinatorics/Zigzag/LaurentCoefficients](LaurentCoefficients.md)
- Dependency: [D5/S3/Combinatorics/Zigzag/OddPaths](OddPaths.md)
