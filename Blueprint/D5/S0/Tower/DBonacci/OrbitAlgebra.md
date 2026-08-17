# D-Bonacci Orbit Algebra

## Abstract

Typed d-bonacci refinement isolates the uniform interval algebra of the period-two orbit.

A gap is indexed by a letter in Fin d and carries its two endpoint arms. Strict monotonicity of gap lengths identifies the geometric substitution witness with that same typed letter.

**Theorem 1.1 (Right-child affine arm law).**

$$\forall letter \in \operatorname{nonzeroGapLetter}\left(d\right),\; \operatorname{rightChild}\left(\operatorname{IsDBonacciLetterOrbitGap}\left(d, Q, x, \mathit{letter}, L, R\right)\right) = \operatorname{IsDBonacciLetterOrbitGap}\left(d, Q + 1, x, \operatorname{predecessor}\left(\mathit{letter}\right), \operatorname{dbonacciPerronRoot}\left(d\right) \cdot L - 1, \operatorname{dbonacciPerronRoot}\left(d\right) \cdot R\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/OrbitAlgebra.letter_orbit_gap_right_child` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every order d at least two and every nonzero gap letter, the right child has predecessor letter. Its normalized arms are beta times the old arms, with one unit removed from the left arm.

**Theorem 1.2 (Left-child affine arm law).**

$$\forall letter \in \operatorname{nonzeroGapLetter}\left(d\right),\; \operatorname{leftChild}\left(\operatorname{IsDBonacciLetterOrbitGap}\left(d, Q, x, \mathit{letter}, L, R\right)\right) = \operatorname{IsDBonacciLetterOrbitGap}\left(d, Q + 1, x, \operatorname{topGapLetter}\left(d\right), \operatorname{dbonacciPerronRoot}\left(d\right) \cdot L, 1 - \operatorname{dbonacciPerronRoot}\left(d\right) \cdot L\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/OrbitAlgebra.letter_orbit_gap_left_child` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The left child returns to the top letter. Its left arm is beta times the old left arm and its right arm is the complementary quantity.

**Theorem 1.3 (Uniform top-predecessor period two).**

$$\forall k \in N,\; \operatorname{topPredecessorPeriodTwoOrbit}\left(d, k, x\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/OrbitAlgebra.top_predecessor_period_two_orbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary d at least three, a typed top-gap base case and four scalar beta arm identities imply the full right-left period-two orbit by induction.

**Theorem 1.4 (Order four is one substitution instance).**

$$\forall k \in N,\; \operatorname{fourChampionGapOrbit}\left(k\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/OrbitAlgebra.four_champion_gap_orbit_reproved` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen order-four base gap and scalar identities instantiate the uniform theorem and recover the exact original orbit statement.

## References

- Truth anchor: `D5/S0/Tower/DBonacci/OrbitAlgebra.four_champion_gap_orbit_reproved`
- Truth anchor: `D5/S0/Tower/DBonacci/OrbitAlgebra.letter_orbit_gap_left_child`
- Truth anchor: `D5/S0/Tower/DBonacci/OrbitAlgebra.letter_orbit_gap_right_child`
- Truth anchor: `D5/S0/Tower/DBonacci/OrbitAlgebra.top_predecessor_period_two_orbit`
- Dependency: [D5/S0/Tower/DBonacci/ChampionOrbit](ChampionOrbit.md)
- Dependency: [D5/S0/Tower/DBonacci/GapAlphabet](GapAlphabet.md)
