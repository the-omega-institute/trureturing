# Cubic Characters on Factored Eisenstein Ideals

## Abstract

The local cubic character is selected by the prime-ideal Euler criterion, and factored denominators preserve both multiplication laws.

**Theorem 1.1 (Local uniqueness and composite-denominator multiplication).**

$$\begin{aligned}\operatorname{Admissible}\left(S, P\right) \Rightarrow \forall i \in S, q_{i} = \operatorname{card}\left(\operatorname{Quotient}\left(E, P_{i}\right)\right) \land m_{i} = \frac{q_{i} - 1}{3}\\\operatorname{Admissible}\left(S, P\right) \Rightarrow \forall i \in S, \forall a, \neg (a \in P_{i}) \Rightarrow \operatorname{chi}\left(P_{i}, a\right) \in \mu_{3} \land [\operatorname{chi}\left(P_{i}, a\right)]_{P_{i}} = \left([a]_{P_{i}}\right)^{m_{i}}\\\operatorname{Admissible}\left(S, P\right) \Rightarrow \forall i \in S, \forall a, \neg (a \in P_{i}) \Rightarrow \forall z \in \mu_{3}, [z]_{P_{i}} = \left([a]_{P_{i}}\right)^{m_{i}} \Rightarrow z = \operatorname{chi}\left(P_{i}, a\right)\\\operatorname{Admissible}\left(S, P\right) \Rightarrow \forall i \in S, \forall a,b, \neg (a \in P_{i}) \land \neg (b \in P_{i}) \Rightarrow \operatorname{chi}\left(P_{i}, a \cdot b\right) = \operatorname{chi}\left(P_{i}, a\right) \cdot \operatorname{chi}\left(P_{i}, b\right)\\\operatorname{Chi}\left(S, P, e, a\right) = \prod_{i \in S} \operatorname{chi}\left(P_{i}, a\right)^{e_{i}}\\\operatorname{Admissible}\left(S, P\right) \Rightarrow \forall e,a,b, \operatorname{C}\left(S, a\right) \land \operatorname{C}\left(S, b\right) \Rightarrow \operatorname{Chi}\left(S, P, e, a \cdot b\right) = \operatorname{Chi}\left(S, P, e, a\right) \cdot \operatorname{Chi}\left(S, P, e, b\right)\\\operatorname{Admissible}\left(S, P\right) \Rightarrow \forall e,f,a, \operatorname{C}\left(S, a\right) \Rightarrow \operatorname{Chi}\left(S, P, e + f, a\right) = \operatorname{Chi}\left(S, P, e, a\right) \cdot \operatorname{Chi}\left(S, P, f, a\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/CubicIdealCharacter.cubic_ideal_character_and_factored_multiplicativity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be the Eisenstein order, omega its distinguished cube root of unity, and S a finite index set. Each P_i is maximal, E/P_i is finite of order q_i congruent to one modulo three, and 3 is not in P_i; write Admissible(S,P) for these conditions at every i in S. The exponent m_i is (q_i - 1)/3. The condition C_S(a) means that a lies in none of the P_i.

The function chi at P_i returns one of 1, omega, omega squared. For a outside P_i, its residue is the m_i-th power of a, and no other member of those three roots has that residue. The three classes are distinct because any coincidence would put 3 in P_i. Fermat's theorem and the factorization of T cubed minus one establish existence.

The character of a specified factored denominator is the product of the local characters raised to their ideal multiplicities. It multiplies in the numerator, and adding multiplicities multiplies the denominator characters. The definition never uses one Euler exponent in a composite quotient.

## References

- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/CubicIdealCharacter.cubic_ideal_character_and_factored_multiplicativity`
- Dependency: [D5/S3/Factorization/QuadraticIdeals/EisensteinOddQuotient](EisensteinOddQuotient.md)
