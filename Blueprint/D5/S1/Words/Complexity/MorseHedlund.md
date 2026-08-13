# The One-Sided Morse-Hedlund Theorem

## Abstract

Low factor complexity forces eventual periodicity for every one-sided word over a finite alphabet.

Let x be a one-sided infinite word over an arbitrary finite alphabet. Factors begin at natural indices. The conclusion permits a finite prefix before exact repetition, matching the one-sided convention throughout the repository.

**Definition 1.1 (The factor set contains exactly the factors at natural starts).**

$$F_x(n) = \{(x(i+k))_{k\in Fin(n)} : i\in\mathbb{N}\}$$

*Formalization.* `D5/S1/Words/Complexity/MorseHedlund.wordFactorSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A length-n factor is represented by a function from Fin n to the alphabet. The finite ambient function type is filtered by occurrence at some natural starting index.

**Theorem 1.2 (Low factor complexity forces eventual periodicity).**

$$(\exists n\in\mathbb{N},\ \operatorname{card}(F_x(n)) \leq n) \Rightarrow \exists s,p\in\mathbb{N},\ 0 < p \land \forall t\in\mathbb{N},\ x(s+t+p)=x(s+t)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/MorseHedlund.eventuallyPeriodic_of_factor_complexity_le` (`✓ std3`). ∎

*Citation.* Marston Morse and Gustav A. Hedlund (1940). *Symbolic Dynamics II. Sturmian Trajectories*. DOI: [10.2307/2371431](https://doi.org/10.2307/2371431).

*Commentary.*

Deleting the last letter maps length-(n+1) factors onto length-n factors, so complexity is monotone and begins at one. A bound at N therefore forces a flat step below N.

At a flat step the deletion map is bijective, hence every occurring factor has a unique right extension. Two equal factors among one more natural starts than there are factors propagate forever and give a positive period on a tail.

This is the one-sided finite-alphabet theorem only. It asserts neither recurrence nor balance, and it does not classify Sturmian words.

**Theorem 1.3 (Every non-eventually-periodic word has the n plus one complexity floor).**

$$\neg(\exists s,p\in\mathbb{N},\ 0 < p \land \forall t\in\mathbb{N},\ x(s+t+p)=x(s+t)) \Rightarrow \forall n\in\mathbb{N},\ n+1 \leq \operatorname{card}(F_x(n))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/MorseHedlund.factor_complexity_ge_add_one_of_not_eventuallyPeriodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the direct contrapositive of the one-sided Morse-Hedlund theorem. The inequality is stated as n plus one less than or equal to the factor count, avoiding a hidden conversion between strict and non-strict bounds.

## References

- Truth anchor: `D5/S1/Words/Complexity/MorseHedlund.eventuallyPeriodic_of_factor_complexity_le`
- Truth anchor: `D5/S1/Words/Complexity/MorseHedlund.factor_complexity_ge_add_one_of_not_eventuallyPeriodic`
- Truth anchor: `D5/S1/Words/Complexity/MorseHedlund.wordFactorSet`
