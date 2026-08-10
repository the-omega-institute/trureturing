# Fermat's Little Theorem

## Abstract

A power one below a prime is congruent to one when the prime does not divide the base.

**Theorem 1.1 (A base not divisible by a prime has power p minus one congruent to one).**

$$\forall p,a\in\mathbb{N},\ p\ \text{prime} \land \neg(p \mid a) \Rightarrow a^{p-1} \equiv 1\ (\operatorname{mod}\ p)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/FermatLittle.fermat_little_theorem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural prime p and natural base a, if p does not divide a, then a raised to p minus one is congruent to one modulo p. The explicit primality and nondivisibility premises preserve the source atom's full scope, and the conclusion is an exact natural-number modular congruence.

Pinned Mathlib already proves the congruence from coprimality as Nat.ModEq.pow_card_sub_one_eq_one. Its theorem Nat.Prime.coprime_iff_not_dvd converts the stated nondivisibility premise to that library hypothesis. The Lean declaration is therefore a thin repository-addressed wrapper, not a reproof of the classical permutation argument recorded with the source atom. No numerical certificate is asserted.

## References

- Truth anchor: `D5/S3/ArithUnits/FermatLittle.fermat_little_theorem`
