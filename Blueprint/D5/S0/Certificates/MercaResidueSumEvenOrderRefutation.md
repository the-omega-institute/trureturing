# Merca's Even-Order Residue-Sum Conjecture

## Abstract

Merca's printed even-order residue-sum conjecture fails for a = 2 and m = 15.

**Definition 1.1 (Residue sum through the multiplicative order).**

$$\forall m \in \mathrm{Nat}, a \in \mathrm{Nat},\; residueSum\left(m, a\right) = \sum_{i = 1}^{orderOf\left(a: ZMod\left(m\right)\right)} (a^{i} \bmod m)$$

*Formalization.* `D5/S0/Certificates/MercaResidueSumEvenOrderRefutation.residueSum` (`✓ std3`).

*Citation.* Mircea Merca (2011). *Inequalities and Identities Involving Sums of Integer Functions*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL14/Merca/merca3.pdf>.

*Commentary.*

The sum ranges over every natural index i from 1 through orderOf (a : ZMod m), inclusive. Each summand is the least non-negative remainder of a^i modulo m. Here orderOf (a : ZMod m) is Mathlib's multiplicative order of the residue class of a modulo m: the least positive n with a^n congruent to 1 modulo m, and zero when no such n exists. It is the paper's ord_m(a) from page 17. The zero convention is never reached on the claim's domain.

**Definition 1.2 (Conjecture 1).**

$$(claim) \Leftrightarrow (\forall a \in \mathrm{Nat}, m \in \mathrm{Nat},\; (0 < a) \Rightarrow ((0 < m) \Rightarrow ((Nat.Coprime\left(a, m\right)) \Rightarrow ((Nat.Coprime\left(a - 1, m\right)) \Rightarrow ((Even\left(orderOf\left(a: ZMod\left(m\right)\right)\right)) \Rightarrow (2 \cdot residueSum\left(m, a\right) = m \cdot orderOf\left(a: ZMod\left(m\right)\right)))))))$$

*Formalization.* `D5/S0/Certificates/MercaResidueSumEvenOrderRefutation.claim` (`✓ std3`).

*Citation.* Mircea Merca (2011). *Inequalities and Identities Involving Sums of Integer Functions*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL14/Merca/merca3.pdf>.

*Commentary.*

The paper states: "Conjecture 1. Let a and m be relatively prime positive integers. If a−1 and m are relatively prime and ord_m(a) is even then Σ_{i=1}^{ord_m(a)} (a^i mod m) = m · ord_m(a) / 2." The displayed formal equality doubles both sides. This is exact because orderOf (a : ZMod m) is even, so m times the order is divisible by two. Subtraction is natural subtraction and a is positive.

**Theorem 1.3 (Conjecture 1 is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/MercaResidueSumEvenOrderRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/merca-2011-residue-sum-even-order-refutation` (refuted) by `D5/S0/Certificates/MercaResidueSumEvenOrderRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"merca-2011-residue-sum-even-order-refutation","declaration_gid":"D5/S0/Certificates/MercaResidueSumEvenOrderRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mircea Merca (2011). *Inequalities and Identities Involving Sums of Integer Functions*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL14/Merca/merca3.pdf>.

*Commentary.*

At a = 2 and m = 15, both coprimality conditions hold and orderOf (2 : ZMod 15) = 4. The residues are 2, 4, 8, and 1, with sum 15. The conjecture's right side is 15 * 4 / 2 = 30, so the universal claim is false.

## References

- Truth anchor: `D5/S0/Certificates/MercaResidueSumEvenOrderRefutation.claim`
- Truth anchor: `D5/S0/Certificates/MercaResidueSumEvenOrderRefutation.residueSum`
- Truth anchor: `D5/S0/Certificates/MercaResidueSumEvenOrderRefutation.result`
