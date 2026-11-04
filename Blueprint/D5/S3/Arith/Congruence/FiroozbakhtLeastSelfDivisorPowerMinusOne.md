# The Least Self-Divisor Exponent

## Abstract

The least self-divisor exponent in OEIS A092028 is the least prime factor of n minus one.

**Definition 1.1 (The A092028 sequence).**

$$\forall n \in \mathbb{N},\; a\left(n\right) = sInf\left(\{m \in \mathbb{N} \mid (1 < m) \land (m \mid n^{m} - 1)\}\right)$$

*Formalization.* `D5/S3/Arith/Congruence/FiroozbakhtLeastSelfDivisorPowerMinusOne.a` (`✓ std3`).

*Citation.* Farideh Firoozbakht (2004). *OEIS A092028, a(n) is the smallest m > 1 such that m divides n^m-1*. URL: <https://oeis.org/A092028>.

*Commentary.*

In the natural numbers, `sInf` selects the least element of the set, and `sInf` of the empty set is zero. For n greater than two, the defining set is nonempty. Every subtraction in the formula is truncated natural-number subtraction.

**Theorem 1.2 (Firoozbakht's second conjecture).**

$$\forall n \in \mathbb{N},\; (2 < n) \Rightarrow (a\left(n\right) = minFac\left(n - 1\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/FiroozbakhtLeastSelfDivisorPowerMinusOne.firoozbakht_a092028` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a092028-least-self-divisor-power-minus-one` (proved) by `D5/S3/Arith/Congruence/FiroozbakhtLeastSelfDivisorPowerMinusOne.firoozbakht_a092028`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a092028-least-self-divisor-power-minus-one","declaration_gid":"D5/S3/Arith/Congruence/FiroozbakhtLeastSelfDivisorPowerMinusOne.firoozbakht_a092028","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

The upper bound uses p=minFac(n-1), since p divides n-1 and therefore p divides n^p-1. For the lower bound, take q=minFac(m). The multiplicative order of n modulo q divides both m and q-1; minimality of q makes those integers coprime, so the order is one and q divides n-1. Firoozbakht's first conjecture follows because minFac(n-1) is prime when n is greater than two.

Application: Harvey P. Dale's A014865 recurrence. Let t be any integer-valued sequence with t(1)=1 and, for every integer j at least two, t(j)=15t(j-1)+j. Its values at nonpositive indices are unrestricted. Define the natural-valued sequence s by the following recurrence.

$(s\left(0\right) = 0) \land (\forall k \in \mathbb{N},\; s\left(k + 1\right) = 15 \cdot s\left(k\right) + k + 1)$

For every positive natural k, induction using the original recurrence at j=k+1 gives t(k)=s(k), with the natural value cast to the integers. Every positive integer n is the cast of the positive natural k=n.toNat. Consequently n divides t(n) in the integers exactly when k divides s(k) in the naturals; this is the natural-cast divisibility equivalence Int.natCast_dvd_natCast. Thus the encoding includes every original positive index, and places no extra condition on that index. At index one, s(1)=1, so the qualifying class is nonempty.

The order-one recurrence with coefficient 15 has a unique solution for a fixed initial value, by LinearRecurrence.eq_iff_eqOn_range_order. The sequences 196s(k)+14k+15 and 15^(k+1) both satisfy it and both start at 15. Hence the following identity holds even at k=0.

$\forall k \in \mathbb{N},\; 196 \cdot s\left(k\right) + 14 \cdot k + 15 = 15^{k + 1}$

For a positive qualifying k, choose q in the naturals with s(k)=kq. Rearranging the identity gives the next equation and therefore k divides 15(15^k-1). In the original integer notation the closed form is 196t(n)=15^(n+1)-14n-15 for every positive n.

$\forall k \in \mathbb{N},\; \forall q \in \mathbb{N},\; ((0 < k) \land (s\left(k\right) = k \cdot q)) \Rightarrow (15 \cdot (15^{k} - 1) = 14 \cdot k \cdot (1 + 14 \cdot q))$

Oddness follows from the existing two-adic LTE theorem padicValNat.pow_two_sub_one at x=15 and an even positive exponent k. Its hypotheses hold: 1<15, two does not divide 15, k is nonzero, and k is even in the contradiction case. The theorem gives v2(15^k-1)+1=v2(16)+v2(14)+v2(k)=5+v2(k). The power difference is positive because k>0; 1+14q is positive and odd. Thus all factors used with padicValNat.mul are nonzero. The displayed identity would equate valuations v2(k)+4 and v2(k)+1, a contradiction. This proves oddness rather than assuming it.

For k>1, if neither three nor five divides k, then gcd(k,15)=1. Cancellation yields k divides 15^k-1. Put p=minFac(k), a prime divisor of k. In ZMod p the residue of 15 has kth power one and is nonzero. By orderOf_dvd_of_pow_eq_one and ZMod.orderOf_dvd_card_sub_one its order d divides both k and p-1. Nat.coprime_of_lt_minFac gives gcd(k,p-1)=1, so d=1. Then orderOf_eq_one_iff and the natural-cast congruence bridge give p divides 14. Oddness excludes p=2, hence p=7 and seven divides k. The other branches give divisibility by three or five directly; the disjunction is inclusive.

This order argument is the local divisibility step in minFac_sub_one_le_of_dvd_pow_sub_one. That private declaration concludes only minFac(N-1) <= m; neither that bound nor the public A092028 equality alone states minFac(m) divides N-1. The application above uses the finite-field order argument itself, with N=15 and m=k, and the named Mathlib order and coprimality facts. The same argument appears in the solution to Problem 3 of Parvardi's Lifting The Exponent Lemma, version 6; its Theorem 4 in section 4 (page 4) gives the two-adic identity used above, and the solution to Problem 3 is in section 6 (page 7): https://s3.amazonaws.com/aops-cdn.artofproblemsolving.com/resources/articles/lifting-the-exponent.pdf.

If a qualifying k>7 were prime, every divisor three, five or seven supplied by the alternative would have to equal k. Each equality contradicts k>7. Thus k>1 and k is not prime, the usual composite condition. Transporting the three conclusions along the positive-index correspondence gives the following statement for the original sequence t.

$\forall n \in \mathbb{Z},\; ((0 < n) \land (n \mid t\left(n\right))) \Rightarrow ((Odd\left(n\right)) \land (((7 < n) \Rightarrow ((1 < n) \land (\neg Prime\left(toNat\left(n\right)\right)))) \land ((1 < n) \Rightarrow ((3 \mid n) \lor ((5 \mid n) \lor (7 \mid n))))))$

Here Prime(toNat(n)) is primality of the positive natural represented by n. The hypotheses on t are exactly its initial value and recurrence above, and all divisibilities in this last formula are integer divisibilities. No conclusion is asserted for indices outside the qualifying class. The recurrence and thresholds are those of OEIS A014865, revision 18, whose entry authors are N. J. A. Sloane and Olivier Gérard and whose conjectural clauses are attributed to Harvey P. Dale: https://oeis.org/A014865/internal. These are applications of recurrence uniqueness, LTE and finite-field order facts; they imply no claim about the current literature status or originality of the historical clauses.

## References

- Truth anchor: `D5/S3/Arith/Congruence/FiroozbakhtLeastSelfDivisorPowerMinusOne.a`
- Truth anchor: `D5/S3/Arith/Congruence/FiroozbakhtLeastSelfDivisorPowerMinusOne.firoozbakht_a092028`
