# Cyclotomic Five Residue Sums

## Abstract

Units whose fifth cyclotomic value is again a unit sum to something whose five-adic valuation is one short of the modulus.

Indices and values are natural numbers; reduction is natural remainder. A residue is admissible for a modulus when it is coprime to that modulus and the fifth cyclotomic value at it is coprime as well. The sum below runs over the admissible residues strictly between zero and the modulus.

**Definition 1.1 (The fifth cyclotomic value).**

$$\forall u \in \mathbb{N}, \operatorname{phi5}\left(u\right) = {u}^{4} + {u}^{3} + {u}^{2} + u + 1$$

*Formalization.* `D5/S3/Arith/CyclotomicFiveResidueSum.phi5` (`✓ std3`).

*Citation.* OEIS Foundation Inc. (2024). *OEIS A290322*. URL: <https://oeis.org/A290322>.

*Commentary.*

The quartic whose roots are the primitive fifth roots of unity. It is written out rather than taken from a cyclotomic library so that the arithmetic below stays elementary.

**Definition 1.2 (The admissible residues).**

$$\forall n \in \mathbb{N}, \operatorname{goodUnits}\left(n\right) = \{ u \mid 1 \leq u < n \land \operatorname{gcd}\left(u, n\right) = 1 \land \operatorname{gcd}\left(\operatorname{phi5}\left(u\right), n\right) = 1 \}$$

*Formalization.* `D5/S3/Arith/CyclotomicFiveResidueSum.goodUnits` (`✓ std3`).

*Citation.* OEIS Foundation Inc. (2024). *OEIS A290322*. URL: <https://oeis.org/A290322>.

*Commentary.*

Both coprimality conditions are required. The companion counting sequence in the source tracks the size of this set; the statement here concerns its weighted first moment instead.

**Lemma 1.3 (Where the value vanishes modulo five).**

$$\forall u \in \mathbb{N}, \operatorname{phi5}\left(u\right) \bmod 5 = 0 \iff u \bmod 5 = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CyclotomicFiveResidueSum.phi5_mod_five_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Modulo five the quartic takes the value one at every residue except one, where it vanishes. So for a power of five the admissible residues are exactly those congruent to two, three or four.

**Theorem 1.4 (The sum over a power of five).**

$$\forall a \in \mathbb{N}, \sum_{u \in \operatorname{goodUnits}\left({5}^{a + 1}\right)} u = 9 \cdot {5}^{a} + 15 \cdot \frac{{5}^{a} \cdot \left({5}^{a} - 1\right)}{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CyclotomicFiveResidueSum.sum_goodUnits_five_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The admissible representatives are the three surviving residues shifted by multiples of five, so the sum splits into three arithmetic progressions with a common step. This is an exact equality, not a congruence.

**Theorem 1.5 (The count at a prime).**

$$\forall p \operatorname{prime}\left(p\right), p \neq 5 \Rightarrow \operatorname{residueCount}\left(p\right) = p - \operatorname{gcd}\left(p - 1, 5\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CyclotomicFiveResidueSum.residueCount_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over a prime field the product of the quartic with one less than the variable is the fifth power minus one, and away from characteristic five the value one is not a root of the quartic. The excluded units are therefore the nontrivial fifth roots of unity, and the unit group being cyclic makes their number a greatest common divisor. Both possible values leave a count prime to five.

**Theorem 1.6 (The count avoids five).**

$$\forall m \in \mathbb{N}, \neg(5 \mid m) \Rightarrow \neg(5 \mid \operatorname{residueCount}\left(m\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CyclotomicFiveResidueSum.residueCount_not_dvd_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both branches of the count at a prime are prime to five, and the count is multiplicative, so the property survives to any modulus prime to five.

**Theorem 1.7 (Splitting the sum).**

$$\forall m, n, \operatorname{gcd}\left(m, n\right) = 1 \Rightarrow (\sum_{u \in \operatorname{goodUnits}\left(m \cdot n\right)} u) = \operatorname{residueCount}\left(n\right) \cdot (\sum_{u \in \operatorname{goodUnits}\left(m\right)} u) \mathrm{in} \operatorname{ZMod}\left(m\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CyclotomicFiveResidueSum.sum_goodUnits_mul_cast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The remainder theorem makes the admissible set a product, and each admissible residue of the first factor appears once for every admissible residue of the second. The identity is one sided and lives in the residue ring of the first factor, where the count of the second enters as a scalar; that is all the argument downstream needs.

**Theorem 1.8 (The conjecture).**

$$\forall n \in \mathbb{N}, 2 \leq n \land 5 \mid n \Rightarrow \sum_{u \in \operatorname{goodUnits}\left(n\right)} u \bmod n \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CyclotomicFiveResidueSum.residue_sum_ne_zero` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a290322-cyclotomic-five-residue-sum` (proved) by `D5/S3/Arith/CyclotomicFiveResidueSum.residue_sum_ne_zero`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a290322-cyclotomic-five-residue-sum","declaration_gid":"D5/S3/Arith/CyclotomicFiveResidueSum.residue_sum_ne_zero","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2024). *OEIS A290322*. URL: <https://oeis.org/A290322>.

*Commentary.*

The three preceding results give the sum, modulo the power of five in the modulus, as a count prime to five times something whose valuation is one short. So the valuation of the sum is exactly one short of the modulus, and in particular the modulus does not divide it. Nothing is claimed for moduli not divisible by five, where the sum often is a multiple.

## References

- Truth anchor: `D5/S3/Arith/CyclotomicFiveResidueSum.goodUnits`
- Truth anchor: `D5/S3/Arith/CyclotomicFiveResidueSum.phi5`
- Truth anchor: `D5/S3/Arith/CyclotomicFiveResidueSum.phi5_mod_five_eq_zero_iff`
- Truth anchor: `D5/S3/Arith/CyclotomicFiveResidueSum.residueCount_not_dvd_five`
- Truth anchor: `D5/S3/Arith/CyclotomicFiveResidueSum.residueCount_prime`
- Truth anchor: `D5/S3/Arith/CyclotomicFiveResidueSum.residue_sum_ne_zero`
- Truth anchor: `D5/S3/Arith/CyclotomicFiveResidueSum.sum_goodUnits_five_pow`
- Truth anchor: `D5/S3/Arith/CyclotomicFiveResidueSum.sum_goodUnits_mul_cast`
- Dependency: [D5/S3/Arith/ChineseRemainder](ChineseRemainder.md)
