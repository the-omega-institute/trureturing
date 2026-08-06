# Golden Prime Splitting

## Abstract

Prime splitting and inertia in the golden integers are classified by residue classes modulo five.

**Theorem 1.1 (Quadratic-residue criterion).**

$$\forall p \in \mathbb{N},\ \operatorname{Prime}(p) \land p\neq5 \land p\neq2 \Rightarrow (\operatorname{IsSquare}(5 : \operatorname{ZMod} p) \Leftrightarrow p\equiv\pm1\ (\operatorname{mod} 5))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenSplitSufficient.five_is_square_mod_prime_iff_mod_five_eq_one_or_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural prime p distinct from both five and two, five is a square in ZMod p if and only if p is congruent to one or minus one modulo five. The exclusion of two is explicit because five is a square modulo two although two belongs to a nonsquare residue class modulo five.

**Theorem 1.2 (Split-prime criterion).**

$$\forall p \in \mathbb{N},\ \operatorname{Prime}(p) \land p\neq5 \Rightarrow (\neg\operatorname{Prime}(p : \operatorname{GoldenInt}) \Leftrightarrow p\equiv\pm1\ (\operatorname{mod} 5))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenSplitSufficient.golden_not_prime_iff_mod_five_eq_one_or_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural prime p other than five, its image fails to remain prime in the golden integers exactly when p is congruent to one or minus one modulo five. Failure to remain prime is the formal splitting predicate used here.

**Theorem 1.3 (Inert-prime criterion).**

$$\forall p \in \mathbb{N},\ \operatorname{Prime}(p) \land p\neq5 \Rightarrow (\operatorname{Prime}(p : \operatorname{GoldenInt}) \Leftrightarrow (p\equiv2 \lor p\equiv3)\ (\operatorname{mod} 5))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenSplitSufficient.golden_prime_iff_mod_five_eq_two_or_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural prime p other than five, its image remains prime in the golden integers exactly when p is congruent to two or three modulo five, equivalently plus or minus two modulo five.

## References

- Truth anchor: `D5/S3/Arith/GoldenSplitSufficient.five_is_square_mod_prime_iff_mod_five_eq_one_or_four`
- Truth anchor: `D5/S3/Arith/GoldenSplitSufficient.golden_not_prime_iff_mod_five_eq_one_or_four`
- Truth anchor: `D5/S3/Arith/GoldenSplitSufficient.golden_prime_iff_mod_five_eq_two_or_three`
- Dependency: [D5/S3/Arith/GoldenPrimeSplitting](GoldenPrimeSplitting.md)
