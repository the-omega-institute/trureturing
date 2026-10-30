# Prime Odd-Character Moments on Native Units

## Abstract

The first character moment over actual residue units equals the all-residue weighted sum. For a prime modulus, a nonprincipal odd character has a nonzero moment.

All sums take values in the complex numbers. Each weight is the natural representative of the residue, coerced before multiplication. The units are the same native unit groups used for the least-residue coset moments. At a modulus greater than one their representatives are positive and strictly below the modulus. The definition and extension-by-zero equality require only NeZero n, and include n = 1: the sole residue has natural representative zero, so both weighted sums vanish. Character values at units mean values at their underlying ZMod residues. The prime nonvanishing argument uses the licensed Yao Xu supplier cited below. In the displayed formulas c denotes the source character χ.

Audit status (current evidence): exactly three Reg source-equivalence records are declared_validated: Reg.D5.S3.Analytic.Zeta.CatalanPrimeOddMoment.argumentFamily for D5.S3.Analytic.Zeta.CatalanPrimeOddMoment.arg_one_sub_exp_two_pi; Reg.D5.S3.Analytic.Zeta.CatalanPrimeOddMoment.family for D5.S3.Analytic.Zeta.CatalanPrimeOddMoment.hurwitzZeta_apply_zero_of_mem_Ioo; and Reg.D5.S3.Analytic.Zeta.CatalanPrimeOddMoment.sineFamily for D5.S3.Analytic.Zeta.CatalanPrimeOddMoment.sinZeta_one_eq_of_mem_Ioo. The continuation is open/unknown, with 17 additional unvalidated unfinished audit targets tracked at https://github.com/the-omega-institute/trureturing/issues/17346#issuecomment-6304013114. These three records do not complete the 17 audits and do not establish an inexhaustibility result. The current evidence ceiling is standard axiom closure, not Reg admission completion or a full audit certificate. The archived extension_by_zero consumer failure remains un-restored. Exact remaining exclusions are the composite induced-character weighted-moment identity, strict sign, class-number formula, collision converse, quartic or sextic family conclusions, and broader 21-paper completion.

**Definition 1.1 (The unit character moment).**

$$\forall (n:\mathbb{N}), [\operatorname{NeZero}(n)] \forall (c:\operatorname{DirichletCharacter}(\mathbb{C},n)), A_{n}(c) = \sum_{u:(\mathbb{Z}/n\mathbb{Z})^{\times}} \operatorname{val}(u) c(u)$$

*Formalization.* `D5/S3/ArithUnits/MercaPrimeCharacterMoment.characterMoment` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yao Xu (2026). *catalan-lean4: CharacterSpecialValue*. URL: <https://github.com/cadamcat/catalan-lean4/blob/3dc9375da48d13751fd291f3ee0fda8fa18be56d/Catalan/Stickelberger/CharacterSpecialValue.lean>.

*Commentary.*

The sum ranges over every actual unit exactly once.

**Theorem 1.2 (Extension by zero on nonunits).**

$$\forall (n:\mathbb{N}), [\operatorname{NeZero}(n)] \forall (c:\operatorname{DirichletCharacter}(\mathbb{C},n)), A_{n}(c) = \sum_{a:\operatorname{ZMod}(n)} \operatorname{val}(a) c(a)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/MercaPrimeCharacterMoment.character_moment_eq_zmod_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yao Xu (2026). *catalan-lean4: CharacterSpecialValue*. URL: <https://github.com/cadamcat/catalan-lean4/blob/3dc9375da48d13751fd291f3ee0fda8fa18be56d/Catalan/Stickelberger/CharacterSpecialValue.lean>.

*Commentary.*

The unit coercion is injective. Every residue outside its image is a nonunit, where a Dirichlet character vanishes. Mapping the finite unit set and adjoining these zero summands proves the equality.

**Theorem 1.3 (Nonvanishing at the full prime odd-character domain).**

$$\forall (p:\mathbb{N}), [\operatorname{Prime}(p)] \forall (c:\operatorname{DirichletCharacter}(\mathbb{C},p)), c\neq1 \land c(-1)=-1 \Rightarrow A_{p}(c)\neq0$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/MercaPrimeCharacterMoment.prime_odd_character_moment_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yao Xu (2026). *catalan-lean4: CharacterSpecialValue*. URL: <https://github.com/cadamcat/catalan-lean4/blob/3dc9375da48d13751fd291f3ee0fda8fa18be56d/Catalan/Stickelberger/CharacterSpecialValue.lean>.

*Commentary.*

Apply the prime odd-character weighted-sum theorem to the preceding finite-sum identity. The nonprincipal and odd hypotheses remain explicit. This result supplies the prime moment required by the Merca collision converse. It does not assert the corresponding formula at a composite induced level, or the collision, quartic or sextic family conclusions.

## References

- Truth anchor: `D5/S3/ArithUnits/MercaPrimeCharacterMoment.characterMoment`
- Truth anchor: `D5/S3/ArithUnits/MercaPrimeCharacterMoment.character_moment_eq_zmod_sum`
- Truth anchor: `D5/S3/ArithUnits/MercaPrimeCharacterMoment.prime_odd_character_moment_ne_zero`
- Dependency: [D5/S3/Analytic/Zeta/CatalanPrimeOddMoment](../Analytic/Zeta/CatalanPrimeOddMoment.md)
- Dependency: [D5/S3/ArithUnits/MercaCosetFiberLift](MercaCosetFiberLift.md)
