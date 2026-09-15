# The OEIS A008365 Four-Residue Characterization of 13-Rough Numbers

## Abstract

The prime 17 refutes Detlefs's four-residue characterization of 13-rough numbers.

**Definition 1.1 (The 13-rough numbers).**

$$\forall n \in \mathrm{Nat},\; (\operatorname{isRough13}\left(n\right)) \Leftrightarrow (\forall p \in \mathrm{Nat},\; (\operatorname{Prime}\left(p\right)) \Rightarrow ((p \mid n) \Rightarrow (13 \le p)))$$

*Formalization.* `D5/S0/Certificates/DetlefsRoughResidueCharacterizationRefutation.isRough13` (`✓ std3`).

*Citation.* N. J. A. Sloane; Gary Detlefs (2011). *OEIS A008365, 13-rough numbers: positive integers that have no prime factors less than 13*. URL: <https://oeis.org/A008365>.

*Commentary.*

For each natural n, isRough13(n) holds when every prime divisor p of n is at least 13.

**Definition 1.2 (Detlefs's four residue classes).**

$$\forall n \in \mathrm{Nat},\; (\operatorname{inResidueSet}\left(n\right)) \Leftrightarrow ((n^{24} \bmod 2310 = 1) \lor \left((n^{24} \bmod 2310 = 421) \lor \left((n^{24} \bmod 2310 = 631) \lor (n^{24} \bmod 2310 = 841)\right)\right))$$

*Formalization.* `D5/S0/Certificates/DetlefsRoughResidueCharacterizationRefutation.inResidueSet` (`✓ std3`).

*Citation.* N. J. A. Sloane; Gary Detlefs (2011). *OEIS A008365, 13-rough numbers: positive integers that have no prime factors less than 13*. URL: <https://oeis.org/A008365>.

*Commentary.*

For each natural n, inResidueSet(n) holds when its twenty-fourth power modulo 2310 is one of 1, 421, 631, and 841.

**Definition 1.3 (Detlefs's rough-number characterization).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; (0 < n) \Rightarrow ((\operatorname{isRough13}\left(n\right)) \Leftrightarrow (\operatorname{inResidueSet}\left(n\right))))$$

*Formalization.* `D5/S0/Certificates/DetlefsRoughResidueCharacterizationRefutation.claim` (`✓ std3`).

*Citation.* N. J. A. Sloane; Gary Detlefs (2011). *OEIS A008365, 13-rough numbers: positive integers that have no prime factors less than 13*. URL: <https://oeis.org/A008365>.

*Commentary.*

For every positive natural n, the characterization identifies being 13-rough exactly with membership in the four residue classes.

**Theorem 1.4 (The characterization fails at 17).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/DetlefsRoughResidueCharacterizationRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a008365-detlefs-rough-residue-characterization-refutation` (refuted) by `D5/S0/Certificates/DetlefsRoughResidueCharacterizationRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a008365-detlefs-rough-residue-characterization-refutation","declaration_gid":"D5/S0/Certificates/DetlefsRoughResidueCharacterizationRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane; Gary Detlefs (2011). *OEIS A008365, 13-rough numbers: positive integers that have no prime factors less than 13*. URL: <https://oeis.org/A008365>.

*Commentary.*

The prime 17 is 13-rough, but its twenty-fourth power has residue 1681 modulo 2310, outside the four proposed classes. The five residues 1, 421, 631, 841, and 1681 attained by 13-rough values are disclosed here without asserting the corrected characterization or its converse.

## References

- Truth anchor: `D5/S0/Certificates/DetlefsRoughResidueCharacterizationRefutation.claim`
- Truth anchor: `D5/S0/Certificates/DetlefsRoughResidueCharacterizationRefutation.inResidueSet`
- Truth anchor: `D5/S0/Certificates/DetlefsRoughResidueCharacterizationRefutation.isRough13`
- Truth anchor: `D5/S0/Certificates/DetlefsRoughResidueCharacterizationRefutation.result`
