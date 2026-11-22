# The first two positive energies of a product rotor ladder

## Abstract

For a product rotor branch list with ordered positive coefficients, the lowest two distinct positive levels determine the smaller coefficient and classify all ambiguities in the larger one.

**Definition 1.1 (Product rotor branch).**

Lean statement: `D5/S3/Quantum/Rotors/ProductBranchLevels.energy`

*Formalization.* `D5/S3/Quantum/Rotors/ProductBranchLevels.energy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For nonnegative integral indices l and k, the listed energy is a l(l+2)+b k(k+2).

**Definition 1.2 (Branches above a threshold).**

Lean statement: `D5/S3/Quantum/Rotors/ProductBranchLevels.above`

*Formalization.* `D5/S3/Quantum/Rotors/ProductBranchLevels.above` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write E(>t) for the set of branch values strictly above t. Each distinct energy appears once.

**Definition 1.3 (Second-level formula).**

Lean statement: `D5/S3/Quantum/Rotors/ProductBranchLevels.secondLevel`

*Formalization.* `D5/S3/Quantum/Rotors/ProductBranchLevels.secondLevel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write L(a,b) for 6a when a=b and for min(3b,8a) otherwise.

**Theorem 1.4 (The lowest two distinct positive branch energies).**

$$0<a \le b \Rightarrow \mathrm{min}E(>0)=3a,\quad \mathrm{min}E(>3a)=L(a,b)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Rotors/ProductBranchLevels.first_two_positive_levels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first positive value is 3a. The next distinct value equals 6a for equal coefficients. For a<b it equals the smaller of 3b and 8a. The indices (1,0), (1,1), (0,1) and (2,0) realize these candidates. Each single-rotor factor is zero, three, or at least eight. These alternatives bound every other branch from below.

**Theorem 1.5 (All parameter collisions of the second-level formula).**

$$0<a \Rightarrow (L(a,b)=L(a,c) \Leftrightarrow b=c \lor \{b,c\}=\{a,2a\} \lor (8a \le 3b \land 8a \le 3c))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Rotors/ProductBranchLevels.second_level_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a>0. The two first energies coincide for ordered candidates b,c≥a exactly in the listed cases. The value at b=a recurs at b=2a. For b≥8a/3 the second value stays equal to 8a. On the intervening unequal branch below the cutoff, L(a,b)=3b. The mathematical equality criterion for L itself holds for arbitrary real b and c.

## References

- Truth anchor: `D5/S3/Quantum/Rotors/ProductBranchLevels.above`
- Truth anchor: `D5/S3/Quantum/Rotors/ProductBranchLevels.energy`
- Truth anchor: `D5/S3/Quantum/Rotors/ProductBranchLevels.first_two_positive_levels`
- Truth anchor: `D5/S3/Quantum/Rotors/ProductBranchLevels.secondLevel`
- Truth anchor: `D5/S3/Quantum/Rotors/ProductBranchLevels.second_level_fiber`
