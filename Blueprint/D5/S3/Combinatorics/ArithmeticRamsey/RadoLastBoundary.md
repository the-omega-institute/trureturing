# Boundary colourings for the last Rado exception

## Abstract

An explicit two-colouring avoids the boundary equation for every k at least three.

**Definition 1.1 (The lower-bound expression).**

Lean statement: `D5/S3/Combinatorics/ArithmeticRamsey/RadoLastBoundary.LB`

*Formalization.* `D5/S3/Combinatorics/ArithmeticRamsey/RadoLastBoundary.LB` (`✓ std3`).

*Citation.* Tyler B. Hughes and research agents (2026). *The Last Exception for Two-Colour Rado Numbers*. URL: <https://github.com/mathdiscoveries/rado-numbers-last-exception/tree/82a9a73903a9f68b476818a37e20b10405aa8b53>.

*Commentary.*

LB(c,k) is the natural-number ceiling expression used for the two-colour lower bound.

**Definition 1.2 (The last-exception parameter).**

Lean statement: `D5/S3/Combinatorics/ArithmeticRamsey/RadoLastBoundary.cstar`

*Formalization.* `D5/S3/Combinatorics/ArithmeticRamsey/RadoLastBoundary.cstar` (`✓ std3`).

*Citation.* Tyler B. Hughes and research agents (2026). *The Last Exception for Two-Colour Rado Numbers*. URL: <https://github.com/mathdiscoveries/rado-numbers-last-exception/tree/82a9a73903a9f68b476818a37e20b10405aa8b53>.

*Commentary.*

cstar(k) is k(k^2+k-4)/2 for odd k and k(k^2-2)/2 for even k.

**Definition 1.3 (Odd residue colouring).**

Lean statement: `D5/S3/Combinatorics/ArithmeticRamsey/RadoLastBoundary.colOdd`

*Formalization.* `D5/S3/Combinatorics/ArithmeticRamsey/RadoLastBoundary.colOdd` (`✓ std3`).

*Citation.* Tyler B. Hughes and research agents (2026). *The Last Exception for Two-Colour Rado Numbers*. URL: <https://github.com/mathdiscoveries/rado-numbers-last-exception/tree/82a9a73903a9f68b476818a37e20b10405aa8b53>.

*Commentary.*

For odd k, the colouring is one on the prescribed nonzero residue interval and on the sufficiently large zero residue class.

**Definition 1.4 (Even block colouring).**

Lean statement: `D5/S3/Combinatorics/ArithmeticRamsey/RadoLastBoundary.colEven`

*Formalization.* `D5/S3/Combinatorics/ArithmeticRamsey/RadoLastBoundary.colEven` (`✓ std3`).

*Citation.* Tyler B. Hughes and research agents (2026). *The Last Exception for Two-Colour Rado Numbers*. URL: <https://github.com/mathdiscoveries/rado-numbers-last-exception/tree/82a9a73903a9f68b476818a37e20b10405aa8b53>.

*Commentary.*

For even k, the colouring marks the exceptional singleton and the terminal block around k(k-2)/2.

**Theorem 1.5 (The boundary avoiding colouring).**

Lean statement: `D5/S3/Combinatorics/ArithmeticRamsey/RadoLastBoundary.exists_good_col_cstar`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArithmeticRamsey/RadoLastBoundary.exists_good_col_cstar` (`✓ std3`). ∎

*Citation.* Tyler B. Hughes and research agents (2026). *The Last Exception for Two-Colour Rado Numbers*. URL: <https://github.com/mathdiscoveries/rado-numbers-last-exception/tree/82a9a73903a9f68b476818a37e20b10405aa8b53>.

*Commentary.*

For every k at least three, the explicit colouring has no monochromatic solution of x + y + cstar(k) = k z on [1,LB(cstar(k),k)]. Repeated variables remain allowed; no finite boundary Rado-number existence is asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/ArithmeticRamsey/RadoLastBoundary.LB`
- Truth anchor: `D5/S3/Combinatorics/ArithmeticRamsey/RadoLastBoundary.colEven`
- Truth anchor: `D5/S3/Combinatorics/ArithmeticRamsey/RadoLastBoundary.colOdd`
- Truth anchor: `D5/S3/Combinatorics/ArithmeticRamsey/RadoLastBoundary.cstar`
- Truth anchor: `D5/S3/Combinatorics/ArithmeticRamsey/RadoLastBoundary.exists_good_col_cstar`
