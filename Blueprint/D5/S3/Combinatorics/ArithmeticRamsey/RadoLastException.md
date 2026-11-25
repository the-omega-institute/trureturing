# The all-parameter Rado last-exception theorem

## Abstract

The two-colour Rado lower bound is exact above the explicit last exception for every k at least three.

**Definition 1.1 (Good colourings for the reflected equation).**

Lean statement: `D5/S3/Combinatorics/ArithmeticRamsey/RadoLastException.Good`

*Formalization.* `D5/S3/Combinatorics/ArithmeticRamsey/RadoLastException.Good` (`✓ std3`).

*Citation.* Tyler B. Hughes and research agents (2026). *The Last Exception for Two-Colour Rado Numbers*. URL: <https://github.com/mathdiscoveries/rado-numbers-last-exception/tree/82a9a73903a9f68b476818a37e20b10405aa8b53>.

*Commentary.*

Good records the absence of a monochromatic solution of x + y = k z + b in a finite interval and supplies the forcing and reflection mechanism.

**Definition 1.2 (Forcing for every two-colouring).**

Lean statement: `D5/S3/Combinatorics/ArithmeticRamsey/RadoLastException.Forced`

*Formalization.* `D5/S3/Combinatorics/ArithmeticRamsey/RadoLastException.Forced` (`✓ std3`).

*Citation.* Tyler B. Hughes and research agents (2026). *The Last Exception for Two-Colour Rado Numbers*. URL: <https://github.com/mathdiscoveries/rado-numbers-last-exception/tree/82a9a73903a9f68b476818a37e20b10405aa8b53>.

*Commentary.*

HasMono means that there exist positive x,y,z at most n with x+y+c=k*z and equal Boolean colours. Forced quantifies over every col : Nat to Bool; only its values on [1,n] enter the assertion. Repeated variables are allowed.

**Definition 1.3 (The parity validity condition).**

Lean statement: `D5/S3/Combinatorics/ArithmeticRamsey/RadoLastException.Valid`

*Formalization.* `D5/S3/Combinatorics/ArithmeticRamsey/RadoLastException.Valid` (`✓ std3`).

*Citation.* Tyler B. Hughes and research agents (2026). *The Last Exception for Two-Colour Rado Numbers*. URL: <https://github.com/mathdiscoveries/rado-numbers-last-exception/tree/82a9a73903a9f68b476818a37e20b10405aa8b53>.

*Commentary.*

A parameter is valid when k is odd or c is even, matching the parity range of the theorem.

**Definition 1.4 (The least forcing endpoint).**

Lean statement: `D5/S3/Combinatorics/ArithmeticRamsey/RadoLastException.IsRado`

*Formalization.* `D5/S3/Combinatorics/ArithmeticRamsey/RadoLastException.IsRado` (`✓ std3`).

*Citation.* Tyler B. Hughes and research agents (2026). *The Last Exception for Two-Colour Rado Numbers*. URL: <https://github.com/mathdiscoveries/rado-numbers-last-exception/tree/82a9a73903a9f68b476818a37e20b10405aa8b53>.

*Commentary.*

IsRado(c,k,R) means forcing at R and non-forcing at every natural n smaller than R.

**Theorem 1.5 (The complete last-exception theorem).**

Lean statement: `D5/S3/Combinatorics/ArithmeticRamsey/RadoLastException.rado_last_exception`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArithmeticRamsey/RadoLastException.rado_last_exception` (`✓ std3`). ∎

*Citation.* Tyler B. Hughes and research agents (2026). *The Last Exception for Two-Colour Rado Numbers*. URL: <https://github.com/mathdiscoveries/rado-numbers-last-exception/tree/82a9a73903a9f68b476818a37e20b10405aa8b53>.

*Commentary.*

For every natural k at least three, cstar(k) is valid; every valid natural c strictly above cstar(k) has IsRado(c,k,LB(c,k)); and an explicit colouring avoids every monochromatic solution on the closed interval [1,LB(cstar(k),k)]. All three variables range independently over that interval and may repeat. IsRado includes every smaller endpoint, not only the endpoint forcing assertion. No finite existence of a boundary Rado number or negative-c classification is asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/ArithmeticRamsey/RadoLastException.Forced`
- Truth anchor: `D5/S3/Combinatorics/ArithmeticRamsey/RadoLastException.Good`
- Truth anchor: `D5/S3/Combinatorics/ArithmeticRamsey/RadoLastException.IsRado`
- Truth anchor: `D5/S3/Combinatorics/ArithmeticRamsey/RadoLastException.Valid`
- Truth anchor: `D5/S3/Combinatorics/ArithmeticRamsey/RadoLastException.rado_last_exception`
- Dependency: [D5/S3/Combinatorics/ArithmeticRamsey/RadoLastBoundary](RadoLastBoundary.md)
