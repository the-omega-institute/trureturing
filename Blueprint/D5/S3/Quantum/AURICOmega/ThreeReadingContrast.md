# Three-point contrast for a normalized rational Gram form

## Abstract

Which differences can a third probe see at a prescribed mutual reading?

**Theorem 1.1 (The rational disk of attainable differences).**

Lean statement: `D5/S3/Quantum/AURICOmega/ThreeReadingContrast.exists_nonnegative_readings_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/ThreeReadingContrast.exists_nonnegative_readings_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix rational numbers r and d. A positive semidefinite three-by-three rational Gram matrix with diagonal entries one, mutual reading r, and nonnegative probe readings a and b with a minus b equal to d exists exactly when r squared plus d squared is at most one. Here positivity is tested on every rational weight vector.

Two weights first give r at most one. For a at least b, test the weights (1, -r, -d). Adding twice the nonnegative correction (1-r) b d gives the disk inequality. Interchange the points for negative d. Conversely, take the nonnegative part of d as a and the nonnegative part of minus d as b. The Gram form splits into two squares and the nonnegative slack times a square.

At r equal to three fifths the rational contrast four fifths attains the boundary with b equal to zero. At r equal to one every probe gives equal readings. The construction realizes three-point data.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/ThreeReadingContrast.exists_nonnegative_readings_iff`
