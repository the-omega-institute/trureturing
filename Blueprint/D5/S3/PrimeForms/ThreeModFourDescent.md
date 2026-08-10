# Descent at Primes Three Modulo Four

## Abstract

A prime congruent to three modulo four dividing a sum of two squares divides both bases.

**Theorem 1.1 (A prime congruent to three modulo four dividing a sum of two squares divides both bases).**

$$q \text{prime},\ q\equiv 3\ (\operatorname{mod}\ 4),\ q\ \mid\ a^2+b^2\quad\Rightarrow\quad q\ \mid\ a \land q\ \mid\ b$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/ThreeModFourDescent.prime_dvd_dvd_of_dvd_sq_add_sq` (`✓ std3`). ∎

*Citation.* Emil Grosswald (1985). *Representations of Integers as Sums of Squares*. DOI: [10.1007/978-1-4613-8566-0](https://doi.org/10.1007/978-1-4613-8566-0).

*Commentary.*

If a prime q congruent to three modulo four divides a sum of two natural squares, then q divides both bases: otherwise the quotient of the two residues would be a square root of minus one modulo q, which is impossible for q congruent to three modulo four. The statement is the descent engine of the classical two-squares theory and forces the exponent of q in any sum of two squares to be even. The formal proof is thin but not a wrapper: pinned Mathlib carries the modular tool (nonzero squares are never negatives of each other modulo such a prime) yet not the descent implication itself, which is proved here by casting into the residue field and splitting on whether the second base vanishes. The source lemma's parenthetical consequence that the q-adic valuation of a sum of two squares is always even is not part of this deposit. Original numerical-certificate disposition: the source lemma is purely universal and contains no numerical certificate.

## References

- Truth anchor: `D5/S3/PrimeForms/ThreeModFourDescent.prime_dvd_dvd_of_dvd_sq_add_sq`
