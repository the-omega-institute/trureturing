# Cubic Exponent Residues

## Abstract

Every positive integer has canonical coprime squarefree factors for its cubic exponent residues.

**Theorem 1.1 (Canonical mixed-radicand factors).**

Lean statement: `D5/S3/Arith/Lattices/PureCubicExponentResidues.pure_cubic_exponent_residues`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/PureCubicExponentResidues.pure_cubic_exponent_residues` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let B be a positive integer. For each prime p, divide its exponent in B by three. Let c contain the quotient of each division, let m contain the primes with remainder one, and let n contain the primes with remainder two.

The three factors are positive. Both m and n are squarefree, they are coprime, and B equals c cubed times m times n squared. For every p, the exponent in c is the quotient, while the exponents in m and n are respectively one exactly for remainders one and two. These conditions uniquely determine c, m, and n.

The quotient B divided by c cubed has every prime exponent below three, and its radical is m times n. The proof compares prime exponents after Euclidean division; disjoint remainder classes give coprimality.

## References

- Truth anchor: `D5/S3/Arith/Lattices/PureCubicExponentResidues.pure_cubic_exponent_residues`
