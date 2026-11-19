# Binomial irreducibility for elimination

## Abstract

Coprime signed degree forces rational-function binomial irreducibility.

Over any field k, a nonzero rational function a and a positive integer m give an irreducible polynomial W^m-a whenever gcd(m,intDegree(a))=1. The degree is signed; negative degrees and even or composite m are included. This is an algebraic ingredient for Laurent elimination. It does not establish the one-direction elimination theorem or the full six-cell conjecture.

**Theorem 1.1 (Coprime degree binomial).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanBinomialIrreducibility.X_pow_sub_C_irreducible_of_intDegree_coprime`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/KhetanBinomialIrreducibility.X_pow_sub_C_irreducible_of_intDegree_coprime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose an irreducible divisor g of W^m-a and adjoin a root alpha. The nonzero root has nonzero norm N, with N^m=a^natDegree(g). Integer degree and Bezout give m dividing natDegree(g). The divisor degree bound and positivity force natDegree(g)=m, hence g is associated to W^m-a. The root-norm calculation adapts Andrew Yang and Patrick Lutz's Mathlib KummerPolynomial prime-degree proof (Apache 2.0); the signed-degree argument supplies the all-degree conclusion.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanBinomialIrreducibility.X_pow_sub_C_irreducible_of_intDegree_coprime`
